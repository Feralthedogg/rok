//! Stones: packages published to a registry index, a git repository laid
//! out like crates.io-index (`rokstones.io-index`). One file per stone,
//! one `Stone { .. }` ROKON value per line, one line per version, oldest
//! first:
//!
//! ```text
//! config.rokon     Config { api: "https://rokstones.io" }   the registry API
//! 1/a  2/ab  3/a/abc  ab/cd/abcd..      a stone's file (by its lowercased name)
//! native/1/a  native/ab/cd/abcd..       a native package's (see `native`)
//! ```
//!
//! ```rokon
//! Stone { name: "geom", vers: "0.3.1", deps: [{ name: "num", req: "^1.2", kind: "normal" }], source: Dep::git("https://github.com/o/geom", rev: "<commit>"), cksum: "<tree>", yanked: false }
//! ```
//!
//! A stone with features has `features: { "name": [..] }` after `deps`,
//! and a dependency `optional: true`, `features: [..]` and
//! `default_features: false` (each only when not the default), as in
//! `rok.rokon`.
//!
//! Sources are not uploaded: `source` names a git commit, and `cksum` is
//! that commit's tree hash, checked after the checkout. A dependency
//! without `registry` is on the same index.

// `HEAD^{tree}` is git revision syntax, not a format argument.
#![allow(clippy::literal_string_with_formatting_args)]

use std::path::{Path, PathBuf};

use rokc_rokon::{Decoder, Doc, Kind, Value};

use crate::git::{self, Cache};
use crate::manifest::{self, Dep, Features, GitRef, Manifest, Source};
use crate::semver::{Req, Version};

/// The index used when neither `ROK_REGISTRY` nor `$ROK_HOME/config.rokon`
/// names one.
pub const DEFAULT: &str = "https://github.com/rok-lang/rokstones.io-index";

/// The configured index: `$ROK_REGISTRY`, else `registry` of
/// `$ROK_HOME/config.rokon` (`Config { registry: ".." }`), else `DEFAULT`.
pub fn default_url(home: &Path) -> Result<String, String> {
    if let Some(u) = std::env::var("ROK_REGISTRY").ok().filter(|u| !u.is_empty()) {
        return Ok(u);
    }
    Ok(crate::config(home, "registry")?.unwrap_or_else(|| DEFAULT.to_owned()))
}

/// A stone's file in the index.
pub fn path(name: &str) -> String {
    let n = name.to_ascii_lowercase();
    match n.len() {
        1 => format!("1/{n}"),
        2 => format!("2/{n}"),
        3 => format!("3/{}/{n}", &n[..1]),
        _ => format!("{}/{}/{n}", &n[..2], &n[2..4]),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)] // the line's fields
pub struct IndexDep {
    pub name: String,
    pub req: String,
    /// `kind: "dev"`: for the stone's own tests, not followed.
    pub dev: bool,
    /// `kind: "native"`: a native package (`crate::native`).
    pub native: bool,
    /// Another index (`None`: the stone's own).
    pub registry: Option<String>,
    pub optional: bool,
    pub features: Vec<String>,
    pub default_features: bool,
}

impl IndexDep {
    /// As a dependency of a stone from index `url`.
    pub fn to_dep(&self, url: &str) -> Dep {
        Dep {
            optional: self.optional,
            features: self.features.clone(),
            default_features: self.default_features,
            ..Dep::new(
                self.name.clone(),
                Source::Registry {
                    req: self.req.clone(),
                    registry: Some(self.registry.clone().unwrap_or_else(|| url.to_owned())),
                },
            )
        }
    }
}

/// One version of a stone: one line of its file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub name: String,
    pub vers: Version,
    pub deps: Vec<IndexDep>,
    pub features: Features,
    /// `source: Dep::git(url, rev: commit)`.
    pub url: String,
    pub rev: String,
    /// The commit's git tree hash.
    pub cksum: String,
    pub yanked: bool,
    /// The manifest's `description` / `license` / `repository`.
    pub meta: Vec<(&'static str, String)>,
}

/// Manifest metadata an entry carries, in line order.
const META: [&str; 3] = ["description", "license", "repository"];

fn entry(d: Decoder<'_>) -> Result<Entry, String> {
    let r = d.record("Stone")?;
    r.only(&[
        "name",
        "vers",
        "deps",
        "features",
        "source",
        "cksum",
        "yanked",
        "description",
        "license",
        "repository",
    ])?;
    let string = |k: &str| r.req(k).and_then(|d| d.string());
    let name = string("name")?;
    manifest::check_name(&name).map_err(|e| r.field_error("name", &e))?;
    let vers = Version::parse(&string("vers")?).map_err(|e| r.field_error("vers", &e))?;
    let mut deps = Vec::new();
    for item in r
        .opt("deps")
        .map(|l| l.list())
        .transpose()?
        .unwrap_or_default()
    {
        let q = item.record("Req")?;
        q.only(&[
            "name",
            "req",
            "kind",
            "registry",
            "optional",
            "features",
            "default_features",
        ])?;
        let name = q.req("name")?.string()?;
        manifest::check_name(&name).map_err(|e| q.field_error("name", &e))?;
        let req = q.req("req")?.string()?;
        Req::parse(&req).map_err(|e| q.field_error("req", &e))?;
        let (dev, native) = match q.opt("kind").map(|k| k.string()).transpose()?.as_deref() {
            None | Some("normal") => (false, false),
            Some("dev") => (true, false),
            Some("native") => (false, true),
            Some(_) => {
                return Err(q.field_error("kind", "`kind` is \"normal\", \"dev\" or \"native\""));
            }
        };
        let registry = q.opt("registry").map(|r| r.string()).transpose()?;
        let optional = q.opt("optional").map(|o| o.bool()).transpose()?;
        if optional == Some(true) && (dev || native) {
            return Err(q.field_error("optional", "only a normal dependency is optional"));
        }
        let mut features = Vec::new();
        for f in q
            .opt("features")
            .map(|l| l.list())
            .transpose()?
            .unwrap_or_default()
        {
            let n = f.string()?;
            manifest::check_feature(&n).map_err(|e| f.error(&e))?;
            features.push(n);
        }
        if native && !features.is_empty() {
            return Err(q.field_error("features", "a native package has no features"));
        }
        deps.push(IndexDep {
            name,
            req,
            dev,
            native,
            registry,
            optional: optional.unwrap_or(false),
            features,
            default_features: q
                .opt("default_features")
                .map(|o| o.bool())
                .transpose()?
                .unwrap_or(true),
        });
    }
    let mut features = Features::new();
    for (k, v) in r
        .opt("features")
        .map(|f| f.dict())
        .transpose()?
        .unwrap_or_default()
    {
        let list = v
            .list()?
            .iter()
            .map(Decoder::string)
            .collect::<Result<_, _>>()?;
        features.push((k.string()?, list));
    }
    let normal: Vec<Dep> = deps
        .iter()
        .filter(|d| !d.dev && !d.native)
        .map(|d| d.to_dep(""))
        .collect();
    manifest::check_features(&features, &normal).map_err(|(_, e)| r.field_error("features", &e))?;
    let src = r.req("source")?;
    let Source::Git {
        url,
        reference: GitRef::Rev(rev),
    } = manifest::source(src)?
    else {
        return Err(src.error("a stone's source is `Dep::git(\"url\", rev: \"<commit>\")`"));
    };
    Ok(Entry {
        name,
        vers,
        deps,
        features,
        url,
        rev,
        cksum: string("cksum")?,
        yanked: r
            .opt("yanked")
            .map(|y| y.bool())
            .transpose()?
            .unwrap_or(false),
        meta: META
            .iter()
            .filter_map(|k| Some(r.opt(k)?.string().map(|v| (*k, v))))
            .collect::<Result<_, _>>()?,
    })
}

/// The entries of one index file (`file` names it in errors); blank lines
/// are skipped.
pub fn parse_file(text: &str, file: &str) -> Result<Vec<Entry>, String> {
    let mut out = Vec::new();
    for (i, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let at = format!("{file} (line {})", i + 1);
        out.push(entry(Doc::parse(line, &at)?.root())?);
    }
    Ok(out)
}

impl Entry {
    /// The index line (canonical ROKON on one line).
    pub fn to_line(&self) -> String {
        let deps = self
            .deps
            .iter()
            .map(|d| {
                let kind = match (d.dev, d.native) {
                    (true, _) => "dev",
                    (_, true) => "native",
                    _ => "normal",
                };
                let mut f = vec![
                    ("name", Value::str(&d.name)),
                    ("req", Value::str(&d.req)),
                    ("kind", Value::str(kind)),
                ];
                if let Some(r) = &d.registry {
                    f.push(("registry", Value::str(r)));
                }
                if d.optional {
                    f.push(("optional", Value::new(Kind::Bool(true))));
                }
                if !d.features.is_empty() {
                    f.push(("features", manifest::strings(&d.features)));
                }
                if !d.default_features {
                    f.push(("default_features", Value::new(Kind::Bool(false))));
                }
                Value::record(None, f)
            })
            .collect();
        let source = Source::Git {
            url: self.url.clone(),
            reference: GitRef::Rev(self.rev.clone()),
        };
        let features = (!self.features.is_empty()).then(|| {
            let kv = self
                .features
                .iter()
                .map(|(k, l)| (Value::str(k), manifest::strings(l)))
                .collect();
            ("features", Value::new(Kind::Dict(kv)))
        });
        rokc_rokon::to_line(&Value::record(
            Some("Stone"),
            [
                ("name", Value::str(&self.name)),
                ("vers", Value::str(self.vers.to_string())),
                ("deps", Value::new(Kind::List(deps))),
            ]
            .into_iter()
            .chain(features)
            .chain([
                ("source", source.to_value()),
                ("cksum", Value::str(&self.cksum)),
                ("yanked", Value::new(Kind::Bool(self.yanked))),
            ])
            .chain(self.meta.iter().map(|(k, v)| (*k, Value::str(v))))
            .collect(),
        ))
    }
}

/// The file of `name` under `prefix` (`""` / `"native/"`) in the cached
/// index `url`, and its text, if any. `a_b` finds `a-b` (and back): one
/// name, two spellings.
pub fn index_file(
    cache: &Cache,
    url: &str,
    prefix: &str,
    name: &str,
) -> Result<Option<(String, String)>, String> {
    for n in [
        name.to_owned(),
        name.replace('_', "-"),
        name.replace('-', "_"),
    ] {
        let file = format!("{prefix}{}", path(&n));
        if let Some(text) = cache.show(url, &file)? {
            return Ok(Some((file, text)));
        }
    }
    Ok(None)
}

/// The versions of stone `name` in the cached index `url` (none when it
/// has no such stone).
pub fn entries(cache: &Cache, url: &str, name: &str) -> Result<Vec<Entry>, String> {
    let Some((file, text)) = index_file(cache, url, "", name)? else {
        return Ok(Vec::new());
    };
    let mut all = parse_file(&text, &format!("{url}: {file}"))?;
    all.retain(|e| manifest::same(&e.name, name));
    Ok(all)
}

/// The highest version matching `req` that is not yanked.
pub fn best<'a>(entries: &'a [Entry], req: &Req) -> Option<&'a Entry> {
    entries
        .iter()
        .filter(|e| !e.yanked && req.matches(&e.vers))
        .max_by(|a, b| a.vers.cmp(&b.vers))
}

/// "no stone .." / "no version of .." for a requirement nothing meets.
pub fn no_match(entries: &[Entry], name: &str, req: &str, url: &str) -> String {
    if entries.is_empty() {
        return format!("no stone named `{name}` in {url}");
    }
    let vs: Vec<String> = entries
        .iter()
        .map(|e| {
            let y = if e.yanked { " (yanked)" } else { "" };
            format!("{}{y}", e.vers)
        })
        .collect();
    format!(
        "no version of stone `{name}` matches `{req}` (in {url}: {})",
        vs.join(", ")
    )
}

/// The index `url`, fetched first unless `offline`.
pub fn open(home: &Path, url: &str, offline: bool, quiet: bool) -> Result<Cache, String> {
    let cache = Cache::index(home);
    if !offline {
        if !quiet {
            eprintln!("    Updating index {url}");
        }
        cache.fetch(url)?;
    } else if !cache.has(url) {
        return Err(format!(
            "the index {url} is not cached, and --offline is set"
        ));
    }
    Ok(cache)
}

/// The index entry for the package at `dir` (its `rok.rokon`): its git
/// remote `origin`, HEAD commit and tree. The work tree must be clean and
/// the package at the repository's root.
pub fn entry_for(dir: &Path, m: &Manifest) -> Result<Entry, String> {
    let name = m.name.clone().ok_or("rok.rokon has no `name`")?;
    manifest::check_name(&name)?;
    let vers = Version::parse(m.version.as_deref().ok_or("rok.rokon has no `version`")?)?;
    if !dir.join("src/lib.rok").is_file() {
        return Err(format!(
            "`{name}` is not a library package (no src/lib.rok)"
        ));
    }
    let mut deps = Vec::new();
    for d in &m.native {
        let manifest::NativeSource::Registry { req, registry } = &d.source else {
            return Err(format!(
                "native dependency `{}` is not in an index: a stone's native packages are \
                 `Dep::native(\"<req>\")`",
                d.name
            ));
        };
        deps.push(IndexDep {
            name: d.name.clone(),
            req: req.clone(),
            dev: false,
            native: true,
            registry: registry.clone(),
            optional: false,
            features: Vec::new(),
            default_features: true,
        });
    }
    for (d, dev) in m
        .deps
        .iter()
        .map(|d| (d, false))
        .chain(m.dev_deps.iter().map(|d| (d, true)))
    {
        match &d.source {
            Source::Registry { req, registry } => deps.push(IndexDep {
                name: d.name.clone(),
                req: req.clone(),
                dev,
                native: false,
                registry: registry.clone(),
                optional: d.optional,
                features: d.features.clone(),
                default_features: d.default_features,
            }),
            // A stone's users never build its tests.
            _ if dev => {}
            _ => {
                return Err(format!(
                    "dependency `{}` is not a stone: a stone depends on stones only \
                     (`Dep::version(..)`)",
                    d.name
                ));
            }
        }
    }
    let top = git::run(dir, &["rev-parse", "--show-toplevel"])?;
    let same = rokc_core::real_path(&top).ok() == rokc_core::real_path(dir).ok();
    if !same {
        return Err(format!(
            "the package must be at the root of its git repository ({top})"
        ));
    }
    if !git::run(dir, &["status", "--porcelain"])?.is_empty() {
        return Err("the work tree has uncommitted changes; commit them first".into());
    }
    let url = git::run(dir, &["remote", "get-url", "origin"])
        .map_err(|_| "the repository has no remote `origin` (where users fetch the source)")?;
    Ok(Entry {
        name,
        vers,
        deps,
        features: m.features.clone(),
        url,
        rev: git::run(dir, &["rev-parse", "HEAD"])?,
        cksum: git::run(dir, &["rev-parse", "HEAD^{tree}"])?,
        yanked: false,
        meta: [
            ("description", &m.description),
            ("license", &m.license),
            ("repository", &m.repository),
        ]
        .into_iter()
        .filter_map(|(k, v)| Some((k, v.clone()?)))
        .collect(),
    })
}

/// A local checkout of an index: file `rel` there, and its text.
pub fn local(index: &Path, rel: &str) -> Result<(PathBuf, String), String> {
    if !index.join(".git").exists() {
        return Err(format!(
            "{} is not a git checkout of an index",
            index.display()
        ));
    }
    let file = index.join(rel);
    let text = match std::fs::read_to_string(&file) {
        Ok(t) => t,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(e) => return Err(format!("{}: {e}", file.display())),
    };
    Ok((file, text))
}

pub fn commit(index: &Path, file: &Path, text: &str, msg: &str) -> Result<(), String> {
    std::fs::create_dir_all(file.parent().unwrap_or(index))
        .and_then(|()| std::fs::write(file, text))
        .map_err(|e| format!("{}: {e}", file.display()))?;
    let rel = file
        .strip_prefix(index)
        .unwrap_or(file)
        .display()
        .to_string();
    git::run(index, &["add", "--", &rel])?;
    git::run(index, &["commit", "--quiet", "-m", msg, "--", &rel]).map(drop)
}

/// Add `e` to the index checkout `index` (checked against what is there);
/// with `write`, as a new commit. The file it goes to.
pub fn publish(index: &Path, e: &Entry, write: bool) -> Result<PathBuf, String> {
    let (file, text) = local(index, &path(&e.name))?;
    let have = parse_file(&text, &file.display().to_string())?;
    let names = have.iter().map(|o| o.name.clone());
    taken(index, "", &e.name, names)?;
    if have.iter().any(|o| o.vers == e.vers) {
        return Err(format!("{} {} is already in the index", e.name, e.vers));
    }
    if write {
        let mut out = text;
        if !out.is_empty() && !out.ends_with('\n') {
            out.push('\n');
        }
        out.push_str(&e.to_line());
        out.push('\n');
        commit(
            index,
            &file,
            &out,
            &format!("Publish {} {}", e.name, e.vers),
        )?;
    }
    Ok(file)
}

/// Fail when the index checkout `index` has a name under `prefix` (or
/// in `have`, the target file's) that is `name` spelled otherwise: `a-b`
/// and `a_b` (or another case) are one package, but each spelling has
/// its own file.
pub fn taken(
    index: &Path,
    prefix: &str,
    name: &str,
    have: impl Iterator<Item = String>,
) -> Result<(), String> {
    let files = git::run(index, &["ls-files"])?;
    let other = files
        .lines()
        .filter(|f| f.starts_with("native/") == (prefix == "native/"))
        .filter_map(|f| f.rsplit('/').next().map(str::to_owned))
        .chain(have)
        .find(|n| n != name && manifest::same(n, name));
    match other {
        Some(o) => Err(format!(
            "the index has {}`{o}`; `{name}` is the same name (`-` / `_` and case are one)",
            if prefix.is_empty() {
                "stone "
            } else {
                "native package "
            }
        )),
        None => Ok(()),
    }
}

/// Set `yanked` of `name`'s version `vers` in the index checkout `index`,
/// as a new commit: a stone's, or with `native`, a native package's.
pub fn yank(
    index: &Path,
    name: &str,
    vers: &str,
    yanked: bool,
    native: bool,
) -> Result<(), String> {
    let vers = Version::parse(vers)?;
    let rel = if native {
        crate::native::path(name)
    } else {
        path(name)
    };
    let (file, text) = local(index, &rel)?;
    let shown = file.display().to_string();
    let mut found = false;
    let mut out = String::new();
    for (i, line) in text.lines().enumerate() {
        let at = format!("{shown} (line {})", i + 1);
        // The line's name and version, and the line with `yanked` set.
        let e = if line.trim().is_empty() {
            None
        } else if native {
            let mut e = crate::native::parse_one(line, &at)?;
            e.yanked = yanked;
            Some((e.name.clone(), e.vers.clone(), e.to_line()))
        } else {
            let mut e = entry(Doc::parse(line, &at)?.root())?;
            e.yanked = yanked;
            Some((e.name.clone(), e.vers.clone(), e.to_line()))
        };
        match e {
            Some((n, v, l)) if manifest::same(&n, name) && v == vers => {
                found = true;
                out.push_str(&l);
            }
            _ => out.push_str(line),
        }
        out.push('\n');
    }
    let what = if native { "native " } else { "" };
    if !found {
        return Err(format!(
            "{what}{name} {vers} is not in the index {}",
            index.display()
        ));
    }
    if out == text {
        return Ok(());
    }
    let verb = if yanked { "Yank" } else { "Unyank" };
    commit(index, &file, &out, &format!("{verb} {what}{name} {vers}"))
}

/// `rok login`'s file: `Credentials { token: ".." }`.
fn credentials(home: &Path) -> PathBuf {
    home.join("credentials.rokon")
}

/// A token goes into an HTTP header: printable ASCII, no spaces.
pub fn check_token(token: &str) -> Result<(), String> {
    if token.is_empty() || !token.bytes().all(|b| b.is_ascii_graphic()) {
        return Err("a token is printable ASCII without spaces".into());
    }
    Ok(())
}

/// The token for the registry API: `$ROK_REGISTRY_TOKEN`, else
/// `rok login`'s.
pub fn token(home: &Path) -> Result<String, String> {
    pick_token(std::env::var("ROK_REGISTRY_TOKEN").ok(), home)
}

fn pick_token(env: Option<String>, home: &Path) -> Result<String, String> {
    if let Some(t) = env.filter(|t| !t.is_empty()) {
        check_token(&t).map_err(|e| format!("ROK_REGISTRY_TOKEN: {e}"))?;
        return Ok(t);
    }
    let path = credentials(home);
    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Err("publishing needs a token: run `rok login` first".into());
        }
        Err(e) => return Err(format!("{}: {e}", path.display())),
    };
    // Parse errors would quote the line holding the token.
    let bad = |_| format!("{} is malformed; run `rok login` again", path.display());
    let doc = Doc::parse(&text, "credentials").map_err(bad)?;
    let r = doc.root().record("Credentials").map_err(bad)?;
    r.only(&["token"]).map_err(bad)?;
    let t = r.req("token").and_then(|t| t.string()).map_err(bad)?;
    check_token(&t).map_err(bad)?;
    Ok(t)
}

/// Keep `token` in `$ROK_HOME/credentials.rokon` (mode 0600 on Unix);
/// the file.
pub fn save_token(home: &Path, token: &str) -> Result<PathBuf, String> {
    use std::io::Write;
    let path = credentials(home);
    std::fs::create_dir_all(home).map_err(|e| format!("{}: {e}", home.display()))?;
    let text = rokc_rokon::to_string(&Value::record(
        Some("Credentials"),
        vec![("token", Value::str(token))],
    )) + "\n";
    // Created anew, so the mode applies.
    let _ = std::fs::remove_file(&path);
    let mut o = std::fs::OpenOptions::new();
    o.write(true).create_new(true);
    #[cfg(unix)]
    std::os::unix::fs::OpenOptionsExt::mode(&mut o, 0o600);
    o.open(&path)
        .and_then(|mut f| f.write_all(text.as_bytes()))
        .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    Ok(path)
}

/// Remove `rok login`'s token; whether there was one.
pub fn logout(home: &Path) -> Result<bool, String> {
    let path = credentials(home);
    match std::fs::remove_file(&path) {
        Ok(()) => Ok(true),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(format!("cannot remove {}: {e}", path.display())),
    }
}

/// The registry API of the index `url`: `api` of its `config.rokon`
/// (`Config { api: "https://.." }`), without a trailing `/`. HTTPS only,
/// except on the loopback host.
pub fn api(home: &Path, url: &str, quiet: bool) -> Result<String, String> {
    let cache = open(home, url, false, quiet)?;
    let text = cache.show(url, "config.rokon")?.ok_or_else(|| {
        format!("the index {url} has no config.rokon naming its API; use --index <checkout>")
    })?;
    let file = format!("{url}: config.rokon");
    let doc = Doc::parse(&text, &file)?;
    let a = doc.root().record("Config")?.req("api")?.string()?;
    check_api(&a).map_err(|e| format!("{url}: config.rokon: {e}"))?;
    Ok(a.trim_end_matches('/').to_owned())
}

fn check_api(a: &str) -> Result<(), String> {
    let local = ["http://127.0.0.1", "http://localhost"].iter().any(|h| {
        a.strip_prefix(h)
            .is_some_and(|r| r.is_empty() || r.starts_with([':', '/']))
    });
    if a.starts_with("https://") || local {
        Ok(())
    } else {
        Err(format!("api `{a}` must be an https:// URL"))
    }
}

/// `{api}{path}` with `token` as a bearer token: `GET`, or `POST` of
/// `body`. The reply's text on a 2xx status; else an error, the reply's
/// `Error { message }` if it has one. The token reaches `curl` on stdin,
/// never on its command line, and is stripped from errors.
fn call(api: &str, path: &str, token: &str, body: Option<&str>) -> Result<String, String> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    // A curl config file: values quoted, `\` and `"` escaped.
    let q = |s: &str| format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""));
    let mut config = format!(
        "header = {}\n",
        q(&format!("Authorization: Bearer {token}"))
    );
    if let Some(b) = body {
        config += "header = \"Content-Type: application/rokon; charset=utf-8\"\n";
        config += &format!("data-raw = {}\n", q(b));
    }
    let url = format!("{api}{path}");
    let hide = |e: String| e.replace(token, "***");
    let mut child = Command::new("curl")
        .args(["-sS", "--proto", "=https,http", "-w", "\n%{http_code}"])
        .args(["--config", "-"])
        .arg(&url)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot run `curl` (is it installed?): {e}"))?;
    // Dropped after writing: curl reads to the end.
    let sent = child
        .stdin
        .take()
        .map(|mut i| i.write_all(config.as_bytes()));
    let out = child.wait_with_output().map_err(|e| e.to_string())?;
    if !out.status.success() || !matches!(sent, Some(Ok(()))) {
        return Err(hide(format!(
            "cannot reach {url}: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        )));
    }
    let all = String::from_utf8_lossy(&out.stdout);
    let (text, code) = all.rsplit_once('\n').unwrap_or(("", &all));
    let code: u16 = code.trim().parse().unwrap_or(0);
    if (200..300).contains(&code) {
        return Ok(text.to_owned());
    }
    if code == 401 {
        return Err(format!(
            "{api} refused the token: create one at {api}/me, then run `rok login`"
        ));
    }
    let message = Doc::parse(text, &url).ok().and_then(|d| {
        let r = d.root().record("Error").ok()?;
        r.req("message").and_then(|m| m.string()).ok()
    });
    Err(hide(match message {
        Some(m) => format!("{api}: {m}"),
        None => format!("{url}: HTTP status {code}"),
    }))
}

/// The account `token` belongs to at `api`: its login, and whether it
/// may publish.
pub fn me(api: &str, token: &str) -> Result<(String, bool), String> {
    let text = call(api, "/api/v1/me", token, None)?;
    let file = format!("{api}/api/v1/me");
    let doc = Doc::parse(&text, &file)?;
    let r = doc.root().record("Me")?;
    Ok((r.req("login")?.string()?, r.req("publish")?.bool()?))
}

/// Publish the index line `line` (`Stone { .. }` / `Native { .. }`)
/// through `api`; the name and version it took.
pub fn publish_api(api: &str, token: &str, line: &str) -> Result<(String, String), String> {
    let text = call(api, "/api/v1/publish", token, Some(line))?;
    let file = format!("{api}/api/v1/publish");
    let doc = Doc::parse(&text, &file)?;
    let r = doc.root().record("Published")?;
    Ok((r.req("name")?.string()?, r.req("vers")?.string()?))
}

/// Yank (with `undo`, unyank) `name`'s version `vers` through `api`: a
/// stone's, or with `native`, a native package's.
pub fn yank_api(
    api: &str,
    token: &str,
    name: &str,
    vers: &str,
    undo: bool,
    native: bool,
) -> Result<(), String> {
    let vers = Version::parse(vers)?.to_string();
    let flag = |b| Value::new(Kind::Bool(b));
    let body = rokc_rokon::to_line(&Value::record(
        Some("Yank"),
        vec![
            ("name", Value::str(name)),
            ("vers", Value::str(vers)),
            ("undo", flag(undo)),
            ("native", flag(native)),
        ],
    ));
    call(api, "/api/v1/yank", token, Some(&body)).map(drop)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokens() {
        for a in [
            "https://rokstones.io",
            "http://127.0.0.1:8080",
            "http://localhost",
        ] {
            assert!(check_api(a).is_ok(), "{a}");
        }
        for a in [
            "http://rokstones.io",
            "http://127.0.0.1.x",
            "file:///x",
            "ftp://x",
        ] {
            assert!(check_api(a).is_err(), "{a}");
        }
        let home = std::env::temp_dir().join(format!("rok-token-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&home);
        let e = pick_token(None, &home).unwrap_err();
        assert!(e.contains("run `rok login` first"), "{e}");
        let file = save_token(&home, "ghp_file").unwrap();
        assert_eq!(pick_token(None, &home).unwrap(), "ghp_file");
        // The environment wins over the file.
        assert_eq!(
            pick_token(Some("ghp_env".into()), &home).unwrap(),
            "ghp_env"
        );
        assert_eq!(pick_token(Some(String::new()), &home).unwrap(), "ghp_file");
        assert!(pick_token(Some("a b".into()), &home).is_err());
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::metadata(&file).unwrap().permissions().mode();
            assert_eq!(mode & 0o777, 0o600);
        }
        std::fs::write(&file, "Credentials { token: \"ghp_secret\", x: 1 }").unwrap();
        let e = pick_token(None, &home).unwrap_err();
        assert!(e.contains("malformed") && !e.contains("ghp_secret"), "{e}");
        assert!(logout(&home).unwrap());
        assert!(!logout(&home).unwrap());
        let _ = std::fs::remove_dir_all(&home);
    }

    #[test]
    fn paths_and_lines() {
        assert_eq!(path("a"), "1/a");
        assert_eq!(path("ab"), "2/ab");
        assert_eq!(path("Abc"), "3/a/abc");
        assert_eq!(path("geom_x"), "ge/om/geom_x");
        let e = Entry {
            name: "geom".into(),
            vers: Version::parse("0.3.1").unwrap(),
            deps: vec![IndexDep {
                name: "num".into(),
                req: "^1.2".into(),
                dev: false,
                native: false,
                registry: None,
                optional: false,
                features: Vec::new(),
                default_features: true,
            }],
            features: Vec::new(),
            url: "https://github.com/o/geom".into(),
            rev: "c".repeat(40),
            cksum: "t".repeat(40),
            yanked: false,
            meta: vec![("license", "MIT".into())],
        };
        let line = e.to_line();
        assert_eq!(
            line,
            format!(
                "Stone {{ name: \"geom\", vers: \"0.3.1\", deps: [{{ name: \"num\", req: \"^1.2\", \
                 kind: \"normal\" }}], source: Dep::git(\"https://github.com/o/geom\", rev: \
                 \"{}\"), cksum: \"{}\", yanked: false, license: \"MIT\" }}",
                "c".repeat(40),
                "t".repeat(40)
            )
        );
        let two = format!("{line}\n\n{}\n", line.replace("0.3.1", "0.4.0"));
        let back = parse_file(&two, "ge/om/geom").unwrap();
        assert_eq!(back[0], e);
        assert_eq!(back[1].vers.to_string(), "0.4.0");
        assert_eq!(best(&back, &Req::parse("^0.3").unwrap()), Some(&back[0]));
        // Features round-trip; only what differs from the defaults is written.
        let mut f = e;
        f.deps[0].optional = true;
        f.deps[0].features = vec!["fast".into()];
        f.deps[0].default_features = false;
        f.features = vec![
            ("default".into(), vec!["simd".into()]),
            ("simd".into(), vec!["dep:num".into(), "num?/x".into()]),
        ];
        let fl = f.to_line();
        assert!(
            fl.contains(
                "kind: \"normal\", optional: true, features: [\"fast\"], default_features: false \
                 }], features: { \"default\": [\"simd\"], \"simd\": [\"dep:num\", \"num?/x\"] }, \
                 source:"
            ),
            "{fl}"
        );
        assert_eq!(parse_file(&fl, "f").unwrap()[0], f);
        let bad = fl.replace("\"dep:num\"", "\"dep:nope\"");
        let err = parse_file(&bad, "f").unwrap_err();
        assert!(err.contains("there is no dependency `nope`"), "{err}");
        let e = parse_file(&format!("\n{}", line.replace("rev:", "tag:")), "f").unwrap_err();
        assert!(e.contains("--> f (line 2):1:"), "{e}");
        assert!(e.contains("a stone's source"), "{e}");
    }
}

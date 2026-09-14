//! Stones: packages published to a registry index, a git repository laid
//! out like crates.io-index (`rokstones.io-index`). One file per stone,
//! one `Stone { .. }` RokON value per line, one line per version, oldest
//! first:
//!
//! ```text
//! config.rokon     Registry { name: "rokstones.io", dl: "git", api: "https://rokstones.io" }
//! 1/a  2/ab  3/a/abc  ab/cd/abcd..      a stone's file (by its lowercased name)
//! ```
//!
//! ```rokon
//! Stone { name: "geom", vers: "0.3.1", deps: [{ name: "num", req: "^1.2", kind: "normal" }], source: Dep::git("https://github.com/o/geom", rev: "<commit>"), cksum: "<tree>", yanked: false }
//! ```
//!
//! Sources are not uploaded: `source` names a git commit, and `cksum` is
//! that commit's tree hash, checked after the checkout. A dependency
//! without `registry` is on the same index.

// `HEAD^{tree}` is git revision syntax, not a format argument.
#![allow(clippy::literal_string_with_formatting_args)]

use std::path::{Path, PathBuf};

use rokc_rokon::{Decoder, Doc, Kind, Value};

use crate::git::{self, Cache};
use crate::manifest::{self, GitRef, Manifest, Source};
use crate::semver::{Req, Version};

/// The index used when neither `ROK_REGISTRY` nor `$ROK_HOME/config.rokon`
/// names one.
// Placeholder organization until the index is hosted.
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
pub struct IndexDep {
    pub name: String,
    pub req: String,
    /// `kind: "dev"`: for the stone's own tests, not followed.
    pub dev: bool,
    /// Another index (`None`: the stone's own).
    pub registry: Option<String>,
}

/// One version of a stone: one line of its file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub name: String,
    pub vers: Version,
    pub deps: Vec<IndexDep>,
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
        q.only(&["name", "req", "kind", "registry"])?;
        let name = q.req("name")?.string()?;
        manifest::check_name(&name).map_err(|e| q.field_error("name", &e))?;
        let req = q.req("req")?.string()?;
        Req::parse(&req).map_err(|e| q.field_error("req", &e))?;
        let dev = match q.opt("kind").map(|k| k.string()).transpose()?.as_deref() {
            None | Some("normal") => false,
            Some("dev") => true,
            Some(_) => return Err(q.field_error("kind", "`kind` is \"normal\" or \"dev\"")),
        };
        let registry = q.opt("registry").map(|r| r.string()).transpose()?;
        deps.push(IndexDep {
            name,
            req,
            dev,
            registry,
        });
    }
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
    /// The index line (canonical RokON on one line).
    pub fn to_line(&self) -> String {
        let deps = self
            .deps
            .iter()
            .map(|d| {
                let kind = if d.dev { "dev" } else { "normal" };
                let mut f = vec![
                    ("name", Value::str(&d.name)),
                    ("req", Value::str(&d.req)),
                    ("kind", Value::str(kind)),
                ];
                if let Some(r) = &d.registry {
                    f.push(("registry", Value::str(r)));
                }
                Value::record(None, f)
            })
            .collect();
        let source = Source::Git {
            url: self.url.clone(),
            reference: GitRef::Rev(self.rev.clone()),
        };
        rokc_rokon::to_line(&Value::record(
            Some("Stone"),
            vec![
                ("name", Value::str(&self.name)),
                ("vers", Value::str(self.vers.to_string())),
                ("deps", Value::new(Kind::List(deps))),
                ("source", source.to_value()),
                ("cksum", Value::str(&self.cksum)),
                ("yanked", Value::new(Kind::Bool(self.yanked))),
            ]
            .into_iter()
            .chain(self.meta.iter().map(|(k, v)| (*k, Value::str(v))))
            .collect(),
        ))
    }
}

/// The versions of stone `name` in the cached index `url` (none when it
/// has no such stone).
pub fn entries(cache: &Cache, url: &str, name: &str) -> Result<Vec<Entry>, String> {
    // `a_b` finds stone `a-b` (and back): one name, two spellings.
    let mut text = None;
    let mut file = path(name);
    for n in [
        name.to_owned(),
        name.replace('_', "-"),
        name.replace('-', "_"),
    ] {
        file = path(&n);
        text = cache.show(url, &file)?;
        if text.is_some() {
            break;
        }
    }
    let Some(text) = text else {
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
    if !dir.join("lib.rok").is_file() {
        return Err(format!("`{name}` is not a library package (no lib.rok)"));
    }
    let mut deps = Vec::new();
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
                registry: registry.clone(),
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
    let same = std::fs::canonicalize(&top).ok() == std::fs::canonicalize(dir).ok();
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

/// A local checkout of an index: the stone's file there, and its text.
fn local(index: &Path, name: &str) -> Result<(PathBuf, String), String> {
    if !index.join(".git").exists() {
        return Err(format!(
            "{} is not a git checkout of an index",
            index.display()
        ));
    }
    let file = index.join(path(name));
    let text = match std::fs::read_to_string(&file) {
        Ok(t) => t,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(e) => return Err(format!("{}: {e}", file.display())),
    };
    Ok((file, text))
}

fn commit(index: &Path, file: &Path, text: &str, msg: &str) -> Result<(), String> {
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
    let (file, text) = local(index, &e.name)?;
    let have = parse_file(&text, &file.display().to_string())?;
    // `a-b` and `a_b` (or another case) are one stone; the other spelling
    // has its own file.
    let files = git::run(index, &["ls-files"])?;
    let other = files
        .lines()
        .filter_map(|f| f.rsplit('/').next())
        .chain(have.iter().map(|o| o.name.as_str()))
        .find(|n| *n != e.name && manifest::same(n, &e.name));
    if let Some(o) = other {
        return Err(format!(
            "the index has stone `{o}`; `{}` is the same name (`-` / `_` and case are one)",
            e.name
        ));
    }
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

/// Set `yanked` of `name`'s version `vers` in the index checkout `index`,
/// as a new commit.
pub fn yank(index: &Path, name: &str, vers: &str, yanked: bool) -> Result<(), String> {
    let vers = Version::parse(vers)?;
    let (file, text) = local(index, name)?;
    let shown = file.display().to_string();
    let mut found = false;
    let mut out = String::new();
    for (i, line) in text.lines().enumerate() {
        let at = format!("{shown} (line {})", i + 1);
        let mut e = (!line.trim().is_empty())
            .then(|| Doc::parse(line, &at).and_then(|d| entry(d.root())))
            .transpose()?;
        match &mut e {
            Some(e) if manifest::same(&e.name, name) && e.vers == vers => {
                found = true;
                e.yanked = yanked;
                out.push_str(&e.to_line());
            }
            _ => out.push_str(line),
        }
        out.push('\n');
    }
    if !found {
        return Err(format!(
            "{name} {vers} is not in the index {}",
            index.display()
        ));
    }
    if out == text {
        return Ok(());
    }
    let verb = if yanked { "Yank" } else { "Unyank" };
    commit(index, &file, &out, &format!("{verb} {name} {vers}"))
}

#[cfg(test)]
mod tests {
    use super::*;

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
                registry: None,
            }],
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
        let e = parse_file(&format!("\n{}", line.replace("rev:", "tag:")), "f").unwrap_err();
        assert!(e.contains("--> f (line 2):1:"), "{e}");
        assert!(e.contains("a stone's source"), "{e}");
    }
}

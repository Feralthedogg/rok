//! `rok.rokon`: the package manifest (also an environment's), and the
//! `//! ```rokon` block of a single-file script.
//!
//! The file is one RokON value (`rokc_rokon`), a `Package { .. }` struct
//! (the name `Package` may be left out). It is data only: strings,
//! `{ "key": value }` dicts and the `Dep::path(..)` / `Dep::git(..)` /
//! `Dep::version(..)` variants.
//!
//! ```rokon
//! Package {
//!     name: "app",
//!     version: "0.1.0",
//!     toolchain: "0.3",
//!     description: "A JSON app",
//!     license: "MIT OR Apache-2.0",
//!     repository: "https://example.com/app.git",
//!     deps: {
//!         "json": Dep::git("https://example.com/json.git", tag: "v1.2"),
//!         "util": Dep::path("../util"),
//!         "geom": Dep::version("^0.3"),   // a stone; also `"geom": "^0.3"`
//!     },
//!     dev_deps: {},
//!     lints: { "dead_code": "allow" },
//! }
//! ```

use std::path::{Path, PathBuf};

use rokc_core::lint::Level;
use rokc_rokon::edit::{self, Step};
use rokc_rokon::{Decoder, Doc, Value};

pub const MANIFEST: &str = "rok.rokon";
pub const LOCK: &str = "rok.lock";
/// A manifest with nothing in it, for `rok add` to fill.
pub const EMPTY: &str = "Package {\n    deps: {},\n}\n";

const FIELDS: [&str; 9] = [
    "name",
    "version",
    "toolchain",
    "description",
    "license",
    "repository",
    "deps",
    "dev_deps",
    "lints",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GitRef {
    Default,
    Rev(String),
    Tag(String),
    Branch(String),
}

impl GitRef {
    /// `(name, value)` of the `Dep::git(.., name: value)` argument.
    pub fn pair(&self) -> Option<(&'static str, &str)> {
        match self {
            Self::Default => None,
            Self::Rev(r) => Some(("rev", r)),
            Self::Tag(t) => Some(("tag", t)),
            Self::Branch(b) => Some(("branch", b)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    /// As written: relative to the manifest's directory.
    Path(String),
    Git {
        url: String,
        reference: GitRef,
    },
    /// A stone: a version requirement (`crate::semver::Req` syntax) on a
    /// registry index (`None`: the configured one).
    Registry {
        req: String,
        registry: Option<String>,
    },
}

impl Source {
    /// The `Dep::..` value.
    pub fn to_value(&self) -> Value {
        match self {
            Self::Path(p) => Value::call("Dep::path", vec![Value::str(p)], Vec::new()),
            Self::Git { url, reference } => Value::call(
                "Dep::git",
                vec![Value::str(url)],
                reference
                    .pair()
                    .map(|(k, v)| (k, Value::str(v)))
                    .into_iter()
                    .collect(),
            ),
            Self::Registry { req, registry } => Value::call(
                "Dep::version",
                vec![Value::str(req)],
                registry
                    .iter()
                    .map(|r| ("registry", Value::str(r)))
                    .collect(),
            ),
        }
    }

    /// The `Dep::..` text for `rok.rokon`, on one line (it is spliced in).
    pub fn to_rok(&self) -> String {
        rokc_rokon::to_line(&self.to_value())
    }
}

#[derive(Clone, Debug)]
pub struct Dep {
    pub name: String,
    pub source: Source,
}

#[derive(Clone, Debug, Default)]
pub struct Manifest {
    pub name: Option<String>,
    pub version: Option<String>,
    pub toolchain: Option<String>,
    /// Package metadata, carried into a stone's index entry.
    pub description: Option<String>,
    /// An SPDX license expression.
    pub license: Option<String>,
    pub repository: Option<String>,
    pub deps: Vec<Dep>,
    pub dev_deps: Vec<Dep>,
    /// `lints`: `"name": "allow" | "warn" | "deny"`, in file order
    /// (lint names are checked by `rokc lint`).
    pub lints: Vec<(String, Level)>,
}

/// A package (and dependency) name: `[a-z][a-z0-9_-]*`. Code names it
/// with `-` as `_` (`code_name`), so it starts with a letter.
pub fn check_name(name: &str) -> Result<(), String> {
    let valid = |n: &str| {
        n.starts_with(|c: char| c.is_ascii_lowercase())
            && n.chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-' || c == '_')
    };
    if valid(name) {
        return Ok(());
    }
    let fixed: String = name
        .to_ascii_lowercase()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '-'
            }
        })
        .collect();
    Err(format!(
        "`{name}` is not a valid package name: lowercase ASCII letters, digits, `-` and `_`, \
         starting with a letter{}",
        if valid(&fixed) {
            format!("; try `{fixed}`")
        } else {
            String::new()
        }
    ))
}

/// The name code uses for package `name` (`use`, `--extern`): `-` as `_`.
pub fn code_name(name: &str) -> String {
    name.replace('-', "_")
}

/// A package's identity: names equal up to case and `-` / `_` are one
/// package (so they cannot both exist).
pub fn key(name: &str) -> String {
    code_name(&name.to_ascii_lowercase())
}

pub fn same(a: &str, b: &str) -> bool {
    key(a) == key(b)
}

/// `dir/rok.rokon`, if present. A file whose name differs only in case
/// (`Rok.rokon`) is not the manifest: warn, whatever the file system.
pub fn find(dir: &Path) -> Option<PathBuf> {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return None;
    };
    let mut found = None;
    let mut names: Vec<(String, PathBuf)> = rd
        .flatten()
        .filter_map(|e| Some((e.file_name().into_string().ok()?, e.path())))
        .collect();
    names.sort();
    for (name, path) in names {
        if name == MANIFEST {
            found = Some(path);
        } else if name.eq_ignore_ascii_case(MANIFEST) {
            eprintln!(
                "rok: warning: ignoring `{}`: the manifest is named `{MANIFEST}` (lowercase)",
                path.display()
            );
        }
    }
    found
}

pub fn load(path: &Path) -> Result<Manifest, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    parse(&text, &path.display().to_string())
}

fn not_yet(what: &str) -> String {
    format!("{what} is reserved and not supported yet")
}

/// Parse manifest text; `file` names it in errors.
pub fn parse(text: &str, file: &str) -> Result<Manifest, String> {
    let doc = Doc::parse(text, file)?;
    let pkg = doc.root().record("Package")?;
    if pkg.get("registry").is_some() {
        return Err(pkg.field_error("registry", &not_yet("registries")));
    }
    if pkg.get("native").is_some() {
        return Err(pkg.field_error("native", &not_yet("`native`")));
    }
    pkg.only(&FIELDS)?;
    let string = |f: &str| pkg.opt(f).map(|d| d.string()).transpose();
    let deps = |f: &str| pkg.opt(f).map_or(Ok(Vec::new()), deps);
    let mut lints = Vec::new();
    if let Some(d) = pkg.opt("lints") {
        for (k, v) in d.dict()? {
            let Some(level) = Level::parse(&v.string()?) else {
                return Err(v.error(&format!(
                    "lint `{}` takes \"allow\", \"warn\" or \"deny\"",
                    k.string()?
                )));
            };
            lints.push((k.string()?, level));
        }
    }
    // The package name is the dependency name others give it.
    if let Some(d) = pkg.opt("name") {
        check_name(&d.string()?).map_err(|m| d.error(&m))?;
    }
    Ok(Manifest {
        name: string("name")?,
        version: string("version")?,
        toolchain: string("toolchain")?,
        description: string("description")?,
        license: string("license")?,
        repository: string("repository")?,
        deps: deps("deps")?,
        dev_deps: deps("dev_deps")?,
        lints,
    })
}

fn deps(d: Decoder<'_>) -> Result<Vec<Dep>, String> {
    let mut out = Vec::new();
    for (k, v) in d.dict()? {
        let name = k.string()?;
        check_name(&name).map_err(|m| k.error(&m))?;
        if let Some(o) = out.iter().find(|o: &&Dep| same(&o.name, &name)) {
            return Err(k.error(&format!(
                "`{name}` and `{}` are the same package (`-` and `_` are one)",
                o.name
            )));
        }
        let source = source(v)?;
        out.push(Dep { name, source });
    }
    Ok(out)
}

/// A requirement string, checked.
fn req(d: Decoder<'_>) -> Result<String, String> {
    let s = d.string()?;
    crate::semver::Req::parse(&s).map_err(|e| d.error(&e))?;
    Ok(s)
}

/// A `Dep::path(..)` / `Dep::git(..)` / `Dep::version(..)` value, or a
/// requirement string (`"^1.2"`, short for `Dep::version("^1.2")`).
pub fn source(d: Decoder<'_>) -> Result<Source, String> {
    if d.string().is_ok() {
        return Ok(Source::Registry {
            req: req(d)?,
            registry: None,
        });
    }
    let v = d.variant("Dep").map_err(|_| {
        d.expected("`Dep::path(\"..\")`, `Dep::git(\"..\")` or `Dep::version(\"..\")`")
    })?;
    let one = |what: &str| match v.args.as_slice() {
        [x] => x.string(),
        _ => Err(d.error(&format!("`Dep::{}` takes one string, the {what}", v.name))),
    };
    Ok(match v.name {
        "path" => {
            v.fields.only(&[])?;
            Source::Path(one("path")?)
        }
        "git" => {
            v.fields.only(&["rev", "tag", "branch"])?;
            let mut refs = Vec::new();
            for k in v.fields.names() {
                let s = v.fields.req(k)?.string()?;
                refs.push(match k {
                    "rev" => GitRef::Rev(s),
                    "tag" => GitRef::Tag(s),
                    _ => GitRef::Branch(s),
                });
            }
            Source::Git {
                url: one("url")?,
                reference: match refs.len() {
                    0 => GitRef::Default,
                    1 => refs.remove(0),
                    _ => return Err(d.error("give at most one of rev, tag, branch")),
                },
            }
        }
        "version" => {
            v.fields.only(&["registry"])?;
            let [r] = v.args.as_slice() else {
                return Err(d.error("`Dep::version` takes one string, the version requirement"));
            };
            Source::Registry {
                req: req(*r)?,
                registry: v.fields.opt("registry").map(|r| r.string()).transpose()?,
            }
        }
        "native" => return Err(d.error(&not_yet("`native` dependencies"))),
        other => {
            return Err(d.error(&format!(
                "unknown dependency kind `Dep::{other}` (expected Dep::path, Dep::git, \
                 Dep::version)"
            )));
        }
    })
}

/// `text` with `field` (`deps` / `dev_deps`) entry `key` set to the
/// RokON text `value`; the rest of the text (comments too) as it was.
pub fn set_dep(
    text: &str,
    file: &str,
    field: &str,
    key: &str,
    value: &str,
) -> Result<String, String> {
    parse(text, file)?;
    let out = edit::set(text, &[Step::Field(field), Step::Key(key)], value)
        .map_err(|e| e.render(text, file))?;
    parse(&out, file).map(|_| out)
}

/// `text` without `field` entry `key`, or `None` when it has none.
pub fn remove_dep(
    text: &str,
    file: &str,
    field: &str,
    key: &str,
) -> Result<Option<String>, String> {
    parse(text, file)?;
    edit::remove(text, &[Step::Field(field), Step::Key(key)]).map_err(|e| e.render(text, file))
}

/// A script's leading block of `//!` lines from a ```` ```rokon ```` line
/// to a ```` ``` ```` line: a `rok.rokon` value, without the `//!`
/// prefixes.
pub fn script_block(src: &str) -> Option<String> {
    let mut lines = src
        .lines()
        .map_while(|l| l.strip_prefix("//!"))
        .map(|l| l.strip_prefix(' ').unwrap_or(l));
    if !lines.by_ref().any(|l| l.trim() == "```rokon") {
        return None;
    }
    let mut out = String::new();
    for l in lines {
        if l.trim() == "```" {
            return Some(out);
        }
        out.push_str(l);
        out.push('\n');
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    const APP: &str = "// the app\nPackage {\n    name: \"app\",\n    toolchain: \"0.3\",\n    \
                       deps: {\n        \"a\": Dep::path(\"../a\"), // local\n        \"b\": \
                       Dep::git(\"u\", tag: \"v1\"),\n    },\n    dev_deps: { \"c\": \
                       Dep::git(\"u2\") },\n}\n";

    #[test]
    fn manifest_forms_and_errors() {
        let m = parse(APP, "rok.rokon").unwrap();
        assert_eq!(m.toolchain.as_deref(), Some("0.3"));
        assert_eq!(m.deps[0].source, Source::Path("../a".into()));
        assert_eq!(
            m.deps[1].source,
            Source::Git {
                url: "u".into(),
                reference: GitRef::Tag("v1".into())
            }
        );
        assert_eq!(m.dev_deps[0].name, "c");
        let m = parse(
            "Package { lints: { \"unused\": \"allow\", \"all\": \"deny\" }, deps: {} }",
            "rok.rokon",
        )
        .unwrap();
        assert_eq!(
            m.lints,
            [
                ("unused".to_owned(), Level::Allow),
                ("all".to_owned(), Level::Deny)
            ]
        );
        assert_eq!(
            parse("Package { name: \"a\\u{62}\" }", "f")
                .unwrap()
                .name
                .as_deref(),
            Some("ab")
        );
        // The root name is optional; `none` is a missing field.
        let m = parse("{ name: \"x\", toolchain: none }", "f").unwrap();
        assert_eq!(m.name.as_deref(), Some("x"));
        assert!(m.toolchain.is_none());
        assert!(parse("{}", "f").unwrap().deps.is_empty());
        for (src, want) in [
            (
                "Package { deps: { \"a\": \"1.0.x.y\" } }",
                "is not a version requirement",
            ),
            (
                "Package { deps: { \"a\": Dep::version(\"1\", tag: \"x\") } }",
                "unknown argument `tag`",
            ),
            (
                "Package { deps: { \"a\": Dep::version() } }",
                "takes one string, the version requirement",
            ),
            (
                "Package { deps: { \"a\": Dep::registry(\"u\") } }",
                "unknown dependency kind `Dep::registry`",
            ),
            (
                "Package { deps: { \"a\": Dep::native(\"z\") } }",
                "`native` dependencies is reserved",
            ),
            ("Package { native: 1 }", "`native` is reserved"),
            ("Package { registry: {} }", "registries is reserved"),
            (
                "Package { deps: { \"My Dep\": Dep::path(\"x\") } }",
                "try `my-dep`",
            ),
            (
                "Package { deps: { \"a-b\": Dep::path(\"x\"), \"a_b\": Dep::path(\"y\") } }",
                "`a_b` and `a-b` are the same package",
            ),
            ("Package { name: \"1x\" }", "starting with a letter"),
            (
                "Package { deps: { \"a\": Dep::git(\"u\", tag: \"t\", rev: \"r\") } }",
                "at most one",
            ),
            (
                "Package { deps: { \"a\": Dep::git(\"u\", sha: \"t\") } }",
                "unknown argument `sha`",
            ),
            (
                "Package { deps: { \"a\": Dep::path(\"p\", tag: \"t\") } }",
                "unknown argument `tag`",
            ),
            (
                "Package { deps: { \"a\": Dep::path() } }",
                "takes one string, the path",
            ),
            (
                "Package { deps: { \"a\": Dep::svn(\"u\") } }",
                "unknown dependency kind `Dep::svn`",
            ),
            ("Package { deps: { \"a\": 1 } }", "found an integer"),
            (
                "Package { deps: { \"a\": Dep::path(\"x\"), \"a\": Dep::path(\"y\") } }",
                "given twice",
            ),
            ("Package { deps: [] }", "`deps` must be a dict"),
            ("Package { edition: \"x\" }", "unknown field `edition`"),
            ("Package { name: \"a\", name: \"b\" }", "given twice"),
            ("Package { name: 1 + 2 }", "operator `+` is not allowed"),
            ("Package { name: x }", "bare identifier `x`"),
            (
                "Package { name: 1 }",
                "`name` must be a string, found an integer",
            ),
            (
                "Package { lints: { \"unused\": \"off\" } }",
                "takes \"allow\"",
            ),
            (
                "Manifest { }",
                "expected `Package { .. }`, found a struct `Manifest",
            ),
            ("Package { } Package { }", "holds one value"),
            ("", "expected a value"),
            ("Package { name: \"x }", "unterminated"),
        ] {
            let e = parse(src, "rok.rokon").unwrap_err();
            assert!(e.contains(want), "{src:?}: {e}");
            assert!(e.contains("--> rok.rokon:1:"), "{e}");
        }
        // The position is the offending token's.
        let e = parse(
            "Package {\n    name: \"a\",\n    edtion: \"x\",\n}",
            "rok.rokon",
        )
        .unwrap_err();
        assert!(
            e.contains("unknown field `edtion`") && e.contains("--> rok.rokon:3:5\n"),
            "{e}"
        );
        let e = parse(APP.replace("tag", "tga").as_str(), "rok.rokon").unwrap_err();
        assert!(
            e.contains("unknown argument `tga`") && e.contains("--> rok.rokon:7:28\n"),
            "{e}"
        );
    }

    #[test]
    fn edits_keep_the_rest() {
        let src = Source::Path("x".into()).to_rok();
        assert_eq!(src, "Dep::path(\"x\")");
        let t = set_dep(APP, "f", "deps", "a", &src).unwrap();
        assert!(t.contains("\"a\": Dep::path(\"x\"), // local\n"), "{t}");
        let t = set_dep("Package {\n    name: \"n\"\n}\n", "f", "deps", "d", &src).unwrap();
        assert_eq!(parse(&t, "f").unwrap().deps[0].name, "d");
        let t = remove_dep(APP, "f", "dev_deps", "c").unwrap().unwrap();
        assert!(parse(&t, "f").unwrap().dev_deps.is_empty());
        assert!(remove_dep(APP, "f", "deps", "zz").unwrap().is_none());
        // An edit that makes a bad manifest is refused.
        assert!(set_dep(APP, "f", "deps", "My.x", &src).is_err());
        // `-` is a package name's, `_` its code name's.
        assert_eq!(code_name("rok-syntax"), "rok_syntax");
        assert!(same("rok-syntax", "Rok_Syntax") && !same("rok-syntax", "roksyntax"));
        let git = Source::Git {
            url: "u".into(),
            reference: GitRef::Branch("b".into()),
        };
        assert_eq!(git.to_rok(), "Dep::git(\"u\", branch: \"b\")");
        let m = parse(
            "{ deps: { \"a\": \"^1.2\", \"b\": Dep::version(\"~0.3\", registry: \"file:///i\") } }",
            "f",
        )
        .unwrap();
        let back: Vec<String> = m.deps.iter().map(|d| d.source.to_rok()).collect();
        assert_eq!(
            back,
            [
                "Dep::version(\"^1.2\")",
                "Dep::version(\"~0.3\", registry: \"file:///i\")"
            ]
        );
    }

    #[test]
    fn script_blocks() {
        let src = "//! ```rokon\n//! Package { deps: {} }\n//! ```\nprintln(\"hi\");\n";
        assert_eq!(script_block(src).as_deref(), Some("Package { deps: {} }\n"));
        assert_eq!(script_block("//! ```rokon\n//! x\nfn main() {}"), None);
        assert_eq!(script_block("println(1);\n//! ```rokon\n//! ```"), None);
        assert_eq!(script_block("//! ```rok\n//! let x = 1;\n//! ```\n"), None);
    }
}

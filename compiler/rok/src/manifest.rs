//! `Rok.toml`: the package manifest (also an environment's), and the
//! `//! ```toml` block of a single-file script.

use std::path::{Path, PathBuf};

use rokc_toml::{Item, Table, Value, render};

pub const MANIFEST: &str = "Rok.toml";
pub const LOCK: &str = "Rok.lock";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GitRef {
    Default,
    Rev(String),
    Tag(String),
    Branch(String),
}

impl GitRef {
    /// `(key, value)` as written in `Rok.toml` / `Rok.lock`.
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
}

impl Source {
    /// The inline-table text for `Rok.toml`.
    pub fn to_toml(&self) -> String {
        let q = |s: &str| rokc_toml::format_value(&Value::String(s.to_owned()));
        match self {
            Self::Path(p) => format!("{{ path = {} }}", q(p)),
            Self::Git { url, reference } => match reference.pair() {
                None => format!("{{ git = {} }}", q(url)),
                Some((k, v)) => format!("{{ git = {}, {k} = {} }}", q(url), q(v)),
            },
        }
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
    pub deps: Vec<Dep>,
    pub dev_deps: Vec<Dep>,
}

/// A dependency name is a top-level name in `use`: an identifier.
pub fn check_name(name: &str) -> Result<(), String> {
    let ok = name
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    if ok {
        Ok(())
    } else {
        Err(format!(
            "`{name}` is not a valid package name: it is imported as `use {name}::..`, so it \
             must be an identifier (letters, digits, `_`){}",
            if name.contains('-') {
                format!("; try `{}`", name.replace('-', "_"))
            } else {
                String::new()
            }
        ))
    }
}

/// `dir/Rok.toml`, if present. A file whose name differs only in case
/// (`rok.toml`) is not the manifest: warn, whatever the file system.
pub fn find(dir: &Path) -> Option<PathBuf> {
    let mut found = None;
    for e in std::fs::read_dir(dir).ok()?.flatten() {
        let name = e.file_name();
        let Some(name) = name.to_str() else { continue };
        if name == MANIFEST {
            found = Some(e.path());
        } else if name.eq_ignore_ascii_case(MANIFEST) {
            eprintln!(
                "rok: warning: ignoring `{}`: the manifest is named `{MANIFEST}`",
                e.path().display()
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

/// Parse manifest text; `file` names it in errors.
pub fn parse(text: &str, file: &str) -> Result<Manifest, String> {
    let root = rokc_toml::parse(text).map_err(|e| e.render(text, file))?;
    let err = |item: &Item, msg: String| render(text, file, item.span, &msg);
    let key_err = |t: &Table, key: &str, msg: String| {
        render(
            text,
            file,
            t.key(key).map(|k| k.span).unwrap_or_default(),
            &msg,
        )
    };
    let mut m = Manifest::default();
    for (k, item) in root.iter() {
        match k.name.as_str() {
            "package" => {
                let t = table(item, "[package]").map_err(|e| err(item, e))?;
                for (pk, v) in t.iter() {
                    let slot = match pk.name.as_str() {
                        "name" => &mut m.name,
                        "version" => &mut m.version,
                        "toolchain" => &mut m.toolchain,
                        "native" => return Err(key_err(t, "native", not_yet("`native`"))),
                        other => {
                            return Err(key_err(
                                t,
                                other,
                                format!(
                                    "unknown key `{other}` in [package] (expected name, version, \
                                     toolchain)"
                                ),
                            ));
                        }
                    };
                    let s = v
                        .value
                        .as_str()
                        .ok_or_else(|| err(v, format!("`{}` must be a string", pk.name)))?;
                    *slot = Some(s.to_owned());
                }
            }
            "deps" => m.deps = deps(text, file, item)?,
            "dev-deps" => m.dev_deps = deps(text, file, item)?,
            "registry" => return Err(key_err(&root, "registry", not_yet("registries"))),
            "native" => return Err(key_err(&root, "native", not_yet("`native`"))),
            other => {
                return Err(key_err(
                    &root,
                    other,
                    format!("unknown key `{other}` (expected [package], [deps], [dev-deps])"),
                ));
            }
        }
    }
    Ok(m)
}

fn not_yet(what: &str) -> String {
    format!("{what} is reserved and not supported yet")
}

fn table<'a>(item: &'a Item, what: &str) -> Result<&'a Table, String> {
    item.value
        .as_table()
        .ok_or_else(|| format!("{what} must be a table"))
}

fn deps(text: &str, file: &str, item: &Item) -> Result<Vec<Dep>, String> {
    let err = |span, msg: &str| render(text, file, span, msg);
    let t = table(item, "a dependency list").map_err(|e| err(item.span, &e))?;
    let mut out = Vec::new();
    for (k, v) in t.iter() {
        check_name(&k.name).map_err(|e| err(k.span, &e))?;
        let Some(spec) = v.value.as_table() else {
            return Err(err(
                v.span,
                &format!(
                    "registry dependencies are not supported yet; write `{} = {{ path = \"..\" }}` \
                     or `{{ git = \"..\" }}`",
                    k.name
                ),
            ));
        };
        let field = |name: &str| -> Result<Option<String>, String> {
            spec.get(name).map_or(Ok(None), |i| {
                i.value
                    .as_str()
                    .map(|s| Some(s.to_owned()))
                    .ok_or_else(|| err(i.span, &format!("`{name}` must be a string")))
            })
        };
        for (sk, _) in spec.iter() {
            match sk.name.as_str() {
                "path" | "git" | "rev" | "tag" | "branch" => {}
                "version" | "registry" => {
                    return Err(err(sk.span, &not_yet("registry dependencies")));
                }
                "native" => return Err(err(sk.span, &not_yet("`native` dependencies"))),
                other => {
                    return Err(err(
                        sk.span,
                        &format!(
                            "unknown key `{other}` (expected path, or git with rev, tag or branch)"
                        ),
                    ));
                }
            }
        }
        let refs: Vec<GitRef> = [
            field("rev")?.map(GitRef::Rev),
            field("tag")?.map(GitRef::Tag),
            field("branch")?.map(GitRef::Branch),
        ]
        .into_iter()
        .flatten()
        .collect();
        let source = match (field("path")?, field("git")?) {
            (Some(p), None) if refs.is_empty() => Source::Path(p),
            (Some(_), None) => {
                return Err(err(v.span, "rev / tag / branch only go with `git`"));
            }
            (None, Some(url)) => Source::Git {
                url,
                reference: match refs.len() {
                    0 => GitRef::Default,
                    1 => refs.into_iter().next().unwrap(),
                    _ => return Err(err(v.span, "give at most one of rev, tag, branch")),
                },
            },
            (Some(_), Some(_)) => return Err(err(v.span, "give `path` or `git`, not both")),
            (None, None) => return Err(err(v.span, "a dependency needs `path` or `git`")),
        };
        out.push(Dep {
            name: k.name.clone(),
            source,
        });
    }
    Ok(out)
}

/// A script's leading block of `//!` lines from a ```` ```toml ```` line to a
/// ```` ``` ```` line: a `Rok.toml` fragment, without the `//!` prefixes.
pub fn script_block(src: &str) -> Option<String> {
    let mut lines = src
        .lines()
        .map_while(|l| l.strip_prefix("//!"))
        .map(|l| l.strip_prefix(' ').unwrap_or(l));
    lines.by_ref().find(|l| l.trim() == "```toml")?;
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

    #[test]
    fn manifest_forms_and_errors() {
        let m = parse(
            "[package]\nname = \"app\"\ntoolchain = \"0.3\"\n[deps]\na = { path = \"../a\" }\n\
             b = { git = \"u\", tag = \"v1\" }\n[dev-deps]\nc = { git = \"u2\" }\n",
            "Rok.toml",
        )
        .unwrap();
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
        for (src, want) in [
            (
                "[deps]\na = \"1.0\"",
                "registry dependencies are not supported yet",
            ),
            ("[deps]\na = { version = \"1\" }", "not supported yet"),
            (
                "[deps]\na = { native = \"z\" }",
                "`native` dependencies is reserved",
            ),
            ("native = 1", "`native` is reserved"),
            ("[registry]", "registries is reserved"),
            ("[deps]\nmy-dep = { path = \"x\" }", "try `my_dep`"),
            (
                "[deps]\na = { git = \"u\", tag = \"t\", rev = \"r\" }",
                "at most one",
            ),
            ("[deps]\na = { path = \"p\", git = \"u\" }", "not both"),
            (
                "[deps]\na = { path = \"p\", tag = \"t\" }",
                "only go with `git`",
            ),
            ("[package]\nedition = \"x\"", "unknown key `edition`"),
            ("[deps]\na = {}", "needs `path` or `git`"),
        ] {
            let e = parse(src, "Rok.toml").unwrap_err();
            assert!(e.contains(want), "{src:?}: {e}");
            assert!(e.starts_with("Rok.toml:"), "{e}");
        }
    }

    #[test]
    fn script_blocks() {
        let src = "//! ```toml\n//! [deps]\n//! a = { path = \"x\" }\n//! ```\nprintln(\"hi\");\n";
        assert_eq!(
            script_block(src).as_deref(),
            Some("[deps]\na = { path = \"x\" }\n")
        );
        assert_eq!(script_block("//! ```toml\n//! [deps]\nfn main() {}"), None);
        assert_eq!(script_block("println(1);\n//! ```toml\n//! ```"), None);
    }
}

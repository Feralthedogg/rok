//! `rok.lock` (RokON): the exact commit (and its content hash) of every git
//! package and stone the build uses. Path packages are not pinned: they
//! are always their current content.

use std::path::Path;

use rokc_rokon::{Doc, Kind, Value};

use crate::manifest::{GitRef, Source};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Locked {
    pub name: String,
    /// A stone's version; `url` is then its registry index
    /// (`Dep::registry(url)`), and `reference` is `Default`.
    pub vers: Option<String>,
    pub url: String,
    pub reference: GitRef,
    pub commit: String,
    /// Git tree hash of the package's files.
    pub tree: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Lock {
    pub packages: Vec<Locked>,
}

impl Lock {
    pub fn find(&self, name: &str) -> Option<&Locked> {
        self.packages
            .iter()
            .find(|p| crate::manifest::same(&p.name, name))
    }

    pub fn read(path: &Path) -> Result<Option<Self>, String> {
        match std::fs::read_to_string(path) {
            Ok(text) => Self::parse(&text, &path.display().to_string()).map(Some),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(format!("cannot read {}: {e}", path.display())),
        }
    }

    pub fn parse(text: &str, file: &str) -> Result<Self, String> {
        let bad = |e: String| format!("{e}\n(delete {file} and run `rok update` to make it again)");
        let doc = Doc::parse(text, file).map_err(bad)?;
        let root = doc.root().record("Lock").map_err(bad)?;
        root.only(&["version", "packages"]).map_err(bad)?;
        let version = root.req("version").and_then(|v| Ok((v, v.int::<u32>()?)));
        match version {
            Ok((_, 1)) => {}
            Ok((v, _)) => return Err(bad(v.error("unsupported lockfile version"))),
            Err(e) => return Err(bad(e)),
        }
        let mut packages = Vec::new();
        let list = root
            .opt("packages")
            .map(|p| p.list())
            .transpose()
            .map_err(bad)?;
        for item in list.unwrap_or_default() {
            let p = item.record("Locked").map_err(bad)?;
            p.only(&["name", "vers", "source", "commit", "tree"])
                .map_err(bad)?;
            let field = |k: &str| p.req(k).and_then(|d| d.string()).map_err(bad);
            let name = field("name")?;
            let source = p.req("source").map_err(bad)?;
            let vers = p.opt("vers").map(|v| v.string()).transpose().map_err(bad)?;
            let registry = source
                .variant("Dep")
                .ok()
                .filter(|v| v.name == "registry")
                .map(|v| match v.args.as_slice() {
                    [u] if v.fields.names().next().is_none() => u.string(),
                    _ => Err(source.error("`Dep::registry` takes one string, the index url")),
                })
                .transpose()
                .map_err(bad)?;
            let (url, reference) = match (registry, &vers) {
                (Some(url), Some(_)) => (url, GitRef::Default),
                (Some(_), None) => return Err(bad(p.req("vers").unwrap_err())),
                (None, None) => match crate::manifest::source(source).map_err(bad)? {
                    Source::Git { url, reference } => (url, reference),
                    _ => {
                        return Err(bad(source.error(
                            "a locked package comes from `Dep::git(..)` or `Dep::registry(..)`",
                        )));
                    }
                },
                (None, Some(_)) => {
                    return Err(bad(
                        p.field_error("vers", "`vers` goes with `Dep::registry(..)`")
                    ));
                }
            };
            packages.push(Locked {
                name,
                vers,
                url,
                reference,
                commit: field("commit")?,
                tree: field("tree")?,
            });
        }
        Ok(Self { packages })
    }

    /// Deterministic text: packages sorted by name, fixed field order.
    pub fn to_text(&self) -> String {
        let mut pkgs: Vec<&Locked> = self.packages.iter().collect();
        pkgs.sort_by(|a, b| a.name.cmp(&b.name));
        let packages = pkgs
            .into_iter()
            .map(|p| {
                let mut fields = vec![("name", Value::str(&p.name))];
                if let Some(v) = &p.vers {
                    fields.push(("vers", Value::str(v)));
                    let src = Value::call("Dep::registry", vec![Value::str(&p.url)], Vec::new());
                    fields.push(("source", src));
                } else {
                    let src = Source::Git {
                        url: p.url.clone(),
                        reference: p.reference.clone(),
                    };
                    fields.push(("source", src.to_value()));
                }
                fields.push(("commit", Value::str(&p.commit)));
                fields.push(("tree", Value::str(&p.tree)));
                Value::record(Some("Locked"), fields)
            })
            .collect();
        let lock = Value::record(
            Some("Lock"),
            vec![
                ("version", Value::new(Kind::Int(1))),
                ("packages", Value::new(Kind::List(packages))),
            ],
        );
        format!(
            "// rok.lock: generated by `rok`; do not edit. Commit it with your sources.\n{}\n",
            rokc_rokon::to_string(&lock)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_sorted() {
        let lock = Lock {
            packages: vec![
                Locked {
                    name: "z".into(),
                    vers: None,
                    url: "file:///z".into(),
                    reference: GitRef::Default,
                    commit: "c1".into(),
                    tree: "t1".into(),
                },
                Locked {
                    name: "a".into(),
                    vers: None,
                    url: "https://x/a.git".into(),
                    reference: GitRef::Branch("main".into()),
                    commit: "c2".into(),
                    tree: "t2".into(),
                },
            ],
        };
        let text = lock.to_text();
        assert!(text.find("name: \"a\"").unwrap() < text.find("name: \"z\"").unwrap());
        let back = Lock::parse(&text, "rok.lock").unwrap();
        assert_eq!(back, lock_sorted(&lock));
        assert_eq!(back.to_text(), text);

        // The documented layout, with real hashes.
        let (c, t) = ("3f2a".repeat(10), "9c1e".repeat(10));
        let one = Lock {
            packages: vec![Locked {
                name: "json".into(),
                vers: None,
                url: "https://example.com/json.git".into(),
                reference: GitRef::Tag("v1.2".into()),
                commit: c.clone(),
                tree: t.clone(),
            }],
        };
        assert_eq!(
            one.to_text(),
            format!(
                "// rok.lock: generated by `rok`; do not edit. Commit it with your sources.\n\
                 Lock {{\n    version: 1,\n    packages: [\n        Locked {{\n            \
                 name: \"json\",\n            source: Dep::git(\"https://example.com/json.git\", \
                 tag: \"v1.2\"),\n            commit: \"{c}\",\n            tree: \"{t}\",\n        \
                 }},\n    ],\n}}\n"
            )
        );
        let stone = Lock {
            packages: vec![Locked {
                name: "geom".into(),
                vers: Some("0.3.1".into()),
                url: "https://github.com/o/rokstones.io-index".into(),
                reference: GitRef::Default,
                commit: c,
                tree: t,
            }],
        };
        let text = stone.to_text();
        assert!(
            text.contains(
                "name: \"geom\",\n            vers: \"0.3.1\",\n            source: \
                 Dep::registry(\"https://github.com/o/rokstones.io-index\"),\n"
            ),
            "{text}"
        );
        assert_eq!(Lock::parse(&text, "rok.lock").unwrap(), stone);
        assert_eq!(
            Lock::default().to_text().lines().nth(1),
            Some("Lock { version: 1, packages: [] }")
        );
        assert_eq!(
            Lock::parse("Lock { version: 1 }", "rok.lock").unwrap(),
            Lock::default()
        );

        for (src, want) in [
            (
                "Lock { version: 2, packages: [] }",
                "rok.lock:1:17: error: unsupported lockfile version",
            ),
            (
                "version = 1",
                "rok.lock:1:9: error: expected the end of the file",
            ),
            ("Lock { packages: [] }", "missing field `version`"),
            (
                "Lock { version: 1, packages: [Locked { name: \"a\", source: Dep::path(\"p\"), \
                 commit: \"c\", tree: \"t\" }] }",
                "a locked package comes from `Dep::git(..)` or `Dep::registry(..)`",
            ),
            (
                "Lock { version: 1, packages: [Locked { name: \"a\", source: Dep::registry(\"u\"), \
                 commit: \"c\", tree: \"t\" }] }",
                "missing field `vers`",
            ),
            (
                "Lock { version: 1, packages: [Locked { name: \"a\", vers: \"1.0.0\", \
                 source: Dep::git(\"u\"), commit: \"c\", tree: \"t\" }] }",
                "`vers` goes with",
            ),
            (
                "Lock { version: 1, packages: [Locked { name: \"a\", source: Dep::git(\"u\") }] }",
                "missing field `commit`",
            ),
        ] {
            let e = Lock::parse(src, "rok.lock").unwrap_err();
            assert!(e.contains(want), "{src}: {e}");
            assert!(e.contains("run `rok update`"), "{e}");
        }
    }

    fn lock_sorted(l: &Lock) -> Lock {
        let mut packages = l.packages.clone();
        packages.sort_by(|a, b| a.name.cmp(&b.name));
        Lock { packages }
    }
}

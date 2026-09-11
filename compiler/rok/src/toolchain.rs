//! Toolchains: `$ROK_HOME/toolchains/<version>/` holds an install
//! (`bin/rokc`, `lib/`). A project pinning `toolchain: "X"` whose
//! version differs from this `rok` runs that toolchain's `rokc`.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::{VERSION, home};

fn rokc_name() -> String {
    format!("rokc{}", std::env::consts::EXE_SUFFIX)
}

/// `pin` (`"0.3"`) accepts `version` (`"0.3"`, `"0.3.1"`).
fn matches(pin: &str, version: &str) -> bool {
    version == pin
        || version
            .strip_prefix(pin)
            .is_some_and(|r| r.starts_with('.'))
}

fn root() -> PathBuf {
    home().join("toolchains")
}

fn installed() -> Vec<String> {
    let mut v: Vec<String> = std::fs::read_dir(root())
        .map(|rd| {
            rd.flatten()
                .filter(|e| e.path().is_dir())
                .filter_map(|e| e.file_name().into_string().ok())
                .filter(|n| !n.starts_with('.'))
                .collect()
        })
        .unwrap_or_default();
    // Numeric order: 0.10 after 0.9.
    v.sort_by_key(|n| {
        n.split('.')
            .map(|p| p.parse::<u64>().unwrap_or(0))
            .collect::<Vec<_>>()
    });
    v
}

/// The `rokc` to run, and the toolchain root to give it as `ROK_HOME`
/// (its `lib/`) when it is a pinned one.
pub fn rokc_for(pin: Option<&str>) -> Result<(PathBuf, Option<PathBuf>), String> {
    match pin {
        Some(p) if !matches(p, VERSION) => {
            let Some(v) = installed().into_iter().rev().find(|v| matches(p, v)) else {
                return Err(format!(
                    "this project pins toolchain {p} (rok.rokon), but this rok is {VERSION} and \
                     {p} is not installed; install it with `rok toolchain install {p} --from \
                     <dir | tarball>`"
                ));
            };
            let dir = root().join(v);
            Ok((dir.join("bin").join(rokc_name()), Some(dir)))
        }
        _ => {
            let exe = std::env::current_exe().map_err(|e| e.to_string())?;
            let rokc = exe.with_file_name(rokc_name());
            if !rokc.is_file() {
                return Err(format!("no `rokc` next to {}", exe.display()));
            }
            Ok((rokc, None))
        }
    }
}

/// Where a toolchain comes from.
enum Origin<'a> {
    Dir(&'a Path),
    Tarball(&'a Path),
}

fn copy_tree(from: &Path, to: &Path) -> Result<(), String> {
    std::fs::create_dir_all(to).map_err(|e| format!("{}: {e}", to.display()))?;
    for e in std::fs::read_dir(from).map_err(|e| format!("{}: {e}", from.display()))? {
        let e = e.map_err(|e| e.to_string())?;
        let (src, dst) = (e.path(), to.join(e.file_name()));
        if src.is_dir() {
            copy_tree(&src, &dst)?;
        } else {
            // `copy` keeps the permission bits (executables stay so).
            std::fs::copy(&src, &dst).map_err(|e| format!("{}: {e}", src.display()))?;
        }
    }
    Ok(())
}

fn install(version: &str, origin: &Origin<'_>) -> Result<PathBuf, String> {
    if version.is_empty()
        || !version
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_'))
    {
        return Err(format!("`{version}` is not a version"));
    }
    let dest = root().join(version);
    if dest.exists() {
        return Err(format!("toolchain {version} is already installed"));
    }
    let tmp = root().join(format!(".tmp-{version}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    let result = (|| {
        match origin {
            Origin::Dir(d) => copy_tree(d, &tmp)?,
            Origin::Tarball(t) => {
                std::fs::create_dir_all(&tmp).map_err(|e| e.to_string())?;
                let ok = Command::new("tar")
                    .arg("-xf")
                    .arg(t)
                    .arg("-C")
                    .arg(&tmp)
                    .status()
                    .map_err(|e| format!("cannot run `tar`: {e}"))?
                    .success();
                if !ok {
                    return Err(format!("cannot unpack {}", t.display()));
                }
            }
        }
        // A tarball holding one top directory: that directory.
        let mut top = tmp.clone();
        if !top.join("bin").is_dir() {
            let entries: Vec<PathBuf> = std::fs::read_dir(&tmp)
                .map_err(|e| e.to_string())?
                .flatten()
                .map(|e| e.path())
                .collect();
            if let [only] = entries.as_slice() {
                top.clone_from(only);
            }
        }
        if !top.join("bin").join(rokc_name()).is_file() {
            return Err("not a rok toolchain: no bin/rokc".to_owned());
        }
        std::fs::rename(&top, &dest).map_err(|e| format!("{}: {e}", dest.display()))
    })();
    let _ = std::fs::remove_dir_all(&tmp);
    result.map(|()| dest)
}

pub fn cmd(args: &[String]) -> Result<i32, String> {
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["list"] => {
            println!("{VERSION} (this rok)");
            for v in installed() {
                println!("{v}");
            }
        }
        ["install", version, rest @ ..] => {
            let from = match rest {
                ["--from", f] => *f,
                [f] if f.starts_with("--from=") => &f[7..],
                _ => {
                    return Err(
                        "usage: rok toolchain install <version> --from <dir | tarball>".into(),
                    );
                }
            };
            let p = Path::new(from);
            let origin = if p.is_dir() {
                Origin::Dir(p)
            } else if p.is_file() {
                Origin::Tarball(p)
            } else {
                return Err(format!("{} does not exist", p.display()));
            };
            std::fs::create_dir_all(root()).map_err(|e| e.to_string())?;
            let dir = install(version, &origin)?;
            eprintln!("   Installed toolchain {version} ({})", dir.display());
        }
        ["remove", version] => {
            let dir = root().join(version);
            if !dir.is_dir() {
                return Err(format!("toolchain {version} is not installed"));
            }
            std::fs::remove_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        }
        _ => {
            return Err(
                "usage: rok toolchain list | install <version> --from <dir | tarball> | remove \
                 <version>"
                    .into(),
            );
        }
    }
    Ok(0)
}

#[cfg(test)]
mod tests {
    #[test]
    fn pins_match_prefixes() {
        assert!(super::matches("0.3", "0.3.1"));
        assert!(super::matches("0.3.1", "0.3.1"));
        assert!(!super::matches("0.3", "0.30.0"));
        assert!(!super::matches("0.3.1", "0.3"));
    }
}

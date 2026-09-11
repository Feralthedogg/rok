//! Package discovery (spec 902.2, 0.3, 4.16.8) and the source-tree walk.

use std::path::{Path, PathBuf};

/// A package to build: a directory holding `main.rok` (executable) or
/// `lib.rok` (library), or a lone file outside any package (the
/// anonymous executable package, 4.16.8).
#[derive(Debug)]
pub struct Package {
    /// `main.rok` / `lib.rok` / the anonymous file.
    pub root: PathBuf,
    pub dir: PathBuf,
    /// Artifact name: the directory name, or the anonymous file's stem.
    pub name: String,
    pub lib: bool,
    pub anonymous: bool,
}

/// The root file name standing for standard input (`check -`, 901.9).
pub const STDIN: &str = "<stdin>";

impl Package {
    /// Source read from stdin: an anonymous package (no file submodules).
    #[must_use]
    pub fn stdin() -> Self {
        Self {
            root: PathBuf::from(STDIN),
            dir: PathBuf::from("."),
            name: "stdin".to_owned(),
            lib: false,
            anonymous: true,
        }
    }

    /// `target/` (spec 902.15); `ROKC_TARGET_DIR` overrides (901.7).
    #[must_use]
    pub fn target_dir(&self) -> PathBuf {
        std::env::var_os("ROKC_TARGET_DIR").map_or_else(|| self.dir.join("target"), PathBuf::from)
    }
}

/// Find the package `path` belongs to: `path` itself when it is a
/// `main.rok` / `lib.rok`, else the nearest directory at or above it
/// holding one (902.2). A file with no such ancestor is anonymous.
pub fn discover(path: &Path) -> Result<Package, String> {
    if !path.exists() {
        return Err(format!("`{}` does not exist", path.display()));
    }
    let abs = std::path::absolute(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let is_file = abs.is_file();
    let start: &Path = if is_file {
        abs.parent().unwrap_or(&abs)
    } else {
        &abs
    };
    let named_root = is_file
        && abs
            .file_name()
            .is_some_and(|n| n == "main.rok" || n == "lib.rok");
    let search: Box<dyn Iterator<Item = &Path>> = if named_root {
        Box::new(std::iter::once(start))
    } else {
        Box::new(start.ancestors())
    };
    for dir in search {
        let main = dir.join("main.rok");
        let lib = dir.join("lib.rok");
        let root = match (main.is_file(), lib.is_file()) {
            (true, true) => {
                return Err(format!(
                    "`{}` has both `main.rok` and `lib.rok`; a package is one or the other \
                     (spec 0.3.1)",
                    shown(dir).display()
                ));
            }
            (true, false) => main,
            (false, true) => lib,
            (false, false) => continue,
        };
        return Ok(Package {
            lib: root.ends_with("lib.rok"),
            root: shown(&root),
            dir: shown(dir),
            name: dir_name(dir),
            anonymous: false,
        });
    }
    if !is_file {
        return Err(format!(
            "no `main.rok` or `lib.rok` in `{}` or any parent directory",
            path.display()
        ));
    }
    Ok(Package {
        root: shown(&abs),
        dir: shown(start),
        name: abs
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("main")
            .to_owned(),
        lib: false,
        anonymous: true,
    })
}

fn dir_name(dir: &Path) -> String {
    dir.file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("main")
        .to_owned()
}

/// Relative to the working directory when under it (diagnostics show
/// `src/main.rok`, not an absolute path).
fn shown(p: &Path) -> PathBuf {
    let cwd = std::env::current_dir().unwrap_or_default();
    match p.strip_prefix(&cwd) {
        Ok(rel) if rel.as_os_str().is_empty() => PathBuf::from("."),
        Ok(rel) => rel.to_path_buf(),
        Err(_) => p.to_path_buf(),
    }
}

/// Every `.rok` and `.rokon` file under `dir`, sorted; `target/` and dot
/// directories are skipped.
#[must_use]
pub fn source_files(dir: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else {
            return;
        };
        for e in rd.flatten() {
            let p = e.path();
            let name = e.file_name();
            let name = name.to_string_lossy();
            if p.is_dir() {
                if name != "target" && !name.starts_with('.') {
                    walk(&p, out);
                }
            } else if p.extension().is_some_and(|x| x == "rok" || x == "rokon") {
                out.push(p);
            }
        }
    }
    let mut out = Vec::new();
    walk(dir, &mut out);
    out.sort();
    out
}

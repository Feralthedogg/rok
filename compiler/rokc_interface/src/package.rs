//! Package discovery (spec 902.2, 0.3, 4.16.8) and the source-tree walk.

use std::path::{Path, PathBuf};

/// A package to build: a directory holding `src/main.rok` (executable),
/// `src/lib.rok` (library) or both, or a lone file outside any package's
/// `src/` (the anonymous executable package, 4.16.8).
#[derive(Clone, Debug)]
pub struct Package {
    /// `src/main.rok` when there, else `src/lib.rok`; or the anonymous
    /// file.
    pub root: PathBuf,
    pub dir: PathBuf,
    /// Artifact name: the directory name, or the anonymous file's stem.
    pub name: String,
    pub lib: bool,
    pub anonymous: bool,
    /// `src/lib.rok` when `root` is `src/main.rok`: the executable uses
    /// that library as dependency `name` (0.3.1).
    pub library: Option<PathBuf>,
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
            library: None,
        }
    }

    /// The library of a package that also has `src/main.rok`.
    #[must_use]
    pub fn library_target(&self) -> Option<Self> {
        Some(Self {
            root: self.library.clone()?,
            lib: true,
            library: None,
            ..self.clone()
        })
    }

    /// `target/` (spec 902.15); `ROKC_TARGET_DIR` overrides (901.7).
    #[must_use]
    pub fn target_dir(&self) -> PathBuf {
        std::env::var_os("ROKC_TARGET_DIR").map_or_else(|| self.dir.join("target"), PathBuf::from)
    }
}

/// Package name `name` as code and symbols spell it: `my-app` is
/// `my_app`.
#[must_use]
pub fn code_name(name: &str) -> String {
    let n: String = name
        .chars()
        .map(|c| if c.is_alphanumeric() { c } else { '_' })
        .collect();
    if n.starts_with(|c: char| c.is_ascii_digit()) {
        format!("_{n}")
    } else {
        n
    }
}

/// The root file of the package at `dir`: `src/main.rok`, else
/// `src/lib.rok` (spec 0.3.1).
#[must_use]
pub fn root_file(dir: &Path) -> Option<PathBuf> {
    ["src/main.rok", "src/lib.rok"]
        .into_iter()
        .map(|f| dir.join(f))
        .find(|f| f.is_file())
}

/// Find the package `path` belongs to: the nearest directory at or
/// above it with `src/main.rok` / `src/lib.rok` (902.2). A file outside
/// that package's `src/` is anonymous.
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
    for dir in start.ancestors() {
        let Some(root) = root_file(dir) else {
            continue;
        };
        if is_file && !abs.starts_with(dir.join("src")) {
            break;
        }
        let lib = root.ends_with("lib.rok");
        let library = Some(dir.join("src/lib.rok")).filter(|l| !lib && l.is_file());
        return Ok(Package {
            lib,
            root: shown(&root),
            dir: shown(dir),
            name: dir_name(dir),
            anonymous: false,
            library: library.as_deref().map(shown),
        });
    }
    if !is_file {
        return Err(format!(
            "no `src/main.rok` or `src/lib.rok` in `{}` or any parent directory",
            path.display()
        ));
    }
    if abs.extension().is_none_or(|x| x != "rok") {
        return Err(format!(
            "`{}` is not a rok source file: rok sources end in `.rok` (spec 1.1.1)",
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
        library: None,
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

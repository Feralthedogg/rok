//! The standard library prebuilt once per toolchain, options and
//! target: its bootstrap tiers as one prebuilt library `rok`
//! (`librok.a` + `rok.rhir`), which builds link instead of compiling
//! the library's concrete code each time.
//!
//! Kept in `rokc_driver::cache_dir()` (the sysroot's `lib/rok-cache/`,
//! or `rok-cache/` beside a repository build of `rokc`), one folder
//! per `<toolchain>-<options>-<sources>` hash: written to a scratch
//! folder and renamed into place, so a folder that exists is complete.
//! A new folder replaces those of other toolchains and of older sources;
//! a failed build leaves `<folder>.failed` instead.

use std::path::{Path, PathBuf};

use rokc_core::hash::{FNV_OFFSET, fnv_add};

use crate::{BuildOptions, Session, rhir, source_files};

/// What the library build depends on besides its sources.
pub struct StdKey<'a> {
    pub bootstrap: &'a [PathBuf],
    pub cfg: &'a [String],
    pub opts: &'a BuildOptions,
    pub target: Option<&'a str>,
    /// `cfg(test)` (a test or bench build).
    pub test: bool,
}

/// A build holding the lock longer than this crashed.
const STALE_LOCK: std::time::Duration = std::time::Duration::from_secs(600);

/// `rok.rhir` of the prebuilt standard library for `key`, built now if
/// missing.
///
/// `None` (compile it from source) when the options rule it out, the
/// cache is not writable, the build fails, or another process is
/// building it.
#[must_use]
pub fn prebuilt_std(key: &StdKey<'_>) -> Option<PathBuf> {
    let o = key.opts;
    let plain = o.repl.is_none()
        && o.mlir_dialect_plugins.is_empty()
        && o.mlir_pass_plugins.is_empty()
        && o.mlir_passes.is_empty();
    // A `--cfg` or `--target` build is rare enough that a library build
    // of its own costs more than it saves.
    if !plain || key.bootstrap.is_empty() || !key.cfg.is_empty() || key.target.is_some() {
        return None;
    }
    let root = rokc_driver::cache_dir()?;
    let hash = |words: &[&[u8]]| {
        let h = words
            .iter()
            .fold(FNV_OFFSET, |h, w| fnv_add(fnv_add(h, w), b"\0"));
        format!("{h:016x}")
    };
    let toolchain = hash(&[rhir::producer().as_bytes()]);
    let options = hash(&[
        o.opt_level.as_bytes(),
        format!("{} {:?} {:?}", o.debug, o.overflow_checks, key.target).as_bytes(),
        // Either backend's objects link with the other's, but a cached
        // library is the backend's own build.
        if rokc_driver::native::chosen(o) {
            b"native".as_slice()
        } else {
            b"llvm".as_slice()
        },
        format!("{} {:?} {:?}", key.test, key.cfg, key.bootstrap).as_bytes(),
    ]);
    let mut sources: Vec<Vec<u8>> = Vec::new();
    for b in key.bootstrap {
        for f in source_files(b.parent().unwrap_or(b)) {
            sources.push(f.display().to_string().into_bytes());
            sources.push(std::fs::read(&f).unwrap_or_default());
        }
    }
    let sources = hash(&sources.iter().map(Vec::as_slice).collect::<Vec<_>>());
    let family = format!("{toolchain}-{options}-");
    let dir = root.join(format!("{family}{sources}"));
    let rhir = dir.join(format!("{}.rhir", rokc_driver::STD_PKG));
    let failed = dir.with_extension("failed");
    if rhir.is_file() {
        return Some(rhir);
    }
    if failed.exists() {
        return None;
    }
    std::fs::create_dir_all(&root).ok()?;
    let lock = root.join(format!("{family}lock"));
    let stale = std::fs::metadata(&lock)
        .and_then(|m| m.modified())
        .is_ok_and(|t| t.elapsed().is_ok_and(|age| age > STALE_LOCK));
    if stale {
        let _ = std::fs::remove_file(&lock);
    }
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&lock)
        .ok()?;
    let built = build(key, &root, &dir);
    if !built {
        // Not tried again until the sources or the toolchain change.
        let _ = std::fs::write(&failed, "");
    }
    // Other toolchains' builds, and this one's of older sources.
    for e in std::fs::read_dir(&root).into_iter().flatten().flatten() {
        let name = e.file_name().to_string_lossy().into_owned();
        let p = e.path();
        let old = !name.starts_with(&toolchain)
            || (name.starts_with(&family) && !name.contains(&sources));
        if old && !name.starts_with('.') {
            let _ = std::fs::remove_dir_all(&p).or_else(|_| std::fs::remove_file(&p));
        }
    }
    let _ = std::fs::remove_file(&lock);
    built.then_some(rhir)
}

/// Build into a scratch folder of `root`, then rename it to `dir`.
fn build(key: &StdKey<'_>, root: &Path, dir: &Path) -> bool {
    let tmp = root.join(format!(".build-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    if std::fs::create_dir_all(&tmp).is_err() {
        return false;
    }
    let mut s = Session::new();
    for b in key.bootstrap {
        s.add_bootstrap_file(b.clone());
    }
    for c in key.cfg {
        s.add_cfg(c.clone());
    }
    if key.test {
        s.add_cfg("test".to_owned());
    }
    s.set_target(key.target);
    s.set_std_lib(true);
    let stub = tmp.join("rok.prebuilt").join("lib.rok");
    let r = s.compile_source("// the prebuilt standard library\n", &stub);
    let archive = tmp.join(format!("lib{}.a", rokc_driver::STD_PKG));
    let ok = !r.has_errors() && r.archive(key.opts, &archive).is_ok();
    // Its files are not the user build's.
    rokc_diagnostic::clear_files();
    if ok && std::fs::rename(&tmp, dir).is_ok() {
        return true;
    }
    let _ = std::fs::remove_dir_all(&tmp);
    // Another process may have put it there first.
    dir.join(format!("{}.rhir", rokc_driver::STD_PKG)).is_file()
}

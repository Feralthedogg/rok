//! Prebuilt dependencies (spec 902.3 / 904): `rok build` / `run` /
//! `test` / `bench` build each dependency once into
//! `target/[<triple>/]<profile>/deps/lib<name>.a` + `<name>.rhir`, and
//! hand rokc the RHIRs. A dependency is rebuilt when its fingerprint
//! (`<name>.fp`: the compiler, the build flags, its sources, and the
//! dependencies built before it) changes.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::resolve::Resolved;

/// rokc flags that change what a dependency compiles to: `(flag, takes a
/// value)`.
const DEP_FLAGS: &[(&str, bool)] = &[
    ("--release", false),
    ("-O0", false),
    ("-O1", false),
    ("-O2", false),
    ("-O3", false),
    ("-Os", false),
    ("-g", false),
    ("--debug", false),
    ("--target", true),
    ("--cfg", true),
    ("--bootstrap", true),
];

/// The dependency-relevant flags of a rokc command line, as `[flag,
/// value]` words (`--x=v` split).
fn dep_flags(args: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--" {
            break;
        }
        let (name, inline) = match a.split_once('=') {
            Some((n, v)) if n.starts_with("--") => (n, Some(v.to_owned())),
            _ => (a.as_str(), None),
        };
        let Some(&(flag, value)) = DEP_FLAGS.iter().find(|(f, _)| *f == name) else {
            continue;
        };
        out.push(flag.to_owned());
        if value {
            if let Some(v) = inline.or_else(|| it.next().cloned()) {
                out.push(v);
            }
        }
    }
    out
}

/// `target/[<triple>/]<profile>/deps` for the package in `pkg_dir`, as
/// rokc lays it out.
fn deps_dir(pkg_dir: &Path, args: &[String], flags: &[String]) -> PathBuf {
    let value_of = |name: &str| {
        let mut it = args.iter();
        while let Some(a) = it.next() {
            if a == "--" {
                break;
            }
            if a == name {
                return it.next().cloned();
            }
            if let Some(v) = a.strip_prefix(name).and_then(|r| r.strip_prefix('=')) {
                return Some(v.to_owned());
            }
        }
        None
    };
    let mut dir = value_of("--target-dir")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("ROKC_TARGET_DIR").map(PathBuf::from))
        .unwrap_or_else(|| pkg_dir.join("target"));
    if let Some(t) = value_of("--target") {
        dir.push(t);
    }
    let release = flags
        .iter()
        .any(|f| matches!(f.as_str(), "--release" | "-O2" | "-O3" | "-Os"));
    dir.join(if release { "release" } else { "debug" })
        .join("deps")
}

/// Every `.rok` / `Rok.toml` under `dir` (not `target/`, not dot
/// directories), sorted.
fn sources(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    for e in rd.flatten() {
        let p = e.path();
        let name = e.file_name().to_string_lossy().into_owned();
        if p.is_dir() {
            if name != "target" && !name.starts_with('.') {
                sources(&p, out);
            }
        } else if p.extension().is_some_and(|x| x == "rok") || name == "Rok.toml" {
            out.push(p);
        }
    }
    out.sort();
}

fn fnv(h: u64, bytes: &[u8]) -> u64 {
    bytes
        .iter()
        .fold(h, |h, &b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
}

/// What a dependency's build depends on.
fn fingerprint(rokc: &Path, flags: &[String], dep: &Resolved, before: &[String]) -> String {
    let mut h = 0xcbf2_9ce4_8422_2325;
    // The compiler: its path, size and mtime (as rokc checks a RHIR's).
    if let Ok(m) = std::fs::metadata(rokc) {
        let t = m
            .modified()
            .ok()
            .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
            .map_or(0, |d| d.as_nanos());
        h = fnv(
            h,
            format!("{}\0{}\0{t}\0", rokc.display(), m.len()).as_bytes(),
        );
    }
    for w in flags.iter().chain(before).chain([&dep.name]) {
        h = fnv(h, w.as_bytes());
        h = fnv(h, b"\0");
    }
    let mut files = Vec::new();
    sources(
        dep.root.parent().unwrap_or_else(|| Path::new(".")),
        &mut files,
    );
    for f in files {
        h = fnv(h, f.display().to_string().as_bytes());
        h = fnv(h, &std::fs::read(&f).unwrap_or_default());
    }
    format!("{h:016x}")
}

/// Dependencies first: `deps` in an order where each package's own
/// dependencies come before it.
fn order(deps: &[Resolved]) -> Vec<&Resolved> {
    fn visit<'a>(d: &'a Resolved, all: &'a [Resolved], out: &mut Vec<&'a Resolved>) {
        if out.iter().any(|o| o.name == d.name) {
            return;
        }
        out.push(d); // cycle guard; moved to its place below
        let at = out.len() - 1;
        for n in &d.deps {
            if let Some(x) = all.iter().find(|x| x.name == *n) {
                visit(x, all, out);
            }
        }
        let me = out.remove(at);
        out.push(me);
    }
    let mut out = Vec::new();
    for d in deps {
        visit(d, deps, &mut out);
    }
    out
}

/// Build (or reuse) every dependency of the package in `pkg_dir` for
/// the rokc command line `args`; `(name, <name>.rhir)` each.
pub fn build(
    rokc: &Path,
    home: Option<&Path>,
    pkg_dir: &Path,
    args: &[String],
    deps: &[Resolved],
    quiet: bool,
) -> Result<Vec<(String, PathBuf)>, String> {
    let flags = dep_flags(args);
    let dir = deps_dir(pkg_dir, args, &flags);
    if !deps.is_empty() {
        std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    }
    let mut built: Vec<(String, PathBuf)> = Vec::new();
    let mut fps: Vec<String> = Vec::new();
    for dep in order(deps) {
        let fp = fingerprint(rokc, &flags, dep, &fps);
        let rhir = dir.join(format!("{}.rhir", dep.name));
        let archive = dir.join(format!("lib{}.a", dep.name));
        let fp_file = dir.join(format!("{}.fp", dep.name));
        let fresh = std::fs::read_to_string(&fp_file).is_ok_and(|old| old == fp)
            && rhir.is_file()
            && archive.is_file();
        if !fresh {
            let _ = std::fs::remove_file(&fp_file);
            let mut c = Command::new(rokc);
            c.arg("build")
                .arg(dep.root.parent().unwrap_or_else(|| Path::new(".")))
                .arg("--name")
                .arg(&dep.name)
                .arg("-o")
                .arg(&archive)
                .args(&flags);
            if quiet {
                c.arg("-q");
            }
            if let Some(h) = home {
                c.env("ROK_HOME", h);
            }
            // The ones before it: its own dependencies, and GC type ids
            // to start after (rokc gives each library its own range).
            for (n, r) in &built {
                c.arg("--extern").arg(format!("{n}={}", r.display()));
            }
            let status = c
                .status()
                .map_err(|e| format!("cannot run {}: {e}", rokc.display()))?;
            if !status.success() {
                return Err(format!("could not build dependency `{}`", dep.name));
            }
            std::fs::write(&fp_file, &fp).map_err(|e| format!("{}: {e}", fp_file.display()))?;
        }
        fps.push(fp);
        built.push((dep.name.clone(), rhir));
    }
    Ok(built)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dependencies_come_first() {
        let r = |n: &str, deps: &[&str]| Resolved {
            name: n.into(),
            root: PathBuf::new(),
            dev: false,
            deps: deps.iter().map(|d| (*d).to_owned()).collect(),
        };
        let all = [r("a", &[]), r("b", &["a", "c"]), r("c", &["a"])];
        // root → b → a, c: BFS order is b, a, c; c needs a.
        let all = [all[1].clone(), all[0].clone(), all[2].clone()];
        let names: Vec<&str> = order(&all).iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, ["a", "c", "b"]);
        let flags = dep_flags(&["--release".into(), "--cfg=x".into(), "-v".into()]);
        assert_eq!(flags, ["--release", "--cfg", "x"]);
    }
}

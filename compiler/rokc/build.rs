// `ROK_COMMIT_INFO` (` (<commit> <date>)` when built from a git
// checkout, else `ROK_COMMIT_HASH` / `ROK_COMMIT_DATE` if set, else
// empty) and `ROK_HOST` (the target triple) for `--version`. `rok`
// includes this file as its own build script.

use std::process::Command;

fn git(args: &[&str]) -> Option<String> {
    let out = Command::new("git").args(args).output().ok()?;
    let s = String::from_utf8(out.stdout).ok()?;
    (out.status.success() && !s.trim().is_empty()).then(|| s.trim().to_owned())
}

fn main() {
    let env = |k: &str| std::env::var(k).ok().filter(|v| !v.is_empty());
    println!("cargo:rerun-if-env-changed=ROK_COMMIT_HASH");
    println!("cargo:rerun-if-env-changed=ROK_COMMIT_DATE");
    println!("cargo:rerun-if-changed=build.rs");
    // A new commit moves HEAD or the branch it names (a missing file
    // would rerun this every build).
    let branch = git(&["symbolic-ref", "-q", "HEAD"]);
    for p in ["HEAD", "packed-refs"].into_iter().chain(branch.as_deref()) {
        if let Some(f) = git(&["rev-parse", "--git-path", p]) {
            if std::path::Path::new(&f).exists() {
                println!("cargo:rerun-if-changed={f}");
            }
        }
    }
    let hash = env("ROK_COMMIT_HASH").or_else(|| git(&["rev-parse", "--short=9", "HEAD"]));
    let date = env("ROK_COMMIT_DATE").or_else(|| git(&["log", "-1", "--format=%cs"]));
    let info = match (hash, date) {
        (Some(h), Some(d)) => format!(" ({h} {d})"),
        (Some(h), None) => format!(" ({h})"),
        _ => String::new(),
    };
    println!("cargo:rustc-env=ROK_COMMIT_INFO={info}");
    println!(
        "cargo:rustc-env=ROK_HOST={}",
        std::env::var("TARGET").unwrap_or_default()
    );
    // rokc exports what rokc_llvm lists (MLIR and LLVM's support
    // library), so MLIR plugins built with those symbols undefined bind
    // to rokc's own; the linker strips the rest. A plugin DLL links
    // rokc.exe's import library instead (rokc_llvm's `plugin_dev`). No
    // list: no LLVM.
    if std::env::var("CARGO_PKG_NAME").as_deref() == Ok("rokc") {
        println!("cargo:rerun-if-env-changed=DEP_ROKC_LLVM_EXPORTS");
        println!("cargo:rerun-if-env-changed=DEP_ROKC_LLVM_PLUGIN_DEV");
        println!("cargo:rerun-if-env-changed=DEP_ROKC_LLVM_PREFIX");
        if let Ok(list) = std::env::var("DEP_ROKC_LLVM_EXPORTS") {
            let link = |flag: String| println!("cargo:rustc-link-arg-bin=rokc={flag}");
            if std::env::var("CARGO_CFG_TARGET_ENV").as_deref() == Ok("msvc") {
                let dev = std::env::var("DEP_ROKC_LLVM_PLUGIN_DEV").unwrap();
                link(format!("/DEF:{list}"));
                link(format!("/IMPLIB:{dev}/lib/rokc.lib"));
            } else {
                // The prefix's lld, for identical code folding (link.exe
                // folds under rustc's /OPT:REF,ICF): MLIR's and LLVM's
                // template instances fold by the thousand.
                let bin = format!("{}/bin", std::env::var("DEP_ROKC_LLVM_PREFIX").unwrap());
                if std::env::var("CARGO_CFG_TARGET_VENDOR").as_deref() == Ok("apple") {
                    link(format!("-fuse-ld={bin}/ld64.lld"));
                    link(format!("-Wl,-exported_symbols_list,{list}"));
                } else {
                    link(format!("-B{bin}"));
                    link("-fuse-ld=lld".into());
                    link(format!("-Wl,--dynamic-list={list}"));
                }
                link("-Wl,--icf=safe".into());
            }
        }
    }
}

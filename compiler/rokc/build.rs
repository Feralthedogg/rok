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
    // to rokc's own; the linker strips the rest. No list: no LLVM.
    if std::env::var("CARGO_PKG_NAME").as_deref() == Ok("rokc") {
        println!("cargo:rerun-if-env-changed=DEP_ROKC_LLVM_EXPORTS");
        if let Ok(list) = std::env::var("DEP_ROKC_LLVM_EXPORTS") {
            let flag = if std::env::var("CARGO_CFG_TARGET_VENDOR").as_deref() == Ok("apple") {
                format!("-Wl,-exported_symbols_list,{list}")
            } else {
                format!("-Wl,--dynamic-list={list}")
            };
            println!("cargo:rustc-link-arg-bin=rokc={flag}");
        }
    }
}

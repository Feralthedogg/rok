//! The REPL's session host (`src/repl_host.c`) as an object, linked
//! with the runtime when a session starts. Empty where the host does not
//! run (it maps Mach-O arm64 cells).

use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=src/repl_host.c");
    println!("cargo:rerun-if-env-changed=CC");
    let out = PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("repl_host.o");
    let host = std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos")
        && std::env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("aarch64");
    if !host {
        std::fs::write(&out, []).unwrap();
        return;
    }
    let cc = std::env::var_os("CC").unwrap_or_else(|| "cc".into());
    let status = Command::new(&cc)
        .args([
            "-O2",
            "-mmacosx-version-min=11.0",
            "-c",
            "src/repl_host.c",
            "-o",
        ])
        .arg(&out)
        .status()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", cc.to_string_lossy()));
    assert!(status.success(), "compiling src/repl_host.c failed");
}

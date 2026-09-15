//! The REPL's session host (`src/repl_host.c`) as an object, linked
//! with the runtime when a session starts. Empty where the host does not
//! run (it loads Mach-O / ELF / COFF objects of arm64 / `x86_64`:
//! `REPL_HOST`). Windows: compiled by clang (`CC`) without the Windows
//! SDK or MSVC headers.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=src/repl_host.c");
    println!("cargo:rerun-if-env-changed=CC");
    println!("cargo:rustc-check-cfg=cfg(rok_repl_host)");
    let out = PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("repl_host.o");
    let os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let flags: &[&str] = match (os.as_str(), arch.as_str()) {
        ("macos", "aarch64") => &["-arch", "arm64", "-mmacosx-version-min=11.0"],
        ("macos", "x86_64") => &["-arch", "x86_64", "-mmacosx-version-min=11.0"],
        // Linked into a PIE.
        ("linux", "aarch64" | "x86_64") => &["-fPIC"],
        // No C++ thread-local initialization guards (no MSVC CRT).
        ("windows", "aarch64") => &[
            "--target=aarch64-pc-windows-msvc",
            "-ffreestanding",
            "-fno-ms-tls-guards",
        ],
        ("windows", "x86_64") => &[
            "--target=x86_64-pc-windows-msvc",
            "-ffreestanding",
            "-fno-ms-tls-guards",
        ],
        _ => {
            std::fs::write(&out, []).unwrap();
            return;
        }
    };
    let cc = std::env::var_os("CC")
        .unwrap_or_else(|| if os == "windows" { "clang" } else { "cc" }.into());
    let status = Command::new(&cc)
        .args(flags)
        .args(["-O2", "-c", "src/repl_host.c", "-o"])
        .arg(&out)
        .status()
        .unwrap_or_else(|e| panic!("cannot run {}: {e}", cc.to_string_lossy()));
    assert!(status.success(), "compiling src/repl_host.c failed");
    println!("cargo:rustc-cfg=rok_repl_host");
}

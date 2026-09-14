//! Links the pinned LLVM / MLIR / lld static libraries and the C++ shim
//! over them.
//!
//! The prefix is `ROK_LLVM_PREFIX`, else the default of `llvm/build.sh`
//! (`$ROK_LLVM_CACHE/llvm-<version>`, `~/.cache/rok`). Without one the
//! crate builds its stub (`cfg(rok_llvm)` unset): every entry point
//! returns an error. A `ROK_LLVM_PREFIX` that is not a usable prefix is a
//! build error.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Must match `VERSION` in `llvm/build.sh`.
const LLVM_VERSION: &str = "22.1.8";

fn main() {
    println!("cargo:rustc-check-cfg=cfg(rok_llvm)");
    println!("cargo:rerun-if-changed=src/shim.cpp");
    for v in ["ROK_LLVM_PREFIX", "ROK_LLVM_CACHE", "XDG_CACHE_HOME", "CXX"] {
        println!("cargo:rerun-if-env-changed={v}");
    }
    let explicit = env::var_os("ROK_LLVM_PREFIX").filter(|p| !p.is_empty());
    let prefix = explicit.clone().map(PathBuf::from).or_else(default_prefix);
    // Rebuilt once the prefix appears: watch its nearest existing ancestor.
    if let Some(dir) = prefix
        .as_deref()
        .and_then(|p| p.ancestors().find(|a| a.exists()))
    {
        println!("cargo:rerun-if-changed={}", dir.display());
    }
    let Some(prefix) = prefix.filter(|p| usable(p)) else {
        assert!(
            explicit.is_none(),
            "ROK_LLVM_PREFIX={} has no LLVM {LLVM_VERSION} with MLIR and lld \
             (build one with llvm/build.sh)",
            Path::new(&explicit.unwrap_or_default()).display()
        );
        return;
    };
    println!("cargo:rustc-cfg=rok_llvm");
    println!("cargo:prefix={}", prefix.display());

    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let apple = env::var("CARGO_CFG_TARGET_VENDOR").as_deref() == Ok("apple");
    compile_shim(&prefix, &out, apple);
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static=rokc_llvm_shim");

    // Users before what they use: lld, then MLIR, then LLVM. Not bundled
    // into the rlib (-bundle): the archives go to the final link as they
    // are.
    let lib = prefix.join("lib");
    println!("cargo:rustc-link-search=native={}", lib.display());
    let mut names: Vec<String> = std::fs::read_dir(&lib)
        .unwrap()
        .filter_map(|e| {
            let n = e.ok()?.file_name().into_string().ok()?;
            let n = n.strip_prefix("lib")?.strip_suffix(".a")?.to_owned();
            ["lld", "MLIR", "LLVM"]
                .iter()
                .any(|p| n.starts_with(p))
                .then_some(n)
        })
        .collect();
    names.sort_by_key(|n| {
        (
            ["lld", "MLIR", "LLVM"]
                .iter()
                .position(|p| n.starts_with(p)),
            n.clone(),
        )
    });
    for n in &names {
        println!("cargo:rustc-link-lib=static:-bundle={n}");
    }
    if apple {
        println!("cargo:rustc-link-lib=dylib=c++");
        // dsymutil writes the dSYM bundle's Info.plist with it.
        println!("cargo:rustc-link-lib=framework=CoreFoundation");
    } else {
        for l in ["stdc++", "m", "dl", "pthread", "rt"] {
            println!("cargo:rustc-link-lib=dylib={l}");
        }
    }
}

fn default_prefix() -> Option<PathBuf> {
    let cache = env::var_os("ROK_LLVM_CACHE")
        .filter(|p| !p.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            env::var_os("XDG_CACHE_HOME")
                .filter(|p| !p.is_empty())
                .map(|c| PathBuf::from(c).join("rok"))
        })
        .or_else(|| env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache/rok")))?;
    Some(cache.join(format!("llvm-{LLVM_VERSION}")))
}

/// A prefix of the pinned LLVM with MLIR and lld static libraries.
fn usable(prefix: &Path) -> bool {
    let version = std::fs::read_to_string(prefix.join("include/llvm/Config/llvm-config.h"))
        .unwrap_or_default();
    version.contains(&format!("#define LLVM_VERSION_STRING \"{LLVM_VERSION}"))
        && prefix.join("lib/libMLIRIR.a").is_file()
        && prefix.join("lib/liblldMachO.a").is_file()
        && prefix.join("include/lld/Common/Driver.h").is_file()
        && prefix.join("share/rok/dsymutil/Options.inc").is_file()
}

/// The shim and dsymutil's sources (`llvm/build.sh` keeps them in
/// `share/rok/dsymutil`), compiled in parallel into one archive.
fn compile_shim(prefix: &Path, out: &Path, apple: bool) {
    let dsym = prefix.join("share/rok/dsymutil");
    let mut sources = vec![PathBuf::from("src/shim.cpp")];
    sources.extend(
        std::fs::read_dir(&dsym)
            .unwrap()
            .filter_map(|e| Some(e.ok()?.path()))
            .filter(|p| p.extension().is_some_and(|x| x == "cpp")),
    );
    println!("cargo:rerun-if-changed={}", dsym.display());
    let objs: Vec<PathBuf> = std::thread::scope(|s| {
        // Collect first so every compile starts before any join.
        #[allow(clippy::needless_collect)]
        let jobs: Vec<_> = sources
            .iter()
            .map(|src| {
                let obj = out.join(src.file_stem().unwrap()).with_extension("o");
                let dsym = &dsym;
                s.spawn(move || {
                    let cxx = env::var_os("CXX").unwrap_or_else(|| "c++".into());
                    let mut cmd = Command::new(cxx);
                    cmd.args([
                        "-std=c++17",
                        "-O2",
                        "-DNDEBUG",
                        "-fno-rtti",
                        "-fno-exceptions",
                        "-fPIC",
                        "-fvisibility-inlines-hidden",
                        "-w",
                        "-c",
                    ])
                    .arg(src)
                    .arg(format!("-I{}", prefix.join("include").display()))
                    .arg(format!("-I{}", dsym.display()))
                    .arg("-o")
                    .arg(&obj);
                    if apple {
                        cmd.arg("-mmacosx-version-min=11.0");
                    }
                    run(&mut cmd);
                    obj
                })
            })
            .collect();
        jobs.into_iter().map(|j| j.join().unwrap()).collect()
    });
    let archive = out.join("librokc_llvm_shim.a");
    let _ = std::fs::remove_file(&archive);
    run(Command::new("ar").arg("crs").arg(&archive).args(&objs));
}

fn run(cmd: &mut Command) {
    let status = cmd
        .status()
        .unwrap_or_else(|e| panic!("cannot run {cmd:?}: {e}"));
    assert!(status.success(), "{cmd:?} failed");
}

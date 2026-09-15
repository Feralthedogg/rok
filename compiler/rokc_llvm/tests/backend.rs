//! The in-process backend on small MLIR / LLVM IR modules. Skipped when
//! the crate is built without LLVM.

use std::io::Write as _;
#[cfg(target_vendor = "apple")]
use std::path::PathBuf;
#[cfg(target_vendor = "apple")]
use std::process::Command;

use rokc_llvm::{Compile, Emit, OptLevel, Target};

fn skip() -> bool {
    if !rokc_llvm::AVAILABLE {
        let _ = writeln!(
            std::io::stderr(),
            "\n!!!!!!!! SKIPPED: rokc_llvm built without LLVM !!!!!!!!\n"
        );
    }
    !rokc_llvm::AVAILABLE
}

#[cfg(target_vendor = "apple")]
fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("rokc-llvm-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

const fn opts<'a>(t: &'a Target, opt: OptLevel, emit: Emit, pipeline: &'a str) -> Compile<'a> {
    Compile {
        target: t,
        opt,
        emit,
        tls_initial_exec: true,
        mlir_pipeline: pipeline,
        dialect_plugins: &[],
        pass_plugins: &[],
        profile: rokc_llvm::Profile::None,
    }
}

#[cfg(target_vendor = "apple")]
const HELLO_MLIR: &str = r#"
module {
  llvm.mlir.global internal constant @msg("hello from rokc_llvm\00") : !llvm.array<21 x i8>
  llvm.func @puts(!llvm.ptr) -> i32
  func.func @twice(%x: i32) -> i32 {
    %r = arith.addi %x, %x : i32
    return %r : i32
  }
  func.func @main() -> i32 {
    %p = llvm.mlir.addressof @msg : !llvm.ptr
    %0 = llvm.call @puts(%p) : (!llvm.ptr) -> i32
    %c = arith.constant 21 : i32
    %r = call @twice(%c) : (i32) -> i32
    return %r : i32
  }
}
"#;

const ADD_LL: &str = "define i32 @add(i32 %a, i32 %b) {\n  %r = add i32 %a, %b\n  ret i32 %r\n}\n";

#[test]
fn llvm_ir_to_objects_for_every_target() {
    if skip() {
        return;
    }
    let magic: &[(&str, &[u8])] = &[
        ("arm64-apple-macosx11.0", &[0xcf, 0xfa, 0xed, 0xfe]),
        ("x86_64-apple-macosx11.0", &[0xcf, 0xfa, 0xed, 0xfe]),
        ("x86_64-unknown-linux-gnu", b"\x7fELF"),
        ("aarch64-unknown-linux-gnu", b"\x7fELF"),
        ("armv7-unknown-linux-gnueabihf", b"\x7fELF"),
        ("riscv64-unknown-linux-gnu", b"\x7fELF"),
        ("wasm32-unknown-unknown", b"\0asm"),
        ("x86_64-pc-windows-msvc", &[0x64, 0x86]),
    ];
    for (triple, m) in magic {
        let t = Target::new(triple);
        for opt in [OptLevel::O0, OptLevel::O2] {
            let obj = rokc_llvm::compile_llvm_ir(ADD_LL, &opts(&t, opt, Emit::Obj, ""))
                .unwrap_or_else(|e| panic!("{triple}: {e}"));
            assert!(obj.starts_with(m), "{triple}: not an object");
        }
        let asm =
            rokc_llvm::compile_llvm_ir(ADD_LL, &opts(&t, OptLevel::O2, Emit::Asm, "")).unwrap();
        assert!(String::from_utf8(asm).unwrap().contains("add"), "{triple}");
        assert!(!rokc_llvm::data_layout(&t).unwrap().is_empty(), "{triple}");
    }
}

#[test]
fn data_layout_is_clangs() {
    if skip() {
        return;
    }
    let t = Target::new("arm64-apple-macosx11.0");
    assert_eq!(
        rokc_llvm::data_layout(&t).unwrap(),
        "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
    );
    let t = Target::new("x86_64-unknown-linux-gnu");
    assert_eq!(
        rokc_llvm::data_layout(&t).unwrap(),
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
    );
}

#[test]
fn mlir_lowers_to_llvm_ir_with_initial_exec_tls() {
    if skip() {
        return;
    }
    let src = "module {\n  llvm.mlir.global external thread_local @rok_tls_flag() : i8\n  \
               llvm.mlir.global external thread_local @other() : i8\n}\n";
    let t = Target::host();
    let p = rokc_llvm::mlir_pipeline(false, &[]);
    let ll = rokc_llvm::compile_mlir(src, &opts(&t, OptLevel::O0, Emit::LlvmIr, &p)).unwrap();
    let ll = String::from_utf8(ll).unwrap();
    assert!(ll.starts_with("; ModuleID = 'LLVMDialectModule'"), "{ll}");
    assert!(
        ll.contains("@rok_tls_flag = external thread_local(initialexec) global i8"),
        "{ll}"
    );
    assert!(
        ll.contains("@other = external thread_local global i8"),
        "{ll}"
    );
}

#[test]
fn mlir_errors_are_reported() {
    if skip() {
        return;
    }
    let t = Target::host();
    let p = rokc_llvm::mlir_pipeline(true, &[]);
    let e = rokc_llvm::compile_mlir(
        "module { func.func @f() -> i32 { return } }",
        &opts(&t, OptLevel::O0, Emit::Obj, &p),
    )
    .unwrap_err();
    assert!(e.contains("<stdin>:1:") && e.contains("error"), "{e}");
    let e = rokc_llvm::compile_mlir(
        "module {}",
        &opts(&t, OptLevel::O0, Emit::Obj, "no-such-pass"),
    )
    .unwrap_err();
    assert!(e.contains("no-such-pass"), "{e}");
    let e = rokc_llvm::compile_llvm_ir("define i32 @f( {", &opts(&t, OptLevel::O0, Emit::Obj, ""))
        .unwrap_err();
    assert!(e.contains("error"), "{e}");
}

#[test]
#[cfg(target_vendor = "apple")]
fn mlir_hello_links_and_runs() {
    if skip() {
        return;
    }
    let dir = scratch("hello");
    let host = Target::host();
    for (opt, optimize) in [
        (OptLevel::O0, false),
        (OptLevel::O2, true),
        (OptLevel::Os, true),
    ] {
        let p = rokc_llvm::mlir_pipeline(optimize, &[]);
        let obj = rokc_llvm::compile_mlir(HELLO_MLIR, &opts(&host, opt, Emit::Obj, &p)).unwrap();
        let o = dir.join("hello.o");
        std::fs::write(&o, obj).unwrap();
        // Through an archive, as a library build hands it to the link.
        let a = dir.join("libhello.a");
        let _ = std::fs::remove_file(&a);
        rokc_llvm::write_archive(&host, &a, &[&o]).unwrap();
        let exe = dir.join("hello");
        let l = format!("-L{}", dir.display());
        rokc_llvm::link_executable(&host, &[l.as_str(), "-lhello"], &exe, true, None).unwrap();
        let run = Command::new(&exe).output().unwrap();
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            "hello from rokc_llvm\n"
        );
        assert_eq!(run.status.code(), Some(42));
    }
    let e = rokc_llvm::link_executable(&host, &["-lno_such_lib_xyz"], &dir.join("x"), true, None)
        .unwrap_err();
    assert!(e.contains("no_such_lib_xyz"), "{e}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
#[cfg(target_vendor = "apple")]
fn split_objects_link_and_dsymutil_bundles_them() {
    if skip() {
        return;
    }
    let dir = scratch("split");
    let host = Target::host();
    let p = rokc_llvm::mlir_pipeline(true, &[]);
    let parts =
        rokc_llvm::compile_mlir_split(HELLO_MLIR, &opts(&host, OptLevel::O2, Emit::Obj, &p), 3)
            .unwrap()
            .0;
    assert_eq!(parts.len(), 3);
    let mut objs = Vec::new();
    for (i, o) in parts.iter().enumerate() {
        let path = dir.join(format!("part{i}.o"));
        std::fs::write(&path, o).unwrap();
        objs.push(path);
    }
    let exe = dir.join("split");
    rokc_llvm::link_executable(&host, &objs, &exe, true, None).unwrap();
    let run = Command::new(&exe).output().unwrap();
    assert_eq!(run.status.code(), Some(42));
    rokc_llvm::dsymutil(&[exe.as_os_str()]).unwrap();
    assert!(dir.join("split.dSYM/Contents/Info.plist").is_file());
    let _ = std::fs::remove_dir_all(&dir);
}

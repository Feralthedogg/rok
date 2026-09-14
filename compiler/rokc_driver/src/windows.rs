//! Windows (`*-pc-windows-msvc`) executables without the MSVC tools or a
//! Windows SDK: import libraries built in process from the mingw-w64
//! module definitions embedded here (`windows/<arch>/*.def`, `gen.sh`),
//! rok's own C runtime startup over the UCRT (`ucrtbase.dll`), and
//! lld-link's options. No MSVC static library is linked.

use std::ffi::OsString;
use std::path::Path;

/// `(link name, module definition)`, the UCRT first: `ntdll` repeats some
/// C functions, and the first import library that has a symbol wins.
type Defs = [(&'static str, &'static str); 11];

macro_rules! defs {
    ($arch:literal) => {
        defs!($arch; "ucrtbase" "kernel32" "synchronization" "ws2_32" "advapi32" "bcrypt"
            "userenv" "shell32" "ole32" "user32" "ntdll")
    };
    ($arch:literal; $($name:literal)*) => {
        [$(($name, include_str!(concat!("../windows/", $arch, "/", $name, ".def")))),*]
    };
}

const X86_64: Defs = defs!("x86_64");
const AARCH64: Defs = defs!("aarch64");

/// `-C subsystem=console|windows` (`/SUBSYSTEM`): a console program's
/// entry is `mainCRTStartup`, a GUI program's `WinMainCRTStartup`, which
/// calls `WinMain` (spec 9.5.9).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Subsystem {
    #[default]
    Console,
    Windows,
}

impl Subsystem {
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "console" => Some(Self::Console),
            "windows" => Some(Self::Windows),
            _ => None,
        }
    }
}

fn defs(t: &rokc_llvm::Target) -> Result<&'static Defs, String> {
    match t.triple.split('-').next() {
        Some("x86_64") => Ok(&X86_64),
        Some("aarch64" | "arm64") => Ok(&AARCH64),
        _ => Err(format!("no Windows libraries for {}", t.triple)),
    }
}

/// What a Windows executable links besides its objects and archives, as
/// lld-link arguments: the startup object and the import libraries
/// (written into `dir`), `#[link]` libraries the embedded set lacks
/// (`<name>.lib` on the library path), the subsystem and entry point,
/// and `/debug` (a PDB from the objects' `CodeView`) with `debug`.
pub fn link_args(
    t: &rokc_llvm::Target,
    native_libs: &[(String, bool)],
    subsystem: Subsystem,
    debug: bool,
    dir: &Path,
) -> Result<Vec<OsString>, String> {
    let defs = defs(t)?;
    let startup = dir.join("rok_startup.obj");
    let obj = rokc_llvm::compile_llvm_ir(
        &startup_ir(t, subsystem),
        &rokc_llvm::Compile {
            target: t,
            opt: rokc_llvm::OptLevel::O2,
            emit: rokc_llvm::Emit::Obj,
            tls_initial_exec: false,
            mlir_pipeline: "",
            dialect_plugins: &[],
            pass_plugins: &[],
        },
    )?;
    std::fs::write(&startup, obj).map_err(|e| format!("{}: {e}", startup.display()))?;
    let mut a = vec![startup.into_os_string()];
    for (name, _) in native_libs {
        if !defs.iter().any(|(n, _)| n.eq_ignore_ascii_case(name)) {
            a.push(format!("{name}.lib").into());
        }
    }
    for (name, def) in defs {
        let lib = dir.join(format!("{name}.lib"));
        rokc_llvm::import_library(t, def, &lib)?;
        a.push(lib.into_os_string());
    }
    let (sub, entry) = match subsystem {
        Subsystem::Console => ("console", "mainCRTStartup"),
        Subsystem::Windows => ("windows", "WinMainCRTStartup"),
    };
    a.push(format!("/subsystem:{sub}").into());
    a.push(format!("/entry:{entry}").into());
    // Nothing refers to the TLS directory but the loader.
    a.push("/include:_tls_used".into());
    if debug {
        a.push("/debug".into());
    }
    Ok(a)
}

/// rok's C runtime startup, in place of the MSVC CRT's static parts: the
/// entry point (UCRT setup, the program's `main` wrapper, `exit`), the
/// TLS directory the loader reads (`_tls_used`; thread-locals are in
/// `.tls$`), `_fltused` (referenced by code using floating point) and
/// `__chkstk` (the stack probe LLVM calls for frames of a page or more).
fn startup_ir(t: &rokc_llvm::Target, subsystem: Subsystem) -> String {
    let arm64 = !t.triple.starts_with("x86_64");
    let chkstk = if arm64 {
        // x15: the frame size / 16. Touches each page below sp; keeps
        // every register but x16 / x17.
        r#"module asm ".text"
module asm ".globl __chkstk"
module asm ".p2align 2"
module asm "__chkstk:"
module asm "  lsl x16, x15, #4"
module asm "  mov x17, sp"
module asm "1:"
module asm "  sub x17, x17, #4096"
module asm "  subs x16, x16, #4096"
module asm "  ldr xzr, [x17]"
module asm "  b.gt 1b"
module asm "  ret"
"#
    } else {
        // rax: the frame size. Touches each page below the caller's rsp;
        // keeps every register.
        r#"module asm ".text"
module asm ".globl __chkstk"
module asm ".p2align 4"
module asm "__chkstk:"
module asm "  push %rcx"
module asm "  push %rax"
module asm "  cmp $0x1000, %rax"
module asm "  lea 24(%rsp), %rcx"
module asm "  jb 1f"
module asm "2:"
module asm "  sub $0x1000, %rcx"
module asm "  test %rcx, (%rcx)"
module asm "  sub $0x1000, %rax"
module asm "  cmp $0x1000, %rax"
module asm "  ja 2b"
module asm "1:"
module asm "  sub %rax, %rcx"
module asm "  test %rcx, (%rcx)"
module asm "  pop %rax"
module asm "  pop %rcx"
module asm "  ret"
"#
    };
    // `_set_app_type`: 1 console, 2 GUI.
    let entry = match subsystem {
        Subsystem::Console => {
            r"define void @mainCRTStartup() {
  call void @_set_app_type(i32 1)
  %a = call i32 @_configure_narrow_argv(i32 1)
  %e = call i32 @_initialize_narrow_environment()
  %r = call i32 @main()
  call void @exit(i32 %r)
  unreachable
}
"
        }
        // rok's WinMain ignores lpCmdLine (the runtime reads
        // the command line itself), so it gets "".
        Subsystem::Windows => {
            r"@__ImageBase = external global i8
@empty = private constant [1 x i8] zeroinitializer

define void @WinMainCRTStartup() {
  call void @_set_app_type(i32 2)
  %a = call i32 @_configure_narrow_argv(i32 1)
  %e = call i32 @_initialize_narrow_environment()
  %r = call i32 @WinMain(ptr @__ImageBase, ptr null, ptr @empty, i32 10)
  call void @exit(i32 %r)
  unreachable
}

define i32 @WinMain(ptr %instance, ptr %prev, ptr %cmd, i32 %show) {
  %r = call i32 @main()
  ret i32 %r
}
"
        }
    };
    format!(
        r#"{chkstk}
@_tls_index = global i32 0
@_tls_start = global i8 0, section ".tls"
@_tls_end = global i8 0, section ".tls$ZZZ"
@__xl_a = global ptr null, section ".CRT$XLA"
@__xl_z = global ptr null, section ".CRT$XLZ"
@_tls_used = constant {{ ptr, ptr, ptr, ptr, i32, i32 }} {{ ptr @_tls_start, ptr @_tls_end, ptr @_tls_index, ptr getelementptr (i8, ptr @__xl_a, i64 8), i32 0, i32 0 }}, section ".rdata$T"
@_fltused = global i32 39029

declare void @_set_app_type(i32)
declare i32 @_configure_narrow_argv(i32)
declare i32 @_initialize_narrow_environment()
declare void @exit(i32) noreturn
declare i32 @main()

{entry}"#
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(machine, subsystem)` of a PE image.
    fn pe_header(exe: &[u8]) -> (u16, u16) {
        assert_eq!(&exe[..2], b"MZ");
        let pe = u32::from_le_bytes(exe[0x3c..0x40].try_into().unwrap()) as usize;
        assert_eq!(&exe[pe..pe + 4], b"PE\0\0");
        let machine = u16::from_le_bytes([exe[pe + 4], exe[pe + 5]]);
        // The optional header's `Subsystem`.
        let sub = pe + 24 + 68;
        (machine, u16::from_le_bytes([exe[sub], exe[sub + 1]]))
    }

    /// A `main` alone links into a console / GUI PE with nothing but
    /// what rokc carries: no MSVC, no Windows SDK.
    #[test]
    fn links_a_pe_from_embedded_libraries() {
        if !rokc_llvm::AVAILABLE {
            return;
        }
        let dir = crate::TempDir::new(false).unwrap();
        for (triple, machine) in [
            ("x86_64-pc-windows-msvc", 0x8664),
            ("aarch64-pc-windows-msvc", 0xaa64),
        ] {
            let t = rokc_llvm::Target::new(triple);
            let obj = rokc_llvm::compile_llvm_ir(
                "define i32 @main() {\n  ret i32 0\n}\n",
                &rokc_llvm::Compile {
                    target: &t,
                    opt: rokc_llvm::OptLevel::O0,
                    emit: rokc_llvm::Emit::Obj,
                    tls_initial_exec: false,
                    mlir_pipeline: "",
                    dialect_plugins: &[],
                    pass_plugins: &[],
                },
            )
            .unwrap();
            let main = dir.path().join(format!("{triple}.obj"));
            std::fs::write(&main, obj).unwrap();
            for (sub, code) in [(Subsystem::Console, 3), (Subsystem::Windows, 2)] {
                let exe = dir.path().join(format!("{triple}-{code}.exe"));
                let libs = [("ws2_32".to_owned(), false)];
                let mut args = vec![main.clone().into_os_string()];
                args.extend(link_args(&t, &libs, sub, false, dir.path()).unwrap());
                rokc_llvm::link_executable(&t, &args, &exe, true, None).unwrap();
                assert_eq!(pe_header(&std::fs::read(&exe).unwrap()), (machine, code));
            }
        }
    }
}

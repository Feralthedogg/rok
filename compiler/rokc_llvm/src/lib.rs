//! In-process native backend: MLIR → LLVM IR → object → executable with
//! the LLVM, MLIR and lld that rokc links statically (`build.rs`). No
//! subprocess, no textual hand-off between the stages.
//!
//! Built without an LLVM prefix, [`AVAILABLE`] is false and every entry
//! point returns an error.

use std::ffi::{CString, OsStr, OsString};
use std::path::Path;

/// The LLVM this crate links (`llvm/build.sh`).
pub const LLVM_VERSION: &str = "22.1.8";

/// Whether this build links LLVM.
pub const AVAILABLE: bool = cfg!(rok_llvm);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OptLevel {
    O0,
    O1,
    O2,
    O3,
    Os,
    Oz,
}

impl OptLevel {
    /// `0`..`3`, `s`, `z` (rokc's `-O<level>`).
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "0" => Self::O0,
            "1" => Self::O1,
            "2" => Self::O2,
            "3" => Self::O3,
            "s" => Self::Os,
            "z" => Self::Oz,
            _ => return None,
        })
    }

    #[cfg_attr(not(rok_llvm), allow(dead_code))]
    const fn code(self) -> i32 {
        match self {
            Self::O0 => 0,
            Self::O1 => 1,
            Self::O2 => 2,
            Self::O3 => 3,
            Self::Os => b's' as i32,
            Self::Oz => b'z' as i32,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Emit {
    /// LLVM IR text as translated from MLIR, before any LLVM pass.
    LlvmIr,
    Asm,
    Obj,
}

/// A code generation target: clang's `-target`, `-mcpu`, features.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Target {
    pub triple: String,
    pub cpu: String,
    pub features: String,
}

impl Target {
    /// `triple` with the CPU and features clang picks for it by default.
    #[must_use]
    pub fn new(triple: &str) -> Self {
        let arch = triple.split('-').next().unwrap_or("");
        let apple = triple.contains("-apple-");
        let (cpu, features) = match arch {
            "arm64" | "arm64e" | "aarch64" if apple => ("apple-m1", ""),
            "aarch64" | "arm64" => ("generic", "+neon"),
            "x86_64" if apple => ("core2", ""),
            "x86_64" => ("x86-64", ""),
            "riscv64" => ("generic-rv64", "+m,+a,+f,+d,+c"),
            "riscv32" => ("generic-rv32", "+m,+a,+c"),
            _ => ("generic", ""),
        };
        Self {
            triple: triple.to_owned(),
            cpu: cpu.to_owned(),
            features: features.to_owned(),
        }
    }

    /// The machine rokc runs on, as clang names it: on Apple platforms
    /// `<arch>-apple-macosx<deployment target>` (`MACOSX_DEPLOYMENT_TARGET`,
    /// else 11.0, what the runtime library is built for).
    #[must_use]
    pub fn host() -> Self {
        let process = process_triple();
        let arch = process.split('-').next().unwrap_or("");
        if process.contains("-apple-") {
            Self::new(&format!("{arch}-apple-macosx{}", macos_deployment_target()))
        } else {
            Self::new(&process)
        }
    }

    fn is_apple(&self) -> bool {
        self.triple.contains("-apple-")
    }
}

/// What to compile and how.
#[derive(Clone, Debug)]
pub struct Compile<'a> {
    pub target: &'a Target,
    pub opt: OptLevel,
    pub emit: Emit,
    /// `rok_tls_*` globals use the initial-exec TLS model (spec 8.3.8);
    /// off for JIT'd code.
    pub tls_initial_exec: bool,
    /// The MLIR pass pipeline ([`mlir_pipeline`]).
    pub mlir_pipeline: &'a str,
    pub dialect_plugins: &'a [&'a Path],
    pub pass_plugins: &'a [&'a Path],
}

/// The MLIR passes rokc runs before the translation to LLVM IR:
/// `extra` (plugin dialects' own lowerings) first, the cleanup when
/// optimizing, then the conversion to the LLVM dialect.
#[must_use]
pub fn mlir_pipeline(optimize: bool, extra: &[String]) -> String {
    let mut v: Vec<&str> = extra.iter().map(String::as_str).collect();
    if optimize {
        v.extend(["canonicalize", "cse"]);
    }
    v.extend([
        // `scf` / `memref` ops written with `__mlir_op` (bare 1.9).
        "convert-scf-to-cf",
        "convert-func-to-llvm",
        "convert-arith-to-llvm",
        "convert-cf-to-llvm",
        "finalize-memref-to-llvm",
        "reconcile-unrealized-casts",
    ]);
    v.join(",")
}

/// MLIR text in the standard dialects → `c.emit`.
pub fn compile_mlir(src: &str, c: &Compile<'_>) -> Result<Vec<u8>, String> {
    ffi::compile(true, src, c, 1).map(|mut v| v.remove(0))
}

/// MLIR text → `c.opt`-optimized code split into `parts` objects,
/// compiled in parallel (fewer when the module has fewer functions are
/// not guaranteed: some objects may be empty).
pub fn compile_mlir_split(
    src: &str,
    c: &Compile<'_>,
    parts: usize,
) -> Result<Vec<Vec<u8>>, String> {
    ffi::compile(
        true,
        src,
        &Compile {
            emit: Emit::Obj,
            ..c.clone()
        },
        parts.max(1),
    )
}

/// LLVM IR text → `c.emit` (`LlvmIr` only applies the TLS model).
pub fn compile_llvm_ir(src: &str, c: &Compile<'_>) -> Result<Vec<u8>, String> {
    ffi::compile(false, src, c, 1).map(|mut v| v.remove(0))
}

/// The data layout LLVM gives `t` (what clang writes as `target datalayout`).
pub fn data_layout(t: &Target) -> Result<String, String> {
    ffi::data_layout(t)
}

/// The triple LLVM was configured for (`sys::getProcessTriple`); see
/// [`Target::host`] for clang's spelling.
#[must_use]
pub fn process_triple() -> String {
    ffi::process_triple().unwrap_or_else(|| {
        let arch = if cfg!(target_arch = "aarch64") {
            "aarch64"
        } else {
            std::env::consts::ARCH
        };
        if cfg!(target_vendor = "apple") {
            format!("{arch}-apple-darwin")
        } else {
            format!("{arch}-unknown-{}-gnu", std::env::consts::OS)
        }
    })
}

/// Runs lld; `args[0]` names the flavor (`ld64.lld`, `ld.lld`, `lld-link`,
/// `wasm-ld`). Returns what it printed; an error carries it.
pub fn lld<S: AsRef<OsStr>>(args: &[S]) -> Result<String, String> {
    let args = args
        .iter()
        .map(|a| cstr(a.as_ref()))
        .collect::<Result<Vec<_>, _>>()?;
    ffi::lld(&args)
}

/// Links the executable `out` with lld against the platform C library.
///
/// `inputs`: objects, archives, `-l<lib>`, `-L<dir>` and lld options of
/// the target's flavor; `strip` drops what nothing references.
///
/// Mach-O: the SDK is `SDKROOT`, else `xcrun --show-sdk-path`. ELF (GNU
/// libc): the C runtime objects and libraries of `ROK_SYSROOT` (else `/`)
/// and its GCC.
pub fn link_executable<S: AsRef<OsStr>>(
    t: &Target,
    inputs: &[S],
    out: &Path,
    strip: bool,
) -> Result<String, String> {
    // `LIBRARY_PATH` directories are searched, as by cc.
    let search = std::env::var_os("LIBRARY_PATH").unwrap_or_default();
    let search = std::env::split_paths(&search)
        .filter(|d| !d.as_os_str().is_empty())
        .map(|d| {
            let mut l = OsString::from("-L");
            l.push(d);
            l
        });
    let inputs: Vec<OsString> = search
        .chain(inputs.iter().map(|a| a.as_ref().to_owned()))
        .collect();
    let args = if t.is_apple() {
        let mut a = macho_args(t, out)?;
        a.extend(inputs);
        a.push("-lSystem".into());
        if strip {
            a.push("-dead_strip".into());
        }
        a
    } else if t.triple.contains("-linux") {
        let (mut a, tail) = elf_args(t, out)?;
        a.extend(inputs);
        if strip {
            a.push("--gc-sections".into());
        }
        a.extend(tail);
        a
    } else {
        return Err(format!("linking for {} is not supported yet", t.triple));
    };
    lld(&args)
}

fn macho_args(t: &Target, out: &Path) -> Result<Vec<OsString>, String> {
    let sdk = apple_sdk()?;
    let arch = match t.triple.split('-').next() {
        Some("aarch64" | "arm64") => "arm64",
        Some(a) => a,
        None => "",
    };
    let min = t
        .triple
        .split('-')
        .nth(2)
        .and_then(|os| {
            os.strip_prefix("macosx")
                .or_else(|| os.strip_prefix("macos"))
        })
        .filter(|v| !v.is_empty())
        .map_or_else(macos_deployment_target, str::to_owned);
    let sdk_version = sdk_version(&sdk).unwrap_or_else(|| min.clone());
    let mut a: Vec<OsString> = [
        "ld64.lld",
        "-arch",
        arch,
        "-platform_version",
        "macos",
        &min,
        &sdk_version,
    ]
    .map(OsString::from)
    .into();
    a.extend(["-syslibroot".into(), sdk.into_os_string()]);
    // ld64 also searches the real /usr/local/lib.
    if Path::new("/usr/local/lib").is_dir() {
        a.push("-L/usr/local/lib".into());
    }
    a.extend(["-o".into(), out.as_os_str().to_owned()]);
    Ok(a)
}

/// lld's arguments before and after the inputs for a GNU/Linux
/// executable, as gcc / clang pass them (PIE, the C runtime objects,
/// libgcc, libc).
fn elf_args(t: &Target, out: &Path) -> Result<(Vec<OsString>, Vec<OsString>), String> {
    let arch = t.triple.split('-').next().unwrap_or("");
    let (emulation, loader) = match arch {
        "x86_64" => ("elf_x86_64", "/lib64/ld-linux-x86-64.so.2"),
        "aarch64" => ("aarch64linux", "/lib/ld-linux-aarch64.so.1"),
        "riscv64" => ("elf64lriscv", "/lib/ld-linux-riscv64-lp64d.so.1"),
        _ => return Err(format!("linking for {} is not supported yet", t.triple)),
    };
    let root = std::env::var_os("ROK_SYSROOT")
        .filter(|r| !r.is_empty())
        .map_or_else(|| std::path::PathBuf::from("/"), Into::into);
    let multi = format!("{arch}-linux-gnu");
    let dirs: Vec<std::path::PathBuf> = [
        format!("usr/lib/{multi}"),
        format!("lib/{multi}"),
        "usr/lib64".to_owned(),
        "lib64".to_owned(),
        "usr/lib".to_owned(),
        "lib".to_owned(),
    ]
    .iter()
    .map(|d| root.join(d))
    .filter(|d| d.is_dir())
    .collect();
    let find = |name: &str| {
        dirs.iter()
            .map(|d| d.join(name))
            .find(|p| p.is_file())
            .ok_or_else(|| format!("no {name} under {} (install the C library's development files, or set ROK_SYSROOT)", root.display()))
    };
    let (crt1, crti, crtn) = (find("Scrt1.o")?, find("crti.o")?, find("crtn.o")?);
    // The newest GCC's: crtbeginS.o, libgcc.
    let gcc = ["usr/lib/gcc", "usr/lib64/gcc"]
        .iter()
        .filter_map(|g| std::fs::read_dir(root.join(g)).ok())
        .flatten()
        .filter_map(|e| Some(e.ok()?.path()))
        .filter(|d| {
            d.file_name()
                .is_some_and(|n| n.to_string_lossy().starts_with(arch))
        })
        .filter_map(|d| std::fs::read_dir(d).ok())
        .flatten()
        .filter_map(|e| Some(e.ok()?.path()))
        .filter(|d| d.join("crtbeginS.o").is_file())
        .max_by_key(|d| {
            d.file_name().and_then(|n| n.to_str()).map(|v| {
                v.split('.')
                    .map(|x| x.parse::<u32>().unwrap_or(0))
                    .collect::<Vec<_>>()
            })
        })
        .ok_or_else(|| format!("no GCC runtime (crtbeginS.o) under {}", root.display()))?;
    let mut head: Vec<OsString> = [
        "ld.lld",
        "-m",
        emulation,
        "-pie",
        "--eh-frame-hdr",
        "--hash-style=gnu",
        "--build-id",
        "-dynamic-linker",
        loader,
    ]
    .map(OsString::from)
    .into();
    head.extend(["-o".into(), out.as_os_str().to_owned()]);
    head.extend([crt1, crti, gcc.join("crtbeginS.o")].map(std::path::PathBuf::into_os_string));
    let mut l = OsString::from("-L");
    l.push(&gcc);
    head.push(l);
    for d in &dirs {
        let mut l = OsString::from("-L");
        l.push(d);
        head.push(l);
    }
    let mut tail: Vec<OsString> = [
        "-lgcc",
        "--as-needed",
        "-lgcc_s",
        "--no-as-needed",
        "-lc",
        "-lgcc",
        "--as-needed",
        "-lgcc_s",
        "--no-as-needed",
    ]
    .map(OsString::from)
    .into();
    tail.extend([gcc.join("crtendS.o"), crtn].map(std::path::PathBuf::into_os_string));
    Ok((head, tail))
}

/// `dsymutil <args>`: the DWARF of a Mach-O executable's objects into a
/// `.dSYM` bundle. It reports on stderr.
pub fn dsymutil<S: AsRef<OsStr>>(args: &[S]) -> Result<(), String> {
    let mut v = vec![cstr(OsStr::new("dsymutil"))?];
    for a in args {
        v.push(cstr(a.as_ref())?);
    }
    ffi::dsymutil(&v)
}

/// An archive of `members` with a symbol table: BSD format for Apple
/// targets, else GNU.
pub fn write_archive(t: &Target, out: &Path, members: &[&Path]) -> Result<(), String> {
    let members = members
        .iter()
        .map(|m| cstr(m.as_os_str()))
        .collect::<Result<Vec<_>, _>>()?;
    ffi::write_archive(&cstr(out.as_os_str())?, &members, t.is_apple())
}

fn macos_deployment_target() -> String {
    std::env::var("MACOSX_DEPLOYMENT_TARGET")
        .ok()
        .filter(|v| !v.is_empty())
        .unwrap_or_else(|| "11.0".to_owned())
}

fn apple_sdk() -> Result<std::path::PathBuf, String> {
    if let Some(p) = std::env::var_os("SDKROOT").filter(|p| !p.is_empty()) {
        return Ok(p.into());
    }
    let out = std::process::Command::new("xcrun")
        .arg("--show-sdk-path")
        .output()
        .map_err(|e| format!("cannot run xcrun to find the macOS SDK: {e}"))?;
    let path = String::from_utf8_lossy(&out.stdout).trim().to_owned();
    if !out.status.success() || path.is_empty() {
        return Err("no macOS SDK (install the Xcode command line tools)".to_owned());
    }
    Ok(path.into())
}

/// `"Version":"26.0"` of the SDK's `SDKSettings.json`.
fn sdk_version(sdk: &Path) -> Option<String> {
    let json = std::fs::read_to_string(sdk.join("SDKSettings.json")).ok()?;
    let rest = &json[json.find("\"Version\"")? + 9..];
    let rest = &rest[rest.find('"')? + 1..];
    Some(rest[..rest.find('"')?].to_owned())
}

fn cstr(s: &OsStr) -> Result<CString, String> {
    CString::new(s.as_encoded_bytes())
        .map_err(|_| format!("{} contains NUL", Path::new(s).display()))
}

#[cfg(rok_llvm)]
mod ffi {
    use std::ffi::{CString, c_char, c_int};
    use std::path::Path;

    use super::{Compile, Emit, Target};

    #[repr(C)]
    struct RokBuf {
        ptr: *mut c_char,
        len: usize,
    }

    impl RokBuf {
        const fn new() -> Self {
            Self {
                ptr: std::ptr::null_mut(),
                len: 0,
            }
        }

        fn take(mut self) -> Vec<u8> {
            let v = if self.ptr.is_null() {
                Vec::new()
            } else {
                // SAFETY: the shim wrote `len` bytes at `ptr`.
                unsafe { std::slice::from_raw_parts(self.ptr.cast::<u8>(), self.len) }.to_vec()
            };
            // SAFETY: a buffer of the shim.
            unsafe { rok_llvm_free(&raw mut self) };
            v
        }

        fn text(self) -> String {
            String::from_utf8_lossy(&self.take()).into_owned()
        }
    }

    #[repr(C)]
    struct RokCompile {
        triple: *const c_char,
        cpu: *const c_char,
        features: *const c_char,
        opt: c_int,
        emit: c_int,
        tls_initial_exec: c_int,
        mlir_pipeline: *const c_char,
        dialect_plugins: *const *const c_char,
        n_dialect_plugins: usize,
        pass_plugins: *const *const c_char,
        n_pass_plugins: usize,
        parts: usize,
    }

    unsafe extern "C" {
        fn rok_llvm_free(b: *mut RokBuf);
        fn rok_llvm_compile_mlir(
            src: *const c_char,
            len: usize,
            o: *const RokCompile,
            out: *mut RokBuf,
            err: *mut RokBuf,
        ) -> c_int;
        fn rok_llvm_compile_ir(
            src: *const c_char,
            len: usize,
            o: *const RokCompile,
            out: *mut RokBuf,
            err: *mut RokBuf,
        ) -> c_int;
        fn rok_llvm_data_layout(o: *const RokCompile, out: *mut RokBuf, err: *mut RokBuf) -> c_int;
        fn rok_llvm_process_triple(out: *mut RokBuf);
        fn rok_llvm_dsymutil(argv: *const *const c_char, argc: usize) -> c_int;
        fn rok_llvm_lld(argv: *const *const c_char, argc: usize, log: *mut RokBuf) -> c_int;
        fn rok_llvm_write_archive(
            path: *const c_char,
            members: *const *const c_char,
            n: usize,
            darwin: c_int,
            err: *mut RokBuf,
        ) -> c_int;
    }

    fn c(s: &str) -> Result<CString, String> {
        CString::new(s).map_err(|_| format!("`{s}` contains NUL"))
    }

    fn paths(ps: &[&Path]) -> Result<Vec<CString>, String> {
        ps.iter().map(|p| super::cstr(p.as_os_str())).collect()
    }

    pub fn compile(
        mlir: bool,
        src: &str,
        o: &Compile<'_>,
        parts: usize,
    ) -> Result<Vec<Vec<u8>>, String> {
        let (triple, cpu, features) = (
            c(&o.target.triple)?,
            c(&o.target.cpu)?,
            c(&o.target.features)?,
        );
        let pipeline = c(o.mlir_pipeline)?;
        let dialects = paths(o.dialect_plugins)?;
        let passes = paths(o.pass_plugins)?;
        let dialect_ptrs: Vec<*const c_char> = dialects.iter().map(|s| s.as_ptr()).collect();
        let pass_ptrs: Vec<*const c_char> = passes.iter().map(|s| s.as_ptr()).collect();
        let opts = RokCompile {
            triple: triple.as_ptr(),
            cpu: cpu.as_ptr(),
            features: features.as_ptr(),
            opt: o.opt.code(),
            emit: match o.emit {
                Emit::LlvmIr => 0,
                Emit::Asm => 1,
                Emit::Obj => 2,
            },
            tls_initial_exec: c_int::from(o.tls_initial_exec),
            mlir_pipeline: pipeline.as_ptr(),
            dialect_plugins: dialect_ptrs.as_ptr(),
            n_dialect_plugins: dialect_ptrs.len(),
            pass_plugins: pass_ptrs.as_ptr(),
            n_pass_plugins: pass_ptrs.len(),
            parts,
        };
        let mut out: Vec<RokBuf> = (0..parts).map(|_| RokBuf::new()).collect();
        let mut err = RokBuf::new();
        let f = if mlir {
            rok_llvm_compile_mlir
        } else {
            rok_llvm_compile_ir
        };
        // SAFETY: every pointer outlives the call; the shim fills the buffers.
        let rc = unsafe {
            f(
                src.as_ptr().cast(),
                src.len(),
                &raw const opts,
                out.as_mut_ptr(),
                &raw mut err,
            )
        };
        let out: Vec<Vec<u8>> = out.into_iter().map(RokBuf::take).collect();
        if rc == 0 {
            drop(err.take());
            Ok(out)
        } else {
            Err(err.text())
        }
    }

    pub fn data_layout(t: &Target) -> Result<String, String> {
        let (triple, cpu, features, none) = (c(&t.triple)?, c(&t.cpu)?, c(&t.features)?, c("")?);
        let opts = RokCompile {
            triple: triple.as_ptr(),
            cpu: cpu.as_ptr(),
            features: features.as_ptr(),
            opt: 0,
            emit: 2,
            tls_initial_exec: 0,
            mlir_pipeline: none.as_ptr(),
            dialect_plugins: std::ptr::null(),
            n_dialect_plugins: 0,
            pass_plugins: std::ptr::null(),
            n_pass_plugins: 0,
            parts: 1,
        };
        let (mut out, mut err) = (RokBuf::new(), RokBuf::new());
        // SAFETY: as in `compile`.
        let rc = unsafe { rok_llvm_data_layout(&raw const opts, &raw mut out, &raw mut err) };
        if rc == 0 {
            drop(err.take());
            Ok(out.text())
        } else {
            drop(out.take());
            Err(err.text())
        }
    }

    // The stub's signature.
    #[allow(clippy::unnecessary_wraps)]
    pub fn process_triple() -> Option<String> {
        let mut out = RokBuf::new();
        // SAFETY: the shim fills `out`.
        unsafe { rok_llvm_process_triple(&raw mut out) };
        Some(out.text())
    }

    pub fn dsymutil(args: &[CString]) -> Result<(), String> {
        let ptrs: Vec<*const c_char> = args.iter().map(|s| s.as_ptr()).collect();
        // SAFETY: `ptrs` points into `args`, alive for the call.
        let rc = unsafe { rok_llvm_dsymutil(ptrs.as_ptr(), ptrs.len()) };
        if rc == 0 {
            Ok(())
        } else {
            Err("dsymutil failed".to_owned())
        }
    }

    pub fn lld(args: &[CString]) -> Result<String, String> {
        let ptrs: Vec<*const c_char> = args.iter().map(|s| s.as_ptr()).collect();
        let mut log = RokBuf::new();
        // SAFETY: `ptrs` points into `args`, alive for the call.
        let rc = unsafe { rok_llvm_lld(ptrs.as_ptr(), ptrs.len(), &raw mut log) };
        let log = log.text();
        if rc == 0 { Ok(log) } else { Err(log) }
    }

    pub fn write_archive(out: &CString, members: &[CString], darwin: bool) -> Result<(), String> {
        let ptrs: Vec<*const c_char> = members.iter().map(|s| s.as_ptr()).collect();
        let mut err = RokBuf::new();
        // SAFETY: as in `lld`.
        let rc = unsafe {
            rok_llvm_write_archive(
                out.as_ptr(),
                ptrs.as_ptr(),
                ptrs.len(),
                c_int::from(darwin),
                &raw mut err,
            )
        };
        if rc == 0 {
            drop(err.take());
            Ok(())
        } else {
            Err(err.text())
        }
    }
}

#[cfg(not(rok_llvm))]
mod ffi {
    use std::ffi::CString;

    use super::{Compile, Target};

    fn off<T>() -> Result<T, String> {
        Err(format!(
            "this rokc was built without LLVM {} (set ROK_LLVM_PREFIX, see llvm/build.sh)",
            super::LLVM_VERSION
        ))
    }

    pub fn compile(_: bool, _: &str, _: &Compile<'_>, _: usize) -> Result<Vec<Vec<u8>>, String> {
        off()
    }

    pub fn data_layout(_: &Target) -> Result<String, String> {
        off()
    }

    pub const fn process_triple() -> Option<String> {
        None
    }

    pub fn lld(_: &[CString]) -> Result<String, String> {
        off()
    }

    pub fn dsymutil(_: &[CString]) -> Result<(), String> {
        off()
    }

    pub fn write_archive(_: &CString, _: &[CString], _: bool) -> Result<(), String> {
        off()
    }
}

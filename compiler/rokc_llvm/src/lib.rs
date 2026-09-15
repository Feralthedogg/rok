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

/// The prefix this build links (its headers build MLIR plugins).
pub const PREFIX: Option<&str> = option_env!("ROK_LLVM_LINKED_PREFIX");

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
            // SSE2, NEON (spec 0.6.4); the thread pointer from TPIDRURO,
            // not glibc's `__aeabi_read_tp` (in ld.so).
            "i686" => ("pentium4", ""),
            "armv7" => ("generic", "+vfp3,+d32,+neon,+read-tp-tpidruro"),
            "riscv64" => ("generic-rv64", "+m,+a,+f,+d,+c"),
            "riscv32" => ("generic-rv32", "+m,+a,+c"),
            // Spec 0.6.4: SIMD128 on by default; wasi-threads needs
            // shared memory (atomics, bulk memory).
            "wasm32" if triple.ends_with("-threads") => {
                ("generic", "+simd128,+atomics,+bulk-memory,+mutable-globals")
            }
            "wasm32" => ("generic", "+simd128"),
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

    fn is_windows(&self) -> bool {
        self.triple.contains("-windows")
    }

    /// lld-link's `/machine:` of a Windows target and its COFF machine
    /// type.
    fn coff_machine(&self) -> Result<(&'static str, u16), String> {
        match self.triple.split('-').next() {
            Some("x86_64") => Ok(("x64", 0x8664)),
            Some("aarch64" | "arm64") => Ok(("arm64", 0xaa64)),
            Some("i686") => Ok(("x86", 0x14c)),
            _ => Err(format!("linking for {} is not supported yet", self.triple)),
        }
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
    pub profile: Profile<'a>,
}

/// IR profile-guided optimization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Profile<'a> {
    None,
    /// Instrument: the program writes its raw profile to this file name
    /// pattern (`%m`, `%p`; `LLVM_PROFILE_FILE` overrides it at run time).
    Generate(&'a Path),
    /// Optimize with this indexed profile.
    Use(&'a Path),
    /// Context-sensitive: optimize with this indexed profile, then
    /// instrument again after inlining, writing to this pattern.
    CsGenerate(&'a Path, &'a Path),
}

/// The MLIR passes rokc runs before the translation to LLVM IR:
/// `extra` (plugin dialects' own lowerings) first, the cleanup when
/// optimizing, then the conversion to the LLVM dialect.
///
/// Passes that work on any op run nested (`any(..)`) on each function
/// and global, in parallel.
#[must_use]
pub fn mlir_pipeline(optimize: bool, extra: &[String]) -> String {
    let mut v: Vec<&str> = extra.iter().map(String::as_str).collect();
    // `scf` / `memref` ops written with `__mlir_op` (bare 1.9).
    v.extend([
        if optimize {
            "any(canonicalize,cse,convert-scf-to-cf)"
        } else {
            "any(convert-scf-to-cf)"
        },
        "convert-func-to-llvm",
        "any(convert-arith-to-llvm)",
        "convert-cf-to-llvm",
        "finalize-memref-to-llvm",
        "any(reconcile-unrealized-casts)",
    ]);
    v.join(",")
}

/// MLIR text in the standard dialects → `c.emit`.
pub fn compile_mlir(src: &str, c: &Compile<'_>) -> Result<Vec<u8>, String> {
    ffi::compile(true, src, c, 1).map(|(mut v, _)| v.remove(0))
}

/// MLIR text → `c.emit`; an object split into `parts` objects compiled
/// in parallel (some may be empty). Also what LLVM warned about.
pub fn compile_mlir_split(
    src: &str,
    c: &Compile<'_>,
    parts: usize,
) -> Result<(Vec<Vec<u8>>, String), String> {
    ffi::compile(true, src, c, parts.max(1))
}

/// LLVM IR text → `c.emit` (`LlvmIr` only applies the TLS model).
pub fn compile_llvm_ir(src: &str, c: &Compile<'_>) -> Result<Vec<u8>, String> {
    ffi::compile(false, src, c, 1).map(|(mut v, _)| v.remove(0))
}

/// The raw (`.profraw`), indexed or text IR profiles `inputs` merged into
/// the indexed profile `out`, as `llvm-profdata merge` does; its warnings
/// (counter overflow, mismatched counters), one per line.
pub fn profdata_merge(inputs: &[&Path], out: &Path) -> Result<String, String> {
    let inputs = inputs
        .iter()
        .map(|p| cstr(p.as_os_str()))
        .collect::<Result<Vec<_>, _>>()?;
    ffi::profdata_merge(&inputs, &cstr(out.as_os_str())?)
}

/// `llvm-profdata show` of the IR profile `file`: a summary; with `all`,
/// every function; with `topn`, the hottest ones.
pub fn profdata_show(file: &Path, all: bool, topn: usize) -> Result<String, String> {
    ffi::profdata_show(&cstr(file.as_os_str())?, all, topn)
}

/// The data layout LLVM gives `t` (what clang writes as `target datalayout`).
pub fn data_layout(t: &Target) -> Result<String, String> {
    ffi::data_layout(t)
}

/// The triple LLVM was configured for (`sys::getProcessTriple`); see
/// [`Target::host`] for clang's spelling. Without LLVM, the triple
/// rokc was compiled for.
#[must_use]
pub fn process_triple() -> String {
    ffi::process_triple().unwrap_or_else(|| env!("ROK_LLVM_TARGET").to_owned())
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
/// Mach-O: the SDK is `SDKROOT`, else the selected developer
/// directory's. Linux and wasm32: `libc`, the toolchain's C runtime
/// objects and C library for the target (`targets/build.sh`). COFF: no default
/// libraries; `inputs` bring the C runtime (import libraries,
/// [`import_library`]) and the entry point.
pub fn link_executable<S: AsRef<OsStr>>(
    t: &Target,
    inputs: &[S],
    out: &Path,
    strip: bool,
    libc: Option<&Path>,
) -> Result<String, String> {
    // `-L<dir>` inputs, then `LIBRARY_PATH` directories, as by cc.
    let search = std::env::var_os("LIBRARY_PATH").unwrap_or_default();
    let search = std::env::split_paths(&search)
        .filter(|d| !d.as_os_str().is_empty())
        .map(|d| {
            let mut l = OsString::from("-L");
            l.push(d);
            l
        });
    let (dirs, rest): (Vec<OsString>, Vec<OsString>) = inputs
        .iter()
        .map(|a| a.as_ref().to_owned())
        .partition(|a| a.to_str().is_some_and(|s| s.starts_with("-L")));
    let inputs: Vec<OsString> = dirs.into_iter().chain(search).chain(rest).collect();
    let args =
        if t.is_apple() {
            let mut a = macho_args(t, out)?;
            a.extend(inputs);
            a.push("-lSystem".into());
            if strip {
                a.push("-dead_strip".into());
            }
            a
        } else if t.triple.contains("-linux") {
            let libc = libc.ok_or_else(|| format!("no C library for {}", t.triple))?;
            let (mut a, tail) = elf_args(t, out, libc)?;
            a.extend(inputs);
            if strip {
                a.push("--gc-sections".into());
            }
            a.extend(tail);
            a
        } else if t.is_windows() {
            let mut a: Vec<OsString> = [
                "lld-link",
                "/nologo",
                "/nodefaultlib",
                "/dynamicbase",
                "/nxcompat",
            ]
            .map(OsString::from)
            .into();
            let machine = t.coff_machine()?.0;
            a.push(format!("/machine:{machine}").into());
            // x86: a 4 GiB address space under 64-bit Windows (the heap of
            // spec 0.6.3), and no SafeSEH table: rok code raises no SEH
            // exceptions and the runtime's handler is vectored.
            if machine == "x86" {
                a.extend(["/largeaddressaware".into(), "/safeseh:no".into()]);
            }
            let mut o = OsString::from("/out:");
            o.push(out);
            a.push(o);
            // `-L<dir>` (LIBRARY_PATH) in lld-link's spelling.
            a.extend(inputs.into_iter().map(
                |i| match i.to_str().and_then(|s| s.strip_prefix("-L")) {
                    Some(d) => format!("/libpath:{d}").into(),
                    None => i,
                },
            ));
            a.push(if strip { "/opt:ref" } else { "/opt:noref" }.into());
            a
        } else if t.triple.starts_with("wasm32") {
            let libc = libc.ok_or_else(|| format!("no C library for {}", t.triple))?;
            let mut a = wasm_args(out, libc, t.triple.ends_with("-threads"))?;
            a.extend(inputs);
            a.push(libc.join("libc.a").into_os_string());
            if t.triple == "wasm32-wasi" {
                return link_component(&a, libc);
            }
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

/// lld's arguments before and after the inputs for a Linux executable
/// against the C library in `libc`: musl statically, glibc (link stubs)
/// as a PIE run by the system's dynamic loader.
fn elf_args(t: &Target, out: &Path, libc: &Path) -> Result<(Vec<OsString>, Vec<OsString>), String> {
    let (emulation, loader) = match t.triple.split('-').next().unwrap_or("") {
        "x86_64" => ("elf_x86_64", "/lib64/ld-linux-x86-64.so.2"),
        "aarch64" => ("aarch64linux", "/lib/ld-linux-aarch64.so.1"),
        "i686" => ("elf_i386", "/lib/ld-linux.so.2"),
        "armv7" => ("armelf_linux_eabi", "/lib/ld-linux-armhf.so.3"),
        _ => return Err(format!("linking for {} is not supported yet", t.triple)),
    };
    let musl = t.triple.contains("-musl");
    let crt1 = if musl { "crt1.o" } else { "Scrt1.o" };
    if !libc.join(crt1).is_file() {
        return Err(format!(
            "no C library for {} in {}",
            t.triple,
            libc.display()
        ));
    }
    let f = |name: &str| libc.join(name).into_os_string();
    let mut search = OsString::from("-L");
    search.push(libc);
    let mut head: Vec<OsString> = ["ld.lld", "-m", emulation, "--eh-frame-hdr", "--build-id"]
        .map(OsString::from)
        .into();
    head.extend(["-o".into(), out.as_os_str().to_owned()]);
    let tail = if musl {
        head.extend(["-static".into(), f(crt1), f("crti.o"), search]);
        vec![f("libc.a"), f("crtn.o")]
    } else {
        head.extend(["-pie", "--hash-style=gnu", "-dynamic-linker", loader].map(OsString::from));
        head.extend([f(crt1), f("crti.o"), search]);
        vec![
            "--as-needed".into(),
            "-lm".into(),
            "--no-as-needed".into(),
            "-lc".into(),
            f("libc_nonshared.a"),
            f("crtn.o"),
        ]
    };
    Ok((head, tail))
}

/// Set in the environment of `wasm-component-ld`, which runs rokc as its
/// `wasm-ld`: rokc then only links ([`wasm_ld_main`]).
pub const AS_WASM_LD: &str = "ROK_AS_WASM_LD";

/// rokc run as `wasm-ld` ([`AS_WASM_LD`]): lld's wasm flavor over the
/// arguments. The exit code.
#[must_use]
pub fn wasm_ld_main() -> i32 {
    let mut args: Vec<OsString> = vec!["wasm-ld".into()];
    args.extend(std::env::args_os().skip(1));
    match lld(&args) {
        Ok(text) => {
            eprint!("{text}");
            0
        }
        Err(text) => {
            eprint!("{text}");
            1
        }
    }
}

/// `wasm32-wasi` is a WASI preview 2 component: the toolchain's
/// `wasm-component-ld` (the Rust toolchain's, shipped beside wasi-libc)
/// links with rokc as its `wasm-ld` (`args` past the flavor), then wraps
/// the module, adapting its preview 1 imports with the adapter it
/// embeds. What it printed; an error carries it.
fn link_component(args: &[OsString], libc: &Path) -> Result<String, String> {
    let rokc = std::env::current_exe().map_err(|e| format!("cannot find rokc: {e}"))?;
    let tool = libc.join(format!("wasm-component-ld{}", std::env::consts::EXE_SUFFIX));
    let run = std::process::Command::new(&tool)
        .arg("--wasm-ld-path")
        .arg(&rokc)
        .args(&args[1..])
        .env(AS_WASM_LD, "1")
        .output()
        .map_err(|e| format!("{}: {e}", tool.display()))?;
    let text =
        String::from_utf8_lossy(&run.stderr).into_owned() + &String::from_utf8_lossy(&run.stdout);
    if run.status.success() {
        Ok(text)
    } else {
        Err(text)
    }
}

/// wasm-ld's arguments before the inputs for a wasm32 command module
/// against wasi-libc in `libc`: `_start` (its `crt1-command.o`) calls
/// `__main_void`. The 8 MiB stack (rok's thread stack) comes first in
/// linear memory, so an overflow runs off address 0 and traps. wasm-ld
/// drops unreferenced sections by default. With `threads`
/// (wasi-threads): a shared memory the host provides, up to wasm32's
/// 4 GiB, and `wasi_thread_start`, where each new thread begins.
fn wasm_args(out: &Path, libc: &Path, threads: bool) -> Result<Vec<OsString>, String> {
    let crt1 = libc.join("crt1-command.o");
    if !crt1.is_file() {
        return Err(format!("no C library in {}", libc.display()));
    }
    let mut search = OsString::from("-L");
    search.push(libc);
    // The stack first: one that overflows runs off address 0 and wraps
    // to the top of the address space, which memory never reaches (its
    // last 64 KiB page is never grown), so a store there traps.
    let mut a: Vec<OsString> = [
        "wasm-ld",
        "--stack-first",
        "-z",
        "stack-size=8388608",
        "--max-memory=4294901760",
    ]
    .map(OsString::from)
    .into();
    if threads {
        a.extend(
            [
                "--shared-memory",
                "--import-memory",
                "--export-memory",
                "--export=wasi_thread_start",
            ]
            .map(OsString::from),
        );
    }
    a.extend([
        "-o".into(),
        out.as_os_str().to_owned(),
        crt1.into_os_string(),
        search,
    ]);
    Ok(a)
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
/// targets, COFF for Windows, else GNU.
pub fn write_archive(t: &Target, out: &Path, members: &[&Path]) -> Result<(), String> {
    let members = members
        .iter()
        .map(|m| cstr(m.as_os_str()))
        .collect::<Result<Vec<_>, _>>()?;
    let kind = if t.is_apple() {
        1
    } else if t.is_windows() {
        2
    } else {
        0
    };
    ffi::write_archive(&cstr(out.as_os_str())?, &members, kind)
}

/// The import library `out` of the module definition `def` (a `.def`
/// file's text, mingw-w64 syntax) for a Windows target.
pub fn import_library(t: &Target, def: &str, out: &Path) -> Result<(), String> {
    ffi::import_library(def, t.coff_machine()?.1, &cstr(out.as_os_str())?)
}

fn macos_deployment_target() -> String {
    std::env::var("MACOSX_DEPLOYMENT_TARGET")
        .ok()
        .filter(|v| !v.is_empty())
        .unwrap_or_else(|| "11.0".to_owned())
}

/// The macOS SDK as `xcrun` finds it, without running it: `SDKROOT`,
/// else the SDK of the developer directory (`DEVELOPER_DIR`, else the
/// one `xcode-select` chose, else the command line tools).
fn apple_sdk() -> Result<std::path::PathBuf, String> {
    if let Some(p) = std::env::var_os("SDKROOT").filter(|p| !p.is_empty()) {
        return Ok(p.into());
    }
    let dev = std::env::var_os("DEVELOPER_DIR")
        .filter(|d| !d.is_empty())
        .map(std::path::PathBuf::from)
        .or_else(|| std::fs::read_link("/var/db/xcode_select_link").ok())
        .unwrap_or_else(|| "/Library/Developer/CommandLineTools".into());
    // Xcode keeps it in the platform, the command line tools at the top.
    [
        "Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk",
        "SDKs/MacOSX.sdk",
    ]
    .iter()
    .map(|s| dev.join(s))
    .find(|s| s.is_dir())
    .ok_or_else(|| {
        format!(
            "no macOS SDK in {} (install the Xcode command line tools, or set SDKROOT)",
            dev.display()
        )
    })
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

    use super::{Compile, Emit, Profile, Target};

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
        profile_generate: *const c_char,
        profile_use: *const c_char,
    }

    unsafe extern "C" {
        fn rok_llvm_free(b: *mut RokBuf);
        fn rok_llvm_compile_mlir(
            src: *const c_char,
            len: usize,
            o: *const RokCompile,
            out: *mut RokBuf,
            err: *mut RokBuf,
            warn: *mut RokBuf,
        ) -> c_int;
        fn rok_llvm_compile_ir(
            src: *const c_char,
            len: usize,
            o: *const RokCompile,
            out: *mut RokBuf,
            err: *mut RokBuf,
            warn: *mut RokBuf,
        ) -> c_int;
        fn rok_llvm_data_layout(o: *const RokCompile, out: *mut RokBuf, err: *mut RokBuf) -> c_int;
        fn rok_llvm_process_triple(out: *mut RokBuf);
        fn rok_llvm_dsymutil(argv: *const *const c_char, argc: usize) -> c_int;
        fn rok_llvm_lld(argv: *const *const c_char, argc: usize, log: *mut RokBuf) -> c_int;
        fn rok_llvm_write_archive(
            path: *const c_char,
            members: *const *const c_char,
            n: usize,
            kind: c_int,
            err: *mut RokBuf,
        ) -> c_int;
        fn rok_llvm_profdata_merge(
            inputs: *const *const c_char,
            n: usize,
            path: *const c_char,
            warn: *mut RokBuf,
            err: *mut RokBuf,
        ) -> c_int;
        fn rok_llvm_profdata_show(
            path: *const c_char,
            all: c_int,
            topn: usize,
            out: *mut RokBuf,
            err: *mut RokBuf,
        ) -> c_int;
        fn rok_llvm_import_lib(
            def: *const c_char,
            len: usize,
            machine: u16,
            path: *const c_char,
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
    ) -> Result<(Vec<Vec<u8>>, String), String> {
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
        let (generate, used) = match o.profile {
            Profile::None => (None, None),
            Profile::Generate(p) => (Some(p), None),
            Profile::Use(p) => (None, Some(p)),
            Profile::CsGenerate(u, g) => (Some(g), Some(u)),
        };
        let path = |p: Option<&Path>| p.map_or_else(|| c(""), |p| super::cstr(p.as_os_str()));
        let (generate, used) = (path(generate)?, path(used)?);
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
            profile_generate: generate.as_ptr(),
            profile_use: used.as_ptr(),
        };
        let mut out: Vec<RokBuf> = (0..parts).map(|_| RokBuf::new()).collect();
        let (mut err, mut warn) = (RokBuf::new(), RokBuf::new());
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
                &raw mut warn,
            )
        };
        let out: Vec<Vec<u8>> = out.into_iter().map(RokBuf::take).collect();
        let warn = warn.text();
        if rc == 0 {
            drop(err.take());
            Ok((out, warn))
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
            profile_generate: none.as_ptr(),
            profile_use: none.as_ptr(),
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

    pub fn write_archive(out: &CString, members: &[CString], kind: c_int) -> Result<(), String> {
        let ptrs: Vec<*const c_char> = members.iter().map(|s| s.as_ptr()).collect();
        let mut err = RokBuf::new();
        // SAFETY: as in `lld`.
        let rc = unsafe {
            rok_llvm_write_archive(out.as_ptr(), ptrs.as_ptr(), ptrs.len(), kind, &raw mut err)
        };
        if rc == 0 {
            drop(err.take());
            Ok(())
        } else {
            Err(err.text())
        }
    }

    pub fn profdata_merge(inputs: &[CString], out: &CString) -> Result<String, String> {
        let ptrs: Vec<*const c_char> = inputs.iter().map(|s| s.as_ptr()).collect();
        let (mut warn, mut err) = (RokBuf::new(), RokBuf::new());
        // SAFETY: as in `lld`.
        let rc = unsafe {
            rok_llvm_profdata_merge(
                ptrs.as_ptr(),
                ptrs.len(),
                out.as_ptr(),
                &raw mut warn,
                &raw mut err,
            )
        };
        if rc == 0 {
            drop(err.take());
            Ok(warn.text())
        } else {
            drop(warn.take());
            Err(err.text())
        }
    }

    pub fn profdata_show(file: &CString, all: bool, topn: usize) -> Result<String, String> {
        let (mut out, mut err) = (RokBuf::new(), RokBuf::new());
        // SAFETY: as in `lld`.
        let rc = unsafe {
            rok_llvm_profdata_show(
                file.as_ptr(),
                c_int::from(all),
                topn,
                &raw mut out,
                &raw mut err,
            )
        };
        if rc == 0 {
            drop(err.take());
            Ok(out.text())
        } else {
            drop(out.take());
            Err(err.text())
        }
    }

    pub fn import_library(def: &str, machine: u16, out: &CString) -> Result<(), String> {
        let mut err = RokBuf::new();
        // SAFETY: as in `lld`.
        let rc = unsafe {
            rok_llvm_import_lib(
                def.as_ptr().cast(),
                def.len(),
                machine,
                out.as_ptr(),
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

    pub fn compile(
        _: bool,
        _: &str,
        _: &Compile<'_>,
        _: usize,
    ) -> Result<(Vec<Vec<u8>>, String), String> {
        off()
    }

    pub fn profdata_merge(_: &[CString], _: &CString) -> Result<String, String> {
        off()
    }

    pub fn profdata_show(_: &CString, _: bool, _: usize) -> Result<String, String> {
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

    pub fn write_archive(_: &CString, _: &[CString], _: i32) -> Result<(), String> {
        off()
    }

    pub fn import_library(_: &str, _: u16, _: &CString) -> Result<(), String> {
        off()
    }
}

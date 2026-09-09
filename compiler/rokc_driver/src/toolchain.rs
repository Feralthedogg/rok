//! Native back half of the AOT pipeline (spec 902.11-902.14): MLIR text
//! → `mlir-opt` → `mlir-translate` → `clang`. Lives in the driver so any
//! embedder (CLI, REPL, LSP) can build, not just the `rokc` binary.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use rokc_diagnostic::{ErrorKind, RokDiagnostic};

use crate::CompiledModule;

/// Intermediate artifact selectable with `--emit=<kind>` (spec 901).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EmitKind {
    Hir,
    Mir,
    Mlir,
    LlvmIr,
    Asm,
    Obj,
}

impl EmitKind {
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "hir" => Self::Hir,
            "mir" => Self::Mir,
            "mlir" => Self::Mlir,
            "llvmir" | "llvm-ir" | "ll" => Self::LlvmIr,
            "asm" => Self::Asm,
            "obj" => Self::Obj,
            _ => return None,
        })
    }

    /// File extension used under `target/`.
    #[must_use]
    pub const fn extension(self) -> &'static str {
        match self {
            Self::Hir => "hir",
            Self::Mir => "mir",
            Self::Mlir => "mlir",
            Self::LlvmIr => "ll",
            Self::Asm => "s",
            Self::Obj => "o",
        }
    }
}

#[derive(Clone, Debug)]
pub struct BuildOptions {
    /// LLVM target triple (`--target`). `None` = host.
    pub target: Option<String>,
    /// `0`..`3` or `s`, forwarded to clang as `-O<level>`.
    pub opt_level: String,
    /// Runtime library: a path when it has an extension, else `-l<name>`.
    pub rokr: String,
    /// Keep the scratch directory instead of deleting it.
    pub keep_temps: bool,
    /// `-g`: DWARF debug info (spec 9.9.6).
    pub debug: bool,
    /// Codegen a REPL cell (`link_shared`).
    pub repl: Option<rokc_codegen_mlir::ReplCell>,
}

impl Default for BuildOptions {
    fn default() -> Self {
        Self {
            target: None,
            opt_level: "0".to_owned(),
            rokr: "rokr".to_owned(),
            keep_temps: false,
            debug: false,
            repl: None,
        }
    }
}

/// Private scratch directory, created exclusively and removed on drop
/// unless `keep` is set.
pub struct TempDir {
    path: PathBuf,
    keep: bool,
}

impl TempDir {
    pub fn new(keep: bool) -> Result<Self, RokDiagnostic> {
        let base = std::env::temp_dir();
        let pid = std::process::id();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.subsec_nanos());
        for attempt in 0..100u32 {
            let path = base.join(format!("rokc-{pid}-{nanos:x}-{attempt}"));
            let mut builder = std::fs::DirBuilder::new();
            #[cfg(unix)]
            std::os::unix::fs::DirBuilderExt::mode(&mut builder, 0o700);
            match builder.create(&path) {
                Ok(()) => return Ok(Self { path, keep }),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(e) => {
                    return Err(err(format!("cannot create {}: {e}", path.display())));
                }
            }
        }
        Err(err("cannot create a unique temporary directory".to_owned()))
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        if self.keep {
            eprintln!("rokc: kept temporaries in {}", self.path.display());
        } else {
            let _ = std::fs::remove_dir_all(&self.path);
        }
    }
}

fn err(msg: String) -> RokDiagnostic {
    RokDiagnostic::error(ErrorKind::Linkage, msg)
}

/// Codegen a module to MLIR text, tagging the module with the target
/// triple so LLVM IR and clang agree on it.
pub fn mlir_text(
    module: &CompiledModule,
    opts: &BuildOptions,
) -> Result<rokc_codegen_mlir::MlirOutput, RokDiagnostic> {
    // ponytail: overflow checks follow -O0 (debug); add `-C overflow-checks` if
    // someone needs checked release builds.
    let overflow_checks = opts.opt_level == "0";
    let mut out = rokc_codegen_mlir::codegen_with_target(
        &module.mir,
        opts.target.as_deref(),
        overflow_checks,
        opts.debug,
        opts.repl.as_ref(),
    )?;
    let mut attrs = Vec::new();
    if let Some(t) = &opts.target {
        attrs.push(format!("llvm.target_triple = \"{t}\""));
    }
    if let Some(dl) = data_layout(opts) {
        attrs.push(format!("llvm.data_layout = \"{dl}\""));
    }
    if !attrs.is_empty() {
        out.text = out.text.replacen(
            "module {",
            &format!("module attributes {{{}}} {{", attrs.join(", ")),
            1,
        );
    }
    Ok(out)
}

/// The `target datalayout` clang uses for the target, so MLIR / LLVM fold
/// `sizeof` idioms with the real layout instead of LLVM's default one
/// (where `i64` is 4-aligned). `None` when clang is unavailable (`emit
/// mlir` without a toolchain); the build itself needs clang anyway.
/// Asked once per target (a REPL session builds many cells).
fn data_layout(opts: &BuildOptions) -> Option<String> {
    type Layouts = Vec<(Option<String>, Option<String>)>;
    static SEEN: std::sync::Mutex<Layouts> = std::sync::Mutex::new(Vec::new());
    let mut seen = SEEN
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some((_, dl)) = seen.iter().find(|(t, _)| *t == opts.target) {
        return dl.clone();
    }
    let dl = ask_data_layout(opts);
    seen.push((opts.target.clone(), dl.clone()));
    dl
}

fn ask_data_layout(opts: &BuildOptions) -> Option<String> {
    let mut cmd = clang(opts).ok()?;
    cmd.args(["-S", "-emit-llvm", "-x", "c", "-", "-o", "-"])
        .stdin(std::process::Stdio::null());
    let text = String::from_utf8(output(&mut cmd, "clang").ok()?).ok()?;
    let dl = text
        .lines()
        .find_map(|l| l.strip_prefix("target datalayout = \""))?;
    Some(dl.trim_end_matches('"').to_owned())
}

/// Produce one artifact's bytes.
pub fn emit(
    module: &CompiledModule,
    kind: EmitKind,
    opts: &BuildOptions,
) -> Result<Vec<u8>, RokDiagnostic> {
    match kind {
        EmitKind::Hir => Ok(rokc_hir::print_hir(&module.hir).into_bytes()),
        EmitKind::Mir => Ok(rokc_mir::print_mir(&module.mir).into_bytes()),
        EmitKind::Mlir => Ok(mlir_text(module, opts)?.text.into_bytes()),
        EmitKind::LlvmIr | EmitKind::Asm | EmitKind::Obj => {
            let tmp = TempDir::new(opts.keep_temps)?;
            let (ll, _) = llvm_ir(module, opts, tmp.path())?;
            if kind == EmitKind::LlvmIr {
                return std::fs::read(&ll).map_err(|e| err(format!("{}: {e}", ll.display())));
            }
            let out = tmp.path().join(format!("out.{}", kind.extension()));
            let mut cmd = clang(opts)?;
            cmd.arg(if kind == EmitKind::Asm { "-S" } else { "-c" });
            cmd.arg(&ll).arg("-o").arg(&out);
            run(&mut cmd, "clang")?;
            std::fs::read(&out).map_err(|e| err(format!("{}: {e}", out.display())))
        }
    }
}

/// Full build: MLIR → LLVM IR → executable at `exe_out`.
pub fn link_executable(
    module: &CompiledModule,
    link_libraries: &[String],
    opts: &BuildOptions,
    exe_out: &Path,
) -> Result<(), RokDiagnostic> {
    let tmp = TempDir::new(opts.keep_temps)?;
    let (ll, mlir) = llvm_ir(module, opts, tmp.path())?;
    // `--rokr` with an extension is a library path; otherwise `-l<name>`.
    // With a path, skip the codegen-hinted `-lrokr` so the linker does
    // not go looking for it on its search path.
    let mut cmd = clang(opts)?;
    cmd.arg(&ll);
    cmd.args(&module.archives);
    let rokr_is_path = Path::new(&opts.rokr).extension().is_some();
    if rokr_is_path {
        cmd.arg(&opts.rokr);
    } else {
        cmd.arg(format!("-l{}", opts.rokr));
    }
    for lib in link_libraries {
        cmd.arg(format!("-l{lib}"));
    }
    // core's float methods call libm (`floor`, `sin`, ..); glibc keeps it
    // out of libc.
    cmd.arg("-lm");
    for lib in &mlir.runtime_libraries {
        if !(lib == "rokr" && (rokr_is_path || opts.rokr == "rokr")) {
            cmd.arg(format!("-l{lib}"));
        }
    }
    cmd.arg("-o").arg(exe_out);
    run(&mut cmd, "clang")
}

/// A REPL cell (`opts.repl`) as a shared library at `out`: its runtime
/// symbols and earlier cells' slots resolve when the session host
/// loads it. Returns the GC type ids the cell used.
pub fn link_shared(
    module: &CompiledModule,
    link_libraries: &[String],
    opts: &BuildOptions,
    out: &Path,
) -> Result<u32, RokDiagnostic> {
    let mut cmd = clang(opts)?;
    cmd.args(["-shared", "-fPIC"]);
    if cfg!(target_vendor = "apple") {
        cmd.args(["-undefined", "dynamic_lookup"]);
    } else {
        // ponytail: untested off macOS. Each cell carries its own copy
        // of the library code; bind its calls to that copy.
        cmd.arg("-Wl,-Bsymbolic");
    }
    for lib in link_libraries {
        cmd.arg(format!("-l{lib}"));
    }
    piped_build(module, opts, cmd, out)
}

/// A REPL cell (`opts.repl`) as a relocatable object at `out`, which
/// the session host loads itself. Returns the GC type ids it used.
pub fn compile_object(
    module: &CompiledModule,
    opts: &BuildOptions,
    out: &Path,
) -> Result<u32, RokDiagnostic> {
    let mut cmd = clang(opts)?;
    cmd.arg("-c");
    piped_build(module, opts, cmd, out)
}

/// `mlir-opt | mlir-translate | clang <cmd> -x ir -`: the three tools
/// start together (most of each one's time is its own startup) and no
/// intermediate file is written. Without `tls_initial_exec`: the
/// general-dynamic model is what a loaded cell wants anyway (Mach-O
/// ignores the model).
fn piped_build(
    module: &CompiledModule,
    opts: &BuildOptions,
    mut cc: Command,
    out: &Path,
) -> Result<u32, RokDiagnostic> {
    let mlir = mlir_text(module, opts)?;
    let spawn = |cmd: &mut Command, what: &str| {
        cmd.stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| err(format!("cannot run {what}: {e}")))
    };
    let mut opt = Command::new(locate_tool("mlir-opt")?);
    opt.args(opt_passes(opts)).stdin(Stdio::piped());
    let mut opt = spawn(&mut opt, "mlir-opt")?;
    let mut translate = Command::new(locate_tool("mlir-translate")?);
    translate
        .arg("--mlir-to-llvmir")
        .stdin(opt.stdout.take().expect("piped stdout"));
    let mut translate = spawn(&mut translate, "mlir-translate")?;
    cc.args(["-x", "ir", "-", "-o"])
        .arg(out)
        .stdin(translate.stdout.take().expect("piped stdout"));
    let cc = spawn(&mut cc, "clang")?;
    let mut stdin = opt.stdin.take().expect("piped stdin");
    let text = mlir.text;
    let writer = std::thread::spawn(move || stdin.write_all(text.as_bytes()));
    // Each one's stderr on its own thread: a full pipe cannot stall the
    // others.
    let waits = [
        (opt, "mlir-opt"),
        (translate, "mlir-translate"),
        (cc, "clang"),
    ]
    .map(|(c, what)| (std::thread::spawn(move || c.wait_with_output()), what));
    let _ = writer.join();
    for (w, what) in waits {
        let o = w
            .join()
            .map_err(|_| err(format!("{what} waiter panicked")))?
            .map_err(|e| err(format!("{what}: {e}")))?;
        if !o.status.success() {
            // The first tool that failed says why; the later ones only
            // saw its missing output.
            return Err(err(format!(
                "{what} failed:\n{}",
                String::from_utf8_lossy(&o.stderr)
            )));
        }
    }
    Ok(mlir.gc_types)
}

fn opt_passes(opts: &BuildOptions) -> Vec<&'static str> {
    let mut v = Vec::new();
    if opts.opt_level != "0" {
        v.extend(["--canonicalize", "--cse"]);
    }
    if opts.debug {
        // Keep the locations in the text mlir-translate reads.
        v.push("--mlir-print-debuginfo");
    }
    v.extend([
        "--convert-func-to-llvm",
        "--convert-arith-to-llvm",
        "--convert-cf-to-llvm",
        "--finalize-memref-to-llvm",
        "--reconcile-unrealized-casts",
    ]);
    v
}

/// The REPL's session host: the C program `c_src` with the whole
/// runtime linked in and exported, for the cells it loads.
pub fn link_host(c_src: &Path, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
    let mut cmd = clang(opts)?;
    cmd.arg(c_src);
    let whole = if Path::new(&opts.rokr).extension().is_some() {
        opts.rokr.clone()
    } else {
        format!("-l{}", opts.rokr)
    };
    if cfg!(target_vendor = "apple") {
        cmd.arg("-Wl,-all_load").arg(whole);
    } else {
        cmd.args(["-rdynamic", "-Wl,--whole-archive"])
            .arg(whole)
            .args(["-Wl,--no-whole-archive", "-ldl", "-lpthread"]);
    }
    cmd.arg("-lm").arg("-o").arg(out);
    run(&mut cmd, "clang")
}

/// Library build (spec 902.13): `target/foo.o` + `ar rcs target/libfoo.a`,
/// and, for a prebuilt-library build (`CompiledModule::interface`), its
/// RHIR `foo.rhir` beside them (spec 904).
// ponytail: the RHIR is a sibling file, not an `.a` member `foo.hir.o`
// (903): no object-section writer / reader needed.
pub fn build_archive(
    module: &CompiledModule,
    opts: &BuildOptions,
    archive_out: &Path,
) -> Result<(), RokDiagnostic> {
    let stem = archive_out
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("out");
    let name = stem.strip_prefix("lib").unwrap_or(stem);
    let obj = archive_out.with_file_name(format!("{name}.o"));
    let tmp = TempDir::new(opts.keep_temps)?;
    let (ll, mlir) = llvm_ir(module, opts, tmp.path())?;
    let mut cmd = clang(opts)?;
    run(cmd.arg("-c").arg(&ll).arg("-o").arg(&obj), "clang")?;
    // `ar r` appends to an existing archive; start fresh.
    let _ = std::fs::remove_file(archive_out);
    let ar = locate_tool("ar").or_else(|_| locate_tool("llvm-ar"))?;
    run(Command::new(ar).arg("rcs").arg(archive_out).arg(&obj), "ar")?;
    if let Some(r) = &module.interface {
        let mut r = r.clone();
        r.type_count = mlir.gc_types;
        let path = archive_out.with_file_name(format!("{}.rhir", r.name));
        std::fs::write(&path, r.encode())
            .map_err(|e| err(format!("cannot write {}: {e}", path.display())))?;
    }
    Ok(())
}

fn llvm_ir(
    module: &CompiledModule,
    opts: &BuildOptions,
    dir: &Path,
) -> Result<(PathBuf, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let mlir = mlir_text(module, opts)?;
    let mlir_path = dir.join("module.mlir");
    std::fs::write(&mlir_path, &mlir.text)
        .map_err(|e| err(format!("cannot write {}: {e}", mlir_path.display())))?;

    let mut opt = Command::new(locate_tool("mlir-opt")?);
    opt.args(opt_passes(opts)).arg(&mlir_path);
    let opt_out = output(&mut opt, "mlir-opt")?;

    let mut translate = Command::new(locate_tool("mlir-translate")?)
        .arg("--mlir-to-llvmir")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| err(format!("cannot run mlir-translate: {e}")))?;
    // Write on a thread so a large stdout cannot deadlock the pipe.
    let mut stdin = translate.stdin.take().expect("piped stdin");
    let writer = std::thread::spawn(move || stdin.write_all(&opt_out));
    let out = translate
        .wait_with_output()
        .map_err(|e| err(format!("mlir-translate: {e}")))?;
    writer
        .join()
        .map_err(|_| err("mlir-translate stdin writer panicked".to_owned()))?
        .map_err(|e| err(format!("cannot feed mlir-translate: {e}")))?;
    if !out.status.success() {
        return Err(err(format!(
            "mlir-translate failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        )));
    }
    let ll_path = dir.join("module.ll");
    let ll = String::from_utf8(out.stdout)
        .map_err(|_| err("mlir-translate printed non-UTF-8 LLVM IR".to_owned()))?;
    std::fs::write(&ll_path, tls_initial_exec(&ll))
        .map_err(|e| err(format!("cannot write {}: {e}", ll_path.display())))?;
    Ok((ll_path, mlir))
}

/// 803 §8.3.8: the `rok_tls_*` slots use the initial-exec TLS model
/// (the runtime is always linked into the executable). MLIR's
/// `llvm.mlir.global` has no TLS-model attribute, so the external
/// declarations are rewritten in the translated LLVM IR. Mach-O ignores
/// the model (TLV access); ELF gets `@gottpoff` instead of
/// `__tls_get_addr`.
fn tls_initial_exec(ll: &str) -> String {
    let mut out = String::with_capacity(ll.len() + 64);
    for line in ll.split_inclusive('\n') {
        if line.starts_with("@rok_tls_") {
            out.push_str(&line.replacen(" thread_local ", " thread_local(initialexec) ", 1));
        } else {
            out.push_str(line);
        }
    }
    out
}

fn clang(opts: &BuildOptions) -> Result<Command, RokDiagnostic> {
    let mut cmd = Command::new(locate_tool("clang")?);
    cmd.arg("-Wno-override-module")
        .arg(format!("-O{}", opts.opt_level));
    if opts.debug {
        // Also makes clang run `dsymutil` after a macOS link.
        cmd.arg("-g");
    }
    if let Some(t) = &opts.target {
        cmd.arg(format!("--target={t}"));
    }
    Ok(cmd)
}

fn output(cmd: &mut Command, what: &str) -> Result<Vec<u8>, RokDiagnostic> {
    let out = cmd
        .output()
        .map_err(|e| err(format!("cannot run {what}: {e}")))?;
    if !out.status.success() {
        return Err(err(format!(
            "{what} failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        )));
    }
    Ok(out.stdout)
}

fn run(cmd: &mut Command, what: &str) -> Result<(), RokDiagnostic> {
    output(cmd, what).map(drop)
}

fn locate_tool(name: &str) -> Result<PathBuf, RokDiagnostic> {
    let path = std::env::var_os("PATH").unwrap_or_default();
    std::env::split_paths(&path)
        .map(|dir| dir.join(name))
        .find(|c| c.is_file())
        .ok_or_else(|| err(format!("cannot find `{name}` in PATH (needed to build)")))
}

#[cfg(test)]
mod tests {
    #[test]
    fn rok_tls_slots_are_initial_exec() {
        let ll = "@rok_tls_yield_flag = external thread_local global i8\n\
                  @other = external thread_local global i8\n\
                  @rok_tls_tlab_cursor = external thread_local global i64\n\
                  define void @f() {\n  ret void\n}";
        assert_eq!(
            super::tls_initial_exec(ll),
            "@rok_tls_yield_flag = external thread_local(initialexec) global i8\n\
             @other = external thread_local global i8\n\
             @rok_tls_tlab_cursor = external thread_local(initialexec) global i64\n\
             define void @f() {\n  ret void\n}"
        );
    }
}

//! Native back half of the AOT pipeline (spec 902.11-902.14): MLIR text
//! → `mlir-opt` → `mlir-translate` (`lower_to_llvm`) → `clang`
//! (`finish`). rokc links no LLVM, so the tools run as processes.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use rokc_diagnostic::{ErrorKind, RokDiagnostic};

use crate::CompiledModule;

/// Intermediate artifact selectable with `--emit=<kind>` (spec 901).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EmitKind {
    /// The user package's whole AST after meta expansion and the
    /// parser's desugaring, as rok source; needs the parsed files
    /// (`keep_ast`). (`expanded` shows the meta expansions alone.)
    Ast,
    Hir,
    Mir,
    Mlir,
    LlvmIr,
    Asm,
    Obj,
    /// Meta expansions as source text (spec 6.9.9); needs the parsed
    /// sources (`Session::set_keep_ast`), so `CompileResult::emit` makes it.
    Expanded,
}

impl EmitKind {
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "ast" => Self::Ast,
            "hir" => Self::Hir,
            "mir" => Self::Mir,
            "mlir" => Self::Mlir,
            "llvmir" | "llvm-ir" | "ll" => Self::LlvmIr,
            "asm" => Self::Asm,
            "obj" => Self::Obj,
            "expanded" => Self::Expanded,
            _ => return None,
        })
    }

    /// File extension used under `target/`.
    #[must_use]
    pub const fn extension(self) -> &'static str {
        match self {
            Self::Ast => "ast.rok",
            Self::Hir => "hir",
            Self::Mir => "mir",
            Self::Mlir => "mlir",
            Self::LlvmIr => "ll",
            Self::Asm => "s",
            Self::Obj => "o",
            Self::Expanded => "expanded.rok",
        }
    }
}

/// How to build native code; the target is the compiled module's.
#[derive(Clone, Debug)]
pub struct BuildOptions {
    /// `0`..`3` or `s`, forwarded to clang as `-O<level>`.
    pub opt_level: String,
    /// Runtime library: a path when it has an extension, else `-l<name>`.
    pub rokr: String,
    /// Keep the scratch directory instead of deleting it.
    pub keep_temps: bool,
    /// `-g`: DWARF debug info (spec 9.9.6).
    pub debug: bool,
    /// Codegen a REPL cell (`cell_ir`).
    pub repl: Option<rokc_codegen_mlir::ReplCell>,
    /// `-C overflow-checks=yes|no`; `None` = on at `-O0` only.
    pub overflow_checks: Option<bool>,
    /// `--load-mlir-plugin`: MLIR dialect plugins `mlir-opt` loads
    /// (`--load-dialect-plugin`, stdlib bare 1.10).
    pub mlir_dialect_plugins: Vec<PathBuf>,
    /// `--load-mlir-pass-plugin`: MLIR pass plugins (`--load-pass-plugin`).
    pub mlir_pass_plugins: Vec<PathBuf>,
    /// `--mlir-pass <pass>`: extra `mlir-opt` passes, run before the
    /// lowering to the LLVM dialect (a plugin dialect's own lowering).
    pub mlir_passes: Vec<String>,
}

impl Default for BuildOptions {
    fn default() -> Self {
        Self {
            opt_level: "0".to_owned(),
            rokr: "rokr".to_owned(),
            keep_temps: false,
            debug: false,
            repl: None,
            overflow_checks: None,
            mlir_dialect_plugins: Vec::new(),
            mlir_pass_plugins: Vec::new(),
            mlir_passes: Vec::new(),
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

/// Codegen a module to MLIR text for its target.
pub fn mlir_text(
    module: &CompiledModule,
    opts: &BuildOptions,
) -> Result<rokc_codegen_mlir::MlirOutput, RokDiagnostic> {
    let triple = module.mir.target.triple.as_deref();
    rokc_codegen_mlir::codegen(
        &module.mir,
        &rokc_codegen_mlir::CodegenOptions {
            overflow_checks: opts.overflow_checks.unwrap_or(opts.opt_level == "0"),
            debug: opts.debug,
            repl: opts.repl.clone(),
            data_layout: data_layout(triple, opts),
        },
    )
}

/// The `target datalayout` clang uses for `triple`, so MLIR / LLVM fold
/// `sizeof` idioms with the real layout instead of LLVM's default one
/// (where `i64` is 4-aligned). `None` without clang (`--emit=mlir`
/// needs no toolchain). Asked once per target (a REPL session builds
/// many cells).
fn data_layout(triple: Option<&str>, opts: &BuildOptions) -> Option<String> {
    type Layouts = Vec<(Option<String>, Option<String>)>;
    static SEEN: std::sync::Mutex<Layouts> = std::sync::Mutex::new(Vec::new());
    let mut seen = SEEN
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some((_, dl)) = seen.iter().find(|(t, _)| t.as_deref() == triple) {
        return dl.clone();
    }
    let dl = (|| {
        let mut cmd = clang(opts, triple).ok()?;
        cmd.args(["-S", "-emit-llvm", "-x", "c", "-", "-o", "-"])
            .stdin(Stdio::null());
        let text = String::from_utf8(output(&mut cmd, "clang").ok()?).ok()?;
        let dl = text
            .lines()
            .find_map(|l| l.strip_prefix("target datalayout = \""))?;
        Some(dl.trim_end_matches('"').to_owned())
    })();
    seen.push((triple.map(str::to_owned), dl.clone()));
    dl
}

/// Produce one artifact's bytes.
pub fn emit(
    module: &CompiledModule,
    kind: EmitKind,
    opts: &BuildOptions,
) -> Result<Vec<u8>, RokDiagnostic> {
    match kind {
        EmitKind::Ast => Err(RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Internal,
            "--emit=ast needs the parsed files (keep_ast)",
        )),
        EmitKind::Hir => Ok(rokc_hir::print_hir(&module.hir).into_bytes()),
        EmitKind::Mir => Ok(rokc_mir::print_mir(&module.mir).into_bytes()),
        EmitKind::Expanded => Err(err("`--emit=expanded` needs the parsed sources".to_owned())),
        EmitKind::Mlir => Ok(mlir_text(module, opts)?.text.into_bytes()),
        EmitKind::LlvmIr => Ok(lower_to_llvm(module, opts)?.0.into_bytes()),
        EmitKind::Asm | EmitKind::Obj => {
            let tmp = TempDir::new(opts.keep_temps)?;
            let out = tmp.path().join(format!("out.{}", kind.extension()));
            let what = if kind == EmitKind::Asm {
                Artifact::Asm
            } else {
                Artifact::Obj
            };
            finish(module, &lower_to_llvm(module, opts)?.0, what, opts, &out)?;
            std::fs::read(&out).map_err(|e| err(format!("{}: {e}", out.display())))
        }
    }
}

/// What `finish` makes of a module's LLVM IR.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Artifact {
    /// An executable linked with the runtime and the dependencies.
    Exe,
    /// `lib<name>.a` (spec 902.13), the object beside it.
    Archive,
    Obj,
    Asm,
}

/// Full build: an executable at `out`.
pub fn link_executable(
    module: &CompiledModule,
    opts: &BuildOptions,
    out: &Path,
) -> Result<(), RokDiagnostic> {
    let (ll, _) = lower_to_llvm(module, opts)?;
    finish(module, &ll, Artifact::Exe, opts, out)
}

/// Library build (spec 902.13): `foo.o` + `libfoo.a`.
///
/// For a prebuilt-library build (`CompiledModule::interface`), its RHIR
/// `foo.rhir` beside them (spec 904). The RHIR is a sibling file rather
/// than an archive member (903): no object-section reader is needed.
pub fn build_archive(
    module: &CompiledModule,
    opts: &BuildOptions,
    archive_out: &Path,
) -> Result<(), RokDiagnostic> {
    let (ll, mlir) = lower_to_llvm(module, opts)?;
    finish(module, &ll, Artifact::Archive, opts, archive_out)?;
    if let Some(r) = &module.interface {
        let mut r = r.clone();
        r.type_count = mlir.gc_types;
        let path = archive_out.with_file_name(format!("{}.rhir", r.name));
        std::fs::write(&path, r.encode())
            .map_err(|e| err(format!("cannot write {}: {e}", path.display())))?;
    }
    Ok(())
}

/// A REPL cell (`opts.repl`) as LLVM IR text for the session host's JIT.
pub fn cell_ir(
    module: &CompiledModule,
    opts: &BuildOptions,
) -> Result<(Vec<u8>, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let (ll, mlir) = lower_to_llvm(module, opts)?;
    Ok((ll.into_bytes(), mlir))
}

/// MLIR → LLVM IR text through `mlir-opt | mlir-translate`, started
/// together (most of each one's time is its own startup).
pub fn lower_to_llvm(
    module: &CompiledModule,
    opts: &BuildOptions,
) -> Result<(String, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let mut mlir = mlir_text(module, opts)?;
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
    let translate = spawn(&mut translate, "mlir-translate")?;
    let mut stdin = opt.stdin.take().expect("piped stdin");
    let text = std::mem::take(&mut mlir.text);
    let writer = std::thread::spawn(move || stdin.write_all(text.as_bytes()));
    // Each one's stderr on its own thread: a full pipe cannot stall the
    // other.
    let waits = [(opt, "mlir-opt"), (translate, "mlir-translate")]
        .map(|(c, what)| (std::thread::spawn(move || c.wait_with_output()), what));
    let _ = writer.join();
    let mut ir = Vec::new();
    for (w, what) in waits {
        let o = w
            .join()
            .map_err(|_| err(format!("{what} waiter panicked")))?
            .map_err(|e| err(format!("{what}: {e}")))?;
        if failed(&o) {
            // The first tool that failed says why; the later one only saw
            // its missing output.
            return Err(err(format!(
                "{what} failed:\n{}",
                String::from_utf8_lossy(&o.stderr)
            )));
        }
        ir = o.stdout;
    }
    let ll = String::from_utf8(ir)
        .map_err(|_| err("mlir-translate printed non-UTF-8 LLVM IR".to_owned()))?;
    // JIT'd code keeps the general-dynamic TLS model.
    let ll = if opts.repl.is_some() {
        ll
    } else {
        tls_initial_exec(&ll)
    };
    Ok((ll, mlir))
}

/// LLVM IR `ll` of `module` → `out` through clang (and `ar`).
pub fn finish(
    module: &CompiledModule,
    ll: &str,
    what: Artifact,
    opts: &BuildOptions,
    out: &Path,
) -> Result<(), RokDiagnostic> {
    let tmp = TempDir::new(opts.keep_temps)?;
    let ll_path = tmp.path().join("module.ll");
    std::fs::write(&ll_path, ll)
        .map_err(|e| err(format!("cannot write {}: {e}", ll_path.display())))?;
    let mut cmd = clang(opts, module.mir.target.triple.as_deref())?;
    match what {
        Artifact::Exe => {
            cmd.arg(&ll_path).args(&module.archives).arg(rokr_arg(opts));
            // core's float methods call libm; glibc keeps it out of libc.
            cmd.arg("-lm").arg("-o").arg(out);
            run(&mut cmd, "clang")
        }
        Artifact::Obj | Artifact::Asm => {
            cmd.arg(if what == Artifact::Asm { "-S" } else { "-c" });
            run(cmd.arg(&ll_path).arg("-o").arg(out), "clang")
        }
        Artifact::Archive => {
            let stem = out.file_stem().and_then(|s| s.to_str()).unwrap_or("out");
            let name = stem.strip_prefix("lib").unwrap_or(stem);
            let obj = out.with_file_name(format!("{name}.o"));
            run(cmd.arg("-c").arg(&ll_path).arg("-o").arg(&obj), "clang")?;
            // `ar r` appends to an existing archive; start fresh.
            let _ = std::fs::remove_file(out);
            let ar = locate_tool("ar").or_else(|_| locate_tool("llvm-ar"))?;
            run(Command::new(ar).arg("rcs").arg(out).arg(&obj), "ar")
        }
    }
}

/// `--rokr`: a library path when it has an extension, else `-l<name>`.
fn rokr_arg(opts: &BuildOptions) -> String {
    if Path::new(&opts.rokr).extension().is_some() {
        opts.rokr.clone()
    } else {
        format!("-l{}", opts.rokr)
    }
}

fn opt_passes(opts: &BuildOptions) -> Vec<String> {
    let mut v: Vec<String> = Vec::new();
    let plugins = [
        ("--load-dialect-plugin", &opts.mlir_dialect_plugins),
        ("--load-pass-plugin", &opts.mlir_pass_plugins),
    ];
    for (flag, paths) in plugins {
        v.extend(paths.iter().map(|p| format!("{flag}={}", p.display())));
    }
    v.extend(opts.mlir_passes.iter().map(|p| format!("--{p}")));
    if opts.opt_level != "0" {
        v.extend(["--canonicalize".to_owned(), "--cse".to_owned()]);
    }
    if opts.debug {
        // Keep the locations in the text mlir-translate reads.
        v.push("--mlir-print-debuginfo".to_owned());
    }
    v.extend(
        [
            // `scf` / `memref` ops written with `__mlir_op` (bare 1.9).
            "--convert-scf-to-cf",
            "--convert-func-to-llvm",
            "--convert-arith-to-llvm",
            "--convert-cf-to-llvm",
            "--finalize-memref-to-llvm",
            "--reconcile-unrealized-casts",
        ]
        .map(str::to_owned),
    );
    v
}

/// `--load-mlir-plugin <path | name>` (stdlib bare 1.10.3): a path must
/// exist; a bare name is `lib<name>.{dylib,so}` / `<name>.dll` in a
/// directory of `ROK_MLIR_PLUGIN_PATH`.
///
/// # Errors
/// The plugin is not there.
pub fn find_mlir_plugin(spec: &str) -> Result<PathBuf, String> {
    let p = Path::new(spec);
    if p.components().count() > 1 || p.extension().is_some() {
        return if p.is_file() {
            Ok(p.to_path_buf())
        } else {
            Err(format!("MLIR plugin `{spec}`: no such file"))
        };
    }
    let dirs = std::env::var_os("ROK_MLIR_PLUGIN_PATH").unwrap_or_default();
    let names = [
        format!("lib{spec}.dylib"),
        format!("lib{spec}.so"),
        format!("{spec}.dll"),
    ];
    std::env::split_paths(&dirs)
        .flat_map(|d| names.iter().map(move |n| d.join(n)))
        .find(|c| c.is_file())
        .ok_or_else(|| {
            format!("MLIR plugin `{spec}` not found (looked for lib{spec}.dylib / .so in ROK_MLIR_PLUGIN_PATH)")
        })
}

/// The REPL's session host: the C program `c_src` with the whole
/// runtime linked in and exported, for the cells it JIT-compiles, and
/// LLVM's ORC JIT (`libLLVM`, found by `llvm_prefix`).
pub fn link_host(c_src: &Path, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
    let mut cmd = clang(opts, None)?;
    cmd.arg(c_src);
    let whole = rokr_arg(opts);
    if cfg!(target_vendor = "apple") {
        cmd.arg("-Wl,-all_load").arg(whole);
    } else {
        cmd.args(["-rdynamic", "-Wl,--whole-archive"])
            .arg(whole)
            .args(["-Wl,--no-whole-archive", "-ldl", "-lpthread"]);
    }
    let llvm = llvm_prefix()?;
    cmd.arg(format!("-I{}", llvm.join("include").display()))
        .arg(format!("-L{}", llvm.join("lib").display()))
        .arg(format!("-Wl,-rpath,{}", llvm.join("lib").display()))
        .arg("-lLLVM");
    cmd.arg("-lm").arg("-o").arg(out);
    run(&mut cmd, "clang")
}

/// The LLVM install the toolchain's `mlir-translate` belongs to (its
/// `bin/..`): the session host JITs that tool's LLVM IR with the same
/// LLVM's ORC (`lib/libLLVM`, the C API headers in `include/llvm-c`).
fn llvm_prefix() -> Result<PathBuf, RokDiagnostic> {
    let tool = locate_tool("mlir-translate")?;
    let tool = std::fs::canonicalize(&tool).unwrap_or(tool);
    let prefix = tool
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .unwrap_or_default();
    let lib = ["libLLVM.dylib", "libLLVM.so"]
        .iter()
        .any(|l| prefix.join("lib").join(l).is_file());
    let header = prefix.join("include/llvm-c/LLJIT.h");
    if !lib {
        return Err(err(format!(
            "the REPL needs LLVM's shared library (libLLVM.dylib / libLLVM.so) in {}, \
             the LLVM {} belongs to",
            prefix.join("lib").display(),
            tool.display()
        )));
    }
    if !header.is_file() {
        return Err(err(format!(
            "the REPL needs LLVM's C API headers ({} is missing)",
            header.display()
        )));
    }
    Ok(prefix)
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

fn clang(opts: &BuildOptions, triple: Option<&str>) -> Result<Command, RokDiagnostic> {
    let mut cmd = Command::new(locate_tool("clang")?);
    cmd.arg("-Wno-override-module")
        .arg(format!("-O{}", opts.opt_level));
    if opts.debug {
        // Also makes clang run `dsymutil` after a macOS link.
        cmd.arg("-g");
    }
    if let Some(t) = triple {
        cmd.arg(format!("--target={t}"));
    }
    Ok(cmd)
}

/// A tool failed — or `mlir-opt` could not load an MLIR plugin, which it
/// only reports ("Failed to load .. Request ignored.") and goes on.
fn failed(o: &std::process::Output) -> bool {
    !o.status.success() || o.stderr.windows(15).any(|w| w == b"Failed to load ")
}

fn output(cmd: &mut Command, what: &str) -> Result<Vec<u8>, RokDiagnostic> {
    let out = cmd
        .output()
        .map_err(|e| err(format!("cannot run {what}: {e}")))?;
    if failed(&out) {
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
    fn mlir_plugins_reach_mlir_opt_before_the_llvm_lowering() {
        let opts = super::BuildOptions {
            mlir_dialect_plugins: vec!["/p/libd.so".into()],
            mlir_pass_plugins: vec!["/p/libpass.so".into()],
            mlir_passes: vec!["convert-d-to-llvm".to_owned()],
            ..super::BuildOptions::default()
        };
        let v = super::opt_passes(&opts);
        assert_eq!(
            v[..3],
            [
                "--load-dialect-plugin=/p/libd.so",
                "--load-pass-plugin=/p/libpass.so",
                "--convert-d-to-llvm"
            ]
        );
        assert!(v.iter().any(|f| f == "--convert-func-to-llvm"));
        assert!(super::find_mlir_plugin("/no/such/libx.so").is_err());
        assert!(super::find_mlir_plugin("no_such_plugin_xyz").is_err());
    }

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

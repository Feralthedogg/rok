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
            Self::Hir => "hir.rok",
            Self::Mir => "mir.rok",
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
}

impl Default for BuildOptions {
    fn default() -> Self {
        Self {
            target: None,
            opt_level: "0".to_owned(),
            rokr: "rokr".to_owned(),
            keep_temps: false,
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
    )?;
    if let Some(t) = &opts.target {
        out.text = out.text.replacen(
            "module {",
            &format!("module attributes {{llvm.target_triple = \"{t}\"}} {{"),
            1,
        );
    }
    Ok(out)
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
    let rokr_is_path = Path::new(&opts.rokr).extension().is_some();
    if rokr_is_path {
        cmd.arg(&opts.rokr);
    } else {
        cmd.arg(format!("-l{}", opts.rokr));
    }
    for lib in link_libraries {
        cmd.arg(format!("-l{lib}"));
    }
    for lib in &mlir.runtime_libraries {
        if !(lib == "rokr" && (rokr_is_path || opts.rokr == "rokr")) {
            cmd.arg(format!("-l{lib}"));
        }
    }
    cmd.arg("-o").arg(exe_out);
    run(&mut cmd, "clang")
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
    if opts.opt_level != "0" {
        opt.args(["--canonicalize", "--cse"]);
    }
    opt.args([
        "--convert-func-to-llvm",
        "--convert-arith-to-llvm",
        "--convert-cf-to-llvm",
        "--finalize-memref-to-llvm",
        "--reconcile-unrealized-casts",
    ])
    .arg(&mlir_path);
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
    std::fs::write(&ll_path, &out.stdout)
        .map_err(|e| err(format!("cannot write {}: {e}", ll_path.display())))?;
    Ok((ll_path, mlir))
}

fn clang(opts: &BuildOptions) -> Result<Command, RokDiagnostic> {
    let mut cmd = Command::new(locate_tool("clang")?);
    cmd.arg("-Wno-override-module")
        .arg(format!("-O{}", opts.opt_level));
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

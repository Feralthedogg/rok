//! Native back half of the AOT pipeline (spec 902.11-902.14), in
//! process: the MLIR passes, the translation to LLVM IR, LLVM's
//! optimization and code generation, and the link (lld) through the
//! LLVM / MLIR / lld rokc links statically (`rokc_llvm`). `ROK_CC`, when
//! set, links instead.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

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
    /// `0`..`3`, `s` or `z`: LLVM's `-O<level>`.
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
    /// `--load-mlir-plugin`: MLIR dialect plugins (stdlib bare 1.10).
    pub mlir_dialect_plugins: Vec<PathBuf>,
    /// `--load-mlir-pass-plugin`: MLIR pass plugins.
    pub mlir_pass_plugins: Vec<PathBuf>,
    /// `--mlir-pass <pass>`: extra MLIR passes, run before the
    /// lowering to the LLVM dialect (a plugin dialect's own lowering).
    pub mlir_passes: Vec<String>,
    /// `-C backend=native|llvm` (else `ROK_BACKEND`): who generates the
    /// machine code (`native::object`).
    pub backend: Option<String>,
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
            backend: std::env::var("ROK_BACKEND").ok().filter(|b| !b.is_empty()),
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
    let data_layout = rokc_diagnostic::time("data layout", || {
        rokc_llvm::data_layout(&target(triple)).ok()
    });
    codegen(module, opts, data_layout)
}

/// Codegen for its errors alone (`rokc check`).
pub fn check_codegen(module: &CompiledModule, opts: &BuildOptions) -> Result<(), RokDiagnostic> {
    codegen(module, opts, None).map(drop)
}

fn codegen(
    module: &CompiledModule,
    opts: &BuildOptions,
    data_layout: Option<String>,
) -> Result<rokc_codegen_mlir::MlirOutput, RokDiagnostic> {
    rokc_diagnostic::time("mlir emit", || {
        rokc_codegen_mlir::codegen(
            &module.mir,
            &rokc_codegen_mlir::CodegenOptions {
                overflow_checks: opts.overflow_checks.unwrap_or(opts.opt_level == "0"),
                debug: opts.debug,
                repl: opts.repl.clone(),
                data_layout,
            },
        )
    })
}

/// The LLVM target of a module's `--target` triple (`None`: this machine).
fn target(triple: Option<&str>) -> rokc_llvm::Target {
    triple.map_or_else(rokc_llvm::Target::host, rokc_llvm::Target::new)
}

/// Produce one artifact's bytes.
pub fn emit(
    module: &CompiledModule,
    kind: EmitKind,
    opts: &BuildOptions,
) -> Result<Vec<u8>, RokDiagnostic> {
    if kind == EmitKind::Obj {
        if let Some(o) = crate::native::object(module, opts)? {
            return Ok(o.object);
        }
    }
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
        EmitKind::Asm => Ok(llvm(module, opts, rokc_llvm::Emit::Asm, 1)?.0.remove(0)),
        EmitKind::Obj => Ok(llvm(module, opts, rokc_llvm::Emit::Obj, 1)?.0.remove(0)),
    }
}

/// Full build: an executable at `out`.
pub fn link_executable(
    module: &CompiledModule,
    opts: &BuildOptions,
    out: &Path,
) -> Result<(), RokDiagnostic> {
    let objects = if let Some(o) = crate::native::object(module, opts)? {
        vec![o.object]
    } else {
        llvm(module, opts, rokc_llvm::Emit::Obj, 0)?.0
    };
    let tmp = TempDir::new(opts.keep_temps)?;
    let mut paths = Vec::new();
    for (i, o) in objects.iter().enumerate() {
        let p = tmp.path().join(format!("module{i}.o"));
        std::fs::write(&p, o).map_err(|e| err(format!("cannot write {}: {e}", p.display())))?;
        paths.push(p);
    }
    link_object(module, &paths, opts, out)
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
    let (object, gc_types) = if let Some(o) = crate::native::object(module, opts)? {
        (o.object, o.gc_types)
    } else {
        let (mut objs, mlir) = llvm(module, opts, rokc_llvm::Emit::Obj, 1)?;
        (objs.remove(0), mlir.gc_types)
    };
    let obj = object_beside(archive_out);
    std::fs::write(&obj, object)
        .map_err(|e| err(format!("cannot write {}: {e}", obj.display())))?;
    // A fresh archive, not members appended to an old one.
    let _ = std::fs::remove_file(archive_out);
    let t = target(module.mir.target.triple.as_deref());
    rokc_llvm::write_archive(&t, archive_out, &[&obj])
        .map_err(|e| err(format!("cannot write {}: {e}", archive_out.display())))?;
    if let Some(r) = &module.interface {
        let mut r = r.clone();
        r.type_count = gc_types;
        let path = archive_out.with_file_name(format!("{}.rhir", r.name));
        std::fs::write(&path, r.encode())
            .map_err(|e| err(format!("cannot write {}: {e}", path.display())))?;
    }
    Ok(())
}

/// A REPL cell (`opts.repl`) as an object for the session host, built by
/// LLVM, and what codegen says about it.
pub fn cell_object(
    module: &CompiledModule,
    opts: &BuildOptions,
) -> Result<(Vec<u8>, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let (mut objs, mlir) = llvm(module, opts, rokc_llvm::Emit::Obj, 1)?;
    Ok((objs.remove(0), mlir))
}

/// The module's LLVM IR, as translated from MLIR (`--emit=llvm-ir`).
pub fn lower_to_llvm(
    module: &CompiledModule,
    opts: &BuildOptions,
) -> Result<(String, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let (mut ir, mlir) = llvm(module, opts, rokc_llvm::Emit::LlvmIr, 1)?;
    let ir =
        String::from_utf8(ir.remove(0)).map_err(|_| err("LLVM printed non-UTF-8 IR".to_owned()))?;
    Ok((ir, mlir))
}

/// MLIR text below this size compiles as one object: splitting costs
/// more than the cores win back.
const SPLIT_MIN: usize = 1 << 20;

/// The module through LLVM in process: the MLIR passes (plugins' first),
/// the translation to LLVM IR, `-O<level>` and code generation. `parts`
/// 0: as many objects as the module's size makes worth compiling in
/// parallel (the whole module optimized first, so inlining still sees
/// every function).
fn llvm(
    module: &CompiledModule,
    opts: &BuildOptions,
    emit: rokc_llvm::Emit,
    parts: usize,
) -> Result<(Vec<Vec<u8>>, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let mut mlir = mlir_text(module, opts)?;
    let t = target(module.mir.target.triple.as_deref());
    let opt = rokc_llvm::OptLevel::parse(&opts.opt_level)
        .ok_or_else(|| err(format!("unknown optimization level `{}`", opts.opt_level)))?;
    let pipeline = rokc_llvm::mlir_pipeline(opts.opt_level != "0", &opts.mlir_passes);
    let dialects: Vec<&Path> = opts
        .mlir_dialect_plugins
        .iter()
        .map(PathBuf::as_path)
        .collect();
    let passes: Vec<&Path> = opts
        .mlir_pass_plugins
        .iter()
        .map(PathBuf::as_path)
        .collect();
    let c = rokc_llvm::Compile {
        target: &t,
        opt,
        emit,
        // JIT'd cells keep the general-dynamic model.
        tls_initial_exec: opts.repl.is_none(),
        mlir_pipeline: &pipeline,
        dialect_plugins: &dialects,
        pass_plugins: &passes,
    };
    let parts = if parts == 0 {
        let cores = std::thread::available_parallelism().map_or(1, usize::from);
        let jobs = cores.min(mlir.text.len() / (SPLIT_MIN / 4)).min(16);
        if mlir.text.len() < SPLIT_MIN || jobs < 2 {
            1
        } else {
            jobs
        }
    } else {
        parts
    };
    let text = std::mem::take(&mut mlir.text);
    let out = rokc_diagnostic::time("llvm", || {
        if parts > 1 {
            rokc_llvm::compile_mlir_split(&text, &c, parts)
        } else {
            rokc_llvm::compile_mlir(&text, &c).map(|o| vec![o])
        }
    })
    .map_err(|e| err(format!("LLVM back end failed:\n{e}")))?;
    mlir.text = text;
    Ok((out, mlir))
}

/// `foo.o` beside `libfoo.a`.
fn object_beside(archive: &Path) -> PathBuf {
    let stem = archive
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("out");
    let name = stem.strip_prefix("lib").unwrap_or(stem);
    archive.with_file_name(format!("{name}.o"))
}

/// Link the objects `objs` of `module` with the runtime and the
/// dependencies into the executable `out`: lld in process, or the C
/// compiler driver `ROK_CC`.
pub fn link_object(
    module: &CompiledModule,
    objs: &[PathBuf],
    opts: &BuildOptions,
    out: &Path,
) -> Result<(), RokDiagnostic> {
    let triple = module.mir.target.triple.as_deref();
    let t = target(triple);
    let apple = t.triple.contains("-apple-");
    // A rokc built without LLVM has no lld either: the system's `cc`.
    let cc = std::env::var_os("ROK_CC")
        .filter(|c| !c.is_empty())
        .or_else(|| (!rokc_llvm::AVAILABLE).then(|| "cc".into()));
    if let Some(cc) = cc {
        let mut link = Command::new(cc);
        link.args(objs).args(&module.archives).arg(rokr_arg(opts));
        for (name, stat) in &module.mir.link.native_libs {
            // ld64 has no `-Bstatic`: it takes the first `lib<name>` on
            // the search path.
            if *stat && !apple {
                link.args(["-Wl,-Bstatic", &format!("-l{name}"), "-Wl,-Bdynamic"]);
            } else {
                link.arg(format!("-l{name}"));
            }
        }
        link.arg(if apple {
            "-Wl,-dead_strip"
        } else {
            "-Wl,--gc-sections"
        });
        if opts.debug {
            link.arg("-g");
        }
        if let Some(t) = triple {
            link.arg(format!("--target={t}"));
        }
        // core's float methods call libm; glibc keeps it out of libc.
        link.arg("-lm").arg("-o").arg(out);
        run(&mut link, "the link")?;
    } else {
        let mut inputs: Vec<OsString> = objs.iter().map(|o| o.clone().into_os_string()).collect();
        inputs.extend(module.archives.iter().map(|a| a.clone().into_os_string()));
        inputs.push(rokr_arg(opts).into());
        for (name, stat) in &module.mir.link.native_libs {
            if *stat && !apple {
                inputs.extend([
                    "-Bstatic".into(),
                    format!("-l{name}").into(),
                    "-Bdynamic".into(),
                ]);
            } else {
                inputs.push(format!("-l{name}").into());
            }
        }
        inputs.push("-lm".into());
        rokc_diagnostic::time("link", || {
            rokc_llvm::link_executable(&t, &inputs, out, true)
        })
        .map_err(|e| err(format!("the link failed:\n{e}")))?;
    }
    // Mach-O keeps DWARF in the objects: gather it into a `.dSYM` while
    // they still exist.
    if opts.debug && apple {
        rokc_diagnostic::time("dsymutil", || rokc_llvm::dsymutil(&[out.as_os_str()]))
            .map_err(|e| err(format!("{}: {e}", out.display())))?;
    }
    Ok(())
}

/// `--rokr`: a library path when it has an extension, else `-l<name>`.
fn rokr_arg(opts: &BuildOptions) -> String {
    if Path::new(&opts.rokr).extension().is_some() {
        opts.rokr.clone()
    } else {
        format!("-l{}", opts.rokr)
    }
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

/// The REPL's session host: `host_object` (`repl_host.c`, compiled with
/// rokc) with the whole runtime linked in and exported, for the cells it
/// maps and links itself.
pub fn link_host(host_object: &Path, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
    let inputs: [OsString; 4] = [
        host_object.as_os_str().to_owned(),
        "-all_load".into(),
        rokr_arg(opts).into(),
        "-lm".into(),
    ];
    rokc_llvm::link_executable(&rokc_llvm::Target::host(), &inputs, out, false)
        .map(drop)
        .map_err(|e| err(format!("cannot link the REPL host:\n{e}")))
}

/// rokc's build cache: `<sysroot>/lib/rok-cache` of an installed
/// toolchain, else `rok-cache/` beside `rokc` (a build in the
/// repository).
#[must_use]
pub fn cache_dir() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    let exe = std::fs::canonicalize(&exe).unwrap_or(exe);
    let bin = exe.parent()?;
    let sysroot = bin.parent()?;
    Some(if sysroot.join("lib/rok").is_dir() {
        sysroot.join("lib/rok-cache")
    } else {
        bin.join("rok-cache")
    })
}

fn run(cmd: &mut Command, what: &str) -> Result<(), RokDiagnostic> {
    let out = rokc_diagnostic::time(what, || cmd.output())
        .map_err(|e| err(format!("cannot run {what}: {e}")))?;
    if !out.status.success() {
        return Err(err(format!(
            "{what} failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn mlir_plugins_are_found_by_path_or_name() {
        assert!(super::find_mlir_plugin("/no/such/libx.so").is_err());
        assert!(super::find_mlir_plugin("no_such_plugin_xyz").is_err());
    }
}

//! Native back half of the AOT pipeline (spec 902.11-902.14), in
//! process: the MLIR passes, the translation to LLVM IR, LLVM's
//! optimization and code generation, and the link (lld) through the
//! LLVM / MLIR / lld rokc links statically (`rokc_llvm`). `ROK_CC`, when
//! set, links instead.

use std::borrow::Cow;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

use rokc_diagnostic::{ErrorKind, RokDiagnostic, SourceMap};
use rokc_mir::TargetSpec;
use rokc_target::{Linker, ObjectFormat};

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
    /// A shipped C library (`Libc::shipped`): the C runtime objects and C library
    /// for the target (`<sysroot>/lib/rok/targets/<target>/`).
    pub libc: Option<PathBuf>,
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
    /// `-L <dir>`: native library search directories, before the C
    /// driver's `LIBRARY_PATH`.
    pub lib_dirs: Vec<PathBuf>,
    /// `-l [static=|dylib=]<name>`: native libraries linked as if named by
    /// `#[link]` (`true`: static).
    pub libs: Vec<(String, bool)>,
    /// `--native-runtime <file>`: shared libraries an executable loads at
    /// run time, copied beside it; the executable then searches its own
    /// directory (rpath `@loader_path` / `$ORIGIN`; Windows always does).
    pub runtime_files: Vec<PathBuf>,
    /// `-C subsystem=console|windows`: a Windows executable's subsystem.
    pub subsystem: crate::windows::Subsystem,
    /// `-C profile-generate` / `-C profile-use`: IR profile-guided
    /// optimization, by LLVM at every level.
    pub profile: Profile,
    /// The profile runtime an instrumented executable links
    /// (`<sysroot>/lib/rok/targets/<target>/`).
    pub profile_rt: Option<PathBuf>,
    /// An executable builds by codegen units, reusing from this
    /// directory the objects of the units that did not change (spec
    /// 9.2.16, `units`).
    pub incremental: Option<PathBuf>,
}

/// IR profile-guided optimization of the program and its source
/// dependencies.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum Profile {
    #[default]
    Off,
    /// Instrumented: the program writes its raw profile to this file
    /// name pattern (`LLVM_PROFILE_FILE` overrides it at run time).
    Generate(PathBuf),
    /// Optimized with this indexed profile (`rokc profdata merge`).
    Use(PathBuf),
    /// `-C cs-profile-generate`: optimized with this profile, then
    /// instrumented again after inlining (context-sensitive), writing to
    /// this pattern; merged with the first, it is a profile to use.
    CsGenerate(PathBuf, PathBuf),
}

impl Profile {
    /// The profile the build optimizes with.
    #[must_use]
    pub fn used(&self) -> Option<&Path> {
        match self {
            Self::Use(p) | Self::CsGenerate(p, _) => Some(p),
            _ => None,
        }
    }

    /// The build is instrumented (links the profile runtime).
    #[must_use]
    pub const fn generates(&self) -> bool {
        matches!(self, Self::Generate(_) | Self::CsGenerate(..))
    }
}

impl Default for BuildOptions {
    fn default() -> Self {
        Self {
            opt_level: "0".to_owned(),
            rokr: "rokr".to_owned(),
            libc: None,
            keep_temps: false,
            debug: false,
            repl: None,
            overflow_checks: None,
            mlir_dialect_plugins: Vec::new(),
            mlir_pass_plugins: Vec::new(),
            mlir_passes: Vec::new(),
            backend: std::env::var("ROK_BACKEND").ok().filter(|b| !b.is_empty()),
            lib_dirs: Vec::new(),
            libs: Vec::new(),
            runtime_files: Vec::new(),
            subsystem: crate::windows::Subsystem::Console,
            profile: Profile::Off,
            profile_rt: None,
            incremental: None,
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
            match private_dir(&path) {
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

/// Create `path` readable by this user alone (Windows: the user's temp
/// directory is private already).
fn private_dir(path: &Path) -> std::io::Result<()> {
    #[cfg(unix)]
    return std::os::unix::fs::DirBuilderExt::mode(&mut std::fs::DirBuilder::new(), 0o700)
        .create(path);
    #[cfg(not(unix))]
    std::fs::create_dir(path)
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
    RokDiagnostic::error(ErrorKind::Linkage, rokc_diagnostic::Span::DUMMY, msg)
}

/// Codegen a module to MLIR text for its target.
pub fn mlir_text(
    module: &CompiledModule,
    sources: &SourceMap,
    opts: &BuildOptions,
) -> Result<rokc_codegen_mlir::MlirOutput, RokDiagnostic> {
    codegen(
        module,
        sources,
        opts,
        Some(module.mir.target.data_layout.clone()),
    )
}

/// Codegen for its errors alone (`rokc check`).
pub fn check_codegen(
    module: &CompiledModule,
    sources: &SourceMap,
    opts: &BuildOptions,
) -> Result<(), RokDiagnostic> {
    codegen(module, sources, opts, None).map(drop)
}

fn codegen(
    module: &CompiledModule,
    sources: &SourceMap,
    opts: &BuildOptions,
    data_layout: Option<String>,
) -> Result<rokc_codegen_mlir::MlirOutput, RokDiagnostic> {
    rokc_diagnostic::time("mlir emit", || {
        rokc_codegen_mlir::codegen(&module.mir, &codegen_options(opts, data_layout), sources)
    })
}

/// The MLIR emitter's options of a build.
pub fn codegen_options(
    opts: &BuildOptions,
    data_layout: Option<String>,
) -> rokc_codegen_mlir::CodegenOptions {
    rokc_codegen_mlir::CodegenOptions {
        overflow_checks: opts.overflow_checks.unwrap_or(opts.opt_level == "0"),
        debug: opts.debug,
        optimized: opts.opt_level != "0",
        repl: opts.repl.clone(),
        data_layout,
    }
}

/// Produce one artifact's bytes.
pub fn emit(
    module: &CompiledModule,
    sources: &SourceMap,
    kind: EmitKind,
    opts: &BuildOptions,
) -> Result<Vec<u8>, RokDiagnostic> {
    if kind == EmitKind::Obj {
        if let Some(o) = crate::native::object(module, sources, opts)? {
            return Ok(o.object);
        }
    }
    match kind {
        EmitKind::Ast => Err(RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Internal,
            rokc_diagnostic::Span::DUMMY,
            "--emit=ast needs the parsed files (keep_ast)",
        )),
        EmitKind::Hir => Ok(rokc_hir::print_hir(&module.hir).into_bytes()),
        EmitKind::Mir => Ok(rokc_mir::print_mir(&module.mir).into_bytes()),
        EmitKind::Expanded => Err(err("`--emit=expanded` needs the parsed sources".to_owned())),
        EmitKind::Mlir => Ok(mlir_text(module, sources, opts)?.text.into_bytes()),
        EmitKind::LlvmIr => Ok(lower_to_llvm(module, sources, opts)?.0.into_bytes()),
        EmitKind::Asm => Ok(llvm(module, sources, opts, rokc_llvm::Emit::Asm, 1)?
            .0
            .remove(0)),
        EmitKind::Obj => Ok(llvm(module, sources, opts, rokc_llvm::Emit::Obj, 1)?
            .0
            .remove(0)),
    }
}

/// Full build: an executable at `out`; by codegen units with
/// `opts.incremental` (`units::applies`), and then how many it
/// compiled.
pub fn link_executable(
    module: &CompiledModule,
    sources: &SourceMap,
    opts: &BuildOptions,
    out: &Path,
) -> Result<Option<crate::units::UnitCounts>, RokDiagnostic> {
    let mut counts = None;
    let objects = if let Some(dir) = opts
        .incremental
        .as_deref()
        .filter(|_| crate::units::applies(module, opts))
    {
        let (objects, c, _) = crate::units::objects(module, sources, opts, dir)?;
        counts = Some(c);
        objects
    } else if let Some(o) = crate::native::object(module, sources, opts)? {
        vec![o.object]
    } else {
        llvm(module, sources, opts, rokc_llvm::Emit::Obj, 0)?.0
    };
    let tmp = TempDir::new(opts.keep_temps)?;
    let mut paths = Vec::new();
    for (i, o) in objects.iter().enumerate() {
        let p = tmp.path().join(format!("module{i}.o"));
        std::fs::write(&p, o).map_err(|e| err(format!("cannot write {}: {e}", p.display())))?;
        paths.push(p);
    }
    link_object(module, &paths, opts, out)?;
    Ok(counts)
}

/// Library build (spec 902.13): `libfoo.a`.
///
/// By codegen units with `opts.incremental` (`units::applies`; and then
/// how many it compiled), else as many members as LLVM compiles in
/// parallel (a prebuilt dependency, the standard library cache).
///
/// For a prebuilt-library build (`CompiledModule::interface`), its ROKHIR
/// `foo.rokhir` beside them (spec 904). The ROKHIR is a sibling file rather
/// than an archive member (903): no object-section reader is needed.
pub fn build_archive(
    module: &CompiledModule,
    sources: &SourceMap,
    opts: &BuildOptions,
    archive_out: &Path,
) -> Result<Option<crate::units::UnitCounts>, RokDiagnostic> {
    let mut counts = None;
    let (objects, gc_types) = if let Some(dir) = opts
        .incremental
        .as_deref()
        .filter(|_| crate::units::applies(module, opts))
    {
        let (objects, c, gc_types) = crate::units::objects(module, sources, opts, dir)?;
        counts = Some(c);
        (objects, gc_types)
    } else if let Some(o) = crate::native::object(module, sources, opts)? {
        (vec![o.object], o.gc_types)
    } else {
        let (objs, mlir) = llvm(module, sources, opts, rokc_llvm::Emit::Obj, 0)?;
        (objs, mlir.gc_types)
    };
    let tmp = TempDir::new(opts.keep_temps)?;
    let mut paths = Vec::new();
    for (i, o) in objects.iter().enumerate() {
        let p = tmp.path().join(format!("part{i}.o"));
        std::fs::write(&p, o).map_err(|e| err(format!("cannot write {}: {e}", p.display())))?;
        paths.push(p);
    }
    // A fresh archive, not members appended to an old one.
    let _ = std::fs::remove_file(archive_out);
    let t = &module.mir.target.spec;
    let members: Vec<&Path> = paths.iter().map(PathBuf::as_path).collect();
    rokc_llvm::write_archive(t, archive_out, &members)
        .map_err(|e| err(format!("cannot write {}: {e}", archive_out.display())))?;
    if let Some(r) = &module.interface {
        let mut r = r.clone();
        r.type_count = gc_types;
        let path = archive_out.with_file_name(format!("{}.rokhir", r.name));
        std::fs::write(&path, r.encode())
            .map_err(|e| err(format!("cannot write {}: {e}", path.display())))?;
    }
    Ok(counts)
}

/// A REPL cell (`opts.repl`) as an object for the session host, built by
/// LLVM, and what codegen says about it.
pub fn cell_object(
    module: &CompiledModule,
    sources: &SourceMap,
    opts: &BuildOptions,
) -> Result<(Vec<u8>, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let (mut objs, mlir) = llvm(module, sources, opts, rokc_llvm::Emit::Obj, 1)?;
    Ok((objs.remove(0), mlir))
}

/// The module's LLVM IR, as translated from MLIR (`--emit=llvm-ir`).
pub fn lower_to_llvm(
    module: &CompiledModule,
    sources: &SourceMap,
    opts: &BuildOptions,
) -> Result<(String, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let (mut ir, mlir) = llvm(module, sources, opts, rokc_llvm::Emit::LlvmIr, 1)?;
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
/// parallel (in-process `ThinLTO` above -O0, so inlining still sees
/// every function).
fn llvm(
    module: &CompiledModule,
    sources: &SourceMap,
    opts: &BuildOptions,
    emit: rokc_llvm::Emit,
    parts: usize,
) -> Result<(Vec<Vec<u8>>, rokc_codegen_mlir::MlirOutput), RokDiagnostic> {
    let mut mlir = mlir_text(module, sources, opts)?;
    let t = &module.mir.target.spec;
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
        target: t,
        opt,
        emit,
        // JIT'd Mach-O cells reach thread-locals through TLV
        // descriptors; the ELF loader resolves initial exec.
        tls_initial_exec: opts.repl.is_none() || t.object_format != ObjectFormat::MachO,
        mlir_pipeline: &pipeline,
        dialect_plugins: &dialects,
        pass_plugins: &passes,
        profile: match &opts.profile {
            Profile::Off => rokc_llvm::Profile::None,
            Profile::Generate(p) => rokc_llvm::Profile::Generate(p),
            Profile::Use(p) => rokc_llvm::Profile::Use(p),
            Profile::CsGenerate(u, g) => rokc_llvm::Profile::CsGenerate(u, g),
        },
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
    let (out, warnings) =
        rokc_diagnostic::time("llvm", || rokc_llvm::compile_mlir_split(&text, &c, parts))
            .map_err(|e| err(format!("LLVM back end failed:\n{e}")))?;
    for w in warnings.lines() {
        SourceMap::new().report(&RokDiagnostic::warning(
            ErrorKind::Linkage,
            rokc_diagnostic::Span::DUMMY,
            w,
        ));
    }
    mlir.text = text;
    Ok((out, mlir))
}

/// Link the objects `objs` of `module` with the runtime and the
/// dependencies into the executable `out`: lld in process, or the C
/// compiler driver `ROK_CC`.
///
/// A Windows executable links its C runtime and system libraries
/// through import libraries rokc makes (`windows::link_args`).
pub fn link_object(
    module: &CompiledModule,
    objs: &[PathBuf],
    opts: &BuildOptions,
    out: &Path,
) -> Result<(), RokDiagnostic> {
    let t = &*module.mir.target.spec;
    let apple = t.object_format == ObjectFormat::MachO;
    let windows = t.object_format == ObjectFormat::Coff;
    let search: Vec<OsString> = opts
        .lib_dirs
        .iter()
        .map(|d| {
            let mut l = OsString::from("-L");
            l.push(d);
            l
        })
        .collect();
    let mut libs = module.mir.link.native_libs.clone();
    for l in &opts.libs {
        if !libs.iter().any(|(n, _)| *n == l.0) {
            libs.push(l.clone());
        }
    }
    // The loader looks beside the executable for the shared libraries
    // copied there.
    let origin = if opts.runtime_files.is_empty() || windows {
        None
    } else if apple {
        Some("@loader_path")
    } else {
        Some("$ORIGIN")
    };
    let wit = module.mir.link.wit.as_ref();
    if let Some(cc) = c_compiler() {
        let tmp = TempDir::new(opts.keep_temps)?;
        let mut link = Command::new(cc);
        link.args(objs)
            .args(&module.archives)
            .arg(rokr_arg(opts, t));
        link.args(&search);
        link.args(cc_wit_args(wit, tmp.path())?);
        if let Some((rt, sym)) = profile_runtime(t, opts) {
            link.arg(rt).arg(format!("-Wl,-u,{sym}"));
        }
        for (name, stat) in &libs {
            if *stat && apple {
                link.arg(static_archive(name, opts)?);
            } else if *stat {
                link.args(["-Wl,-Bstatic", &format!("-l{name}"), "-Wl,-Bdynamic"]);
            } else {
                link.arg(format!("-l{name}"));
            }
        }
        if apple {
            link.arg("-Wl,-dead_strip");
        } else if !windows {
            link.arg("-Wl,--gc-sections");
        }
        if let Some(o) = origin {
            link.arg(format!("-Wl,-rpath,{o}"));
        }
        if opts.debug {
            link.arg("-g");
        }
        // Apple's clang links for the machine it runs as (not rokc's,
        // under Rosetta) unless told.
        if t != TargetSpec::host() || apple {
            link.arg(format!("--target={}", cc_target(t)));
        }
        // core's float methods call libm; glibc keeps it out of libc.
        if !windows {
            link.arg("-lm");
        }
        link.arg("-o").arg(out);
        run(&mut link, "the link")?;
    } else if windows {
        let tmp = TempDir::new(opts.keep_temps)?;
        let mut inputs: Vec<OsString> = objs.iter().map(|o| o.clone().into_os_string()).collect();
        inputs.extend(module.archives.iter().map(|a| a.clone().into_os_string()));
        inputs.push(rokr_arg(opts, t).into());
        if let Some((rt, sym)) = profile_runtime(t, opts) {
            inputs.extend([rt.into(), format!("/include:{sym}").into()]);
        }
        inputs.extend(search);
        inputs.extend(
            crate::windows::link_args(t, &libs, opts.subsystem, opts.debug, tmp.path())
                .map_err(|e| err(format!("the link failed:\n{e}")))?,
        );
        rokc_diagnostic::time("link", || {
            rokc_llvm::link_executable(t, &inputs, out, true, None)
        })
        .map_err(|e| err(format!("the link failed:\n{e}")))?;
    } else {
        let tmp = TempDir::new(opts.keep_temps)?;
        let mut inputs: Vec<OsString> = objs.iter().map(|o| o.clone().into_os_string()).collect();
        if t.object_format == ObjectFormat::Wasm && t.threads {
            inputs.push(wasm_tls_object(t, tmp.path())?.into_os_string());
        }
        if let Some(w) = wit {
            inputs.extend(wit_link_args(w, tmp.path())?);
        }
        inputs.extend(module.archives.iter().map(|a| a.clone().into_os_string()));
        inputs.push(rokr_arg(opts, t).into());
        if let Some((rt, sym)) = profile_runtime(t, opts) {
            // wasm-component-ld forwards only the long form.
            let u = if t.object_format == ObjectFormat::Wasm {
                "--undefined"
            } else {
                "-u"
            };
            inputs.extend([rt.into(), u.into(), sym.into()]);
        }
        inputs.extend(search);
        inputs.extend(native_lib_args(&libs, apple, opts)?);
        if let Some(o) = origin {
            inputs.extend(["-rpath".into(), o.into()]);
        }
        let t = &*entry_model(t, wit);
        rokc_diagnostic::time("link", || {
            rokc_llvm::link_executable(t, &inputs, out, true, opts.libc.as_deref())
        })
        .map_err(|e| err(format!("the link failed:\n{e}")))?;
    }
    let dir = out.parent().unwrap_or_else(|| Path::new("."));
    for f in &opts.runtime_files {
        let to = dir.join(f.file_name().unwrap_or_default());
        // A new file: one a running program maps stays intact.
        let _ = std::fs::remove_file(&to);
        std::fs::copy(f, &to).map_err(|e| {
            err(format!(
                "cannot copy {} to {}: {e}",
                f.display(),
                to.display()
            ))
        })?;
    }
    // Mach-O keeps DWARF in the objects: gather it into a `.dSYM` while
    // they still exist.
    if opts.debug && apple {
        rokc_diagnostic::time("dsymutil", || rokc_llvm::dsymutil(&[out.as_os_str()]))
            .map_err(|e| err(format!("{}: {e}", out.display())))?;
    }
    Ok(())
}

/// `wasm-component-ld`'s arguments for the WIT of `ffi::wit` (stdlib
/// 1.8): the component's world in a directory under `tmp`, its sources
/// under `deps/` (as `wit-parser` reads a package directory), and the
/// core exports the world's functions are.
fn wit_link_args(w: &rokc_mir::WitLink, tmp: &Path) -> Result<Vec<OsString>, RokDiagnostic> {
    let io = |p: &Path, e: std::io::Error| err(format!("cannot write {}: {e}", p.display()));
    let dir = tmp.join("wit");
    let deps = dir.join("deps");
    std::fs::create_dir_all(&deps).map_err(|e| io(&deps, e))?;
    let world = dir.join("component.wit");
    std::fs::write(&world, &w.world).map_err(|e| io(&world, e))?;
    for (i, src) in w.sources.iter().enumerate() {
        let stem = src.file_stem().and_then(|s| s.to_str()).unwrap_or("wit");
        if src.is_dir() {
            let to = deps.join(format!("{i}-{stem}"));
            std::fs::create_dir_all(&to).map_err(|e| io(&to, e))?;
            let files = std::fs::read_dir(src).map_err(|e| io(src, e))?;
            for f in files.filter_map(Result::ok).map(|e| e.path()) {
                if f.is_file() && f.extension().is_some_and(|x| x == "wit") {
                    let dst = to.join(f.file_name().unwrap_or_default());
                    std::fs::copy(&f, &dst).map_err(|e| io(&dst, e))?;
                }
            }
        } else {
            let dst = deps.join(format!("{i}-{stem}.wit"));
            std::fs::copy(src, &dst).map_err(|e| io(&dst, e))?;
        }
    }
    let mut a: Vec<OsString> = vec!["--component-type".into(), dir.into_os_string()];
    a.extend(w.exports.iter().map(|s| format!("--export={s}").into()));
    Ok(a)
}

/// The target `t` links a program for: a component without `main` is a
/// reactor (wasi-libc's `crt1-reactor.o`, no entry; the host calls
/// `_initialize`, then the exports).
fn entry_model<'t>(t: &'t TargetSpec, wit: Option<&rokc_mir::WitLink>) -> Cow<'t, TargetSpec> {
    if wit.is_some_and(|w| w.reactor) {
        Cow::Owned(TargetSpec {
            crt_objects: vec!["crt1-reactor.o".to_owned()],
            pre_link_args: [&t.pre_link_args[..], &["--no-entry".to_owned()]].concat(),
            ..t.clone()
        })
    } else {
        Cow::Borrowed(t)
    }
}

/// The C compiler driver's name of target `t`: clang calls a WASI
/// preview 2 component by its Rust name (`wasm32-wasip2`).
fn cc_target(t: &TargetSpec) -> String {
    if t.linker == Linker::WasmComponentLd {
        t.rust_target.clone()
    } else {
        t.llvm_triple()
    }
}

/// `wit_link_args` for the C compiler driver (`ROK_CC`), which hands
/// them to `wasm-component-ld`; a reactor's exec model.
fn cc_wit_args(w: Option<&rokc_mir::WitLink>, tmp: &Path) -> Result<Vec<OsString>, RokDiagnostic> {
    let Some(w) = w else {
        return Ok(Vec::new());
    };
    let args = wit_link_args(w, tmp)?;
    let mut out = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut wl = OsString::from("-Wl,");
        wl.push(a);
        if a == "--component-type" {
            wl.push(",");
            wl.push(it.next().map_or_else(OsString::new, Clone::clone));
        }
        out.push(wl);
    }
    if w.reactor {
        out.push("-mexec-model=reactor".into());
    }
    Ok(out)
}

/// An instrumented executable's profile runtime (compiler-rt's) and the
/// symbol that pulls in its registration, which writes the profile at
/// exit.
fn profile_runtime(t: &TargetSpec, opts: &BuildOptions) -> Option<(PathBuf, String)> {
    if !opts.profile.generates() {
        return None;
    }
    let rt = opts.profile_rt.clone()?;
    Some((rt, format!("{}__llvm_profile_runtime", t.c_symbol_prefix)))
}

/// lld's arguments for the `#[link]` libraries `libs` (name, static).
fn native_lib_args(
    libs: &[(String, bool)],
    apple: bool,
    opts: &BuildOptions,
) -> Result<Vec<OsString>, RokDiagnostic> {
    let mut a: Vec<OsString> = Vec::new();
    for (name, stat) in libs {
        if *stat && apple {
            a.push(static_archive(name, opts)?.into_os_string());
        } else if *stat {
            a.extend([
                "-Bstatic".into(),
                format!("-l{name}").into(),
                "-Bdynamic".into(),
            ]);
        } else {
            a.push(format!("-l{name}").into());
        }
    }
    Ok(a)
}

/// The runtime's TLS block `rok_tls` (803 §8.3.1) for
/// `wasm32-wasi-threads`, in wasm TLS (`__tls_base` + offset), with the
/// accessor the runtime reaches its own thread's copy through
/// (`rokr_common::tls`, which stable Rust cannot define there), in `dir`.
fn wasm_tls_object(t: &TargetSpec, dir: &Path) -> Result<PathBuf, RokDiagnostic> {
    let size = rokc_mir::tls_abi::SIZE.offset(t.pointer_width / 8);
    let align = rokc_mir::tls_abi::ALIGN;
    let ir = format!(
        "declare ptr @llvm.threadlocal.address.p0(ptr)\n\
         @rok_tls = thread_local global [{size} x i8] zeroinitializer, align {align}\n\
         define hidden ptr @rokr_tls_addr() nounwind {{\n\
         \x20 %p = call ptr @llvm.threadlocal.address.p0(ptr @rok_tls)\n\
         \x20 ret ptr %p\n}}\n"
    );
    let obj = rokc_llvm::compile_llvm_ir(
        &ir,
        &rokc_llvm::Compile {
            target: t,
            opt: rokc_llvm::OptLevel::O2,
            emit: rokc_llvm::Emit::Obj,
            tls_initial_exec: false,
            mlir_pipeline: "",
            dialect_plugins: &[],
            pass_plugins: &[],
            profile: rokc_llvm::Profile::None,
        },
    )
    .map_err(|e| err(format!("the TLS object: {e}")))?;
    let path = dir.join("rok_tls.o");
    std::fs::write(&path, obj).map_err(|e| err(format!("cannot write {}: {e}", path.display())))?;
    Ok(path)
}

/// `#[link(name, kind = "static")]` for ld64, which has no `-Bstatic`
/// (it takes a `.dylib` before a `.a` in each directory): the first
/// `lib<name>.a` in the `-L` directories, then `LIBRARY_PATH`.
fn static_archive(name: &str, opts: &BuildOptions) -> Result<PathBuf, RokDiagnostic> {
    let env = std::env::var_os("LIBRARY_PATH").unwrap_or_default();
    let dirs: Vec<PathBuf> = opts
        .lib_dirs
        .iter()
        .cloned()
        .chain(std::env::split_paths(&env).filter(|d| !d.as_os_str().is_empty()))
        .collect();
    let file = format!("lib{name}.a");
    dirs.iter()
        .map(|d| d.join(&file))
        .find(|p| p.is_file())
        .ok_or_else(|| {
            err(format!(
                "`#[link(name = \"{name}\", kind = \"static\")]`: no {file} in the -L directories \
             or LIBRARY_PATH"
            ))
        })
}

/// `--rokr`: a library path when it has an extension, else `-l<name>`
/// (COFF: the library's file name).
fn rokr_arg(opts: &BuildOptions, t: &TargetSpec) -> String {
    if Path::new(&opts.rokr).extension().is_some() {
        opts.rokr.clone()
    } else if t.object_format == ObjectFormat::Coff {
        t.staticlib(&opts.rokr)
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
    let t = TargetSpec::host();
    if t.object_format == ObjectFormat::Coff {
        return link_windows_host(t, host_object, opts, out);
    }
    let cc = c_compiler();
    let flag = |f: &str| -> OsString {
        if cc.is_some() {
            format!("-Wl,{f}").into()
        } else {
            f.into()
        }
    };
    let obj = host_object.as_os_str().to_owned();
    let rokr = OsString::from(rokr_arg(opts, t));
    // ELF: the runtime in the dynamic symbol table, for `dlsym`.
    let inputs = if t.object_format == ObjectFormat::MachO {
        let mut v = vec![obj, flag("-all_load"), rokr];
        if cc.is_some() {
            v.push(format!("--target={}", t.llvm_triple()).into());
        }
        v
    } else {
        vec![
            flag("--export-dynamic"),
            obj,
            flag("--whole-archive"),
            rokr,
            flag("--no-whole-archive"),
        ]
    };
    if let Some(cc) = cc {
        let mut link = Command::new(cc);
        link.args(&inputs).arg("-lm").arg("-o").arg(out);
        return run(&mut link, "the REPL host link");
    }
    rokc_llvm::link_executable(t, &inputs, out, false, opts.libc.as_deref())
        .map(drop)
        .map_err(|e| err(format!("cannot link the REPL host:\n{e}")))
}

/// The Windows session host: every runtime member, every symbol
/// exported (the host finds them with `GetProcAddress`), linked like a
/// program (`windows::link_args`).
fn link_windows_host(
    t: &TargetSpec,
    host_object: &Path,
    opts: &BuildOptions,
    out: &Path,
) -> Result<(), RokDiagnostic> {
    let tmp = TempDir::new(opts.keep_temps)?;
    let mut inputs: Vec<OsString> = vec![
        host_object.into(),
        format!("/wholearchive:{}", rokr_arg(opts, t)).into(),
        // lld-link honors it in its MinGW mode only.
        "-lldmingw".into(),
        "/export-all-symbols".into(),
    ];
    let fail = |e: String| err(format!("cannot link the REPL host:\n{e}"));
    inputs.extend(
        crate::windows::link_args(t, &[], crate::Subsystem::Console, false, tmp.path())
            .map_err(fail)?,
    );
    rokc_llvm::link_executable(t, &inputs, out, false, None)
        .map(drop)
        .map_err(fail)
}

/// The C compiler driver that links instead of lld: `ROK_CC`, else the
/// system's `cc` for a rokc built without LLVM (no lld either).
fn c_compiler() -> Option<OsString> {
    std::env::var_os("ROK_CC")
        .filter(|c| !c.is_empty())
        .or_else(|| (!rokc_llvm::AVAILABLE).then(|| "cc".into()))
}

/// rokc's build cache: `<sysroot>/lib/rok-cache` of an installed
/// toolchain, else `rok-cache/` beside `rokc` (a build in the
/// repository).
#[must_use]
pub fn cache_dir() -> Option<PathBuf> {
    let exe = rokc_core::current_exe()?;
    let bin = exe.parent()?;
    let sysroot = bin.parent()?;
    Some(if sysroot.join("lib/rok/core/src").is_dir() {
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

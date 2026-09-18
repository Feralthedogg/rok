//! Compiler driver. Threads source through lexer, parser,
//! HIR lowering (name resolution + type checks), and MIR lowering.

mod attrs;
mod cfg;
mod coro;
mod entry;
mod harness;
mod incr;
pub use incr::Reuse;
pub mod native;
pub mod rokhir;
mod toolchain;
pub mod units;
mod windows;
mod wit;

use std::path::{Path, PathBuf};

use rokc_diagnostic::{RokDiagnostic, SourceMap};
use rokc_hir::HirModule;
use rokc_lexer::Lexer;
use rokc_mir::MirModule;
use rokc_parser::{
    ExtOps, KeywordDef, KeywordTable, LitRule, LiteralDef, LiteralTable, MetaDef, MetaTable,
    PatKind, PrecTable, apply_keywords, check_keyword, collect_keywords, collect_literals,
    collect_meta_blocks, collect_prec_table, parse_pattern, parse_program, parse_program_meta,
};

pub use cfg::{CfgEnv, feature_of};
pub use rokc_codegen_mlir::{Demangled, demangle};
pub use rokc_codegen_mlir::{MlirOutput, ReplCell, ReplFn};
pub use rokc_hir::instance;
pub use rokc_llvm::{profdata_merge, profdata_show};
pub use rokc_mir::{Target, TargetSpec};
pub use windows::Subsystem;
/// Whether the REPL's session host runs here: it loads Mach-O / ELF /
/// COFF objects of arm64 / `x86_64`.
#[must_use]
pub fn repl_host() -> bool {
    rokc_mir::TargetSpec::host().repl
}

pub use rokc_llvm::{AS_WASM_LD, wasm_ld_main};

/// The LLVM rokc links (`None`: built without one; only the native
/// backend's `-O0` builds work).
pub const LLVM_VERSION: Option<&str> = if rokc_llvm::AVAILABLE {
    Some(rokc_llvm::LLVM_VERSION)
} else {
    None
};

pub use toolchain::{
    BuildOptions, EmitKind, Profile, TempDir, build_archive, cache_dir, cell_object, check_codegen,
    emit, find_mlir_plugin, link_executable, link_host, link_object, lower_to_llvm, mlir_text,
};

// Independent switches, one per session setter.
#[allow(clippy::struct_excessive_bools)]
#[derive(Clone, Debug, Default)]
pub struct CompilerConfig {
    /// Files containing operator declarations to pre-load before parsing
    /// the user input. Populates the `PrecTable`.
    pub bootstrap_files: Vec<PathBuf>,
    /// `--cfg` flags. Each entry is either a bare flag (`"test"`) or a
    /// `key=value` pair (`"target_os=macos"`). Consulted by `#[cfg(...)]`
    /// during the pre-HIR filter pass.
    pub cfg_flags: Vec<String>,
    /// Test build (`rokc test`): `#[test]` functions are kept and a
    /// generated `main` runs the one named by `argv[1]`.
    pub test: bool,
    /// Bench build (`rokc bench`): a test build whose generated `main`
    /// times the `#[bench]` function named by `argv[1]`.
    pub bench: bool,
    /// Keep every parsed file's AST in `CompiledProject::sources`
    /// (`rokc lint` / `rokc doc`).
    pub keep_ast: bool,
    /// The input is a lone file outside any package (spec 4.16.8): it is
    /// the anonymous package's `main.rok` and cannot have `mod foo;`.
    pub anonymous: bool,
    /// Source files read from these texts instead of the disk (an
    /// editor's unsaved buffers), by absolute path.
    pub buffers: Vec<(PathBuf, String)>,
    /// Dependency packages (`--extern name=path`, spec 902.3): each
    /// `lib.rok` is compiled with the user package and mounted at the
    /// top-level path `name`; a `<name>.rokhir` (spec 904) is a prebuilt
    /// one, linked from the `lib<name>.a` beside it.
    pub externs: Vec<(String, PathBuf)>,
    /// Build the library package as prebuilt dependency `name`: it is
    /// mounted as `name` (as its users will see it), every body is
    /// compiled, and `CompiledModule::interface` holds its ROKHIR.
    pub lib_name: Option<String>,
    /// Keep the library's parse for the next build with the same
    /// library and the same user declarations that change its lexing
    /// (`#[infix]`, meta blocks, keywords): a long-lived session (REPL).
    pub cache_library: bool,
    /// The target (`--target`): `#[cfg]`, layout and code follow it.
    pub target: rokc_mir::Target,
    /// Lower every library body, not only the reachable ones.
    pub check_library: bool,
    /// Lower the small prebuilt standard library functions reached, for
    /// the optimizer to inline (`HirInput::inline_prebuilt`).
    pub inline_prebuilt: bool,
    /// Build the bootstrap tiers as one prebuilt library, `rok`: its
    /// ROKHIR covers every tier, its archive their concrete code.
    pub std_lib: bool,
    /// The bootstrap tiers prebuilt (`rok.rokhir`, its `librok.a` beside
    /// it): their concrete code is linked, not compiled. Ignored when
    /// stale or not of these tiers.
    pub std_prebuilt: Option<PathBuf>,
    /// The package's incremental directory (spec 9.2.16): parses and
    /// lowered bodies of the last build are kept there for the next.
    pub incremental: Option<PathBuf>,
}

/// The build's cfg (spec 6.3): the target's keys, `--cfg` and `test`.
#[must_use]
pub fn cfg_env(config: &CompilerConfig) -> CfgEnv {
    package_cfg(config, None)
}

/// The cfg a package of the build is parsed with: the build's, with its
/// `feature` keys replaced by `features` when given (features are per
/// package).
fn package_cfg(config: &CompilerConfig, features: Option<&[String]>) -> CfgEnv {
    let mut env = CfgEnv::new();
    cfg::add_target(&mut env, &config.target);
    for f in &config.cfg_flags {
        if features.is_none() || cfg::feature_of(f).is_none() {
            env.add(f);
        }
    }
    for f in features.unwrap_or_default() {
        env.add_pair("feature", f);
    }
    if config.test || config.bench {
        env.add("test");
    }
    env
}

/// The prebuilt standard library's package name.
pub const STD_PKG: &str = "rok";

thread_local! {
    /// Files served instead of the disk: the interface sources of the
    /// prebuilt dependencies (`rokhir::Rokhir::files`) at their old paths.
    static OVERLAY: std::cell::RefCell<std::collections::HashMap<PathBuf, String>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
    /// The source files this compile read from disk.
    static READ: std::cell::RefCell<Vec<PathBuf>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn read_source(path: &Path) -> std::io::Result<String> {
    if let Some(text) = OVERLAY.with(|o| o.borrow().get(path).cloned()) {
        return Ok(text);
    }
    READ.with(|r| r.borrow_mut().push(path.to_path_buf()));
    std::fs::read_to_string(path)
}

fn source_exists(path: &Path) -> bool {
    OVERLAY.with(|o| o.borrow().contains_key(path)) || path.exists()
}

fn source_dir_exists(dir: &Path) -> bool {
    OVERLAY.with(|o| o.borrow().keys().any(|p| p.starts_with(dir) && p != dir)) || dir.is_dir()
}

/// A prebuilt dependency of this build (`--extern name=x.rokhir`).
struct Prebuilt {
    rokhir: rokhir::Rokhir,
    archive: PathBuf,
}

/// Load the `.rokhir` externs into the overlay; `config` with each one's
/// root replaced by its (overlaid) `lib.rok`.
fn load_prebuilt(
    config: &CompilerConfig,
    diags: &mut Vec<RokDiagnostic>,
) -> (CompilerConfig, Vec<Prebuilt>) {
    let mut config = config.clone();
    let mut out: Vec<Prebuilt> = Vec::new();
    OVERLAY.with(|o| *o.borrow_mut() = config.buffers.iter().cloned().collect());
    READ.with(|r| r.borrow_mut().clear());
    if let Some(r) = config
        .std_prebuilt
        .as_deref()
        .and_then(|p| load_std(p, &config))
    {
        out.push(r);
    }
    for (name, root) in &mut config.externs {
        if root.extension().is_none_or(|e| e != "rokhir") {
            continue;
        }
        let r = match rokhir::Rokhir::load(root) {
            Ok(r) if r.name == *name => r,
            Ok(r) => {
                diags.push(RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Module,
                    rokc_diagnostic::Span::DUMMY,
                    format!(
                        "`--extern {name}={}`: it was built as `{}`, and the name is in its \
                         symbols — rebuild it as `{name}`",
                        root.display(),
                        r.name
                    ),
                ));
                continue;
            }
            Err(e) => {
                diags.push(RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Module,
                    rokc_diagnostic::Span::DUMMY,
                    e,
                ));
                continue;
            }
        };
        if let Some(p) = out
            .iter()
            .find(|p| r.type_offset < p.rokhir.type_end() && p.rokhir.type_offset < r.type_end())
        {
            diags.push(RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Module,
                rokc_diagnostic::Span::DUMMY,
                format!(
                    "prebuilt `{}` and `{}` use the same GC type ids — build each dependency \
                     with the ones before it as `--extern` (`rok build` does)",
                    p.rokhir.name, r.name
                ),
            ));
        }
        OVERLAY.with(|o| {
            let mut o = o.borrow_mut();
            for (rel, text) in &r.files {
                o.insert(r.src_dir.join(rel), text.clone());
            }
        });
        let archive = rokhir::companions(root).1;
        *root = r.src_dir.join("lib.rok");
        out.push(Prebuilt { rokhir: r, archive });
    }
    (config, out)
}

/// The prebuilt standard library at `path` when it holds every
/// bootstrap root of `config` (else `None`: they compile from source),
/// its files overlaid.
fn load_std(path: &Path, config: &CompilerConfig) -> Option<Prebuilt> {
    let r = rokhir::Rokhir::load(path)
        .ok()
        .filter(|r| r.name == STD_PKG)?;
    let complete = bootstrap_tiers(&config.bootstrap_files).iter().all(|b| {
        b.strip_prefix(&r.src_dir).is_ok_and(|rel| {
            let rel = rel.to_string_lossy().replace('\\', "/");
            r.files.iter().any(|(f, _)| *f == rel)
        })
    });
    if !complete {
        return None;
    }
    OVERLAY.with(|o| {
        let mut o = o.borrow_mut();
        for (rel, text) in &r.files {
            o.insert(r.src_dir.join(rel), text.clone());
        }
    });
    let archive = rokhir::companions(path).1;
    Some(Prebuilt { rokhir: r, archive })
}

/// A library root mounted beside the user package: its module path
/// prefix and root file.
type LibRoot = (Vec<String>, PathBuf);

/// The bootstrap roots `files` names, with `bare/lib.rok` beside a
/// `core/lib.rok` added when missing: core is built on bare (stdlib 0.1).
#[must_use]
pub fn bootstrap_tiers(files: &[PathBuf]) -> Vec<PathBuf> {
    let tier = |f: &PathBuf| f.parent().and_then(Path::file_name).map(ToOwned::to_owned);
    let mut out = files.to_vec();
    if !files.iter().any(|f| tier(f).is_some_and(|t| t == "bare")) {
        out.extend(
            files
                .iter()
                .filter(|f| tier(f).is_some_and(|t| t == "core"))
                .filter_map(|c| Some(c.parent()?.parent()?.join("bare/lib.rok")))
                .filter(|b| b.is_file())
                .take(1),
        );
    }
    out
}

/// Each bootstrap file as `rok::<tier>` (`library/core/lib.rok` →
/// `rok::core`), then each `--extern` dependency under its own name.
fn lib_roots(config: &CompilerConfig) -> Vec<LibRoot> {
    let mut out: Vec<LibRoot> = bootstrap_tiers(&config.bootstrap_files)
        .iter()
        .map(|root| {
            let tier = root
                .parent()
                .and_then(|d| d.file_name())
                .and_then(|n| n.to_str())
                .unwrap_or("core")
                .to_owned();
            (vec!["rok".to_owned(), tier], root.clone())
        })
        .collect();
    out.extend(
        config
            .externs
            .iter()
            .map(|(name, root)| (vec![name.clone()], root.clone())),
    );
    out
}

/// One parsed source file, as tools see it: after `#[cfg]` filtering,
/// before the driver flattens modules (so `use` / `mod` items, nested
/// item names and inner attributes are as written).
#[derive(Clone, Debug)]
pub struct SourceFile {
    pub path: PathBuf,
    /// Its `Span::file` id.
    pub file_id: u32,
    /// `""` for the user package, else the library root's mount path
    /// (`rok::core`, a dependency's name).
    pub package: String,
    /// Module path (with the package's mount prefix).
    pub module: Vec<String>,
    /// Inner (`#![..]`) attributes.
    pub attrs: Vec<rokc_ast::Attribute>,
    pub items: Vec<rokc_ast::Item>,
    /// Top-level statements (the entry file's implicit `main`).
    pub stmts: Vec<rokc_ast::Stmt>,
    /// Its meta expansions as source text (`--emit=expanded`).
    pub expanded: Vec<String>,
}

/// A user module named like a dependency would merge with it: dependency
/// names are top-level (902.3). Modules are seen through their items and
/// `use`s (an empty one can't clash).
fn check_dependency_names(
    items: &[ModItem],
    uses: &[(String, rokc_core::Visibility, rokc_ast::UseTree)],
    externs: &[(String, PathBuf)],
    diags: &mut Vec<RokDiagnostic>,
) {
    use rokc_ast::Item;
    let item_modules = items.iter().filter_map(|(module, item)| match item {
        Item::Fn(_)
        | Item::Struct(_)
        | Item::Enum(_)
        | Item::Union(_)
        | Item::Trait(_)
        | Item::Const(_)
        | Item::Static(_)
        | Item::TypeAlias(_)
            if !module.is_empty() =>
        {
            Some(module.as_str())
        }
        _ => None,
    });
    let modules: Vec<&str> = item_modules
        .chain(uses.iter().map(|(m, _, _)| m.as_str()))
        .collect();
    for (dep, _) in externs {
        let under = format!("{dep}::");
        if modules.iter().any(|m| m == dep || m.starts_with(&under)) {
            diags.push(RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Module,
                rokc_diagnostic::Span::DUMMY,
                format!(
                    "module `{dep}` has the name of the dependency `{dep}` — dependency names \
                     are top-level paths (spec 902.3); rename the module"
                ),
            ));
        }
    }
}

#[derive(Clone, Debug)]
pub struct CompiledModule {
    pub name: String,
    pub path: PathBuf,
    pub hir: HirModule,
    pub mir: MirModule,
    /// Prebuilt dependencies' archives, in link order.
    pub archives: Vec<PathBuf>,
    /// A `CompilerConfig::lib_name` build: its ROKHIR, but the GC type
    /// count (known after codegen).
    pub interface: Option<rokhir::Rokhir>,
}

#[derive(Clone, Debug, Default)]
pub struct CompiledProject {
    pub modules: Vec<CompiledModule>,
    pub warnings: Vec<RokDiagnostic>,
    /// `#[test]` functions of a test build (`#[bench]` functions of a
    /// bench build), `::`-qualified.
    pub tests: Vec<String>,
    /// Parsed files, when `CompilerConfig::keep_ast`.
    pub sources: Vec<SourceFile>,
    /// The source files read from disk (`#[path]` ones outside the
    /// package too).
    pub files: Vec<PathBuf>,
    /// What was taken from the incremental directory.
    pub reuse: Option<Reuse>,
}

/// Compile the package rooted at `path`; `files` gets every source file
/// read, by the ids the diagnostics' spans carry.
pub fn compile_file(
    path: &Path,
    config: &CompilerConfig,
    files: &mut SourceMap,
) -> Result<CompiledProject, Vec<RokDiagnostic>> {
    let source = std::fs::read_to_string(path).map_err(|e| {
        vec![RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Module,
            rokc_diagnostic::Span::DUMMY,
            format!("cannot read {}: {e}", path.display()),
        )]
    })?;
    compile_source(&source, path, config, files)
}

pub fn compile_source(
    source: &str,
    path: &Path,
    config: &CompilerConfig,
    files: &mut SourceMap,
) -> Result<CompiledProject, Vec<RokDiagnostic>> {
    let mut diags: Vec<RokDiagnostic> = Vec::new();
    let (mut config, prebuilt) = load_prebuilt(config, &mut diags);
    if !diags.is_empty() {
        return Err(diags);
    }
    let archives: Vec<PathBuf> = prebuilt.iter().rev().map(|p| p.archive.clone()).collect();
    if config.std_lib {
        return compile_std(source, path, config, &prebuilt, files);
    }
    let Some(lib) = config.lib_name.take() else {
        let r = compile_unit(source, path, &config, &prebuilt, None, files);
        OVERLAY.with(|o| o.borrow_mut().clear());
        let mut p = r?;
        if let Some(m) = p.modules.first_mut() {
            m.archives = archives;
        }
        return Ok(p);
    };
    // The library is a dependency `lib` of an empty package (whose own
    // hash is unique per library: closures etc. are named in it).
    let src_dir = path.parent().unwrap_or_else(|| Path::new(""));
    let dir = std::path::absolute(src_dir).unwrap_or_default();
    let keep_ast = config.keep_ast;
    config.keep_ast = true;
    config.externs.push((lib.clone(), path.to_path_buf()));
    let root = dir.join(format!("{lib}.prebuilt")).join("lib.rok");
    let stub = format!("// prebuilt library `{lib}`\n");
    let r = compile_unit(&stub, &root, &config, &prebuilt, Some(&lib), files);
    OVERLAY.with(|o| o.borrow_mut().clear());
    let mut p = r?;
    let seeds = p
        .modules
        .first()
        .map(|m| m.hir.any_seeds.clone())
        .unwrap_or_default();
    let interface = rokhir::interface(&p.sources, files, &lib, src_dir, &seeds, true);
    if !keep_ast {
        p.sources.clear();
    }
    if let Some(m) = p.modules.first_mut() {
        m.archives = archives;
        let hash = m
            .mir
            .link
            .packages
            .iter()
            .find(|(n, _)| *n == lib)
            .map(|(_, h)| h.clone())
            .unwrap_or_default();
        m.interface = Some(rokhir::Rokhir {
            producer: rokhir::producer(),
            hash,
            name: lib,
            src_dir: dir,
            type_offset: m.mir.link.type_offset,
            type_count: 0,
            features: config
                .cfg_flags
                .iter()
                .filter_map(|f| cfg::feature_of(f).map(str::to_owned))
                .collect(),
            files: interface,
        });
    }
    Ok(p)
}

/// The bootstrap tiers as prebuilt library `rok` (`std_lib`), with
/// `path` an empty package's root.
fn compile_std(
    source: &str,
    path: &Path,
    mut config: CompilerConfig,
    prebuilt: &[Prebuilt],
    sources: &mut SourceMap,
) -> Result<CompiledProject, Vec<RokDiagnostic>> {
    let keep_ast = config.keep_ast;
    config.keep_ast = true;
    let r = compile_unit(source, path, &config, prebuilt, Some(STD_PKG), sources);
    OVERLAY.with(|o| o.borrow_mut().clear());
    let mut p = r?;
    let no_dir = || {
        vec![RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Module,
            rokc_diagnostic::Span::DUMMY,
            "the bootstrap tiers must be the folders of one directory".to_owned(),
        )]
    };
    let tiers: Vec<(String, PathBuf)> = lib_roots(&config)
        .into_iter()
        .filter(|(prefix, _)| prefix.first().is_some_and(|f| f == STD_PKG))
        .map(|(prefix, root)| {
            (
                prefix.join("::"),
                root.parent().unwrap_or(&root).to_path_buf(),
            )
        })
        .collect();
    let src_dir = match tiers.first().and_then(|(_, d)| d.parent()) {
        Some(d) if tiers.iter().all(|(_, t)| t.parent() == Some(d)) => d.to_path_buf(),
        _ => return Err(no_dir()),
    };
    let Some(m) = p.modules.first_mut() else {
        return Ok(p);
    };
    let mut files = Vec::new();
    let in_tier = |module: &str, pkg: &str| {
        module
            .strip_prefix(pkg)
            .is_some_and(|r| r.is_empty() || r.starts_with("::"))
    };
    for (i, (pkg, dir)) in tiers.iter().enumerate() {
        // A seed homed in no tier (`rok` itself) goes to the first's root.
        let seeds: Vec<(String, String)> = m
            .hir
            .any_seeds
            .iter()
            .filter(|(module, _)| {
                in_tier(module, pkg) || (i == 0 && !tiers.iter().any(|(t, _)| in_tier(module, t)))
            })
            .cloned()
            .collect();
        let tier = dir
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        for (rel, text) in rokhir::interface(&p.sources, sources, pkg, dir, &seeds, false) {
            files.push((format!("{tier}/{rel}"), text));
        }
    }
    let hash = m
        .mir
        .link
        .packages
        .iter()
        .filter(|(n, _)| rokc_mir::Link::owns(STD_PKG, n))
        .map(|(n, h)| format!("{n}={h}"))
        .collect::<Vec<_>>()
        .join(";");
    m.interface = Some(rokhir::Rokhir {
        producer: rokhir::producer(),
        hash,
        name: STD_PKG.to_owned(),
        src_dir,
        type_offset: m.mir.link.type_offset,
        type_count: 0,
        features: Vec::new(),
        files,
    });
    if !keep_ast {
        p.sources.clear();
    }
    Ok(p)
}

fn compile_unit(
    source: &str,
    path: &Path,
    config: &CompilerConfig,
    prebuilt: &[Prebuilt],
    lib: Option<&str>,
    files: &mut SourceMap,
) -> Result<CompiledProject, Vec<RokDiagnostic>> {
    // One store per kind of build of the package (a check, a build, a
    // test build ..), so that alternating them keeps each one's.
    let flavor = format!(
        "{}|{}|{}|{}|{:?}|{:?}|{}",
        incr::target_key(&cfg_env(config), &config.target),
        config.check_library,
        config.inline_prebuilt,
        config.keep_ast,
        lib,
        prebuilt.iter().map(|p| &p.rokhir.name).collect::<Vec<_>>(),
        config.std_lib,
    );
    let dir = config
        .incremental
        .as_ref()
        .map(|d| d.join(format!("{:016x}", incr::key(&[flavor.as_bytes()]))));
    let (r, reuse) = incr::with(dir.as_deref(), || {
        compile_unit_in(source, path, config, prebuilt, lib, files)
    });
    r.map(|mut p| {
        p.reuse = reuse;
        p
    })
}

fn compile_unit_in(
    source: &str,
    path: &Path,
    config: &CompilerConfig,
    prebuilt: &[Prebuilt],
    lib: Option<&str>,
    files: &mut SourceMap,
) -> Result<CompiledProject, Vec<RokDiagnostic>> {
    let mut diags: Vec<RokDiagnostic> = Vec::new();

    // Bootstrap PrecTable from operator-declaration sources, if any.
    // The same pre-pass gathers every meta block (spec 6.8) of the
    // library and the user package before any derive is expanded.
    let roots = lib_roots(config);
    // The library's parses are cached across builds (a REPL session)
    // when nothing that changes them changed; never with prebuilt
    // dependencies (their sources are an overlay) or kept ASTs.
    let cache = config.cache_library && prebuilt.is_empty() && !config.keep_ast && lib.is_none();
    let (mut prec, mut d, mut metas) = rokc_diagnostic::time("prepass library", || {
        cached(
            &PREPASS_CACHE,
            cache,
            format!("{roots:?}"),
            files,
            |files| {
                let (mut diags, mut metas) = (Vec::new(), PrePass::default());
                let prec = build_prec_table(&roots, &mut diags, &mut metas, files);
                (prec, diags, metas)
            },
        )
    });
    diags.append(&mut d);
    let lib_metas = metas.metas.len();
    // Spec 6.7.11: the user package's own `#[infix]` registrations are
    // gathered by the same pre-pass, so its extension tokens lex.
    metas.idents = Some(Vec::new());
    let mut user = Vec::new();
    let sub_dir = path.parent();
    let mut pre = prepass_parse(
        vec![(
            path.to_path_buf(),
            Some(source.to_owned()),
            sub_dir.map(Path::to_path_buf),
        )],
        files,
    );
    prepass_tree(path, sub_dir, &[], &mut pre, &mut metas, &mut user);
    for (sub, mut d) in user {
        diags.append(&mut d);
        diags.extend(sub.entries().cloned().filter_map(|e| prec.merge(e)));
    }
    diags.extend(cross_file_confusables(
        metas.idents.take().unwrap_or_default(),
    ));
    for d in &mut metas.metas[lib_metas..] {
        d.set_package("");
    }
    let user_metas = format!("{:?}", &metas.metas[lib_metas..]);
    let ext = prec.ext_ops();
    relex_metas(&mut metas, &ext);
    let cfg_env = cfg_env(config);
    let mut meta_table = MetaTable::default();
    diags.extend(
        metas
            .metas
            .into_iter()
            .filter(|m| cfg::attrs_pass(&m.cfg, &cfg_env))
            .filter_map(|m| meta_table.add(m)),
    );
    let meta_table = std::sync::Arc::new(meta_table);
    let root_dir_kw = path
        .parent()
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    // 6.6.13: a handler whose cfg is false registers nothing.
    let kw_defs = metas
        .keywords
        .into_iter()
        .filter(|d| cfg::attrs_pass(&d.cfg, &cfg_env))
        .collect();
    let keywords = keyword_tables(kw_defs, path, &root_dir_kw, &roots, &mut diags);
    let (lib_lits, user_lits) =
        literal_tables(metas.literals, path, &root_dir_kw, &roots, &ext, &mut diags);
    // Per package: the user's, then each library root's.
    let metas: Vec<MetaCtx> = (0..=roots.len())
        .map(|i| MetaCtx {
            table: std::sync::Arc::clone(&meta_table),
            keywords: keywords.get(i).cloned().unwrap_or_default(),
            literals: std::sync::Arc::clone(if i == 0 { &user_lits } else { &lib_lits }),
            key: std::sync::OnceLock::new(),
            target: config.target.clone(),
            cfg: match roots
                .get(i.wrapping_sub(1))
                .map(|(prefix, _)| prefix.join("::"))
            {
                // The library being built has the build's features; a
                // prebuilt one those it was built with; others none.
                None => cfg_env.clone(),
                Some(p) if lib == Some(p.as_str()) => cfg_env.clone(),
                Some(p) => {
                    let built = prebuilt.iter().find(|b| b.rokhir.name == p);
                    package_cfg(config, Some(built.map_or(&[], |b| &b.rokhir.features)))
                }
            },
        })
        .collect();
    let incr = incr::current();
    let ids = incr::Ids::of(files);
    rokc_diagnostic::time("parse", || {
        real_parse(
            incr.as_deref().map(|i| (i, &ids)),
            &root_dir_kw,
            &roots,
            &metas,
            &ext,
            config.keep_ast,
        );
    });
    // Walk the user package's module tree (`mod foo;` follows files
    // alongside the entry `main.rok` / `lib.rok`) and merge every
    // visited file's items into one `Program` so HIR sees a single
    // flat compilation unit.
    let root_dir = path
        .parent()
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    // Spec 4.16.8: the anonymous package has no file submodules.
    let sub_dir = (!config.anonymous).then_some(root_dir.as_path());
    let mut sources = Vec::new();

    let mut all_items: Vec<ModItem> = Vec::new();
    let mut all_uses: Vec<(String, rokc_core::Visibility, rokc_ast::UseTree)> = Vec::new();
    NO_IMPLICIT.with(|n| n.borrow_mut().clear());
    let top_stmts = rokc_diagnostic::time("parse package", || {
        collect_module_tree(
            path,
            Some(source),
            sub_dir,
            &[],
            &ext,
            &metas[0],
            &mut diags,
            &mut all_items,
            &mut all_uses,
            config.keep_ast.then_some(&mut sources),
            files,
        )
    });
    let is_lib = !config.anonymous && path.file_name().is_some_and(|n| n == "lib.rok");
    let mut tests = Vec::new();
    let mut root_main = rokc_hir::RootMain::Declared;
    // An entry file with neither `main` nor statements.
    let mut no_entry = false;
    if config.test || config.bench {
        // Top-level statements are the package's own entry: dropped.
        tests = harness::install(&mut all_items, &ext, &mut diags, config.bench);
        root_main = rokc_hir::RootMain::Harness;
    } else if !is_lib {
        let has_main = all_items
            .iter()
            .any(|(m, i)| m.is_empty() && matches!(i, rokc_ast::Item::Fn(f) if f.name == "main"));
        no_entry = top_stmts.is_empty() && !has_main;
        if entry::resolve_entry(top_stmts, &mut all_items, &mut diags) {
            root_main = rokc_hir::RootMain::Implicit;
        }
    } else if !top_stmts.is_empty() {
        diags.push(entry::stmts_outside_entry(path));
    }
    check_dependency_names(&all_items, &all_uses, &config.externs, &mut diags);
    // Mount each library root (`rok::<tier>`, then the dependencies) and
    // compile its items with the user's; HIR gives every module an
    // implicit `use rok::core::**;` (stdlib spec 0.1).
    let key = format!(
        "{roots:?}|{:?}|{}|{}|{ext:?}|{user_metas}|{keywords:?}",
        config.cfg_flags, config.test, config.bench
    );
    let parse_libs = rokc_diagnostic::time_passes().then(std::time::Instant::now);
    let (mut items, mut uses, mut d) = cached(&LIB_CACHE, cache, key, files, |files| {
        let (mut items, mut uses, mut diags) = (Vec::new(), Vec::new(), Vec::new());
        for (i, (prefix, root)) in roots.iter().enumerate() {
            let first = sources.len();
            let stray = collect_module_tree(
                root,
                None,
                root.parent(),
                prefix,
                &ext,
                &metas[i + 1],
                &mut diags,
                &mut items,
                &mut uses,
                config.keep_ast.then_some(&mut sources),
                files,
            );
            if !stray.is_empty() {
                diags.push(entry::stmts_outside_entry(root));
            }
            let pkg = prefix.join("::");
            for f in &mut sources[first..] {
                f.package.clone_from(&pkg);
            }
        }
        (items, uses, diags)
    });
    if let Some(t) = parse_libs {
        eprintln!(
            "time: {:>9.1}ms  parse library",
            t.elapsed().as_secs_f64() * 1e3
        );
    }
    // Parses not taken (cached library, cfg'd-out modules), dropped on
    // another thread.
    let rest = PARSED.with(std::cell::RefCell::take);
    let _ = std::thread::Builder::new()
        .stack_size(AST_STACK)
        .spawn(move || drop(rest));
    all_items.append(&mut items);
    all_uses.append(&mut uses);
    diags.append(&mut d);
    // `ffi::wit` of the package and of its dependencies.
    let packages: Vec<String> = roots.iter().map(|(p, _)| p.join("::")).collect();
    let prebuilt_names: Vec<String> = prebuilt.iter().map(|p| p.rokhir.name.clone()).collect();
    let mut wit_link = wit::expand(
        &mut all_items,
        &mut all_uses,
        &packages,
        &prebuilt_names,
        &config.target,
        &ext,
        &metas[0],
        &mut diags,
        files,
    );
    // A component exporting WIT whose entry file has neither `main` nor
    // statements is a reactor: its exports, no `wasi:cli/run` (its empty
    // implicit `main` is never called).
    if let Some(w) = wit_link
        .as_mut()
        .filter(|w| no_entry && w.exports.iter().any(|e| e != "cabi_realloc"))
    {
        w.reactor = true;
    }
    coro::rewrite_items(&mut all_items, &mut diags);
    let (item_modules, items): (Vec<String>, Vec<rokc_ast::Item>) = all_items.into_iter().unzip();
    let input = rokc_hir::HirInput {
        packages: config.externs.iter().map(|(n, _)| n.clone()).collect(),
        lib: lib.map(str::to_owned),
        prebuilt: prebuilt.iter().map(|p| p.rokhir.name.clone()).collect(),
        check_library: config.check_library,
        root_main,
        inline_prebuilt: config.inline_prebuilt,
        pointer_width: config.target.pointer_width,
        item_modules,
        no_implicit_rok: NO_IMPLICIT.with(std::cell::RefCell::take),
        fingerprint: incr::key(&[incr::target_key(&cfg_env, &config.target).as_bytes()]),
        bodies: incr::current().map(|i| incr::bodies(i, files)),
    };
    let program = rokc_ast::Program {
        attrs: Vec::new(),
        items,
        stmts: Vec::new(),
        expanded: Vec::new(),
        tops: Vec::new(),
    };

    // Name resolution and type / exhaustiveness checking happen during
    // HIR lowering (`rokc_hir::lower_full`), where every type is known.
    // Warnings go out with the errors (a failed build still shows them).
    if diags.iter().any(RokDiagnostic::is_error) {
        return Err(diags);
    }

    // Convert raw use trees into a per-module table of resolution
    // entries that the HIR resolver can consult during name lookup, plus
    // a list of `pub use` re-exports the lower pass installs as fn-table
    // aliases.
    let (use_table, reexports, mut use_diags) = rokc_diagnostic::time("use table", || {
        rokc_hir::build_use_table(&all_uses, &input.packages)
    });
    diags.append(&mut use_diags);
    let mut libs = Vec::new();
    native_libs(&program.items, &mut libs);
    let mut hir = rokc_diagnostic::time("hir", || {
        let lower = |program, input: &rokc_hir::HirInput| {
            rokc_hir::lower_full(
                program, &prec, &all_uses, &use_table, &reexports, input, files,
            )
        };
        match input.bodies.is_some().then(incr::verify).flatten() {
            Some(check) => {
                let clean = lower(
                    program.clone(),
                    &rokc_hir::HirInput {
                        bodies: None,
                        ..input.clone()
                    },
                );
                let mut hir = lower(program, &input);
                check(&clean, &mut hir);
                hir
            }
            None => lower(program, &input),
        }
    });
    diags.append(&mut hir.diagnostics);
    if let Some(i) = incr::current() {
        i.bodies_reused(hir.reuse.replayed, hir.reuse.lowered);
    }
    // Warnings go out with the errors (a failed build still shows them).
    if diags.iter().any(RokDiagnostic::is_error) {
        return Err(diags);
    }
    let mut mir = rokc_diagnostic::time("mir", || rokc_mir::lower(&hir, &config.target));
    mir.link.packages = package_hashes(&root_dir, &roots, files);
    for p in prebuilt {
        // The standard library's hash is one per tier: `pkg=hash;..`.
        let hashes: Vec<(&str, &str)> = if p.rokhir.name == STD_PKG {
            p.rokhir
                .hash
                .split(';')
                .filter_map(|kv| kv.split_once('='))
                .collect()
        } else {
            vec![(p.rokhir.name.as_str(), p.rokhir.hash.as_str())]
        };
        for (name, hash) in hashes {
            if let Some(h) = mir.link.packages.iter_mut().find(|(n, _)| n == name) {
                hash.clone_into(&mut h.1);
            }
        }
    }
    mir.link.native_libs = libs;
    mir.link.wit = wit_link;
    mir.link.lib = input.lib;
    mir.link.prebuilt = input.prebuilt;
    mir.link.type_offset = prebuilt
        .iter()
        .map(|p| p.rokhir.type_end())
        .max()
        .unwrap_or(0);

    Ok(CompiledProject {
        modules: vec![CompiledModule {
            name: path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("module")
                .to_owned(),
            path: path.to_path_buf(),
            hir,
            mir,
            archives: Vec::new(),
            interface: None,
        }],
        warnings: diags.into_iter().filter(|d| !d.is_error()).collect(),
        tests,
        sources,
        files: READ.with(std::cell::RefCell::take),
        reuse: None,
    })
}

/// Lower MIR again after an embedder edited the HIR (the REPL's slot
/// stores).
pub fn relower(m: &mut CompiledModule) {
    let link = std::mem::take(&mut m.mir.link);
    m.mir = rokc_mir::lower(&m.hir, &m.mir.target);
    m.mir.link = link;
}

/// Spec 0.3.3: each package's hash is the SHA-256 (first 8 hex digits)
/// of its source files in path order — `rok::<tier>` for each library
/// root, `""` for the user package. A file belongs to the package whose
/// directory is its closest ancestor. Longest prefix first (mangling
/// picks the first match).
fn package_hashes(
    user_dir: &Path,
    roots: &[LibRoot],
    sources: &SourceMap,
) -> Vec<(String, String)> {
    let mut pkgs: Vec<(String, PathBuf)> = roots
        .iter()
        .filter_map(|(prefix, r)| Some((prefix.join("::"), r.parent()?.to_path_buf())))
        .collect();
    pkgs.push((String::new(), user_dir.to_path_buf()));
    let files = sources.files();
    let mut out: Vec<(String, String)> = pkgs
        .iter()
        .map(|(prefix, dir)| {
            let mut mine: Vec<(String, &str)> = files
                .iter()
                .filter_map(|(path, text)| {
                    let p = Path::new(path);
                    // The closest package directory owns the file.
                    let owner = pkgs
                        .iter()
                        .filter(|(_, d)| p.starts_with(d))
                        .max_by_key(|(_, d)| d.components().count())?;
                    (owner.1 == *dir).then(|| {
                        let rel = p.strip_prefix(dir).unwrap_or(p);
                        let rel: Vec<String> = rel
                            .components()
                            .map(|c| c.as_os_str().to_string_lossy().into_owned())
                            .collect();
                        (rel.join("/"), text.as_str())
                    })
                })
                .collect();
            (prefix.clone(), hash_package(&mut mine))
        })
        .collect();
    out.sort_by_key(|(p, _)| std::cmp::Reverse(p.len()));
    out
}

/// Spec 0.3.3: SHA-256 over the files in byte-wise order of their
/// package-relative `/` paths, each as `path \0 content \0`; the first
/// 8 hex digits.
fn hash_package(files: &mut Vec<(String, &str)>) -> String {
    files.sort_unstable();
    files.dedup();
    let blob: String = files
        .iter()
        .flat_map(|(rel, text)| [rel.as_str(), "\0", text, "\0"])
        .collect();
    rokc_codegen_mlir::pkg_hash(&blob)
}

fn build_prec_table(
    roots: &[LibRoot],
    diags: &mut Vec<RokDiagnostic>,
    metas: &mut PrePass,
    sources: &mut SourceMap,
) -> PrecTable {
    let mut files = prepass_parse(
        roots
            .iter()
            .map(|(_, root)| (root.clone(), None, root.parent().map(Path::to_path_buf)))
            .collect(),
        sources,
    );
    let mut table = PrecTable::new();
    for (pkg, root) in roots {
        let mut tables = Vec::new();
        let first = metas.metas.len();
        prepass_tree(root, root.parent(), pkg, &mut files, metas, &mut tables);
        let package = pkg.join("::");
        for d in &mut metas.metas[first..] {
            d.set_package(&package);
        }
        for (sub_table, mut collect_diags) in tables {
            diags.append(&mut collect_diags);
            diags.extend(sub_table.entries().cloned().filter_map(|e| table.merge(e)));
        }
    }
    table
}

/// Pre-pass parses by path, with their file ids.
type PreFiles = std::collections::HashMap<PathBuf, (u32, Prepassed)>;

/// The pre-pass parses of the module trees from `roots` (path, text or
/// the file's, directory of its submodules), by path. Breadth first:
/// each level's files are read and registered in order (file ids stay
/// deterministic), then lexed and parsed in parallel.
fn prepass_parse(
    roots: Vec<(PathBuf, Option<String>, Option<PathBuf>)>,
    sources: &mut SourceMap,
) -> PreFiles {
    let mut files = std::collections::HashMap::new();
    let mut seen = std::collections::HashSet::new();
    let mut level = roots;
    while !level.is_empty() {
        let jobs: Vec<(PathBuf, Option<PathBuf>, String, u32)> = level
            .into_iter()
            .filter(|(path, ..)| seen.insert(path.clone()))
            .filter_map(|(path, source, sub_dir)| {
                let source = source.or_else(|| read_source(&path).ok())?;
                let id = sources.add(path.display().to_string(), source.clone());
                Some((path, sub_dir, source, id))
            })
            .collect();
        let incr = incr::current();
        let ids = incr.is_some().then(|| incr::Ids::of(sources));
        let parsed: Vec<Prepassed> = std::thread::scope(|s| {
            let mut parses = Vec::new();
            for (path, _, source, id) in &jobs {
                let incr = incr.as_deref().zip(ids.as_ref());
                parses.push(s.spawn(move || prepass_file(path, source, *id, incr)));
            }
            parses
                .into_iter()
                .map(|p| p.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
                .collect()
        });
        level = Vec::new();
        for ((path, sub_dir, _, id), file) in jobs.into_iter().zip(parsed) {
            mod_files(&file.sum.skeleton, sub_dir.as_deref(), &mut level);
            files.insert(path, (id, file));
        }
    }
    files
}

/// One pre-pass file `id`: lexed without extension operators and parsed
/// (or its summary from the incremental store).
fn prepass_file(
    path: &Path,
    source: &str,
    id: u32,
    incr: Option<(&incr::Incr, &incr::Ids)>,
) -> Prepassed {
    let file = path.display().to_string();
    let k = incr::key(&[b"pre", file.as_bytes(), source.as_bytes()]);
    if let Some(sum) = incr.and_then(|(i, ids)| i.parse.get::<Summary>(k, ids)) {
        return Prepassed {
            source: source.to_owned(),
            sum,
            program: None,
        };
    }
    let (program, sum) = plain_parse(&file, source, id, |tokens, program, quiet| {
        Summary::of(tokens, program, quiet, &file, source)
    });
    if let Some((i, ids)) = incr {
        i.parse.put(k, &sum, ids);
    }
    Prepassed {
        source: source.to_owned(),
        sum,
        program: Some(program),
    }
}

/// File `id` lexed without extension operators and parsed: the program,
/// and `then` of its tokens, the program and whether no diagnostic came
/// up.
fn plain_parse<T>(
    file: &str,
    source: &str,
    id: u32,
    then: impl FnOnce(&[rokc_lexer::Token], &rokc_ast::Program, bool) -> T,
) -> (rokc_ast::Program, T) {
    let (mut tokens, lex) = Lexer::new(source, file.to_owned()).lex_all();
    for t in &mut tokens {
        t.span.file = id;
    }
    let (program, parse) = parse_program(&tokens, file.to_owned());
    let t = then(&tokens, &program, lex.is_empty() && parse.is_empty());
    (program, t)
}

/// The files of the `mod name;` among `items` (inline modules' too),
/// their submodules in `sub_dir`.
fn mod_files(
    items: &[rokc_ast::Item],
    sub_dir: Option<&Path>,
    out: &mut Vec<(PathBuf, Option<String>, Option<PathBuf>)>,
) {
    for item in items {
        if let rokc_ast::Item::Mod(m) = item {
            match &m.items {
                Some(inner) => mod_files(inner, sub_dir, out),
                None => {
                    if let Ok((body, next)) = mod_file(m, sub_dir) {
                        out.push((body, None, next));
                    }
                }
            }
        }
    }
}

/// The pre-pass over a package's module tree from `path` (parsed by
/// `prepass_parse` into `files`), module `module`: each module parsed
/// without extension operators (they are what it finds), submodules
/// first, gathering meta blocks, keywords and literals. Errors are left
/// to the real parse.
fn prepass_tree(
    path: &Path,
    sub_dir: Option<&Path>,
    module: &[String],
    files: &mut PreFiles,
    metas: &mut PrePass,
    out: &mut Vec<(PrecTable, Vec<RokDiagnostic>)>,
) {
    let Some((id, f)) = files.remove(path) else {
        return;
    };
    prepass_gather(&f.sum, &f.source, &path.display().to_string(), id, metas);
    prepass_mods(&f.sum.skeleton, sub_dir, module, files, metas, out);
    let skeleton = rokc_ast::Program {
        attrs: Vec::new(),
        items: f.sum.skeleton.clone(),
        stmts: Vec::new(),
        expanded: Vec::new(),
        tops: Vec::new(),
    };
    out.push(collect_prec_table(&skeleton, module));
    PREPASSED.with(|p| p.borrow_mut().insert(path.to_path_buf(), (id, f)));
}

/// Whether the real parse of `p` (with the build's extension operators,
/// keywords, meta blocks, literals and cfg) would give the pre-pass's
/// tokens and AST: the file uses none of them.
fn reusable(p: &Prepassed, ext: &ExtOps, metas: &MetaCtx) -> bool {
    let sum = &p.sum;
    let prefixes: Vec<Vec<u8>> = metas
        .literals
        .rules
        .iter()
        .filter(|r| r.kind == PatKind::Prefix)
        .filter_map(|r| match r.pattern.elems.first() {
            Some(rokc_parser::PatElem::Tok(k, _)) => Some(kind_bytes(k)),
            _ => None,
        })
        .collect();
    sum.quiet
        && !sum.ext_op
        && !sum.cfg_bang
        && !ext.symbols().iter().any(|s| p.source.contains(s.as_str()))
        && !sum.idents.iter().any(|(n, _)| {
            matches!(n.as_str(), "cfg" | "cfg_attr")
                || metas.table.defines(n)
                || metas.keywords.iter().any(|(k, ..)| k == n)
        })
        && !sum.kinds.iter().any(|k| prefixes.contains(k))
}

/// A token kind's encoding (kinds compare by it).
fn kind_bytes(k: &rokc_lexer::TokenKind) -> Vec<u8> {
    let mut e = rokc_core::codec::Enc::new(false);
    rokc_core::codec::Codec::enc(k, &mut e);
    e.buf
}

fn prepass_mods(
    items: &[rokc_ast::Item],
    sub_dir: Option<&Path>,
    module: &[String],
    files: &mut PreFiles,
    metas: &mut PrePass,
    out: &mut Vec<(PrecTable, Vec<RokDiagnostic>)>,
) {
    for item in items {
        let rokc_ast::Item::Mod(m) = item else {
            continue;
        };
        let before = metas.metas.len();
        let mut sub = module.to_vec();
        sub.push(m.name.clone());
        match &m.items {
            Some(inner) => prepass_mods(inner, sub_dir, &sub, files, metas, out),
            None => {
                if let Ok((body, next)) = mod_file(m, sub_dir) {
                    prepass_tree(&body, next.as_deref(), &sub, files, metas, out);
                }
            }
        }
        // The module's `#[cfg]` holds for the meta blocks of its files
        // (a block is registered only when its cfgs hold).
        let cfg = m.attrs.iter().filter(|a| a.name() == "cfg");
        for d in &mut metas.metas[before..] {
            d.cfg.extend(cfg.clone().cloned());
        }
    }
}

/// The file of `mod name;` declared in a module whose submodules live in
/// `dir` (spec 5.4.4), and the directory of its own submodules. A
/// `#[path("f.rok")]` (5.4.6) names the file relative to `dir`; its
/// submodules are in `f/` beside it.
fn mod_file(
    m: &rokc_ast::ModDef,
    dir: Option<&Path>,
) -> Result<(PathBuf, Option<PathBuf>), RokDiagnostic> {
    let name = &m.name;
    let err = |msg: String| {
        RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Module,
            rokc_diagnostic::Span::DUMMY,
            msg,
        )
    };
    let custom = m.attrs.iter().find(|a| a.path == ["path"]).map(|a| {
        match &a.body {
            rokc_ast::AttrBody::Args(args) => match args.as_slice() {
                [rokc_ast::AttrArg::Lit(rokc_ast::Literal::Str(p))] => Ok(p.clone()),
                _ => Err(()),
            },
            _ => Err(()),
        }
        .map_err(|()| {
            err("`#[path]` takes one file path: `#[path(\"file.rok\")]` (spec 5.4.6)".to_owned())
                .with_span(a.span, "")
        })
    });
    let Some(dir) = dir else {
        return Err(err(format!(
            "`mod {name}` in a single-file module — declare a sibling `{name}/` folder to \
             host submodules (a lone file run outside any package cannot have file \
             submodules, spec 4.16.8; use `mod {name} {{ }}`)"
        )));
    };
    let (body, folder) = match custom.transpose()? {
        Some(p) => {
            let body = dir.join(&p);
            let folder = body.with_extension("");
            (body, folder)
        }
        None => (dir.join(format!("{name}.rok")), dir.join(name)),
    };
    if !source_exists(&body) {
        return Err(err(format!(
            "module `{name}` body not found at `{}`",
            body.display()
        )));
    }
    let next = source_dir_exists(&folder).then_some(folder);
    Ok((body, next))
}

/// A file that defines meta blocks (`@`), keywords or literals: the
/// pre-pass gathers them, and its interface copy is kept whole.
pub(crate) fn defines_metas(tokens: &[rokc_lexer::Token], source: &str) -> bool {
    tokens.iter().any(|t| t.kind == rokc_lexer::TokenKind::At)
        || source.contains("#[keyword(")
        || source.contains("#[literal(")
}

/// Gather the meta blocks, keywords and literals of a pre-pass file
/// `id` (their template tokens keep spans into file `id`).
fn prepass_gather(sum: &Summary, source: &str, file: &str, id: u32, metas: &mut PrePass) {
    if let Some(idents) = &mut metas.idents {
        // The user package's names, first use per file.
        idents.extend(sum.idents.iter().cloned());
    }
    if !sum.metas.is_empty() {
        metas
            .meta_files
            .push((file.to_owned(), source.to_owned(), id));
    }
    metas.metas.extend(sum.metas.iter().cloned());
    metas.keywords.extend(sum.keywords.iter().cloned());
    metas.literals.extend(sum.literals.iter().cloned());
}

/// Spec 1.4.2: distinct names of one package with the same confusable
/// skeleton warn. The lexer checks each file; this checks pairs across
/// the package's files.
fn cross_file_confusables(idents: Vec<(String, rokc_diagnostic::Span)>) -> Vec<RokDiagnostic> {
    if idents.iter().all(|(n, _)| n.is_ascii()) {
        return Vec::new();
    }
    let mut first: std::collections::HashMap<String, &(String, rokc_diagnostic::Span)> =
        std::collections::HashMap::new();
    let mut out = Vec::new();
    for id in &idents {
        match first.entry(rokc_lexer::unicode::skeleton(&id.0)) {
            std::collections::hash_map::Entry::Occupied(o) => {
                let (name, at) = o.get();
                if *name != id.0 && at.file != id.1.file {
                    out.push(
                        RokDiagnostic::warning(
                            rokc_diagnostic::ErrorKind::Lexical,
                            id.1,
                            format!(
                                "identifier `{}` looks like `{name}` (confusable spelling)",
                                id.0
                            ),
                        )
                        .with_secondary(*at, "the other spelling"),
                    );
                }
            }
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(id);
            }
        }
    }
    out
}

/// The pre-pass lexed meta block bodies before the extension operators
/// (spec 1.10.4) were known: gather them again with those operators, so
/// a template can use `⊕`.
fn relex_metas(metas: &mut PrePass, ext: &rokc_parser::ExtOps) {
    let symbols = ext.symbols();
    if symbols.is_empty() || metas.meta_files.is_empty() {
        return;
    }
    // What the module tree gave each block: its package and the cfgs of
    // enclosing modules.
    let placed: std::collections::HashMap<_, _> = std::mem::take(&mut metas.metas)
        .into_iter()
        .map(|d| ((d.file, d.span), (d.package, d.cfg)))
        .collect();
    for (file, source, id) in &metas.meta_files {
        let lexer = Lexer::new(source, file.clone()).with_ext_ops(symbols.clone());
        let (mut tokens, _) = lexer.lex_all();
        for t in &mut tokens {
            t.span.file = *id;
        }
        for mut d in collect_meta_blocks(&tokens, file) {
            if let Some((package, cfg)) = placed.get(&(d.file.clone(), d.span)) {
                d.set_package(package);
                d.cfg.clone_from(cfg);
            }
            metas.metas.push(d);
        }
    }
}

/// What the pre-pass gathers besides operators: meta blocks (6.8) and
/// keyword registrations (6.6).
#[derive(Clone, Default)]
struct PrePass {
    metas: Vec<MetaDef>,
    /// While the user package is pre-lexed: its identifiers, first use
    /// per file (`cross_file_confusables`).
    idents: Option<Vec<(String, rokc_diagnostic::Span)>>,
    /// Files with meta blocks (path, source, file id): lexed again once
    /// the extension operators are known (`relex_metas`).
    meta_files: Vec<(String, String, u32)>,
    keywords: Vec<KeywordDef>,
    literals: Vec<LiteralDef>,
}

/// A file the pre-pass parsed (without extension operators, keywords,
/// meta blocks, literals or cfg), for the real parse to take when it
/// is `reusable`.
struct Prepassed {
    source: String,
    sum: Summary,
    /// The parse, unless the summary came from the incremental store.
    program: Option<rokc_ast::Program>,
}

/// What the pre-pass needs of a file's plain parse.
struct Summary {
    /// Its `mod` and `trait` items (`trait` method bodies dropped): the
    /// module tree and the operator declarations.
    skeleton: Vec<rokc_ast::Item>,
    /// Lexed and parsed without a diagnostic.
    quiet: bool,
    /// Each identifier at its first use.
    idents: Vec<(String, rokc_diagnostic::Span)>,
    /// Its other token kinds (`kind_bytes`), each once.
    kinds: Vec<Vec<u8>>,
    /// An extension-operator token; `cfg!`.
    ext_op: bool,
    cfg_bang: bool,
    /// The path literals of its `include_str!("..")` / `include_bytes!("..")`.
    includes: Vec<String>,
    metas: Vec<MetaDef>,
    keywords: Vec<KeywordDef>,
    literals: Vec<LiteralDef>,
}

rokc_core::codec_struct!(Summary {
    skeleton,
    quiet,
    idents,
    kinds,
    ext_op,
    cfg_bang,
    includes,
    metas,
    keywords,
    literals,
});

impl Summary {
    fn of(
        tokens: &[rokc_lexer::Token],
        program: &rokc_ast::Program,
        quiet: bool,
        file: &str,
        source: &str,
    ) -> Self {
        use rokc_lexer::TokenKind as T;
        let mut seen = std::collections::HashSet::new();
        let mut kinds = std::collections::HashSet::new();
        let mut sum = Self {
            skeleton: skeleton(&program.items),
            quiet,
            idents: Vec::new(),
            kinds: Vec::new(),
            ext_op: false,
            cfg_bang: false,
            includes: Vec::new(),
            metas: Vec::new(),
            keywords: Vec::new(),
            literals: Vec::new(),
        };
        for (i, t) in tokens.iter().enumerate() {
            match &t.kind {
                T::Ident(n) => {
                    if seen.insert(n.as_str()) {
                        sum.idents.push((n.clone(), t.span));
                    }
                    if n == "cfg" && tokens.get(i + 1).is_some_and(|b| b.kind == T::Bang) {
                        sum.cfg_bang = true;
                    }
                    if let (
                        "include_str" | "include_bytes",
                        [
                            rokc_lexer::Token { kind: T::Bang, .. },
                            rokc_lexer::Token {
                                kind: T::LParen, ..
                            },
                            rokc_lexer::Token {
                                kind: T::StrLit(s), ..
                            },
                            ..,
                        ],
                    ) = (n.as_str(), tokens.get(i + 1..).unwrap_or_default())
                    {
                        sum.includes.push(s.clone());
                    }
                }
                T::ExtOp(_) => sum.ext_op = true,
                k => {
                    let b = kind_bytes(k);
                    if kinds.insert(b.clone()) {
                        sum.kinds.push(b);
                    }
                }
            }
        }
        if defines_metas(tokens, source) {
            sum.metas = collect_meta_blocks(tokens, file);
            sum.keywords = collect_keywords(&program.items, file);
            sum.literals = collect_literals(tokens, file);
        }
        sum
    }
}

/// What `collect_prec_table` reads of `items`: the `mod` and `trait`
/// items (inline modules' too), and the functions and `impl` methods
/// with an operator attribute (misplaced ones), bodies dropped.
fn skeleton(items: &[rokc_ast::Item]) -> Vec<rokc_ast::Item> {
    use rokc_ast::{ImplItem, Item, TraitItem};
    let op = |f: &rokc_ast::FnDef| {
        f.attrs
            .iter()
            .any(|a| matches!(a.name(), "infix" | "prefix" | "postfix"))
    };
    let op_method = |m: &ImplItem| matches!(m, ImplItem::Method(f) if op(f));
    items
        .iter()
        .filter_map(|item| match item {
            Item::Mod(m) => {
                let mut m = m.clone();
                m.items = m.items.as_deref().map(skeleton);
                Some(Item::Mod(m))
            }
            Item::Trait(t) => {
                let mut t = t.clone();
                for ti in &mut t.items {
                    if let TraitItem::Method(f) = ti {
                        f.body = None;
                    }
                }
                Some(Item::Trait(t))
            }
            Item::Fn(f) if op(f) => Some(Item::Fn(rokc_ast::FnDef {
                body: None,
                ..f.clone()
            })),
            Item::Impl(i) if i.items.iter().any(op_method) => {
                let mut i = i.clone();
                i.items.retain(op_method);
                for m in &mut i.items {
                    if let ImplItem::Method(f) = m {
                        f.body = None;
                    }
                }
                Some(Item::Impl(i))
            }
            _ => None,
        })
        .collect()
}

thread_local! {
    /// This compile's pre-pass parses by file path, with their file ids.
    static PREPASSED: std::cell::RefCell<PreFiles> =
        std::cell::RefCell::new(std::collections::HashMap::new());
    /// This compile's real parses by file path (`real_parse`).
    static PARSED: std::cell::RefCell<std::collections::HashMap<PathBuf, Parsed>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
    /// The modules whose file opts out of `use rok::core::**;`
    /// (`#![no_implicit_rok]`, stdlib 0.2.5).
    static NO_IMPLICIT: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// A file's real parse, ready for the module tree walk: its items
/// with `#[cfg]` applied, top-level statements, a copy for
/// `CompilerConfig::keep_ast` (module path not yet set), and its
/// diagnostics.
struct Parsed {
    items: Vec<rokc_ast::Item>,
    stmts: Vec<rokc_ast::Stmt>,
    /// `#![no_implicit_rok]`.
    no_implicit: bool,
    kept: Option<SourceFile>,
    diags: Vec<RokDiagnostic>,
    /// The files its `include_str!` / `include_bytes!` read.
    includes: Vec<PathBuf>,
}

// An AST is as deep as its longest operator chain, and dropping or
// cloning it recurses that deep: the threads that do get the stack of
// rokc's main thread (address space until used).
const AST_STACK: usize = 1 << 30;

/// The real parse of every pre-passed file, in parallel, into `PARSED`:
/// a file's package (the closest of `user_dir` and the library roots'
/// directories) picks its `metas` (user first, then each root). File ids
/// are the pre-pass's, so the result does not depend on the order the
/// threads finish in. Token buffers are dropped, and the `keep` copies
/// made, on the worker threads.
fn real_parse(
    incr: Option<(&incr::Incr, &incr::Ids)>,
    user_dir: &Path,
    roots: &[LibRoot],
    metas: &[MetaCtx],
    ext: &ExtOps,
    keep: bool,
) {
    let files: Vec<(PathBuf, (u32, Prepassed))> =
        PREPASSED.with(|p| p.borrow_mut().drain().collect());
    let dirs: Vec<PathBuf> = package_roots(user_dir, roots)
        .into_iter()
        .map(|(d, _)| d)
        .collect();
    let parsed: Vec<(PathBuf, Parsed)> = std::thread::scope(|s| {
        let dirs = &dirs;
        let mut jobs = Vec::new();
        for (path, (file_id, pre)) in files {
            let job = std::thread::Builder::new().stack_size(AST_STACK);
            let job = job.spawn_scoped(s, move || {
                let (pkg, _) = dirs
                    .iter()
                    .enumerate()
                    .filter(|(_, d)| path.starts_with(d))
                    .max_by_key(|(_, d)| d.components().count())?;
                let metas = metas.get(pkg)?;
                let includes = included(&path, &pre.sum.includes);
                let (program, diags) =
                    cached_parse(&path, file_id, pre, &includes, incr, ext, metas);
                let mut parsed = settle(&path, file_id, program, diags, metas, keep);
                parsed.includes = includes.into_iter().map(|(p, _)| p).collect();
                Some((path, parsed))
            });
            jobs.push(job.expect("spawn a parse thread"));
        }
        jobs.into_iter()
            .filter_map(|j| j.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
            .collect()
    });
    READ.with(|r| {
        let mut r = r.borrow_mut();
        r.extend(parsed.iter().flat_map(|(_, p)| p.includes.iter().cloned()));
    });
    PARSED.with(|p| p.borrow_mut().extend(parsed));
}

/// The files `includes` (`Summary::includes`) of the file at `path`
/// name, and the key part of their contents.
fn included(path: &Path, includes: &[String]) -> Vec<(PathBuf, Vec<u8>)> {
    let file = path.display().to_string();
    includes
        .iter()
        .map(|lit| {
            let p = rokc_parser::include_path(&file, lit);
            let data = std::fs::read(&p).map_or_else(
                |_| b"-".to_vec(),
                |d| format!("+{:016x}", incr::key(&[&d])).into_bytes(),
            );
            (p, data)
        })
        .collect()
}

/// The real parse of pre-passed file `file_id` at `path`: the
/// pre-pass's when `reusable`, else with the package's tables; from the
/// incremental store when it has it (and the files it includes are
/// unchanged).
fn cached_parse(
    path: &Path,
    file_id: u32,
    pre: Prepassed,
    includes: &[(PathBuf, Vec<u8>)],
    incr: Option<(&incr::Incr, &incr::Ids)>,
    ext: &ExtOps,
    metas: &MetaCtx,
) -> (rokc_ast::Program, Vec<RokDiagnostic>) {
    let file = path.display().to_string();
    let source = pre.source.as_bytes();
    let inc: Vec<u8> = includes
        .iter()
        .flat_map(|(p, k)| [p.display().to_string().as_bytes(), b"\0", k].concat())
        .collect();
    if reusable(&pre, ext, metas) {
        let k = incr::key(&[b"plain", file.as_bytes(), source, &inc]);
        let cached = match pre.program {
            Some(_) => None,
            None => incr.and_then(|(i, ids)| i.parse.get(k, ids)),
        };
        if let Some((i, _)) = incr {
            i.count_parse(cached.is_some());
        }
        let program = cached.unwrap_or_else(|| {
            let program = pre
                .program
                .unwrap_or_else(|| plain_parse(&file, &pre.source, file_id, |_, _, _| ()).0);
            if let Some((i, ids)) = incr {
                i.parse.put(k, &program, ids);
            }
            program
        });
        return (program, Vec::new());
    }
    let tables = metas.tables_key(ext).to_le_bytes();
    let k = incr::key(&[b"parse", file.as_bytes(), source, &tables, &inc]);
    let cached = incr.and_then(|(i, ids)| i.parse.get(k, ids));
    if let Some((i, _)) = incr {
        i.count_parse(cached.is_some());
    }
    cached.unwrap_or_else(|| {
        let parsed = parse_file(&pre.source, file, file_id, ext, metas);
        if let Some((i, ids)) = incr {
            i.parse.put(k, &parsed, ids);
        }
        parsed
    })
}

/// Check the `#[cfg]` predicates of `program` (before filtering drops
/// the items they guard), drop the items they rule out, check the other
/// attributes, and (`keep`) copy the file.
fn settle(
    path: &Path,
    file_id: u32,
    program: rokc_ast::Program,
    mut diags: Vec<RokDiagnostic>,
    metas: &MetaCtx,
    keep: bool,
) -> Parsed {
    attrs::check_cfg(&program.attrs, &program.items, &metas.table, &mut diags);
    let items = cfg::filter_items(program.items, &metas.cfg);
    attrs::check(&program.attrs, &items, &metas.table, &mut diags);
    let no_implicit = program.attrs.iter().any(|a| a.path == ["no_implicit_rok"]);
    let kept = keep.then(|| SourceFile {
        path: path.to_path_buf(),
        file_id,
        package: String::new(),
        module: Vec::new(),
        attrs: program.attrs,
        items: items.clone(),
        stmts: program.stmts.clone(),
        expanded: program.expanded,
    });
    Parsed {
        items,
        stmts: program.stmts,
        no_implicit,
        kept,
        diags,
        includes: Vec::new(),
    }
}

/// Lex and parse `source`, file `file_id`, with the build's extension
/// operators, the package's keywords and meta blocks, and cfg.
fn parse_file(
    source: &str,
    file: String,
    file_id: u32,
    ext: &ExtOps,
    metas: &MetaCtx,
) -> (rokc_ast::Program, Vec<RokDiagnostic>) {
    let lexer = Lexer::new(source, file.clone()).with_ext_ops(ext.symbols());
    let (mut tokens, mut diags) = lexer.lex_all();
    for t in &mut tokens {
        t.span.file = file_id;
    }
    // The lexer's own warnings (confusables) too.
    for d in &mut diags {
        if let Some(p) = d.primary.as_mut().filter(|p| p.span.file == 0) {
            p.span.file = file_id;
        }
    }
    apply_keywords(&mut tokens, &metas.keywords, &mut diags);
    let (program, mut parse_diags) = parse_program_meta(
        &tokens,
        file,
        ext,
        &metas.table,
        &metas.literals,
        Some(&metas.cfg),
    );
    diags.append(&mut parse_diags);
    (program, diags)
}

/// An item and the module path (`a::b`, `""` at the root) it is in.
type ModItem = (String, rokc_ast::Item);
type UseEntry = (String, rokc_core::Visibility, rokc_ast::UseTree);

/// One cached parse (`cached`): its key, the files it added, its
/// result.
type Cached<T> = std::sync::Mutex<Option<(String, Vec<(String, String)>, T)>>;
type LibParse = (
    Vec<ModItem>,
    Vec<(String, rokc_core::Visibility, rokc_ast::UseTree)>,
    Vec<RokDiagnostic>,
);
static PREPASS_CACHE: Cached<(PrecTable, Vec<RokDiagnostic>, PrePass)> =
    std::sync::Mutex::new(None);
static LIB_CACHE: Cached<LibParse> = std::sync::Mutex::new(None);

/// `parse(files)`, or (`on`) a copy of its last result when `key` and
/// the number of files before it are the same: its files are added
/// again, so they get the ids its spans have.
// One entry per parse; files are not rechecked on disk
// (`CompilerConfig::cache_library` is for a fixed library).
fn cached<T: Clone>(
    slot: &Cached<T>,
    on: bool,
    key: String,
    files: &mut SourceMap,
    parse: impl FnOnce(&mut SourceMap) -> T,
) -> T {
    if !on {
        return parse(files);
    }
    let key = format!("{}|{key}", files.len());
    let mut slot = slot
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some((k, added, v)) = slot.as_ref() {
        if *k == key {
            for (path, text) in added {
                files.add(path.clone(), text.clone());
            }
            return v.clone();
        }
    }
    let before = files.len();
    let v = parse(files);
    let added = files.files()[before..].to_vec();
    *slot = Some((key, added, v.clone()));
    v
}

/// What a package's parse needs from the pre-pass: every meta block,
/// and the package's own keywords (6.6.5) with their handler paths.
struct MetaCtx {
    table: std::sync::Arc<MetaTable>,
    keywords: KeywordTable,
    /// `#[literal]` patterns: the libraries', plus the package's own.
    literals: std::sync::Arc<LiteralTable>,
    /// `tables_key`, once asked for.
    key: std::sync::OnceLock<u64>,
    target: rokc_mir::Target,
    /// The package's cfg (`package_cfg`).
    cfg: CfgEnv,
}

impl MetaCtx {
    /// A key of what, besides its text, a file's parse in this package
    /// depends on: the extension operators, meta blocks, keywords,
    /// literals and cfg.
    fn tables_key(&self, ext: &ExtOps) -> u64 {
        *self.key.get_or_init(|| {
            let mut levels: Vec<String> = ext.levels.iter().map(|l| format!("{l:?}")).collect();
            levels.sort();
            incr::key(&[
                levels.join(";").as_bytes(),
                format!("{:?}", self.table).as_bytes(),
                format!("{:?}", self.keywords).as_bytes(),
                format!("{:?}", self.literals).as_bytes(),
                incr::target_key(&self.cfg, &self.target).as_bytes(),
            ])
        })
    }
}

/// Spec 6.6: per package (user first, then each library root), its
/// registered keywords and the handler's absolute path. A keyword
/// registered twice in a build is an error (6.6.4). A standard library
/// type keyword (`#[keyword("int")] struct Int`, stdlib 2.1) goes to
/// every package; only the standard library may register one.
fn keyword_tables(
    defs: Vec<KeywordDef>,
    entry: &Path,
    user_dir: &Path,
    roots: &[LibRoot],
    diags: &mut Vec<RokDiagnostic>,
) -> Vec<KeywordTable> {
    let pkgs = package_roots(user_dir, roots);
    let mut out = vec![Vec::new(); pkgs.len()];
    let mut seen: Vec<&KeywordDef> = Vec::new();
    for d in &defs {
        if let Some(e) = check_keyword(d) {
            diags.push(e);
            continue;
        }
        if let Some(old) = seen.iter().find(|o| o.name == d.name) {
            diags.push(
                RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Meta,
                    d.span,
                    format!("keyword `{}` is registered twice (spec 6.6.4)", d.name),
                )
                .with_secondary(old.span, "first registered here"),
            );
            continue;
        }
        seen.push(d);
        let Some((i, path)) = handler_path(&pkgs, entry, &d.file, &d.handler) else {
            continue;
        };
        if !d.ty {
            out[i].push((d.name.clone(), path, false));
        } else if path.first().is_some_and(|p| p == "rok") {
            for t in &mut out {
                t.push((d.name.clone(), path.clone(), true));
            }
        } else {
            diags.push(RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Meta,
                d.span,
                format!(
                    "`#[keyword(\"{}\")]` must be on a function — its handler (spec 6.6.2); \
                         only the standard library names a type with it",
                    d.name
                ),
            ));
        }
    }
    out
}

/// (package dir, path root) of the user package, then each library root.
fn package_roots(user_dir: &Path, roots: &[LibRoot]) -> Vec<(PathBuf, Vec<String>)> {
    let mut pkgs: Vec<(PathBuf, Vec<String>)> =
        vec![(user_dir.to_path_buf(), vec!["pkg".to_owned()])];
    for (prefix, r) in roots {
        let dir = r
            .parent()
            .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
        // A dependency's handlers live under `pkg::<dep>`.
        let path = if prefix.first().is_some_and(|p| p == "rok") {
            prefix.clone()
        } else {
            std::iter::once("pkg".to_owned())
                .chain(prefix.iter().cloned())
                .collect()
        };
        pkgs.push((dir, path));
    }
    pkgs
}

/// The package index and absolute path of `handler` defined in `file`:
/// the closest package directory owns the file; its path below that
/// directory is the module path (`a/b.rok` → `a::b`); the build's entry
/// file is its package's root module; `handler` may go through inline
/// `mod`s (`inner::f`).
fn handler_path(
    pkgs: &[(PathBuf, Vec<String>)],
    entry: &Path,
    file: &str,
    handler: &str,
) -> Option<(usize, Vec<String>)> {
    let file = Path::new(file);
    let (i, (dir, root)) = pkgs
        .iter()
        .enumerate()
        .filter(|(_, (dir, _))| file.starts_with(dir))
        .max_by_key(|(_, (dir, _))| dir.components().count())?;
    let mut path = root.clone();
    let rel = file.strip_prefix(dir).unwrap_or(file).with_extension("");
    let segs: Vec<String> = rel
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    if file != entry && !(segs.len() == 1 && (segs[0] == "lib" || segs[0] == "main")) {
        path.extend(segs);
    }
    path.extend(handler.split("::").map(str::to_owned));
    Some((i, path))
}

/// Spec 6.5: the `#[literal]` patterns the parser matches — the
/// libraries' (seen by every package) and the user package's own (seen
/// by it only). The built-in shapes are dispatched by HIR instead, and
/// an invalid pattern is reported by the real parse.
fn literal_tables(
    defs: Vec<LiteralDef>,
    entry: &Path,
    user_dir: &Path,
    roots: &[LibRoot],
    ext: &ExtOps,
    diags: &mut Vec<RokDiagnostic>,
) -> (std::sync::Arc<LiteralTable>, std::sync::Arc<LiteralTable>) {
    let pkgs = package_roots(user_dir, roots);
    let (mut lib, mut user) = (LiteralTable::default(), LiteralTable::default());
    for d in defs {
        if d.handler.is_empty() {
            diags.push(RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Meta,
                d.span,
                "`#[literal(..)]` must be on a function — its handler (spec 6.5.2)",
            ));
            continue;
        }
        let Ok(pattern) = parse_pattern(&d.tokens, &ext.symbols()) else {
            continue;
        };
        let Ok(kind) = pattern.kind() else { continue };
        if matches!(kind, PatKind::Shape(_)) {
            continue;
        }
        let Some((i, handler)) = handler_path(&pkgs, entry, &d.file, &d.handler) else {
            continue;
        };
        let rule = LitRule {
            pattern,
            kind,
            handler,
            span: d.span,
        };
        if i == 0 { &mut user } else { &mut lib }.rules.push(rule);
    }
    user.rules.extend(lib.rules.iter().cloned());
    (std::sync::Arc::new(lib), std::sync::Arc::new(user))
}

/// Walk a package's module tree starting from `body_path`. Inline
/// `mod foo { ... }` extends the module path; file-mapped `mod foo;`
/// recurses into `foo.rok` with the same extension.
///
/// Items are flattened into one list of (module path, item), names as
/// written (HIR qualifies them).
#[allow(clippy::too_many_arguments)] // recursive walker threading accumulators; a context struct buys nothing
fn collect_module_tree(
    body_path: &Path,
    preloaded: Option<&str>,
    submodule_dir: Option<&Path>,
    module_path: &[String],
    ext: &ExtOps,
    metas: &MetaCtx,
    diags: &mut Vec<RokDiagnostic>,
    out: &mut Vec<ModItem>,
    uses: &mut Vec<(String, rokc_core::Visibility, rokc_ast::UseTree)>,
    mut keep: Option<&mut Vec<SourceFile>>,
    files: &mut SourceMap,
) -> Vec<rokc_ast::Stmt> {
    let parsed = match PARSED.with(|p| p.borrow_mut().remove(body_path)) {
        Some(p) => p,
        // A file the pre-pass did not see (its result was cached).
        None => {
            let read = preloaded.map_or_else(|| read_source(body_path), |s| Ok(s.to_owned()));
            let source = match read {
                Ok(s) => s,
                Err(e) => {
                    diags.push(RokDiagnostic::error(
                        rokc_diagnostic::ErrorKind::Module,
                        rokc_diagnostic::Span::DUMMY,
                        format!("cannot read module file {}: {e}", body_path.display()),
                    ));
                    return Vec::new();
                }
            };
            let file = body_path.display().to_string();
            // Every span parsed from here on knows its file (diagnostic locations).
            let file_id = files.add(file.clone(), source.clone());
            let (program, d) = parse_file(&source, file, file_id, ext, metas);
            let keeping = keep.is_some();
            settle(body_path, file_id, program, d, metas, keeping)
        }
    };
    let Parsed {
        items,
        stmts,
        no_implicit,
        kept,
        diags: mut file_diags,
        ..
    } = parsed;
    if no_implicit {
        NO_IMPLICIT.with(|n| n.borrow_mut().push(module_path.join("::")));
    }
    diags.append(&mut file_diags);
    if let (Some(keep), Some(mut f)) = (keep.as_deref_mut(), kept) {
        f.module = module_path.to_vec();
        keep.push(f);
    }

    // `#[cfg(...)]`-gated items are gone: excluded modules get no files
    // resolved and no inline items flattened.
    flatten_module_items(
        items,
        module_path,
        submodule_dir,
        ext,
        metas,
        diags,
        out,
        uses,
        keep,
        files,
    );
    stmts
}

#[allow(clippy::too_many_arguments)] // mutually recursive with `collect_module_tree`, same accumulators
fn flatten_module_items(
    items: Vec<rokc_ast::Item>,
    module_path: &[String],
    submodule_dir: Option<&Path>,
    ext: &ExtOps,
    metas: &MetaCtx,
    diags: &mut Vec<RokDiagnostic>,
    out: &mut Vec<ModItem>,
    uses: &mut Vec<(String, rokc_core::Visibility, rokc_ast::UseTree)>,
    mut keep: Option<&mut Vec<SourceFile>>,
    files: &mut SourceMap,
) {
    let module_key = module_path.join("::");
    let mut mods: Vec<String> = Vec::new();
    for item in items {
        match item {
            rokc_ast::Item::Use(u) => {
                uses.push((module_key.clone(), u.vis, u.tree));
            }
            rokc_ast::Item::Mod(m) => {
                let err = |msg: String| {
                    RokDiagnostic::error(rokc_diagnostic::ErrorKind::Module, m.span, msg)
                };
                if mods.contains(&m.name) {
                    diags.push(err(format!(
                        "module `{}` is declared twice in the same module (spec 5.4.12)",
                        m.name
                    )));
                    continue;
                }
                mods.push(m.name.clone());
                // 5.4.5: an inline module has no file or folder of its name.
                if let (Some(_), Some(dir)) = (&m.items, submodule_dir) {
                    let file = dir.join(format!("{}.rok", m.name));
                    let folder = dir.join(&m.name);
                    if let Some(p) = [file, folder].into_iter().find(|p| {
                        if p.extension().is_some() {
                            source_exists(p)
                        } else {
                            source_dir_exists(p)
                        }
                    }) {
                        diags.push(err(format!(
                            "inline module `{}` conflicts with `{}`: a module is either \
                             inline or a file (spec 5.4.5)",
                            m.name,
                            p.file_name().unwrap_or_default().to_string_lossy()
                        )));
                        continue;
                    }
                }
                let mut child_path = module_path.to_vec();
                child_path.push(m.name.clone());
                // An empty stub keeps the module's visibility for HIR
                // (spec 5.6.13).
                out.push((
                    module_key.clone(),
                    rokc_ast::Item::Mod(rokc_ast::ModDef {
                        vis: m.vis,
                        attrs: Vec::new(),
                        name: m.name.clone(),
                        items: Some(Vec::new()),
                        span: m.span,
                    }),
                ));
                if let Some(inner) = m.items {
                    flatten_module_items(
                        inner,
                        &child_path,
                        submodule_dir,
                        ext,
                        metas,
                        diags,
                        out,
                        uses,
                        keep.as_deref_mut(),
                        files,
                    );
                } else {
                    let (body, next_dir) = match mod_file(&m, submodule_dir) {
                        Ok(f) => f,
                        Err(e) => {
                            diags.push(e);
                            continue;
                        }
                    };
                    let stray = collect_module_tree(
                        &body,
                        None,
                        next_dir.as_deref(),
                        &child_path,
                        ext,
                        metas,
                        diags,
                        out,
                        uses,
                        keep.as_deref_mut(),
                        files,
                    );
                    if !stray.is_empty() {
                        diags.push(entry::stmts_outside_entry(&body));
                    }
                }
            }
            other => out.push((module_key.clone(), other)),
        }
    }
}

/// `#[link("z")]` / `#[link(name = "z", kind = "static")]` on the
/// `extern` blocks of `items` (spec 6.2.3).
fn native_libs(items: &[rokc_ast::Item], out: &mut Vec<(String, bool)>) {
    use rokc_ast::{AttrArg, AttrBody, Item, Literal};
    for item in items {
        match item {
            Item::Mod(m) => native_libs(m.items.as_deref().unwrap_or_default(), out),
            Item::Extern(b) => {
                for a in b.attrs.iter().filter(|a| a.path == ["link"]) {
                    let AttrBody::Args(args) = &a.body else {
                        continue;
                    };
                    let mut name = None;
                    let mut stat = false;
                    for arg in args {
                        match arg {
                            AttrArg::Lit(Literal::Str(n)) => name = Some(n.clone()),
                            AttrArg::KeyValue(k, Literal::Str(v)) if k == "name" => {
                                name = Some(v.clone());
                            }
                            AttrArg::KeyValue(k, Literal::Str(v)) if k == "kind" => {
                                stat = v == "static";
                            }
                            _ => {}
                        }
                    }
                    if let Some(n) = name.filter(|n| !out.iter().any(|(m, _)| m == n)) {
                        out.push((n, stat));
                    }
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn package_hash_known_answer() {
        // python3: sha256(b"lib.rok\0pub mod m;\n\0m.rok\0fn f() {}\n\0")
        let mut files = vec![
            ("m.rok".to_owned(), "fn f() {}\n"),
            ("lib.rok".to_owned(), "pub mod m;\n"),
        ];
        assert_eq!(super::hash_package(&mut files), "b0cf4718");
    }

    /// Compile `src` as an anonymous program for `triple` with the core
    /// library.
    fn compile(src: &str, triple: &str) -> super::CompiledModule {
        let core =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../library/core/lib.rok");
        let config = super::CompilerConfig {
            bootstrap_files: vec![core],
            anonymous: true,
            target: super::Target::builtin(triple),
            ..super::CompilerConfig::default()
        };
        let path = std::env::temp_dir().join("rokc_driver_test_main.rok");
        let mut files = super::SourceMap::new();
        let p = super::compile_source(src, &path, &config, &mut files).unwrap_or_else(|d| {
            panic!(
                "{}",
                d.iter()
                    .map(|d| files.line(d))
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        });
        p.modules.into_iter().next().expect("one module")
    }

    #[test]
    fn cfg_follows_the_target() {
        let src = "#[cfg(target_pointer_width = \"32\")]\nfn narrow() {}\n\
                   #[cfg(target_os = \"windows\")]\nfn win() {}\nfn main() {}\n";
        let has = |m: &super::CompiledModule, n: &str| m.hir.functions.iter().any(|f| f.name == n);
        let i686 = compile(src, "i686-pc-windows-msvc");
        assert!(has(&i686, "narrow") && has(&i686, "win"));
        let x64 = compile(src, "x86_64-unknown-linux-gnu");
        assert!(!has(&x64, "narrow") && !has(&x64, "win"));
    }

    /// `usize` literals and constants are checked at the target's width.
    #[test]
    fn usize_range_follows_the_pointer_width() {
        let src = "const BIG: usize = 4294967295 + 1;\nfn main() { let n = BIG; }\n";
        let core =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../library/core/lib.rok");
        let errs = |triple: &str| {
            let config = super::CompilerConfig {
                bootstrap_files: vec![core.clone()],
                anonymous: true,
                target: super::Target::builtin(triple),
                ..super::CompilerConfig::default()
            };
            let path = std::env::temp_dir().join("rokc_driver_test_usize.rok");
            let mut files = super::SourceMap::new();
            super::compile_source(src, &path, &config, &mut files)
                .err()
                .map(|d| d.iter().map(|d| files.line(d)).collect::<String>())
        };
        assert!(errs("x86_64-unknown-linux-gnu").is_none());
        let e = errs("i686-unknown-linux-gnu").expect("an overflow on 32-bit");
        assert!(e.contains("overflow"), "{e}");
        assert!(
            compile(
                "fn main() { let n: usize = 4294967295; }\n",
                "armv7-unknown-linux-gnueabihf"
            )
            .hir
            .functions
            .iter()
            .any(|f| f.name == "main")
        );
    }

    #[test]
    fn any_payload_boxing_follows_the_pointer_width() {
        // An `i64` fits the payload word on a 64-bit target, not on a
        // 32-bit one: there the tag carries `ANY_BOXED`.
        let src = "fn main() { let v: any = 5i64; }\n";
        let boxed = |m: &super::CompiledModule| {
            m.mir
                .functions
                .iter()
                .flat_map(|f| &f.blocks)
                .flat_map(|b| &b.stmts)
                .any(|s| {
                    matches!(s, rokc_mir::Statement::Assign {
                    rvalue: rokc_mir::RValue::StructInit { fields, .. }, ..
                } if matches!(fields.first(), Some(rokc_mir::Operand::Const(
                    rokc_ir_common::ConstVal::Int { value, .. })) if *value < 0))
                })
        };
        assert!(boxed(&compile(src, "i686-unknown-linux-gnu")));
        assert!(!boxed(&compile(src, "x86_64-unknown-linux-gnu")));
    }

    #[test]
    fn extern_c_is_the_c_abi_whatever_the_name() {
        // A user's `extern "C"` function gets the C ABI even when its name
        // starts with `rok_`; `extern "rok"` is the runtime's.
        let src = "extern \"C\" { fn rok_probe_c(f: fn(i32) -> i32) -> i32; }\n\
                   extern \"rok\" { fn rok_probe_rok(s: str) -> i32; }\n\
                   fn twice(x: i32) -> i32 { x * 2 }\n\
                   fn main() { unsafe { rok_probe_c(twice); rok_probe_rok(\"y\"); } }\n";
        let m = compile(src, "x86_64-unknown-linux-gnu");
        let text = super::mlir_text(
            &m,
            &super::SourceMap::new(),
            &super::BuildOptions::default(),
        )
        .expect("codegen")
        .text;
        assert!(
            text.contains("func.func private @rok_probe_c(%arg0: !llvm.ptr) -> i32"),
            "{text}"
        );
        assert!(
            text.contains("func.func private @rok_probe_rok(!llvm.struct<(ptr, i64)>) -> i32"),
            "{text}"
        );
    }
}

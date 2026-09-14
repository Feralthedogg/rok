//! The compiler as a library: sessions, package discovery, prebuilt
//! dependencies and incremental-build records, for the `rokc` binary and
//! its embedded tools (REPL, Jupyter, LSP).

mod deps;
mod fresh;
mod package;
mod std_cache;

use std::path::{Path, PathBuf};

pub use deps::DepBuild;
pub use fresh::Fingerprint;
pub use package::{Package, STDIN, discover, source_files};
pub use std_cache::{StdKey, prebuilt_std};

use rokc_driver::{CompiledModule, CompilerConfig, compile_file, compile_source};

pub use rokc_diagnostic::{
    ErrorKind, Json, RokDiagnostic, clear_files, print_rendered, render, report, set_report_style,
};
pub use rokc_driver::{
    BuildOptions, Demangled, EmitKind, ReplCell, ReplFn, SourceFile, TempDir, demangle,
    find_mlir_plugin, link_host, rhir,
};

#[derive(Default)]
pub struct Session {
    config: CompilerConfig,
}

impl Session {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a `.rok` file to the bootstrap pre-pass that populates the
    /// operator precedence table. Order matters only for diagnostic
    /// determinism — registrations are merged with conflict detection.
    pub fn add_bootstrap_file(&mut self, path: PathBuf) {
        self.config.bootstrap_files.push(path);
    }

    /// A dependency package (`--extern name=root`, spec 902.3): its
    /// `lib.rok` is compiled with this build and mounted at `name`.
    pub fn add_extern(&mut self, name: String, root: PathBuf) {
        self.config.externs.push((name, root));
    }

    /// Add a `--cfg` flag (either `"flag"` or `"key=value"`). Consulted
    /// by the `#[cfg(...)]` filter pass before HIR.
    pub fn add_cfg(&mut self, flag: String) {
        self.config.cfg_flags.push(flag);
    }

    /// `rokc test` build: keep `#[test]` functions, generate the runner
    /// `main`, set `cfg(test)`.
    pub const fn set_test(&mut self, on: bool) {
        self.config.test = on;
    }

    /// `rokc bench` build: keep `#[bench]` functions, generate the
    /// timing `main`, set `cfg(test)`.
    pub const fn set_bench(&mut self, on: bool) {
        self.config.bench = on;
    }

    /// Keep each parsed file's AST in `CompileResult::sources` (lint,
    /// doc).
    pub const fn set_keep_ast(&mut self, on: bool) {
        self.config.keep_ast = on;
    }

    /// Build the library package as prebuilt dependency `name`
    /// (`archive` then also writes `<name>.rhir`, spec 904).
    pub fn set_lib_name(&mut self, name: Option<String>) {
        self.config.lib_name = name;
    }

    /// The input is a lone file outside any package (spec 4.16.8).
    pub const fn set_anonymous(&mut self, on: bool) {
        self.config.anonymous = on;
    }

    /// Compile for LLVM target `triple` (`--target`); `None` is the host.
    pub fn set_target(&mut self, triple: Option<&str>) {
        self.config.target = rokc_driver::Target::new(triple);
    }

    /// Keep the library's parse across compiles (a long-lived session
    /// over a library that does not change: the REPL).
    pub const fn set_cache_library(&mut self, on: bool) {
        self.config.cache_library = on;
    }

    /// Build the bootstrap tiers as the prebuilt library `rok`.
    pub const fn set_std_lib(&mut self, on: bool) {
        self.config.std_lib = on;
    }

    /// Link the bootstrap tiers prebuilt (`rok.rhir`, `prebuilt_std`).
    pub fn set_std_prebuilt(&mut self, rhir: Option<PathBuf>) {
        self.config.std_prebuilt = rhir;
    }

    /// Lower (and so check) every library body, reached or not.
    pub const fn set_check_library(&mut self, on: bool) {
        self.config.check_library = on;
    }

    pub fn compile_file(&self, path: &Path) -> CompileResult {
        Self::result(compile_file(path, &self.config))
    }

    /// `compile_file` with the root file's text given (stdin, an editor
    /// buffer, a REPL session); `path` still locates `mod foo;` files.
    pub fn compile_source(&self, source: &str, path: &Path) -> CompileResult {
        Self::result(compile_source(source, path, &self.config))
    }

    fn result(r: Result<rokc_driver::CompiledProject, Vec<RokDiagnostic>>) -> CompileResult {
        match r {
            Ok(p) => CompileResult {
                modules: p.modules,
                errors: Vec::new(),
                warnings: p.warnings,
                tests: p.tests,
                sources: p.sources,
            },
            Err(errors) => CompileResult {
                modules: Vec::new(),
                errors,
                warnings: Vec::new(),
                tests: Vec::new(),
                sources: Vec::new(),
            },
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct CompileResult {
    pub modules: Vec<CompiledModule>,
    pub errors: Vec<RokDiagnostic>,
    pub warnings: Vec<RokDiagnostic>,
    /// Test names of a `set_test` build (bench names of `set_bench`).
    pub tests: Vec<String>,
    /// Parsed files of a `set_keep_ast` build (user package first).
    pub sources: Vec<SourceFile>,
}

impl CompileResult {
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn report_errors(&self) {
        for d in &self.errors {
            report(d);
        }
    }

    fn module(&self) -> Result<&CompiledModule, RokDiagnostic> {
        self.modules
            .first()
            .ok_or_else(|| RokDiagnostic::error(ErrorKind::Internal, "no module produced"))
    }

    /// One intermediate artifact (`--emit=<kind>`).
    pub fn emit(&self, kind: EmitKind, opts: &BuildOptions) -> Result<Vec<u8>, RokDiagnostic> {
        if kind == EmitKind::Expanded {
            // The user package's files (a `set_keep_ast` build).
            let text: Vec<&str> = self
                .sources
                .iter()
                .filter(|s| s.package.is_empty())
                .flat_map(|s| &s.expanded)
                .map(String::as_str)
                .collect();
            return Ok(text.join("\n").into_bytes());
        }
        if kind == EmitKind::Ast && !self.sources.is_empty() {
            return Ok(self.ast_source().into_bytes());
        }
        rokc_driver::emit(self.module()?, kind, opts)
    }

    /// Codegen for its errors alone (`check`), without the toolchain.
    pub fn check_codegen(&self, opts: &BuildOptions) -> Result<(), RokDiagnostic> {
        rokc_driver::check_codegen(self.module()?, opts)
    }

    /// The user package's files (of a `set_keep_ast` build) after meta
    /// expansion, as rok source, each under a `// <file> (<module>)`
    /// line (`--emit=ast`).
    #[must_use]
    pub fn ast_source(&self) -> String {
        let mut out = String::new();
        for f in self.sources.iter().filter(|f| f.package.is_empty()) {
            let module = if f.module.is_empty() {
                "pkg".to_owned()
            } else {
                f.module.join("::")
            };
            out.push_str(&format!("// {} ({module})\n", f.path.display()));
            out.push_str(&rokc_ast::print::print_file(&f.attrs, &f.items, &f.stmts));
            out.push('\n');
        }
        out
    }

    /// Lower MIR again after editing `modules[0].hir`.
    pub fn relower(&mut self) {
        if let Some(m) = self.modules.first_mut() {
            rokc_driver::relower(m);
        }
    }

    /// Build an executable at `out` through mlir-opt / mlir-translate / clang.
    pub fn link(&self, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
        rokc_driver::link_executable(self.module()?, opts, out)
    }

    /// A REPL cell (`opts.repl`) as LLVM IR text for the session host's
    /// JIT, and what codegen says about it (GC tables, new symbols).
    pub fn cell_ir(
        &self,
        opts: &BuildOptions,
    ) -> Result<(Vec<u8>, rokc_driver::MlirOutput), RokDiagnostic> {
        rokc_driver::cell_ir(self.module()?, opts)
    }

    /// A REPL cell for the session host: a native object when the host
    /// runs those (`native::jit`), else LLVM IR (`cell_ir`).
    pub fn cell_code(
        &self,
        opts: &BuildOptions,
    ) -> Result<(Vec<u8>, rokc_driver::MlirOutput), RokDiagnostic> {
        if rokc_driver::native::jit(opts) {
            rokc_driver::native::cell_object(self.module()?, opts)
        } else {
            self.cell_ir(opts)
        }
    }

    /// Build a library package's static archive at `out` (spec 902.13).
    pub fn archive(&self, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
        rokc_driver::build_archive(self.module()?, opts, out)
    }
}

/// The standard library and the runtime of this `rokc` (spec 9.2.19).
///
/// They are under its sysroot (the executable's `..`: `lib/rok/{core,std,bare}/`,
/// `lib/librokr.a`), else, for a build in the repository, its
/// `library/` and the `librokr.a` cargo puts beside `rokc`. `ROK_HOME`
/// plays no part. Each `Err` lists where it looked.
pub struct Sysroot {
    /// The library roots to preload (`core`, then `std` / `bare`).
    pub libs: Result<Vec<PathBuf>, String>,
    pub rokr: Result<PathBuf, String>,
}

/// The sysroot's library directory.
pub const SYSROOT_LIBS: &str = "lib/rok";
const SYSROOT_RT: &str = "lib/librokr.a";
/// The repository's `library/` (a dev build).
const DEV_LIBS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../library");

#[must_use]
pub fn sysroot() -> Sysroot {
    let exe = std::env::current_exe().unwrap_or_default();
    let exe = std::fs::canonicalize(&exe).unwrap_or(exe);
    let bin = exe.parent().unwrap_or_else(|| Path::new("."));
    let root = bin.parent().unwrap_or(bin);
    let dev = Path::new(DEV_LIBS);
    let dev = std::fs::canonicalize(dev).unwrap_or_else(|_| dev.to_path_buf());
    let lib_dirs = [root.join(SYSROOT_LIBS), dev];
    let libs = lib_dirs
        .iter()
        .find(|d| d.join("core/lib.rok").is_file())
        .map(|d| bootstrap_roots(d))
        .ok_or_else(|| {
            format!(
                "the standard library is missing: no {} (the sysroot of {}) nor {} (a build in \
                 the repository); reinstall the toolchain, or pass --bootstrap <core/lib.rok>",
                lib_dirs[0].join("core/lib.rok").display(),
                exe.display(),
                lib_dirs[1].join("core/lib.rok").display(),
            )
        });
    let rt = [root.join(SYSROOT_RT), bin.join("librokr.a")];
    let rokr = rt.iter().find(|p| p.is_file()).cloned().ok_or_else(|| {
        format!(
            "the runtime library is missing: no {} (the sysroot of {}) nor {} (a build in the \
             repository: `cargo build -p rokr`); reinstall the toolchain, or pass --rokr <lib>",
            rt[0].display(),
            exe.display(),
            rt[1].display(),
        )
    });
    Sysroot { libs, rokr }
}

/// The library roots to preload from a library directory: `core/lib.rok`,
/// then `std` / `bare` when present (no implicit glob: user code names
/// them).
fn bootstrap_roots(libs: &Path) -> Vec<PathBuf> {
    let mut out = vec![libs.join("core/lib.rok")];
    out.extend(
        ["std", "bare"]
            .iter()
            .map(|tier| libs.join(tier).join("lib.rok"))
            .filter(|p| p.is_file()),
    );
    out
}

//! The compiler as a library: sessions, package discovery, prebuilt
//! dependencies and incremental-build records, for the `rokc` binary and
//! its embedded tools (REPL, Jupyter, LSP).

mod deps;
mod fresh;
mod package;

use std::path::{Path, PathBuf};

pub use deps::DepBuild;
pub use fresh::Fingerprint;
pub use package::{Package, STDIN, discover, source_files};

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

    /// Build a library package's static archive at `out` (spec 902.13).
    pub fn archive(&self, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
        rokc_driver::build_archive(self.module()?, opts, out)
    }
}

/// Installed layout: `$ROK_HOME/bin/rokc`, `$ROK_HOME/lib/librokr.a`,
/// `$ROK_HOME/lib/rok/{core,std,bare}/`.
pub const INSTALLED_LIBS: &str = "lib/rok";
const INSTALLED_RT: &str = "lib/librokr.a";
/// Dev layout: the repository's `library/` above `target/<profile>/rokc`,
/// with `librokr.a` next to `rokc`.
const DEV_LIBS: &str = "library";

/// `(bootstrap roots, librokr.a)`: the install at `ROK_HOME`, else the dev
/// layout around the running executable.
#[must_use]
pub fn toolchain() -> (Option<Vec<PathBuf>>, Option<PathBuf>) {
    let file = |p: PathBuf| p.is_file().then_some(p);
    let libs_in = |d: &Path, rel: &str| {
        let libs = d.join(rel);
        libs.join("core/lib.rok").is_file().then_some(libs)
    };
    let exe_dir = std::env::current_exe()
        .ok()
        .and_then(|e| e.parent().map(Path::to_path_buf));
    let home = rokc_core::rok_home();
    let installed = home.as_deref().and_then(|h| libs_in(h, INSTALLED_LIBS));
    let (libs, rokr) = if installed.is_some() {
        (installed, home.and_then(|h| file(h.join(INSTALLED_RT))))
    } else {
        let dev = home
            .as_deref()
            .and_then(|h| libs_in(h, DEV_LIBS))
            .or_else(|| {
                exe_dir
                    .as_deref()?
                    .ancestors()
                    .find_map(|d| libs_in(d, DEV_LIBS))
            });
        (dev, exe_dir.and_then(|d| file(d.join("librokr.a"))))
    };
    (libs.as_deref().map(bootstrap_roots), rokr)
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

//! Thin façade over the driver. Used by the `rokc` binary and any
//! embedder that wants a simple session API (REPL, Jupyter, LSP).

use std::path::{Path, PathBuf};

use rokc_driver::{CompiledModule, CompilerConfig, compile_file, compile_source};

pub use rokc_diagnostic::{ErrorKind, RokDiagnostic, report, set_report_style};
pub use rokc_driver::{
    BuildOptions, Demangled, EmitKind, ReplCell, SourceFile, TempDir, demangle, link_host, rhir,
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

    /// Keep the library's parse across compiles (a long-lived session
    /// over a library that does not change: the REPL).
    pub const fn set_cache_library(&mut self, on: bool) {
        self.config.cache_library = on;
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
                link_libraries: p.link_libraries,
                tests: p.tests,
                sources: p.sources,
            },
            Err(errors) => CompileResult {
                modules: Vec::new(),
                errors,
                warnings: Vec::new(),
                link_libraries: Vec::new(),
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
    pub link_libraries: Vec<String>,
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
        rokc_driver::emit(self.module()?, kind, opts)
    }

    /// Lower MIR again after editing `modules[0].hir`.
    pub fn relower(&mut self) {
        if let Some(m) = self.modules.first_mut() {
            rokc_driver::relower(m);
        }
    }

    /// Build an executable at `out` through mlir-opt / mlir-translate / clang.
    pub fn link(&self, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
        rokc_driver::link_executable(self.module()?, &self.link_libraries, opts, out)
    }

    /// Build a REPL cell (`opts.repl`) as a shared library at `out`;
    /// the GC type ids it used.
    pub fn link_shared(&self, opts: &BuildOptions, out: &Path) -> Result<u32, RokDiagnostic> {
        rokc_driver::link_shared(self.module()?, &self.link_libraries, opts, out)
    }

    /// Build a REPL cell (`opts.repl`) as a relocatable object at `out`
    /// (the session host loads it itself); the GC type ids it used.
    pub fn compile_object(&self, opts: &BuildOptions, out: &Path) -> Result<u32, RokDiagnostic> {
        rokc_driver::compile_object(self.module()?, opts, out)
    }

    /// Build a library package's static archive at `out` (spec 902.13).
    pub fn archive(&self, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
        rokc_driver::build_archive(self.module()?, opts, out)
    }
}

/// Installed layout (E6): `$ROK_HOME/bin/rokc`, `$ROK_HOME/lib/librokr.a`,
/// `$ROK_HOME/lib/rok/{core,std,bare}/`.
pub const INSTALLED_LIBS: &str = "lib/rok";
const INSTALLED_RT: &str = "lib/librokr.a";
/// Dev layout: the repository's `library/` above `target/<profile>/rokc`,
/// with `librokr.a` next to `rokc`.
const DEV_LIBS: &str = "library";

/// `(library root holding core/ std/ bare/, librokr.a)`. `ROK_HOME`
/// defaults to the parent of the directory holding `rokc` (`bin/..`);
/// when that is not an install, fall back to the dev layout.
pub fn locate(exe_dir: Option<&Path>) -> (Option<PathBuf>, Option<PathBuf>) {
    let file = |p: PathBuf| p.is_file().then_some(p);
    let libs_in = |d: &Path, rel: &str| {
        let libs = d.join(rel);
        libs.join("core/lib.rok").is_file().then_some(libs)
    };
    let env_home = std::env::var_os("ROK_HOME").map(PathBuf::from);
    let home = env_home
        .clone()
        .or_else(|| exe_dir.and_then(Path::parent).map(Path::to_path_buf));
    if let Some(h) = home {
        if let Some(libs) = libs_in(&h, INSTALLED_LIBS) {
            return (Some(libs), file(h.join(INSTALLED_RT)));
        }
    }
    let dev = env_home
        .and_then(|h| libs_in(&h, DEV_LIBS))
        .or_else(|| exe_dir?.ancestors().find_map(|d| libs_in(d, DEV_LIBS)));
    (dev, exe_dir.and_then(|d| file(d.join("librokr.a"))))
}

/// The library roots to preload from a `locate` library directory:
/// `core/lib.rok`, then `std` / `bare` when present (no implicit glob:
/// user code names them).
pub fn bootstrap_roots(libs: &Path) -> Vec<PathBuf> {
    let mut out = vec![libs.join("core/lib.rok")];
    out.extend(
        ["std", "bare"]
            .iter()
            .map(|tier| libs.join(tier).join("lib.rok"))
            .filter(|p| p.is_file()),
    );
    out
}

/// `(bootstrap roots, librokr.a)` for the running executable (`locate`
/// from its directory + `bootstrap_roots`).
pub fn toolchain() -> (Option<Vec<PathBuf>>, Option<PathBuf>) {
    let exe_dir = std::env::current_exe()
        .ok()
        .and_then(|e| e.parent().map(Path::to_path_buf));
    let (libs, rokr) = locate(exe_dir.as_deref());
    (libs.as_deref().map(bootstrap_roots), rokr)
}

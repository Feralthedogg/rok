//! Thin façade over the driver. Used by the `rokc` binary and any
//! embedder that wants a simple session API (REPL, Jupyter, LSP).

use std::path::{Path, PathBuf};

use rokc_driver::{CompilerConfig, CompiledModule, compile_file};

pub use rokc_diagnostic::{ErrorKind, RokDiagnostic, report};
pub use rokc_driver::{BuildOptions, EmitKind, TempDir};

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

    /// Add a `--cfg` flag (either `"flag"` or `"key=value"`). Consulted
    /// by the `#[cfg(...)]` filter pass before HIR.
    pub fn add_cfg(&mut self, flag: String) {
        self.config.cfg_flags.push(flag);
    }

    pub fn compile_file(&self, path: &Path) -> CompileResult {
        match compile_file(path, &self.config) {
            Ok(p) => CompileResult {
                modules: p.modules,
                errors: Vec::new(),
                warnings: p.warnings,
                link_libraries: p.link_libraries,
            },
            Err(errors) => CompileResult {
                modules: Vec::new(),
                errors,
                warnings: Vec::new(),
                link_libraries: Vec::new(),
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

    /// Build an executable at `out` through mlir-opt / mlir-translate / clang.
    pub fn link(&self, opts: &BuildOptions, out: &Path) -> Result<(), RokDiagnostic> {
        rokc_driver::link_executable(self.module()?, &self.link_libraries, opts, out)
    }
}

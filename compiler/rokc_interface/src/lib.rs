//! Thin façade over the driver. Used by the `rokc` binary and any
//! embedder that wants a simple session API (REPL, Jupyter, LSP).

use std::path::{Path, PathBuf};

use rokc_diagnostic::{RokDiagnostic, report};
use rokc_driver::{CompilerConfig, CompiledModule, compile_file};

pub use rokc_driver::LibGlob;

#[derive(Default)]
pub struct Session {
    config: CompilerConfig,
}

impl Session {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_lib(&mut self, path: PathBuf, glob: LibGlob) {
        self.config.libs.push((path, glob));
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
}

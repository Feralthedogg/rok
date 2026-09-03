//! Name resolution and visibility checks. Builds the `DefTable`,
//! resolves `use` paths to file paths, and detects circular imports.
//!
//! Skeleton only.

use rokc_ast::Program;
use rokc_core::DefTable;
use rokc_diagnostic::RokDiagnostic;

pub struct Resolver {
    pub defs: DefTable,
    pub diagnostics: Vec<RokDiagnostic>,
}

impl Default for Resolver {
    fn default() -> Self {
        Self::new()
    }
}

impl Resolver {
    #[must_use]
    pub fn new() -> Self {
        Self {
            defs: DefTable::new(),
            diagnostics: Vec::new(),
        }
    }

    pub fn resolve(&mut self, _program: &Program) {
        // TODO: walk the program, intern items, and resolve `use` paths.
    }
}

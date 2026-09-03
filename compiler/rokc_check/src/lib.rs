//! Type / scope / visibility checking. Skeleton.

use rokc_ast::Program;
use rokc_diagnostic::RokDiagnostic;

#[derive(Default)]
pub struct Checker {
    pub diagnostics: Vec<RokDiagnostic>,
}

impl Checker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            diagnostics: Vec::new(),
        }
    }

    pub fn check(&mut self, _program: &Program) {
        // TODO: scope checks, type inference, exhaustiveness, await/yield context.
    }
}

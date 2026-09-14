//! MIR → MLIR text in upstream dialects (`func`, `arith`, `cf`, `llvm`;
//! user `__mlir_op` regions may bring more). The MLIR passes, the translation
//! to LLVM IR and the code generation follow (`rokc_llvm`).

pub mod abi;
mod compact;
mod debug;
pub mod emit;
pub mod mangle;
mod repl;

pub use mangle::{Demangled, demangle, pkg_hash};
pub use repl::ReplFn;

use rokc_diagnostic::{ErrorKind, RokDiagnostic};
use rokc_mir::MirModule;

#[derive(Clone, Debug, Default)]
pub struct MlirOutput {
    pub text: String,
    /// Number of GC type ids used.
    pub gc_types: u32,
    /// A REPL cell: every `ScanTable` of the session so far (the next
    /// cell's `ReplCell::gc_tables`).
    pub gc_tables: Vec<Vec<u32>>,
    /// A REPL cell: the exported symbols it defines anew (`repl::reuse`).
    pub fresh: Vec<String>,
    /// A REPL cell: the functions it defines anew.
    pub fns: Vec<ReplFn>,
    /// A REPL cell: how many functions it takes from earlier cells.
    pub reused: usize,
}

/// One REPL cell (`rokc repl`).
///
/// Code the session host links into a process whose runtime is
/// already up. Instead of a C `main`,
/// `rok_repl_cell()` registers the cell's GC types and roots and runs
/// the user `main`.
#[derive(Clone, Debug, Default)]
pub struct ReplCell {
    /// The `ScanTable`s earlier cells registered (type id
    /// `USER_TYPE_BASE + i`): the same type keeps its id, new ones follow.
    pub gc_tables: Vec<Vec<u32>>,
    /// Functions the session has (symbol → text hash, `repl::reuse`):
    /// declared, not defined, when this cell's text is the same.
    pub known: std::collections::HashMap<String, u64>,
    /// `extern` statics this cell defines (zeroed, exported, GC roots):
    /// the slots of the session's new bindings.
    pub define: Vec<String>,
    /// Statics (MIR names) an earlier cell defined: declared, not
    /// defined, so their state carries over.
    pub statics: Vec<String>,
}

/// How to generate code for a module (its target is `MirModule::target`).
#[derive(Clone, Debug, Default)]
pub struct CodegenOptions {
    /// Panic on integer overflow (debug builds).
    pub overflow_checks: bool,
    /// `-g`: DWARF debug info (spec 9.9.6).
    pub debug: bool,
    /// Generate a REPL cell instead of a program.
    pub repl: Option<ReplCell>,
    /// LLVM `target datalayout` (the toolchain's), so MLIR folds `sizeof`
    /// idioms with the real layout.
    pub data_layout: Option<String>,
}

/// The MLIR text of `module`.
pub fn codegen(module: &MirModule, opts: &CodegenOptions) -> Result<MlirOutput, RokDiagnostic> {
    let target = module.target.clone();
    let mut e = emit::Emitter::new(target.clone());
    e.overflow_checks = opts.overflow_checks;
    e.data_layout.clone_from(&opts.data_layout);
    if opts.debug {
        e.debug = Some(debug::DebugInfo::new(target));
    }
    if let Some(r) = &opts.repl {
        e.gc_types.clone_from(&r.gc_tables);
    }
    e.repl.clone_from(&opts.repl);
    e.emit_module(module);
    if let Some(first) = e.errors.first() {
        let mut d = RokDiagnostic::error(ErrorKind::Unsupported, first.clone());
        for more in e.errors.iter().skip(1) {
            d = d.with_note(more.clone());
        }
        return Err(d);
    }
    let gc_types = e.gc_type_count();
    let gc_tables = if opts.repl.is_some() {
        std::mem::take(&mut e.gc_types)
    } else {
        Vec::new()
    };
    let mut out = MlirOutput {
        gc_types,
        gc_tables,
        text: e.finish(),
        ..MlirOutput::default()
    };
    if let Some(r) = &opts.repl {
        (out.text, out.reused, out.fresh, out.fns) = repl::reuse(&out.text, &r.known);
    }
    Ok(out)
}

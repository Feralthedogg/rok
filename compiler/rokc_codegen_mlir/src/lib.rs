//! Standard-MLIR text emission. Looks at MIR only.
//!
//! Output uses only upstream dialects (`func`, `arith`, `scf`, `cf`,
//! `memref`, `index`, `math`, `llvm`). The downstream toolchain
//! (`mlir-opt` + `mlir-translate` + `clang/lld`) does the rest.

mod abi;
mod debug;
pub mod emit;
mod mangle;

pub use mangle::{Demangled, demangle, pkg_hash};

use rokc_diagnostic::{ErrorKind, RokDiagnostic};
use rokc_mir::MirModule;

#[derive(Clone, Debug, Default)]
pub struct MlirOutput {
    pub text: String,
    /// Names hinted to the linker (e.g. `rokr`, ABI shims).
    pub runtime_libraries: Vec<String>,
    /// Number of GC type ids used (`ReplCell::type_offset`).
    pub gc_types: u32,
}

/// One REPL cell (`rokc repl`).
///
/// A shared library the session host loads into a process whose
/// runtime is already up. Instead of a C
/// `main`, `rok_repl_cell()` registers the cell's GC types and roots
/// and runs the user `main`.
#[derive(Clone, Debug, Default)]
pub struct ReplCell {
    /// Added to the GC type ids: objects of earlier cells keep theirs,
    /// so each cell takes fresh ones.
    pub type_offset: u32,
    /// `extern` statics this cell defines (zeroed, exported, GC roots):
    /// the slots of the session's new bindings.
    pub define: Vec<String>,
}

pub fn codegen(module: &MirModule) -> Result<MlirOutput, RokDiagnostic> {
    codegen_with_target(module, None, true, false, None)
}

pub fn codegen_with_target(
    module: &MirModule,
    target: Option<&str>,
    overflow_checks: bool,
    debug: bool,
    repl: Option<&ReplCell>,
) -> Result<MlirOutput, RokDiagnostic> {
    let pointer_width = pointer_width_for_target(target);
    let mut e = emit::Emitter::new(pointer_width);
    e.overflow_checks = overflow_checks;
    e.c_target = abi::CTarget::from_triple(target);
    if debug {
        e.debug = Some(debug::DebugInfo::new());
    }
    e.repl = repl.cloned();
    e.emit_module(module);
    if let Some(first) = e.errors.first() {
        let mut d = RokDiagnostic::error(ErrorKind::Unsupported, first.clone());
        for more in e.errors.iter().skip(1) {
            d = d.with_note(more.clone());
        }
        return Err(d);
    }
    let gc_types = e.gc_type_count();
    Ok(MlirOutput {
        gc_types,
        text: e.finish(),
        runtime_libraries: vec!["rokr".to_owned()],
    })
}

fn pointer_width_for_target(target: Option<&str>) -> u32 {
    // 32-bit architectures by triple prefix; everything else (x86_64,
    // aarch64, arm64, riscv64, wasm64, …) is 64-bit.
    const BITS32: &[&str] = &[
        "i386", "i486", "i586", "i686", "arm-", "armv", "armeb", "thumb", "riscv32", "wasm32",
        "mips-", "mipsel-", "powerpc-", "sparc-",
    ];
    match target {
        Some(t) if BITS32.iter().any(|p| t.starts_with(p)) => 32,
        _ => 64,
    }
}

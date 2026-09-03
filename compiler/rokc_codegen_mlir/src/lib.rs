//! Standard-MLIR text emission. Looks at MIR only.
//!
//! Output uses only upstream dialects (`func`, `arith`, `scf`, `cf`,
//! `memref`, `index`, `math`, `llvm`). The downstream toolchain
//! (`mlir-opt` + `mlir-translate` + `clang/lld`) does the rest.

pub mod emit;

use rokc_diagnostic::RokDiagnostic;
use rokc_mir::MirModule;

#[derive(Clone, Debug, Default)]
pub struct MlirOutput {
    pub text: String,
    /// Names hinted to the linker (e.g. `rokr`, ABI shims).
    pub runtime_libraries: Vec<String>,
}

pub fn codegen(module: &MirModule) -> Result<MlirOutput, RokDiagnostic> {
    codegen_with_target(module, None)
}

pub fn codegen_with_target(
    module: &MirModule,
    target: Option<&str>,
) -> Result<MlirOutput, RokDiagnostic> {
    let pointer_width = pointer_width_for_target(target);
    let mut e = emit::Emitter::new(pointer_width);
    e.emit_module(module);
    Ok(MlirOutput {
        text: e.finish(),
        runtime_libraries: vec!["rokr".to_owned()],
    })
}

fn pointer_width_for_target(target: Option<&str>) -> u32 {
    match target {
        Some(t) if t.contains("wasm32") || t.contains("i686") || t.contains("armv7") => 32,
        _ => 64,
    }
}

//! rok's own native backend: MIR straight to machine code and an object
//! file, no LLVM. It builds `-O0` code and REPL cells fast; LLVM builds
//! the optimized code. Both follow one runtime ABI, so objects from
//! either link together.
//!
//! MIR → LIR (`lower`, target-independent: layouts, calling
//! conventions, GC frames, barriers, checks) → machine code (`a64`, one
//! module per ISA) → object (`macho`, `elf`, `coff`: one module per
//! format).

// Instruction selection names registers and encodings tersely; its
// dispatch matches are long by nature.
#![allow(clippy::many_single_char_names, clippy::cognitive_complexity)]

mod a64;
mod cc;
mod coff;
mod dwarf;
mod elf;
mod lir;
mod lower;
mod macho;
mod module;
mod obj;
mod wrap;
mod x64;

use rokc_diagnostic::{ErrorKind, RokDiagnostic};
use rokc_mir::{MirModule, MirTy, RValue, Statement};

/// How to generate code for a module (its target is `MirModule::target`).
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Panic on integer overflow.
    pub overflow_checks: bool,
    /// `-g`: DWARF debug info (spec 9.9.6).
    pub debug: bool,
    /// Generate a REPL cell instead of a program.
    pub repl: Option<rokc_codegen_mlir::ReplCell>,
    /// A REPL cell: the exported functions it defines anew (the rest the
    /// session has: declared only, `rokc_codegen_mlir::ReplFn`).
    pub fresh_fns: Option<std::collections::HashSet<String>>,
}

/// A compiled module.
pub struct Output {
    /// The relocatable object file.
    pub object: Vec<u8>,
    /// Number of GC type ids used.
    pub gc_types: u32,
    /// Every `ScanTable` so far (a REPL cell: the next one's
    /// `ReplCell::gc_tables`).
    pub gc_tables: Vec<Vec<u32>>,
}

/// Why this backend cannot compile `module` (the caller then uses
/// LLVM): a target without an instruction selector / object writer, or
/// MLIR written in the source (`__mlir_op`, bare 1.9).
#[must_use]
pub fn unsupported(module: &MirModule) -> Option<String> {
    let t = &module.target;
    if !matches!(
        (t.arch.as_str(), t.os.as_str()),
        ("aarch64" | "x86_64", "macos" | "linux" | "windows")
    ) {
        return Some(format!("no native backend for {}-{}", t.arch, t.os));
    }
    let mlir = module.functions.iter().any(|f| {
        f.locals.iter().any(|l| matches!(l.ty, MirTy::Mlir(_)))
            || f.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
                matches!(
                    s,
                    Statement::MlirRegion { .. }
                        | Statement::Assign {
                            rvalue: RValue::MlirOp { .. },
                            ..
                        }
                )
            })
    });
    mlir.then(|| "the module uses `__mlir_op`".to_owned())
}

/// Compile `module` to an object file.
pub fn compile(module: &MirModule, opts: &Options) -> Result<Output, RokDiagnostic> {
    if let Some(why) = unsupported(module) {
        return Err(RokDiagnostic::error(ErrorKind::Unsupported, why));
    }
    let emit = if module.target.arch == "x86_64" {
        x64::emit
    } else {
        a64::emit
    };
    let mut c = module::compile(module, opts, &mut { emit });
    // COFF: no DWARF (Windows debuggers read CodeView; `-g` builds for
    // Windows go through LLVM).
    if opts.debug && !c.obj.coff {
        dwarf::write(&mut c.obj, &module.target, &module.struct_names);
    }
    if let Some(d) = rokc_codegen_mlir::codegen_error(&c.errors) {
        return Err(d);
    }
    Ok(Output {
        object: if c.obj.coff {
            coff::write(&c.obj)
        } else if c.obj.elf {
            elf::write(&c.obj)
        } else {
            macho::write(&c.obj)
        },
        gc_types: c.gc_types.len() as u32,
        gc_tables: c.gc_types,
    })
}

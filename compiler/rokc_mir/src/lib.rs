//! Mid-level IR. SSA basic blocks; the last representation before MLIR
//! text emission. Looks at HIR only.

mod coro;
mod liveness;
mod lower;
mod print;
mod ty;

pub use liveness::{Deaths, deaths};
pub use lower::lower;
pub use print::print_mir;
pub use ty::{has_gc_ref, lower_ty, sum_layout};

use rokc_core::DefId;
use rokc_diagnostic::Span;
use rokc_hir::StructId;
use rokc_ir_common::{BlockId, ConstVal, FunctionId, LocalId, PrimOp, PrimTy};

#[derive(Clone, Debug, Default)]
pub struct MirModule {
    pub functions: Vec<MirFunction>,
    pub statics: Vec<MirStaticDef>,
    /// `#[export_name]` functions: id → linker symbol.
    pub exports: Vec<(FunctionId, String)>,
    /// C variadic `extern` declarations (spec 8.6.10): calls pass the
    /// arguments past the declared parameters as C `...` arguments.
    pub c_variadic: Vec<FunctionId>,
    /// Package hash per item-path prefix (`rok::core`, ..., `""` for the
    /// user package; spec 0.3.3), longest prefix first. Filled by the
    /// driver; empty → one hash over the printed MIR.
    pub pkg_hashes: Vec<(String, String)>,
    /// Separate compilation with prebuilt dependencies (spec 904).
    pub link: Link,
}

/// How this module links with prebuilt dependency packages (their
/// `lib<name>.a` + `<name>.rhir`). Filled by the driver, but
/// `prebuilt_fns` (from HIR).
#[derive(Clone, Debug, Default)]
pub struct Link {
    /// This module is package `lib`'s prebuilt library: only that
    /// package's functions and statics are exported, the rest of the
    /// code it uses (library, instances) is a private copy.
    pub lib: Option<String>,
    /// Packages loaded from RHIR: their code and statics live in their
    /// `.a`; bodies compiled here (generics, kept bodies) are private.
    pub prebuilt: Vec<String>,
    /// Body-less declarations of prebuilt functions (rok ABI, mangled).
    pub prebuilt_fns: Vec<FunctionId>,
    /// Added to every GC type id: the ids below belong to the prebuilt
    /// dependencies.
    pub type_offset: u32,
}

#[derive(Clone, Debug)]
pub struct MirStaticDef {
    pub name: String,
    pub ty: MirTy,
    pub init: ConstVal,
    pub is_mut: bool,
    /// `extern "C" { static .. }`: defined outside, keeps its C name.
    pub is_extern: bool,
    /// Lazily initialized by this function on first access.
    pub init_fn: Option<FunctionId>,
}

#[derive(Clone, Debug)]
pub struct MirFunction {
    pub id: FunctionId,
    pub def_id: Option<DefId>,
    pub name: String,
    pub params: Vec<LocalId>,
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<BasicBlock>,
    pub param_tys: Vec<MirTy>,
    pub ret_ty: MirTy,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub id: LocalId,
    pub name: Option<String>,
    pub ty: MirTy,
}

#[derive(Clone, Debug)]
pub struct BasicBlock {
    pub id: BlockId,
    /// Block parameters (the MLIR cf-dialect equivalent of phi nodes).
    /// Predecessors pass values by terminator args.
    pub params: Vec<LocalId>,
    pub stmts: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Clone, Debug)]
pub enum Statement {
    Assign {
        target: LocalId,
        rvalue: RValue,
    },
    // `arr[index] = value` — store into a memref-stored array local.
    ArrayWrite {
        array: LocalId,
        index: Operand,
        value: Operand,
        elem_ty: MirTy,
        len: u32,
    },
    // The local's scope ended (only emitted for GC-holding locals):
    // codegen clears its shadow-stack root so it stops retaining.
    StorageDead(LocalId),
    // `buf[index] = value` into a `BufAlloc` object (unchecked).
    BufStore {
        buf: Operand,
        index: Operand,
        value: Operand,
        elem_ty: MirTy,
    },
    /// The following statements come from source position `Span` (a
    /// HIR statement or block value): debug line info only.
    Loc(Span),
    // Store `value` (a `ty`) at raw address `addr` (`usize`).
    RawStore {
        addr: Operand,
        value: Operand,
        ty: MirTy,
        volatile: bool,
    },
    // Field `index` of the `ty` (a tuple) payload of the GC object
    // `ptr` = `value`, in place (coroutine frames, spec 708).
    HeapStore {
        ptr: Operand,
        ty: MirTy,
        index: u32,
        value: Operand,
    },
    // `STATIC_NAME = value` — store into a module-level global.
    StaticStore {
        name: String,
        value: Operand,
        ty: MirTy,
    },
}

#[derive(Clone, Debug)]
pub enum RValue {
    Use(Operand),
    /// `op_ty` is the operand type — the result type lives on the
    /// destination `LocalDecl` (comparisons widen to `bool`).
    BinOp {
        op: PrimOp,
        op_ty: MirTy,
        lhs: Operand,
        rhs: Operand,
    },
    UnaryOp {
        op: PrimOp,
        op_ty: MirTy,
        operand: Operand,
    },
    // Direct call to a function in the same compilation unit.
    Call {
        callee: FunctionId,
        args: Vec<Operand>,
        ret_ty: MirTy,
    },
    // Build a struct value from its fields, in declaration order.
    StructInit {
        ty: MirTy,
        fields: Vec<Operand>,
    },
    // Read field `index` of a struct value.
    FieldRead {
        target: Operand,
        index: u32,
        field_ty: MirTy,
    },
    // Integer cast: zext / extsi when widening, trunci when narrowing.
    // Codegen picks the right arith op from `from_ty` and `to_ty`.
    Cast {
        source: Operand,
        from_ty: MirTy,
        to_ty: MirTy,
    },
    // Bit-preserving move between a variant's payload type and the
    // shared payload slot of its enum / sum (zero-extend / truncate,
    // float bits reinterpreted). Not a value conversion like `Cast`.
    Bitcast {
        source: Operand,
        from_ty: MirTy,
        to_ty: MirTy,
    },
    // Functional field replace: same struct as `source` but with the
    // given index updated. Lowers to `llvm.insertvalue`.
    WithField {
        source: Operand,
        struct_ty: MirTy,
        index: u32,
        value: Operand,
    },
    // Build a fixed-size array literal. Codegen stores each element
    // into the destination local's `memref<N x T>` slot.
    ArrayInit {
        elem_ty: MirTy,
        elements: Vec<Operand>,
    },
    // Read `array[index]` from a memref-stored array local.
    ArrayIndex {
        array: LocalId,
        index: Operand,
        elem_ty: MirTy,
        len: u32,
    },
    // Materialise a function-pointer SSA value from a known callee id.
    FnAddr {
        callee: FunctionId,
        fn_ty: MirTy,
    },
    // Read a module-level `static` global by name. Codegen lowers to
    // `llvm.mlir.addressof + load`.
    StaticLoad {
        name: String,
        ty: MirTy,
    },
    // Copy `value` (of type `ty`) into a fresh GC object; yields its
    // `GcRef`. The payload of an `any Tr` value. Codegen keeps a numeric /
    // bool / char primitive no wider than a pointer inline (the word is
    // the value's bits, not a reference).
    HeapBox {
        value: Operand,
        ty: MirTy,
    },
    // A zeroed GC object holding `len` `elem_ty`s; yields its `GcRef`.
    // Its type's ScanTable traces the payload when `elem_ty` holds GC
    // references.
    BufAlloc {
        elem_ty: MirTy,
        len: Operand,
    },
    // Load a `ty` from raw address `addr` (`usize`).
    RawLoad {
        addr: Operand,
        ty: MirTy,
        volatile: bool,
    },
    // Size (or alignment) of `ty` in bytes, as `usize`.
    SizeOf {
        ty: MirTy,
        align: bool,
    },
    // Element `index` of a `BufAlloc` object (unchecked).
    BufLoad {
        buf: Operand,
        index: Operand,
        elem_ty: MirTy,
    },
    // Atomic `op` on element `index` of a `BufAlloc` object (see
    // `HirExprKind::BufAtomic`); yields the previous value.
    BufAtomic {
        op: &'static str,
        buf: Operand,
        index: Operand,
        args: Vec<Operand>,
        elem_ty: MirTy,
        order: [&'static str; 2],
    },
    // Load the `ty` payload of the `GcRef` `ptr` (a `HeapBox` object),
    // or unpack an inline payload.
    HeapLoad {
        ptr: Operand,
        ty: MirTy,
    },
    // A zeroed GC object with a `ty` payload (traced by `ty`'s
    // ScanTable); yields its `GcRef`. A coroutine frame (spec 708).
    HeapAlloc {
        ty: MirTy,
    },
    // Field `index` of the `ty` (a tuple) payload of GC object `ptr`.
    HeapField {
        ptr: Operand,
        ty: MirTy,
        index: u32,
    },
    // Indirect call through a function-typed operand.
    CallIndirect {
        callee: Operand,
        args: Vec<Operand>,
        arg_tys: Vec<MirTy>,
        ret_ty: MirTy,
    },
}

#[derive(Clone, Debug)]
pub enum Operand {
    Const(ConstVal),
    Copy(LocalId),
}

#[derive(Clone, Debug)]
pub enum Terminator {
    Goto {
        target: BlockId,
        args: Vec<Operand>,
    },
    If {
        cond: Operand,
        then_bb: BlockId,
        then_args: Vec<Operand>,
        else_bb: BlockId,
        else_args: Vec<Operand>,
    },
    Return(Option<Operand>),
    Unreachable,
    /// Coroutine suspend point (only before `coro::transform`): hand
    /// `value` to the resumer; the next resume continues at `resume`.
    /// `is_final` marks the point a finished coroutine parks at.
    Suspend {
        value: Option<Operand>,
        resume: BlockId,
        is_final: bool,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum MirTy {
    Unit,
    Prim(PrimTy),
    Any,
    // Tagged union (sum type).
    Sum(Vec<MirTy>),
    Tuple(Vec<MirTy>),
    // Concrete struct, fields stored in declaration order.
    Struct(StructId, Vec<MirTy>),
    // Fixed-size array of `MirTy` repeated `len` times.
    Array(Box<MirTy>, u32),
    // First-class function pointer.
    Fn(Vec<MirTy>, Box<MirTy>),
    /// Word that may hold a GC reference (an object's header address,
    /// 801), lowered as a pointer-width integer: the payload of an `any`
    /// value, which holds small primitives inline instead. Codegen roots
    /// and traces exactly these words; the collector ignores a word that
    /// is not an object address.
    GcRef,
}

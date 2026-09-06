//! Mid-level IR. SSA basic blocks; the last representation before MLIR
//! text emission. Looks at HIR only.

mod lower;
mod print;
mod ty;

pub use lower::lower;
pub use print::print_mir;
pub use ty::{enums_without_layout, lower_ty, sum_layout};

use rokc_core::DefId;
use rokc_diagnostic::Span;
use rokc_hir::StructId;
use rokc_ir_common::{BlockId, ConstVal, FunctionId, LocalId, PrimOp, PrimTy};

#[derive(Clone, Debug, Default)]
pub struct MirModule {
    pub functions: Vec<MirFunction>,
    pub statics: Vec<MirStaticDef>,
}

#[derive(Clone, Debug)]
pub struct MirStaticDef {
    pub name: String,
    pub ty: MirTy,
    pub init: ConstVal,
    pub is_mut: bool,
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
    // Copy `value` (of type `ty`) to a fresh heap cell; yields the cell's
    // address as `usize`. The payload of an `any Tr` value. Codegen keeps
    // a numeric / bool / char primitive no wider than a pointer inline
    // (the `usize` is the value's bits, not an address).
    HeapBox {
        value: Operand,
        ty: MirTy,
    },
    // Load a `ty` from the `usize` address `ptr` (a `HeapBox` cell), or
    // unpack an inline payload.
    HeapLoad {
        ptr: Operand,
        ty: MirTy,
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
}

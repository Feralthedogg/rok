//! High-level IR.
//!
//! Lowering from AST. The compiler still has no operator semantics —
//! `OpInfix` etc. would resolve to stdlib trait method calls in a later
//! pass that has access to the registered `#[infix]` table. The current
//! lowering only handles the subset that is independent of stdlib
//! bootstrap: function definitions, blocks, locals, and primitive
//! literals carrying an explicit type suffix.

mod lower;
mod print;
mod ty;
mod uses;
mod walk;

pub use lower::{lower, lower_full, lower_with_uses};
pub use print::print_hir;
pub use ty::resolve_ty;
pub use uses::{ReExport, UseEntry, UseTable, build_use_table};

use rokc_core::DefId;
use rokc_diagnostic::RokDiagnostic;
use rokc_diagnostic::Span;
use rokc_ir_common::{ConstVal, FunctionId, LocalId, PrimOp, PrimTy};

#[derive(Clone, Debug, Default)]
pub struct HirModule {
    pub functions: Vec<HirFunction>,
    pub structs: Vec<HirStructDef>,
    pub enums: Vec<HirEnumDef>,
    /// Module-level `static` items with stable storage (one global per
    /// entry). Differs from `const` (which inlines at each use site).
    pub statics: Vec<HirStaticDef>,
    /// Diagnostics produced during lowering: visibility violations,
    /// glob conflicts, unresolved paths, etc. Driver appends these to
    /// its overall diagnostic list.
    pub diagnostics: Vec<RokDiagnostic>,
}

#[derive(Clone, Debug)]
pub struct HirStaticDef {
    pub name: String,
    pub ty: HirTy,
    /// Const value the global is initialized to. Restricted to literal
    /// or const-folded primitives in the current slice.
    pub init: ConstVal,
    pub is_mut: bool,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EnumId(pub u32);

#[derive(Clone, Debug)]
pub struct HirEnumDef {
    pub id: EnumId,
    pub def_id: Option<DefId>,
    pub name: String,
    pub variants: Vec<HirEnumVariant>,
    pub span: Span,
}

// Unit + single-primitive tuple variants in this slice.
#[derive(Clone, Debug)]
pub struct HirEnumVariant {
    pub name: String,
    pub tag: u32,
    pub payload_ty: Option<HirTy>,
    /// For named-form variants (`Move { x: i32; y: i32; }`), the field
    /// names in declaration order. The payload is a tuple keyed by
    /// position, so this list maps field name → tuple index. Empty
    /// for unit and tuple-form variants.
    pub named_fields: Vec<String>,
    /// Number of constructor arguments (0 = unit variant). Needed because
    /// `V(T)` and `V(A, B)` both store one `payload_ty` (a tuple for the
    /// latter), so a tuple-typed single payload is otherwise ambiguous.
    pub arity: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct StructId(pub u32);

#[derive(Clone, Debug)]
pub struct HirStructDef {
    pub id: StructId,
    pub def_id: Option<DefId>,
    pub name: String,
    pub fields: Vec<HirField>,
    pub span: Span,
    /// Concrete type-arg substitution if this struct is a
    /// monomorphization of a generic struct. Empty for non-generic
    /// struct definitions.
    pub generic_args: Vec<HirTy>,
    /// `Some(_)` when this entry actually models a `union { ... }`
    /// declaration (spec 2.x / i-want 322-340). The struct backing
    /// has a single synthetic `__data` field whose type comes from
    /// the chosen `UnionStorage`; declared field names are kept in
    /// `aliases` for lookup at init/read sites.
    pub union_kind: Option<HirUnionKind>,
}

/// How a `union` decl is laid out in storage. Spec lets the compiler
/// choose the default layout; `#[repr(C)]` and non-primitive fields
/// force the byte-array path so the layout matches C ABI semantics.
#[derive(Clone, Debug)]
pub enum UnionStorage {
    /// All declared fields are primitive and the union isn't `#[repr(C)]`.
    /// The backing store is a single primitive wide enough to hold any
    /// field; access is via int/float cast (`zext`/`trunc`/`bitcast`).
    /// Optimised for register allocation.
    WidestPrim(PrimTy),
    /// At least one declared field is a struct/enum, or `#[repr(C)]`
    /// is set. Backing store is `[u8; size]` aligned to `align`; field
    /// access goes through `llvm.bitcast`+load/store on the storage
    /// pointer (see codegen).
    ByteArray { size: u32, align: u32 },
}

#[derive(Clone, Debug)]
pub struct HirUnionKind {
    pub storage: UnionStorage,
    /// Each declared field name → its declared `HirTy`. Cast targets
    /// at write/read sites use this map.
    pub aliases: Vec<(String, HirTy)>,
    pub is_repr_c: bool,
}

#[derive(Clone, Debug)]
pub struct HirField {
    pub name: String,
    pub ty: HirTy,
    /// Default expression (spec 2.x / i-want 942-950) — evaluated at
    /// init time when this field is omitted from the struct literal.
    /// Stored as the raw AST expression so the init site can lower it
    /// in the surrounding context (one local-set per instance is fine
    /// because the spec requires the expression to be const, hence
    /// side-effect free).
    pub default: Option<rokc_ast::Expr>,
}

#[derive(Clone, Debug)]
pub struct HirFunction {
    pub id: FunctionId,
    pub def_id: Option<DefId>,
    pub name: String,
    pub params: Vec<HirParam>,
    pub locals: Vec<HirLocal>,
    pub ret_ty: HirTy,
    pub body: Option<HirBlock>,
    pub is_async: bool,
    pub is_generator: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct HirParam {
    pub name: String,
    pub local: LocalId,
    pub ty: HirTy,
    pub by_ref: bool,
}

#[derive(Clone, Debug)]
pub struct HirLocal {
    pub id: LocalId,
    pub name: Option<String>,
    pub ty: HirTy,
}

#[derive(Clone, Debug)]
pub struct HirBlock {
    pub stmts: Vec<HirStmt>,
    /// Trailing expression: when present this is the value of the block.
    pub trailing: Option<HirExpr>,
    /// `'label:` prefix on the block. When set, `break 'label value`
    /// inside the block exits with `value` (labeled block early exit).
    pub label: Option<String>,
}

#[derive(Clone, Debug)]
pub enum HirStmt {
    Let {
        local: LocalId,
        init: HirExpr,
    },
    Assign {
        local: LocalId,
        value: HirExpr,
    },
    // `arr[index] = value;` — array-element write.
    ArrayAssign {
        array_local: LocalId,
        index: HirExpr,
        value: HirExpr,
        elem_ty: HirTy,
    },
    /// Write to a module-level `static`. Codegen lowers via global
    /// addressof + store. Only valid when the static was declared `mut`.
    StaticAssign {
        name: String,
        value: HirExpr,
    },
    Expr(HirExpr),
    Return(Option<HirExpr>),
    Break {
        label: Option<String>,
        value: Option<HirExpr>,
    },
    Continue {
        label: Option<String>,
    },
    /// `throw v` — divergent statement (spec 3.14.1). Stage-1 lowers the
    /// payload to a `rok_panic(code)` call carried in the inner expr; MIR
    /// emits the call followed by an `unreachable` terminator so the
    /// surrounding block is correctly seen as not falling through.
    Throw(HirExpr),
}

#[derive(Clone, Debug)]
pub struct HirExpr {
    pub kind: HirExprKind,
    pub ty: HirTy,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum HirExprKind {
    Const(ConstVal),
    Local(LocalId),
    Block(Box<HirBlock>),
    /// Read of a module-level `static` (stable storage). Lowered to a
    /// global addressof + load by codegen.
    StaticRef(String),
    /// Pre-resolution placeholder for unresolved paths.
    UnresolvedPath(Vec<String>),
    /// Primitive binary op produced by short-circuit dispatch when both
    /// operands are the same primitive type. The full path goes through
    /// trait dispatch + `#[lang(...)]` recognition; for primitives the
    /// short-circuit gives the same result.
    PrimBinOp {
        op: PrimOp,
        lhs: Box<HirExpr>,
        rhs: Box<HirExpr>,
    },
    PrimUnaryOp {
        op: PrimOp,
        operand: Box<HirExpr>,
    },
    /// Direct call to a function by id (resolved within this module).
    Call {
        callee: FunctionId,
        args: Vec<HirExpr>,
    },
    /// Function pointer literal — refers to a known module-level function
    /// id. Used by closures lifted to anonymous top-level functions.
    FnRef(FunctionId),
    /// Indirect call through a function-typed expression.
    CallIndirect {
        callee: Box<HirExpr>,
        args: Vec<HirExpr>,
        ret_ty: HirTy,
    },
    /// `expr as Type` — primitive integer cast for now (zext/sext/trunc).
    /// Codegen picks the right op from `from_ty`/`to_ty`.
    Cast {
        operand: Box<HirExpr>,
        from_ty: HirTy,
        to_ty: HirTy,
    },
    /// Build a closure value: a struct of (`fn_addr`, env). The lifted
    /// function takes `env` as its first parameter; the user-visible
    /// signature is `(arg_tys) -> ret_ty`.
    ClosureValue {
        fn_id: FunctionId,
        env: Box<HirExpr>,
        env_ty: HirTy,
        arg_tys: Vec<HirTy>,
        ret_ty: HirTy,
    },
    /// Call a closure value: extract `fn_addr` and env, then call the
    /// underlying function with `(env, args...)`.
    CallClosure {
        closure: Box<HirExpr>,
        args: Vec<HirExpr>,
        arg_tys: Vec<HirTy>,
        ret_ty: HirTy,
        env_ty: HirTy,
    },
    /// `if cond { then_block } else { else_branch }`. The `else_branch`
    /// is itself an expression so `else if` chains and block-as-else are
    /// represented uniformly.
    If {
        cond: Box<HirExpr>,
        then_block: Box<HirBlock>,
        else_branch: Option<Box<HirExpr>>,
    },
    /// `while cond { body }`. Always evaluates to unit.
    While {
        label: Option<String>,
        cond: Box<HirExpr>,
        body: Box<HirBlock>,
    },
    /// `loop { body }`. The block runs until a `break` exits it; the
    /// loop's value comes from the break operand (or unit).
    Loop {
        label: Option<String>,
        body: Box<HirBlock>,
        result_ty: HirTy,
    },
    /// `match scrut { pat => body, ... }`.
    Match {
        scrutinee: Box<HirExpr>,
        arms: Vec<HirMatchArm>,
    },
    // `Foo { field: value, ... }`; fields in declaration order.
    StructInit {
        struct_id: StructId,
        fields: Vec<HirExpr>,
    },
    // `expr.field` on a struct value.
    FieldRead {
        target: Box<HirExpr>,
        struct_id: StructId,
        field_index: u32,
        field_ty: HirTy,
    },
    // Functional field update: same struct as `target` but with one
    // field replaced. Produced by lowering `p.x = value`.
    WithField {
        target: Box<HirExpr>,
        struct_id: StructId,
        field_index: u32,
        value: Box<HirExpr>,
    },
    // `EnumName::Variant(args)`. `args` is empty for unit variants.
    EnumVariantInit {
        enum_id: EnumId,
        variant_index: u32,
        args: Vec<HirExpr>,
    },
    // Wrap a value into a sum-type slot: `let x: i32 | none = 42`.
    // `value` is `None` for the `none` variant.
    SumWrap {
        sum_ty: HirTy,
        variant_index: u32,
        value: Option<Box<HirExpr>>,
    },
    // `(a, b, c)` tuple literal.
    Tuple {
        fields: Vec<HirExpr>,
    },
    // `t.0`, `t.1` — read tuple field by positional index.
    TupleField {
        target: Box<HirExpr>,
        index: u32,
        field_ty: HirTy,
    },
    // `[a, b, c]` fixed-size array literal.
    ArrayInit {
        elem_ty: HirTy,
        elements: Vec<HirExpr>,
    },
    // `arr[idx]` — element read.
    ArrayIndex {
        array: Box<HirExpr>,
        index: Box<HirExpr>,
        elem_ty: HirTy,
    },
    /// Cast a value into the synthetic `__data` storage of a union
    /// during initialiser lowering. For `WidestPrim` storage this is
    /// an int/float cast (zext / sext / trunc / float-to-int bitcast).
    /// For `ByteArray` storage MIR/codegen lowers it to an alloca +
    /// pointer bitcast + store + reload pattern. Spec 2.x.
    UnionWrite {
        struct_id: StructId,
        from_ty: HirTy,
        storage_ty: HirTy,
        value: Box<HirExpr>,
    },
    /// Read a declared field from a union's `__data` storage. The
    /// storage value is cast/bitcast back to `field_ty`. Symmetric
    /// counterpart of `UnionWrite`.
    UnionRead {
        struct_id: StructId,
        target: Box<HirExpr>,
        field_name: String,
        storage_ty: HirTy,
        field_ty: HirTy,
    },
}

#[derive(Clone, Debug)]
pub struct HirMatchArm {
    pub pat: HirPattern,
    pub guard: Option<HirExpr>,
    pub body: HirExpr,
}

/// Pattern subset supported by the current lowering. Range / struct /
/// enum / tuple patterns land later, together with exhaustiveness.
#[derive(Clone, Debug)]
pub enum HirPattern {
    /// `_` — matches anything, no binding.
    Wildcard,
    /// `name` — matches anything and binds the value to a fresh local.
    Binding { local: LocalId, ty: HirTy },
    /// `42i32`, `"foo"`, `true` — matches when the scrutinee equals
    /// the constant value.
    Literal { value: ConstVal, prim: PrimTy },
    /// `a | b | c` — matches if any sub-pattern matches.
    Or(Vec<HirPattern>),
    /// `(p0, p1, ...)` — matches a tuple, sub-patterns aligned to elements.
    Tuple(Vec<HirPattern>),
    /// `Foo { field: pat, ... }` — matches a struct, fields keyed by index
    /// into the struct definition. Fields not listed are matched as wildcard.
    Struct {
        struct_id: StructId,
        fields: Vec<(u32, HirPattern)>,
    },
    /// `lo..hi` (exclusive) or `lo..=hi` (inclusive). Either bound may be
    /// absent — `0..` matches anything `>= 0`. The compare type is the
    /// scrutinee's primitive.
    Range {
        start: Option<ConstVal>,
        end: Option<ConstVal>,
        inclusive: bool,
        prim: PrimTy,
    },
    // `EnumName::Variant(sub_pat...)` pattern.
    EnumVariant {
        enum_id: EnumId,
        variant_index: u32,
        args: Vec<HirPattern>,
    },
    // `name: T` — match variant of a sum at index `variant_index` and
    // optionally bind the unwrapped payload to `binder`.
    SumVariant {
        sum_ty: HirTy,
        variant_index: u32,
        binder: Option<LocalId>,
        payload_ty: Option<HirTy>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum HirTy {
    /// Not yet inferred.
    Unknown,
    /// Unit `()`. Empty tuple — the implicit return type when none is given.
    Unit,
    Prim(PrimTy),
    /// Dynamic `any` slot.
    Any,
    Path(Vec<String>),
    Sum(Vec<HirTy>),
    Tuple(Vec<HirTy>),
    // Resolved struct (Path → known def).
    Struct(StructId),
    // Resolved enum.
    Enum(EnumId),
    // Fixed-size array `[T; N]`.
    Array(Box<HirTy>, u32),
    // `fn(A, B) -> R` — first-class function pointer.
    Fn(Vec<HirTy>, Box<HirTy>),
    // Closure value: function pointer paired with captured-by-value
    // environment. Stored in MIR as a 2-tuple `{fn_ptr, env}`. The env
    // type is part of the closure's type identity — closures with
    // different capture sets are different closure types.
    Closure {
        args: Vec<HirTy>,
        ret: Box<HirTy>,
        env: Box<HirTy>,
    },
}

//! High-level IR.
//!
//! Lowering from AST. The compiler still has no operator semantics —
//! `OpInfix` etc. would resolve to stdlib trait method calls in a later
//! pass that has access to the registered `#[infix]` table. The current
//! lowering only handles the subset that is independent of stdlib
//! bootstrap: function definitions, blocks, locals, and primitive
//! literals carrying an explicit type suffix.

#[path = "../../../runtime/rokr/src/fmt_spec.rs"]
mod fmt_spec;
mod lower;
mod print;
mod ty;
mod uses;
pub mod walk;

pub use lower::FN_BLOCK_LABEL;
pub use lower::type_visible;
pub use lower::{lower, lower_full, lower_with_uses};
pub use print::print_hir;

/// Program attribute set by the driver: the dependency packages' names.
///
/// Its args are words, the top-level module names that are dependency
/// packages (`--extern`). Visibility stops
/// at a package (`pub(pkg)`, `pub(sub)`), `pkg::` in a dependency is the
/// dependency, and a path starting with a dependency's name reaches it
/// from any module.
pub const PACKAGES_ATTR: &str = "#packages";

/// Marker attribute (string argument) with the module of an `impl`
/// block, set by the driver.
pub const IMPL_MODULE_ATTR: &str = "#impl_module";

/// Marker attribute on a trait / impl method, path `[ASSOC_TYPES_ATTR,
/// X, ..]`: the associated types whose bare name `X` means `Self::X` in
/// the body (spec 2.8.3).
pub const ASSOC_TYPES_ATTR: &str = "#assoc";

/// Marker attribute on the compiler-injected runtime hook block.
///
/// Its functions are safe to call although they are `extern "C"` (spec
/// 4.15 makes user-declared externs implicitly `unsafe`). `#` cannot
/// start a user attribute name.
pub const SAFE_EXTERN_ATTR: &str = "#safe_extern";

/// Marker attribute on a function of a prebuilt dependency (loaded from
/// its RHIR, spec 904) whose body is in the dependency's `.a`: a
/// declaration with the dependency's mangled symbol and the rok ABI.
pub const PREBUILT_ATTR: &str = "#prebuilt";

/// Program attribute (one word): the dependency package this build
/// compiles as a prebuilt library (`lib<name>.a` + `<name>.rhir`). Every
/// body of that package is lowered, not only the reachable ones.
pub const LIB_ATTR: &str = "#lib";
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
    /// `#[export_name("sym")]` functions (spec 905 / 509.10): linker
    /// symbol, and a root of unreachable-function pruning.
    pub exports: Vec<(FunctionId, String)>,
    /// Library functions no lowered body reaches: body-less stubs in
    /// `functions` (signatures for tools), not code to emit.
    pub unlowered: Vec<FunctionId>,
    /// C variadic `extern` declarations (spec 8.6.10).
    pub c_variadic: Vec<FunctionId>,
    /// `extern "C" fn` definitions (spec 5.9.10): C code calls them.
    pub c_defs: Vec<FunctionId>,
    /// Every type-like item (struct, enum, union, alias, trait) by full
    /// name: its visibility (`type_visible`).
    pub type_visibility: std::collections::HashMap<String, rokc_core::Visibility>,
    /// Declarations of a prebuilt dependency's functions (`PREBUILT_ATTR`).
    pub prebuilt: Vec<FunctionId>,
    /// A prebuilt-library build's `any` seeds for its RHIR: `(module,
    /// rok source)` (see `lower::expr::any_link`).
    pub any_seeds: Vec<(String, String)>,
    /// The types this program stores into `any` slots that source can
    /// name, as written (the REPL seeds later cells with them).
    pub any_types: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct HirStaticDef {
    pub name: String,
    pub ty: HirTy,
    /// Const value the global is initialized to. Restricted to literal
    /// or const-folded primitives in the current slice.
    pub init: ConstVal,
    pub is_mut: bool,
    /// `extern "C" { static .. }` (spec 5.9.3): no initializer here.
    pub is_extern: bool,
    /// Non-literal initializer: this function computes the value on
    /// first access (lazy, thread-safe); `init` is unused.
    pub init_fn: Option<FunctionId>,
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
    /// Concrete type args if this enum is an instantiation of a generic
    /// enum (`Res<i32, bool>`); empty otherwise. Mirrors `HirStructDef`.
    pub generic_args: Vec<HirTy>,
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
    /// A call to a never-returning runtime hook (`rok_panic` for a failed
    /// `try!`, `rok_uncaught_error` for an error escaping a throwing
    /// `main`). MIR emits the call followed by an `unreachable`
    /// terminator so the block is seen as not falling through. `throw`
    /// itself lowers to plain returns / jumps (see `lower::throws`).
    Panic(HirExpr),
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
    /// `[v; len]` with a large `len`: `value` stored into every element
    /// by a loop.
    ArrayRepeat {
        elem_ty: HirTy,
        value: Box<HirExpr>,
        len: u32,
    },
    /// `buf_new::<T>(len)` — a zeroed `GcBuf<T>` of `len` elements.
    BufNew {
        elem: HirTy,
        len: Box<HirExpr>,
    },
    /// `ptr_read::<T>(addr)` (`rok::bare`): load a `T` at a raw address.
    RawRead {
        addr: Box<HirExpr>,
        ty: HirTy,
        volatile: bool,
    },
    /// `ptr_write(addr, v)`: store `v` at a raw address; unit.
    RawWrite {
        addr: Box<HirExpr>,
        value: Box<HirExpr>,
        ty: HirTy,
        volatile: bool,
    },
    /// `size_of::<T>()` / `align_of::<T>()` (`usize`).
    SizeOf {
        ty: HirTy,
        align: bool,
    },
    /// `buf_get(buf, i)` — element `i` (unchecked).
    BufGet {
        buf: Box<HirExpr>,
        index: Box<HirExpr>,
        elem: HirTy,
    },
    /// `buf_set(buf, i, v)` — store element `i` (unchecked); unit.
    BufSet {
        buf: Box<HirExpr>,
        index: Box<HirExpr>,
        value: Box<HirExpr>,
        elem: HirTy,
    },
    /// `#[intrinsic("rok.atomic.OP")]` (stdlib 2.16.2): atomic `op`
    /// (`load`, `xchg`, `add`, `sub`, `and`, `or`, `xor`, `cas`) on
    /// element `i` of an integer / `bool` buffer. Yields the element's
    /// previous value; `args` are the operand (`cas`: expected, new).
    BufAtomic {
        op: &'static str,
        buf: Box<HirExpr>,
        index: Box<HirExpr>,
        args: Vec<HirExpr>,
        elem: HirTy,
        /// LLVM ordering(s) (`monotonic` .. `seq_cst`); `cas` uses both
        /// (success, failure), the others the first.
        order: [&'static str; 2],
    },
    /// `__mlir_op::<"dialect.op", R>(args.., attributes = {..},
    /// regions = [..])` (stdlib bare 1.9): one MLIR op in generic form,
    /// `attrs` (`name`, MLIR attribute text) verbatim; the expression's
    /// type is the result. Each region is its block arguments (locals of
    /// this function) and a straight-line body ending in the terminator.
    MlirOp {
        op: String,
        attrs: Vec<(String, String)>,
        args: Vec<HirExpr>,
        regions: Vec<(Vec<LocalId>, HirExpr)>,
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
    /// Coroutine suspend point (`yield`, a pending `await`): hand `value`
    /// (the step value, the body function's return type) to the resumer;
    /// the next resume continues after it. `is_final` marks the point a
    /// finished coroutine parks at (it hands back the same value on every
    /// later resume). Unit-typed.
    Suspend {
        value: Box<HirExpr>,
        is_final: bool,
    },
    /// A fresh coroutine of body `body_fn` (an `is_async` /
    /// `is_generator` function) with its initial `args`: a function value
    /// `fn(resume args..) -> step` whose env is the coroutine frame.
    CoroNew {
        body_fn: FunctionId,
        args: Vec<HirExpr>,
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
    /// `name @ sub` — matches like `sub` and binds the whole value.
    At {
        local: LocalId,
        ty: HirTy,
        sub: Box<HirPattern>,
    },
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

impl HirPattern {
    /// Matches every value of its type (no refutable sub-pattern).
    #[must_use]
    pub fn is_irrefutable(&self) -> bool {
        match self {
            Self::Wildcard | Self::Binding { .. } => true,
            Self::At { sub, .. } => sub.is_irrefutable(),
            Self::Tuple(parts) => parts.iter().all(Self::is_irrefutable),
            Self::Struct { fields, .. } => fields.iter().all(|(_, p)| p.is_irrefutable()),
            Self::Or(alts) => alts.iter().any(Self::is_irrefutable),
            Self::Literal { .. }
            | Self::Range { .. }
            | Self::EnumVariant { .. }
            | Self::SumVariant { .. } => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum HirTy {
    /// Not yet inferred.
    Unknown,
    /// Unit `()`. Empty tuple — the implicit return type when none is given.
    Unit,
    Prim(PrimTy),
    /// Untyped wildcard (error recovery, untyped parameters); compatible
    /// with everything. The user's `any` is `AnyTrait(vec![])`.
    Any,
    /// `any` / `any Tr` / `any (A + B)`: canonical trait keys, sorted (D4);
    /// plain `any` has none.
    /// Tag + heap payload; the tag numbers concrete types program-wide.
    /// Construction reuses `SumWrap` (variant index = tag) and narrowing
    /// reuses `SumVariant` with this as `sum_ty`.
    AnyTrait(Vec<String>),
    Path(Vec<String>),
    Sum(Vec<HirTy>),
    Tuple(Vec<HirTy>),
    // Resolved struct (Path → known def).
    Struct(StructId),
    // Resolved enum.
    Enum(EnumId),
    // Fixed-size array `[T; N]`.
    Array(Box<HirTy>, u32),
    // `fn(A, B) -> R` — first-class function pointer. The third field
    // is its auto-trait bounds (`+ Send + Sync`, E3): sorted trait keys.
    Fn(Vec<HirTy>, Box<HirTy>, Vec<String>),
    // Closure value: function pointer paired with captured-by-value
    // environment. Stored in MIR as a 2-tuple `{fn_ptr, env}`. The env
    // type is part of the closure's type identity — closures with
    // different capture sets are different closure types.
    Closure {
        args: Vec<HirTy>,
        ret: Box<HirTy>,
        env: Box<HirTy>,
    },
    // What a function declared `throws (err) -> ok` returns: the
    // `{ is_err: bool, ok, err }` carrier (value-based errors, no
    // unwinding). Appears only as a function's (or `fn` type's) return
    // type; `try` unpacks it at the call site.
    Throws {
        ok: Box<HirTy>,
        err: Box<HirTy>,
    },
    /// `rok::core::collections::raw::GcBuf<T>`: a GC object holding a
    /// run of `T`s (the storage of `List` / `Dict` / `Set`). One `GcRef`
    /// word; its length lives with whoever owns it.
    GcBuf(Box<HirTy>),
    /// `!`: the type of a diverging expression (`panic(..)`, `exit(..)`,
    /// `loop {}` without `break`). Flows into any slot.
    Never,
    /// `rok::bare::mlir::__mlir_type<"text">` (stdlib bare 1.9): an
    /// opaque MLIR type, written verbatim into the MLIR text.
    Mlir(String),
}

impl HirTy {
    /// An `extern "C" fn(..)` type: a thin C function pointer, called
    /// with the C ABI (spec 5.9.4), rather than a `{code, env}` value.
    #[must_use]
    pub fn is_c_fn(&self) -> bool {
        matches!(self, Self::Fn(_, _, b) if b.iter().any(|k| k == rokc_ast::C_FN_MARK))
    }

    /// Spec 2.6.4: a sum is a set — nested sums flatten, duplicates
    /// drop, and the members take one canonical order, so `A | B` and
    /// `B | A` are the same `HirTy` (same layout, same tags, same
    /// `PartialOrd` across variants). One member left is that type.
    /// Build every `HirTy::Sum` through this (or `canonicalize` after
    /// rewriting members in place).
    ///
    /// Except a nested layer: a member sum sharing a member with the
    /// outer set's own (non-sum) members stays one member. Generic
    /// substitution builds that shape: `T | none` with `T = i32 | none`
    /// is `(i32 | none)?`, whose outer `none` is not the inner one, and
    /// `T | E` with `T = i32 | E` keeps the generic's `E` apart from
    /// `T`'s. Disjoint members flatten (`T | none` with `T = i32 | str`
    /// is `i32 | str | none`). A written sum is `spread` first, so
    /// `(i32 | none) | none` is `i32 | none`. Each layer is canonical
    /// on its own.
    ///
    /// The order (the spec fixes none): `none` last, the rest by their
    /// structural `Debug` rendering — deterministic for one program
    /// (struct / enum ids are program-wide), so tags agree across modules.
    #[must_use]
    pub fn sum(parts: impl IntoIterator<Item = Self>) -> Self {
        let parts: Vec<Self> = parts.into_iter().collect();
        let own: Vec<Self> = parts
            .iter()
            .filter(|p| !matches!(p, Self::Sum(_)))
            .cloned()
            .collect();
        let mut out = Vec::new();
        for p in parts {
            match p {
                Self::Sum(ps) if !ps.iter().any(|m| own.contains(m)) => out.extend(ps),
                t => out.push(t),
            }
        }
        out.sort_by_cached_key(|t| (t.is_none(), format!("{t:?}")));
        out.dedup();
        if out.len() == 1 {
            out.pop().expect("one member")
        } else {
            Self::Sum(out)
        }
    }

    /// A written member of a written sum: its members join the outer set
    /// (`(A | B) | C` is `A | B | C`, flattening even `none` layers).
    pub fn spread(self, out: &mut Vec<Self>) {
        match self {
            Self::Sum(ps) => out.extend(ps),
            t => out.push(t),
        }
    }

    /// `A | B`, with a nested layer in parentheses: `(i32 | E) | E`,
    /// and `(i32 | none)?` for one beside just the outer `none`.
    pub fn sum_name(&self, name: impl Fn(&Self) -> String) -> String {
        let Self::Sum(ps) = self else {
            return name(self);
        };
        let member = |t: &Self| match t {
            Self::Sum(_) => format!("({})", name(t)),
            t => name(t),
        };
        match ps.as_slice() {
            [inner @ Self::Sum(_), n] if n.is_none() => format!("{}?", member(inner)),
            _ => ps.iter().map(member).collect::<Vec<_>>().join(" | "),
        }
    }

    /// The `none` type.
    #[must_use]
    pub fn is_none(&self) -> bool {
        matches!(self, Self::Path(p) if p.as_slice() == ["none"])
    }

    /// Re-establish the `sum` canon everywhere inside `self` (after
    /// members were rewritten in place: alias / generic substitution).
    pub fn canonicalize(&mut self) {
        match self {
            Self::Sum(ps) => {
                ps.iter_mut().for_each(Self::canonicalize);
                *self = Self::sum(std::mem::take(ps));
            }
            Self::Tuple(ps) => ps.iter_mut().for_each(Self::canonicalize),
            Self::Array(e, _) | Self::GcBuf(e) => e.canonicalize(),
            Self::Fn(a, r, _)
            | Self::Closure {
                args: a, ret: r, ..
            } => {
                a.iter_mut().for_each(Self::canonicalize);
                r.canonicalize();
            }
            Self::Throws { ok, err } => {
                ok.canonicalize();
                err.canonicalize();
            }
            _ => {}
        }
    }
}

/// Pre-order visit of every expression in `b`.
pub fn each_block<'a>(b: &'a HirBlock, f: &mut impl FnMut(&'a HirExpr)) {
    for s in &b.stmts {
        match s {
            HirStmt::Let { init: e, .. }
            | HirStmt::Assign { value: e, .. }
            | HirStmt::StaticAssign { value: e, .. }
            | HirStmt::Expr(e)
            | HirStmt::Panic(e)
            | HirStmt::Return(Some(e))
            | HirStmt::Break { value: Some(e), .. } => each_expr(e, f),
            HirStmt::ArrayAssign { index, value, .. } => {
                each_expr(index, f);
                each_expr(value, f);
            }
            HirStmt::Return(None) | HirStmt::Break { .. } | HirStmt::Continue { .. } => {}
        }
    }
    if let Some(t) = &b.trailing {
        each_expr(t, f);
    }
}

/// Pre-order visit of `e` and its subexpressions.
pub fn each_expr<'a>(e: &'a HirExpr, f: &mut impl FnMut(&'a HirExpr)) {
    f(e);
    let mut go = |x: &'a HirExpr| each_expr(x, f);
    match &e.kind {
        HirExprKind::Const(_)
        | HirExprKind::Local(_)
        | HirExprKind::StaticRef(_)
        | HirExprKind::UnresolvedPath(_)
        | HirExprKind::FnRef(_)
        | HirExprKind::SizeOf { .. } => {}
        HirExprKind::Block(b) => each_block(b, f),
        HirExprKind::While { cond, body, .. } => {
            go(cond);
            each_block(body, f);
        }
        HirExprKind::Loop { body, .. } => each_block(body, f),
        HirExprKind::If {
            cond,
            then_block,
            else_branch,
        } => {
            go(cond);
            each_block(then_block, f);
            if let Some(e) = else_branch {
                each_expr(e, f);
            }
        }
        HirExprKind::Match { scrutinee, arms } => {
            go(scrutinee);
            for a in arms {
                if let Some(g) = &a.guard {
                    each_expr(g, f);
                }
                each_expr(&a.body, f);
            }
        }
        HirExprKind::PrimBinOp { lhs, rhs, .. } => {
            go(lhs);
            go(rhs);
        }
        HirExprKind::PrimUnaryOp { operand: x, .. }
        | HirExprKind::Cast { operand: x, .. }
        | HirExprKind::ClosureValue { env: x, .. }
        | HirExprKind::FieldRead { target: x, .. }
        | HirExprKind::TupleField { target: x, .. }
        | HirExprKind::ArrayRepeat { value: x, .. }
        | HirExprKind::BufNew { len: x, .. }
        | HirExprKind::RawRead { addr: x, .. }
        | HirExprKind::UnionWrite { value: x, .. }
        | HirExprKind::UnionRead { target: x, .. }
        | HirExprKind::Suspend { value: x, .. } => go(x),
        HirExprKind::SumWrap { value, .. } => {
            if let Some(v) = value {
                go(v);
            }
        }
        HirExprKind::Call { args: xs, .. }
        | HirExprKind::StructInit { fields: xs, .. }
        | HirExprKind::EnumVariantInit { args: xs, .. }
        | HirExprKind::Tuple { fields: xs }
        | HirExprKind::ArrayInit { elements: xs, .. }
        | HirExprKind::CoroNew { args: xs, .. } => xs.iter().for_each(go),
        HirExprKind::CallIndirect {
            callee: c, args, ..
        }
        | HirExprKind::CallClosure {
            closure: c, args, ..
        } => {
            go(c);
            args.iter().for_each(go);
        }
        HirExprKind::WithField { target, value, .. } => {
            go(target);
            go(value);
        }
        HirExprKind::RawWrite { addr, value, .. } => {
            go(addr);
            go(value);
        }
        HirExprKind::BufGet { buf, index, .. }
        | HirExprKind::ArrayIndex {
            array: buf, index, ..
        } => {
            go(buf);
            go(index);
        }
        HirExprKind::BufSet {
            buf, index, value, ..
        } => {
            go(buf);
            go(index);
            go(value);
        }
        HirExprKind::BufAtomic {
            buf, index, args, ..
        } => {
            go(buf);
            go(index);
            args.iter().for_each(go);
        }
        HirExprKind::MlirOp { args, regions, .. } => {
            args.iter().for_each(&mut go);
            regions.iter().for_each(|(_, b)| go(b));
        }
    }
}

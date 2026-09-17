//! High-level IR: the AST with names resolved, types checked and
//! generics instantiated.

mod codec;
#[path = "../../../runtime/rokr/src/fmt_spec.rs"]
mod fmt_spec;
mod lower;
mod print;
#[cfg(test)]
mod tests;
mod ty;
mod uses;
pub mod walk;

pub use lower::FN_BLOCK_LABEL;
pub use lower::type_visible;
pub use lower::{Bodies, BodyCache, BodyReuse, Unit};
pub use lower::{lower, lower_full, lower_with_uses};
pub use print::{instance, print_hir};

/// Origin of the root `main`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RootMain {
    /// Declared by the program (or none, for a library).
    #[default]
    Declared,
    /// Made from the entry file's top-level statements (spec 4.16.2).
    Implicit,
    /// The `rokc test` / `rokc bench` harness: it reaches every test, so
    /// item and module visibility do not apply to the paths in its body
    /// (spec 9.1, 6.2.5).
    Harness,
}

/// What the driver tells HIR about the build besides the program.
#[derive(Clone, Debug, Default)]
pub struct HirInput {
    /// The dependency packages' top-level names (`--extern`).
    /// Visibility stops at a package (`pub(pkg)`, `pub(sub)`), `pkg::`
    /// in a dependency is the dependency, and a path starting with a
    /// dependency's name reaches it from any module.
    pub packages: Vec<String>,
    /// The dependency package this build compiles as a prebuilt library
    /// (`lib<name>.a` + `<name>.rokhir`): every body of it is lowered.
    pub lib: Option<String>,
    /// Packages loaded from ROKHIR (spec 904): their body-less functions
    /// are declarations of the symbols in their archives.
    pub prebuilt: Vec<String>,
    /// Lower (and so check) every library body, reached or not
    /// (`rokc check --check-library`).
    pub check_library: bool,
    /// Where the root `main` comes from.
    pub root_main: RootMain,
    /// Also lower the reached small functions of the prebuilt standard
    /// library, for the optimizer to inline: they stay the archive's
    /// symbols (`available_externally`).
    pub inline_prebuilt: bool,
    /// Bits of `usize` / `isize` (the target's pointer width) for
    /// literal ranges and constant evaluation; 0 means 64.
    pub pointer_width: u32,
    /// The module path (`a::b`, `""` at the root) of each item of the
    /// program, by index; missing ones are at the root. HIR qualifies
    /// the item names with it.
    pub item_modules: Vec<String>,
    /// The modules without the implicit `use rok::core::**;`
    /// (`#![no_implicit_rok]`, stdlib 0.2.5).
    pub no_implicit_rok: Vec<String>,
    /// What lowering depends on besides the program (the target and
    /// cfg, the compiler): part of every key of `bodies`.
    pub fingerprint: u64,
    /// Where lowered bodies are kept for the next build (spec 9.2.16).
    pub bodies: Option<Bodies>,
}

/// Marker attribute on a trait / impl method, path `[ASSOC_TYPES_ATTR,
/// X, ..]`: the associated types whose bare name `X` means `Self::X` in
/// the body (spec 2.8.3).
pub const ASSOC_TYPES_ATTR: &str = "#assoc";

pub use ty::resolve_ty;
pub use uses::{ReExport, UseEntry, UseTable, build_use_table, check_use_targets};

use rokc_core::DefId;
use rokc_diagnostic::RokDiagnostic;
use rokc_diagnostic::Span;
use rokc_ir_common::{ConstVal, FnFacts, FunctionId, LocalId, PrimOp, PrimTy};

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
    /// What code generation starts from: `main`, the exports and the
    /// lazy static initializers (a prebuilt library: also every function
    /// of its package and the `any` dispatchers). `None`: keep every
    /// function (a library without `main`).
    pub roots: Option<Vec<FunctionId>>,
    /// Library functions no lowered body reaches: body-less stubs in
    /// `functions` (signatures for tools), not code to emit.
    pub unlowered: Vec<FunctionId>,
    /// Every type-like item (struct, enum, union, alias, trait) by full
    /// name: its visibility (`type_visible`).
    pub type_visibility: std::collections::HashMap<String, rokc_core::Visibility>,
    /// A prebuilt-library build's `any` seeds for its ROKHIR: `(module,
    /// rok source)` (see `lower::expr::any_link`).
    pub any_seeds: Vec<(String, String)>,
    /// The types this program stores into `any` slots that source can
    /// name, as written (the REPL seeds later cells with them).
    pub any_types: Vec<String>,
    /// Every concrete type stored into an `any` slot, with its type tag
    /// (`-g` describes an `any` by them).
    pub any_tags: Vec<(HirTy, u32)>,
    /// Bodies replayed from `HirInput::bodies`, of those lowered.
    pub reuse: BodyReuse,
}

#[derive(Clone, Debug)]
pub struct HirStaticDef {
    pub name: String,
    pub ty: HirTy,
    /// Initial value: a literal or const-folded primitive.
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
    /// `#[repr(..)]` (spec 6.2.2): an integer tag type.
    pub repr: Repr,
    pub def_id: Option<DefId>,
    pub name: String,
    pub variants: Vec<HirEnumVariant>,
    pub span: Span,
    /// Concrete type args if this enum is an instantiation of a generic
    /// enum (`Res<i32, bool>`); empty otherwise. Mirrors `HirStructDef`.
    pub generic_args: Vec<HirTy>,
}

#[derive(Clone, Debug)]
pub struct HirEnumVariant {
    pub name: String,
    /// Stored tag: the variant index, or a value variant's value.
    pub tag: i128,
    pub payload_ty: Option<HirTy>,
    /// Field names of a named-form variant (`Move { x: i32; y: i32; }`),
    /// by payload tuple index. Empty for unit and tuple-form variants.
    pub named_fields: Vec<String>,
    /// Constructor argument count (0 = unit). `V(T)` and `V(A, B)` both
    /// store one `payload_ty`, so a tuple payload is otherwise ambiguous.
    pub arity: usize,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct StructId(pub u32);

#[derive(Clone, Debug)]
pub struct HirStructDef {
    pub id: StructId,
    /// `#[repr(..)]` (spec 6.2.2).
    pub repr: Repr,
    pub def_id: Option<DefId>,
    pub name: String,
    pub fields: Vec<HirField>,
    pub span: Span,
    /// Type arguments of a generic struct instance; empty otherwise.
    pub generic_args: Vec<HirTy>,
    /// `Some` for a `union`: one synthetic `__data` field typed by its
    /// `UnionStorage`; declared fields live in `aliases`.
    pub union_kind: Option<HirUnionKind>,
    /// `#[niche(..)]` (spec 2.7.4): bit patterns the single field never
    /// holds. Empty without the attribute.
    pub niche: Vec<NicheArg>,
}

/// `#[repr(..)]` of a struct, enum or union (spec 6.2.2). The default
/// layout is already C's (declaration order, natural alignment), so `C`
/// changes nothing there.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Repr {
    pub c: bool,
    /// One field, passed and laid out as that field.
    pub transparent: bool,
    /// No padding, alignment 1.
    pub packed: bool,
    /// `align(N)`: at least `N`-aligned; 0 without.
    pub align: u32,
    /// An enum's tag type (`u8` .. `i64`).
    pub int: Option<PrimTy>,
}

/// One `#[niche(..)]` value, read against the field's primitive type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NicheVal {
    Int(i128),
    /// The field type's `MIN` / `MAX`.
    Min,
    Max,
    /// The canonical quiet NaN / `±∞` of the field's float type.
    Nan,
    Inf,
    NegInf,
}

/// One `#[niche(..)]` argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NicheArg {
    Val(NicheVal),
    /// Inclusive bounds; an open end is `Min` / `Max`.
    Range(NicheVal, NicheVal),
}

/// A `union`'s storage. `#[repr(C)]` or a non-primitive field forces
/// the byte array, so the layout matches C.
#[derive(Clone, Debug)]
pub enum UnionStorage {
    /// One primitive wide enough for every field, accessed by cast;
    /// stays in registers.
    WidestPrim(PrimTy),
    /// Bytes as large and aligned as the largest field, laid out by MIR
    /// (`rokc_mir::ty::union_storage`); words that may hold a reference
    /// are scanned as ambiguous.
    ByteArray,
}

#[derive(Clone, Debug)]
pub struct HirUnionKind {
    pub storage: UnionStorage,
    /// Declared fields and their types: the cast targets at access sites.
    pub aliases: Vec<(String, HirTy)>,
    pub is_repr_c: bool,
}

#[derive(Clone, Debug)]
pub struct HirField {
    pub name: String,
    pub ty: HirTy,
    /// Default for a field a struct literal omits. Kept as AST and
    /// lowered at each literal; it is const, so re-evaluating it has no
    /// side effects.
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
    pub facts: FnFacts,
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
    /// A `[ref]`-captured variable: the local holds its one-element
    /// `GcBuf` cell (`ty`), shared with the closures.
    pub boxed: bool,
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
    // `arr[index] = value;` — array-element write; with a `path` of
    // field indices, into the array field `array_local.f.g` in place.
    ArrayAssign {
        array_local: LocalId,
        path: Vec<u32>,
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
    /// A call to a never-returning runtime hook (`rok_panic_at` for a failed
    /// `try!`, `rok_uncaught_error_at` for an error escaping a throwing
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
    /// Binary op on two operands of one primitive type, bypassing trait
    /// dispatch (same result).
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
    /// A function as a value (also lifted closure bodies).
    FnRef(FunctionId),
    /// Indirect call through a function-typed expression.
    CallIndirect {
        callee: Box<HirExpr>,
        args: Vec<HirExpr>,
        ret_ty: HirTy,
    },
    /// `expr as Type`; codegen picks the op from `from_ty` / `to_ty`.
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
    /// `addr_of(place)` (`rok::bare`): the address (`usize`) of a local,
    /// or of a field / array element inside one; the local lives in
    /// memory from then on.
    AddrOf {
        place: Box<HirExpr>,
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
    /// Cast a value into a union's `__data` storage: a numeric cast for
    /// `WidestPrim`, a store through memory for `ByteArray`.
    UnionWrite {
        struct_id: StructId,
        from_ty: HirTy,
        storage_ty: HirTy,
        value: Box<HirExpr>,
    },
    /// Read a declared field back out of a union's `__data` storage.
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

/// A lowered pattern.
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
    /// A pattern on one member of a sum or `any` (`'a'` on `char | none`,
    /// `E { msg }` on `any Error`): the tag test, then `sub` on the
    /// member's payload.
    SumMember {
        sum_ty: HirTy,
        variant_index: u32,
        payload_ty: HirTy,
        sub: Box<HirPattern>,
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
            | Self::SumVariant { .. }
            | Self::SumMember { .. } => false,
        }
    }
}

thread_local! {
    /// Each struct's and enum's build-independent name, by id
    /// (`[structs, enums]`), for `HirTy::stable_key`.
    static TYPE_NAMES: std::cell::RefCell<[Vec<String>; 2]> =
        const { std::cell::RefCell::new([Vec::new(), Vec::new()]) };
}

/// Forget the type names of an earlier compile.
pub(crate) fn clear_type_names() {
    TYPE_NAMES.with(|n| *n.borrow_mut() = [Vec::new(), Vec::new()]);
}

/// Name struct (or `enum_`) `id`: its full path, and a generic
/// instance's arguments by their own stable keys. Called when the id is
/// handed out, before any type names it.
pub(crate) fn name_type(enum_: bool, id: u32, base: &str, args: &[HirTy]) {
    let name = if args.is_empty() {
        base.to_owned()
    } else {
        let args: Vec<String> = args.iter().map(HirTy::stable_key).collect();
        format!("{base}<{}>", args.join(", "))
    };
    set_type_name(enum_, id, name);
}

/// Set the `name_type` of struct (or `enum_`) `id`.
pub(crate) fn set_type_name(enum_: bool, id: u32, name: String) {
    TYPE_NAMES.with(|n| {
        let v = &mut n.borrow_mut()[usize::from(enum_)];
        let id = id as usize;
        if v.len() <= id {
            v.resize(id + 1, String::new());
        }
        v[id] = name;
    });
}

/// The build-independent name of struct (or `enum_`) `id` (`name_type`),
/// while its compile's types are named.
#[must_use]
pub fn type_name(enum_: bool, id: u32) -> Option<String> {
    TYPE_NAMES.with(|n| {
        n.borrow()[usize::from(enum_)]
            .get(id as usize)
            .filter(|s| !s.is_empty())
            .cloned()
    })
}

/// A trait as a bound names it or an impl provides it, `Get<i32, Item =
/// u8>` (spec 2.8, 2.10): the trait's full path, its positional
/// arguments and its associated-type bindings (sorted by name).
#[derive(Clone, Debug, PartialEq)]
pub struct TraitRef {
    pub path: String,
    pub args: Vec<HirTy>,
    pub binds: Vec<(String, HirTy)>,
}

impl TraitRef {
    #[must_use]
    pub fn new(path: String, args: Vec<HirTy>, mut binds: Vec<(String, HirTy)>) -> Self {
        binds.sort_by(|a, b| a.0.cmp(&b.0));
        Self { path, args, binds }
    }

    /// The trait alone, no arguments.
    #[must_use]
    pub fn plain(path: &str) -> Self {
        Self::new(path.to_owned(), Vec::new(), Vec::new())
    }

    /// No arguments and no bindings.
    #[must_use]
    pub fn is_plain(&self) -> bool {
        self.args.is_empty() && self.binds.is_empty()
    }

    /// Does an impl providing `self` (its arguments and associated types
    /// all given) meet bound `want`? `want` may leave the arguments and
    /// any binding out.
    #[must_use]
    pub fn satisfies(&self, want: &Self) -> bool {
        self.path == want.path
            && (want.args.is_empty() || want.args == self.args)
            && want.binds.iter().all(|b| self.binds.contains(b))
    }

    /// `Path<A, Name = B>`, each type rendered by `name`.
    pub fn render(&self, path: &str, name: impl Fn(&HirTy) -> String) -> String {
        if self.is_plain() {
            return path.to_owned();
        }
        let parts: Vec<String> = self
            .args
            .iter()
            .map(&name)
            .chain(self.binds.iter().map(|(n, t)| format!("{n} = {}", name(t))))
            .collect();
        format!("{path}<{}>", parts.join(", "))
    }
}

/// What a `fn` type promises beyond its signature.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FnBounds {
    /// `+ Send + Sync`: sorted auto-trait keys.
    pub auto: Vec<String>,
    /// `unsafe fn(..)` (spec 4.15): calling it needs an unsafe scope.
    pub unsafe_fn: bool,
    /// `extern "C" fn(..)` (spec 5.9.4): a thin C function pointer.
    pub c_abi: bool,
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
    /// `any` / `any Tr` / `any (A + B)`: the bounds in canonical order
    /// (`HirTy::any`); plain `any` has none.
    /// Tag + heap payload; the tag numbers concrete types program-wide.
    /// Construction reuses `SumWrap` (variant index = tag) and narrowing
    /// reuses `SumVariant` with this as `sum_ty`.
    AnyTrait(Vec<TraitRef>),
    /// A type name not resolved (yet): a type parameter, `Self`, or an
    /// unknown name reported later.
    Path(Vec<String>),
    /// The type of `none` (spec 2.13).
    None,
    /// A const generic argument (spec 2.11) in a type substitution: its
    /// value, and the parameter's declared type once known.
    Const(i128, Option<PrimTy>),
    /// A const parameter not bound yet (argument hints before inference).
    OpenConst(String),
    /// What a `rethrows` error parameter binds to for a non-throwing
    /// argument.
    NoThrow,
    /// An inference variable of an un-annotated `let` (`lower::infer`).
    Var(u32),
    Sum(Vec<HirTy>),
    Tuple(Vec<HirTy>),
    // Resolved struct (Path → known def).
    Struct(StructId),
    // Resolved enum.
    Enum(EnumId),
    // Fixed-size array `[T; N]`.
    Array(Box<HirTy>, u32),
    // `fn(A, B) -> R` — first-class function pointer, with its bounds.
    Fn(Vec<HirTy>, Box<HirTy>, FnBounds),
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
    pub const fn is_c_fn(&self) -> bool {
        matches!(self, Self::Fn(_, _, b) if b.c_abi)
    }

    /// `any (A + B)`: the bounds deduplicated in one canonical order
    /// (by `stable_key` rendering), so `any (A + B)` is `any (B + A)`.
    #[must_use]
    pub fn any(mut bounds: Vec<TraitRef>) -> Self {
        bounds.sort_by_cached_key(|b| b.render(&b.path, Self::stable_key));
        bounds.dedup();
        Self::AnyTrait(bounds)
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
    /// The order: `none` last, the rest by `stable_key` — their
    /// structure with structs and enums by full name (and generic
    /// arguments), so the tags agree across separately compiled
    /// packages (a prebuilt library and its users).
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
        out.sort_by_cached_key(|t| (t.is_none(), t.stable_key()));
        out.dedup();
        if out.len() == 1 {
            out.pop().expect("one member")
        } else {
            Self::Sum(out)
        }
    }

    /// The structural rendering with each struct / enum id replaced by
    /// its name (`name_type`): the same in every build.
    #[must_use]
    pub fn stable_key(&self) -> String {
        let text = format!("{self:?}");
        TYPE_NAMES.with(|names| {
            let names = names.borrow();
            let mut out = String::with_capacity(text.len());
            let mut rest = text.as_str();
            loop {
                let next = [("Struct(StructId(", 0), ("Enum(EnumId(", 1)]
                    .into_iter()
                    .filter_map(|(p, k)| rest.find(p).map(|at| (at, p, k)))
                    .min();
                let Some((at, p, k)) = next else { break };
                let tail = &rest[at + p.len()..];
                let n = tail.bytes().take_while(u8::is_ascii_digit).count();
                let name = tail[..n]
                    .parse::<usize>()
                    .ok()
                    .and_then(|id| names[k].get(id))
                    .filter(|s| !s.is_empty() && tail[n..].starts_with("))"));
                out.push_str(&rest[..at]);
                if let Some(name) = name {
                    let kind = if k == 0 { "Struct" } else { "Enum" };
                    out.push_str(&format!("{kind}({name})"));
                    rest = &tail[n + 2..];
                } else {
                    out.push_str(&rest[at..at + p.len() + n]);
                    rest = &tail[n..];
                }
            }
            out.push_str(rest);
            out
        })
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
    pub const fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }

    /// A const argument's value and declared type.
    #[must_use]
    pub const fn as_const(&self) -> Option<(i128, Option<PrimTy>)> {
        match self {
            Self::Const(v, p) => Some((*v, *p)),
            _ => None,
        }
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
        | HirExprKind::AddrOf { place: x }
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

/// Pre-order visit of every expression in `b`, mutably.
pub fn each_block_mut(b: &mut HirBlock, f: &mut impl FnMut(&mut HirExpr)) {
    for s in &mut b.stmts {
        match s {
            HirStmt::Let { init: e, .. }
            | HirStmt::Assign { value: e, .. }
            | HirStmt::StaticAssign { value: e, .. }
            | HirStmt::Expr(e)
            | HirStmt::Panic(e)
            | HirStmt::Return(Some(e))
            | HirStmt::Break { value: Some(e), .. } => each_expr_mut(e, f),
            HirStmt::ArrayAssign { index, value, .. } => {
                each_expr_mut(index, f);
                each_expr_mut(value, f);
            }
            HirStmt::Return(None) | HirStmt::Break { .. } | HirStmt::Continue { .. } => {}
        }
    }
    if let Some(t) = &mut b.trailing {
        each_expr_mut(t, f);
    }
}

/// Pre-order visit of `e` and its subexpressions, mutably.
pub fn each_expr_mut(e: &mut HirExpr, f: &mut impl FnMut(&mut HirExpr)) {
    f(e);
    let mut go = |x: &mut HirExpr| each_expr_mut(x, f);
    match &mut e.kind {
        HirExprKind::Const(_)
        | HirExprKind::Local(_)
        | HirExprKind::StaticRef(_)
        | HirExprKind::UnresolvedPath(_)
        | HirExprKind::FnRef(_)
        | HirExprKind::SizeOf { .. } => {}
        HirExprKind::Block(b) => each_block_mut(b, f),
        HirExprKind::Loop { body, .. } => each_block_mut(body, f),
        HirExprKind::While { cond, body, .. } => {
            go(cond);
            each_block_mut(body, f);
        }
        HirExprKind::If {
            cond,
            then_block,
            else_branch,
        } => {
            go(cond);
            each_block_mut(then_block, f);
            if let Some(e) = else_branch {
                each_expr_mut(e, f);
            }
        }
        HirExprKind::Match { scrutinee, arms } => {
            go(scrutinee);
            for a in arms {
                if let Some(g) = &mut a.guard {
                    each_expr_mut(g, f);
                }
                each_expr_mut(&mut a.body, f);
            }
        }
        HirExprKind::PrimBinOp { lhs: a, rhs: b, .. }
        | HirExprKind::WithField {
            target: a,
            value: b,
            ..
        }
        | HirExprKind::RawWrite {
            addr: a, value: b, ..
        }
        | HirExprKind::BufGet {
            buf: a, index: b, ..
        }
        | HirExprKind::ArrayIndex {
            array: a, index: b, ..
        } => {
            go(a);
            go(b);
        }
        HirExprKind::PrimUnaryOp { operand: x, .. }
        | HirExprKind::Cast { operand: x, .. }
        | HirExprKind::ClosureValue { env: x, .. }
        | HirExprKind::FieldRead { target: x, .. }
        | HirExprKind::TupleField { target: x, .. }
        | HirExprKind::ArrayRepeat { value: x, .. }
        | HirExprKind::BufNew { len: x, .. }
        | HirExprKind::RawRead { addr: x, .. }
        | HirExprKind::AddrOf { place: x }
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
        | HirExprKind::CoroNew { args: xs, .. } => xs.iter_mut().for_each(go),
        HirExprKind::CallIndirect {
            callee: c, args, ..
        }
        | HirExprKind::CallClosure {
            closure: c, args, ..
        } => {
            go(c);
            args.iter_mut().for_each(go);
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
            args.iter_mut().for_each(go);
        }
        HirExprKind::MlirOp { args, regions, .. } => {
            args.iter_mut().for_each(&mut go);
            regions.iter_mut().for_each(|(_, b)| go(b));
        }
    }
}

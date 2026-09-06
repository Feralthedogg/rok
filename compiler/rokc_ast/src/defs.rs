//! Item / statement / expression / pattern / type AST.
//!
//! No operator enums. Binary/unary expressions carry the lexical operator
//! symbol; trait resolution happens in a later pass.

use rokc_core::Visibility;
use rokc_diagnostic::Span;

use crate::{Attribute, Item, Literal};

#[derive(Clone, Debug)]
pub struct FnDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub generics: Generics,
    pub params: Vec<Param>,
    pub ret_ty: Option<Ty>,
    pub body: Option<Block>,
    pub is_async: bool,
    pub is_generator: bool,
    pub throws: ThrowsKind,
    pub where_clause: Vec<WherePred>,
    pub span: Span,
}

/// Error type written for an untyped `throws` (= `throws (any Error)`).
pub const UNTYPED_THROWS_MARK: &str = "#throws";

/// `throws` clause of a fn signature (spec 4.14). `rethrows` is
/// desugared by the parser into `Typed` over synthetic generic error
/// parameters (`#E0`, ...), one per throwing fn-typed parameter.
#[derive(Clone, Debug, Default)]
pub enum ThrowsKind {
    #[default]
    None,
    /// Bare `throws` = `throws (any Error)`; the parser rewrites it to
    /// `Typed([UNTYPED_THROWS_MARK])`.
    Untyped,
    /// `throws (A | B)` — the listed types form the error sum.
    Typed(Vec<Ty>),
}

#[derive(Clone, Debug, Default)]
pub struct Generics {
    pub params: Vec<GenericParam>,
}

#[derive(Clone, Debug)]
pub enum GenericParam {
    /// `T`, `T: Bound`, or `T = Default` (spec 2.10.5). The `default`
    /// type is applied during instantiation when no concrete type was
    /// supplied and the generic context provides no inference signal.
    Type {
        name: String,
        bounds: Vec<Ty>,
        default: Option<Ty>,
    },
    Const {
        name: String,
        ty: Ty,
    },
}

#[derive(Clone, Debug)]
pub struct WherePred {
    pub ty: Ty,
    pub bounds: Vec<Ty>,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: Option<Ty>,
    pub by_ref: bool,
    pub default: Option<Expr>,
    pub variadic: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub trailing: Option<Box<Expr>>,
    pub span: Span,
    /// Optional `'label:` prefix. When set, `break 'label value` inside
    /// the block exits the block with `value`. Loop / `while` / `for`
    /// carry the label on their own variant; this field is for plain
    /// labeled blocks `'b: { ... }`.
    pub label: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    /// `let name [: ty] = init;` — fresh binding.
    Let {
        name: String,
        ty: Option<Ty>,
        init: Expr,
    },
    /// `let (a, b, ...) [: ty] = init;` — tuple destructure.
    /// `_` in `names` is the discard placeholder.
    /// `rest`: `Some((index_into_names, optional_name))` records a `..` or
    /// `..name` rest-pattern (spec 3.15.3). The index is the position
    /// among `names` *before* which the rest splice slots in, e.g.
    ///   `(first, ..rest)`              → `names=["first"], rest=(1, Some("rest"))`
    ///   `(..init, last)`               → `names=["last"], rest=(0, Some("init"))`
    ///   `(head, ..mid, tail)`          → `names=["head","tail"], rest=(1, Some("mid"))`
    ///   `(..)`                         → `names=[], rest=(0, None)`
    LetTuple {
        names: Vec<String>,
        rest: Option<(usize, Option<String>)>,
        ty: Option<Ty>,
        init: Expr,
    },
    /// `let StructName { f1, f2: alias, .. } [: ty] = init;` — struct destructure.
    /// Each `(field_name, bind_name)` pair lifts the named field into a
    /// fresh local. `bind_name` defaults to `field_name` when no rename
    /// was written. `rest` is true if the pattern ended in `..`.
    LetStruct {
        path: Path,
        fields: Vec<(String, String)>,
        rest: bool,
        ty: Option<Ty>,
        init: Expr,
    },
    /// `name = expr;` — reassignment (no `let`).
    Assign(Expr, Expr),
    /// `name op= expr;` — `op` is the lexical compound symbol (`+=` etc.).
    CompoundAssign {
        target: Expr,
        op: String,
        value: Expr,
    },
    /// Item declaration appearing inside a block / module body.
    Item(Item),
    /// Bare expression statement (terminated with `;`).
    Expr(Expr),
    /// Trailing expression that yields the block's value (no `;`).
    Trailing(Expr),
    Return(Option<Expr>),
    Break {
        label: Option<String>,
        value: Option<Expr>,
    },
    Continue {
        label: Option<String>,
    },
    Throw(Expr),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Literal(Literal),
    /// Bare identifier reference (variable or item).
    Path(Path),
    SelfLower,
    SelfUpper,
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    Dict(Vec<(Expr, Expr)>),
    Set(Vec<Expr>),
    Block(Block),
    If {
        cond: Box<Expr>,
        then_branch: Block,
        else_branch: Option<Box<Expr>>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Loop {
        label: Option<String>,
        body: Block,
    },
    While {
        label: Option<String>,
        cond: Box<Expr>,
        body: Block,
    },
    For {
        label: Option<String>,
        pat: Pattern,
        iter: Box<Expr>,
        body: Block,
    },
    /// Prefix `try e` / `try? e` / `try! e`: marks the throwing calls in
    /// `e` (everything to its right).
    Try {
        kind: TryKind,
        operand: Box<Expr>,
    },
    /// Postfix `e catch pat { .. } ... finally { .. }` (either part may
    /// be absent, not both). `try { .. } catch ..` is a `Catch` over a
    /// `Try` of a block.
    Catch {
        body: Box<Expr>,
        catches: Vec<CatchArm>,
        finally: Option<Block>,
    },
    /// `let pat = expr else { ... };`
    LetElse {
        pat: Pattern,
        ty: Option<Ty>,
        init: Box<Expr>,
        else_body: Block,
    },
    /// Infix operator. `op` is the lexeme (e.g. `"+"`, `"<="`, `".+"`,
    /// `"≤"`); resolved to a stdlib trait method later.
    OpInfix {
        op: String,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// Prefix operator (`!`, `-`, `~`, ...).
    OpPrefix {
        op: String,
        operand: Box<Expr>,
    },
    /// Postfix operator (registered via `#[postfix]`).
    OpPostfix {
        op: String,
        operand: Box<Expr>,
    },
    Cast(Box<Expr>, Ty),
    Is(Box<Expr>, Pattern),
    /// `expr.field`.
    Field(Box<Expr>, String),
    /// Tuple field access: `expr.0`, `expr.1` ...
    TupleField(Box<Expr>, u32),
    /// `expr.method(args...)`
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        type_args: Vec<Ty>,
        args: Vec<CallArg>,
        trailing_closure: Option<Box<Expr>>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<CallArg>,
        trailing_closure: Option<Box<Expr>>,
    },
    Index(Box<Expr>, Box<Expr>),
    Slice {
        target: Box<Expr>,
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        step: Option<Box<Expr>>,
    },
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        inclusive: bool,
    },
    /// `x?.tail` — language-level sum-type-aware access (desugars to match).
    QuestionDot(Box<Expr>, AccessTail),
    /// `lhs ?? rhs` — language-level sum-type-aware coalesce.
    NullishCoalesce(Box<Expr>, Box<Expr>),
    /// `expr?` — postfix early-return for sum types. Yields the
    /// non-none value or `return none` from the enclosing function.
    TryQ(Box<Expr>),
    Closure {
        captures: Vec<CaptureSpec>,
        params: Vec<Param>,
        ret_ty: Option<Ty>,
        body: Box<Expr>,
        is_async: bool,
        is_generator: bool,
    },
    Await(Box<Expr>),
    Yield(Option<Box<Expr>>),
    AsyncBlock(Block),
    YieldBlock(Block),
    AsyncYieldBlock(Block),
    StructInit {
        path: Path,
        fields: Vec<(String, Expr)>,
        spread: Option<Box<Expr>>,
    },
    /// Spread expression for `..arg` in call sites or struct init.
    Spread(Box<Expr>),
    /// Discard expression `_ = expr`.
    Discard(Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum AccessTail {
    Field(String),
    TupleField(u32),
    Method {
        method: String,
        type_args: Vec<Ty>,
        args: Vec<CallArg>,
    },
    Index(Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum CallArg {
    Positional(Expr),
    Named { name: String, value: Expr },
    Spread(Expr),
}

#[derive(Clone, Debug)]
pub enum CaptureSpec {
    Value(String),
    Ref(String),
}

#[derive(Clone, Debug)]
pub struct MatchArm {
    pub pat: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TryKind {
    /// `try e` — errors propagate.
    Plain,
    /// `try? e` — errors become `none`.
    Optional,
    /// `try! e` — errors panic.
    Force,
}

/// `catch pat { body }`; an omitted pattern is `_`.
#[derive(Clone, Debug)]
pub struct CatchArm {
    pub pat: Pattern,
    pub body: Block,
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum PatternKind {
    Wildcard,
    Binding {
        name: String,
        sub: Option<Box<Pattern>>,
    },
    Literal(Literal),
    Range {
        start: Option<Literal>,
        end: Option<Literal>,
        inclusive: bool,
    },
    /// `name: T` — type-narrowing pattern.
    TypeCheck {
        binder: Option<String>,
        ty: Ty,
    },
    Tuple(Vec<Pattern>),
    /// `..rest` (rest pattern).
    Rest(Option<String>),
    Struct {
        path: Path,
        fields: Vec<FieldPattern>,
        rest: bool,
    },
    EnumVariant {
        path: Path,
        args: Vec<Pattern>,
    },
    Or(Vec<Pattern>),
}

#[derive(Clone, Debug)]
pub struct FieldPattern {
    pub name: String,
    pub pat: Option<Pattern>,
}

#[derive(Clone, Debug)]
pub struct Path {
    pub segments: Vec<PathSegment>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct PathSegment {
    pub name: String,
    pub generics: Vec<Ty>,
}

#[derive(Clone, Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TyKind {
    /// Path type (`i32`, `List<T>`, `std::time::Duration`).
    Path(Path),
    /// Sum type `A | B | C`.
    Sum(Vec<Ty>),
    /// Tuple `(A, B)`.
    Tuple(Vec<Ty>),
    /// Function type `fn(A, B) -> R`. A throwing one has a `Throws`
    /// return type.
    Fn(Vec<Ty>, Box<Ty>),
    /// Return slot of `fn(..) throws (err) -> ok`; only appears as the
    /// return type of `Fn`.
    Throws { ok: Box<Ty>, err: Box<Ty> },
    /// Fixed-size array `[T; N]`.
    Array(Box<Ty>, ConstExpr),
    /// `any` slot.
    Any,
    /// `any Tr` / `any (A + B)` — a dynamic slot bounded by traits (D4).
    AnyTrait(Vec<Path>),
    /// `none` (used inside sum types).
    None,
    /// Self type.
    SelfUpper,
}

/// Const-expression placeholder for array length / const generics.
#[derive(Clone, Debug)]
pub enum ConstExpr {
    Literal(Literal),
    Path(Path),
    Expr(Box<Expr>),
}

#[derive(Clone, Debug)]
pub struct StructDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub generics: Generics,
    pub kind: StructKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StructKind {
    Unit,
    Tuple(Vec<TupleField>),
    Named(Vec<NamedField>),
}

#[derive(Clone, Debug)]
pub struct NamedField {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub ty: Ty,
    pub default: Option<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct TupleField {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct EnumDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub generics: Generics,
    pub variants: Vec<EnumVariant>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct EnumVariant {
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub kind: EnumVariantKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum EnumVariantKind {
    Unit,
    Tuple(Vec<Ty>),
    Named(Vec<NamedField>),
    Value(Expr),
}

#[derive(Clone, Debug)]
pub struct UnionDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub generics: Generics,
    pub fields: Vec<NamedField>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct TraitDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub generics: Generics,
    pub supertraits: Vec<Ty>,
    pub items: Vec<TraitItem>,
    pub where_clause: Vec<WherePred>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TraitItem {
    Method(FnDef),
    AssocType {
        name: String,
        bounds: Vec<Ty>,
        default: Option<Ty>,
    },
    Const(ConstDef),
}

#[derive(Clone, Debug)]
pub struct ImplDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub generics: Generics,
    pub trait_path: Option<Path>,
    pub self_ty: Ty,
    pub where_clause: Vec<WherePred>,
    pub items: Vec<ImplItem>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ImplItem {
    Method(FnDef),
    AssocType { name: String, ty: Ty },
    Const(ConstDef),
}

#[derive(Clone, Debug)]
pub struct ConstDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub ty: Ty,
    pub value: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct StaticDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub ty: Ty,
    pub value: Option<Expr>,
    pub is_mut: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct TypeAliasDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub generics: Generics,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct ModDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: String,
    pub items: Option<Vec<Item>>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct UseDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub tree: UseTree,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct UseTree {
    pub prefix: Path,
    pub kind: UseTreeKind,
}

#[derive(Clone, Debug)]
pub enum UseTreeKind {
    Simple(Option<String>),
    Glob,
    GlobRecursive,
    Group(Vec<UseTree>),
}

#[derive(Clone, Debug)]
pub struct ExternBlock {
    pub attrs: Vec<Attribute>,
    pub abi: String,
    pub items: Vec<ExternItem>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExternItem {
    Fn(FnDef),
    Static(StaticDef),
}

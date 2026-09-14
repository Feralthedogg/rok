//! Item / statement / expression / pattern / type AST.
//!
//! No operator enums. Binary/unary expressions carry the lexical operator
//! symbol; trait resolution happens in a later pass.

use rokc_core::Visibility;
use rokc_diagnostic::Span;

use crate::{AttrArg, AttrBody, Attribute, Item, Literal};

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
    /// `unsafe fn` (spec 4.15.1): callers need an unsafe scope.
    pub is_unsafe: bool,
    pub throws: ThrowsKind,
    pub where_clause: Vec<WherePred>,
    pub span: Span,
}

/// Marker attribute of an `extern "C" fn f(..) { .. }` definition
/// (spec 5.9.10).
pub const EXTERN_C_FN_ATTR: &str = "#extern_c";

/// Marker attribute of a nested `fn` statement (spec 4.10): the fn is
/// lifted to a module item named by the attribute's string (`outer#f`);
/// a second `true` argument marks a sibling visible from an enclosing
/// block rather than one declared here.
pub const NESTED_FN_ATTR: &str = "#nested_fn";

/// Marker attribute of a `const fn` (spec 5.2.5): callable in const
/// contexts, evaluated at compile time there.
pub const CONST_FN_ATTR: &str = "#const_fn";

/// Marker attribute of a C variadic declaration `fn printf(fmt: str, ...)`
/// (spec 8.6.10).
pub const C_VARIADIC_ATTR: &str = "#c_variadic";

/// Bound-list marker of an `unsafe fn(..)` type (`#` cannot start a
/// user identifier).
pub const UNSAFE_FN_MARK: &str = "#unsafe";

/// Bound-list marker of an `extern "C" fn(..)` type: a thin C function
/// pointer called with the C ABI (spec 5.9.4).
pub const C_FN_MARK: &str = "#extern_c";

/// First path segment of a qualified path `<T as Tr>::X` (spec 2.13.4):
/// its generics are `[T, Tr]`.
pub const QPATH_MARK: &str = "#as";

/// Sum member `#nest<X>`: a substituted generic member.
///
/// A generic alias's parameter or an associated type replaced by its
/// argument `X` inside a sum (`Maybe<i32 | none>`
/// with `type Maybe<T> = T | none`, `Self::Item | none`). Like a type
/// parameter, `X` stays one member, so an overlap with the sum's own
/// members keeps it a nested layer (spec 2.6.4).
pub const NEST_MARK: &str = "#nest";

/// Method name of the `using` desugar's release call (`x.#drop()`):
/// `Drop::drop`, exempt from the direct-call ban (spec 2.13.4).
pub const USING_DROP_METHOD: &str = "#drop";

/// Error type written for an untyped `throws` (= `throws (any Error)`).
pub const UNTYPED_THROWS_MARK: &str = "#throws";

/// An associated-type binding `Name = Ty` among a trait's generic
/// arguments (`Iterator<Item = i32>`, spec 2.1 `trait_arg`) is carried
/// as the path type `=Name<Ty>` (`=` cannot start an identifier).
#[must_use]
pub fn assoc_binding(name: &str, ty: Ty) -> Ty {
    let span = ty.span;
    Ty {
        kind: TyKind::Path(Path {
            segments: vec![PathSegment {
                name: format!("={name}"),
                generics: vec![ty],
            }],
            span,
        }),
        span,
    }
}

/// `Name = Ty` if `ty` is an [`assoc_binding`].
#[must_use]
pub fn as_assoc_binding(ty: &Ty) -> Option<(&str, &Ty)> {
    match &ty.kind {
        TyKind::Path(p) => match p.segments.as_slice() {
            [seg] => Some((seg.name.strip_prefix('=')?, seg.generics.first()?)),
            _ => None,
        },
        _ => None,
    }
}

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
    /// `'b: { ... }` label; `break 'b value` exits the block with `value`.
    /// Loops carry their label on their own variant.
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
    /// `let pat = init;` for any irrefutable pattern (the `pat` of
    /// `let name @ pat = ..`, after `name` is bound).
    LetPattern {
        pat: Pattern,
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

/// One `#[literal]` handler a literal matched, with its captures.
#[derive(Clone, Debug)]
pub struct LitCand {
    /// The handler's absolute path.
    pub handler: Path,
    pub args: Vec<LitArg>,
    pub priority: i64,
    /// The `#[literal]` attribute.
    pub reg: Span,
}

/// A handler argument: one capture, or a repetition's items (a
/// variadic `...T` parameter's arguments, else one array argument).
#[derive(Clone, Debug)]
pub enum LitArg {
    One(Expr),
    Many(Vec<Expr>),
}

impl LitArg {
    #[must_use]
    pub fn exprs(&self) -> &[Expr] {
        match self {
            Self::One(e) => std::slice::from_ref(e),
            Self::Many(es) => es,
        }
    }
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
    /// `[v; N]` — `v` repeated `N` times, a `[T; N]` (spec 2.11).
    ArrayRepeat {
        value: Box<Expr>,
        len: ConstExpr,
    },
    Dict(Vec<(Expr, Expr)>),
    Set(Vec<Expr>),
    /// Source matched by registered `#[literal(..)]` patterns (spec
    /// 6.5.4): one candidate per matching handler; HIR picks one by the
    /// slot's type, then priority (6.5.5).
    MagicLiteral(Vec<LitCand>),
    Block(Block),
    /// `unsafe { ... }` (spec 4.15.2).
    Unsafe(Block),
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
        /// `for await` over a `Stream` (spec 4.13.5).
        is_await: bool,
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
    /// `expr` resolved in `module`'s scope with no locals: a parameter /
    /// field default spliced into a use in another module (spec 4.2.3).
    InModule(String, Box<Expr>),
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
    /// `f"..."` (spec 1.7.3): literal runs and `{expr:spec}` holes,
    /// formatted by type in HIR (stdlib 2.10).
    FString(Vec<FStringPart>),
}

#[derive(Clone, Debug)]
pub enum FStringPart {
    /// Literal text as written (escapes not yet decoded, `{{` / `}}`
    /// folded).
    Lit(String),
    Hole {
        expr: Expr,
        /// The format spec after `:`; empty when there is none.
        spec: Vec<SpecPiece>,
    },
}

/// A piece of a format spec: text (`$$` folded to `$`) or a dynamic
/// `${expr}`.
#[derive(Clone, Debug)]
pub enum SpecPiece {
    Text(String),
    Expr(Expr),
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
    Named {
        name: String,
        value: Expr,
    },
    Spread(Expr),
    /// `f(ref x)`: pass the binding `x` by reference (spec 4.7.3).
    Ref(Expr),
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

impl Ty {
    /// `X` of a `#nest<X>` sum member (`NEST_MARK`).
    #[must_use]
    pub fn nest_inner(&self) -> Option<&Self> {
        match &self.kind {
            TyKind::Path(p) => match p.segments.as_slice() {
                [s] if s.name == NEST_MARK => s.generics.first(),
                _ => None,
            },
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub enum TyKind {
    /// Path type (`i32`, `List<T>`, `std::time::Duration`).
    Path(Path),
    /// Sum type `A | B | C`.
    Sum(Vec<Ty>),
    /// Tuple `(A, B)`.
    Tuple(Vec<Ty>),
    /// Function type `fn(A, B) -> R [+ Send + Sync]`. A throwing one has
    /// a `Throws` return type. The paths are auto-trait bounds.
    Fn(Vec<Ty>, Box<Ty>, Vec<Path>),
    /// Return slot of `fn(..) throws (err) -> ok`; only appears as the
    /// return type of `Fn`.
    Throws { ok: Box<Ty>, err: Box<Ty> },
    /// Fixed-size array `[T; N]`.
    Array(Box<Ty>, ConstExpr),
    /// `any` slot.
    Any,
    /// `any Tr` / `any (A + B)` — a dynamic slot bounded by traits.
    AnyTrait(Vec<Path>),
    /// `none` (used inside sum types).
    None,
    /// Self type.
    SelfUpper,
    /// `!` — the never type of a diverging function (`panic`, `exit`).
    Never,
    /// A const generic argument in a type-argument list (`Matrix<f64, 3, 4>`,
    /// `replicate::<i32, 8>`; spec 2.11.4).
    Const(ConstExpr),
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
    /// `where` predicates after the header (spec 2.10.4).
    pub where_clause: Vec<WherePred>,
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
    /// `where` predicates after the header (spec 2.10.4).
    pub where_clause: Vec<WherePred>,
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
    /// `where` predicates after the header (spec 2.10.4).
    pub where_clause: Vec<WherePred>,
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
    /// `const N: T;` / `const N: T = v;` (spec 2.8.3a).
    Const {
        name: String,
        ty: Ty,
        default: Option<Expr>,
    },
}

#[derive(Clone, Debug)]
pub struct ImplDef {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub generics: Generics,
    pub trait_path: Option<Path>,
    /// `unsafe impl` (manual `Send` / `Sync` opt-in).
    pub is_unsafe: bool,
    /// `impl !Tr for T` (auto-trait opt-out).
    pub negative: bool,
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
    /// `where` predicates after the header (spec 2.10.4).
    pub where_clause: Vec<WherePred>,
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

/// `(lifted name, inherited)` of a nested fn marker (`NESTED_FN_ATTR`).
#[must_use]
pub fn nested_marker_of(f: &FnDef) -> Option<(&str, bool)> {
    let a = f
        .attrs
        .iter()
        .find(|a| a.path.first().map(String::as_str) == Some(NESTED_FN_ATTR))?;
    let AttrBody::Args(args) = &a.body else {
        return None;
    };
    let AttrArg::Lit(Literal::Str(name)) = args.first()? else {
        return None;
    };
    Some((name.as_str(), args.len() > 1))
}

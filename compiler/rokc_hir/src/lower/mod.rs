//! AST → HIR lowering.

use std::collections::HashMap;

use rokc_ast::{
    Block, CallArg, EnumDef as AstEnumDef, EnumVariantKind as AstEnumVariantKind, Expr, ExprKind,
    FnDef, ImplItem as AstImplItem, Item, Literal as AstLit, MatchArm as AstMatchArm, Param,
    Path as AstPath, Pattern as AstPattern, PatternKind as AstPatternKind, Program, Stmt, StmtKind,
    StructDef as AstStructDef, StructKind as AstStructKind, Ty, TyKind as AstTyKind,
};
use rokc_core::Visibility;
use rokc_ir_common::{ConstVal, FunctionId, LocalId, PrimOp, PrimTy};
use rokc_parser::{Fixity, PrecTable};

use crate::ty::resolve_ty;
use crate::{
    EnumId, HirBlock, HirEnumDef, HirEnumVariant, HirExpr, HirExprKind, HirField, HirFunction,
    HirLocal, HirMatchArm, HirModule, HirParam, HirPattern, HirStaticDef, HirStmt, HirStructDef,
    HirTy, HirUnionKind, StructId, UnionStorage,
};

mod collect;
mod desugar;
mod expr;
mod mono;
mod pattern;
mod resolve;
mod throws;

use collect::collect_unknown_paths;
pub use collect::lower_full;
use desugar::{
    desugar_nullish_coalesce, desugar_question_dot, desugar_try_q, lower_closure_expr, lower_for,
};
use expr::{
    build_any_dispatchers, enum_base_name, field_access, has_int_suffix, hir_binop, hir_int,
    hir_local, lower_block, lower_cond, lower_expr, lower_loop_body, lower_sibling_pair,
    method_call_on, parse_char_literal, parse_int_literal, resolve_enum_variant, variant_arg_tys,
};
use mono::{
    bind_from_arg, generic_enum_variants, generic_struct_fields, generic_subst,
    instantiate_generic_enums, instantiate_generic_structs, lower_fn, monomorphize,
    resolve_in_mono, unify_param_ty_with,
};
use pattern::{int_fits, lower_match, lower_pattern};
use resolve::{
    bound_key, impl_bound_keys, impl_module, item_module, leaf_name, mangle_inst,
    method_target_for, module_display, module_of, resolve_name, resolve_ty_with_structs,
    split_trait_args, substitute_aliases, ty_mangle, visible_from,
};
use throws::{
    ErrFrame, adapt_fn_value, erase_unbound_errors, exit_through, finish_throwing_body, jump_index,
    lower_catch, lower_return, lower_throw, lower_try, main_frame, rethrows_value, sig_ret_ast,
    uncaught_in_main, unpack_call,
};

/// Outcome of glob resolution for one bare name. Single imports always
/// trump glob imports (per Rust 2018+ rules), so a Single hit returns
/// immediately. Glob hits are accumulated — two distinct globs landing
/// on the same suffix yield `Ambiguous`, which the caller surfaces as
/// a diagnostic.
enum LookupOutcome {
    None,
    Resolved(String),
    Ambiguous(Vec<String>),
}

/// A name table to resolve against: membership test plus (lazily) the
/// full key list, needed only by `use a::**` deep globs.
struct NameSet<'b> {
    exists: &'b dyn Fn(&str) -> bool,
    keys: &'b dyn Fn() -> Vec<String>,
}

/// Type-namespace index: every struct / union / enum / alias / trait
/// name (driver-qualified, e.g. `a::P`; generic bases unmangled) plus
/// `pub use` re-export aliases. All type paths — in signatures, fields,
/// struct literals, patterns, enum paths — resolve through `canon`.
struct TypeNames<'a> {
    names: std::collections::HashSet<String>,
    traits: std::collections::HashSet<String>,
    /// Every enum variant as `a::E::V` (generic bases unmangled). A
    /// variant is as visible as its enum (spec 5.6.9).
    variants: std::collections::HashSet<String>,
    /// `pub use` alias key → full path it re-exports.
    reexports: HashMap<String, String>,
    visibility: HashMap<String, Visibility>,
    uses: &'a crate::uses::UseTable,
    diags: std::cell::RefCell<Vec<rokc_diagnostic::RokDiagnostic>>,
}

impl TypeNames<'_> {
    fn canon(
        &self,
        segments: &[&str],
        module: &str,
        local_uses: &[Vec<crate::uses::UseEntry>],
    ) -> Option<String> {
        let exists = |k: &str| self.names.contains(k) || self.reexports.contains_key(k);
        let keys = || {
            let mut v: Vec<String> = self.names.iter().cloned().collect();
            v.extend(self.reexports.keys().cloned());
            v
        };
        let set = NameSet {
            exists: &exists,
            keys: &keys,
        };
        let mut full = match resolve_name(segments, module, local_uses, self.uses, &set) {
            Ok(r) => r?,
            Err(hits) => {
                self.error(format!(
                    "type name `{}` is ambiguous in module `{}` — multiple glob imports \
                     resolve it: {}",
                    segments.join("::"),
                    module_display(module),
                    hits.join(", ")
                ));
                hits.into_iter().next()?
            }
        };
        for _ in 0..8 {
            match self.reexports.get(&full) {
                Some(t) => full = t.clone(),
                None => break,
            }
        }
        if let Some(&vis) = self.visibility.get(&full) {
            let def_module = module_of(&full);
            if !visible_from(module, &def_module, vis) {
                self.error(format!(
                    "type `{full}` is private to module `{}` and cannot be used from \
                     `{}` (spec 5.6 — add `pub` to expose it)",
                    module_display(&def_module),
                    module_display(module)
                ));
            }
        }
        Some(full)
    }

    /// A bare (imported) variant name → its `a::E::V` key. Use entries
    /// may name the enum relative to the module (`use Result::{Ok}`).
    fn canon_variant(
        &self,
        segments: &[&str],
        module: &str,
        local_uses: &[Vec<crate::uses::UseEntry>],
    ) -> Option<String> {
        let full_key = |k: &str| -> Option<String> {
            if self.variants.contains(k) {
                return Some(k.to_owned());
            }
            let (ty, v) = k.rsplit_once("::")?;
            let segs: Vec<&str> = ty.split("::").collect();
            let e = self.canon(&segs, module, local_uses)?;
            let key = format!("{e}::{v}");
            self.variants.contains(&key).then_some(key)
        };
        let exists = |k: &str| full_key(k).is_some();
        let keys = || self.variants.iter().cloned().collect::<Vec<_>>();
        let set = NameSet {
            exists: &exists,
            keys: &keys,
        };
        match resolve_name(segments, module, local_uses, self.uses, &set) {
            Ok(r) => full_key(&r?),
            Err(hits) => {
                self.error(format!(
                    "variant name `{}` is ambiguous in module `{}` — multiple glob imports \
                     resolve it: {}",
                    segments.join("::"),
                    module_display(module),
                    hits.join(", ")
                ));
                full_key(hits.first()?)
            }
        }
    }

    /// Key under which `impl Trait for T` is recorded: a user trait's
    /// qualified name, else (bootstrap traits such as `core::ops::Add`)
    /// the last path segment.
    fn trait_key(&self, segments: &[&str], module: &str) -> String {
        self.canon(segments, module, &[])
            .filter(|full| self.traits.contains(full))
            .unwrap_or_else(|| segments.last().copied().unwrap_or_default().to_owned())
    }

    fn error(&self, msg: String) {
        self.diags
            .borrow_mut()
            .push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                msg,
            ));
    }
}

/// Where a type is being resolved: the name index plus the module the
/// referencing item lives in.
#[derive(Clone, Copy)]
struct Scope<'b> {
    names: &'b TypeNames<'b>,
    module: &'b str,
}

// AST → HIR. Three passes: register struct names, then function
// signatures, then lower function bodies.
#[must_use]
pub fn lower(program: &Program, prec: &PrecTable) -> HirModule {
    let empty_uses: crate::uses::UseTable = HashMap::new();
    let empty_reexports: Vec<crate::uses::ReExport> = Vec::new();
    lower_full(program, prec, &empty_uses, &empty_reexports)
}

#[must_use]
pub fn lower_with_uses(
    program: &Program,
    prec: &PrecTable,
    uses: &crate::uses::UseTable,
) -> HirModule {
    let empty_reexports: Vec<crate::uses::ReExport> = Vec::new();
    lower_full(program, prec, uses, &empty_reexports)
}

/// Per-method facts consulted at call sites: the module whose privacy
/// rules apply, the method's visibility, and the trait it implements
/// (operator dispatch requires a trait impl, spec 0.4 / 6.4).
struct MethodInfo {
    module: String,
    vis: Visibility,
    trait_name: Option<String>,
}

/// A method template monomorphized per call like a generic fn: `def`
/// carries the impl's generics followed by the method's own, and is
/// named `Base__method` in the impl's module.
struct GenericMethod {
    def: FnDef,
    /// The impl target (`Box<T>`): the type of `self` and of `Self`.
    self_ty: Ty,
    info: MethodInfo,
}

/// `impl<..> Tr for Target` (`Target` = `Box<T>`, or a bare `T` for a
/// blanket impl): applies to a type that matches `self_ty` and meets
/// the impl's bounds.
struct GenericTraitImpl {
    trait_key: String,
    /// `impl<T> Get<T> for Box<T> { type Item = T; }`: `[T]` and
    /// `[(Item, T)]`, resolved per instantiation.
    trait_args: Vec<Ty>,
    assoc: Vec<(String, Ty)>,
    generics: rokc_ast::Generics,
    where_clause: Vec<rokc_ast::WherePred>,
    self_ty: Ty,
    module: String,
    /// Method name → template (trait default bodies included).
    methods: HashMap<String, GenericMethod>,
}

/// Module-wide, read-only lowering environment shared by every function
/// body (plus the interior-mutable `sink`).
struct Env<'a> {
    fn_table: HashMap<String, FnSig>,
    method_table: HashMap<(MethodTarget, String), FunctionId>,
    method_info: HashMap<FunctionId, MethodInfo>,
    structs: Vec<HirStructDef>,
    enums: Vec<HirEnumDef>,
    struct_table: HashMap<String, StructId>,
    enum_table: HashMap<String, EnumId>,
    /// Module-level `const NAME: T = expr;` items. A bare `Path(NAME)`
    /// resolves to the const's value expression inlined at the use site.
    consts: HashMap<String, (Ty, Expr)>,
    /// Module-level type aliases. Walked over every `HirTy` produced
    /// from AST resolution so downstream code never sees `Path([alias])`.
    type_aliases: HashMap<String, HirTy>,
    /// Generic function templates keyed by name. `lower_call` queries
    /// this when the callee path matches a generic function.
    generic_fns: HashMap<String, &'a FnDef>,
    /// Generic struct templates, for instantiation inferred from a
    /// struct literal (`Box { v: 5 }` → `Box<i32>`).
    generic_structs: HashMap<String, &'a AstStructDef>,
    /// Generic enum templates, for instantiations that only surface
    /// under a monomorphization substitution (`Res<U, E>` with `U` bound).
    generic_enums: HashMap<String, &'a AstEnumDef>,
    /// Methods of generic impls (and generic methods), keyed by
    /// `(generic base of the impl target, method name)`. Called through
    /// `monomorphize` when `method_table` has no concrete entry.
    generic_methods: HashMap<(String, String), GenericMethod>,
    /// Generic trait impls, in source order.
    generic_trait_impls: Vec<GenericTraitImpl>,
    prec: &'a PrecTable,
    sink: ClosureSink,
    /// Visibility of every value-namespace item, keyed by full name.
    item_visibility: HashMap<String, Visibility>,
    /// Struct name → field name → visibility.
    field_vis: HashMap<String, HashMap<String, Visibility>>,
    /// Per-module `use` table — feeds into bare-name and unresolved
    /// path lookups. Empty when no `use` declarations were collected.
    uses: &'a crate::uses::UseTable,
    /// Set of `(Type, TraitName)` pairs declared by `impl Trait for Type`
    /// blocks. Consulted at monomorphization time to enforce generic
    /// trait bounds.
    impl_traits: std::collections::HashSet<(MethodTarget, String)>,
    /// Trait key → declared methods + supertraits (`any Tr` calls).
    trait_info: HashMap<String, TraitInfo>,
    /// Trait key → implementing types, in impl order (`any Tr` dispatch).
    trait_impl_tys: HashMap<String, Vec<HirTy>>,
    /// Module-level `static` items by name → declared type.
    statics: HashMap<String, HirTy>,
    names: TypeNames<'a>,
}

/// What `any Tr` needs from a trait declaration.
struct TraitInfo {
    methods: Vec<String>,
    supers: Vec<String>,
    /// Per method: what its signature (past `self`) depends on —
    /// `Self`, `Self::X` or a trait type parameter name. `any Tr` can
    /// only dispatch it when the bound fixes each (see `any_method_call`).
    needs: HashMap<String, Vec<String>>,
    /// Method declarations (signature when no concrete impl exists).
    decls: HashMap<String, rokc_ast::FnDef>,
    /// The trait's module (to resolve `decls`).
    module: String,
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum MethodTarget {
    Struct(StructId),
    Enum(EnumId),
    /// Mangled `HirTy` for impl targets that aren't a single struct or
    /// enum (Tuple/Array/Sum/Fn/Prim per spec 2.9.1 — `type_expr` is any
    /// type). Keyed by `ty_mangle` so two impls on the same shape land
    /// on the same target.
    Mangled(String),
}

enum MethodOrFn<'a> {
    Fn(&'a FnDef),
    /// `module` is where the body's names resolve: the impl's module
    /// for explicit methods, the trait's module for default bodies.
    Method {
        fn_def: &'a FnDef,
        self_ty: HirTy,
        module: String,
    },
}

/// Per-function signature used by lowering. Avoids re-resolving the AST
/// return type at every call site. `param_defaults` mirrors the function's
/// parameter list — each entry is `Some(expr)` if the parameter has a
/// default value the caller may omit, else `None`.
#[derive(Clone)]
struct FnSig {
    id: FunctionId,
    ret_ty: HirTy,
    param_defaults: Vec<Option<Expr>>,
    /// Resolved parameter types in declaration order. Used by `lower_call`
    /// to push expected-type hints into argument lowering — that's how an
    /// untyped closure (`apply(3, |x| { x*4 })`) picks up `i32` for `x`
    /// from the callee's `f: fn(i32) -> i32` signature.
    param_tys: Vec<HirTy>,
    /// Parameter names in declaration order. Used by `lower_call` to
    /// reorder named arguments (`f(name: 42)` per spec 4.1) into their
    /// positional slots.
    param_names: Vec<String>,
}

fn none_ty() -> HirTy {
    HirTy::Path(vec!["none".to_owned()])
}

/// The `none` sentinel type (spec 2.x `T | none`).
fn is_none_ty(ty: &HirTy) -> bool {
    matches!(ty, HirTy::Path(p) if p.as_slice() == ["none"])
}

// If `slot_ty` is a Sum and `value.ty` matches one of its variants,
// wrap the value into the sum's tagged-union representation.
fn wrap_into_sum(slot_ty: &HirTy, value: HirExpr) -> HirExpr {
    let HirTy::Sum(variants) = slot_ty else {
        return value;
    };
    let Some(idx) = sum_variant_index(variants, &value.ty) else {
        return value;
    };
    let span = value.span;
    let payload = if is_none_ty(&variants[idx]) {
        None
    } else {
        Some(Box::new(value))
    };
    HirExpr {
        kind: HirExprKind::SumWrap {
            sum_ty: slot_ty.clone(),
            variant_index: u32::try_from(idx).expect("variant overflow"),
            value: payload,
        },
        ty: slot_ty.clone(),
        span,
    }
}

// Locate `value_ty` in a sum's variant list (structural equality).
fn sum_variant_index(variants: &[HirTy], value_ty: &HirTy) -> Option<usize> {
    variants.iter().position(|v| v == value_ty)
}

/// Can a value of type `actual` flow into a slot of type `expected`
/// (after `wrap_into_sum`)? `Unknown` (an error was already reported)
/// and `Any` (untyped wildcard) are compatible with everything.
fn ty_compatible(expected: &HirTy, actual: &HirTy) -> bool {
    let all = |a: &[HirTy], b: &[HirTy]| {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| ty_compatible(x, y))
    };
    match (expected, actual) {
        (HirTy::Unknown | HirTy::Any, _) | (_, HirTy::Unknown | HirTy::Any) => true,
        (HirTy::Sum(vs), a) if !matches!(a, HirTy::Sum(_)) => sum_variant_index(vs, a).is_some(),
        (HirTy::Tuple(a), HirTy::Tuple(b)) | (HirTy::Sum(a), HirTy::Sum(b)) => all(a, b),
        (HirTy::Array(a, n), HirTy::Array(b, m)) => n == m && ty_compatible(a, b),
        (HirTy::Fn(a1, r1), HirTy::Fn(a2, r2)) => all(a1, a2) && ty_compatible(r1, r2),
        // Error types must match exactly: a wider error slot has another
        // carrier layout (fn values are adapted by `adapt_fn_value`).
        (HirTy::Throws { ok: o1, err: e1 }, HirTy::Throws { ok: o2, err: e2 }) => {
            ty_compatible(o1, o2) && (e1 == e2 || **e1 == HirTy::Unknown || **e2 == HirTy::Unknown)
        }
        _ => expected == actual,
    }
}

/// Wrap `value` into `slot` (sum injection) and report a type mismatch.
/// `what` names the slot for the diagnostic ("argument 1 of `f`").
fn coerce(ctx: &LowerCtx<'_>, slot: &HirTy, value: HirExpr, what: &dyn Fn() -> String) -> HirExpr {
    let value = adapt_fn_value(ctx, slot, value);
    let value = box_into_any(ctx, slot, value);
    let v = wrap_into_sum(slot, value);
    if !ty_compatible(slot, &v.ty) {
        let hint = if matches!((slot, &v.ty), (HirTy::Fn(..), HirTy::Closure { .. })) {
            " — a closure that captures variables is not a plain `fn` pointer (spec 4.6)"
        } else if matches!((slot, &v.ty), (HirTy::Fn(_, r), HirTy::Fn(..))
            if matches!(**r, HirTy::Throws { .. }))
        {
            " — only a named function or a capture-free closure is adapted to a `fn` type \
             that throws more (spec 4.4.9)"
        } else {
            ""
        };
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "mismatched types: {} expects `{}`, found `{}`{hint}",
                what(),
                ctx.ty_name(slot),
                ctx.ty_name(&v.ty)
            ),
        );
    }
    v
}

/// `Index<i32>` → `Index`: an `any` bound key without its arguments.
fn bound_base(b: &str) -> &str {
    b.split_once('<').map_or(b, |(base, _)| base)
}

/// Does an `any` value with bounds `have` satisfy bound `want`? Yes
/// when some bound or one of its supertraits (transitively) is `want`;
/// `any Tr<i32>` also satisfies `any Tr` (arguments unconstrained).
fn bound_covers(ctx: &LowerCtx<'_>, have: &[String], want: &str) -> bool {
    let mut stack: Vec<String> = have.to_vec();
    let mut seen: Vec<String> = Vec::new();
    while let Some(h) = stack.pop() {
        if h == want || (!want.contains('<') && bound_base(&h) == want) {
            return true;
        }
        let base = bound_base(&h).to_owned();
        if let (false, Some(info)) = (seen.contains(&base), ctx.env.trait_info.get(&base)) {
            stack.extend(info.supers.iter().cloned());
        }
        seen.push(base);
    }
    false
}

/// The `any Tr` slot a value of type `ty` would be stored into: `slot`
/// itself, or the `any Tr` variant of a sum slot that has no exact
/// variant for `ty`.
fn any_slot_for<'s>(slot: &'s HirTy, ty: &HirTy) -> Option<&'s HirTy> {
    match slot {
        HirTy::AnyTrait(_) => Some(slot),
        HirTy::Sum(vs) if !matches!(ty, HirTy::Sum(_)) && sum_variant_index(vs, ty).is_none() => {
            vs.iter().find(|v| matches!(v, HirTy::AnyTrait(_)))
        }
        _ => None,
    }
}

/// D4 store check + boxing: a value flowing into an `any Tr` slot must
/// implement every bound; it becomes `SumWrap { tag, value }` (tag =
/// program-wide type number, payload = heap copy). `any (A + B)` → `any
/// A` keeps the value as is (same tag numbering).
fn box_into_any(ctx: &LowerCtx<'_>, slot: &HirTy, value: HirExpr) -> HirExpr {
    let Some(target @ HirTy::AnyTrait(bounds)) = any_slot_for(slot, &value.ty) else {
        return value;
    };
    match &value.ty {
        HirTy::AnyTrait(have) if bounds.iter().all(|b| bound_covers(ctx, have, b)) => HirExpr {
            ty: target.clone(),
            ..value
        },
        // Spec 2.2.10: no implicit `any` → `any Tr` (it would hide a
        // runtime check); `any Tr` → `any` is the arm above.
        HirTy::AnyTrait(_) => ctx.error_expr(
            value.span,
            format!(
                "cannot store an `{}` value in an `{}` slot without narrowing — test it with \
                 `is` or a type pattern (`match v {{ x: T => ... }}`) first (spec 2.2.10)",
                ctx.ty_name(&value.ty),
                ctx.ty_name(target)
            ),
        ),
        HirTy::Unknown | HirTy::Any => value,
        ty => {
            let missing: Vec<&String> = bounds
                .iter()
                .filter(|b| !ctx.implements_trait(ty, b, 0))
                .collect();
            if !missing.is_empty() {
                let names: Vec<String> = missing.iter().map(|b| format!("`{b}`")).collect();
                return ctx.error_expr(
                    value.span,
                    format!(
                        "`{}` does not implement {}, so it cannot be stored in an `{}` slot (D4)",
                        ctx.ty_name(ty),
                        names.join(", "),
                        ctx.ty_name(target)
                    ),
                );
            }
            let span = value.span;
            HirExpr {
                kind: HirExprKind::SumWrap {
                    sum_ty: target.clone(),
                    variant_index: ctx.any_tag(ty),
                    value: Some(Box::new(value)),
                },
                ty: target.clone(),
                span,
            }
        }
    }
}

/// `ty_compatible`, or storable through `box_into_any`.
fn coercible(ctx: &LowerCtx<'_>, slot: &HirTy, ty: &HirTy) -> bool {
    ty_compatible(slot, ty)
        || matches!(any_slot_for(slot, ty), Some(HirTy::AnyTrait(bs))
        if bs.iter().all(|b| match ty {
            HirTy::AnyTrait(have) => bound_covers(ctx, have, b),
            _ => ctx.implements_trait(ty, b, 0),
        }))
}

/// Lower `e` with `ty` as its expected type (`Unknown` = no expectation).
fn lower_expected(ctx: &mut LowerCtx<'_>, e: &Expr, ty: HirTy) -> HirExpr {
    ctx.push_expected(ty);
    let r = lower_expr(ctx, e);
    ctx.pop_expected();
    r
}

/// A block / expression whose evaluation never completes normally:
/// it ends in `return` / `throw` / `break` / `continue`, a `loop` with
/// no `break` out of it, or an `if` / `match` whose every branch diverges.
fn hir_block_diverges(b: &HirBlock) -> bool {
    b.stmts.iter().any(|s| match s {
        HirStmt::Return(_)
        | HirStmt::Panic(_)
        | HirStmt::Break { .. }
        | HirStmt::Continue { .. } => true,
        HirStmt::Expr(e) | HirStmt::Let { init: e, .. } => hir_expr_diverges(e),
        _ => false,
    }) || b.trailing.as_ref().is_some_and(hir_expr_diverges)
}

fn hir_expr_diverges(e: &HirExpr) -> bool {
    match &e.kind {
        // `'l: { break 'l v; }` exits with a value: not divergence.
        HirExprKind::Block(b) => {
            hir_block_diverges(b)
                && !(b.label.is_some() && block_breaks_out(b, b.label.as_deref(), false))
        }
        HirExprKind::If {
            then_block,
            else_branch: Some(eb),
            ..
        } => hir_block_diverges(then_block) && hir_expr_diverges(eb),
        HirExprKind::Match { arms, .. } => {
            !arms.is_empty() && arms.iter().all(|a| hir_expr_diverges(&a.body))
        }
        HirExprKind::Loop { label, body, .. } => !block_breaks_out(body, label.as_deref(), true),
        _ => false,
    }
}

/// Does `b` contain a `break` that exits the loop labelled `label`?
/// `direct` = we're not inside a nested loop (unlabelled breaks count).
fn block_breaks_out(b: &HirBlock, label: Option<&str>, direct: bool) -> bool {
    let in_expr = |e: &HirExpr| expr_breaks_out(e, label, direct);
    b.stmts.iter().any(|s| match s {
        HirStmt::Break { label: bl, .. } => {
            (bl.is_none() && direct) || (bl.is_some() && bl.as_deref() == label)
        }
        HirStmt::Let { init: e, .. }
        | HirStmt::Assign { value: e, .. }
        | HirStmt::StaticAssign { value: e, .. }
        | HirStmt::Expr(e)
        | HirStmt::Return(Some(e)) => in_expr(e),
        _ => false,
    }) || b.trailing.as_ref().is_some_and(in_expr)
}

fn expr_breaks_out(e: &HirExpr, label: Option<&str>, direct: bool) -> bool {
    match &e.kind {
        HirExprKind::Block(b) => block_breaks_out(b, label, direct),
        HirExprKind::If {
            then_block,
            else_branch,
            ..
        } => {
            block_breaks_out(then_block, label, direct)
                || else_branch
                    .as_deref()
                    .is_some_and(|x| expr_breaks_out(x, label, direct))
        }
        HirExprKind::Match { arms, .. } => {
            arms.iter().any(|a| expr_breaks_out(&a.body, label, direct))
        }
        HirExprKind::While { body, .. } | HirExprKind::Loop { body, .. } => {
            block_breaks_out(body, label, false)
        }
        _ => false,
    }
}

/// Outcome of resolving `[..enum path.., Variant]`.
enum EnumRes {
    /// The prefix doesn't name an enum.
    NotEnum,
    Found(EnumId, usize),
    /// An enum was named but the variant / instantiation is wrong
    /// (already reported).
    Error,
}

/// Where call arguments come from: still-AST expressions (lowered
/// against the parameter type) or values already lowered (spread).
enum ArgSrc<'e> {
    Ast(&'e Expr),
    Lowered(HirExpr),
}

/// Shared mutable sink for closures lifted into anonymous top-level
/// functions, generic-function monomorphizations and lazily instantiated
/// generic structs. Lowering pushes here as it walks expressions.
struct ClosureSink {
    extras: std::cell::RefCell<Vec<HirFunction>>,
    next_id: std::cell::Cell<u32>,
    /// Cached monomorphizations: `(generic_fn_name, concrete_type_args)`
    /// → specialized `FunctionId`.
    mono_cache: std::cell::RefCell<HashMap<(String, Vec<String>), FunctionId>>,
    /// Specialized `FnSig` per monomorphization for call-site lookup.
    mono_sigs: std::cell::RefCell<HashMap<FunctionId, FnSig>>,
    /// Current monomorphization nesting (bounded by `MONO_DEPTH_LIMIT`).
    mono_depth: std::cell::Cell<u32>,
    /// Generic structs instantiated from a literal during body lowering
    /// (ids continue after `Env::structs`).
    extra_structs: std::cell::RefCell<Vec<HirStructDef>>,
    extra_struct_table: std::cell::RefCell<HashMap<String, StructId>>,
    /// Same for generic enums (ids continue after `Env::enums`).
    extra_enums: std::cell::RefCell<Vec<HirEnumDef>>,
    extra_enum_table: std::cell::RefCell<HashMap<String, EnumId>>,
    /// `any` type tags: index = tag of that concrete type.
    any_tags: std::cell::RefCell<Vec<HirTy>>,
    /// `any Tr` method dispatchers (bodies built after all lowering).
    any_dispatch: std::cell::RefCell<Vec<expr::AnyDispatch>>,
    /// Diagnostics emitted during lowering — surfaced through
    /// `HirModule.diagnostics` so the driver can fail the build.
    diagnostics: std::cell::RefCell<Vec<rokc_diagnostic::RokDiagnostic>>,
}

/// Per-function lowering state: scoped name → local-id map plus the
/// running list of local declarations, on top of the shared `Env`.
struct LowerCtx<'a> {
    env: &'a Env<'a>,
    locals: Vec<HirLocal>,
    scopes: Vec<HashMap<String, LocalId>>,
    /// Per-monomorphization type-parameter substitution. Empty for
    /// non-generic functions. `T` → concrete `HirTy` overrides the
    /// alias table when both contain the same name.
    ty_subst: &'a HashMap<String, HirTy>,
    self_ty: Option<HirTy>,
    /// Enclosing function's (or closure's) return type. `return v;`
    /// checks against it and wraps `v` into a matching sum type.
    fn_ret_ty: HirTy,
    /// Closure without a declared / expected return type: the first
    /// `return v;` fixes `fn_ret_ty`.
    infer_ret: bool,
    /// Lowering the implicit `main` built from top-level statements,
    /// where `return` is not allowed (spec 4.16.4). Closures get a fresh
    /// context, so a `return` inside one stays legal.
    implicit_main: bool,
    /// Enclosing breakable constructs, innermost last: `(label,
    /// is_loop)` — labelled blocks accept `break 'l` but not `continue`.
    breakables: Vec<(Option<String>, bool)>,
    /// `breakables` index → the type its `break` values must have:
    /// the annotated slot (`true` = inferred from the first `break`).
    break_tys: HashMap<usize, (HirTy, bool)>,
    /// Stack of expected types. Every sub-expression whose type is not
    /// its parent's pushes its own expectation (or `Unknown` for none),
    /// so literals and leaf lowerings (`Box::None`, `5` → `i64`) only
    /// ever see the slot they actually flow into.
    expected_ty_stack: Vec<HirTy>,
    /// Module path of the function currently being lowered, joined with
    /// `::`. Empty string for free functions in the package root.
    current_module: String,
    /// Function-/block-scoped `use` entries. Mirrors `scopes`: each
    /// `push_scope` pushes an empty Vec, `pop_scope` pops it. Resolution
    /// walks this stack top-down before consulting module-level uses.
    local_uses: Vec<Vec<crate::uses::UseEntry>>,
    /// Or-pattern shared binders. Each Or-pattern lowering pushes a map
    /// of `name → preset LocalId` so each alternative's `Binding` reuses
    /// the same local instead of allocating a fresh one. Spec 3.11.4 —
    /// `E::A(x) | E::B(x)` must bind `x` once, with consistent type.
    or_pattern_binders: Vec<HashMap<String, LocalId>>,
    /// Error type of the enclosing function's / closure's `throws`
    /// (`None`: no error may leave it).
    fn_throws: Option<HirTy>,
    /// Enclosing prefix `try`s; a throwing call must sit under one.
    try_depth: u32,
    /// Enclosing `catch` / `try?` / `try!` / `finally` frames, innermost
    /// last (see `throws`).
    err_frames: Vec<ErrFrame>,
    /// Probe pass over a closure body: collects the error types that
    /// escape it instead of reporting them.
    throws_probe: Option<Vec<HirTy>>,
    /// Lowering the body of `fn main() throws (E)`: an escaping error
    /// ends the process (spec 4.16.3).
    uncaught_in_main: bool,
    /// Throwing calls lowered so far (a `try` covering none is
    /// pointless).
    throwing_calls: u32,
    /// Counter for synthesized labels and local names.
    next_synth: u32,
    /// Narrowed rebinding (spec 2.2.6) → (original local, its type);
    /// assignments to the rebinding also store into the original.
    narrowed: HashMap<LocalId, (LocalId, HirTy)>,
}

impl<'a> LowerCtx<'a> {
    fn new(env: &'a Env<'a>, ty_subst: &'a HashMap<String, HirTy>, self_ty: Option<HirTy>) -> Self {
        Self {
            env,
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            ty_subst,
            self_ty,
            fn_ret_ty: HirTy::Unit,
            infer_ret: false,
            implicit_main: false,
            breakables: Vec::new(),
            break_tys: HashMap::new(),
            expected_ty_stack: Vec::new(),
            current_module: String::new(),
            local_uses: vec![Vec::new()],
            or_pattern_binders: Vec::new(),
            fn_throws: None,
            try_depth: 0,
            err_frames: Vec::new(),
            throws_probe: None,
            uncaught_in_main: false,
            throwing_calls: 0,
            next_synth: 0,
            narrowed: HashMap::new(),
        }
    }

    /// Push a lowering-time diagnostic onto the shared sink. Drained
    /// into `HirModule.diagnostics` at the end of the lower pass.
    fn emit_error(&self, kind: rokc_diagnostic::ErrorKind, msg: String) {
        self.env
            .sink
            .diagnostics
            .borrow_mut()
            .push(rokc_diagnostic::RokDiagnostic::error(kind, msg));
    }

    /// A warning, except in generic instances: a `rethrows` instance
    /// with a non-throwing argument would flag every `try` in its body.
    fn emit_warning(&self, msg: String) {
        if self.ty_subst.is_empty() {
            self.env
                .sink
                .diagnostics
                .borrow_mut()
                .push(rokc_diagnostic::RokDiagnostic::warning(
                    rokc_diagnostic::ErrorKind::Type,
                    msg,
                ));
        }
    }

    /// Report a type error and return a poisoned placeholder (`Unknown`
    /// type). Checks skip `Unknown` operands, so one root cause yields
    /// one diagnostic.
    fn error_expr(&self, span: rokc_diagnostic::Span, msg: String) -> HirExpr {
        self.emit_error(rokc_diagnostic::ErrorKind::Type, msg);
        poison(span)
    }

    /// User-facing type name (no internal `Struct0` / mangled names).
    fn ty_name(&self, ty: &HirTy) -> String {
        match ty {
            HirTy::Struct(_) | HirTy::Enum(_) => {
                let (name, generic_args) = match ty {
                    HirTy::Struct(id) => {
                        let d = self.struct_def(*id);
                        (d.name, d.generic_args)
                    }
                    HirTy::Enum(id) => {
                        let d = self.enum_def(*id);
                        (d.name, d.generic_args)
                    }
                    _ => unreachable!("matched struct / enum"),
                };
                if generic_args.is_empty() {
                    name
                } else {
                    let base = name.split("__").next().unwrap_or(&name).to_owned();
                    let args: Vec<String> = generic_args.iter().map(|a| self.ty_name(a)).collect();
                    format!("{base}<{}>", args.join(", "))
                }
            }
            HirTy::Prim(p) => p.name().to_owned(),
            HirTy::Unit => "()".to_owned(),
            HirTy::Any => "any".to_owned(),
            HirTy::AnyTrait(b) if b.is_empty() => "any".to_owned(),
            HirTy::AnyTrait(b) if b.len() == 1 => format!("any {}", b[0]),
            HirTy::AnyTrait(b) => format!("any ({})", b.join(" + ")),
            HirTy::Unknown => "{unknown}".to_owned(),
            HirTy::Path(p) => p.join("::"),
            HirTy::Tuple(parts) => {
                let inner: Vec<String> = parts.iter().map(|t| self.ty_name(t)).collect();
                format!("({})", inner.join(", "))
            }
            HirTy::Sum(parts) => {
                let inner: Vec<String> = parts.iter().map(|t| self.ty_name(t)).collect();
                inner.join(" | ")
            }
            HirTy::Array(e, n) => format!("[{}; {n}]", self.ty_name(e)),
            HirTy::Fn(args, ret) | HirTy::Closure { args, ret, .. } => {
                let inner: Vec<String> = args.iter().map(|t| self.ty_name(t)).collect();
                let kw = if matches!(ty, HirTy::Fn(..)) {
                    "fn"
                } else {
                    "closure"
                };
                let ret = match &**ret {
                    HirTy::Throws { .. } => self.ty_name(ret),
                    r => format!("-> {}", self.ty_name(r)),
                };
                format!("{kw}({}) {ret}", inner.join(", "))
            }
            HirTy::Throws { ok, err } => {
                format!("throws ({}) -> {}", self.ty_name(err), self.ty_name(ok))
            }
        }
    }

    /// Does `ty` have an `impl {trait_key} for ty`?
    fn implements(&self, ty: &HirTy, trait_key: &str) -> bool {
        method_target_for(ty)
            .is_some_and(|t| self.env.impl_traits.contains(&(t, trait_key.to_owned())))
    }

    /// `implements`, or a generic impl of the trait covers `ty`.
    fn implements_trait(&self, ty: &HirTy, trait_key: &str, depth: u32) -> bool {
        self.implements(ty, trait_key)
            || self.env.generic_trait_impls.iter().any(|gi| {
                gi.trait_key == bound_base(trait_key)
                    && self.generic_impl_subst(gi, ty, depth).is_some_and(|subst| {
                        trait_key == gi.trait_key
                            || self
                                .generic_impl_keys(gi, &subst)
                                .iter()
                                .any(|k| k == trait_key)
                    })
            })
    }

    /// The bound keys generic impl `gi` answers under `subst` (its
    /// trait arguments and associated types instantiated).
    fn generic_impl_keys(
        &self,
        gi: &GenericTraitImpl,
        subst: &HashMap<String, HirTy>,
    ) -> Vec<String> {
        let mut rcx = LowerCtx::new(self.env, subst, None);
        rcx.current_module.clone_from(&gi.module);
        let args: Vec<HirTy> = gi
            .trait_args
            .iter()
            .map(|t| rcx.resolve_ast_ty(t))
            .collect();
        let assoc: Vec<(String, HirTy)> = gi
            .assoc
            .iter()
            .map(|(n, t)| (n.clone(), rcx.resolve_ast_ty(t)))
            .collect();
        impl_bound_keys(
            &gi.trait_key,
            &args,
            &assoc,
            &self.env.struct_table,
            &self.env.enum_table,
        )
    }

    /// The impl's type-parameter bindings when generic impl `gi` covers
    /// `ty`: `ty` matches its target and meets its bounds.
    fn generic_impl_subst(
        &self,
        gi: &GenericTraitImpl,
        ty: &HirTy,
        depth: u32,
    ) -> Option<HashMap<String, HirTy>> {
        // ponytail: depth cap stops `impl<T: Tr> Tr for T` cycles; a
        // real cycle check would remember the (type, trait) goals.
        if depth > 8 || matches!(ty, HirTy::Unknown) {
            return None;
        }
        let params: std::collections::HashSet<String> = gi
            .generics
            .params
            .iter()
            .filter_map(|gp| match gp {
                rokc_ast::GenericParam::Type { name, .. } => Some(name.clone()),
                rokc_ast::GenericParam::Const { .. } => None,
            })
            .collect();
        let mut subst = HashMap::new();
        unify_param_ty_with(&gi.self_ty, ty, &params, &mut subst, self);
        if params.iter().any(|p| !subst.contains_key(p)) {
            return None;
        }
        let mut rcx = LowerCtx::new(self.env, &subst, None);
        rcx.current_module.clone_from(&gi.module);
        if rcx.resolve_ast_ty(&gi.self_ty) != *ty {
            return None;
        }
        let mut goals: Vec<(HirTy, &Vec<Ty>)> = Vec::new();
        for gp in &gi.generics.params {
            if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
                goals.push((subst[name].clone(), bounds));
            }
        }
        for w in &gi.where_clause {
            goals.push((rcx.resolve_ast_ty(&w.ty), &w.bounds));
        }
        for (bty, bounds) in goals {
            for b in bounds {
                let AstTyKind::Path(p) = &b.kind else {
                    continue;
                };
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                let (args, binds) = split_trait_args(
                    p.segments.last().map_or(&[][..], |s| s.generics.as_slice()),
                    |t| rcx.resolve_ast_ty(t),
                );
                let key = bound_key(
                    self.env.names.trait_key(&segs, &gi.module),
                    &args,
                    &binds,
                    &self.env.struct_table,
                    &self.env.enum_table,
                );
                if !self.implements_trait(&bty, &key, depth + 1) {
                    return None;
                }
            }
        }
        Some(subst)
    }

    /// Program-wide `any` type tag of concrete type `ty`, assigned on
    /// first use (whole-program compilation: closed world).
    fn any_tag(&self, ty: &HirTy) -> u32 {
        let mut tags = self.env.sink.any_tags.borrow_mut();
        let i = tags.iter().position(|t| t == ty).unwrap_or_else(|| {
            tags.push(ty.clone());
            tags.len() - 1
        });
        u32::try_from(i).expect("any tag overflow")
    }

    fn struct_def(&self, id: StructId) -> HirStructDef {
        let i = id.0 as usize;
        match self.env.structs.get(i) {
            Some(d) => d.clone(),
            None => self.env.sink.extra_structs.borrow()[i - self.env.structs.len()].clone(),
        }
    }

    /// Struct id by table key, including lazily instantiated ones.
    fn lookup_struct(&self, key: &str) -> Option<StructId> {
        self.env
            .struct_table
            .get(key)
            .copied()
            .or_else(|| self.env.sink.extra_struct_table.borrow().get(key).copied())
    }

    /// Instantiate generic struct `base` with `args` on demand (struct
    /// literal inference: `Box { v: 5 }` → `Box<i32>`).
    fn instantiate_struct(&self, base: &str, args: Vec<HirTy>) -> Option<StructId> {
        let key = mangle_inst(base, &args);
        if let Some(id) = self.lookup_struct(&key) {
            return Some(id);
        }
        let def = *self.env.generic_structs.get(base)?;
        let idx = self.env.sink.extra_structs.borrow().len();
        let id = StructId(u32::try_from(self.env.structs.len() + idx).expect("StructId overflow"));
        self.env
            .sink
            .extra_struct_table
            .borrow_mut()
            .insert(key.clone(), id);
        // Reserve the slot before resolving fields: a field type can
        // instantiate further structs, which must not take this id.
        self.env.sink.extra_structs.borrow_mut().push(HirStructDef {
            id,
            def_id: None,
            name: key,
            fields: Vec::new(),
            span: def.span,
            generic_args: args.clone(),
            union_kind: None,
        });
        let subst = generic_subst(&def.generics, &args);
        let mut rcx = LowerCtx::new(self.env, &subst, None);
        rcx.current_module = module_of(base);
        let fields = generic_struct_fields(def, &|t| rcx.resolve_ast_ty(t));
        self.env.sink.extra_structs.borrow_mut()[idx].fields = fields;
        Some(id)
    }

    fn enum_def(&self, id: EnumId) -> HirEnumDef {
        let i = id.0 as usize;
        match self.env.enums.get(i) {
            Some(d) => d.clone(),
            None => self.env.sink.extra_enums.borrow()[i - self.env.enums.len()].clone(),
        }
    }

    /// Enum id by table key, including lazily instantiated ones.
    fn lookup_enum(&self, key: &str) -> Option<EnumId> {
        self.env
            .enum_table
            .get(key)
            .copied()
            .or_else(|| self.env.sink.extra_enum_table.borrow().get(key).copied())
    }

    /// Instantiations of generic enum `base`, eager and lazy.
    fn enum_instantiations(&self, base: &str) -> Vec<EnumId> {
        let mut v = Self::instantiations(&self.env.enum_table, base);
        v.extend(Self::instantiations(
            &self.env.sink.extra_enum_table.borrow(),
            base,
        ));
        v
    }

    /// Instantiate generic enum `base` with `args` on demand — for
    /// enum types that only appear under a monomorphization
    /// substitution, which the eager AST scan cannot see.
    fn instantiate_enum(&self, base: &str, args: Vec<HirTy>) -> Option<EnumId> {
        let key = mangle_inst(base, &args);
        if let Some(id) = self.lookup_enum(&key) {
            return Some(id);
        }
        let def = *self.env.generic_enums.get(base)?;
        let idx = self.env.sink.extra_enums.borrow().len();
        let id = EnumId(u32::try_from(self.env.enums.len() + idx).expect("EnumId overflow"));
        self.env
            .sink
            .extra_enum_table
            .borrow_mut()
            .insert(key.clone(), id);
        // Reserve the slot before resolving payloads: a payload type can
        // instantiate further enums, which must not take this id.
        self.env.sink.extra_enums.borrow_mut().push(HirEnumDef {
            id,
            def_id: None,
            name: key,
            variants: Vec::new(),
            span: def.span,
            generic_args: args.clone(),
        });
        let subst = generic_subst(&def.generics, &args);
        let mut rcx = LowerCtx::new(self.env, &subst, None);
        rcx.current_module = module_of(base);
        let variants = generic_enum_variants(def, &|t| rcx.resolve_ast_ty(t));
        self.env.sink.extra_enums.borrow_mut()[idx].variants = variants;
        Some(id)
    }

    fn scope(&self) -> Scope<'_> {
        Scope {
            names: &self.env.names,
            module: &self.current_module,
        }
    }

    /// Canonical type-namespace name for a path (struct / enum / alias /
    /// trait, generic bases included), resolved from this function's
    /// module and `use`s.
    fn canon_type(&self, segments: &[&str]) -> Option<String> {
        self.env
            .names
            .canon(segments, &self.current_module, &self.local_uses)
    }

    /// Split `a::E::V` into (`a::E` enum, `V`) when the prefix names an
    /// enum (or generic enum base).
    /// A single segment is an imported variant (`use E::{A}`, `use
    /// E::*`, or `Ok` / `Err` through the implicit `rok::core::**`).
    fn enum_path(&self, segments: &[&str]) -> Option<(String, String)> {
        let (variant, ty) = segments.split_last()?;
        if ty.is_empty() {
            let key =
                self.env
                    .names
                    .canon_variant(segments, &self.current_module, &self.local_uses)?;
            let (e, v) = key.rsplit_once("::")?;
            return Some((e.to_owned(), v.to_owned()));
        }
        Some((self.canon_type(ty)?, (*variant).to_owned()))
    }

    /// Instantiations of generic base `base` in `table`, sorted by key
    /// for deterministic choice.
    fn instantiations<V: Copy>(table: &HashMap<String, V>, base: &str) -> Vec<V> {
        let prefix = format!("{base}__");
        let mut hits: Vec<(&String, V)> = table
            .iter()
            .filter(|(k, _)| k.starts_with(&prefix))
            .map(|(k, v)| (k, *v))
            .collect();
        hits.sort_by(|a, b| a.0.cmp(b.0));
        hits.into_iter().map(|(_, v)| v).collect()
    }

    /// Resolve a value-namespace path against `table` (fns, consts,
    /// statics) from this function's module and `use`s.
    fn resolve_in<T>(&self, segments: &[&str], table: &HashMap<String, T>) -> Option<String> {
        let exists = |k: &str| table.contains_key(k);
        let keys = || table.keys().cloned().collect::<Vec<_>>();
        let set = NameSet {
            exists: &exists,
            keys: &keys,
        };
        match resolve_name(
            segments,
            &self.current_module,
            &self.local_uses,
            self.env.uses,
            &set,
        ) {
            Ok(r) => r,
            Err(hits) => {
                self.report_ambiguous(&segments.join("::"), &hits);
                hits.into_iter().next()
            }
        }
    }

    /// Resolve a callee name (single- or multi-segment path) to a fully
    /// qualified fn-table key.
    fn resolve_fn_name(&self, segments: &[&str]) -> Option<String> {
        self.resolve_in(segments, &self.env.fn_table)
    }

    fn report_ambiguous(&self, name: &str, hits: &[String]) {
        self.emit_error(
            rokc_diagnostic::ErrorKind::Module,
            format!(
                "name `{name}` is ambiguous in module `{}` — multiple glob imports \
                 resolve it: {}",
                module_display(&self.current_module),
                hits.join(", ")
            ),
        );
    }

    /// Visibility check: can a caller in `self.current_module` see an
    /// item declared in `def_module` with the given visibility?
    fn is_visible(&self, def_module: &str, vis: Visibility) -> bool {
        visible_from(&self.current_module, def_module, vis)
    }

    /// Report use of a private value item (fn / const / static).
    fn check_item_visible(&self, full: &str, what: &str) -> bool {
        let vis = self
            .env
            .item_visibility
            .get(full)
            .copied()
            .unwrap_or(Visibility::Pub);
        let def_module = module_of(full);
        if self.is_visible(&def_module, vis) {
            return true;
        }
        self.emit_error(
            rokc_diagnostic::ErrorKind::Module,
            format!(
                "{what} `{full}` is private to module `{}` and cannot be used from `{}` \
                 (spec 5.6 — add `pub` to expose it)",
                module_display(&def_module),
                module_display(&self.current_module)
            ),
        );
        false
    }

    /// Report access to a private field from outside its struct's module.
    fn check_field_visible(&self, sid: StructId, field: &str) {
        let def = self.struct_def(sid);
        let base = if def.generic_args.is_empty() {
            def.name
        } else {
            def.name.split("__").next().unwrap_or(&def.name).to_owned()
        };
        let Some(vis) = self
            .env
            .field_vis
            .get(&base)
            .and_then(|m| m.get(field))
            .copied()
        else {
            return;
        };
        let def_module = module_of(&base);
        if !self.is_visible(&def_module, vis) {
            self.emit_error(
                rokc_diagnostic::ErrorKind::Module,
                format!(
                    "field `{field}` of `{}` is private to module `{}` (spec 5.6 — add \
                     `pub` to the field to expose it)",
                    self.ty_name(&HirTy::Struct(sid)),
                    module_display(&def_module)
                ),
            );
        }
    }

    fn push_expected(&mut self, ty: HirTy) {
        self.expected_ty_stack.push(ty);
    }
    fn pop_expected(&mut self) {
        self.expected_ty_stack.pop();
    }
    fn current_expected(&self) -> Option<&HirTy> {
        self.expected_ty_stack.last()
    }

    /// Resolve an AST type into a concrete `HirTy`, applying any
    /// monomorphization substitution, `Self`, and the alias map. Generic
    /// struct uses with concrete arguments are instantiated on demand
    /// (`Tagged<T>` under `T = i32` inside a monomorphized body).
    fn resolve_ast_ty(&self, ty: &rokc_ast::Ty) -> HirTy {
        let mut t = self.resolve_ty_inner(ty);
        if let Some(st) = &self.self_ty {
            substitute_aliases(&mut t, &HashMap::from([("Self".to_owned(), st.clone())]));
        }
        substitute_aliases(&mut t, &self.env.type_aliases);
        t
    }

    fn resolve_ty_inner(&self, ty: &rokc_ast::Ty) -> HirTy {
        let rec = |t: &rokc_ast::Ty| self.resolve_ty_inner(t);
        match &ty.kind {
            AstTyKind::Path(p) => {
                if let [seg] = p.segments.as_slice() {
                    if seg.generics.is_empty() {
                        if let Some(t) = self.ty_subst.get(&seg.name) {
                            return t.clone();
                        }
                    }
                }
                let generics = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
                if !generics.is_empty() {
                    let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                    if let Some(full) = self.canon_type(&segs) {
                        let args: Vec<HirTy> = generics.iter().map(rec).collect();
                        let mut leftover = Vec::new();
                        args.iter()
                            .for_each(|a| collect_unknown_paths(a, &mut leftover));
                        if leftover.is_empty() && self.env.generic_structs.contains_key(&full) {
                            if let Some(id) = self.instantiate_struct(&full, args) {
                                return HirTy::Struct(id);
                            }
                        } else if leftover.is_empty() {
                            if let Some(id) = self.instantiate_enum(&full, args) {
                                return HirTy::Enum(id);
                            }
                        } else {
                            // An argument names an unbound type param:
                            // re-resolving it by name could hit a
                            // same-named visible type.
                            return HirTy::Path(vec![full]);
                        }
                    }
                }
                let mut t = resolve_ty_with_structs(
                    ty,
                    &self.env.struct_table,
                    &self.env.enum_table,
                    self.scope(),
                );
                substitute_aliases(&mut t, self.ty_subst);
                t
            }
            AstTyKind::Sum(parts) => HirTy::Sum(parts.iter().map(rec).collect()),
            AstTyKind::Tuple(parts) if parts.is_empty() => HirTy::Unit,
            AstTyKind::Tuple(parts) => HirTy::Tuple(parts.iter().map(rec).collect()),
            AstTyKind::Array(elem, _) => {
                match resolve_ty_with_structs(
                    ty,
                    &self.env.struct_table,
                    &self.env.enum_table,
                    self.scope(),
                ) {
                    HirTy::Array(_, n) => HirTy::Array(Box::new(rec(elem)), n),
                    other => other,
                }
            }
            AstTyKind::Fn(args, ret) => {
                HirTy::Fn(args.iter().map(rec).collect(), Box::new(rec(ret)))
            }
            AstTyKind::Throws { ok, err } => crate::ty::throws_ty(rec(ok), rec(err)),
            _ => resolve_ty_with_structs(
                ty,
                &self.env.struct_table,
                &self.env.enum_table,
                self.scope(),
            ),
        }
    }

    fn into_locals(self) -> Vec<HirLocal> {
        self.locals
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.local_uses.push(Vec::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
        self.local_uses.pop();
    }

    fn add_local_use(&mut self, entry: crate::uses::UseEntry) {
        if let Some(top) = self.local_uses.last_mut() {
            top.push(entry);
        }
    }

    fn declare(&mut self, name: Option<String>, ty: HirTy) -> LocalId {
        let id = LocalId(u32::try_from(self.locals.len()).expect("LocalId overflow"));
        if let Some(n) = &name {
            if let Some(scope) = self.scopes.last_mut() {
                scope.insert(n.clone(), id);
            }
        }
        self.locals.push(HirLocal { id, name, ty });
        id
    }

    fn lookup(&self, name: &str) -> Option<LocalId> {
        for scope in self.scopes.iter().rev() {
            if let Some(id) = scope.get(name) {
                return Some(*id);
            }
        }
        None
    }

    /// Look up a name only in the innermost scope. Used by the let
    /// redeclaration check (spec variant 238): nested scopes can
    /// rebind, but the same scope cannot.
    fn lookup_in_current_scope(&self, name: &str) -> Option<LocalId> {
        self.scopes.last().and_then(|s| s.get(name).copied())
    }

    fn local_ty(&self, id: LocalId) -> HirTy {
        self.locals
            .get(id.0 as usize)
            .map_or(HirTy::Unknown, |l| l.ty.clone())
    }
}

/// Placeholder for an expression whose lowering failed (an error has
/// been reported). Never reaches MIR: the driver stops on errors and
/// `check_unresolved_types` refuses `Unknown` otherwise.
const fn poison(span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr {
        kind: HirExprKind::Const(ConstVal::Unit),
        ty: HirTy::Unknown,
        span,
    }
}

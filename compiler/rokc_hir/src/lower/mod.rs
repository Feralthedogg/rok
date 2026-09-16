//! AST → HIR lowering.

use std::collections::HashMap;

use rokc_ast::{
    Block, CallArg, EnumDef as AstEnumDef, EnumVariantKind as AstEnumVariantKind, Expr, ExprKind,
    FnDef, ImplItem as AstImplItem, Item, Literal as AstLit, MatchArm as AstMatchArm, Param,
    Path as AstPath, Pattern as AstPattern, PatternKind as AstPatternKind, Program, Stmt, StmtKind,
    StructDef as AstStructDef, StructKind as AstStructKind, Ty, TyKind as AstTyKind,
};
use rokc_core::Visibility;
use rokc_diagnostic::Span;
use rokc_ir_common::{ConstVal, FunctionId, LocalId, PrimOp, PrimTy};
use rokc_parser::{Fixity, PrecTable};

use crate::ty::resolve_ty;
use crate::{
    EnumId, HirBlock, HirEnumDef, HirEnumVariant, HirExpr, HirExprKind, HirField, HirFunction,
    HirLocal, HirMatchArm, HirModule, HirParam, HirPattern, HirStaticDef, HirStmt, HirStructDef,
    HirTy, HirUnionKind, NicheArg, NicheVal, StructId, TraitRef, UnionStorage,
};

mod bignum;
mod broadcast;
mod caller;
mod collect;
pub mod const_eval;
mod coro;
mod desugar;
mod expr;
mod frame_ptr;
mod fstring;
mod infer;
mod method_value;
mod mono;
mod pattern;
mod reflect;
mod resolve;
pub use resolve::{hidden_module, hidden_module_msg, module_visibility, visibility_rank};
pub use resolve::{is_dependency, root_path, set_packages};
mod send_check;
mod throws;

use collect::collect_unknown_paths;
pub use collect::lower_full;
pub use coro::FN_BLOCK_LABEL;
use desugar::{
    desugar_nullish_coalesce, desugar_question_dot, desugar_try_q, lower_closure_expr, lower_for,
};
use expr::{
    build_any_dispatchers, enum_base_name, field_access, has_int_suffix, hir_binop, hir_int,
    hir_local, lower_block, lower_cond, lower_expr, lower_loop_body, lower_sibling_pair,
    method_call_on, parse_char_literal, parse_int_literal, resolve_enum_variant, variant_arg_tys,
};
use mono::{
    bind_from_arg, bind_self, generic_enum_variants, generic_struct_fields, generic_subst,
    lower_fn, monomorphize, monomorphize_on, resolve_in_mono, unify_param_ty_with,
};
use pattern::{int_fits, lower_match, lower_pattern};
use resolve::{
    COPY_TRAIT, DEFAULT_TRAIT, EQ_TRAIT, GC_BUF, impl_module, item_module, leaf_name, mangle_inst,
    method_target_for, module_display, module_of, package_of, resolve_name,
    resolve_ty_with_structs, substitute_params, ty_mangle, visible_from,
};
use throws::{
    ErrFrame, adapt_fn_value, adapt_never_fn, erase_unbound_errors, exit_through,
    finish_throwing_body, jump_index, lower_catch, lower_return, lower_throw, lower_try,
    main_frame, rethrows_value, sig_ret_ast, uncaught_in_main, unpack_call,
};

/// Outcome of glob resolution for one bare name. A single import beats
/// any glob; two distinct globs landing on the same suffix are
/// `Ambiguous`.
enum LookupOutcome {
    None,
    Resolved(String),
    Ambiguous(Vec<String>),
}

/// A name table to resolve against: membership test plus the keys
/// ending in a given segment, needed only by `use a::**` deep globs.
struct NameSet<'b> {
    exists: &'b dyn Fn(&str) -> bool,
    keys: &'b dyn Fn(&str) -> Vec<String>,
    /// Is the key visible from the module being resolved? A glob import
    /// brings in only the items it can see (spec 5.6), so a private
    /// helper of `rok::core::x` never competes through `rok::core::**`.
    visible: &'b dyn Fn(&str) -> bool,
}

/// Type-namespace index: every struct / union / enum / alias / trait
/// name (driver-qualified, e.g. `a::P`; generic bases unmangled) plus
/// `pub use` re-export aliases. All type paths — in signatures, fields,
/// struct literals, patterns, enum paths — resolve through `canon`.
struct TypeNames<'a> {
    names: std::collections::HashSet<String>,
    traits: std::collections::HashSet<String>,
    /// Structural auto traits (`#[lang("send_trait" | "sync_trait")]`):
    /// a type has them unless a component lacks them.
    auto_traits: std::collections::HashSet<String>,
    /// The `#[lang]` slots (spec 6.4).
    lang: rokc_parser::LangTable,
    /// Every enum variant as `a::E::V` (generic bases unmangled). A
    /// variant is as visible as its enum (spec 5.6.9).
    variants: std::collections::HashSet<String>,
    /// `pub use` alias key → the type its re-export chain ends at.
    reexports: HashMap<String, String>,
    visibility: HashMap<String, Visibility>,
    /// Module path → its `mod` visibility (the driver's flattened stubs).
    mod_vis: HashMap<String, Visibility>,
    uses: &'a crate::uses::UseTable,
    diags: std::cell::RefCell<Vec<rokc_diagnostic::RokDiagnostic>>,
    /// Generic type aliases (`type Row<const N: usize> = [i32; N];`)
    /// by full name, expanded at each use; also the non-generic ones
    /// with a `where` clause (checked once, never expanded here).
    generic_aliases: HashMap<String, rokc_ast::TypeAliasDef>,
    /// Non-generic aliases by full name → aliased type, so a generic
    /// instance's argument can name one (`List<Item>`) during
    /// instantiation, before the alias table proper exists.
    plain_aliases: HashMap<String, Ty>,
    /// Plain aliases being expanded (caps a cycle).
    alias_depth: std::cell::Cell<u32>,
    /// Plain aliases that are cyclic or name a projection that fails.
    broken_aliases: std::cell::RefCell<std::collections::HashSet<String>>,
    /// Every generic alias use: (alias, arguments, module, span), for
    /// its bounds check (`check_type_bounds`).
    alias_uses: std::cell::RefCell<Vec<AliasUse>>,
    /// First use of each unresolved type path, for its "cannot find
    /// type" location.
    unknown_spans: std::cell::RefCell<HashMap<String, rokc_diagnostic::Span>>,
    /// `canon` results without local `use`s or diagnostics, by (path,
    /// module): its glob lookups scan every type name.
    canon_memo: std::cell::RefCell<HashMap<(String, String), Option<String>>>,
    /// Type and variant keys by last segment, built on the first deep
    /// glob lookup (the tables are complete by then).
    leaves: std::cell::OnceCell<Leaves>,
    variant_leaves: std::cell::OnceCell<Leaves>,
    /// Module-level `const`s by full name, for array lengths in
    /// signatures and fields (`[i32; N]`).
    consts: HashMap<String, (Ty, rokc_ast::Expr)>,
    const_leaves: std::cell::OnceCell<Leaves>,
}

/// Keys by their last `::` segment.
type Leaves = HashMap<String, Vec<String>>;

fn leaves<'k>(keys: impl IntoIterator<Item = &'k String>) -> Leaves {
    let mut out: Leaves = HashMap::new();
    for k in keys {
        let leaf = k.rsplit("::").next().unwrap_or(k);
        out.entry(leaf.to_owned()).or_default().push(k.clone());
    }
    out
}

/// (alias full name, arguments, module of the use, span of the use).
type AliasUse = (String, Vec<Ty>, String, rokc_diagnostic::Span);

/// Can code in `module` name the type-like item `full` (spec 5.6)?
/// Unknown names (primitives, ..) are visible.
#[must_use]
pub fn type_visible(m: &crate::HirModule, full: &str, module: &str) -> bool {
    m.type_visibility
        .get(full)
        .is_none_or(|&vis| visible_from(module, &module_of(full), vis))
}

impl TypeNames<'_> {
    /// The item bound to lang slot `slot` (spec 6.4), `""` if unbound; a
    /// method slot (`drop_method`) gives its trait.
    fn lang_item(&self, slot: &str) -> &str {
        self.lang.lookup(slot).map_or("", |e| {
            if slot.ends_with("_method") {
                e.item_name.rsplit_once("::").map_or("", |(t, _)| t)
            } else {
                &e.item_name
            }
        })
    }

    /// `Row<3>` → `[i32; 3]` when `ty` names a generic alias. The
    /// alias body's own names are resolved in the alias's module and
    /// written absolute, so the expansion means the same at the use site.
    fn expand_alias(&self, ty: &Ty, module: &str, at: Span) -> Option<Ty> {
        let AstTyKind::Path(p) = &ty.kind else {
            return None;
        };
        let args = &p.segments.last()?.generics;
        if args.is_empty() || self.generic_aliases.is_empty() {
            return None;
        }
        let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
        let full = self.canon(&segs, module, &[], at)?;
        let alias = self
            .generic_aliases
            .get(&full)
            .filter(|a| !a.generics.params.is_empty())?;
        let map: HashMap<String, Ty> = alias
            .generics
            .params
            .iter()
            .map(|gp| match gp {
                rokc_ast::GenericParam::Type { name, .. }
                | rokc_ast::GenericParam::Const { name, .. } => name.clone(),
            })
            .zip(args.iter().cloned())
            .collect();
        let mut out = alias.ty.clone();
        self.absolutize(&mut out, &module_of(&full), module, &map, at);
        collect::subst_assoc_ty(&mut out, &map);
        self.alias_uses
            .borrow_mut()
            .push((full, args.clone(), module.to_owned(), ty.span));
        Some(out)
    }

    /// The non-generic alias `ty` names in `module`.
    fn plain_alias(&self, ty: &Ty, module: &str, at: Span) -> Option<String> {
        let AstTyKind::Path(p) = &ty.kind else {
            return None;
        };
        if !p.segments.last()?.generics.is_empty() {
            return None;
        }
        let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
        self.canon(&segs, module, &[], at)
            .filter(|full| self.plain_aliases.contains_key(full))
    }

    /// `B` → `<A as P>::Out` when plain alias `full`'s body names a
    /// projection: expanded in body context (after impl registration),
    /// the body written absolute for `module`.
    fn projection_alias(&self, full: &str, module: &str, at: Span) -> Option<Ty> {
        let body = self.plain_aliases.get(full)?;
        let from = module_of(full);
        if !self.names_projection(body, &from, at) {
            return None;
        }
        let mut out = body.clone();
        self.absolutize(&mut out, &from, module, &HashMap::new(), at);
        Some(out)
    }

    /// Does `ty` (written in `module`) name a projection: `<T as Tr>::X`,
    /// or `A::X` with `A` a type?
    fn names_projection(&self, ty: &Ty, module: &str, at: Span) -> bool {
        struct Find<'x, 'n> {
            names: &'x TypeNames<'n>,
            module: &'x str,
            at: Span,
            found: bool,
        }
        impl crate::walk::AstVisitor for Find<'_, '_> {
            fn ty(&mut self, t: &Ty) {
                match &t.kind {
                    AstTyKind::QPath(_) => self.found = true,
                    AstTyKind::Path(p) => {
                        let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                        let n = self.names;
                        match n.canon(&segs, self.module, &[], self.at) {
                            // Through another alias (`type D = List<B>;`).
                            Some(full) if n.alias_depth.get() < 32 => {
                                if let Some(body) = n.plain_aliases.get(&full) {
                                    n.alias_depth.set(n.alias_depth.get() + 1);
                                    self.found |=
                                        n.names_projection(body, &module_of(&full), self.at);
                                    n.alias_depth.set(n.alias_depth.get() - 1);
                                }
                            }
                            Some(_) => {}
                            None => {
                                self.found |= segs.len() > 1
                                    && n.canon(&segs[..segs.len() - 1], self.module, &[], self.at)
                                        .is_some();
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut f = Find {
            names: self,
            module,
            at,
            found: false,
        };
        crate::walk::walk_ty(&mut f, ty);
        f.found
    }

    /// Rewrite the type names in `ty` (outside `params`) that resolve in
    /// module `from` to absolute paths valid in module `to`.
    fn absolutize(
        &self,
        ty: &mut Ty,
        from: &str,
        to: &str,
        params: &HashMap<String, Ty>,
        at: Span,
    ) {
        let mut rec = |t: &mut Ty| self.absolutize(t, from, to, params, at);
        match &mut ty.kind {
            AstTyKind::Path(p) => {
                for s in &mut p.segments {
                    s.generics.iter_mut().for_each(&mut rec);
                }
                let mut segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                if params.contains_key(segs[0]) || matches!(segs[0], "pkg" | "rok" | "Self") {
                    return;
                }
                // `A::Out`: a projection keeps its last segment.
                let mut tail = None;
                let full = match self.canon(&segs, from, &[], at) {
                    Some(full) => full,
                    None if segs.len() > 1 => {
                        segs.pop();
                        let Some(full) = self.canon(&segs, from, &[], at) else {
                            return;
                        };
                        tail = p.segments.pop();
                        full
                    }
                    None => return,
                };
                let pkg = resolve::package_of(&full);
                let abs: Vec<String> = if full.starts_with("rok::") {
                    full.split("::").map(str::to_owned).collect()
                } else if pkg == resolve::package_of(to) {
                    let rest = full.strip_prefix(&pkg).unwrap_or(&full);
                    std::iter::once("pkg")
                        .chain(rest.split("::").filter(|x| !x.is_empty()))
                        .map(str::to_owned)
                        .collect()
                } else {
                    full.split("::").map(str::to_owned).collect()
                };
                let last = p.segments.pop().map(|s| s.generics).unwrap_or_default();
                let n = abs.len();
                p.segments = abs
                    .into_iter()
                    .enumerate()
                    .map(|(i, name)| rokc_ast::PathSegment {
                        name,
                        generics: if i + 1 == n { last.clone() } else { Vec::new() },
                    })
                    .collect();
                p.segments.extend(tail);
            }
            AstTyKind::Sum(ts) | AstTyKind::Tuple(ts) => ts.iter_mut().for_each(rec),
            AstTyKind::Array(e, _) | AstTyKind::Nest(e) | AstTyKind::Binding(_, e) => rec(e),
            AstTyKind::QPath(q) => {
                rec(&mut q.self_ty);
                let mut tp = Ty {
                    kind: AstTyKind::Path(q.trait_path.clone()),
                    span: ty.span,
                };
                rec(&mut tp);
                if let AstTyKind::Path(p) = tp.kind {
                    q.trait_path = p;
                }
            }
            AstTyKind::Fn(args, ret, _) => {
                args.iter_mut().for_each(&mut rec);
                rec(ret);
            }
            AstTyKind::Throws { ok, err } => {
                rec(ok);
                rec(err);
            }
            _ => {}
        }
    }

    /// The type key `segments` names from `module`; its errors
    /// (ambiguity, visibility) are reported at `at`.
    fn canon(
        &self,
        segments: &[&str],
        module: &str,
        local_uses: &[Vec<crate::uses::UseEntry>],
        at: Span,
    ) -> Option<String> {
        if !local_uses.iter().all(Vec::is_empty) {
            return self.canon_uncached(segments, module, local_uses, at);
        }
        let key = (segments.join("::"), module.to_owned());
        if let Some(hit) = self.canon_memo.borrow().get(&key) {
            return hit.clone();
        }
        let errors = self.diags.borrow().len();
        let out = self.canon_uncached(segments, module, local_uses, at);
        if self.diags.borrow().len() == errors {
            self.canon_memo.borrow_mut().insert(key, out.clone());
        }
        out
    }

    /// Can `module` see type-namespace key `k`?
    fn visible_type(&self, k: &str, module: &str) -> bool {
        self.visibility
            .get(k)
            .is_none_or(|&vis| visible_from(module, &module_of(k), vis))
    }

    fn canon_uncached(
        &self,
        segments: &[&str],
        module: &str,
        local_uses: &[Vec<crate::uses::UseEntry>],
        at: Span,
    ) -> Option<String> {
        let exists = |k: &str| self.names.contains(k) || self.reexports.contains_key(k);
        let keys = |leaf: &str| {
            self.leaves
                .get_or_init(|| leaves(self.names.iter().chain(self.reexports.keys())))
                .get(leaf)
                .cloned()
                .unwrap_or_default()
        };
        let visible = |k: &str| self.visible_type(k, module);
        let set = NameSet {
            exists: &exists,
            keys: &keys,
            visible: &visible,
        };
        let mut full = match resolve_name(segments, module, local_uses, self.uses, &set) {
            Ok(r) => r?,
            Err(hits) => {
                self.error(
                    at,
                    format!(
                        "type name `{}` is ambiguous in module `{}` — multiple glob imports \
                     resolve it: {}",
                        segments.join("::"),
                        module_display(module),
                        hits.join(", ")
                    ),
                );
                hits.into_iter().next()?
            }
        };
        // Spec 5.6.13: every module on the path as written (a re-export
        // key, before following it) must be visible too.
        if let Some(m) = resolve::hidden_module(&self.mod_vis, module, &full) {
            self.error(at, resolve::hidden_module_msg(&full, &m, module));
        }
        if let Some(t) = self.reexports.get(&full) {
            full.clone_from(t);
        }
        if let Some(&vis) = self.visibility.get(&full) {
            let def_module = module_of(&full);
            if !visible_from(module, &def_module, vis) {
                self.error(
                    at,
                    format!(
                        "type `{full}` is private to module `{}` and cannot be used from \
                     `{}` (spec 5.6 — add `pub` to expose it)",
                        module_display(&def_module),
                        module_display(module)
                    ),
                );
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
        at: Span,
    ) -> Option<String> {
        let full_key = |k: &str| -> Option<String> {
            if self.variants.contains(k) {
                return Some(k.to_owned());
            }
            let (ty, v) = k.rsplit_once("::")?;
            let segs: Vec<&str> = ty.split("::").collect();
            let e = self.canon(&segs, module, local_uses, at)?;
            let key = format!("{e}::{v}");
            self.variants.contains(&key).then_some(key)
        };
        let exists = |k: &str| full_key(k).is_some();
        let keys = |leaf: &str| {
            self.variant_leaves
                .get_or_init(|| leaves(&self.variants))
                .get(leaf)
                .cloned()
                .unwrap_or_default()
        };
        // A variant is as visible as its enum (spec 5.6.9).
        let visible = |k: &str| self.visible_type(&module_of(k), module);
        let set = NameSet {
            exists: &exists,
            keys: &keys,
            visible: &visible,
        };
        match resolve_name(segments, module, local_uses, self.uses, &set) {
            Ok(r) => full_key(&r?),
            Err(hits) => {
                self.error(
                    at,
                    format!(
                        "variant name `{}` is ambiguous in module `{}` — multiple glob imports \
                     resolve it: {}",
                        segments.join("::"),
                        module_display(module),
                        hits.join(", ")
                    ),
                );
                full_key(hits.first()?)
            }
        }
    }

    /// A `fn` type's bounds: `+ Send + Sync` (sorted auto-trait keys),
    /// `unsafe`, `extern "C"`.
    fn fn_bounds(&self, bounds: &rokc_ast::FnTyBounds, module: &str, at: Span) -> crate::FnBounds {
        let mut keys: Vec<String> = bounds
            .auto
            .iter()
            .filter_map(|b| {
                let segs: Vec<&str> = b.segments.iter().map(|s| s.name.as_str()).collect();
                let key = self.trait_key(&segs, module, at);
                if self.auto_traits.contains(&key) {
                    Some(key)
                } else {
                    self.error(
                        at,
                        format!(
                            "`{}` in a `fn` type bound is not an auto trait — only `Send` / \
                         `Sync` can bound a `fn` type",
                            segs.join("::")
                        ),
                    );
                    None
                }
            })
            .collect();
        keys.sort();
        keys.dedup();
        crate::FnBounds {
            auto: keys,
            unsafe_fn: bounds.unsafe_fn,
            c_abi: bounds.c_abi,
        }
    }

    /// Every auto trait, sorted: what a named function (no captures)
    /// carries as a `fn` value.
    fn all_auto(&self) -> crate::FnBounds {
        let mut auto: Vec<String> = self.auto_traits.iter().cloned().collect();
        auto.sort();
        crate::FnBounds {
            auto,
            ..crate::FnBounds::default()
        }
    }

    /// A pre-body integer constant (array lengths in signatures and
    /// fields, const arguments of trait paths): literals and module
    /// `const`s as `module` names them (its `use`s included), through
    /// `const_eval::syntactic_int`.
    fn const_int(&self, c: &rokc_ast::ConstExpr, module: &str) -> Option<i128> {
        self.const_int_in(c, module, &std::cell::RefCell::new(Vec::new()))
    }

    fn const_int_in(
        &self,
        c: &rokc_ast::ConstExpr,
        module: &str,
        seen: &std::cell::RefCell<Vec<String>>,
    ) -> Option<i128> {
        const_eval::syntactic_int(c, &|path| {
            let segs: Vec<&str> = path.split("::").collect();
            let key = self.const_key(&segs, module)?;
            if seen.borrow().contains(&key) {
                return None;
            }
            seen.borrow_mut().push(key.clone());
            let value = rokc_ast::ConstExpr::Expr(Box::new(self.consts[&key].1.clone()));
            let v = self.const_int_in(&value, &module_of(&key), seen);
            seen.borrow_mut().pop();
            v
        })
    }

    /// The module `const` `segments` names from `module`.
    fn const_key(&self, segments: &[&str], module: &str) -> Option<String> {
        let exists = |k: &str| self.consts.contains_key(k);
        let keys = |leaf: &str| {
            self.const_leaves
                .get_or_init(|| leaves(self.consts.keys()))
                .get(leaf)
                .cloned()
                .unwrap_or_default()
        };
        let visible = |_: &str| true;
        let set = NameSet {
            exists: &exists,
            keys: &keys,
            visible: &visible,
        };
        resolve_name(segments, module, &[], self.uses, &set)
            .ok()
            .flatten()
    }

    fn trait_key(&self, segments: &[&str], module: &str, at: Span) -> String {
        self.canon(segments, module, &[], at)
            .filter(|full| self.traits.contains(full))
            .unwrap_or_else(|| segments.last().copied().unwrap_or_default().to_owned())
    }

    fn error(&self, at: Span, msg: String) {
        self.diags
            .borrow_mut()
            .push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                at,
                msg,
            ));
    }

    fn error_help(&self, at: Span, msg: String, help: String) {
        self.diags.borrow_mut().push(
            rokc_diagnostic::RokDiagnostic::error(rokc_diagnostic::ErrorKind::Type, at, msg)
                .with_help(help),
        );
    }
}

/// Where a type is being resolved: the name index, the module the
/// referencing item lives in, and the location its errors go to.
#[derive(Clone, Copy)]
struct Scope<'b> {
    names: &'b TypeNames<'b>,
    module: &'b str,
    at: Span,
}

// AST → HIR. Three passes: register struct names, then function
// signatures, then lower function bodies.
#[must_use]
pub fn lower(program: &Program, prec: &PrecTable) -> HirModule {
    let empty_uses: crate::uses::UseTable = HashMap::new();
    let empty_reexports: Vec<crate::uses::ReExport> = Vec::new();
    lower_full(
        program.clone(),
        prec,
        &[],
        &empty_uses,
        &empty_reexports,
        &crate::HirInput::default(),
        &rokc_diagnostic::SourceMap::new(),
    )
}

#[must_use]
pub fn lower_with_uses(
    program: &Program,
    prec: &PrecTable,
    uses: &crate::uses::UseTable,
) -> HirModule {
    let empty_reexports: Vec<crate::uses::ReExport> = Vec::new();
    lower_full(
        program.clone(),
        prec,
        &[],
        uses,
        &empty_reexports,
        &crate::HirInput::default(),
        &rokc_diagnostic::SourceMap::new(),
    )
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

/// An associated const `(NAME, type, value)`.
type AssocConst = (String, Ty, Expr);

/// One `impl` block (spec 2.9), inherent or of a trait, concrete or
/// generic (`impl<..> Tr for Box<T>`, or a bare `T` for a blanket impl:
/// applies to a type that matches `self_ty` and meets the bounds).
struct Impl {
    /// Empty for an inherent impl.
    trait_key: String,
    /// `impl<T> Get<T> for Box<T> { type Item = T; }`: `[T]` and
    /// `[(Item, T)]`, resolved per instantiation.
    trait_args: Vec<Ty>,
    assoc: Vec<(String, Ty)>,
    generics: rokc_ast::Generics,
    where_clause: Vec<rokc_ast::WherePred>,
    self_ty: Ty,
    module: String,
    /// A generic trait impl's (or structural inherent impl's) method
    /// templates by name, trait default bodies included.
    methods: HashMap<String, GenericMethod>,
    /// Associated consts, trait defaults included (spec 2.8.3a).
    consts: Vec<AssocConst>,
    /// A concrete impl's resolved target, and the trait ref it provides
    /// (arguments with defaults filled, associated types as bindings).
    concrete: Option<(HirTy, Option<TraitRef>)>,
}

impl Impl {
    fn is_generic(&self) -> bool {
        !self.generics.params.is_empty()
    }
}

/// Every impl, in source order, with indexes for the concrete ones.
#[derive(Default)]
struct Impls {
    all: Vec<Impl>,
    /// Concrete trait impls by target.
    by_target: HashMap<MethodTarget, Vec<usize>>,
    /// Concrete trait impls by trait key, in resolution order.
    by_trait: HashMap<String, Vec<usize>>,
}

impl Impls {
    /// Concrete impl `i`'s target and trait ref, once resolved.
    fn resolve(&mut self, i: usize, ty: HirTy, provides: Option<TraitRef>) {
        if let Some(r) = &provides {
            if let Some(t) = method_target_for(&ty) {
                self.by_target.entry(t).or_default().push(i);
            }
            self.by_trait.entry(r.path.clone()).or_default().push(i);
        }
        self.all[i].concrete = Some((ty, provides));
    }

    fn generic(&self) -> impl Iterator<Item = &Impl> {
        self.all.iter().filter(|i| i.is_generic())
    }

    /// The trait refs of the concrete impls on `ty`.
    fn refs_on<'s>(&'s self, ty: &HirTy) -> impl Iterator<Item = &'s TraitRef> + use<'s> {
        method_target_for(ty)
            .and_then(|t| self.by_target.get(&t))
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .filter_map(|&i| self.all[i].concrete.as_ref()?.1.as_ref())
    }

    /// The targets of trait `key`'s concrete impls, in resolution order.
    fn tys_of(&self, key: &str) -> impl Iterator<Item = &HirTy> {
        self.by_trait
            .get(key)
            .into_iter()
            .flatten()
            .filter_map(|&i| Some(&self.all[i].concrete.as_ref()?.0))
    }
}

/// Every struct / union and enum definition by id: the declared ones,
/// and a generic one's instances, made when a type first names them
/// (`instantiate_struct` / `instantiate_enum`), whatever resolves it.
#[derive(Default)]
struct TypeDefs<'a> {
    structs: std::cell::RefCell<Vec<HirStructDef>>,
    struct_table: std::cell::RefCell<HashMap<String, StructId>>,
    enums: std::cell::RefCell<Vec<HirEnumDef>>,
    enum_table: std::cell::RefCell<HashMap<String, EnumId>>,
    /// Generic templates by full name.
    generic_structs: HashMap<String, &'a AstStructDef>,
    generic_enums: HashMap<String, &'a AstEnumDef>,
    /// Leaf names of templates whose parameters all have defaults: their
    /// bare name is an instance (spec 2.10.5).
    defaulted_leaves: std::collections::HashSet<String>,
}

impl TypeDefs<'_> {
    fn generics_of(&self, base: &str) -> Option<&rokc_ast::Generics> {
        self.generic_structs
            .get(base)
            .map(|d| &d.generics)
            .or_else(|| self.generic_enums.get(base).map(|d| &d.generics))
    }

    /// `base` written without arguments names its all-defaults instance.
    fn bare_instance(&self, base: &str) -> bool {
        self.generics_of(base).is_some_and(mono::all_defaulted)
    }

    fn struct_id(&self, key: &str) -> Option<StructId> {
        self.struct_table.borrow().get(key).copied()
    }

    fn enum_id(&self, key: &str) -> Option<EnumId> {
        self.enum_table.borrow().get(key).copied()
    }

    /// Instance `base<args>` of a generic struct (the existing one, or a
    /// new one first named at `span`): its id is taken before `fields`
    /// resolves its field types under the instance's substitution, so a
    /// field naming the instance itself (or another new one) finds it.
    fn instantiate_struct(
        &self,
        base: &str,
        args: Vec<HirTy>,
        span: rokc_diagnostic::Span,
        fields: impl FnOnce(&AstStructDef, &TySubst) -> Vec<HirField>,
    ) -> Option<StructId> {
        let key = mangle_inst(base, &args);
        if let Some(id) = self.struct_id(&key) {
            return Some(id);
        }
        let def = *self.generic_structs.get(base)?;
        let id = StructId(u32::try_from(self.structs.borrow().len()).expect("StructId overflow"));
        crate::name_type(false, id.0, base, &args);
        self.struct_table.borrow_mut().insert(key.clone(), id);
        self.structs.borrow_mut().push(HirStructDef {
            id,
            repr: collect::repr_of(&def.attrs).unwrap_or_default(),
            def_id: None,
            name: key,
            fields: Vec::new(),
            span,
            generic_args: args.clone(),
            union_kind: None,
            niche: collect::niche_args(&def.attrs).unwrap_or_default(),
        });
        let fields = fields(def, &generic_subst(&def.generics, &args));
        self.structs.borrow_mut()[id.0 as usize].fields = fields;
        Some(id)
    }

    /// `instantiate_struct` for a generic enum.
    fn instantiate_enum(
        &self,
        base: &str,
        args: Vec<HirTy>,
        span: rokc_diagnostic::Span,
        variants: impl FnOnce(&AstEnumDef, &TySubst) -> Vec<HirEnumVariant>,
    ) -> Option<EnumId> {
        let key = mangle_inst(base, &args);
        if let Some(id) = self.enum_id(&key) {
            return Some(id);
        }
        let def = *self.generic_enums.get(base)?;
        let id = EnumId(u32::try_from(self.enums.borrow().len()).expect("EnumId overflow"));
        crate::name_type(true, id.0, base, &args);
        self.enum_table.borrow_mut().insert(key.clone(), id);
        self.enums.borrow_mut().push(HirEnumDef {
            id,
            repr: collect::repr_of(&def.attrs).unwrap_or_default(),
            def_id: None,
            name: key,
            variants: Vec::new(),
            span,
            generic_args: args.clone(),
        });
        let variants = variants(def, &generic_subst(&def.generics, &args));
        self.enums.borrow_mut()[id.0 as usize].variants = variants;
        Some(id)
    }
}

/// Module-wide, read-only lowering environment shared by every function
/// body (plus the interior-mutable `sink`).
struct Env<'a> {
    /// The compile's source files (`#[track_caller]` / `throw` sites).
    sources: &'a rokc_diagnostic::SourceMap,
    fn_table: HashMap<String, FnSig>,
    /// `fn_table` and `generic_fns` keys by last segment (both are
    /// complete before any body is lowered).
    fn_leaves: std::cell::OnceCell<Leaves>,
    /// `extern` fns: one global C namespace, callable by bare name from
    /// every module (they are not module items, spec 5.9).
    extern_fns: std::collections::HashSet<String>,
    /// Concrete methods by `(type, name)`: several when traits share a
    /// method name (`pick_method` chooses, spec 4.9.6).
    method_table: HashMap<(MethodTarget, String), Vec<FunctionId>>,
    /// `fn_table` key of every function id (method signatures).
    key_of: HashMap<FunctionId, String>,
    /// Declarations whose return type is inferred from the body.
    infer_ret: std::collections::HashSet<FunctionId>,
    /// `RootMain::Implicit`.
    implicit_main: bool,
    /// `RootMain::Harness`.
    harness_main: bool,
    /// Bodies without `-> T` that may diverge on every path
    /// (`collect::may_diverge`), by span.
    may_diverge: std::collections::HashSet<rokc_diagnostic::Span>,
    method_info: HashMap<FunctionId, MethodInfo>,
    /// Every struct / union / enum, declared or instantiated.
    defs: TypeDefs<'a>,
    /// Module-level `const NAME: T = expr;` items. A bare `Path(NAME)`
    /// resolves to the const's value expression inlined at the use site.
    consts: HashMap<String, (Ty, Expr)>,
    const_leaves: std::cell::RefCell<(usize, Leaves)>,
    /// Generic function templates keyed by name. `lower_call` queries
    /// this when the callee path matches a generic function.
    generic_fns: HashMap<String, &'a FnDef>,
    /// Methods of generic impls (and generic methods), keyed by
    /// `(generic base of the impl target, method name)`. Called through
    /// `monomorphize` when `method_table` has no concrete entry.
    generic_methods: HashMap<(String, String), Vec<GenericMethod>>,
    /// `#[intrinsic("rok.OP.TYPE")]` methods (`Prim` / `Convert`): calls
    /// lower to the op.
    intrinsics: HashMap<FunctionId, collect::Intrinsic>,
    /// Generic `#[intrinsic]` functions by name.
    generic_intrinsics: HashMap<String, collect::Intrinsic>,
    /// `extern "C"` functions: a `fn` argument must be a named fn (a C
    /// function pointer), not a closure or `fn` variable.
    extern_fn_ids: std::collections::HashSet<FunctionId>,
    /// `extern "rok"` declarations: the runtime's own functions.
    rok_externs: std::collections::HashSet<FunctionId>,
    /// C variadic `extern` declarations (`fn printf(fmt: str, ...)`):
    /// extra arguments take the C default argument promotions.
    c_variadic: std::collections::HashSet<FunctionId>,
    /// `extern "C" fn` definitions (spec 5.9.10): with `extern_fn_ids`,
    /// the named functions an `extern "C" fn(..)` value can point to.
    c_defs: std::collections::HashSet<FunctionId>,
    prec: &'a PrecTable,
    sink: ClosureSink,
    /// Visibility of every value-namespace item, keyed by full name.
    item_visibility: HashMap<String, Visibility>,
    /// Struct name → field name → visibility.
    field_vis: HashMap<String, HashMap<String, Visibility>>,
    /// Per-module `use` table — feeds into bare-name and unresolved
    /// path lookups. Empty when no `use` declarations were collected.
    uses: &'a crate::uses::UseTable,
    /// Every impl (bounds, dispatch, projections, associated consts).
    impls: Impls,
    /// `unsafe fn`s and C functions (spec 4.15): calls need an unsafe scope.
    unsafe_fns: std::collections::HashSet<FunctionId>,
    /// `impl !Send for S {}` opt-outs: `(generic base of S, trait key)`.
    neg_auto: std::collections::HashSet<(String, String)>,
    /// Trait key → declared methods + supertraits (`any Tr` calls).
    trait_info: HashMap<String, TraitInfo>,
    /// Module-level `static` items by name → declared type.
    statics: HashMap<String, HirTy>,
    static_leaves: std::cell::RefCell<(usize, Leaves)>,
    /// Statics that may be assigned (`extern` `static mut`, spec 5.9.3).
    mut_statics: std::collections::HashSet<String>,
    /// `#[literal]` handlers of the built-in literal shapes (spec 6.5).
    literal_shapes: Vec<ShapeHandler>,
    names: TypeNames<'a>,
    /// Every non-generic function by `FunctionId` (the ids below
    /// `sink.next_id`'s start).
    decls: Vec<MethodOrFn<'a>>,
    /// `#[non_exhaustive]` structs and enums (spec 6.2.10), by name.
    non_exhaustive: std::collections::HashSet<String>,
}

/// A handler registered with a built-in shape's pattern (`[..]` etc.).
struct ShapeHandler {
    shape: rokc_parser::Shape,
    /// The handler's full name.
    name: String,
    priority: i64,
    /// The `#[literal]` attribute.
    span: rokc_diagnostic::Span,
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
    /// The trait's type parameters, in order (`Index<K>` → `[K]`).
    params: Vec<String>,
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
        /// Borrowed from the program, or a trait default with the
        /// impl's trait arguments substituted into its signature.
        fn_def: std::borrow::Cow<'a, FnDef>,
        self_ty: HirTy,
        module: String,
        /// `fn_table` key, also the function's name.
        key: String,
        /// A trait default body's trait parameters → this impl's
        /// arguments (`trait Dim<const D: usize>` + `impl Dim<3>`).
        subst: HashMap<String, HirTy>,
    },
}

impl MethodOrFn<'_> {
    fn def(&self) -> &FnDef {
        match self {
            Self::Fn(f) => f,
            Self::Method { fn_def, .. } => fn_def,
        }
    }
}

/// A function with `ref` parameters (spec 4.7, `ref self` included),
/// passed copy-in / copy-out: it returns `ret` packed with each `ref`
/// parameter's final value (`ref_packed`), and the call site writes
/// those back into the argument places.
#[derive(Clone)]
struct RefOut {
    /// The declared return (a `Throws` carrier for a throwing fn).
    ret: HirTy,
    /// `(parameter index, type)` of each `ref` parameter.
    refs: Vec<(usize, HirTy)>,
}

/// A projection being resolved: base type, associated name, trait filter.
type ProjectionGoal = (HirTy, String, Option<Vec<String>>);

/// Per-function signature used by lowering. Avoids re-resolving the AST
/// return type at every call site. `param_defaults` mirrors the function's
/// parameter list — each entry is `Some(expr)` if the parameter has a
/// default value the caller may omit, else `None`.
#[derive(Clone)]
struct FnSig {
    id: FunctionId,
    ret_ty: HirTy,
    param_defaults: Vec<Option<Expr>>,
    /// Resolved parameter types: the expected types of the arguments, so
    /// an untyped closure argument takes its parameter types from them.
    param_tys: Vec<HirTy>,
    /// Parameter names, to place named arguments (spec 4.1).
    param_names: Vec<String>,
    /// Which parameters are `ref` (empty = none).
    param_refs: Vec<bool>,
    /// The last parameter is a variadic `...T` (a `Slice<T>` the call
    /// builds from its trailing arguments, spec 4.2.5).
    variadic: bool,
}

// If `slot_ty` is a Sum and `value.ty` matches one of its variants,
// wrap the value into the sum's tagged-union representation.
fn wrap_into_sum(slot_ty: &HirTy, value: HirExpr) -> HirExpr {
    let HirTy::Sum(variants) = slot_ty else {
        return value;
    };
    let Some(idx) = sum_variant_index(variants, &value.ty) else {
        // A nested optional (spec 2.6.4): a value of the inner type's
        // members goes in wrapped by the inner sum.
        return match variants.iter().find(|v| nested_fits(v, &value.ty)) {
            Some(inner) => wrap_into_sum(slot_ty, wrap_into_sum(inner, value)),
            None => value,
        };
    };
    let span = value.span;
    if variants[idx].is_none() {
        return wrap_none(slot_ty, idx, value);
    }
    HirExpr {
        kind: HirExprKind::SumWrap {
            sum_ty: slot_ty.clone(),
            variant_index: u32::try_from(idx).expect("variant overflow"),
            value: Some(Box::new(value)),
        },
        ty: slot_ty.clone(),
        span,
    }
}

/// `value: none` as member `idx` of `slot_ty`. The tag needs no payload,
/// but the value may have effects (`{ f(); none }`, an `if` / `match`
/// / call yielding `none`): the wrap moves into its branches, or the
/// value runs first.
fn wrap_none(slot_ty: &HirTy, idx: usize, mut value: HirExpr) -> HirExpr {
    let span = value.span;
    let tag = HirExpr {
        kind: HirExprKind::SumWrap {
            sum_ty: slot_ty.clone(),
            variant_index: u32::try_from(idx).expect("variant overflow"),
            value: None,
        },
        ty: slot_ty.clone(),
        span,
    };
    let wrap_block = |b: &mut HirBlock| {
        if let Some(t) = b.trailing.take() {
            b.trailing = Some(wrap_none(slot_ty, idx, t));
        }
    };
    match &mut value.kind {
        HirExprKind::Const(_) | HirExprKind::Local(_) | HirExprKind::UnresolvedPath(_) => tag,
        HirExprKind::Block(b) => {
            wrap_block(b);
            value.ty = slot_ty.clone();
            value
        }
        HirExprKind::If {
            then_block,
            else_branch: Some(e),
            ..
        } => {
            wrap_block(then_block);
            let inner = std::mem::replace(&mut **e, tag);
            **e = wrap_none(slot_ty, idx, inner);
            value.ty = slot_ty.clone();
            value
        }
        HirExprKind::Match { arms, .. } => {
            for a in arms.iter_mut() {
                let body = std::mem::replace(&mut a.body, tag.clone());
                a.body = wrap_none(slot_ty, idx, body);
            }
            value.ty = slot_ty.clone();
            value
        }
        _ => HirExpr {
            kind: HirExprKind::Block(Box::new(HirBlock {
                stmts: vec![HirStmt::Expr(value)],
                trailing: Some(tag),
                label: None,
            })),
            ty: slot_ty.clone(),
            span,
        },
    }
}

/// Re-tag a sum value as the sum `to`, member by member: `match value
/// { b: V => <b wrapped into to>, .. }` for each member `V` of the
/// value's sum that `to` also has. Widening (every member is in `to`)
/// is total; for a sub-sum type pattern the arms left out can't occur.
fn resum(ctx: &mut LowerCtx<'_>, value: HirExpr, to: &HirTy) -> HirExpr {
    // An `any` value (narrowed by `x: A | B`) is matched by tag.
    let members: Vec<(u32, HirTy)> = match (&value.ty, to) {
        (HirTy::Sum(vs), HirTy::Sum(ws)) => vs
            .iter()
            .enumerate()
            .filter(|(_, v)| ws.contains(v))
            .map(|(i, v)| (u32::try_from(i).expect("variant overflow"), v.clone()))
            .collect(),
        // A stored `to` value, or one of its members.
        (HirTy::AnyTrait(_), HirTy::Sum(ws)) => std::iter::once(to)
            .chain(ws)
            .map(|w| (ctx.any_tag(w), w.clone()))
            .collect(),
        _ => return value,
    };
    let span = value.span;
    let arms = members
        .into_iter()
        .map(|(i, v)| {
            let b = ctx.declare(None, v.clone());
            HirMatchArm {
                pat: HirPattern::SumVariant {
                    sum_ty: value.ty.clone(),
                    variant_index: i,
                    binder: Some(b),
                    payload_ty: Some(v.clone()),
                },
                guard: None,
                body: wrap_into_sum(to, hir_local(b, &v, span)),
            }
        })
        .collect();
    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(value),
            arms,
        },
        ty: to.clone(),
        span,
    }
}

/// Is `member` (of an outer sum) a nested sum that takes a `value_ty`
/// value by injection — `i32` or `none` into the `i32 | none` of
/// `(i32 | none)?` (spec 2.6.4)?
fn nested_fits(member: &HirTy, value_ty: &HirTy) -> bool {
    match member {
        HirTy::Sum(ws) => {
            sum_variant_index(ws, value_ty).is_some() || ws.iter().any(|w| nested_fits(w, value_ty))
        }
        _ => false,
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
    let exact = |a: &[HirTy], b: &[HirTy]| {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| ty_exact(x, y))
    };
    match (expected, actual) {
        // `!` (a diverging expression) fits any slot.
        (HirTy::Unknown | HirTy::Any, _) | (_, HirTy::Unknown | HirTy::Any | HirTy::Never) => true,
        (HirTy::Sum(vs), a) if !matches!(a, HirTy::Sum(_)) => sum_variant_index(vs, a).is_some(),
        (HirTy::Tuple(a), HirTy::Tuple(b)) | (HirTy::Sum(a), HirTy::Sum(b)) => all(a, b),
        (HirTy::Array(a, n), HirTy::Array(b, m)) => n == m && ty_compatible(a, b),
        (HirTy::GcBuf(a), HirTy::GcBuf(b)) => ty_compatible(a, b),
        // `fn() + Send` flows into `fn()`, not the reverse.
        // A `fn() -> !` value is no `fn() -> R` pointer (different
        // return ABI): only `adapt_never_fn` makes one from a named fn.
        // Spec 4.4.9: no fn subtyping — parameters and return match exactly.
        (HirTy::Fn(a1, r1, b1), HirTy::Fn(a2, r2, b2)) => {
            exact(a1, a2)
                && ty_exact(r1, r2)
                && (**r2 != HirTy::Never || **r1 == HirTy::Never)
                && fn_bounds_fit(b1, b2)
        }
        // Spec 4.4.2: a closure is a value of its `fn` type (`coerce`
        // checks a bound against its captures).
        (
            HirTy::Fn(a1, r1, _),
            HirTy::Closure {
                args: a2, ret: r2, ..
            },
        ) => exact(a1, a2) && ty_exact(r1, r2),
        // Error types must match exactly: a wider error slot has another
        // carrier layout (fn values are adapted by `adapt_fn_value`).
        (HirTy::Throws { ok: o1, err: e1 }, HirTy::Throws { ok: o2, err: e2 }) => {
            ty_compatible(o1, o2) && (e1 == e2 || **e1 == HirTy::Unknown || **e2 == HirTy::Unknown)
        }
        _ => expected == actual,
    }
}

/// Type identity inside a fn type: `ty_compatible` without sum
/// widening (an unresolved type still matches anything).
fn ty_exact(a: &HirTy, b: &HirTy) -> bool {
    let all = |a: &[HirTy], b: &[HirTy]| {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| ty_exact(x, y))
    };
    match (a, b) {
        (HirTy::Unknown | HirTy::Any, _) | (_, HirTy::Unknown | HirTy::Any) => true,
        (HirTy::Tuple(a), HirTy::Tuple(b)) | (HirTy::Sum(a), HirTy::Sum(b)) => all(a, b),
        (HirTy::Array(a, n), HirTy::Array(b, m)) => n == m && ty_exact(a, b),
        (HirTy::GcBuf(a), HirTy::GcBuf(b)) => ty_exact(a, b),
        (HirTy::Fn(..), HirTy::Fn(..) | HirTy::Closure { .. }) => ty_compatible(a, b),
        (HirTy::Throws { ok: o1, err: e1 }, HirTy::Throws { ok: o2, err: e2 }) => {
            ty_exact(o1, o2) && ty_exact(e1, e2)
        }
        _ => a == b,
    }
}

/// Wrap `value` into `slot` (sum injection) and report a type mismatch.
/// `what` names the slot for the diagnostic ("argument 1 of `f`").
fn coerce(
    ctx: &mut LowerCtx<'_>,
    slot: &HirTy,
    value: HirExpr,
    what: &dyn Fn() -> String,
) -> HirExpr {
    if infer::unify_value(ctx, slot, &value) {
        return value;
    }
    // A diverging block has type `!`: it fits any slot (spec 3.9).
    if hir_expr_diverges(&value) {
        return value;
    }
    let value = c_fn_value(ctx, slot, value);
    let value = adapt_never_fn(ctx, slot, value);
    let value = adapt_fn_value(ctx, slot, value);
    let value = box_into_any(ctx, slot, value);
    let value = drop_fn_bounds(slot, value);
    // Spec 2.6.4: a sum flows into any sum holding all its members.
    let value = match (&value.ty, slot) {
        (HirTy::Sum(vs), HirTy::Sum(ws)) if vs != ws && vs.iter().all(|v| ws.contains(v)) => {
            resum(ctx, value, slot)
        }
        // Into a nested optional's inner sum (spec 2.6.4): a sub-sum of
        // it re-tagged, then wrapped by the outer layer.
        (HirTy::Sum(vs), HirTy::Sum(ws)) if !ws.contains(&value.ty) => {
            let inner = ws
                .iter()
                .find(|w| matches!(w, HirTy::Sum(is) if vs.iter().all(|v| is.contains(v))));
            match inner.cloned() {
                Some(inner) => resum(ctx, value, &inner),
                None => value,
            }
        }
        _ => value,
    };
    let mut v = wrap_into_sum(slot, value);
    // Same `{code, env}` layout: the closure takes the slot's type once
    // its captures meet the slot's bounds (`+ Send`).
    let closure_fits = |v: &HirExpr| match (slot, &v.ty) {
        (HirTy::Fn(_, _, want), HirTy::Closure { .. }) => {
            ty_compatible(slot, &v.ty) && want.auto.iter().all(|b| ctx.has_trait(&v.ty, b))
        }
        _ => false,
    };
    if closure_fits(&v) {
        v.ty = slot.clone();
    }
    // An unknown type name is reported on its own.
    let unknown_slot = matches!(slot, HirTy::Path(_)) && {
        let mut names = Vec::new();
        collect::collect_unknown_paths(slot, &mut names);
        !names.is_empty()
    };
    if !unknown_slot
        && (!ty_compatible(slot, &v.ty)
            || matches!(v.ty, HirTy::Closure { .. } if matches!(slot, HirTy::Fn(..))))
    {
        let hint = fn_mismatch_hint(slot, &v.ty);
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "mismatched types: {} expects `{}`, found `{}`{hint}",
                what(),
                ctx.ty_name(slot),
                ctx.ty_name(&v.ty)
            ),
        );
        if let (Some(note), Some(d)) = (
            ctx.closure_bound_note(&v),
            ctx.env.sink.diagnostics.borrow_mut().last_mut(),
        ) {
            d.notes.push(note);
        }
    }
    v
}

/// Why a function value does not fit a `fn` slot (`""`: no hint).
fn fn_mismatch_hint(slot: &HirTy, ty: &HirTy) -> &'static str {
    if matches!((slot, ty), (HirTy::Fn(_, _, want), HirTy::Closure { .. }) if *want != crate::FnBounds::default())
    {
        " — the closure's captures don't meet the `fn` type's bounds"
    } else if matches!((slot, ty), (HirTy::Fn(_, _, want), HirTy::Fn(_, _, have))
        if have.unsafe_fn && !want.unsafe_fn)
    {
        " — an `unsafe fn` value only fits an `unsafe fn` type (spec 4.15)"
    } else if matches!((slot, ty), (HirTy::Fn(_, _, want), HirTy::Fn(_, _, have))
        if want.c_abi != have.c_abi)
    {
        " — an `extern \"C\" fn` value is a bare C function pointer, not a rok `fn` value \
         (spec 5.9.4)"
    } else if matches!((slot, ty), (HirTy::Fn(_, _, want), HirTy::Fn(_, _, have))
        if !fn_bounds_fit(want, have))
    {
        " — a `fn` value must already carry the bound in its type; only a named \
         function or a capture-free closure is always `Send + Sync`"
    } else if matches!((slot, ty), (HirTy::Fn(_, r, _), HirTy::Fn(..))
        if matches!(**r, HirTy::Throws { .. }))
    {
        " — a function value fits a `fn` type that throws more only with the same \
         parameters and result (spec 4.4.9)"
    } else {
        ""
    }
}

/// Spec 5.9.4: a named C-ABI function (an `extern` block declaration
/// or an `extern "C" fn` definition) fills an `extern "C" fn(..)` slot
/// (or such a member of a sum slot) as its own address: the value is
/// retyped, and MIR takes the thin code pointer (the C ABI entry).
fn c_fn_value(ctx: &LowerCtx<'_>, slot: &HirTy, mut value: HirExpr) -> HirExpr {
    let (HirExprKind::FnRef(id), HirTy::Fn(va, vr, have)) = (&value.kind, &value.ty) else {
        return value;
    };
    if have.c_abi {
        return value;
    }
    let fits = |t: &&HirTy| matches!(t, HirTy::Fn(a, r, want) if want.c_abi && a == va && r == vr);
    let target = match slot {
        HirTy::Sum(vs) => vs.iter().find(fits),
        s => Some(s).filter(fits),
    };
    if target.is_none() {
        return value;
    }
    if !(ctx.env.extern_fn_ids.contains(id) || ctx.env.c_defs.contains(id)) {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            "only an `extern \"C\"` function (an `extern` block declaration or an \
             `extern \"C\" fn` definition) is an `extern \"C\" fn(..)` value (spec 5.9.4)"
                .to_owned(),
        );
    }
    let mut bounds = have.clone();
    bounds.c_abi = true;
    value.ty = HirTy::Fn(va.clone(), vr.clone(), bounds);
    value
}

/// Can a `fn` value with bounds `have` fill a slot with bounds `want`?
/// It must carry every auto trait the slot names, and an `unsafe
/// fn` only fills an `unsafe fn` slot (a safe one fills either).
fn fn_bounds_fit(want: &crate::FnBounds, have: &crate::FnBounds) -> bool {
    want.auto.iter().all(|b| have.auto.contains(b))
        && (!have.unsafe_fn || want.unsafe_fn)
        && want.c_abi == have.c_abi
}

/// A `fn` value with more auto-trait bounds than the slot (or the
/// slot's matching sum variant) asks for takes the slot's type, so
/// `fn() + Send` → `fn()` (and → `fn() | none`) needs no conversion.
fn drop_fn_bounds(slot: &HirTy, mut value: HirExpr) -> HirExpr {
    let HirTy::Fn(va, vr, have) = &value.ty else {
        return value;
    };
    let fits = |t: &&HirTy| {
        matches!(t, HirTy::Fn(a, r, want)
            if a == va && r == vr && fn_bounds_fit(want, have))
    };
    let target = match slot {
        HirTy::Sum(vs) => vs.iter().find(fits),
        s => Some(s).filter(fits),
    };
    if let Some(t) = target {
        value.ty = t.clone();
    }
    value
}

/// Does an `any` value with bounds `have` satisfy bound `want`? Yes
/// when some bound or one of its supertraits (transitively) is `want`;
/// `any Tr<i32>` also satisfies `any Tr` (arguments unconstrained).
fn bound_covers(ctx: &LowerCtx<'_>, have: &[TraitRef], want: &TraitRef) -> bool {
    let mut stack: Vec<TraitRef> = have.to_vec();
    let mut seen: Vec<String> = Vec::new();
    while let Some(h) = stack.pop() {
        if h == *want || (want.is_plain() && h.path == want.path) {
            return true;
        }
        if let (false, Some(info)) = (seen.contains(&h.path), ctx.env.trait_info.get(&h.path)) {
            stack.extend(info.supers.iter().map(|s| TraitRef::plain(s)));
        }
        seen.push(h.path);
    }
    false
}

/// Does a value of `ty` (not `any`) or an `any` value meet bound `b`?
fn meets(ctx: &LowerCtx<'_>, ty: &HirTy, b: &TraitRef) -> bool {
    match ty {
        HirTy::AnyTrait(have) => bound_covers(ctx, have, b),
        _ => ctx.implements_trait(ty, b, 0),
    }
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

/// Store check + boxing: a value flowing into an `any Tr` slot must
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
            let names: Vec<String> = bounds
                .iter()
                .filter(|b| !ctx.implements_trait(ty, b, 0))
                .map(|b| format!("`{}`", ctx.trait_name(b)))
                .collect();
            if !names.is_empty() {
                return ctx.error_expr(
                    value.span,
                    format!(
                        "`{}` does not implement {}, so it cannot be stored in an `{}` slot",
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

/// A default value (`x: T = e`, `f: T = e`) resolved where it is
/// declared, not at the use that splices it in (spec 4.2.3).
fn in_module(module: &str, e: Expr) -> Expr {
    Expr {
        span: e.span,
        kind: ExprKind::InModule(module.to_owned(), Box::new(e)),
    }
}

/// `ty_compatible`, or storable through `box_into_any`.
fn coercible(ctx: &LowerCtx<'_>, slot: &HirTy, ty: &HirTy) -> bool {
    ty_compatible(slot, ty)
        || matches!(any_slot_for(slot, ty), Some(HirTy::AnyTrait(bs))
        if bs.iter().all(|b| meets(ctx, ty, b)))
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
        | HirStmt::Return(Some(e))
        | HirStmt::Panic(e) => in_expr(e),
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
    /// `ref x` (spec 4.7.3).
    Ref(&'e Expr),
    /// A dict spread's read of this parameter (spec 4.2.6): the index of
    /// its built expression.
    Dict(usize),
}

/// Shared mutable sink for closures lifted into anonymous top-level
/// functions, generic-function monomorphizations and lazily instantiated
/// generic structs. Lowering pushes here as it walks expressions.
type TySubst = HashMap<String, HirTy>;

#[derive(Default)]
struct InstanceWarns {
    instances: HashMap<rokc_diagnostic::Span, std::collections::HashSet<FunctionId>>,
    warns: Vec<(
        rokc_diagnostic::Span,
        rokc_diagnostic::RokDiagnostic,
        std::collections::HashSet<FunctionId>,
    )>,
}

impl InstanceWarns {
    /// The warnings every instance of their template raised.
    fn agreed(self) -> impl Iterator<Item = rokc_diagnostic::RokDiagnostic> {
        let instances = self.instances;
        self.warns
            .into_iter()
            .filter(move |(t, _, by)| instances.get(t).is_some_and(|all| all.is_subset(by)))
            .map(|(_, d, _)| d)
    }
}

struct ClosureSink {
    extras: std::cell::RefCell<Vec<HirFunction>>,
    /// Functions with `ref` parameters (spec 4.7, `ref self` included).
    ref_out: std::cell::RefCell<HashMap<FunctionId, RefOut>>,
    next_id: std::cell::Cell<u32>,
    /// Cached monomorphizations: `(generic_fn_name, concrete_type_args)`
    /// → specialized `FunctionId`.
    mono_cache: std::cell::RefCell<HashMap<(String, Vec<String>), FunctionId>>,
    /// Specialized `FnSig` per monomorphization for call-site lookup.
    mono_sigs: std::cell::RefCell<HashMap<FunctionId, FnSig>>,
    /// Current monomorphization nesting (bounded by `MONO_DEPTH_LIMIT`).
    mono_depth: std::cell::Cell<u32>,
    /// Bumped by every "type annotations needed" failure (a generic
    /// parameter / literal with nothing to infer it from), so an
    /// un-annotated `let` knows to look at its later uses.
    uninferred: std::cell::Cell<u32>,
    /// `any` type tags of the concrete types stored so far (`any_tag`).
    any_tags: std::cell::RefCell<Vec<(HirTy, u32)>>,
    /// `any Tr` method dispatchers (bodies built after all lowering).
    any_dispatch: std::cell::RefCell<Vec<expr::AnyDispatch>>,
    /// `T::Item` projections being resolved (cuts `impl<I: Iterator>
    /// IntoIterator for I { type Item = I::Item; }` cycles).
    projecting: std::cell::RefCell<Vec<ProjectionGoal>>,
    /// Adapter thunks (`adapt_fn_value` / `adapt_never_fn`) by
    /// `kind|callee|slot type|callee type`.
    thunks: std::cell::RefCell<HashMap<String, FunctionId>>,
    /// Generic instance bodies being lowered: `(template span, instance
    /// id)`, `None` for a non-instance body nested in one.
    instances: std::cell::RefCell<Vec<Option<(rokc_diagnostic::Span, FunctionId)>>>,
    /// Instances lowered per template, and the warnings each raised
    /// (keyed by template, span, message): a warning is reported when
    /// every instance of its template raised it.
    instance_warns: std::cell::RefCell<InstanceWarns>,
    /// Diagnostics emitted during lowering (`HirModule.diagnostics`).
    diagnostics: std::cell::RefCell<Vec<rokc_diagnostic::RokDiagnostic>>,
    /// Inference variables (`infer`): one per open type parameter of an
    /// un-annotated `let` being inferred from its later uses.
    infer_vars: std::cell::RefCell<Vec<infer::Var>>,
    /// `let` inferences in progress: unification only runs when > 0.
    infer_depth: std::cell::Cell<u32>,
    /// Variables before the outermost inference in progress.
    infer_floor: std::cell::Cell<usize>,
    /// Every lowered function's `(const fn, standard library)`.
    fn_origin: std::cell::RefCell<HashMap<FunctionId, (bool, bool)>>,
    /// Lowered `#[track_caller]` functions (`caller`).
    track_caller: std::cell::RefCell<std::collections::HashSet<FunctionId>>,
    /// Declarations being lowered for a compile-time evaluation.
    const_lowering: std::cell::RefCell<std::collections::HashSet<FunctionId>>,
    /// Const items being lowered, innermost last (cycle check).
    const_stack: std::cell::RefCell<Vec<String>>,
    /// Return types inferred from bodies (spec 4.1.3), by function;
    /// `None` while the body is being inferred.
    inferred_ret: std::cell::RefCell<HashMap<FunctionId, Option<HirTy>>>,
    /// Declarations whose inference lowering was final, by id, with the
    /// first function id it could have made (for `rollback`): the decl
    /// pass takes them instead of lowering again.
    inferred_fns: std::cell::RefCell<HashMap<FunctionId, (u32, HirFunction)>>,
    /// Every reachable body is lowered: a later inference (a signature
    /// asked for by a check) must leave no functions behind.
    bodies_done: std::cell::Cell<bool>,
    /// Call sites of the implicit-generic instances being lowered
    /// (spec 4.2.2: their body errors point at the call too).
    call_sites: std::cell::RefCell<Vec<(String, rokc_diagnostic::Span)>>,
    /// Calls met of functions whose return type is being inferred.
    recursive_ret: std::cell::RefCell<Vec<FunctionId>>,
    /// Inferred return types that depend on a fn still being inferred:
    /// dropped once it is done.
    tentative_ret: std::cell::RefCell<Vec<FunctionId>>,
}

/// Per-function lowering state: scoped name → local-id map plus the
/// running list of local declarations, on top of the shared `Env`.
#[derive(Clone)]
#[allow(clippy::struct_excessive_bools)] // independent per-body modes
struct LowerCtx<'a> {
    env: &'a Env<'a>,
    locals: Vec<HirLocal>,
    scopes: Vec<HashMap<String, LocalId>>,
    /// Per-monomorphization type-parameter substitution. Empty for
    /// non-generic functions. `T` → concrete `HirTy` overrides the
    /// alias table when both contain the same name.
    /// Owned while an associated const's value lowers under its impl's.
    ty_subst: std::borrow::Cow<'a, TySubst>,
    self_ty: Option<HirTy>,
    /// Enclosing function's (or closure's) return type. `return v;`
    /// checks against it and wraps `v` into a matching sum type.
    fn_ret_ty: HirTy,
    /// Closure without a declared / expected return type: the first
    /// `return v;` fixes `fn_ret_ty`.
    infer_ret: bool,
    /// Inferring a function's return type (spec 4.1.3): the types of
    /// its `return` values and trailing value.
    ret_tys: Option<Vec<HirTy>>,
    /// Lowering the implicit `main` built from top-level statements,
    /// where `return` is not allowed (spec 4.16.4). Closures get a fresh
    /// context, so a `return` inside one stays legal.
    implicit_main: bool,
    /// Lowering the test harness `main` (`RootMain::Harness`).
    harness_main: bool,
    /// The `ref` parameters' locals and types (`ref self` included);
    /// every return also hands their values back (copy-out).
    ref_params: Vec<(LocalId, HirTy)>,
    /// Bindings some closure in this function captures as `[ref x]`
    /// (spec 4.6.2), by name and declaring span (`ref_captured_bindings`):
    /// they live in a one-element `GcBuf` cell shared with the closures.
    ref_captured: std::collections::HashSet<(String, rokc_diagnostic::Span)>,
    /// Pattern bindings (`declare_bound`) still to be moved into their
    /// cells (`take_cells`) before the code in their scope runs.
    pending_cells: Vec<(String, LocalId, HirTy)>,
    /// Sub-sum type-pattern binders (`v: A | B` against `A | B | C`):
    /// `(binder, whole-scrutinee local)`, converted by `take_cells`.
    pending_resums: Vec<(LocalId, LocalId)>,
    /// In a closure: locals holding a value capture (assigning one is an
    /// error, spec 4.6.4).
    value_captured: std::collections::HashSet<LocalId>,
    /// Set by a path call (`Tr::m(x)` / `Tr::m(ref x)`) whose first
    /// argument fills `self`: whether it was passed with `ref`. Taken by
    /// the argument lowering of that call.
    explicit_recv: Option<bool>,
    /// Enclosing `unsafe fn` body / `unsafe { }` blocks (spec 4.15):
    /// unsafe calls are allowed when > 0.
    unsafe_depth: u32,
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
    /// Per scope: nested fns (spec 4.10) by name → lifted fn key.
    nested_fns: Vec<HashMap<String, String>>,
    /// Or-pattern shared binders. Each Or-pattern lowering pushes a map
    /// of `name → preset LocalId` so each alternative's `Binding` reuses
    /// the same local instead of allocating a fresh one. Spec 3.11.4 —
    /// `E::A(x) | E::B(x)` must bind `x` once, with consistent type.
    or_pattern_binders: Vec<HashMap<String, LocalId>>,
    /// `f::<T, 3>(..)` arguments for the generic call being lowered,
    /// read by `monomorphize_on` (empty otherwise).
    explicit_generics: HashMap<String, HirTy>,
    /// `x.m::<T>(..)`: the method call's explicit type arguments, taken
    /// by `method_call_on`.
    method_type_args: Vec<Ty>,
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
    /// Type parameter → its trait bounds and their supertraits (trait
    /// keys): `T::Item` resolves through them (`set_bounds`).
    ty_bounds: HashMap<String, Vec<String>>,
    /// Type parameter → its direct bounds as written (`T: TryFrom<S>`):
    /// `T::Error` takes the impl of `TryFrom<S>`, not every `TryFrom`
    /// impl of `T`.
    ty_bound_args: HashMap<String, Vec<AstPath>>,
    /// Lowering a coroutine body (`yield` / `await` are allowed).
    coro: Option<coro::CoroCtx>,
    /// Associated types of the enclosing trait / impl
    /// (`ASSOC_TYPES_ATTR`): a bare `X` is `Self::X` (spec 2.8.3).
    assoc_names: Vec<String>,
    /// Probing a block for the type an un-annotated `let` must have:
    /// the local, and the first concrete expected type it is read
    /// under (`expr::infer_from_later_use`).
    /// Lowering an un-annotated `let`'s initializer or the code after
    /// it for inference: an open type parameter becomes an inference
    /// variable instead of an error (`infer`).
    infer_vars: bool,
    /// Already lowered expressions an AST desugar refers to by a `#sN`
    /// path (`expr::splice`).
    splices: HashMap<String, HirExpr>,
    /// What is being lowered (the expression, statement or item): where
    /// diagnostics without a location of their own go.
    at: std::cell::Cell<Span>,
}

/// Where a speculative lowering started (`probe_mark`); `rollback`
/// undoes everything since.
struct ProbeMark {
    diagnostics: usize,
    uninferred: u32,
    next_id: u32,
    any_tags: usize,
    locals: usize,
}

impl<'a> LowerCtx<'a> {
    fn probe_mark(&self) -> ProbeMark {
        ProbeMark {
            diagnostics: self.env.sink.diagnostics.borrow().len(),
            uninferred: self.env.sink.uninferred.get(),
            next_id: self.env.sink.next_id.get(),
            any_tags: self.env.sink.any_tags.borrow().len(),
            locals: self.locals.len(),
        }
    }

    /// Whether nothing was reported since `mark`.
    fn probe_clean(&self, mark: &ProbeMark) -> bool {
        self.env.sink.diagnostics.borrow().len() == mark.diagnostics
    }

    /// Undo everything lowered since `mark` (the speculative lowering is
    /// discarded, or done again for real): this body's locals, the
    /// diagnostics (returned), and every function made since (closures,
    /// thunks and generic instances, with their cache entries — a probe
    /// may have made them over inference variables). Struct / enum
    /// instances stay (keyed by their arguments;
    /// `infer::drop_var_instances` empties the open ones).
    fn rollback(&mut self, mark: &ProbeMark) -> Vec<rokc_diagnostic::RokDiagnostic> {
        self.locals.truncate(mark.locals);
        let kept = |l: &LocalId| (l.0 as usize) < mark.locals;
        for scope in &mut self.scopes {
            scope.retain(|_, l| kept(l));
        }
        self.value_captured.retain(kept);
        self.narrowed.retain(|l, _| kept(l));
        let sink = &self.env.sink;
        let old = |id: &FunctionId| id.0 < mark.next_id;
        let dropped = sink.diagnostics.borrow_mut().split_off(mark.diagnostics);
        sink.uninferred.set(mark.uninferred);
        sink.extras.borrow_mut().retain(|f| old(&f.id));
        sink.mono_cache.borrow_mut().retain(|_, id| old(id));
        sink.mono_sigs.borrow_mut().retain(|id, _| old(id));
        sink.ref_out.borrow_mut().retain(|id, _| old(id));
        sink.inferred_fns
            .borrow_mut()
            .retain(|_, (start, _)| *start < mark.next_id);
        sink.thunks.borrow_mut().retain(|_, id| old(id));
        sink.any_dispatch.borrow_mut().retain(|d| old(&d.id));
        sink.any_tags.borrow_mut().truncate(mark.any_tags);
        let mut iw = sink.instance_warns.borrow_mut();
        for set in iw.instances.values_mut() {
            set.retain(old);
        }
        iw.warns.retain(|(_, _, by)| by.iter().any(old));
        dropped
    }

    /// A "type annotations needed" error (see `ClosureSink::uninferred`).
    fn emit_uninferred(&self, msg: String) {
        self.env
            .sink
            .uninferred
            .set(self.env.sink.uninferred.get() + 1);
        self.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!("type annotations needed: {msg}"),
        );
    }

    /// A context lowering at `at` (see `LowerCtx::at`).
    fn new(
        env: &'a Env<'a>,
        ty_subst: &'a HashMap<String, HirTy>,
        self_ty: Option<HirTy>,
        at: Span,
    ) -> Self {
        Self::with_subst(env, std::borrow::Cow::Borrowed(ty_subst), self_ty, at)
    }

    fn with_subst(
        env: &'a Env<'a>,
        ty_subst: std::borrow::Cow<'a, TySubst>,
        self_ty: Option<HirTy>,
        at: Span,
    ) -> Self {
        Self {
            env,
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            ty_subst,
            self_ty,
            fn_ret_ty: HirTy::Unit,
            infer_ret: false,
            ret_tys: None,
            implicit_main: false,
            harness_main: false,
            ref_params: Vec::new(),
            ref_captured: std::collections::HashSet::new(),
            pending_cells: Vec::new(),
            pending_resums: Vec::new(),
            value_captured: std::collections::HashSet::new(),
            unsafe_depth: 0,
            explicit_recv: None,
            breakables: Vec::new(),
            break_tys: HashMap::new(),
            expected_ty_stack: Vec::new(),
            current_module: String::new(),
            local_uses: vec![Vec::new()],
            nested_fns: vec![HashMap::new()],
            or_pattern_binders: Vec::new(),
            explicit_generics: HashMap::new(),
            method_type_args: Vec::new(),
            fn_throws: None,
            try_depth: 0,
            err_frames: Vec::new(),
            throws_probe: None,
            uncaught_in_main: false,
            throwing_calls: 0,
            next_synth: 0,
            narrowed: HashMap::new(),
            ty_bounds: HashMap::new(),
            ty_bound_args: HashMap::new(),
            coro: None,
            assoc_names: Vec::new(),
            infer_vars: false,
            splices: HashMap::new(),
            at: std::cell::Cell::new(at),
        }
    }

    /// The location being lowered.
    fn here(&self) -> Span {
        self.at.get()
    }

    /// Lower at `span`: `f`'s diagnostics without a location of their
    /// own go there.
    fn at_span<R>(&mut self, span: Span, f: impl FnOnce(&mut Self) -> R) -> R {
        let outer = self.at.replace(span);
        let r = f(self);
        self.at.set(outer);
        r
    }

    /// Push a lowering-time diagnostic onto the shared sink.
    fn emit_error(&self, kind: rokc_diagnostic::ErrorKind, msg: String) {
        self.emit_error_at(kind, self.here(), msg);
    }

    /// An error at `at`.
    fn emit_error_at(&self, kind: rokc_diagnostic::ErrorKind, at: Span, msg: String) {
        let mut d = rokc_diagnostic::RokDiagnostic::error(kind, at, msg);
        if let Some((callee, at)) = self.env.sink.call_sites.borrow().first() {
            d = d.with_secondary(*at, format!("in this call of `{}`", leaf_name(callee)));
        }
        self.env.sink.diagnostics.borrow_mut().push(d);
    }

    /// A warning. In a generic instance it is held until all lowering
    /// is done and reported only if every instance of the template
    /// raised it: a `rethrows` instance with a non-throwing argument
    /// would otherwise flag every `try` in its body.
    fn emit_warning(&self, msg: String) {
        let d = rokc_diagnostic::RokDiagnostic::warning(
            rokc_diagnostic::ErrorKind::Type,
            self.here(),
            msg,
        );
        if self.ty_subst.is_empty() {
            self.env.sink.diagnostics.borrow_mut().push(d);
            return;
        }
        let Some(Some((template, id))) = self.env.sink.instances.borrow().last().copied() else {
            return;
        };
        let mut iw = self.env.sink.instance_warns.borrow_mut();
        let same = |(t, w, _): &&mut (_, rokc_diagnostic::RokDiagnostic, _)| {
            *t == template && w.message == d.message && w.primary == d.primary
        };
        if let Some((_, _, by)) = iw.warns.iter_mut().find(same) {
            by.insert(id);
        } else {
            iw.warns.push((template, d, std::iter::once(id).collect()));
        }
    }

    /// Report a type error and return a poisoned placeholder (`Unknown`
    /// type). Checks skip `Unknown` operands, so one root cause yields
    /// one diagnostic.
    fn error_expr(&self, span: rokc_diagnostic::Span, msg: String) -> HirExpr {
        self.emit_error(rokc_diagnostic::ErrorKind::Type, msg);
        poison(span)
    }

    /// An unknown name (spec 9.9.4 `resolve`), with an optional hint.
    fn unknown_name(
        &self,
        span: rokc_diagnostic::Span,
        msg: String,
        help: Option<String>,
    ) -> HirExpr {
        self.emit_error(rokc_diagnostic::ErrorKind::Resolve, msg);
        self.help_last(help);
        poison(span)
    }

    /// Attach `help` to the diagnostic just emitted.
    fn help_last(&self, help: Option<String>) {
        if let (Some(h), Some(d)) = (help, self.env.sink.diagnostics.borrow_mut().last_mut()) {
            d.notes.push(format!("help: {h}"));
        }
    }

    /// "struct `S` has no field `x`" plus the closest field name.
    fn no_field(&self, sid: StructId, name: &str, span: rokc_diagnostic::Span) -> HirExpr {
        let def = self.struct_def(sid);
        let fields: Vec<&str> = def
            .fields
            .iter()
            .map(|f| f.name.as_str())
            .chain(
                def.union_kind
                    .iter()
                    .flat_map(|u| u.aliases.iter().map(|(n, _)| n.as_str())),
            )
            .filter(|n| !n.starts_with("__"))
            .collect();
        let kind = if def.union_kind.is_some() {
            "union"
        } else {
            "struct"
        };
        let e = self.error_expr(
            span,
            format!(
                "{kind} `{}` has no field `{name}`",
                self.ty_name(&HirTy::Struct(sid))
            ),
        );
        let help = rokc_diagnostic::suggest(name, fields.iter().copied())
            .map(|s| format!("did you mean `{s}`?"))
            .or_else(|| {
                (!fields.is_empty() && fields.len() <= 8).then(|| {
                    let list: Vec<String> = fields.iter().map(|f| format!("`{f}`")).collect();
                    format!("available fields: {}", list.join(", "))
                })
            });
        self.help_last(help);
        e
    }

    /// "did you mean" for an unknown method of `ty`.
    fn method_help(&self, ty: &HirTy, method: &str) -> Option<String> {
        let target = resolve::method_target_for(ty)?;
        let names = self
            .env
            .method_table
            .keys()
            .filter(|(t, _)| *t == target)
            .map(|(_, m)| m.as_str());
        rokc_diagnostic::suggest(method, names).map(|s| format!("did you mean `{s}`?"))
    }

    /// "did you mean" for an unknown type path: types of the current
    /// module and the primitives.
    fn type_help(&self, segs: &[&str]) -> Option<String> {
        let name = segs.last()?;
        let module = self.current_module.as_str();
        let defs = &self.env.defs;
        let (structs, enums) = (defs.struct_table.borrow(), defs.enum_table.borrow());
        let types = structs
            .keys()
            .chain(enums.keys())
            .chain(defs.generic_structs.keys())
            .chain(defs.generic_enums.keys())
            .filter_map(|k| {
                let (m, n) = k.rsplit_once("::").unwrap_or(("", k.as_str()));
                (m == module).then_some(n)
            })
            .chain(PRIM_NAMES.iter().copied());
        rokc_diagnostic::suggest(name, types).map(|s| format!("did you mean `{s}`?"))
    }

    /// "did you mean" for an unknown value path (one segment): locals in
    /// scope, then functions / constants / statics of the current module.
    fn value_help(&self, segs: &[&str]) -> Option<String> {
        let [name] = segs else {
            return None;
        };
        let name = *name;
        if let Some(k) = match name {
            "null" | "nil" | "None" | "NULL" => Some("none"),
            "True" => Some("true"),
            "False" => Some("false"),
            _ => None,
        } {
            return Some(format!("use `{k}`"));
        }
        let module = self.current_module.as_str();
        let in_module = |k: &'a String| {
            let (m, n) = k.rsplit_once("::").unwrap_or(("", k.as_str()));
            (m == module).then_some(n)
        };
        let locals = self
            .scopes
            .iter()
            .flat_map(|s| s.keys().map(String::as_str));
        let items = self
            .env
            .fn_table
            .keys()
            .chain(self.env.generic_fns.keys())
            .chain(self.env.consts.keys())
            .chain(self.env.statics.keys())
            .filter_map(in_module);
        rokc_diagnostic::suggest(name, locals.chain(items)).map(|s| format!("did you mean `{s}`?"))
    }

    /// User-facing type name (no internal `Struct0` / mangled names).
    fn ty_name(&self, ty: &HirTy) -> String {
        if let Some((v, p)) = ty.as_const() {
            return match u32::try_from(v).ok().and_then(char::from_u32) {
                Some(c) if p == Some(PrimTy::Char) => format!("{c:?}"),
                _ => v.to_string(),
            };
        }
        match ty {
            HirTy::GcBuf(t) => format!("GcBuf<{}>", self.ty_name(t)),
            HirTy::Never => "!".to_owned(),
            HirTy::Mlir(t) => format!("__mlir_type<{t:?}>"),
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
                if name == self.lang("int_type") {
                    return "int".to_owned();
                }
                if name == self.lang("float_type") {
                    return "float".to_owned();
                }
                // A library type by its name (`List<i32>`, not
                // `rok::core::collections::list::List<i32>`).
                let name = if name.starts_with("rok::") {
                    let base = name.split("__").next().unwrap_or(&name);
                    leaf_name(base).to_owned() + &name[base.len()..]
                } else {
                    name
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
            HirTy::AnyTrait(b) if b.len() == 1 => format!("any {}", self.trait_name(&b[0])),
            HirTy::AnyTrait(b) => {
                let b: Vec<String> = b.iter().map(|r| self.trait_name(r)).collect();
                format!("any ({})", b.join(" + "))
            }
            HirTy::Unknown => "{unknown}".to_owned(),
            HirTy::Var(_) => "_".to_owned(),
            HirTy::Path(p) => p.join("::"),
            HirTy::None => "none".to_owned(),
            HirTy::OpenConst(n) => format!("#{n}"),
            HirTy::NoThrow => "#nothrow".to_owned(),
            HirTy::Const(v, _) => v.to_string(),
            HirTy::Tuple(parts) => {
                let inner: Vec<String> = parts.iter().map(|t| self.ty_name(t)).collect();
                format!("({})", inner.join(", "))
            }
            HirTy::Sum(_) => ty.sum_name(|t| self.ty_name(t)),
            HirTy::Array(e, n) => format!("[{}; {n}]", self.ty_name(e)),
            HirTy::Fn(args, ret, _) | HirTy::Closure { args, ret, .. } => {
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
                let (bounds, kw): (String, &str) = match ty {
                    HirTy::Fn(_, _, b) => (
                        b.auto.iter().flat_map(|k| [" + ", leaf_name(k)]).collect(),
                        match (b.unsafe_fn, b.c_abi) {
                            (true, true) => "unsafe extern \"C\" fn",
                            (true, false) => "unsafe fn",
                            (false, true) => "extern \"C\" fn",
                            (false, false) => kw,
                        },
                    ),
                    _ => (String::new(), kw),
                };
                format!("{kw}({}) {ret}{bounds}", inner.join(", "))
            }
            HirTy::Throws { ok, err } => {
                format!("throws ({}) -> {}", self.ty_name(err), self.ty_name(ok))
            }
        }
    }

    /// `Path<A, Name = B>` for diagnostics.
    fn trait_name(&self, r: &TraitRef) -> String {
        r.render(&r.path, |t| self.ty_name(t))
    }

    /// The item bound to lang slot `slot` (spec 6.4), `""` if unbound.
    fn lang(&self, slot: &str) -> &'a str {
        self.env.names.lang_item(slot)
    }

    /// The trait refs of `ty`'s concrete impls.
    fn concrete_impls(&self, ty: &HirTy) -> impl Iterator<Item = &'a TraitRef> + use<'a> {
        let env: &'a Env<'a> = self.env;
        env.impls.refs_on(ty)
    }

    /// Does `ty` implement trait `path` (whatever its arguments)?
    fn has_trait(&self, ty: &HirTy, path: &str) -> bool {
        self.implements_trait(ty, &TraitRef::plain(path), 0)
    }

    /// Does `ty` meet bound `want`: an impl of it covers `ty`
    /// (`has_impl`), or a structural rule gives it (auto traits, a
    /// sum's members, an `any` value's bound, `Reflect`).
    fn implements_trait(&self, ty: &HirTy, want: &TraitRef, depth: u32) -> bool {
        let trait_key = want.path.as_str();
        if trait_key == reflect::REFLECT {
            return true;
        }
        if self.env.names.auto_traits.contains(trait_key) {
            return self.auto_trait(ty, trait_key, depth, &mut Vec::new());
        }
        // A sum has the structural traits its variants have (`none`
        // has them all); `expr::sum_structural_call` dispatches them.
        match ty {
            HirTy::Sum(vs) if want.is_plain() => {
                // `T | none` defaults to `none`.
                if trait_key == DEFAULT_TRAIT {
                    return vs.iter().any(HirTy::is_none);
                }
                if expr::is_sum_trait(self, trait_key) {
                    return vs
                        .iter()
                        .all(|v| v.is_none() || self.implements_trait(v, want, depth + 1));
                }
            }
            // An `any` value formats through its bound (`expr::any_fmt`).
            HirTy::AnyTrait(b)
                if want.is_plain()
                    && (trait_key == self.lang("display_trait")
                        || trait_key == self.lang("debug_trait")) =>
            {
                return bound_covers(self, b, want);
            }
            _ => {}
        }
        self.has_impl(ty, want, depth)
    }

    /// Structural auto trait (`Send` / `Sync`). An `unsafe impl`
    /// opts in, `impl !Tr` opts out; otherwise every component must
    /// have it. Primitives and `str` do. A recursive type assumes it
    /// for itself (`seen`).
    fn auto_trait(&self, ty: &HirTy, key: &str, depth: u32, seen: &mut Vec<HirTy>) -> bool {
        if self.has_impl(ty, &TraitRef::plain(key), depth) {
            return true;
        }
        let base = match ty {
            HirTy::Struct(id) => Some(self.struct_def(*id).name),
            HirTy::Enum(id) => Some(self.enum_def(*id).name),
            _ => None,
        };
        if let Some(b) = base {
            let b = b.split("__").next().unwrap_or(&b).to_owned();
            if self.env.neg_auto.contains(&(b, key.to_owned())) {
                return false;
            }
        }
        if seen.contains(ty) {
            return true;
        }
        seen.push(ty.clone());
        let mut rec = |t: &HirTy| self.auto_trait(t, key, depth, seen);
        let ok = match ty {
            HirTy::Tuple(ts) | HirTy::Sum(ts) => ts.iter().all(&mut rec),
            HirTy::Array(e, _) | HirTy::GcBuf(e) => rec(e),
            // A capture is a copy of a handle the creating thread keeps
            // using, so a closure that crosses threads shares every
            // capture: each must be `Sync` too (a `[ref x]` cell is a
            // `GcBuf<X>`, so `X: Sync` — spec 4.6.9).
            HirTy::Closure { env, .. } => {
                let sync = self.lang("sync_trait");
                rec(env) && (key == sync || self.auto_trait(env, sync, depth, &mut Vec::new()))
            }
            HirTy::Throws { ok, err } => rec(ok) && rec(err),
            HirTy::Struct(id) => {
                let def = self.struct_def(*id);
                // A union has what every declared field has (its storage
                // is plain bytes).
                match &def.union_kind {
                    Some(u) => u.aliases.iter().all(|(_, t)| rec(t)),
                    None => def.fields.iter().all(|f| rec(&f.ty)),
                }
            }
            HirTy::Enum(id) => self
                .enum_def(*id)
                .variants
                .iter()
                .all(|v| v.payload_ty.as_ref().is_none_or(&mut rec)),
            // A `+ Send` closure's captures are all `Sync` (above), so a
            // `+ Send` value is also `Sync`.
            HirTy::Fn(_, _, b) => b.auto.iter().any(|k| {
                k == key || (key == self.lang("sync_trait") && *k == self.lang("send_trait"))
            }),
            HirTy::AnyTrait(b) => bound_covers(self, b, &TraitRef::plain(key)),
            // Unresolved paths (`none`, type-param leftovers) and error
            // types count as having it: no cascade errors.
            HirTy::Prim(_)
            | HirTy::Unit
            | HirTy::Never
            | HirTy::Mlir(_)
            | HirTy::Any
            | HirTy::Unknown
            | HirTy::Path(_)
            | HirTy::None
            | HirTy::Const(..)
            | HirTy::OpenConst(_)
            | HirTy::NoThrow
            | HirTy::Var(_) => true,
        };
        seen.pop();
        ok
    }

    /// Why `ty` lacks auto trait `key` (`auto_trait` is false): the
    /// path to the component that opts out, as text to follow "`T` is
    /// not `Sync`", e.g. " because field `accounts` has type
    /// `List<i64>` (collections are not `Sync`; ..)".
    fn auto_trait_cause(&self, ty: &HirTy, key: &str, depth: u32) -> String {
        let tr = leaf_name(key);
        let lacks = |t: &HirTy| !self.auto_trait(t, key, 0, &mut Vec::new());
        let step = |what: String, t: &HirTy| {
            format!(
                " because {what} has type `{}`{}",
                self.ty_name(t),
                self.auto_trait_cause(t, key, depth + 1)
            )
        };
        if depth > 8 {
            return String::new();
        }
        match ty {
            HirTy::Struct(id) => {
                let def = self.struct_def(*id);
                let base = def.name.split("__").next().unwrap_or(&def.name);
                if base.starts_with("rok::core::collections::") {
                    return format!(
                        " (collections are not `{tr}`; share one through a `Mutex`, or use an \
                         array)"
                    );
                }
                if self
                    .env
                    .neg_auto
                    .contains(&(base.to_owned(), key.to_owned()))
                {
                    return String::new();
                }
                def.fields
                    .iter()
                    .find(|f| lacks(&f.ty))
                    .map(|f| step(format!("field `{}`", f.name), &f.ty))
                    .unwrap_or_default()
            }
            HirTy::Enum(id) => self
                .enum_def(*id)
                .variants
                .iter()
                .find_map(|v| {
                    let t = v.payload_ty.as_ref().filter(|t| lacks(t))?;
                    Some(step(format!("variant `{}`", v.name), t))
                })
                .unwrap_or_default(),
            HirTy::Tuple(ts) | HirTy::Sum(ts) => ts
                .iter()
                .find(|t| lacks(t))
                .map(|t| step("a member".to_owned(), t))
                .unwrap_or_default(),
            HirTy::Array(e, _) | HirTy::GcBuf(e) => step("an element".to_owned(), e),
            _ => String::new(),
        }
    }

    /// For a closure that does not fit a `fn .. + Send` slot: which
    /// capture is not `Send` / `Sync`, and why.
    fn closure_bound_note(&self, value: &HirExpr) -> Option<String> {
        let HirExprKind::ClosureValue { env, .. } = &value.kind else {
            return None;
        };
        let HirExprKind::Tuple { fields } = &env.kind else {
            return None;
        };
        let keys = [self.lang("send_trait"), self.lang("sync_trait")];
        fields.iter().find_map(|f| {
            let local = match &f.kind {
                HirExprKind::Local(l) => *l,
                HirExprKind::BufGet { buf, .. } => match buf.kind {
                    HirExprKind::Local(l) => l,
                    _ => return None,
                },
                _ => return None,
            };
            let key = keys
                .iter()
                .find(|k| !self.auto_trait(&f.ty, k, 0, &mut Vec::new()))?;
            let name = self.locals.get(local.0 as usize)?.name.clone()?;
            // A `[ref x]` capture is a cell of `x`'s type.
            let shown = match &f.ty {
                HirTy::GcBuf(t) => t,
                t => t,
            };
            Some(format!(
                "the closure captures `{name}` (type `{}`), which is not `{}`{}",
                self.ty_name(shown),
                leaf_name(key),
                self.auto_trait_cause(shown, key, 0)
            ))
        })
    }

    /// Does an impl give `ty` trait `want` (spec 2.9): a concrete impl
    /// whose trait ref satisfies it, or a generic impl covering `ty`
    /// (`generic_impls`) whose instantiated ref does? Impl questions —
    /// bounds, operator and method dispatch, projections — go through
    /// here, `concrete_impls` and `generic_impls`.
    fn has_impl(&self, ty: &HirTy, want: &TraitRef, depth: u32) -> bool {
        self.concrete_impls(ty).any(|r| r.satisfies(want))
            || self
                .generic_impls(ty, |gi| gi.trait_key == want.path, depth)
                .any(|(gi, subst)| {
                    want.is_plain() || self.generic_impl_ref(gi, &subst).satisfies(want)
                })
    }

    /// The generic impls `keep` picks (a trait's; `trait_key` is `""` for
    /// a generic inherent impl) that cover `ty`, with their parameter
    /// bindings.
    fn generic_impls<'s>(
        &'s self,
        ty: &'s HirTy,
        keep: impl Fn(&Impl) -> bool + 's,
        depth: u32,
    ) -> impl Iterator<Item = (&'a Impl, TySubst)> + 's {
        let env: &'a Env<'a> = self.env;
        env.impls
            .generic()
            .filter(move |gi| keep(gi))
            .filter_map(move |gi| Some((gi, self.generic_impl_subst(gi, ty, depth)?)))
    }

    /// The trait ref generic impl `gi` provides under `subst`: its trait
    /// arguments and associated types instantiated.
    fn generic_impl_ref(&self, gi: &Impl, subst: &TySubst) -> TraitRef {
        let mut rcx = LowerCtx::new(self.env, subst, None, self.here());
        rcx.current_module.clone_from(&gi.module);
        rcx.set_bounds(&gi.generics, &gi.where_clause);
        TraitRef::new(
            gi.trait_key.clone(),
            gi.trait_args
                .iter()
                .map(|t| rcx.resolve_ast_ty(t))
                .collect(),
            gi.assoc
                .iter()
                .map(|(n, t)| (n.clone(), rcx.resolve_ast_ty(t)))
                .collect(),
        )
    }

    /// Bound `b` (an AST trait path) as written in `module`, its type
    /// arguments resolved by `rec`.
    fn bound_ref(&self, b: &Ty, module: &str, rec: impl FnMut(&Ty) -> HirTy) -> Option<TraitRef> {
        let AstTyKind::Path(p) = &b.kind else {
            return None;
        };
        Some(resolve::trait_ref(
            &self.env.names,
            p,
            module,
            self.here(),
            rec,
        ))
    }

    /// The impl's type-parameter bindings when generic impl `gi` covers
    /// `ty`: `ty` matches its target and meets its bounds.
    fn generic_impl_subst(
        &self,
        gi: &Impl,
        ty: &HirTy,
        depth: u32,
    ) -> Option<HashMap<String, HirTy>> {
        self.generic_impl_match(gi, ty, depth).ok()
    }

    /// `generic_impl_subst`, but on failure says why: `Err(Some((T, B)))`
    /// when `gi`'s target matches `ty` but the bound `T: B` fails,
    /// `Err(None)` when the target does not match.
    fn generic_impl_match(
        &self,
        gi: &Impl,
        ty: &HirTy,
        depth: u32,
    ) -> Result<HashMap<String, HirTy>, Option<(HirTy, TraitRef)>> {
        // Depth cap instead of cycle detection (`impl<T: Tr> Tr for T`).
        if depth > 8 || matches!(ty, HirTy::Unknown) {
            return Err(None);
        }
        let params: std::collections::HashSet<String> = gi
            .generics
            .params
            .iter()
            .map(|gp| match gp {
                rokc_ast::GenericParam::Type { name, .. }
                | rokc_ast::GenericParam::Const { name, .. } => name.clone(),
            })
            .collect();
        let mut subst = HashMap::new();
        unify_param_ty_with(&gi.self_ty, ty, &params, &mut subst, self);
        // A parameter only the trait arguments name (`impl<A, B, C>
        // Compose<fn(A) -> B> for fn(B) -> C`) is left to the call's
        // arguments.
        let shown = collect::impl_def_display(&gi.self_ty);
        let mut in_self = shown
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .filter(|w| params.contains(*w));
        if in_self.any(|p| !subst.contains_key(p)) {
            return Err(None);
        }
        // `impl<T, const N: usize> Tr for [T; N]`: `N` takes its type.
        for gp in &gi.generics.params {
            if let rokc_ast::GenericParam::Const { name, ty: cty } = gp {
                let prim = match crate::ty::resolve_ty(cty) {
                    HirTy::Prim(p) => Some(p),
                    _ => None,
                };
                if let Some((v, _)) = subst.get(name).and_then(HirTy::as_const) {
                    subst.insert(name.clone(), HirTy::Const(v, prim));
                }
            }
        }
        let mut rcx = LowerCtx::new(self.env, &subst, None, self.here());
        rcx.current_module.clone_from(&gi.module);
        rcx.set_bounds(&gi.generics, &gi.where_clause);
        // Another generic struct's arguments (`List<i32>` against
        // `Rev<I>`): resolving `Rev<i32>` would instantiate a bogus
        // struct (whose `I::Item` field cannot resolve).
        if let (AstTyKind::Path(p), HirTy::Struct(_) | HirTy::Enum(_)) = (&gi.self_ty.kind, ty) {
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            let name = match ty {
                HirTy::Struct(id) => self.struct_def(*id).name,
                HirTy::Enum(id) => self.enum_def(*id).name,
                _ => unreachable!("matched struct / enum"),
            };
            if p.segments.last().is_some_and(|s| !s.generics.is_empty())
                && rcx.canon_type(&segs).as_deref() != Some(enum_base_name(&name))
            {
                return Err(None);
            }
        }
        if rcx.resolve_ast_ty(&gi.self_ty) != *ty {
            return Err(None);
        }
        let mut goals: Vec<(HirTy, &Vec<Ty>)> = Vec::new();
        for gp in &gi.generics.params {
            if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
                if let Some(t) = subst.get(name) {
                    goals.push((t.clone(), bounds));
                }
            }
        }
        for w in &gi.where_clause {
            goals.push((rcx.resolve_ast_ty(&w.ty), &w.bounds));
        }
        for (bty, bounds) in goals {
            for b in bounds {
                let Some(want) = self.bound_ref(b, &gi.module, |t| rcx.resolve_ast_ty(t)) else {
                    continue;
                };
                if !self.implements_trait(&bty, &want, depth + 1) {
                    return Err(Some((bty, want)));
                }
            }
        }
        Ok(subst)
    }

    /// `any` type tag of concrete type `ty`: a hash of its type name, so
    /// a prebuilt dependency (separately compiled) tags its values alike.
    // 31-bit hash: a collision within one build probes to the next free
    // tag, which is then build-local.
    fn any_tag(&self, ty: &HirTy) -> u32 {
        let mut tags = self.env.sink.any_tags.borrow_mut();
        if let Some((_, tag)) = tags.iter().find(|(t, _)| t == ty) {
            return *tag;
        }
        let mut tag = self.ty_name(ty).bytes().fold(0x811c_9dc5_u32, |h, b| {
            (h ^ u32::from(b)).wrapping_mul(0x0100_0193)
        }) & 0x7fff_ffff;
        while tags.iter().any(|(_, t)| *t == tag) {
            tag = (tag + 1) & 0x7fff_ffff;
        }
        tags.push((ty.clone(), tag));
        tag
    }

    fn struct_def(&self, id: StructId) -> HirStructDef {
        self.env.defs.structs.borrow()[id.0 as usize].clone()
    }

    /// Struct id by table key (a declared struct or an instance).
    fn lookup_struct(&self, key: &str) -> Option<StructId> {
        self.env.defs.struct_id(key)
    }

    /// Instance `base<args>` of a generic struct, its fields resolved
    /// here (projections included); a new one points its bound errors at
    /// `span`.
    fn instantiate_struct(
        &self,
        base: &str,
        args: Vec<HirTy>,
        span: rokc_diagnostic::Span,
    ) -> Option<StructId> {
        let mut args = args;
        if let Some(def) = self.env.defs.generic_structs.get(base) {
            mono::fill_defaults(&def.generics, &mut args, |subst, t| {
                let mut rcx = LowerCtx::new(self.env, subst, None, self.here());
                rcx.current_module = module_of(base);
                rcx.resolve_ast_ty(t)
            });
            self.check_const_args(&def.generics, &args)?;
        }
        self.env
            .defs
            .instantiate_struct(base, args, span, |def, subst| {
                let mut rcx = LowerCtx::new(self.env, subst, None, self.here());
                rcx.current_module = module_of(base);
                generic_struct_fields(def, &|t| rcx.resolve_ast_ty(t))
            })
    }

    fn enum_def(&self, id: EnumId) -> HirEnumDef {
        self.env.defs.enums.borrow()[id.0 as usize].clone()
    }

    /// Enum id by table key (a declared enum or an instance).
    fn lookup_enum(&self, key: &str) -> Option<EnumId> {
        self.env.defs.enum_id(key)
    }

    /// The instances of generic enum `base` made so far.
    fn enum_instantiations(&self, base: &str) -> Vec<EnumId> {
        Self::instantiations(&self.env.defs.enum_table.borrow(), base)
    }

    /// `instantiate_struct` for a generic enum.
    fn instantiate_enum(
        &self,
        base: &str,
        args: Vec<HirTy>,
        span: rokc_diagnostic::Span,
    ) -> Option<EnumId> {
        let mut args = args;
        if let Some(def) = self.env.defs.generic_enums.get(base) {
            mono::fill_defaults(&def.generics, &mut args, |subst, t| {
                let mut rcx = LowerCtx::new(self.env, subst, None, self.here());
                rcx.current_module = module_of(base);
                rcx.resolve_ast_ty(t)
            });
            self.check_const_args(&def.generics, &args)?;
        }
        self.env
            .defs
            .instantiate_enum(base, args, span, |def, subst| {
                let mut rcx = LowerCtx::new(self.env, subst, None, self.here());
                rcx.current_module = module_of(base);
                generic_enum_variants(def, &|t| rcx.resolve_ast_ty(t))
            })
    }

    /// A `char` const parameter takes a `char` argument, any other an
    /// integer or `bool` (spec 2.11.3).
    fn check_const_args(&self, generics: &rokc_ast::Generics, args: &[HirTy]) -> Option<()> {
        for (gp, arg) in generics.params.iter().zip(args) {
            if let (rokc_ast::GenericParam::Const { name, ty }, Some(v)) = (gp, arg.as_const()) {
                mono::typed_const(self, name, ty, v)?;
            }
        }
        Some(())
    }

    fn scope(&self) -> Scope<'_> {
        Scope {
            names: &self.env.names,
            module: &self.current_module,
            at: self.here(),
        }
    }

    /// Canonical type-namespace name for a path (struct / enum / alias /
    /// trait, generic bases included), resolved from this function's
    /// module and `use`s.
    fn canon_type(&self, segments: &[&str]) -> Option<String> {
        self.env.names.canon(
            segments,
            &self.current_module,
            &self.local_uses,
            self.here(),
        )
    }

    /// Split `a::E::V` into (`a::E` enum, `V`) when the prefix names an
    /// enum (or generic enum base).
    /// A single segment is an imported variant (`use E::{A}`, `use
    /// E::*`, or `Ok` / `Err` through the implicit `rok::core::**`).
    fn enum_path(&self, segments: &[&str]) -> Option<(String, String)> {
        let (variant, ty) = segments.split_last()?;
        if ty.is_empty() {
            let key = self.env.names.canon_variant(
                segments,
                &self.current_module,
                &self.local_uses,
                self.here(),
            )?;
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
    /// `index` caches `table`'s keys by last segment (rebuilt when the
    /// table grows; keys are never removed).
    fn resolve_in<T>(
        &self,
        segments: &[&str],
        table: &HashMap<String, T>,
        index: &std::cell::RefCell<(usize, Leaves)>,
    ) -> Option<String> {
        let exists = |k: &str| table.contains_key(k);
        let keys = |leaf: &str| {
            let mut index = index.borrow_mut();
            if index.0 != table.len() {
                *index = (table.len(), leaves(table.keys()));
            }
            index.1.get(leaf).cloned().unwrap_or_default()
        };
        let visible = |k: &str| {
            let vis = self.env.item_visibility.get(k).copied();
            vis.is_none_or(|v| self.is_visible(&module_of(k), v))
        };
        let set = NameSet {
            exists: &exists,
            keys: &keys,
            visible: &visible,
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

    /// Resolve a function path in the one value namespace that holds
    /// both concrete (`fn_table`) and generic (`generic_fns`) functions,
    /// so the nearest declaration wins whichever kind it is (spec 5.7:
    /// the module's own items, then its `use`s, then `rok::core::**`).
    fn resolve_any_fn(&self, segments: &[&str]) -> Option<String> {
        let (fns, gens) = (&self.env.fn_table, &self.env.generic_fns);
        if let [name] = segments {
            if let Some(k) = self.nested_fns.iter().rev().find_map(|m| m.get(*name)) {
                return Some(k.clone());
            }
        }
        let exists = |k: &str| fns.contains_key(k) || gens.contains_key(k);
        let keys = |leaf: &str| {
            self.env
                .fn_leaves
                .get_or_init(|| leaves(fns.keys().chain(gens.keys())))
                .get(leaf)
                .cloned()
                .unwrap_or_default()
        };
        let visible = |k: &str| {
            let vis = self.env.item_visibility.get(k).copied();
            vis.is_none_or(|v| self.is_visible(&module_of(k), v))
        };
        let set = NameSet {
            exists: &exists,
            keys: &keys,
            visible: &visible,
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
    /// qualified fn-table key (a concrete fn), or an `extern "C"` one.
    fn resolve_fn_name(&self, segments: &[&str]) -> Option<String> {
        match self.resolve_any_fn(segments) {
            Some(f) => self.env.fn_table.contains_key(&f).then_some(f),
            None => match segments {
                [name] if self.env.extern_fns.contains(*name) => Some((*name).to_owned()),
                _ => None,
            },
        }
    }

    /// `resolve_fn_name` for a generic fn (a `generic_fns` key).
    fn resolve_generic_fn_name(&self, segments: &[&str]) -> Option<String> {
        self.resolve_any_fn(segments)
            .filter(|f| self.env.generic_fns.contains_key(f))
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
        if self.harness_main {
            return true;
        }
        let vis = self
            .env
            .item_visibility
            .get(full)
            .copied()
            .unwrap_or(Visibility::Pub);
        let def_module = module_of(full);
        if let Some(m) = resolve::hidden_module(&self.env.names.mod_vis, &self.current_module, full)
        {
            self.emit_error(
                rokc_diagnostic::ErrorKind::Module,
                resolve::hidden_module_msg(full, &m, &self.current_module),
            );
            return false;
        }
        if self.is_visible(&def_module, vis) {
            return true;
        }
        if vis == Visibility::Pkg {
            self.emit_error(
                rokc_diagnostic::ErrorKind::Module,
                format!(
                    "{what} `{full}` is `pub(pkg)`: visible only inside its package \
                     `{}` (spec 5.6.4)",
                    module_display(&package_of(&def_module))
                ),
            );
            return false;
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
            substitute_params(&mut t, &HashMap::from([("Self".to_owned(), st.clone())]));
        }
        t
    }

    /// Spec 2.11.4 / 2.11.5: a compile-time integer — a literal, a
    /// const generic parameter of this instantiation, or any const
    /// expression (`const` items, `const fn` calls) evaluated by
    /// `const_eval`.
    fn eval_const(&self, c: &rokc_ast::ConstExpr) -> Option<i128> {
        self.eval_const_msg(c).ok()
    }

    fn eval_const_msg(&self, c: &rokc_ast::ConstExpr) -> Result<i128, String> {
        self.eval_const_arg(c).map(|(v, _)| v)
    }

    /// A const argument's value, tagged `char` when it is one (a `char`
    /// const parameter takes only a `char`, spec 2.11.3).
    fn eval_const_arg(&self, c: &rokc_ast::ConstExpr) -> Result<(i128, Option<PrimTy>), String> {
        let not_int = || "not an integer".to_owned();
        let e = match c {
            rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Char(s)) => {
                return expr::parse_char_literal(s)
                    .map(|v| (i128::from(v), Some(PrimTy::Char)))
                    .ok_or_else(not_int);
            }
            rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Int(s)) => {
                return expr::parse_int_literal(s)
                    .map(|(v, _)| (v, None))
                    .ok_or_else(not_int);
            }
            rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Bool(b)) => {
                return Ok((i128::from(*b), None));
            }
            rokc_ast::ConstExpr::Literal(_) => return Err(not_int()),
            rokc_ast::ConstExpr::Path(p) => {
                if let [seg] = p.segments.as_slice() {
                    if let Some((v, p)) = self.ty_subst.get(&seg.name).and_then(HirTy::as_const) {
                        return Ok((v, p.filter(|p| *p == PrimTy::Char)));
                    }
                }
                Expr {
                    kind: ExprKind::Path(p.clone()),
                    span: p.span,
                }
            }
            rokc_ast::ConstExpr::Expr(e) => (**e).clone(),
        };
        const_eval::eval_scalar(self, &e)
    }

    fn resolve_ty_inner(&self, ty: &rokc_ast::Ty) -> HirTy {
        let rec = |t: &rokc_ast::Ty| self.resolve_ty_inner(t);
        match &ty.kind {
            // `Self` inside generic arguments (`Map<Self, ..>`) must be
            // concrete before the instantiation check.
            AstTyKind::SelfUpper if self.self_ty.is_some() => {
                self.self_ty.clone().unwrap_or(HirTy::Unknown)
            }
            AstTyKind::Path(_)
                if self
                    .env
                    .names
                    .expand_alias(ty, &self.current_module, self.here())
                    .is_some() =>
            {
                let t = self
                    .env
                    .names
                    .expand_alias(ty, &self.current_module, self.here());
                t.map_or(HirTy::Unknown, |t| rec(&t))
            }
            AstTyKind::Path(p) => {
                // Depth-capped: a cyclic alias is reported by the alias pass.
                let param =
                    matches!(p.segments.as_slice(), [s] if self.ty_subst.contains_key(&s.name));
                let names = &self.env.names;
                let alias = (!param && names.alias_depth.get() < 32)
                    .then(|| names.plain_alias(ty, &self.current_module, self.here()))
                    .flatten();
                if let Some(full) = alias {
                    // Reported at the alias.
                    if names.broken_aliases.borrow().contains(&full) {
                        return HirTy::Unknown;
                    }
                    if let Some(t) =
                        names.projection_alias(&full, &self.current_module, self.here())
                    {
                        let depth = &names.alias_depth;
                        depth.set(depth.get() + 1);
                        let r = rec(&t);
                        depth.set(depth.get() - 1);
                        return r;
                    }
                }
                if let [seg] = p.segments.as_slice() {
                    if seg.generics.is_empty() {
                        if let Some(t) = self.ty_subst.get(&seg.name) {
                            return t.clone();
                        }
                        // `X` in a trait / impl body is `Self::X`.
                        if self.self_ty.is_some() && self.assoc_names.contains(&seg.name) {
                            let mut sp = p.clone();
                            sp.segments.insert(
                                0,
                                rokc_ast::PathSegment {
                                    name: "Self".to_owned(),
                                    generics: Vec::new(),
                                },
                            );
                            if let Some(t) = self.projection(&sp) {
                                return t;
                            }
                        }
                        // A `const` item as a const generic argument
                        // (`Grid<W, 3>`, spec 2.11.4).
                        if self.canon_type(&[seg.name.as_str()]).is_none()
                            && self
                                .resolve_in(
                                    &[seg.name.as_str()],
                                    &self.env.consts,
                                    &self.env.const_leaves,
                                )
                                .is_some()
                        {
                            if let Ok((v, t)) =
                                self.eval_const_arg(&rokc_ast::ConstExpr::Path(p.clone()))
                            {
                                return HirTy::Const(v, t);
                            }
                        }
                    }
                }
                if let Some(t) = self.projection(p) {
                    return t;
                }
                let generics = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
                let bare = generics.is_empty()
                    && p.segments
                        .last()
                        .is_some_and(|s| self.env.defs.defaulted_leaves.contains(&s.name));
                if !generics.is_empty() || bare {
                    let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                    if let Some(full) = self
                        .canon_type(&segs)
                        .filter(|f| !bare || self.env.defs.bare_instance(f))
                    {
                        if let (GC_BUF, [elem]) = (full.as_str(), generics) {
                            return HirTy::GcBuf(Box::new(rec(elem)));
                        }
                        if let Some(t) = resolve::mlir_ty(&full, generics) {
                            return t;
                        }
                        let args: Vec<HirTy> = generics.iter().map(rec).collect();
                        // A new instance's bound errors point at this type.
                        let at = Some(ty.span)
                            .filter(|s| !s.is_dummy())
                            .unwrap_or_else(|| self.here());
                        let mut leftover = Vec::new();
                        args.iter()
                            .for_each(|a| collect_unknown_paths(a, &mut leftover));
                        // An inference variable is an argument like any type.
                        leftover.retain(|p| p != "_");
                        if leftover.is_empty() && self.env.defs.generic_structs.contains_key(&full)
                        {
                            if let Some(id) = self.instantiate_struct(&full, args, at) {
                                return HirTy::Struct(id);
                            }
                        } else if leftover.is_empty() {
                            if let Some(id) = self.instantiate_enum(&full, args, at) {
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
                let mut t = resolve_ty_with_structs(ty, &self.env.defs, None, self.scope());
                substitute_params(&mut t, &self.ty_subst);
                t
            }
            AstTyKind::Sum(parts) => crate::ty::written_sum(
                parts,
                |n| self.ty_subst.contains_key(n) || self.assoc_names.iter().any(|a| a == n),
                rec,
            ),
            AstTyKind::Nest(x) => rec(x),
            AstTyKind::Tuple(parts) if parts.is_empty() => HirTy::Unit,
            AstTyKind::Tuple(parts) => HirTy::Tuple(parts.iter().map(rec).collect()),
            AstTyKind::Array(elem, len) => {
                if let rokc_ast::ConstExpr::Literal(_) = len {
                    return match resolve_ty_with_structs(ty, &self.env.defs, None, self.scope()) {
                        HirTy::Array(_, n) => HirTy::Array(Box::new(rec(elem)), n),
                        other => other,
                    };
                }
                // Spec 2.11.5: `[T; N]`, `[T; M * N]`.
                let n = self.eval_const_msg(len).and_then(|v| {
                    u32::try_from(v).map_err(|_| format!("length {v} is out of range"))
                });
                match n {
                    Ok(n) => HirTy::Array(Box::new(rec(elem)), n),
                    // A const parameter not bound yet (argument hints
                    // before inference): no type yet, not an error.
                    Err(_)
                        if self
                            .ty_subst
                            .values()
                            .any(|t| matches!(t, HirTy::OpenConst(_))) =>
                    {
                        HirTy::Unknown
                    }
                    Err(why) => {
                        self.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "array length must be a compile-time integer (spec 2.11.5): \
                                 {why}"
                            ),
                        );
                        HirTy::Unknown
                    }
                }
            }
            AstTyKind::Const(c) => match self.eval_const_arg(c) {
                Ok((v, p)) => HirTy::Const(v, p),
                Err(why) => {
                    self.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "a const generic argument must be a compile-time integer, \
                                 `bool` or `char` (spec 2.11.4): {why}"
                        ),
                    );
                    HirTy::Unknown
                }
            },
            AstTyKind::Fn(args, ret, b) => HirTy::Fn(
                args.iter().map(rec).collect(),
                Box::new(rec(ret)),
                self.env
                    .names
                    .fn_bounds(b, &self.current_module, self.here()),
            ),
            AstTyKind::Throws { ok, err } => crate::ty::throws_ty(rec(ok), rec(err)),
            AstTyKind::QPath(q) => self.qpath_ty(q),
            _ => resolve_ty_with_structs(ty, &self.env.defs, None, self.scope()),
        }
    }

    /// `<T as Tr>::X` (spec 2.13.4): only `Tr`'s `X`.
    fn qpath_ty(&self, q: &rokc_ast::QPath) -> HirTy {
        let base = self.resolve_ty_inner(&q.self_ty);
        let tp = &q.trait_path;
        let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
        let key = self
            .env
            .names
            .trait_key(&segs, &self.current_module, self.here());
        if !self.env.names.traits.contains(&key) {
            self.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`{}` in `<.. as {}>` is not a trait",
                    segs.join("::"),
                    segs.join("::")
                ),
            );
            return HirTy::Unknown;
        }
        let want = resolve::trait_ref(
            &self.env.names,
            tp,
            &self.current_module,
            self.here(),
            |t| self.resolve_ty_inner(t),
        );
        self.project_or_report(&base, &q.item, Some(&[key]), &[want], true)
    }

    /// `T::Item` / `List<i32>::IntoIter` (spec 2.1, 2.13): an associated
    /// type of the type the prefix names, resolved once that type is
    /// concrete. `None`: not a projection (a module path such as `a::P`).
    /// A prefix still naming an unbound type parameter stays an opaque
    /// path (`J::Item`).
    fn projection(&self, p: &AstPath) -> Option<HirTy> {
        let (last, prefix) = p.segments.split_last()?;
        if prefix.is_empty() || !last.generics.is_empty() {
            return None;
        }
        let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
        if self.canon_type(&segs).is_some() {
            return None;
        }
        let pre: Vec<&str> = prefix.iter().map(|s| s.name.as_str()).collect();
        let base = match pre.as_slice() {
            ["Self"] => self.self_ty.clone()?,
            [n] if self.ty_subst.contains_key(*n) && prefix[0].generics.is_empty() => {
                self.ty_subst[*n].clone()
            }
            _ => {
                let ty = Ty {
                    kind: AstTyKind::Path(AstPath {
                        segments: prefix.to_vec(),
                        span: p.span,
                    }),
                    span: p.span,
                };
                let is_prim = matches!(crate::ty::resolve_ty(&ty), HirTy::Prim(_));
                if !is_prim && self.canon_type(&pre).is_none() {
                    return None;
                }
                self.resolve_ty_inner(&ty)
            }
        };
        let mut open = Vec::new();
        collect_unknown_paths(&base, &mut open);
        if !open.is_empty() {
            let mut path: Vec<String> = pre.iter().map(|s| (*s).to_owned()).collect();
            path.push(last.name.clone());
            return Some(HirTy::Path(path));
        }
        // A type parameter's projection goes through its bounds (and
        // their supertraits) first.
        let via = match pre.as_slice() {
            [n] => self.ty_bounds.get(*n).cloned(),
            _ => None,
        };
        let with_args: Vec<TraitRef> = match pre.as_slice() {
            [n] => self
                .ty_bound_args
                .get(*n)
                .into_iter()
                .flatten()
                .map(|p| {
                    resolve::trait_ref(&self.env.names, p, &self.current_module, self.here(), |t| {
                        self.resolve_ty_inner(t)
                    })
                })
                .collect(),
            _ => Vec::new(),
        };
        Some(self.project_or_report(&base, &last.name, via.as_deref(), &with_args, false))
    }

    /// `project`, reporting a miss. `strict`: only `traits` count;
    /// otherwise they are preferred and every impl is the fallback.
    /// `args`: a trait's impls must have these leading arguments.
    fn project_or_report(
        &self,
        base: &HirTy,
        name: &str,
        traits: Option<&[String]>,
        args: &[TraitRef],
        strict: bool,
    ) -> HirTy {
        let hit = match traits {
            Some(t) if strict => self.project(base, name, Some(t), args),
            Some(t) => self
                .project(base, name, Some(t), args)
                .or_else(|| self.project(base, name, None, &[])),
            None => self.project(base, name, None, &[]),
        };
        hit.unwrap_or_else(|| {
            let via = match traits {
                Some([t]) if strict => format!(" of `{t}`"),
                _ => String::new(),
            };
            self.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`{}` has no associated type `{name}`{via} (no trait impl of it defines one)",
                    self.ty_name(base)
                ),
            );
            HirTy::Unknown
        })
    }

    /// Associated type `name` of concrete type `base`, from its trait
    /// impls (concrete or generic) — of `traits` only, when given.
    fn project(
        &self,
        base: &HirTy,
        name: &str,
        traits: Option<&[String]>,
        args: &[TraitRef],
    ) -> Option<HirTy> {
        let key = (
            base.clone(),
            name.to_owned(),
            traits.map(<[String]>::to_vec),
        );
        if self.env.sink.projecting.borrow().contains(&key) {
            // A cycle: this candidate adds nothing (filtered as unknown).
            return Some(HirTy::Unknown);
        }
        let wanted = |t: &str| traits.is_none_or(|ts| ts.iter().any(|x| x == t));
        // An impl's trait arguments against a bound's (`TryFrom<i64>`);
        // an argument not yet concrete matches anything.
        let args_fit = |t: &str, have: &[HirTy]| {
            args.iter().filter(|w| w.path == t).all(|want| {
                want.args.iter().zip(have).all(|(w, h)| {
                    let mut open = Vec::new();
                    collect_unknown_paths(w, &mut open);
                    collect_unknown_paths(h, &mut open);
                    !open.is_empty() || w == h || *w == HirTy::Unknown || *h == HirTy::Unknown
                })
            })
        };
        self.env.sink.projecting.borrow_mut().push(key);
        let mut hits: Vec<HirTy> = self
            .concrete_impls(base)
            .filter(|r| wanted(&r.path) && args_fit(&r.path, &r.args))
            .filter_map(|r| r.binds.iter().find(|(n, _)| n == name))
            .map(|(_, t)| t.clone())
            .collect();
        let generic = self.generic_impls(
            base,
            |gi| wanted(&gi.trait_key) && gi.assoc.iter().any(|(n, _)| n == name),
            0,
        );
        for (gi, subst) in generic {
            let Some((_, ty)) = gi.assoc.iter().find(|(n, _)| n == name) else {
                continue;
            };
            let mut rcx = LowerCtx::new(self.env, &subst, None, self.here());
            rcx.current_module.clone_from(&gi.module);
            rcx.set_bounds(&gi.generics, &gi.where_clause);
            let have = resolve::trait_args(&gi.trait_args, |t| rcx.resolve_ast_ty(t)).0;
            if args_fit(&gi.trait_key, &have) {
                hits.push(rcx.resolve_ast_ty(ty));
            }
        }
        self.env.sink.projecting.borrow_mut().pop();
        hits.retain(|t| *t != HirTy::Unknown);
        let mut uniq: Vec<HirTy> = Vec::new();
        for h in hits {
            if !uniq.contains(&h) {
                uniq.push(h);
            }
        }
        if uniq.len() > 1 {
            let names: Vec<String> = uniq
                .iter()
                .map(|t| format!("`{}`", self.ty_name(t)))
                .collect();
            self.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "associated type `{}::{name}` is ambiguous: impls define it as {} — name \
                     the trait (`<T as Tr>::{name}`, spec 2.13.4)",
                    self.ty_name(base),
                    names.join(", ")
                ),
            );
        }
        uniq.into_iter().next()
    }

    /// Record the trait bounds (with their supertraits) of the type
    /// parameters `generics` / `where_clause` declare, for projections.
    fn set_bounds(&mut self, generics: &rokc_ast::Generics, where_clause: &[rokc_ast::WherePred]) {
        let mut add = |name: &str, bounds: &[Ty]| {
            for b in bounds {
                let AstTyKind::Path(p) = &b.kind else {
                    continue;
                };
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                let key = self
                    .env
                    .names
                    .trait_key(&segs, &self.current_module, self.here());
                self.ty_bound_args
                    .entry(name.to_owned())
                    .or_default()
                    .push(p.clone());
                let mut stack = vec![key];
                while let Some(k) = stack.pop() {
                    let entry = self.ty_bounds.entry(name.to_owned()).or_default();
                    if entry.contains(&k) {
                        continue;
                    }
                    entry.push(k.clone());
                    if let Some(info) = self.env.trait_info.get(&k) {
                        stack.extend(info.supers.iter().cloned());
                    }
                }
            }
        };
        for gp in &generics.params {
            if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
                add(name, bounds);
            }
        }
        for w in where_clause {
            if let AstTyKind::Path(p) = &w.ty.kind {
                if let [seg] = p.segments.as_slice() {
                    add(&seg.name, &w.bounds);
                }
            }
        }
    }

    /// The value type of variable `id` (a `[ref]`-captured cell's
    /// element type).
    fn var_ty(&self, id: LocalId) -> HirTy {
        match self.local_ty(id) {
            HirTy::GcBuf(t) if self.is_boxed(id) => *t,
            t => t,
        }
    }

    /// Read variable `id` (through its cell when `[ref]`-captured).
    fn read_local(&self, id: LocalId, span: rokc_diagnostic::Span) -> HirExpr {
        let ty = self.local_ty(id);
        let HirTy::GcBuf(elem) = &ty else {
            return hir_local(id, &ty, span);
        };
        if !self.is_boxed(id) {
            return hir_local(id, &ty, span);
        }
        HirExpr {
            kind: HirExprKind::BufGet {
                buf: Box::new(hir_local(id, &ty, span)),
                index: Box::new(hir_int(0, PrimTy::Usize, span)),
                elem: (**elem).clone(),
            },
            ty: (**elem).clone(),
            span,
        }
    }

    /// `id = value` (into its cell when `[ref]`-captured).
    fn store_local(&self, id: LocalId, value: HirExpr) -> HirStmt {
        if !self.is_boxed(id) {
            return HirStmt::Assign { local: id, value };
        }
        let span = value.span;
        HirStmt::Expr(buf_store(hir_local(id, &self.local_ty(id), span), value))
    }

    /// Declare `let name: ty = init` (the binding declared at `at`): a
    /// plain local, or a fresh cell for a `[ref]`-captured binding.
    fn declare_var(
        &mut self,
        name: &str,
        ty: HirTy,
        init: HirExpr,
        at: rokc_diagnostic::Span,
    ) -> HirStmt {
        if !self.ref_captured.contains(&(name.to_owned(), at)) {
            let local = self.declare(Some(name.to_owned()), ty);
            return HirStmt::Let { local, init };
        }
        self.cell_let(name, ty, init)
    }

    /// A pattern binding (declared at `at`): a plain local the pattern
    /// binds; a `[ref]`-captured one is moved into a cell by `take_cells`.
    /// Spec 3.11.4: under an or-pattern sharing `name` across
    /// alternatives, the preset local, and each alternative binds the
    /// same type.
    fn declare_bound(&mut self, name: &str, ty: HirTy, at: rokc_diagnostic::Span) -> LocalId {
        if let Some(&local) = self.or_pattern_binders.last().and_then(|m| m.get(name)) {
            let existing = self.local_ty(local);
            if matches!(existing, HirTy::Unknown) {
                self.locals[local.0 as usize].ty = ty;
            } else if existing != ty {
                self.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "or-pattern binding `{name}` has inconsistent types across \
                         alternatives (`{}` and `{}`, spec 3.11.4); to bind either as \
                         their sum, write one type pattern: `{name}: {} | {}`",
                        self.ty_name(&existing),
                        self.ty_name(&ty),
                        self.ty_name(&existing),
                        self.ty_name(&ty),
                    ),
                );
            }
            return local;
        }
        let local = self.declare(Some(name.to_owned()), ty.clone());
        if self.ref_captured.contains(&(name.to_owned(), at)) {
            self.pending_cells.push((name.to_owned(), local, ty));
        }
        local
    }

    /// `let name = cell(name)` for the pattern bindings since the last
    /// call (shadowing the plain locals), to run before their scope's
    /// code.
    fn take_cells(&mut self, span: rokc_diagnostic::Span) -> Vec<HirStmt> {
        let mut out = self.take_resums(span);
        let cells: Vec<HirStmt> = std::mem::take(&mut self.pending_cells)
            .into_iter()
            .map(|(name, l, ty)| {
                let init = hir_local(l, &ty, span);
                self.cell_let(&name, ty, init)
            })
            .collect();
        out.extend(cells);
        out
    }

    /// `binder = resum(whole)` for the sub-sum type patterns since the
    /// last call.
    fn take_resums(&mut self, span: rokc_diagnostic::Span) -> Vec<HirStmt> {
        std::mem::take(&mut self.pending_resums)
            .into_iter()
            .map(|(binder, whole)| {
                let (to, from) = (self.local_ty(binder), self.local_ty(whole));
                let init = resum(self, hir_local(whole, &from, span), &to);
                HirStmt::Let {
                    local: binder,
                    init,
                }
            })
            .collect()
    }

    /// `let name = <new cell holding init>`.
    fn cell_let(&mut self, name: &str, ty: HirTy, init: HirExpr) -> HirStmt {
        let span = init.span;
        let cell_ty = HirTy::GcBuf(Box::new(ty.clone()));
        let tmp = self.declare(None, cell_ty.clone());
        let local = self.declare(Some(name.to_owned()), cell_ty.clone());
        self.locals[local.0 as usize].boxed = true;
        let cell = HirExprKind::BufNew {
            elem: ty,
            len: Box::new(hir_int(1, PrimTy::Usize, span)),
        };
        HirStmt::Let {
            local,
            init: HirExpr {
                kind: HirExprKind::Block(Box::new(HirBlock {
                    stmts: vec![
                        HirStmt::Let {
                            local: tmp,
                            init: HirExpr {
                                kind: cell,
                                ty: cell_ty.clone(),
                                span,
                            },
                        },
                        HirStmt::Expr(buf_store(hir_local(tmp, &cell_ty, span), init)),
                    ],
                    trailing: Some(hir_local(tmp, &cell_ty, span)),
                    label: None,
                })),
                ty: cell_ty,
                span,
            },
        }
    }

    /// Signature of function `id` (a method's, whatever its key).
    fn sig_by_id(&self, id: FunctionId) -> FnSig {
        self.sig_of_key(&self.env.key_of[&id])
    }

    /// `fn_table[key]`, with a return type inferred from the body when
    /// the declaration omits it (spec 4.1.3).
    fn sig_of_key(&self, key: &str) -> FnSig {
        let mut sig = self.env.fn_table[key].clone();
        if self.env.infer_ret.contains(&sig.id) {
            sig.ret_ty = mono::decl_ret(self, sig.id, sig.ret_ty);
        }
        sig
    }

    fn into_locals(self) -> Vec<HirLocal> {
        self.locals
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.local_uses.push(Vec::new());
        self.nested_fns.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
        self.local_uses.pop();
        self.nested_fns.pop();
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
        self.locals.push(HirLocal {
            id,
            name,
            ty,
            boxed: false,
        });
        id
    }

    /// Whether `id` is a `[ref]`-captured variable's cell.
    fn is_boxed(&self, id: LocalId) -> bool {
        self.locals[id.0 as usize].boxed
    }

    fn lookup(&self, name: &str) -> Option<LocalId> {
        for scope in self.scopes.iter().rev() {
            if let Some(id) = scope.get(name) {
                return Some(*id);
            }
        }
        None
    }

    /// Look up a name only in the innermost scope, for the `let`
    /// redeclaration check: nested scopes can rebind, the same one cannot.
    fn lookup_in_current_scope(&self, name: &str) -> Option<LocalId> {
        self.scopes.last().and_then(|s| s.get(name).copied())
    }

    fn local_ty(&self, id: LocalId) -> HirTy {
        self.locals
            .get(id.0 as usize)
            .map_or(HirTy::Unknown, |l| l.ty.clone())
    }
}

/// Primitive type names, for "did you mean" hints.
const PRIM_NAMES: &[&str] = &[
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize", "f32",
    "f64", "bool", "char", "str", "int", "float",
];

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

/// `cell[0] = value` on a one-element `GcBuf` cell.
fn buf_store(cell: HirExpr, value: HirExpr) -> HirExpr {
    let span = value.span;
    let elem = match &cell.ty {
        HirTy::GcBuf(t) => (**t).clone(),
        _ => value.ty.clone(),
    };
    HirExpr {
        kind: HirExprKind::BufSet {
            buf: Box::new(cell),
            index: Box::new(hir_int(0, PrimTy::Usize, span)),
            value: Box::new(value),
            elem,
        },
        ty: HirTy::Unit,
        span,
    }
}

/// The bindings (name, declaring span) that some closure in `body`
/// (nested ones included) captures as `[ref x]`: each `[ref x]` names
/// the innermost `x` in scope at the closure.
fn ref_captured_bindings(
    params: &[Param],
    body: &Block,
) -> std::collections::HashSet<(String, rokc_diagnostic::Span)> {
    type Binding = (String, rokc_diagnostic::Span);
    struct V {
        scopes: Vec<Vec<Binding>>,
        out: std::collections::HashSet<Binding>,
    }
    impl crate::walk::AstVisitor for V {
        fn expr(&mut self, e: &Expr) {
            let ExprKind::Closure { captures, .. } = &e.kind else {
                return;
            };
            for c in captures {
                let rokc_ast::CaptureSpec::Ref(n) = c else {
                    continue;
                };
                let found = self
                    .scopes
                    .iter()
                    .rev()
                    .flat_map(|s| s.iter().rev())
                    .find(|(b, _)| b == n);
                if let Some(b) = found {
                    self.out.insert(b.clone());
                }
            }
        }
        fn bind_at(&mut self, name: &str, at: rokc_diagnostic::Span) {
            if let Some(s) = self.scopes.last_mut() {
                s.push((name.to_owned(), at));
            }
        }
        fn push_scope(&mut self) {
            self.scopes.push(Vec::new());
        }
        fn pop_scope(&mut self) {
            self.scopes.pop();
        }
    }
    let mut v = V {
        scopes: vec![params.iter().map(|p| (p.name.clone(), p.span)).collect()],
        out: std::collections::HashSet::new(),
    };
    crate::walk::walk_block(&mut v, body);
    v.out
}

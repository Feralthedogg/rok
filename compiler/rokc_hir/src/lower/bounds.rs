//! Generic bodies checked at their definition (spec 2.10.9).
//!
//! Each generic body (generic fn, generic impl method, generic method,
//! trait default method) is lowered once with its type parameters (and
//! a default's `Self`) bound to opaque `HirTy::Param`s. A `Param` has
//! only what its bounds give — with their supertraits, defaults
//! filled, associated types (bound by the bound or opaque projections)
//! and `where` clauses: methods and static calls resolve through the
//! bound traits' declarations (`bound_methods`), operators through the
//! operator trait's bound, trait questions (`has_impl`) through the
//! bound list. Instances over a `Param` are signatures only
//! (`mono::var_instance`), as for `let` inference variables, so a check
//! lowers its own body alone. Then everything the lowering made is
//! undone (functions, type instances, ids, recorded uses); only its
//! errors stay. A check thus adds nothing to the build but its errors,
//! and an incremental build takes them from the store
//! (`incr::Incr::checked`) while the interface and the body are
//! unchanged.
//!
//! Monomorphization stays the code path. An instance of a template
//! that failed its check reports nothing more (`failed`). Implicit
//! type parameters (spec 4.2.2) are exempt: such a template is checked
//! per instance only. A `const` parameter takes a value no other in
//! the body has (a distinct prime past the unrolled array lengths), so
//! `[T; N]` and `[T; M]` differ while `[T; M * N]` and `[T; N * M]`
//! agree (spec 2.11.5); diagnostics show its name.

#[allow(clippy::wildcard_imports)]
use super::*;

/// One type parameter (or projection) being checked.
pub(super) struct ParamInfo {
    pub(super) name: String,
    bounds: Vec<TraitRef>,
    /// `bounds` with every supertrait, once asked for.
    all: Option<Vec<TraitRef>>,
    /// Associated types projected so far: name → type.
    projs: Vec<(String, HirTy)>,
}

fn fresh(env: &Env<'_>, name: String) -> HirTy {
    let mut ps = env.sink.params.borrow_mut();
    ps.push(ParamInfo {
        name,
        bounds: Vec::new(),
        all: None,
        projs: Vec::new(),
    });
    HirTy::Param(u32::try_from(ps.len() - 1).expect("type parameter overflow"))
}

fn add_bound(env: &Env<'_>, p: u32, r: TraitRef) {
    let mut ps = env.sink.params.borrow_mut();
    let info = &mut ps[p as usize];
    if !info.bounds.contains(&r) {
        info.bounds.push(r);
        info.all = None;
    }
}

/// Does `t` mention a `Param`?
pub(super) fn has_param(ctx: &LowerCtx<'_>, t: &HirTy) -> bool {
    let rec = |t: &HirTy| has_param(ctx, t);
    match t {
        HirTy::Param(_) => true,
        HirTy::Struct(id) => ctx.struct_def(*id).generic_args.iter().any(rec),
        HirTy::Enum(id) => ctx.enum_def(*id).generic_args.iter().any(rec),
        HirTy::Sum(ps) | HirTy::Tuple(ps) => ps.iter().any(rec),
        HirTy::Array(e, _) | HirTy::GcBuf(e) => rec(e),
        HirTy::Fn(a, r, _) => a.iter().any(rec) || rec(r),
        HirTy::Closure { args, ret, env } => args.iter().any(rec) || rec(ret) || rec(env),
        HirTy::Throws { ok, err } => rec(ok) || rec(err),
        HirTy::AnyTrait(bs) => bs
            .iter()
            .any(|b| b.args.iter().chain(b.binds.iter().map(|(_, t)| t)).any(rec)),
        _ => false,
    }
}

/// A context resolving names inside trait `info`'s declaration, its
/// parameters bound to `r`'s arguments and `Self` to `self_ty`.
fn in_trait<'a>(
    ctx: &LowerCtx<'a>,
    info: &TraitInfo,
    r: &TraitRef,
    self_ty: &HirTy,
    subst: &'a mut TySubst,
) -> LowerCtx<'a> {
    let names = info.generics.params.iter().map(|gp| match gp {
        rokc_ast::GenericParam::Type { name, .. } | rokc_ast::GenericParam::Const { name, .. } => {
            name.clone()
        }
    });
    subst.extend(names.zip(r.args.iter().cloned()));
    subst.extend(r.binds.iter().cloned());
    let subst: &'a TySubst = subst;
    let mut rcx = LowerCtx::new(ctx.env, subst, Some(self_ty.clone()), ctx.here());
    rcx.current_module.clone_from(&info.module);
    // A bare associated type is `Self::X` (spec 2.8.3).
    rcx.assoc_names = info.assoc.iter().map(|(n, _)| n.clone()).collect();
    rcx
}

/// `r` (a bound on `self_ty`) with the trait's omitted arguments taken
/// from its parameter defaults (`Add` is `Add<Self>`, spec 2.10.5).
fn complete(ctx: &LowerCtx<'_>, mut r: TraitRef, self_ty: &HirTy) -> TraitRef {
    let Some(info) = ctx.env.trait_of(&r.path) else {
        return r;
    };
    for gp in info.generics.params.iter().skip(r.args.len()) {
        let t = match gp {
            rokc_ast::GenericParam::Type {
                default: Some(d), ..
            } => {
                let mut subst = TySubst::new();
                in_trait(ctx, info, &r, self_ty, &mut subst).resolve_ast_ty(d)
            }
            // Left open by the bound (`S: Source<Item = i32>` of
            // `Source<K>`): some type, unknown.
            rokc_ast::GenericParam::Type { name, .. } => fresh(ctx.env, name.clone()),
            rokc_ast::GenericParam::Const { .. } => break,
        };
        r.args.push(t);
    }
    r
}

/// Bound `b` on `self_ty` as written in `module` (resolved by `rcx`).
fn bound_on(rcx: &LowerCtx<'_>, b: &Ty, module: &str, self_ty: &HirTy) -> Option<TraitRef> {
    let r = rcx.bound_ref(b, module, |t| rcx.resolve_ast_ty(t))?;
    rcx.env
        .names
        .is_trait(&r.path)
        .then(|| complete(rcx, r, self_ty))
}

/// `p`'s bounds and all their supertraits.
pub(super) fn traits_of(ctx: &LowerCtx<'_>, p: u32) -> Vec<TraitRef> {
    if let Some(all) = &ctx.env.sink.params.borrow()[p as usize].all {
        return all.clone();
    }
    let me = HirTy::Param(p);
    let mut out: Vec<TraitRef> = Vec::new();
    let mut stack: Vec<TraitRef> = ctx.env.sink.params.borrow()[p as usize]
        .bounds
        .iter()
        .rev()
        .cloned()
        .collect();
    while let Some(r) = stack.pop() {
        if out.contains(&r) {
            continue;
        }
        if let Some(info) = ctx.env.trait_of(&r.path) {
            let mut subst = TySubst::new();
            let rcx = in_trait(ctx, info, &r, &me, &mut subst);
            for st in info.super_tys.iter().rev() {
                if let Some(s) = bound_on(&rcx, st, &info.module, &me) {
                    stack.push(s);
                }
            }
        }
        out.push(r);
    }
    ctx.env.sink.params.borrow_mut()[p as usize].all = Some(out.clone());
    out
}

/// Does `p` meet `want` through its bounds?
pub(super) fn has(ctx: &LowerCtx<'_>, p: u32, want: &TraitRef) -> bool {
    traits_of(ctx, p).iter().any(|r| r.satisfies(want))
}

/// Associated type `name` of `p` (of `traits` only, when given): the
/// binding a bound gives it (`I: Iterator<Item = i32>`), else an
/// opaque projection `I::Item` bounded as the trait declares it and as
/// `where` clauses add.
pub(super) fn project(
    ctx: &LowerCtx<'_>,
    p: u32,
    name: &str,
    traits: Option<&[String]>,
) -> Option<HirTy> {
    let wanted = |r: &&TraitRef| traits.is_none_or(|ts| ts.contains(&r.path));
    let all = traits_of(ctx, p);
    if let Some(t) = all.iter().filter(wanted).find_map(|r| {
        r.binds
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, t)| t.clone())
    }) {
        return Some(t);
    }
    let (r, decl) = all.iter().filter(wanted).find_map(|r| {
        let info = ctx.env.trait_of(&r.path)?;
        let bounds = info.assoc.iter().find(|(n, _)| n == name)?;
        Some((r, &bounds.1))
    })?;
    if let Some((_, t)) = ctx.env.sink.params.borrow()[p as usize]
        .projs
        .iter()
        .find(|(n, _)| n == name)
    {
        return Some(t.clone());
    }
    let shown = format!("{}::{name}", ctx.env.sink.params.borrow()[p as usize].name);
    let t = fresh(ctx.env, shown);
    ctx.env.sink.params.borrow_mut()[p as usize]
        .projs
        .push((name.to_owned(), t.clone()));
    let HirTy::Param(q) = t else {
        unreachable!("fresh makes a Param")
    };
    let info = ctx.env.trait_of(&r.path).expect("a trait");
    let mut subst = TySubst::new();
    let rcx = in_trait(ctx, info, r, &HirTy::Param(p), &mut subst);
    for b in decl {
        if let Some(b) = bound_on(&rcx, b, &info.module, &t) {
            add_bound(ctx.env, q, b);
        }
    }
    Some(t)
}

/// The template calling method `method` of `p`'s bound traits (of
/// trait `only` when given) goes through.
pub(super) fn bound_method<'e>(
    ctx: &LowerCtx<'e>,
    p: u32,
    method: &str,
    only: Option<&str>,
) -> Option<&'e GenericMethod> {
    let env: &'e Env<'e> = ctx.env;
    traits_of(ctx, p)
        .iter()
        .filter(|r| only.is_none_or(|k| k == r.path))
        .find_map(|r| env.bound_method(&r.path, method))
}

/// `bind_self` for a bound template (`bound_methods`): the trait's
/// parameters take the arguments of `p`'s bound.
pub(super) fn bind_trait_args(
    ctx: &LowerCtx<'_>,
    fn_def: &FnDef,
    p: u32,
    subst: &mut HashMap<String, HirTy>,
) {
    let Some(key) = ctx.env.bound_trait(&fn_def.name) else {
        return;
    };
    let Some(r) = traits_of(ctx, p).into_iter().find(|r| r.path == *key) else {
        return;
    };
    let info = ctx.env.trait_of(key).expect("a trait");
    for (gp, a) in info.generics.params.iter().zip(r.args) {
        let (rokc_ast::GenericParam::Type { name, .. }
        | rokc_ast::GenericParam::Const { name, .. }) = gp;
        subst.entry(name.clone()).or_insert(a);
    }
}

/// The templates `bound_methods` holds: per trait method, its
/// declaration with the trait's parameters first among its generics
/// (bound from the receiver's bound, `bind_trait_args`), no body, and
/// its bare associated types (the trait's and its supertraits') read
/// as `Self::X`. Also: template name → trait.
pub(super) fn templates(
    trait_info: &HashMap<String, TraitInfo>,
) -> (
    HashMap<(String, String), GenericMethod>,
    HashMap<String, String>,
) {
    let mut out = HashMap::new();
    let mut traits = HashMap::new();
    for (key, info) in trait_info {
        let mut assoc: HashMap<String, Ty> = HashMap::new();
        let mut seen: Vec<&str> = Vec::new();
        let mut stack = vec![key.as_str()];
        while let Some(k) = stack.pop() {
            if seen.contains(&k) {
                continue;
            }
            seen.push(k);
            let Some(i) = trait_info.get(k) else { continue };
            for (n, _) in &i.assoc {
                assoc.entry(n.clone()).or_insert_with(|| self_assoc(n));
            }
            stack.extend(i.supers.iter().map(String::as_str));
        }
        let module = module_of(key);
        for (m, decl) in &info.decls {
            let mut def = decl.clone();
            def.body = None;
            def.name = format!("#{}__{m}", leaf_name(key));
            if !module.is_empty() {
                def.name = format!("{module}::{}", def.name);
            }
            let own = std::mem::take(&mut def.generics.params);
            def.generics.params = info
                .generics
                .params
                .iter()
                .map(|gp| match gp {
                    rokc_ast::GenericParam::Type { name, .. } => rokc_ast::GenericParam::Type {
                        name: name.clone(),
                        bounds: Vec::new(),
                        default: None,
                    },
                    c @ rokc_ast::GenericParam::Const { .. } => c.clone(),
                })
                .chain(own)
                .collect();
            collect::subst_assoc_sig(&mut def, &assoc);
            traits.insert(def.name.clone(), key.clone());
            let self_ty = Ty {
                kind: AstTyKind::SelfUpper,
                span: def.span,
            };
            out.insert(
                (key.clone(), m.clone()),
                GenericMethod {
                    def,
                    self_ty,
                    info: MethodInfo {
                        module: module.clone(),
                        vis: Visibility::Pub,
                        trait_name: Some(key.clone()),
                        trait_args: Vec::new(),
                    },
                },
            );
        }
    }
    (out, traits)
}

/// `Self::name` as written.
fn self_assoc(name: &str) -> Ty {
    let seg = |n: &str| rokc_ast::PathSegment {
        name: n.to_owned(),
        generics: Vec::new(),
    };
    Ty {
        kind: AstTyKind::Path(AstPath {
            segments: vec![seg("Self"), seg(name)],
            span: Span::DUMMY,
        }),
        span: Span::DUMMY,
    }
}

/// Is `f` checked per instance only (an implicit parameter, spec 4.2.2)?
fn implicit(f: &FnDef) -> bool {
    f.generics
        .params
        .iter()
        .any(|gp| matches!(gp, rokc_ast::GenericParam::Type { name, .. } if name.starts_with("T#")))
}

/// Check every generic body whose module `wanted` picks: generic fns,
/// generic impl methods and generic methods, and trait default methods
/// (once, with an opaque `Self`; a copy in an impl is not checked).
pub(super) fn check_all(
    env: &Env<'_>,
    incr: Option<&super::incr::Incr<'_>>,
    wanted: impl Fn(&str) -> bool,
) {
    let defaults: std::collections::HashSet<Span> = env
        .trait_info
        .values()
        .flat_map(|i| i.decls.values())
        .filter(|d| d.body.is_some())
        .map(|d| d.span)
        .collect();
    let mut todo: Vec<(&FnDef, String, SelfOf<'_>)> = env
        .generic_fns
        .values()
        .map(|f| (*f, SelfOf::None))
        .chain(
            env.impls
                .generic()
                .flat_map(|gi| gi.methods.values())
                .chain(env.generic_methods.values().flatten())
                .map(|gm| (&gm.def, SelfOf::Impl(&gm.self_ty))),
        )
        .filter(|(f, _)| f.body.is_some() && !implicit(f) && !defaults.contains(&f.span))
        .map(|(f, s)| (f, module_of(&f.name), s))
        .chain(env.trait_info.iter().flat_map(|(key, info)| {
            info.decls
                .values()
                .filter(|d| d.body.is_some())
                .map(|d| (d, info.module.clone(), SelfOf::Trait(key.as_str())))
        }))
        .filter(|(_, module, _)| wanted(module))
        .collect();
    todo.sort_by(|a, b| a.0.name.cmp(&b.0.name));
    todo.dedup_by(|a, b| a.0.name == b.0.name && a.0.span == b.0.span);
    todo.sort_by_key(|(f, ..)| (f.span.file, f.span.start));
    for (f, module, self_of) in todo {
        let generics: Vec<&rokc_ast::GenericParam> = match self_of {
            SelfOf::Trait(key) => env.trait_info[key].generics.params.iter().collect(),
            _ => Vec::new(),
        };
        let generics: Vec<_> = generics.into_iter().chain(&f.generics.params).collect();
        let mut owner = rokc_core::codec::Enc::new(true);
        match &self_of {
            SelfOf::None => {}
            SelfOf::Impl(t) => rokc_core::codec::Codec::enc(*t, &mut owner),
            SelfOf::Trait(k) => owner.buf.extend_from_slice(k.as_bytes()),
        }
        let run = || check_one(env, f, module.clone(), &generics, &self_of);
        let errors = match incr {
            Some(incr) => incr.checked(env, f, &owner.buf, run),
            None => run(),
        };
        if !errors.is_empty() {
            env.sink.failed.borrow_mut().insert(f.span);
            env.sink.diagnostics.borrow_mut().extend(errors);
        }
    }
}

/// What `Self` is in a checked body.
enum SelfOf<'a> {
    None,
    /// An impl's target as written.
    Impl(&'a Ty),
    /// A trait's default method: opaque, bounded by the trait.
    Trait(&'a str),
}

/// What a check may leave in the shared state, to be undone after it.
struct Snapshot {
    next_id: u32,
    structs: usize,
    enums: usize,
    params: usize,
    infer_vars: usize,
    name_diags: usize,
    alias_uses: usize,
    unknown: std::collections::HashSet<String>,
    /// Return types inferred so far: one inferred during the check may
    /// name a type instance the check made.
    inferred_ret: HashMap<FunctionId, Option<HirTy>>,
    recursive_ret: usize,
    tentative_ret: usize,
}

impl Snapshot {
    fn take(env: &Env<'_>) -> Self {
        let sink = &env.sink;
        Self {
            next_id: sink.next_id.get(),
            structs: env.defs.structs.borrow().len(),
            enums: env.defs.enums.borrow().len(),
            params: sink.params.borrow().len(),
            infer_vars: sink.infer_vars.borrow().len(),
            name_diags: env.names.diags.borrow().len(),
            alias_uses: env.names.alias_uses.borrow().len(),
            unknown: env.names.unknown_spans.borrow().keys().cloned().collect(),
            inferred_ret: sink.inferred_ret.borrow().clone(),
            recursive_ret: sink.recursive_ret.borrow().len(),
            tentative_ret: sink.tentative_ret.borrow().len(),
        }
    }

    /// Back to the snapshot (after `LowerCtx::rollback`); the name
    /// diagnostics reported since.
    fn restore(self, env: &Env<'_>) -> Vec<rokc_diagnostic::RokDiagnostic> {
        let sink = &env.sink;
        let old = |id: &FunctionId| id.0 < self.next_id;
        sink.fn_origin.borrow_mut().retain(|id, _| old(id));
        sink.track_caller.borrow_mut().retain(old);
        *sink.inferred_ret.borrow_mut() = self.inferred_ret;
        sink.recursive_ret.borrow_mut().truncate(self.recursive_ret);
        sink.tentative_ret.borrow_mut().truncate(self.tentative_ret);
        sink.next_id.set(self.next_id);
        env.defs.truncate(self.structs, self.enums);
        sink.params.borrow_mut().truncate(self.params);
        sink.infer_vars.borrow_mut().truncate(self.infer_vars);
        sink.const_names.borrow_mut().clear();
        sink.assumed.borrow_mut().clear();
        env.names.alias_uses.borrow_mut().truncate(self.alias_uses);
        env.names
            .unknown_spans
            .borrow_mut()
            .retain(|k, _| self.unknown.contains(k));
        env.names.diags.borrow_mut().split_off(self.name_diags)
    }
}

/// Lower body `f` with `generics` (the impl's, or the trait's, then its
/// own) as opaque type parameters: its errors. The shared state is left
/// as it was.
fn check_one(
    env: &Env<'_>,
    f: &FnDef,
    module: String,
    generics: &[&rokc_ast::GenericParam],
    self_of: &SelfOf<'_>,
) -> Vec<rokc_diagnostic::RokDiagnostic> {
    let snapshot = Snapshot::take(env);
    let mut subst = TySubst::new();
    let mut consts = Vec::new();
    for gp in generics {
        match gp {
            rokc_ast::GenericParam::Type { name, .. } => {
                subst.insert(name.clone(), fresh(env, name.clone()));
            }
            rokc_ast::GenericParam::Const { name, ty } => consts.push((name, ty)),
        }
    }
    for (name, ty) in consts {
        let p = match LowerCtx::new(env, &subst, None, f.span).resolve_ast_ty(ty) {
            HirTy::Prim(p) => p,
            _ => PrimTy::Usize,
        };
        let v = match p {
            PrimTy::Bool => 1,
            PrimTy::Char => i128::from(u32::from('a')),
            _ => stand_in(env, name),
        };
        subst.insert(name.clone(), HirTy::Const(v, Some(p)));
    }
    let self_param = match self_of {
        SelfOf::Trait(key) => {
            let me = fresh(env, "Self".to_owned());
            let args = env
                .trait_of(key)
                .expect("a trait")
                .generics
                .params
                .iter()
                .map(|gp| {
                    let (rokc_ast::GenericParam::Type { name, .. }
                    | rokc_ast::GenericParam::Const { name, .. }) = gp;
                    subst[name].clone()
                })
                .collect();
            if let HirTy::Param(p) = me {
                add_bound(env, p, TraitRef::new((*key).to_owned(), args, Vec::new()));
            }
            Some(me)
        }
        _ => None,
    };
    let mut ctx = LowerCtx::new(env, &subst, self_param.clone(), f.span);
    ctx.current_module.clone_from(&module);
    ctx.assoc_names = f
        .attrs
        .iter()
        .filter(|a| a.path.first().is_some_and(|p| p == crate::ASSOC_TYPES_ATTR))
        .flat_map(|a| a.path[1..].iter().cloned())
        .collect();
    let mark = ctx.probe_mark();
    // Bounds on the parameters first, then the `where` clauses that
    // name one alone, then the rest (`T::Item: Display` projects
    // through `T`'s bounds).
    for gp in generics {
        if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
            for b in bounds {
                let t = &subst[name];
                if let (HirTy::Param(p), Some(r)) = (t, bound_on(&ctx, b, &module, t)) {
                    add_bound(env, *p, r);
                }
            }
        }
    }
    let bare = |w: &&rokc_ast::WherePred| matches!(&w.ty.kind, AstTyKind::Path(p) if p.segments.len() == 1 && subst.contains_key(&p.segments[0].name));
    let (alone, rest): (Vec<_>, Vec<_>) = f.where_clause.iter().partition(bare);
    // A clause on another type (`where List<T>: Display`) is assumed in
    // the body.
    for w in alone.iter().chain(&rest) {
        let t = ctx.resolve_ast_ty(&w.ty);
        for b in &w.bounds {
            match (&t, bound_on(&ctx, b, &module, &t)) {
                (HirTy::Param(p), Some(r)) => add_bound(env, *p, r),
                (_, Some(r)) => env.sink.assumed.borrow_mut().push((t.clone(), r)),
                _ => {}
            }
        }
    }
    let self_hir = match self_of {
        SelfOf::Impl(t) => Some(ctx.resolve_ast_ty(t)),
        _ => self_param,
    };
    let id = FunctionId(env.sink.next_id.get());
    env.sink.next_id.set(id.0 + 1);
    mono::lower_fn_inner(env, f, id, f.name.clone(), self_hir, module, &subst);
    let mut errors = ctx.rollback(&mark);
    errors.extend(snapshot.restore(env));
    errors.retain(rokc_diagnostic::RokDiagnostic::is_error);
    errors
}

/// Does a `where` clause of the body being checked give `ty` `want`?
pub(super) fn assumed(env: &Env<'_>, ty: &HirTy, want: &TraitRef) -> bool {
    let assumed = env.sink.assumed.borrow();
    assumed.iter().any(|(t, r)| t == ty && r.satisfies(want))
}

/// The integer standing for const `name` in the body being checked:
/// a prime past the unrolled array lengths no other one there takes.
fn stand_in(env: &Env<'_>, name: &str) -> i128 {
    let mut names = env.sink.const_names.borrow_mut();
    if let Some((v, _)) = names.iter().find(|(_, n)| n == name) {
        return *v;
    }
    let floor = names.iter().map(|(v, _)| *v).max().unwrap_or(100);
    // Prime gaps this low are far below 1000.
    let v = (floor + 1..floor + 1000)
        .find(|n| (2..*n).all(|d| n % d != 0))
        .unwrap_or_default();
    names.push((v, name.to_owned()));
    v
}

/// The `const` parameter value `v` stands for in the body being
/// checked.
pub(super) fn const_name(env: &Env<'_>, v: i128) -> Option<String> {
    let names = env.sink.const_names.borrow();
    names.iter().find(|(n, _)| *n == v).map(|(_, s)| s.clone())
}

/// `T::NAME` (spec 2.8.3a): the const a bound's trait declares, of
/// its declared type. An integer, `bool` or `char` stands as a value
/// no other in the body has (as a `const` parameter); another type is
/// an opaque value.
pub(super) fn assoc_const(
    ctx: &LowerCtx<'_>,
    p: u32,
    name: &str,
    traits: Option<&[String]>,
) -> Option<HirExpr> {
    let me = HirTy::Param(p);
    let (r, decl) = traits_of(ctx, p).into_iter().find_map(|r| {
        if traits.is_some_and(|ts| !ts.contains(&r.path)) {
            return None;
        }
        let info = ctx.env.trait_of(&r.path)?;
        let (_, ty) = info.consts.iter().find(|(n, _)| n == name)?;
        Some((r, ty.clone()))
    })?;
    let info = ctx.env.trait_of(&r.path).expect("a trait");
    let mut subst = TySubst::new();
    let ty = in_trait(ctx, info, &r, &me, &mut subst).resolve_ast_ty(&decl);
    let span = ctx.here();
    let shown = format!("{}::{name}", ctx.ty_name(&me));
    let value = match &ty {
        HirTy::Prim(PrimTy::Bool) => Some(ConstVal::Bool(true)),
        HirTy::Prim(PrimTy::Char) => Some(ConstVal::Char(u32::from('a'))),
        HirTy::Prim(t) if t.is_int() => Some(ConstVal::Int {
            value: stand_in(ctx.env, &shown),
            ty: *t,
        }),
        _ => None,
    };
    let kind = value.map_or(
        HirExprKind::Call {
            callee: FunctionId(u32::MAX),
            args: Vec::new(),
        },
        HirExprKind::Const,
    );
    Some(HirExpr { kind, ty, span })
}

/// `t.method(..)` on a type parameter whose bounds don't declare it.
pub(super) fn no_method(ctx: &LowerCtx<'_>, p: u32, method: &str, span: Span) -> HirExpr {
    let t = ctx.ty_name(&HirTy::Param(p));
    let bounds: Vec<String> = ctx.env.sink.params.borrow()[p as usize]
        .bounds
        .iter()
        .map(|r| format!("`{}`", leaf_name(&r.path)))
        .collect();
    let have = if bounds.is_empty() {
        "it has no bounds".to_owned()
    } else {
        format!("its bounds ({}) do not declare it", bounds.join(", "))
    };
    let e = ctx.error_expr(
        span,
        format!("no method `{method}` on type parameter `{t}`: {have} (spec 2.10.9)"),
    );
    ctx.help_last(Some(format!(
        "add a bound on `{t}` whose trait declares `{method}`"
    )));
    e
}

/// Is a body that failed its check being lowered for an instance or an
/// impl (its errors repeat the check's)?
pub(super) fn in_failed(env: &Env<'_>) -> bool {
    let failed = env.sink.failed.borrow();
    env.sink.bodies.borrow().iter().any(|s| {
        super::incr::read(|| super::incr::Read::CheckFailed(*s));
        failed.contains(s)
    })
}

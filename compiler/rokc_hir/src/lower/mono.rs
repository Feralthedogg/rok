//! Function lowering entry points and generic instantiation
//! (monomorphization, generic struct / enum instantiation).

#[allow(clippy::wildcard_imports)]
use super::*;

/// Match an AST parameter type against a concrete `HirTy` (the call
/// argument's inferred type) to discover bindings for generic type
/// parameters. Walks structurally — `[T; N]` against `[i32; 4]` binds
/// `T → i32`, etc.
pub(super) fn unify_param_ty_with(
    param_ty: &rokc_ast::Ty,
    arg_ty: &HirTy,
    generic_names: &std::collections::HashSet<String>,
    subst: &mut HashMap<String, HirTy>,
    ctx: &LowerCtx<'_>,
) {
    let mut rec = |p: &rokc_ast::Ty, a: &HirTy| {
        unify_param_ty_with(p, a, generic_names, subst, ctx);
    };
    match (&param_ty.kind, arg_ty) {
        (rokc_ast::TyKind::Path(p), _)
            if p.segments.len() == 1 && generic_names.contains(&p.segments[0].name) =>
        {
            // First binding wins; a conflicting later argument surfaces
            // as an argument type mismatch at the call site. `!` (a
            // diverging argument) fits any `T`, so a later one rebinds.
            let b = subst
                .entry(p.segments[0].name.clone())
                .or_insert_with(|| arg_ty.clone());
            if *b == HirTy::Never {
                *b = arg_ty.clone();
            }
        }
        // Generic struct / enum param `Pair<T>` against arg `Pair__i32`:
        // recover T by reading the instantiation's recorded generic args.
        (rokc_ast::TyKind::Path(p), HirTy::Struct(_) | HirTy::Enum(_)) => {
            let Some(last) = p.segments.last() else {
                return;
            };
            let generic_args = match arg_ty {
                HirTy::Struct(sid) => ctx.struct_def(*sid).generic_args,
                HirTy::Enum(eid) => ctx.enum_def(*eid).generic_args,
                _ => Vec::new(),
            };
            for (param_arg, concrete) in last.generics.iter().zip(generic_args.iter()) {
                rec(param_arg, concrete);
            }
        }
        (rokc_ast::TyKind::Array(elem, _), HirTy::Array(arg_elem, _)) => rec(elem, arg_elem),
        // `GcBuf<T>` against `GcBuf<i32>`.
        (rokc_ast::TyKind::Path(p), HirTy::GcBuf(e)) => {
            if let Some(g) = p.segments.last().and_then(|s| s.generics.first()) {
                rec(g, e);
            }
        }
        (rokc_ast::TyKind::Tuple(parts), HirTy::Tuple(arg_parts))
        | (rokc_ast::TyKind::Sum(parts), HirTy::Sum(arg_parts)) => {
            for (p, a) in parts.iter().zip(arg_parts.iter()) {
                rec(p, a);
            }
        }
        (
            rokc_ast::TyKind::Fn(args, ret, _),
            HirTy::Fn(arg_args, arg_ret, _)
            | HirTy::Closure {
                args: arg_args,
                ret: arg_ret,
                ..
            },
        ) => {
            for (p, a) in args.iter().zip(arg_args.iter()) {
                rec(p, a);
            }
            rec(ret, arg_ret);
        }
        (rokc_ast::TyKind::Throws { ok, err }, HirTy::Throws { ok: a, err: e }) => {
            rec(ok, a);
            rec(err, e);
        }
        // A non-throwing argument for a `rethrows` parameter: its error
        // parameter binds to "no error".
        (rokc_ast::TyKind::Throws { ok, err }, a) => {
            rec(ok, a);
            rec(err, &crate::ty::nothrow_ty());
        }
        // Nothing to bind: the argument type check reports mismatches.
        _ => {}
    }
}

/// Bind `fn_def`'s type params from the type of argument `i`. A generic
/// method's `self` is typed by its impl target `self_ty`.
pub(super) fn bind_from_arg(
    ctx: &LowerCtx<'_>,
    fn_def: &FnDef,
    self_ty: Option<&Ty>,
    i: usize,
    arg_ty: &HirTy,
    subst: &mut HashMap<String, HirTy>,
) {
    let Some(param) = fn_def.params.get(i) else {
        return;
    };
    let self_param = self_ty.filter(|_| param.name == "self");
    let Some(t) = param.ty.as_ref().or(self_param) else {
        return;
    };
    let generic_names: std::collections::HashSet<String> = fn_def
        .generics
        .params
        .iter()
        .filter_map(|gp| match gp {
            rokc_ast::GenericParam::Type { name, .. } => Some(name.clone()),
            rokc_ast::GenericParam::Const { .. } => None,
        })
        .collect();
    unify_param_ty_with(t, arg_ty, &generic_names, subst, ctx);
}

/// Resolve `ty` under the substitution of a monomorphization in
/// progress, from `fn_def`'s module. `self_ty` (resolved) fills `Self`.
pub(super) fn resolve_in_mono(
    ctx: &LowerCtx<'_>,
    fn_def: &FnDef,
    subst: &HashMap<String, HirTy>,
    self_ty: Option<HirTy>,
    ty: &Ty,
) -> HirTy {
    let mut rcx = LowerCtx::new(ctx.env, subst, self_ty);
    rcx.current_module = module_of(&fn_def.name);
    rcx.resolve_ast_ty(ty)
}

/// Instantiation limits: deeper nesting means the generic recursion
/// never reaches a fixed point (`fn r<T>(x: T) { r((x, x)) }`).
pub(super) const MONO_DEPTH_LIMIT: u32 = 64;
pub(super) const MONO_TYPE_SIZE_LIMIT: usize = 256;

pub(super) fn ty_size(ty: &HirTy) -> usize {
    1 + match ty {
        HirTy::Sum(p) | HirTy::Tuple(p) => p.iter().map(ty_size).sum(),
        HirTy::Array(e, _) => ty_size(e),
        HirTy::Fn(a, r, _) => a.iter().map(ty_size).sum::<usize>() + ty_size(r),
        HirTy::Closure { args, ret, env } => {
            args.iter().map(ty_size).sum::<usize>() + ty_size(ret) + ty_size(env)
        }
        HirTy::Throws { ok, err } => ty_size(ok) + ty_size(err),
        _ => 0,
    }
}

/// Look up or generate a specialized version of a generic function.
/// Returns `(specialized_fn_id, return_type)` on success; `None` after
/// reporting why the call can't be instantiated. Type-parameter
/// substitution is inferred by zipping the call's lowered argument types
/// with the AST parameter type ascriptions.
pub(super) fn monomorphize(
    ctx: &LowerCtx<'_>,
    fn_def: &FnDef,
    self_ty: Option<&Ty>,
    args: &[HirExpr],
    span: rokc_diagnostic::Span,
) -> Option<(FunctionId, HirTy)> {
    monomorphize_on(ctx, fn_def, self_ty, None, args, span)
}

/// Bind the impl parameters of `self_ty` (`Box<T>`) from the known
/// `Self` type `hint` (`Box<i32>` → `T = i32`).
pub(super) fn bind_self(
    ctx: &LowerCtx<'_>,
    fn_def: &FnDef,
    self_ty: &Ty,
    hint: &HirTy,
    subst: &mut HashMap<String, HirTy>,
) {
    let names: std::collections::HashSet<String> = fn_def
        .generics
        .params
        .iter()
        .filter_map(|gp| match gp {
            rokc_ast::GenericParam::Type { name, .. } => Some(name.clone()),
            rokc_ast::GenericParam::Const { .. } => None,
        })
        .collect();
    unify_param_ty_with(self_ty, hint, &names, subst, ctx);
}

/// `monomorphize` with `Self` known up front (see `bind_self`).
pub(super) fn monomorphize_on(
    ctx: &LowerCtx<'_>,
    fn_def: &FnDef,
    self_ty: Option<&Ty>,
    self_hint: Option<&HirTy>,
    args: &[HirExpr],
    _span: rokc_diagnostic::Span,
) -> Option<(FunctionId, HirTy)> {
    let fn_module = module_of(&fn_def.name);
    // Infer concrete types for each generic param by unifying the AST
    // parameter type ascription against the call's arg type. Walks into
    // arrays, tuples, sums, function types, and closures. The first
    // binding wins; a conflicting later argument is reported by the
    // argument type check at the call site.
    let mut subst: HashMap<String, HirTy> = HashMap::new();
    if let (Some(t), Some(hint)) = (self_ty, self_hint) {
        bind_self(ctx, fn_def, t, hint, &mut subst);
    }
    for (i, arg) in args.iter().enumerate() {
        bind_from_arg(ctx, fn_def, self_ty, i, &arg.ty, &mut subst);
    }
    // A type param the arguments leave open (one that only appears in
    // the return type) binds from the call's expected type: the `let`
    // annotation, the parameter slot, the enclosing `return`.
    if let Some(expected) = ctx.current_expected().filter(|t| **t != HirTy::Unknown) {
        let names: std::collections::HashSet<String> = fn_def
            .generics
            .params
            .iter()
            .filter_map(|gp| match gp {
                rokc_ast::GenericParam::Type { name, .. } if !subst.contains_key(name) => {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect();
        if !names.is_empty() {
            let ret = sig_ret_ast(fn_def);
            let ok = match &ret.kind {
                rokc_ast::TyKind::Throws { ok, .. } => ok.as_ref(),
                _ => &ret,
            };
            unify_param_ty_with(ok, expected, &names, &mut subst, ctx);
        }
    }

    // Spec 2.10.5: if a generic param has a default and no concrete type
    // got inferred for it, apply the default. Order is one pass — defaults
    // can't depend on other defaults (would need iteration).
    for gp in &fn_def.generics.params {
        if let rokc_ast::GenericParam::Type {
            name,
            default: Some(d),
            ..
        } = gp
        {
            if !subst.contains_key(name) {
                let sc = Scope {
                    names: &ctx.env.names,
                    module: &fn_module,
                };
                let resolved =
                    resolve_ty_with_structs(d, &ctx.env.struct_table, &ctx.env.enum_table, sc);
                subst.insert(name.clone(), resolved);
            }
        }
    }

    // Every generic param must be inferable.
    let mut subst_tys: Vec<HirTy> = Vec::new();
    for gp in &fn_def.generics.params {
        match gp {
            rokc_ast::GenericParam::Type { name, .. } => {
                if let Some(t) = subst.get(name) {
                    subst_tys.push(t.clone());
                } else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "cannot infer type parameter `{name}` of `{}` from the call \
                         arguments or the expected type — annotate the binding",
                            fn_def.name
                        ),
                    );
                    return None;
                }
            }
            rokc_ast::GenericParam::Const { name, .. } => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "const generic parameter `{name}` of `{}` is not implemented yet \
                         (stage-1 limitation)",
                        fn_def.name
                    ),
                );
                return None;
            }
        }
    }
    if subst_tys.iter().any(|t| matches!(t, HirTy::Unknown)) {
        // An argument already failed to lower (reported).
        return None;
    }
    if subst_tys.iter().any(|t| ty_size(t) > MONO_TYPE_SIZE_LIMIT)
        || ctx.env.sink.mono_depth.get() >= MONO_DEPTH_LIMIT
    {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "instantiating generic function `{}` recursed past the limit \
                 (depth {MONO_DEPTH_LIMIT}) — the instantiation never reaches a \
                 fixed point",
                fn_def.name
            ),
        );
        return None;
    }

    // Check generic-bound satisfaction: for each `T: Bound` declared on
    // the fn, verify that the inferred concrete type for `T` carries an
    // `impl Bound for T` block. `where` predicates count the same.
    let mut goals: Vec<(HirTy, &Vec<rokc_ast::Ty>)> = Vec::new();
    for gp in &fn_def.generics.params {
        if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
            if let Some(concrete) = subst.get(name) {
                goals.push((concrete.clone(), bounds));
            }
        }
    }
    for w in &fn_def.where_clause {
        goals.push((resolve_in_mono(ctx, fn_def, &subst, None, &w.ty), &w.bounds));
    }
    for (concrete, bounds) in goals {
        let concrete = &concrete;
        if method_target_for(concrete).is_none() {
            continue;
        }
        for bound in bounds {
            let rokc_ast::TyKind::Path(p) = &bound.kind else {
                continue;
            };
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            // `T: Iterator<Item = i32>` also checks the impl's arguments
            // and associated types.
            let (args, binds) = split_trait_args(
                p.segments.last().map_or(&[][..], |s| s.generics.as_slice()),
                |t| resolve_in_mono(ctx, fn_def, &subst, None, t),
            );
            let bound_name = bound_key(
                ctx.env.names.trait_key(&segs, &fn_module),
                &args,
                &binds,
                &ctx.env.struct_table,
                &ctx.env.enum_table,
            );
            if !ctx.implements_trait(concrete, &bound_name, 0) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "type `{}` does not satisfy trait bound `{bound_name}` required \
                         by `{}`",
                        ctx.ty_name(concrete),
                        fn_def.name
                    ),
                );
            }
        }
    }

    let key = (
        fn_def.name.clone(),
        subst_tys.iter().map(ty_mangle).collect::<Vec<_>>(),
    );
    if let Some(&existing_id) = ctx.env.sink.mono_cache.borrow().get(&key) {
        let ret_ty = ctx
            .env
            .sink
            .mono_sigs
            .borrow()
            .get(&existing_id)
            .map(|s| s.ret_ty.clone())
            .expect("mono signature registered with its cache entry");
        return Some((existing_id, ret_ty));
    }

    // Allocate a fresh id and lower the FnDef under the substitution.
    let new_id = FunctionId(ctx.env.sink.next_id.get());
    ctx.env.sink.next_id.set(new_id.0 + 1);
    let ref_self_new = super::collect::is_ref_self(fn_def);
    // Pre-cache so a recursive call inside the body finds the in-progress mono.
    ctx.env.sink.mono_cache.borrow_mut().insert(key, new_id);
    // Pre-resolve the return type from AST + subst so a recursive
    // `sum_down(n - 1)` inside the body sees the correct result type.
    // A known `Self` (the receiver's type) is used as is: the template's
    // own module may not see the impl's type (a trait default method).
    let self_hir = self_hint
        .cloned()
        .or_else(|| self_ty.map(|t| resolve_in_mono(ctx, fn_def, &subst, None, t)));
    let preview_ret_ty =
        resolve_in_mono(ctx, fn_def, &subst, self_hir.clone(), &sig_ret_ast(fn_def));
    if let (true, Some(st)) = (ref_self_new, &self_hir) {
        ctx.env
            .sink
            .ref_self
            .borrow_mut()
            .insert(new_id, (preview_ret_ty.clone(), st.clone()));
    }
    ctx.env.sink.mono_sigs.borrow_mut().insert(
        new_id,
        FnSig {
            id: new_id,
            ret_ty: preview_ret_ty,
            param_defaults: Vec::new(),
            param_tys: Vec::new(),
            param_names: Vec::new(),
        },
    );

    let mangled_name = format!(
        "{}__mono__{}",
        fn_def.name,
        subst_tys
            .iter()
            .map(ty_mangle)
            .collect::<Vec<_>>()
            .join("_")
    );

    ctx.env
        .sink
        .mono_depth
        .set(ctx.env.sink.mono_depth.get() + 1);
    let mono_fn = lower_fn_inner(
        ctx.env,
        fn_def,
        new_id,
        mangled_name,
        self_hir,
        fn_module,
        &subst,
    );
    ctx.env
        .sink
        .mono_depth
        .set(ctx.env.sink.mono_depth.get() - 1);

    let ret_ty = mono_fn.ret_ty.clone();
    let mono_param_tys: Vec<HirTy> = mono_fn.params.iter().map(|p| p.ty.clone()).collect();
    let mono_param_names: Vec<String> = mono_fn.params.iter().map(|p| p.name.clone()).collect();
    ctx.env.sink.mono_sigs.borrow_mut().insert(
        new_id,
        FnSig {
            id: new_id,
            ret_ty: ret_ty.clone(),
            param_defaults: Vec::new(),
            param_tys: mono_param_tys,
            param_names: mono_param_names,
        },
    );
    ctx.env.sink.extras.borrow_mut().push(mono_fn);
    Some((new_id, ret_ty))
}

/// Lower one function body. `subst` is the type-parameter substitution
/// of a monomorphization (empty otherwise); `module` is where the
/// body's names resolve.
pub(super) fn lower_fn_inner(
    env: &Env<'_>,
    fn_def: &FnDef,
    id: FunctionId,
    name: String,
    self_ty: Option<HirTy>,
    module: String,
    subst: &HashMap<String, HirTy>,
) -> HirFunction {
    let mut ctx = LowerCtx::new(env, subst, self_ty);
    ctx.current_module = module;
    // Marker set by the driver on the synthesized entry (spec 4.16.2).
    ctx.implicit_main = fn_def.attrs.iter().any(|a| a.path == ["#implicit_main"]);

    let mut params = Vec::with_capacity(fn_def.params.len());
    for p in &fn_def.params {
        params.push(lower_param(&mut ctx, p));
    }
    if super::collect::is_ref_self(fn_def) {
        ctx.ref_self = params.first().map(|p: &HirParam| (p.local, p.ty.clone()));
    }

    let mut ret_ty = ctx.resolve_ast_ty(&sig_ret_ast(fn_def));
    if let HirTy::Throws { ok, err } = &ret_ty {
        ctx.fn_ret_ty = (**ok).clone();
        // Spec 4.16.3: an error escaping a throwing `main` is reported by
        // the entry itself (exit 1); `main` keeps a plain C return type.
        if name == "main" && ctx.self_ty.is_none() && !ctx.implicit_main {
            ctx.uncaught_in_main = true;
            ret_ty = ctx.fn_ret_ty.clone();
        } else {
            ctx.fn_throws = Some((**err).clone());
        }
    } else {
        ctx.fn_ret_ty = ret_ty.clone();
    }

    if ctx.ref_self.is_some() && ctx.fn_throws.is_some() {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "`ref self` on the throwing method `{}` is not supported yet (stage-1 \
                 limitation)",
                leaf_name(&fn_def.name)
            ),
        );
        ctx.ref_self = None;
    }
    let body = fn_def
        .body
        .as_ref()
        .map(|b| lower_fn_body(&mut ctx, b, &fn_def.name));
    // `ref self`: the function hands `self` back with its value.
    if let Some((_, self_ty)) = &ctx.ref_self {
        ret_ty = ref_self_packed(&ret_ty, self_ty);
    }

    HirFunction {
        id,
        def_id: None,
        name,
        params,
        locals: ctx.into_locals(),
        ret_ty,
        body,
        is_async: fn_def.is_async,
        is_generator: fn_def.is_generator,
        span: fn_def.span,
    }
}

/// Like `resolve_ty_with_structs`, but applies an AST-level type-param
/// substitution before lookup. For `Pair<T>` with `subst = {T → i32}`,
/// resolves to `Pair__i32`. Walks recursively into nested types.
pub(super) fn resolve_ast_with_subst(
    ty: &rokc_ast::Ty,
    struct_table: &HashMap<String, StructId>,
    enum_table: &HashMap<String, EnumId>,
    subst: &HashMap<String, HirTy>,
    sc: Scope<'_>,
) -> HirTy {
    let rec = |t: &rokc_ast::Ty| resolve_ast_with_subst(t, struct_table, enum_table, subst, sc);
    match &ty.kind {
        rokc_ast::TyKind::Path(p) => {
            // Bare type-param reference — resolve directly from subst.
            if p.segments.len() == 1 && p.segments[0].generics.is_empty() {
                if let Some(replacement) = subst.get(&p.segments[0].name) {
                    return replacement.clone();
                }
            }
            // Generic-struct/enum path: resolve generic args under subst,
            // then look up the mangled instantiation.
            let generics = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
            if !generics.is_empty() {
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                if let Some(full) = sc.names.canon(&segs, sc.module, &[]) {
                    if let (GC_BUF, [elem]) = (full.as_str(), generics) {
                        return HirTy::GcBuf(Box::new(rec(elem)));
                    }
                    let args: Vec<HirTy> = generics.iter().map(rec).collect();
                    let mangled = mangle_inst(&full, &args);
                    if let Some(id) = struct_table.get(&mangled) {
                        return HirTy::Struct(*id);
                    }
                    if let Some(id) = enum_table.get(&mangled) {
                        return HirTy::Enum(*id);
                    }
                }
            }
            // Fall back to the regular resolver, then post-substitute
            // any leaked type-param paths.
            let mut t = resolve_ty_with_structs(ty, struct_table, enum_table, sc);
            substitute_aliases(&mut t, subst);
            t
        }
        rokc_ast::TyKind::Sum(parts) => HirTy::Sum(parts.iter().map(rec).collect()),
        rokc_ast::TyKind::Tuple(parts) if parts.is_empty() => HirTy::Unit,
        rokc_ast::TyKind::Tuple(parts) => HirTy::Tuple(parts.iter().map(rec).collect()),
        rokc_ast::TyKind::Array(elem, _) => {
            match resolve_ty_with_structs(ty, struct_table, enum_table, sc) {
                HirTy::Array(_, n) => HirTy::Array(Box::new(rec(elem)), n),
                other => other,
            }
        }
        rokc_ast::TyKind::Fn(args, ret, b) => HirTy::Fn(
            args.iter().map(rec).collect(),
            Box::new(rec(ret)),
            sc.names.fn_bounds(b, sc.module),
        ),
        rokc_ast::TyKind::Throws { ok, err } => crate::ty::throws_ty(rec(ok), rec(err)),
        _ => {
            let mut t = resolve_ty_with_structs(ty, struct_table, enum_table, sc);
            substitute_aliases(&mut t, subst);
            t
        }
    }
}

/// `{T → arg}` for a generic item's type parameters.
pub(super) fn generic_subst(
    generics: &rokc_ast::Generics,
    args: &[HirTy],
) -> HashMap<String, HirTy> {
    let mut subst = HashMap::new();
    for (i, gp) in generics.params.iter().enumerate() {
        if let rokc_ast::GenericParam::Type { name, .. } = gp {
            if let Some(arg) = args.get(i) {
                subst.insert(name.clone(), arg.clone());
            }
        }
    }
    subst
}

/// Field list of a generic struct instantiated with `args`.
/// `res` resolves a field type under the instantiation's substitution.
pub(super) fn generic_struct_fields(
    def: &AstStructDef,
    res: &dyn Fn(&Ty) -> HirTy,
) -> Vec<HirField> {
    let field = |name: String, ty: &Ty, default: Option<Expr>| HirField {
        name,
        ty: res(ty),
        default,
    };
    match &def.kind {
        AstStructKind::Named(fs) => fs
            .iter()
            .map(|f| field(f.name.clone(), &f.ty, f.default.clone()))
            .collect(),
        AstStructKind::Tuple(fs) => fs
            .iter()
            .enumerate()
            .map(|(i, f)| field(i.to_string(), &f.ty, None))
            .collect(),
        AstStructKind::Unit => Vec::new(),
    }
}

/// Generic items are left to lazy instantiation: their type uses name
/// type parameters, which must not resolve as same-named visible types
/// (a user `enum E` vs `impl<T, E> Result<T, E>`).
fn declares_type_params(item: &Item) -> bool {
    match item {
        Item::Fn(f) => !f.generics.params.is_empty(),
        Item::Impl(i) => !i.generics.params.is_empty(),
        Item::Struct(s) => !s.generics.params.is_empty(),
        Item::Enum(e) => !e.generics.params.is_empty(),
        // Method signatures name `Self` / associated types (`Map<Self,
        // Item, U>`): never a concrete instantiation.
        Item::Trait(_) => true,
        _ => false,
    }
}

/// Same as `instantiate_generic_structs` but for `enum Maybe<T>` etc.
pub(super) fn instantiate_generic_enums(
    program: &Program,
    generic_enums: &HashMap<String, &AstEnumDef>,
    struct_table: &HashMap<String, StructId>,
    enum_table: &mut HashMap<String, EnumId>,
    enum_defs: &mut Vec<HirEnumDef>,
    names: &TypeNames<'_>,
) {
    if generic_enums.is_empty() {
        return;
    }
    for _ in 0..8 {
        let before = enum_table.len();
        for item in program.items.iter().filter(|i| !declares_type_params(i)) {
            let module = item_module(item);
            let sc = Scope {
                names,
                module: &module,
            };
            crate::walk::for_each_ty(item, &mut |ty| {
                visit_ty_for_enum_mono(ty, generic_enums, struct_table, enum_table, enum_defs, sc);
            });
        }
        if enum_table.len() == before {
            break;
        }
    }
}

/// Canonical generic base + resolved args for a `Base<A, ...>` type path,
/// when every arg is concrete (no unresolved type parameter).
pub(super) fn generic_use<'t, V>(
    ty: &rokc_ast::Ty,
    generic_defs: &'t HashMap<String, V>,
    struct_table: &HashMap<String, StructId>,
    enum_table: &HashMap<String, EnumId>,
    sc: Scope<'_>,
) -> Option<(String, &'t V, Vec<HirTy>)> {
    let rokc_ast::TyKind::Path(p) = &ty.kind else {
        return None;
    };
    let last = p.segments.last()?;
    if last.generics.is_empty() {
        return None;
    }
    let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
    let full = sc.names.canon(&segs, sc.module, &[])?;
    let def = generic_defs.get(&full)?;
    let args: Vec<HirTy> = last
        .generics
        .iter()
        .map(|t| resolve_ty_with_structs(t, struct_table, enum_table, sc))
        .collect();
    let mut leftover = Vec::new();
    for a in &args {
        collect_unknown_paths(a, &mut leftover);
    }
    if !leftover.is_empty() {
        return None;
    }
    Some((full, def, args))
}

pub(super) fn visit_ty_for_enum_mono(
    ty: &rokc_ast::Ty,
    generic_enums: &HashMap<String, &AstEnumDef>,
    struct_table: &HashMap<String, StructId>,
    enum_table: &mut HashMap<String, EnumId>,
    enum_defs: &mut Vec<HirEnumDef>,
    sc: Scope<'_>,
) {
    let Some((full, def, arg_tys)) = generic_use(ty, generic_enums, struct_table, enum_table, sc)
    else {
        return;
    };
    let mangled = mangle_inst(&full, &arg_tys);
    if enum_table.contains_key(&mangled) {
        return;
    }
    let id = EnumId(u32::try_from(enum_defs.len()).expect("EnumId overflow"));
    enum_table.insert(mangled.clone(), id);
    let subst = generic_subst(&def.generics, &arg_tys);
    let variants = generic_enum_variants(def, &|t| {
        resolve_ast_with_subst(t, struct_table, enum_table, &subst, sc)
    });
    enum_defs.push(HirEnumDef {
        id,
        def_id: None,
        name: mangled,
        variants,
        span: def.span,
        generic_args: arg_tys,
    });
}

/// Variants of a generic enum instantiation; `res` resolves a payload
/// type under the instantiation's substitution.
pub(super) fn generic_enum_variants(
    def: &AstEnumDef,
    res: &dyn Fn(&Ty) -> HirTy,
) -> Vec<HirEnumVariant> {
    def.variants
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let tag = u32::try_from(i).expect("variant index overflow");
            let (payload_ty, named_fields, arity) = match &v.kind {
                rokc_ast::EnumVariantKind::Unit | rokc_ast::EnumVariantKind::Value(_) => {
                    (None, Vec::new(), 0)
                }
                rokc_ast::EnumVariantKind::Tuple(tys) if tys.len() == 1 => {
                    (Some(res(&tys[0])), Vec::new(), 1)
                }
                rokc_ast::EnumVariantKind::Tuple(tys) => (
                    Some(HirTy::Tuple(tys.iter().map(res).collect())),
                    Vec::new(),
                    tys.len(),
                ),
                rokc_ast::EnumVariantKind::Named(fields) => (
                    Some(HirTy::Tuple(fields.iter().map(|f| res(&f.ty)).collect())),
                    fields.iter().map(|f| f.name.clone()).collect(),
                    fields.len(),
                ),
            };
            HirEnumVariant {
                name: v.name.clone(),
                tag,
                payload_ty,
                named_fields,
                arity,
            }
        })
        .collect()
}

/// Eager pre-pass over the program AST that finds every generic-struct
/// type usage (`Path("Pair", [T])`) and registers a fresh concrete
/// `HirStructDef` per unique substitution. The instantiation name is
/// mangled (`Pair__i32`) so subsequent type resolution treats it as
/// just another concrete struct.
pub(super) fn instantiate_generic_structs(
    program: &Program,
    generic_structs: &HashMap<String, &AstStructDef>,
    struct_table: &mut HashMap<String, StructId>,
    struct_defs: &mut Vec<HirStructDef>,
    enum_table: &HashMap<String, EnumId>,
    names: &TypeNames<'_>,
) {
    if generic_structs.is_empty() {
        return;
    }
    // Iterate to a fixpoint: instantiations themselves can reference
    // other generic structs.
    for _ in 0..8 {
        let before = struct_table.len();
        for item in program.items.iter().filter(|i| !declares_type_params(i)) {
            let module = item_module(item);
            let sc = Scope {
                names,
                module: &module,
            };
            crate::walk::for_each_ty(item, &mut |ty| {
                let Some((full, def, args)) =
                    generic_use(ty, generic_structs, struct_table, enum_table, sc)
                else {
                    return;
                };
                let mangled = mangle_inst(&full, &args);
                if struct_table.contains_key(&mangled) {
                    return;
                }
                // Reserve the id first so a self-reference inside the
                // fields resolves to itself rather than recursing.
                let id = StructId(u32::try_from(struct_defs.len()).expect("StructId overflow"));
                struct_table.insert(mangled.clone(), id);
                let subst = generic_subst(&def.generics, &args);
                let fields = generic_struct_fields(def, &|t| {
                    resolve_ast_with_subst(t, struct_table, enum_table, &subst, sc)
                });
                struct_defs.push(HirStructDef {
                    id,
                    def_id: None,
                    name: mangled,
                    fields,
                    span: def.span,
                    generic_args: args,
                    union_kind: None,
                });
            });
        }
        // Generic structs an instance's fields name under its own
        // arguments (`Dict<i32, i32>` → `DictSlots<i32, i32>`).
        let mut i = 0;
        while i < struct_defs.len() {
            let inst = &struct_defs[i];
            i += 1;
            let base = inst.name.split("__").next().unwrap_or_default().to_owned();
            let Some(def) = generic_structs.get(&base).copied() else {
                continue;
            };
            if inst.generic_args.is_empty() {
                continue;
            }
            let subst = generic_subst(&def.generics, &inst.generic_args);
            let module = module_of(&base);
            let sc = Scope {
                names,
                module: &module,
            };
            let mut nested = Vec::new();
            for f in struct_field_asts(def) {
                generic_paths(f, &mut nested);
            }
            for t in nested {
                let rokc_ast::TyKind::Path(p) = &t.kind else {
                    continue;
                };
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                let Some(full) = names.canon(&segs, &module, &[]) else {
                    continue;
                };
                let Some(inner) = generic_structs.get(&full).copied() else {
                    continue;
                };
                let generics = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
                let args: Vec<HirTy> = generics
                    .iter()
                    .map(|g| resolve_ast_with_subst(g, struct_table, enum_table, &subst, sc))
                    .collect();
                let mut leftover = Vec::new();
                args.iter()
                    .for_each(|a| collect_unknown_paths(a, &mut leftover));
                let mangled = mangle_inst(&full, &args);
                if !leftover.is_empty() || struct_table.contains_key(&mangled) {
                    continue;
                }
                let id = StructId(u32::try_from(struct_defs.len()).expect("StructId overflow"));
                struct_table.insert(mangled.clone(), id);
                let inner_subst = generic_subst(&inner.generics, &args);
                let fields = generic_struct_fields(inner, &|t| {
                    resolve_ast_with_subst(t, struct_table, enum_table, &inner_subst, sc)
                });
                struct_defs.push(HirStructDef {
                    id,
                    def_id: None,
                    name: mangled,
                    fields,
                    span: inner.span,
                    generic_args: args,
                    union_kind: None,
                });
            }
        }
        if struct_table.len() == before {
            break;
        }
    }
    // Re-resolve every instance's fields now that the instances they
    // name exist.
    for inst in struct_defs.iter_mut() {
        let base = inst.name.split("__").next().unwrap_or_default().to_owned();
        let Some(def) = generic_structs.get(&base).copied() else {
            continue;
        };
        if inst.generic_args.is_empty() {
            continue;
        }
        let subst = generic_subst(&def.generics, &inst.generic_args);
        let module = module_of(&base);
        let sc = Scope {
            names,
            module: &module,
        };
        let fields = generic_struct_fields(def, &|t| {
            resolve_ast_with_subst(t, struct_table, enum_table, &subst, sc)
        });
        inst.fields = fields;
    }
}

/// The AST types of a struct's fields.
fn struct_field_asts(def: &AstStructDef) -> Vec<&Ty> {
    match &def.kind {
        AstStructKind::Named(fs) => fs.iter().map(|f| &f.ty).collect(),
        AstStructKind::Tuple(fs) => fs.iter().map(|f| &f.ty).collect(),
        AstStructKind::Unit => Vec::new(),
    }
}

/// Every path-with-generic-arguments inside `ty` (itself included).
fn generic_paths<'t>(ty: &'t Ty, out: &mut Vec<&'t Ty>) {
    match &ty.kind {
        rokc_ast::TyKind::Path(p) => {
            if p.segments.last().is_some_and(|s| !s.generics.is_empty()) {
                out.push(ty);
            }
            for s in &p.segments {
                for g in &s.generics {
                    generic_paths(g, out);
                }
            }
        }
        rokc_ast::TyKind::Sum(ps) | rokc_ast::TyKind::Tuple(ps) => {
            ps.iter().for_each(|p| generic_paths(p, out));
        }
        rokc_ast::TyKind::Array(e, _) => generic_paths(e, out),
        rokc_ast::TyKind::Fn(args, ret, _) => {
            args.iter().for_each(|a| generic_paths(a, out));
            generic_paths(ret, out);
        }
        _ => {}
    }
}

pub(super) fn lower_fn(
    env: &Env<'_>,
    fn_def: &FnDef,
    id: FunctionId,
    method_self_ty: Option<HirTy>,
    module: String,
) -> HirFunction {
    // Methods get a synthetic mangled name so multiple impls of the
    // same method name don't collide as MLIR symbols.
    let name = method_self_ty.as_ref().map_or_else(
        || fn_def.name.clone(),
        |ty| format!("{}__{}", ty_mangle(ty), leaf_name(&fn_def.name)),
    );
    lower_fn_inner(
        env,
        fn_def,
        id,
        name,
        method_self_ty,
        module,
        &HashMap::new(),
    )
}

pub(super) fn lower_param(ctx: &mut LowerCtx<'_>, p: &Param) -> HirParam {
    let ty = if p.name == "self" {
        // Implicit `self` receiver inherits the impl target's type.
        ctx.self_ty.clone().unwrap_or(HirTy::Any)
    } else {
        p.ty.as_ref().map_or(HirTy::Any, |t| ctx.resolve_ast_ty(t))
    };
    let local = ctx.declare(Some(p.name.clone()), ty.clone());
    HirParam {
        name: p.name.clone(),
        local,
        ty,
        by_ref: p.by_ref,
    }
}

/// Lower a function body and check its value against the return type:
/// the trailing expression must match, and a non-unit function without
/// a trailing value must not fall off the end.
pub(super) fn lower_fn_body(ctx: &mut LowerCtx<'_>, b: &Block, fn_name: &str) -> HirBlock {
    ctx.push_expected(ctx.fn_ret_ty.clone());
    if ctx.uncaught_in_main {
        main_frame(ctx);
    }
    let block = lower_block(ctx, b);
    ctx.pop_expected();
    let mut block = check_fn_body(ctx, block, fn_name);
    if ctx.ref_self.is_some() && !hir_block_diverges(&block) {
        let span = b.span;
        let v = block
            .trailing
            .take()
            .unwrap_or_else(|| super::throws::unit_value(span));
        block.trailing = Some(ref_self_pack(ctx, v, span));
    }
    if ctx.uncaught_in_main {
        block = uncaught_in_main(ctx, block, b.span);
    }
    finish_throwing_body(ctx, &mut block);
    block
}

/// The value checks of `lower_fn_body`.
fn check_fn_body(ctx: &LowerCtx<'_>, mut block: HirBlock, fn_name: &str) -> HirBlock {
    let ret = ctx.fn_ret_ty.clone();
    let falls_off = || {
        let name = leaf_name(fn_name);
        if ret == HirTy::Never {
            format!(
                "function `{name}` returns `!` but its body can finish; it must end in a \
                 call of a `-> !` function or a `loop` without `break`"
            )
        } else {
            format!(
                "function `{name}` returns `{}` but its body can finish without returning a \
                 value (missing `return`)",
                ctx.ty_name(&ret)
            )
        }
    };
    match block.trailing.take() {
        // A unit function discards a trailing value (`fn f() { g() }`).
        Some(t) if ret == HirTy::Unit && t.ty != HirTy::Unit => block.stmts.push(HirStmt::Expr(t)),
        Some(t) if hir_expr_diverges(&t) => block.trailing = Some(t),
        // `fn f() -> i32 { if c { return 1; } }`: a unit-valued tail
        // means some path falls off the end.
        Some(t) if t.ty == HirTy::Unit && !matches!(ret, HirTy::Unknown | HirTy::Unit) => {
            ctx.emit_error(rokc_diagnostic::ErrorKind::Type, falls_off());
            block.trailing = Some(t);
        }
        Some(t) => {
            let name = leaf_name(fn_name).to_owned();
            block.trailing = Some(coerce(ctx, &ret, t, &|| format!("the body of `{name}`")));
        }
        None => {
            if !matches!(ret, HirTy::Unit | HirTy::Unknown) && !hir_block_diverges(&block) {
                ctx.emit_error(rokc_diagnostic::ErrorKind::Type, falls_off());
            }
        }
    }
    block
}

/// A `ref self` function's real return type: `(ret, Self)`, or `Self`
/// for a unit `ret`.
pub(super) fn ref_self_packed(ret: &HirTy, self_ty: &HirTy) -> HirTy {
    if *ret == HirTy::Unit {
        self_ty.clone()
    } else {
        HirTy::Tuple(vec![ret.clone(), self_ty.clone()])
    }
}

/// `v` packed with the current `self` (in a `ref self` method).
pub(super) fn ref_self_pack(
    ctx: &LowerCtx<'_>,
    v: HirExpr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let Some((local, self_ty)) = ctx.ref_self.clone() else {
        return v;
    };
    let me = hir_local(local, &self_ty, span);
    if v.ty == HirTy::Unit {
        return HirExpr {
            ty: self_ty,
            kind: HirExprKind::Block(Box::new(HirBlock {
                stmts: vec![HirStmt::Expr(v)],
                trailing: Some(me),
                label: None,
            })),
            span,
        };
    }
    let ty = ref_self_packed(&v.ty, &self_ty);
    HirExpr {
        kind: HirExprKind::Tuple {
            fields: vec![v, me],
        },
        ty,
        span,
    }
}

/// The call of a `ref self` method (`call` returns the packed pair): the
/// final `self` goes back into `place` (a local or a field chain on
/// one), the value comes out.
pub(super) fn ref_self_unpack(
    ctx: &mut LowerCtx<'_>,
    call: HirExpr,
    ret: &HirTy,
    place: Option<&HirExpr>,
) -> HirExpr {
    let span = call.span;
    let packed = call.ty.clone();
    let tmp = ctx.declare(None, packed.clone());
    let field = |i: u32, ty: HirTy| HirExpr {
        kind: HirExprKind::TupleField {
            target: Box::new(hir_local(tmp, &packed, span)),
            index: i,
            field_ty: ty.clone(),
        },
        ty,
        span,
    };
    let unit = *ret == HirTy::Unit;
    let self_ty = match &packed {
        HirTy::Tuple(ts) if !unit => ts[1].clone(),
        t => t.clone(),
    };
    let new_self = if unit {
        hir_local(tmp, &packed, span)
    } else {
        field(1, self_ty)
    };
    let mut stmts = vec![HirStmt::Let {
        local: tmp,
        init: call,
    }];
    if let Some(st) = place.and_then(|p| assign_place(p, new_self)) {
        stmts.push(st);
    }
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing: (!unit).then(|| field(0, ret.clone())),
            label: None,
        })),
        ty: ret.clone(),
        span,
    }
}

/// `place = value` for a local or a field chain on a local.
fn assign_place(place: &HirExpr, value: HirExpr) -> Option<HirStmt> {
    match &place.kind {
        HirExprKind::Local(l) => Some(HirStmt::Assign { local: *l, value }),
        HirExprKind::FieldRead {
            target,
            struct_id,
            field_index,
            ..
        } => {
            let span = value.span;
            let rebuilt = HirExpr {
                kind: HirExprKind::WithField {
                    target: target.clone(),
                    struct_id: *struct_id,
                    field_index: *field_index,
                    value: Box::new(value),
                },
                ty: target.ty.clone(),
                span,
            };
            assign_place(target, rebuilt)
        }
        _ => None,
    }
}

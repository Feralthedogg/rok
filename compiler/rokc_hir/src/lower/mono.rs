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
            // as an argument type mismatch at the call site.
            subst
                .entry(p.segments[0].name.clone())
                .or_insert_with(|| arg_ty.clone());
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
        (rokc_ast::TyKind::Tuple(parts), HirTy::Tuple(arg_parts))
        | (rokc_ast::TyKind::Sum(parts), HirTy::Sum(arg_parts)) => {
            for (p, a) in parts.iter().zip(arg_parts.iter()) {
                rec(p, a);
            }
        }
        (
            rokc_ast::TyKind::Fn(args, ret),
            HirTy::Fn(arg_args, arg_ret)
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
        HirTy::Fn(a, r) => a.iter().map(ty_size).sum::<usize>() + ty_size(r),
        HirTy::Closure { args, ret, env } => {
            args.iter().map(ty_size).sum::<usize>() + ty_size(ret) + ty_size(env)
        }
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
    _span: rokc_diagnostic::Span,
) -> Option<(FunctionId, HirTy)> {
    let fn_module = module_of(&fn_def.name);
    // Infer concrete types for each generic param by unifying the AST
    // parameter type ascription against the call's arg type. Walks into
    // arrays, tuples, sums, function types, and closures. The first
    // binding wins; a conflicting later argument is reported by the
    // argument type check at the call site.
    let mut subst: HashMap<String, HirTy> = HashMap::new();
    for (i, arg) in args.iter().enumerate() {
        bind_from_arg(ctx, fn_def, self_ty, i, &arg.ty, &mut subst);
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
                         arguments",
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
    // `impl Bound for T` block.
    for gp in &fn_def.generics.params {
        let rokc_ast::GenericParam::Type {
            name,
            bounds,
            default: _,
        } = gp
        else {
            continue;
        };
        let Some(concrete) = subst.get(name) else {
            continue;
        };
        let Some(target) = method_target_for(concrete) else {
            continue;
        };
        for bound in bounds {
            let rokc_ast::TyKind::Path(p) = &bound.kind else {
                continue;
            };
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            let bound_name = ctx.env.names.trait_key(&segs, &fn_module);
            if !ctx
                .env
                .impl_traits
                .contains(&(target.clone(), bound_name.clone()))
            {
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
    // Pre-cache so a recursive call inside the body finds the in-progress mono.
    ctx.env.sink.mono_cache.borrow_mut().insert(key, new_id);
    // Pre-resolve the return type from AST + subst so a recursive
    // `sum_down(n - 1)` inside the body sees the correct result type.
    let self_hir = self_ty.map(|t| resolve_in_mono(ctx, fn_def, &subst, None, t));
    let preview_ret_ty = match &fn_def.ret_ty {
        Some(t) => resolve_in_mono(ctx, fn_def, &subst, self_hir.clone(), t),
        None => HirTy::Unit,
    };
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

    let ret_ty = match &fn_def.ret_ty {
        Some(t) => ctx.resolve_ast_ty(t),
        None => HirTy::Unit,
    };
    ctx.fn_ret_ty = ret_ty.clone();

    let body = fn_def
        .body
        .as_ref()
        .map(|b| lower_fn_body(&mut ctx, b, &fn_def.name));

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
        rokc_ast::TyKind::Fn(args, ret) => {
            HirTy::Fn(args.iter().map(rec).collect(), Box::new(rec(ret)))
        }
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
        for item in &program.items {
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
        for item in &program.items {
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
        if struct_table.len() == before {
            break;
        }
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
    let ret = ctx.fn_ret_ty.clone();
    ctx.push_expected(ret.clone());
    let mut block = lower_block(ctx, b);
    ctx.pop_expected();
    match block.trailing.take() {
        // A unit function discards a trailing value (`fn f() { g() }`).
        Some(t) if ret == HirTy::Unit && t.ty != HirTy::Unit => block.stmts.push(HirStmt::Expr(t)),
        Some(t) if hir_expr_diverges(&t) => block.trailing = Some(t),
        // `fn f() -> i32 { if c { return 1; } }`: a unit-valued tail
        // means some path falls off the end.
        Some(t) if t.ty == HirTy::Unit && !matches!(ret, HirTy::Unknown | HirTy::Unit) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "function `{}` returns `{}` but its body can finish without \
                     returning a value (missing `return`)",
                    leaf_name(fn_name),
                    ctx.ty_name(&ret)
                ),
            );
            block.trailing = Some(t);
        }
        Some(t) => {
            let name = leaf_name(fn_name).to_owned();
            block.trailing = Some(coerce(ctx, &ret, t, &|| format!("the body of `{name}`")));
        }
        None => {
            if !matches!(ret, HirTy::Unit | HirTy::Unknown) && !hir_block_diverges(&block) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "function `{}` returns `{}` but its body can finish without \
                         returning a value (missing `return`)",
                        leaf_name(fn_name),
                        ctx.ty_name(&ret)
                    ),
                );
            }
        }
    }
    block
}

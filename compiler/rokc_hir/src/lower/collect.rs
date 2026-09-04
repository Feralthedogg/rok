//! Module-level passes: item collection (types, fns, impls, statics),
//! duplicate / trait-impl checks, and the final unresolved-type check.

#[allow(clippy::wildcard_imports)]
use super::*;

/// Best-effort const-folding of a static initializer. Accepts integer
/// and bool literals (with optional unary minus) plus string literals.
/// Returns `None` for non-literal initializers — caller falls back to
/// `ConstVal::Unit` and the codegen emits a zero-init global.
pub(super) fn literal_to_const_val(expr: &Expr, ty: &HirTy) -> Option<ConstVal> {
    use rokc_ast::Literal as L;
    let lit = match &expr.kind {
        ExprKind::Literal(l) => l,
        ExprKind::OpPrefix { op, operand } if op == "-" => {
            // Negate a leading unary minus (`static N: i32 = -1;`).
            if let ExprKind::Literal(L::Int(text)) = &operand.kind {
                let stripped = strip_int_suffix(text.as_str());
                if let Ok(n) = stripped.parse::<i128>() {
                    let prim = match ty {
                        HirTy::Prim(p) => *p,
                        _ => return None,
                    };
                    return Some(ConstVal::Int {
                        value: -n,
                        ty: prim,
                    });
                }
            }
            return None;
        }
        _ => return None,
    };
    match lit {
        L::Int(text) => {
            let stripped = strip_int_suffix(text.as_str());
            let value: i128 = stripped.parse().ok()?;
            let prim = match ty {
                HirTy::Prim(p) => *p,
                _ => return None,
            };
            Some(ConstVal::Int { value, ty: prim })
        }
        L::Bool(b) => Some(ConstVal::Bool(*b)),
        L::Str(s) | L::RawStr(s) => Some(ConstVal::Str(s.clone())),
        L::None => Some(ConstVal::None),
        _ => None,
    }
}

pub(super) fn strip_int_suffix(s: &str) -> &str {
    const SUFFIXES: &[&str] = &[
        "isize", "usize", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
    ];
    for sfx in SUFFIXES {
        if let Some(rest) = s.strip_suffix(sfx) {
            return rest;
        }
    }
    s
}

#[must_use]
#[allow(clippy::cognitive_complexity)] // linear sequence of lowering passes; splitting adds plumbing, not clarity
pub fn lower_full(
    program: &Program,
    prec: &PrecTable,
    uses: &crate::uses::UseTable,
    reexports: &[crate::uses::ReExport],
) -> HirModule {
    // Diagnostics emitted during pre-body passes (impl-target validation
    // etc.) — folded into module.diagnostics once the module exists.
    let mut pre_diags: Vec<rokc_diagnostic::RokDiagnostic> = Vec::new();
    let err = |pre: &mut Vec<rokc_diagnostic::RokDiagnostic>, msg: String| {
        pre.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            msg,
        ));
    };
    // Spec 6.2: `#[derive(...)]` expansion isn't implemented in stage-1.
    // Pass over every item and emit an explicit refusal so users don't
    // get a silent miscompile (`a == b` returning `false` when they
    // expected the auto-derived equality, etc.).
    for item in &program.items {
        let attrs: &[rokc_ast::Attribute] = match item {
            Item::Struct(s) => &s.attrs,
            Item::Enum(e) => &e.attrs,
            Item::Union(u) => &u.attrs,
            _ => continue,
        };
        for a in attrs {
            if a.path.as_slice() == ["derive"] {
                err(
                    &mut pre_diags,
                    "`#[derive(...)]` expansion is not yet implemented; \
                     write the trait impl by hand for now (spec 6.2)"
                        .to_owned(),
                );
            }
        }
    }

    // Pass 0: the type namespace. Every type-like item name (already
    // module-qualified by the driver) goes into one index; a second
    // definition of the same name is an error (and is skipped below so
    // ids stay consistent).
    let mut type_set: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut traits: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut type_vis: HashMap<String, Visibility> = HashMap::new();
    for item in &program.items {
        let (name, vis) = match item {
            Item::Struct(s) => (&s.name, s.vis),
            Item::Enum(e) => (&e.name, e.vis),
            Item::Union(u) => (&u.name, u.vis),
            Item::TypeAlias(a) => (&a.name, a.vis),
            Item::Trait(t) => {
                traits.insert(t.name.clone());
                (&t.name, t.vis)
            }
            _ => continue,
        };
        if type_set.insert(name.clone()) {
            type_vis.insert(name.clone(), vis);
        } else {
            err(
                &mut pre_diags,
                format!("type `{name}` is defined more than once"),
            );
        }
    }
    let mut type_reexports: HashMap<String, String> = HashMap::new();
    for _ in 0..3 {
        for re in reexports {
            if type_set.contains(&re.full_path) || type_reexports.contains_key(&re.full_path) {
                type_reexports.insert(reexport_key(re), re.full_path.clone());
            }
        }
    }
    let names = TypeNames {
        names: type_set,
        traits,
        reexports: type_reexports,
        visibility: type_vis,
        uses,
        diags: std::cell::RefCell::new(Vec::new()),
    };

    // Pass 1a: enums. Generic enums get stashed for lazy instantiation.
    let mut enum_table: HashMap<String, EnumId> = HashMap::new();
    let mut enum_decls: Vec<&AstEnumDef> = Vec::new();
    let mut generic_enums: HashMap<String, &AstEnumDef> = HashMap::new();
    for item in &program.items {
        if let Item::Enum(e) = item {
            if enum_table.contains_key(&e.name) || generic_enums.contains_key(&e.name) {
                continue;
            }
            if !e.generics.params.is_empty() {
                generic_enums.insert(e.name.clone(), e);
                continue;
            }
            let id = EnumId(u32::try_from(enum_decls.len()).expect("EnumId overflow"));
            enum_table.insert(e.name.clone(), id);
            enum_decls.push(e);
        }
    }
    // Pass 1b: structs and unions (one id space; unions after structs).
    // Generic structs are stashed aside and instantiated as type uses
    // surface them.
    let mut struct_table: HashMap<String, StructId> = HashMap::new();
    let mut generic_structs: HashMap<String, &AstStructDef> = HashMap::new();
    let mut struct_decls: Vec<&AstStructDef> = Vec::new();
    for item in &program.items {
        if let Item::Struct(s) = item {
            if struct_table.contains_key(&s.name) || generic_structs.contains_key(&s.name) {
                continue;
            }
            if !s.generics.params.is_empty() {
                generic_structs.insert(s.name.clone(), s);
                continue;
            }
            let id = StructId(u32::try_from(struct_decls.len()).expect("StructId overflow"));
            struct_table.insert(s.name.clone(), id);
            struct_decls.push(s);
        }
    }
    // Spec 2.x / i-want 322-340: `union { ... }` declarations live in
    // the same name space as structs. Register each one in
    // `struct_table` so paths resolve uniformly, and tag the resulting
    // `HirStructDef` with a `union_kind` so init/read sites know to use
    // the bitcast/cast access path instead of the regular field-by-index.
    let mut union_decls: Vec<&rokc_ast::UnionDef> = Vec::new();
    for item in &program.items {
        if let Item::Union(u) = item {
            if struct_table.contains_key(&u.name) || generic_structs.contains_key(&u.name) {
                continue;
            }
            let id = StructId(
                u32::try_from(struct_decls.len() + union_decls.len()).expect("StructId overflow"),
            );
            struct_table.insert(u.name.clone(), id);
            union_decls.push(u);
        }
    }

    let mut enum_defs: Vec<HirEnumDef> = Vec::with_capacity(enum_decls.len());
    for (i, e) in enum_decls.iter().enumerate() {
        let id = EnumId(u32::try_from(i).expect("EnumId overflow"));
        let module = module_of(&e.name);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        enum_defs.push(lower_enum_def(
            e,
            id,
            &struct_table,
            &enum_table,
            sc,
            &mut pre_diags,
        ));
    }
    let mut struct_defs: Vec<HirStructDef> =
        Vec::with_capacity(struct_decls.len() + union_decls.len());
    for (i, s) in struct_decls.iter().enumerate() {
        let id = StructId(u32::try_from(i).expect("StructId overflow"));
        let module = module_of(&s.name);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        struct_defs.push(lower_struct_def(s, id, &struct_table, &enum_table, sc));
    }
    for (i, u) in union_decls.iter().enumerate() {
        let id = StructId(u32::try_from(struct_decls.len() + i).expect("StructId overflow"));
        let module = module_of(&u.name);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        struct_defs.push(lower_union_def(
            u,
            id,
            &struct_table,
            &enum_table,
            sc,
            &mut pre_diags,
        ));
    }
    // Pass 1b.1: walk the program collecting every generic-struct
    // instantiation (`Path("Pair", [T...])`) and materialize a fresh
    // `HirStructDef` for each unique substitution.
    instantiate_generic_structs(
        program,
        &generic_structs,
        &mut struct_table,
        &mut struct_defs,
        &enum_table,
        &names,
    );
    // Pass 1b.2: same idea for generic enums.
    instantiate_generic_enums(
        program,
        &generic_enums,
        &struct_table,
        &mut enum_table,
        &mut enum_defs,
        &names,
    );

    // Pass 1c: collect module-level `const` items. Their value
    // expressions are stored as AST and inlined at each use site.
    // `static` items follow a different path — they get stable global
    // storage (`HirStaticDef`) and reads/writes go through addressof
    // + load/store at codegen time.
    let mut consts: HashMap<String, (Ty, Expr)> = HashMap::new();
    for item in &program.items {
        if let Item::Const(c) = item {
            if consts
                .insert(c.name.clone(), (c.ty.clone(), c.value.clone()))
                .is_some()
            {
                err(
                    &mut pre_diags,
                    format!("const `{}` is defined more than once", c.name),
                );
            }
        }
    }
    let mut static_defs: Vec<HirStaticDef> = Vec::new();
    let mut static_tys: HashMap<String, HirTy> = HashMap::new();
    for item in &program.items {
        if let Item::Static(s) = item {
            if static_tys.contains_key(&s.name) {
                err(
                    &mut pre_diags,
                    format!("static `{}` is defined more than once", s.name),
                );
                continue;
            }
            let module = module_of(&s.name);
            let sc = Scope {
                names: &names,
                module: &module,
            };
            let ty = resolve_ty_with_structs(&s.ty, &struct_table, &enum_table, sc);
            // Stage-1: the initializer must const-fold to a literal. A
            // non-literal used to zero-initialize the global silently.
            let init = match s.value.as_ref() {
                Some(v) => literal_to_const_val(v, &ty).unwrap_or_else(|| {
                    err(
                        &mut pre_diags,
                        format!(
                            "static `{}` initializer must be a literal constant \
                             (stage-1 limitation)",
                            s.name
                        ),
                    );
                    ConstVal::Unit
                }),
                None => ConstVal::Unit,
            };
            static_tys.insert(s.name.clone(), ty.clone());
            static_defs.push(HirStaticDef {
                name: s.name.clone(),
                ty,
                init,
                is_mut: s.is_mut,
                span: s.span,
            });
        }
    }
    // Pass 1d: collect type aliases. Names resolve to the aliased type
    // wherever a `Path` appears in a type position. We do a post-pass
    // expansion so the alias table can refer to other aliases.
    let mut type_aliases: HashMap<String, HirTy> = HashMap::new();
    for item in &program.items {
        if let Item::TypeAlias(a) = item {
            let module = module_of(&a.name);
            let sc = Scope {
                names: &names,
                module: &module,
            };
            let resolved = resolve_ty_with_structs(&a.ty, &struct_table, &enum_table, sc);
            type_aliases.entry(a.name.clone()).or_insert(resolved);
        }
    }
    // Substitute alias references inside aliases up to a small fixed
    // depth — direct cycles flatten harmlessly.
    for _ in 0..4 {
        let snapshot = type_aliases.clone();
        for v in type_aliases.values_mut() {
            substitute_aliases(v, &snapshot);
        }
    }
    // Spec 2.x: an alias that still mentions an alias after expansion is
    // cyclic (`type A = B; type B = A;`) and has no meaning.
    {
        let mut cyclic: Vec<&String> = type_aliases
            .iter()
            .filter(|(_, v)| ty_mentions_any(v, &type_aliases))
            .map(|(k, _)| k)
            .collect();
        cyclic.sort();
        for k in cyclic {
            err(&mut pre_diags, format!("type alias `{k}` is cyclic"));
        }
    }
    // Substitute aliases inside struct field types so the rest of the
    // pipeline never sees `Path(["Maybe"])`.
    for s in &mut struct_defs {
        for f in &mut s.fields {
            substitute_aliases(&mut f.ty, &type_aliases);
        }
    }
    for e in &mut enum_defs {
        for v in &mut e.variants {
            if let Some(t) = v.payload_ty.as_mut() {
                substitute_aliases(t, &type_aliases);
            }
        }
    }

    // A struct that contains itself by value (directly or through
    // tuples / arrays / sums / other structs) has no finite size.
    for (i, sd) in struct_defs.iter().enumerate() {
        let me = StructId(u32::try_from(i).expect("StructId overflow"));
        let mut stack: Vec<HirTy> = sd.fields.iter().map(|f| f.ty.clone()).collect();
        let mut seen: std::collections::HashSet<StructId> = std::collections::HashSet::new();
        while let Some(t) = stack.pop() {
            match t {
                HirTy::Struct(id) if id == me => {
                    err(
                        &mut pre_diags,
                        format!(
                            "recursive type `{}` has infinite size (a struct can't contain \
                             itself by value)",
                            sd.name
                        ),
                    );
                    break;
                }
                HirTy::Struct(id) => {
                    if seen.insert(id) {
                        if let Some(d) = struct_defs.get(id.0 as usize) {
                            stack.extend(d.fields.iter().map(|f| f.ty.clone()));
                        }
                    }
                }
                HirTy::Tuple(ps) | HirTy::Sum(ps) => stack.extend(ps),
                HirTy::Array(e, _) => stack.push(*e),
                _ => {}
            }
        }
    }

    // Pass 2: collect every function-like declaration. Free functions
    // first, then `impl` methods (each method becomes a synthetic free
    // function `Type::method` with `self` as its first parameter).
    // Generic functions don't get a single concrete signature — they
    // monomorphize per-call. We stash the AST aside instead of putting
    // them in `decls` / `fn_table`.
    let mut fn_table: HashMap<String, FnSig> = HashMap::new();
    let mut method_table: HashMap<(MethodTarget, String), FunctionId> = HashMap::new();
    let mut method_info: HashMap<FunctionId, MethodInfo> = HashMap::new();
    // Records `(Type, TraitName)` for each `impl Trait for Type` block
    // — feeds the generic-bound check at monomorphization time.
    let mut impl_traits: std::collections::HashSet<(MethodTarget, String)> =
        std::collections::HashSet::new();
    let mut decls: Vec<MethodOrFn<'_>> = Vec::new();
    let mut generic_fns: HashMap<String, &FnDef> = HashMap::new();
    let mut generic_methods: HashMap<(String, String), GenericMethod> = HashMap::new();
    let sig_of = |fn_def: &FnDef, id: FunctionId, self_ty: Option<&HirTy>, sc: Scope<'_>| {
        let resolve = |t: &Ty| {
            let mut r = resolve_ty_with_structs(t, &struct_table, &enum_table, sc);
            if let Some(st) = self_ty {
                substitute_aliases(&mut r, &HashMap::from([("Self".to_owned(), st.clone())]));
            }
            r
        };
        FnSig {
            id,
            ret_ty: fn_def.ret_ty.as_ref().map_or(HirTy::Unit, resolve),
            param_defaults: fn_def.params.iter().map(|p| p.default.clone()).collect(),
            param_tys: fn_def
                .params
                .iter()
                .map(|p| match (self_ty, p.name.as_str(), &p.ty) {
                    (Some(st), "self", _) => st.clone(),
                    (_, _, Some(t)) => resolve(t),
                    (_, _, None) => HirTy::Any,
                })
                .collect(),
            param_names: fn_def.params.iter().map(|p| p.name.clone()).collect(),
        }
    };
    for item in &program.items {
        match item {
            Item::Fn(fn_def) => {
                if fn_table.contains_key(&fn_def.name) || generic_fns.contains_key(&fn_def.name) {
                    err(
                        &mut pre_diags,
                        format!("function `{}` is defined more than once", fn_def.name),
                    );
                    continue;
                }
                if !fn_def.generics.params.is_empty() {
                    generic_fns.insert(fn_def.name.clone(), fn_def);
                    continue;
                }
                // Spec 4.1 / 변경점 833: `xs: ...T` variadic. Stage-1
                // call-site lowering doesn't yet wrap trailing args into
                // a Slice<T>, so any call would fail with arity mismatch
                // at codegen — emit an explicit refusal up front.
                if fn_def.params.iter().any(|p| p.variadic) {
                    err(
                        &mut pre_diags,
                        format!(
                            "function `{}` has a `...T` variadic parameter; \
                             call-site slicing isn't implemented yet \
                             (spec 4.1 — stage-1 limitation)",
                            fn_def.name
                        ),
                    );
                }
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let module = module_of(&fn_def.name);
                let sc = Scope {
                    names: &names,
                    module: &module,
                };
                fn_table.insert(fn_def.name.clone(), sig_of(fn_def, id, None, sc));
                decls.push(MethodOrFn::Fn(fn_def));
            }
            Item::Extern(blk) => {
                for ei in &blk.items {
                    let rokc_ast::ExternItem::Fn(fn_def) = ei else {
                        continue;
                    };
                    // A repeated extern declaration names the same symbol;
                    // keep the first.
                    if fn_table.contains_key(&fn_def.name) {
                        continue;
                    }
                    let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                    let sc = Scope {
                        names: &names,
                        module: "",
                    };
                    fn_table.insert(fn_def.name.clone(), sig_of(fn_def, id, None, sc));
                    decls.push(MethodOrFn::Fn(fn_def));
                }
            }
            _ => {}
        }
    }
    // Pre-collect every trait declaration so `impl Trait for T` blocks
    // can pick up default method bodies.
    let mut trait_defs: HashMap<String, &rokc_ast::TraitDef> = HashMap::new();
    for item in &program.items {
        if let Item::Trait(t) = item {
            trait_defs.entry(t.name.clone()).or_insert(t);
        }
    }

    for item in &program.items {
        let Item::Impl(impl_def) = item else { continue };
        let module = impl_module(impl_def);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        let impl_generic = !impl_def.generics.params.is_empty();
        if let (true, Some(tp)) = (impl_generic, &impl_def.trait_path) {
            // ponytail: generic trait impls need per-instantiation
            // `impl_traits` entries and trait-method dispatch through
            // `generic_methods`; add when the stdlib needs one.
            let tr: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
            err(
                &mut pre_diags,
                format!(
                    "generic trait impl `impl<..> {} for {}` is not implemented yet \
                     (stage-1 limitation — only inherent generic impls are supported)",
                    tr.join("::"),
                    impl_def_display(&impl_def.self_ty)
                ),
            );
            continue;
        }
        // Inherent methods of a generic impl (and generic methods of a
        // plain one) are templates keyed by the target's generic base.
        let generic_base = match &impl_def.self_ty.kind {
            AstTyKind::Path(p) if impl_def.trait_path.is_none() => {
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                names.canon(&segs, &module, &[])
            }
            _ => None,
        };
        if impl_generic && generic_base.is_none() {
            err(
                &mut pre_diags,
                format!(
                    "generic impl target `{}` must be a struct or enum (stage-1 limitation)",
                    impl_def_display(&impl_def.self_ty)
                ),
            );
            continue;
        }
        let target_ty = resolve_ty_with_structs(&impl_def.self_ty, &struct_table, &enum_table, sc);
        let target = method_target_for(&target_ty);
        // Resolve the trait (a user trait resolves to its qualified name;
        // a bootstrap trait like `core::ops::Add` keeps its last segment).
        let trait_name: Option<String> = impl_def.trait_path.as_ref().map(|tp| {
            let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
            names.trait_key(&segs, &module)
        });
        if let (Some(tn), Some(target_key)) = (&trait_name, target.clone()) {
            impl_traits.insert((target_key, tn.clone()));
        }
        let trait_def = trait_name
            .as_ref()
            .and_then(|tn| trait_defs.get(tn).copied());
        let target_display = impl_def_display(&impl_def.self_ty);
        // Names of methods this impl block explicitly provides —
        // used below to avoid double-registering a default that's
        // overridden here.
        let mut explicit_methods: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        for ii in &impl_def.items {
            let m = match ii {
                AstImplItem::Method(m) => m,
                AstImplItem::Const(c) => {
                    err(
                        &mut pre_diags,
                        format!(
                            "associated const `{}` in impl blocks is not implemented yet \
                             (stage-1 limitation)",
                            c.name
                        ),
                    );
                    continue;
                }
                AstImplItem::AssocType { .. } => continue,
            };
            let leaf = leaf_name(&m.name).to_owned();
            // Spec 2.9.2: `ref self` means the receiver mutates the
            // caller's binding. Pointer-typed receivers aren't yet
            // wired through codegen, so the body would silently
            // mutate a copy — reject explicitly to block the silent
            // miscompile until ref semantics land.
            if let Some(first) = m.params.first() {
                if first.name == "self" && first.by_ref {
                    err(
                        &mut pre_diags,
                        format!(
                            "method `{leaf}` declares `ref self`, but ref-self \
                             semantics aren't implemented yet — mutations \
                             would silently target a copy (spec 2.9.2)"
                        ),
                    );
                }
            }
            if !explicit_methods.insert(leaf.clone()) {
                err(
                    &mut pre_diags,
                    format!("method `{leaf}` is defined more than once for `{target_display}`"),
                );
                continue;
            }
            if let (Some(base), true) =
                (&generic_base, impl_generic || !m.generics.params.is_empty())
            {
                // Impl generics first, then the method's own; `self` and
                // `Self` take the impl target type at instantiation.
                let mut def = m.clone();
                let base_leaf = leaf_name(base);
                // ponytail: `Box__get` doubles as the mono cache key and
                // the name in diagnostics ("cannot infer `U` of
                // `Box__get`"); carry a display name if that reads badly.
                def.name = if module.is_empty() {
                    format!("{base_leaf}__{leaf}")
                } else {
                    format!("{module}::{base_leaf}__{leaf}")
                };
                def.generics.params = [&impl_def.generics.params, &m.generics.params]
                    .into_iter()
                    .flatten()
                    .cloned()
                    .collect();
                def.where_clause = [&impl_def.where_clause, &m.where_clause]
                    .into_iter()
                    .flatten()
                    .cloned()
                    .collect();
                if generic_methods.contains_key(&(base.clone(), leaf.clone())) {
                    err(
                        &mut pre_diags,
                        format!("method `{leaf}` is defined more than once for `{target_display}`"),
                    );
                    continue;
                }
                generic_methods.insert(
                    (base.clone(), leaf),
                    GenericMethod {
                        def,
                        self_ty: impl_def.self_ty.clone(),
                        info: MethodInfo {
                            module: module.clone(),
                            vis: m.vis,
                            trait_name: None,
                        },
                    },
                );
                continue;
            }
            if let Some(td) = trait_def {
                let in_trait = td
                    .items
                    .iter()
                    .any(|ti| matches!(ti, rokc_ast::TraitItem::Method(tm) if tm.name == leaf));
                if !in_trait {
                    err(
                        &mut pre_diags,
                        format!("method `{leaf}` is not a member of trait `{}`", td.name),
                    );
                }
            }
            let key = format!("{}__{leaf}", ty_mangle(&target_ty));
            if fn_table.contains_key(&key) {
                err(
                    &mut pre_diags,
                    format!("method `{leaf}` is defined more than once for `{target_display}`"),
                );
                continue;
            }
            let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
            fn_table.insert(key, sig_of(m, id, Some(&target_ty), sc));
            if let Some(t) = target.clone() {
                method_table.insert((t, leaf.clone()), id);
            }
            // Trait-impl methods are as visible as the trait itself;
            // inherent methods carry their own visibility.
            let vis = if trait_name.is_some() {
                Visibility::Pub
            } else {
                m.vis
            };
            method_info.insert(
                id,
                MethodInfo {
                    module: module.clone(),
                    vis,
                    trait_name: trait_name.clone(),
                },
            );
            decls.push(MethodOrFn::Method {
                fn_def: m,
                self_ty: target_ty.clone(),
                module: module.clone(),
            });
        }

        // Pull in default-method bodies from the trait this impl
        // is for, when the impl doesn't override them. Each default
        // gets specialized for `Self = target_ty` by reusing the
        // method-lowering machinery. A required method (no body) that
        // the impl doesn't provide is an error.
        if let Some(trait_def) = trait_def {
            let trait_module = module_of(&trait_def.name);
            for ti in &trait_def.items {
                let rokc_ast::TraitItem::Method(tm) = ti else {
                    continue;
                };
                if explicit_methods.contains(&tm.name) {
                    continue;
                }
                if tm.body.is_none() {
                    err(
                        &mut pre_diags,
                        format!(
                            "impl of trait `{}` for `{target_display}` is missing method `{}`",
                            trait_def.name, tm.name
                        ),
                    );
                    continue;
                }
                let key = format!("{}__{}", ty_mangle(&target_ty), tm.name);
                if fn_table.contains_key(&key) {
                    err(
                        &mut pre_diags,
                        format!(
                            "method `{}` is defined more than once for `{target_display}`",
                            tm.name
                        ),
                    );
                    continue;
                }
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let tsc = Scope {
                    names: &names,
                    module: &trait_module,
                };
                fn_table.insert(key, sig_of(tm, id, Some(&target_ty), tsc));
                if let Some(t) = target.clone() {
                    method_table.insert((t, tm.name.clone()), id);
                }
                method_info.insert(
                    id,
                    MethodInfo {
                        module: trait_module.clone(),
                        vis: Visibility::Pub,
                        trait_name: trait_name.clone(),
                    },
                );
                decls.push(MethodOrFn::Method {
                    fn_def: tm,
                    self_ty: target_ty.clone(),
                    module: trait_module.clone(),
                });
            }
        }
    }

    // Install `pub use` re-exports as fn/static table aliases (types go
    // through `TypeNames`). A fixed-point loop handles re-exports that
    // name another re-export's short form.
    for _ in 0..3 {
        for re in reexports {
            let alias_key = reexport_key(re);
            if let Some(sig) = fn_table.get(&re.full_path).cloned() {
                fn_table.entry(alias_key.clone()).or_insert(sig);
            }
            if let Some(ty) = static_tys.get(&re.full_path).cloned() {
                static_tys.entry(alias_key.clone()).or_insert(ty);
            }
        }
    }

    // Substitute aliases in collected fn signatures before lowering
    // bodies so `wrap_into_sum` and other type-driven decisions see
    // concrete sum / struct / fn types instead of unresolved paths.
    if !type_aliases.is_empty() {
        for sig in fn_table.values_mut() {
            substitute_aliases(&mut sig.ret_ty, &type_aliases);
            for p in &mut sig.param_tys {
                substitute_aliases(p, &type_aliases);
            }
        }
    }

    // Name → Visibility for every value-namespace item (fns, consts,
    // statics) plus type items; consulted by path resolution.
    let mut item_visibility: HashMap<String, Visibility> = HashMap::new();
    for item in &program.items {
        match item {
            Item::Fn(f) => {
                item_visibility.entry(f.name.clone()).or_insert(f.vis);
            }
            Item::Const(c) => {
                item_visibility.entry(c.name.clone()).or_insert(c.vis);
            }
            Item::Static(s) => {
                item_visibility.entry(s.name.clone()).or_insert(s.vis);
            }
            _ => {}
        }
    }
    let field_vis = collect_field_visibility(program);

    // Pass 3: function bodies.
    let sink = ClosureSink {
        extras: std::cell::RefCell::new(Vec::new()),
        next_id: std::cell::Cell::new(u32::try_from(decls.len()).expect("FunctionId overflow")),
        mono_cache: std::cell::RefCell::new(HashMap::new()),
        mono_sigs: std::cell::RefCell::new(HashMap::new()),
        mono_depth: std::cell::Cell::new(0),
        extra_structs: std::cell::RefCell::new(Vec::new()),
        extra_struct_table: std::cell::RefCell::new(HashMap::new()),
        extra_enums: std::cell::RefCell::new(Vec::new()),
        extra_enum_table: std::cell::RefCell::new(HashMap::new()),
        diagnostics: std::cell::RefCell::new(Vec::new()),
    };
    let env = Env {
        fn_table,
        method_table,
        method_info,
        structs: struct_defs,
        enums: enum_defs,
        struct_table,
        enum_table,
        consts,
        type_aliases,
        generic_fns,
        generic_structs,
        generic_enums,
        generic_methods,
        prec,
        sink,
        item_visibility,
        field_vis,
        uses,
        impl_traits,
        statics: static_tys,
        names,
    };
    let mut functions: Vec<HirFunction> = Vec::with_capacity(decls.len());
    for (i, decl) in decls.iter().enumerate() {
        let id = FunctionId(u32::try_from(i).expect("FunctionId overflow"));
        functions.push(match decl {
            MethodOrFn::Fn(fn_def) => lower_fn(&env, fn_def, id, None, module_of(&fn_def.name)),
            MethodOrFn::Method {
                fn_def,
                self_ty,
                module,
            } => lower_fn(&env, fn_def, id, Some(self_ty.clone()), module.clone()),
        });
    }
    let Env {
        structs,
        enums,
        sink,
        type_aliases,
        names,
        ..
    } = env;
    // Append every closure body / monomorphization lifted to a top-level
    // function during expression lowering, and every struct instantiated
    // lazily from a literal (`Box { v: 5 }`).
    functions.extend(sink.extras.into_inner());
    let mut structs = structs;
    structs.extend(sink.extra_structs.into_inner());
    let mut enums = enums;
    enums.extend(sink.extra_enums.into_inner());
    let mut module = HirModule {
        functions,
        structs,
        enums,
        statics: static_defs,
        diagnostics: pre_diags,
    };
    // Final pass: rewrite any leftover `HirTy::Path([alias])` nodes in
    // function signatures and locals using the alias table.
    if !type_aliases.is_empty() {
        for f in &mut module.functions {
            substitute_aliases(&mut f.ret_ty, &type_aliases);
            for p in &mut f.params {
                substitute_aliases(&mut p.ty, &type_aliases);
            }
            for l in &mut f.locals {
                substitute_aliases(&mut l.ty, &type_aliases);
            }
        }
    }
    module.diagnostics.extend(names.diags.into_inner());
    module.diagnostics.extend(sink.diagnostics.into_inner());
    check_unresolved_types(&mut module);
    // The same root cause can be reached from several passes (e.g. a
    // type resolved once per instantiation sweep): report it once.
    let mut seen = std::collections::HashSet::new();
    module
        .diagnostics
        .retain(|d| seen.insert(d.message.clone()));
    module
}

pub(super) fn reexport_key(re: &crate::uses::ReExport) -> String {
    if re.module_path.is_empty() {
        re.short_name.clone()
    } else {
        format!("{}::{}", re.module_path, re.short_name)
    }
}

/// Source-ish rendering of an AST type for diagnostics.
pub(super) fn impl_def_display(ty: &Ty) -> String {
    match &ty.kind {
        AstTyKind::Path(p) => p
            .segments
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>()
            .join("::"),
        _ => "<type>".to_owned(),
    }
}

/// Does `ty` still name any key of `aliases`? (alias-cycle detection)
pub(super) fn ty_mentions_any(ty: &HirTy, aliases: &HashMap<String, HirTy>) -> bool {
    match ty {
        HirTy::Path(p) => p.len() == 1 && aliases.contains_key(&p[0]),
        HirTy::Sum(parts) | HirTy::Tuple(parts) => {
            parts.iter().any(|p| ty_mentions_any(p, aliases))
        }
        HirTy::Array(e, _) => ty_mentions_any(e, aliases),
        HirTy::Fn(a, r)
        | HirTy::Closure {
            args: a, ret: r, ..
        } => a.iter().any(|p| ty_mentions_any(p, aliases)) || ty_mentions_any(r, aliases),
        _ => false,
    }
}

/// `struct name → field name → visibility` from the AST (driver-qualified
/// struct names; generic instantiations look up their base name).
pub(super) fn collect_field_visibility(
    program: &Program,
) -> HashMap<String, HashMap<String, Visibility>> {
    let mut out: HashMap<String, HashMap<String, Visibility>> = HashMap::new();
    for item in &program.items {
        match item {
            Item::Struct(s) => {
                let AstStructKind::Named(fs) = &s.kind else {
                    continue;
                };
                out.entry(s.name.clone())
                    .or_insert_with(|| fs.iter().map(|f| (f.name.clone(), f.vis)).collect());
            }
            Item::Union(u) => {
                out.entry(u.name.clone())
                    .or_insert_with(|| u.fields.iter().map(|f| (f.name.clone(), f.vis)).collect());
            }
            _ => {}
        }
    }
    out
}

/// Safety net: no expression or binding may leave lowering with an
/// unresolved type unless an error was already reported. A leftover
/// `HirTy::Path` is an unknown type name; a leftover `Unknown` /
/// `UnresolvedPath` means some lowering path fell through silently —
/// refuse to hand that to MIR (it would be lowered as unit / `any`).
pub(super) fn check_unresolved_types(module: &mut HirModule) {
    let mut unknown_types: Vec<String> = Vec::new();
    let mut note = |ty: &HirTy| collect_unknown_paths(ty, &mut unknown_types);
    for s in &module.structs {
        for f in &s.fields {
            note(&f.ty);
        }
    }
    for e in &module.enums {
        for v in &e.variants {
            if let Some(t) = &v.payload_ty {
                note(t);
            }
        }
    }
    for st in &module.statics {
        note(&st.ty);
    }
    for f in &module.functions {
        note(&f.ret_ty);
        for p in &f.params {
            note(&p.ty);
        }
        for l in &f.locals {
            note(&l.ty);
        }
    }
    unknown_types.sort();
    unknown_types.dedup();
    for t in unknown_types {
        module
            .diagnostics
            .push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                format!("cannot find type `{t}` in this scope"),
            ));
    }
    if module
        .diagnostics
        .iter()
        .any(rokc_diagnostic::RokDiagnostic::is_error)
    {
        return;
    }
    let mut bad: Option<String> = None;
    for f in &module.functions {
        if f.params.iter().any(|p| p.ty == HirTy::Unknown)
            || f.locals.iter().any(|l| l.ty == HirTy::Unknown)
            || f.body.as_ref().is_some_and(hir_block_has_unknown)
        {
            bad = Some(f.name.clone());
            break;
        }
    }
    if let Some(name) = bad {
        module
            .diagnostics
            .push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "internal compiler error: an expression in `{name}` has no resolved type \
                 (lowering fell through without a diagnostic) — please report"
                ),
            ));
    }
}

pub(super) fn collect_unknown_paths(ty: &HirTy, out: &mut Vec<String>) {
    match ty {
        HirTy::Path(p) if p.as_slice() != ["none"] => out.push(p.join("::")),
        HirTy::Sum(parts) | HirTy::Tuple(parts) => {
            for p in parts {
                collect_unknown_paths(p, out);
            }
        }
        HirTy::Array(e, _) => collect_unknown_paths(e, out),
        HirTy::Fn(a, r)
        | HirTy::Closure {
            args: a, ret: r, ..
        } => {
            for p in a {
                collect_unknown_paths(p, out);
            }
            collect_unknown_paths(r, out);
        }
        _ => {}
    }
}

pub(super) fn hir_block_has_unknown(b: &HirBlock) -> bool {
    b.stmts.iter().any(|s| match s {
        HirStmt::Let { init: e, .. }
        | HirStmt::Assign { value: e, .. }
        | HirStmt::StaticAssign { value: e, .. }
        | HirStmt::Expr(e)
        | HirStmt::Throw(e)
        | HirStmt::Return(Some(e))
        | HirStmt::Break { value: Some(e), .. } => hir_expr_has_unknown(e),
        HirStmt::ArrayAssign { index, value, .. } => {
            hir_expr_has_unknown(index) || hir_expr_has_unknown(value)
        }
        HirStmt::Return(None) | HirStmt::Break { value: None, .. } | HirStmt::Continue { .. } => {
            false
        }
    }) || b.trailing.as_ref().is_some_and(hir_expr_has_unknown)
}

pub(super) fn hir_expr_has_unknown(e: &HirExpr) -> bool {
    use HirExprKind as K;
    if e.ty == HirTy::Unknown {
        return true;
    }
    let any = |es: &[HirExpr]| es.iter().any(hir_expr_has_unknown);
    match &e.kind {
        K::UnresolvedPath(_) => true,
        K::Const(_) | K::Local(_) | K::StaticRef(_) | K::FnRef(_) => false,
        K::Block(b) => hir_block_has_unknown(b),
        K::PrimBinOp { lhs, rhs, .. } => hir_expr_has_unknown(lhs) || hir_expr_has_unknown(rhs),
        K::PrimUnaryOp { operand, .. } | K::Cast { operand, .. } => hir_expr_has_unknown(operand),
        K::Call { args, .. } | K::EnumVariantInit { args, .. } => any(args),
        K::CallIndirect { callee, args, .. } => hir_expr_has_unknown(callee) || any(args),
        K::ClosureValue { env, .. } => hir_expr_has_unknown(env),
        K::CallClosure { closure, args, .. } => hir_expr_has_unknown(closure) || any(args),
        K::If {
            cond,
            then_block,
            else_branch,
        } => {
            hir_expr_has_unknown(cond)
                || hir_block_has_unknown(then_block)
                || else_branch.as_deref().is_some_and(hir_expr_has_unknown)
        }
        K::While { cond, body, .. } => hir_expr_has_unknown(cond) || hir_block_has_unknown(body),
        K::Loop { body, .. } => hir_block_has_unknown(body),
        K::Match { scrutinee, arms } => {
            hir_expr_has_unknown(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(hir_expr_has_unknown)
                        || hir_expr_has_unknown(&a.body)
                })
        }
        K::StructInit { fields, .. } | K::Tuple { fields } => any(fields),
        K::FieldRead { target, .. }
        | K::TupleField { target, .. }
        | K::UnionRead { target, .. } => hir_expr_has_unknown(target),
        K::WithField { target, value, .. } => {
            hir_expr_has_unknown(target) || hir_expr_has_unknown(value)
        }
        K::SumWrap { value, .. } => value.as_deref().is_some_and(hir_expr_has_unknown),
        K::ArrayInit { elements, .. } => any(elements),
        K::ArrayIndex { array, index, .. } => {
            hir_expr_has_unknown(array) || hir_expr_has_unknown(index)
        }
        K::UnionWrite { value, .. } => hir_expr_has_unknown(value),
    }
}

pub(super) fn lower_enum_def(
    e: &AstEnumDef,
    id: EnumId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    sc: Scope<'_>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> HirEnumDef {
    let variants = e
        .variants
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let tag = u32::try_from(i).expect("variant index overflow");
            match &v.kind {
                AstEnumVariantKind::Unit => HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: None,
                    named_fields: Vec::new(),
                    arity: 0,
                },
                // Single-element tuple — store the payload type directly.
                AstEnumVariantKind::Tuple(tys) if tys.len() == 1 => HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(resolve_ty_with_structs(&tys[0], structs, enums, sc)),
                    named_fields: Vec::new(),
                    arity: 1,
                },
                // Multi-element tuple — pack into a tuple payload type.
                AstEnumVariantKind::Tuple(tys) => HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(HirTy::Tuple(
                        tys.iter()
                            .map(|t| resolve_ty_with_structs(t, structs, enums, sc))
                            .collect(),
                    )),
                    named_fields: Vec::new(),
                    arity: tys.len(),
                },
                // Named-form variant `Move { x: i32; y: i32; }` — pack
                // into a tuple payload by declaration order, recording
                // the field names so initialiser/pattern lowering can
                // map name → tuple index. Spec 2.4.
                AstEnumVariantKind::Named(fields) => HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(HirTy::Tuple(
                        fields
                            .iter()
                            .map(|f| resolve_ty_with_structs(&f.ty, structs, enums, sc))
                            .collect(),
                    )),
                    named_fields: fields.iter().map(|f| f.name.clone()).collect(),
                    arity: fields.len(),
                },
                // Dropping the variant would shift every later tag.
                AstEnumVariantKind::Value(_) => {
                    pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "explicit discriminant on enum variant `{}::{}` is not \
                             implemented yet (stage-1 limitation)",
                            e.name, v.name
                        ),
                    ));
                    HirEnumVariant {
                        name: v.name.clone(),
                        tag,
                        payload_ty: None,
                        named_fields: Vec::new(),
                        arity: 0,
                    }
                }
            }
        })
        .collect();
    HirEnumDef {
        id,
        def_id: None,
        name: e.name.clone(),
        variants,
        span: e.span,
        generic_args: Vec::new(),
    }
}

pub(super) fn lower_struct_def(
    s: &AstStructDef,
    id: StructId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    sc: Scope<'_>,
) -> HirStructDef {
    let fields = match &s.kind {
        AstStructKind::Named(fs) => fs
            .iter()
            .map(|f| HirField {
                name: f.name.clone(),
                ty: resolve_ty_with_structs(&f.ty, structs, enums, sc),
                // Spec 2.x / i-want 942-950: keep the default expr so
                // a literal that omits this field can fill it lazily
                // at the use site.
                default: f.default.clone(),
            })
            .collect(),
        // Tuple struct `Foo(A, B)` — synthesize positional field names
        // ("0", "1", ...) so `n.0` tuple-style field access lands in
        // the same field-read path as named structs (spec 2.7.4).
        AstStructKind::Tuple(fs) => fs
            .iter()
            .enumerate()
            .map(|(i, f)| HirField {
                name: i.to_string(),
                ty: resolve_ty_with_structs(&f.ty, structs, enums, sc),
                default: None,
            })
            .collect(),
        AstStructKind::Unit => Vec::new(),
    };
    HirStructDef {
        id,
        def_id: None,
        name: s.name.clone(),
        fields,
        span: s.span,
        generic_args: Vec::new(),
        union_kind: None,
    }
}

/// Lower a `union { f1: T1; f2: T2; ... }` declaration into a single
/// synthetic `HirStructDef` with one field `__data` whose type is the
/// chosen storage. The field name → declared type table goes into
/// `union_kind.aliases`. See `union_storage_strategy` for the
/// fast-path (A) vs general-path (B) decision.
pub(super) fn lower_union_def(
    u: &rokc_ast::UnionDef,
    id: StructId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    sc: Scope<'_>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> HirStructDef {
    let aliases: Vec<(String, HirTy)> = u
        .fields
        .iter()
        .map(|f| {
            (
                f.name.clone(),
                resolve_ty_with_structs(&f.ty, structs, enums, sc),
            )
        })
        .collect();
    let is_repr_c = u.attrs.iter().any(|a| {
        a.path.as_slice() == ["repr"]
            && matches!(&a.body, rokc_ast::AttrBody::Args(args)
                if args.iter().any(|arg| matches!(arg, rokc_ast::AttrArg::Word(w) if w == "C")))
    });
    let storage = union_storage_strategy(&aliases, is_repr_c, &u.name, u.span, pre_diags);
    let storage_ty = match &storage {
        UnionStorage::WidestPrim(p) => HirTy::Prim(*p),
        UnionStorage::ByteArray { size, .. } => {
            HirTy::Array(Box::new(HirTy::Prim(PrimTy::U8)), *size)
        }
    };
    HirStructDef {
        id,
        def_id: None,
        name: u.name.clone(),
        fields: vec![HirField {
            name: "__data".to_owned(),
            ty: storage_ty,
            default: None,
        }],
        span: u.span,
        generic_args: Vec::new(),
        union_kind: Some(HirUnionKind {
            storage,
            aliases,
            is_repr_c,
        }),
    }
}

/// Pick the union backing storage. All-prim unions without `#[repr(C)]`
/// take the fast path (single widest primitive — model A). Anything
/// else (struct/enum field, `#[repr(C)]`) falls through to the general
/// `[u8; size]` byte-array path (model B).
pub(super) fn union_storage_strategy(
    aliases: &[(String, HirTy)],
    is_repr_c: bool,
    name: &str,
    span: rokc_diagnostic::Span,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> UnionStorage {
    let _ = span;
    if aliases.is_empty() {
        pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            format!("union `{name}` declares no fields (spec 2.x)"),
        ));
        return UnionStorage::WidestPrim(PrimTy::U8);
    }
    let all_prim = aliases.iter().all(|(_, t)| matches!(t, HirTy::Prim(_)));
    if all_prim && !is_repr_c {
        // Pick the widest primitive. Tie-break: prefer unsigned > signed
        // > float so written bits round-trip cleanly through a wider read.
        let mut best: Option<PrimTy> = None;
        let mut best_score: (u32, u8) = (0, 0);
        for (_, t) in aliases {
            if let HirTy::Prim(p) = t {
                let width = p.bit_width(64);
                let kind_pref: u8 = match p {
                    PrimTy::U8 | PrimTy::U16 | PrimTy::U32 | PrimTy::U64 | PrimTy::Usize => 3,
                    PrimTy::I8
                    | PrimTy::I16
                    | PrimTy::I32
                    | PrimTy::I64
                    | PrimTy::Isize
                    | PrimTy::CChar
                    | PrimTy::Char => 2,
                    PrimTy::F32 | PrimTy::F64 => 1,
                    PrimTy::Bool | PrimTy::Str => 0,
                };
                let score = (width, kind_pref);
                if best.is_none() || score > best_score {
                    best = Some(*p);
                    best_score = score;
                }
            }
        }
        return UnionStorage::WidestPrim(best.unwrap_or(PrimTy::U8));
    }
    // Byte-array path. Compute size = max byte size, align = max byte
    // alignment over all declared fields.
    let mut size: u32 = 0;
    let mut align: u32 = 1;
    for (fname, t) in aliases {
        let (sz, al) = ty_size_align_bytes(t).unwrap_or_else(|| {
            pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "union `{name}` field `{fname}` has type whose size is \
                     not yet computable in stage-1 (struct fields with \
                     pointer/closure types — spec 2.x byte-array union)"
                ),
            ));
            (0, 1)
        });
        if sz > size {
            size = sz;
        }
        if al > align {
            align = al;
        }
    }
    if size == 0 {
        size = 1;
    }
    // Round size up to align (C ABI: padding to alignment boundary).
    let padded = size.div_ceil(align) * align;
    // Stage-1: byte-array storage path is reserved in HIR (model B) but
    // codegen for value-level bitcast between primitive ↔ `[u8; N]` is
    // not yet wired through (mlir-translate rejects
    // `unrealized_conversion_cast` for these). Emit an explicit message
    // up front so users see a clear stage-1 limitation rather than an
    // opaque MLIR error. Stage-2 will replace this with alloca + GEP +
    // pointer bitcast + store/load pattern.
    pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
        rokc_diagnostic::ErrorKind::Type,
        format!(
            "union `{name}` falls into byte-array storage (non-primitive \
             field or `#[repr(C)]`) — stage-1 codegen for byte-storage \
             union is not yet implemented (spec 2.x byte-array union, \
             stage-2)"
        ),
    ));
    UnionStorage::ByteArray {
        size: padded,
        align,
    }
}

/// Best-effort byte size + alignment for a `HirTy`. Returns `None` for
/// types whose size depends on layout choices we haven't pinned yet
/// (closures with environment, generic struct without monomorphization).
pub(super) fn ty_size_align_bytes(ty: &HirTy) -> Option<(u32, u32)> {
    match ty {
        HirTy::Prim(p) => {
            let bits = p.bit_width(64);
            if bits == 0 {
                None
            } else {
                let bytes = bits / 8;
                Some((bytes, bytes))
            }
        }
        HirTy::Tuple(parts) | HirTy::Sum(parts) => {
            let mut total: u32 = 0;
            let mut align: u32 = 1;
            for p in parts {
                let (sz, al) = ty_size_align_bytes(p)?;
                if al > align {
                    align = al;
                }
                let pad = total.div_ceil(al) * al;
                total = pad + sz;
            }
            let padded = total.div_ceil(align) * align;
            Some((padded, align))
        }
        HirTy::Array(elem, n) => {
            let (sz, al) = ty_size_align_bytes(elem)?;
            Some((sz * n, al))
        }
        // Stage-1: struct/enum sizes need module access; report as
        // unknown so the caller falls back to the byte-array
        // diagnostic. Adding accurate sizing requires plumbing the
        // module reference here — separate milestone.
        HirTy::Struct(_)
        | HirTy::Enum(_)
        | HirTy::Path(_)
        | HirTy::Unknown
        | HirTy::Any
        | HirTy::Unit
        | HirTy::Fn(_, _)
        | HirTy::Closure { .. } => None,
    }
}

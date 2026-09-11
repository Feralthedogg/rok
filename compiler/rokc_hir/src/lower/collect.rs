//! Module-level passes: item collection (types, fns, impls, statics),
//! duplicate / trait-impl checks, and the final unresolved-type check.

#[allow(clippy::wildcard_imports)]
use super::*;
use rokc_ir_common::{Abi, FnRole, Linkage};

/// Const-fold a static initializer: an integer (optionally negated),
/// bool, string or `none` literal; `None` for anything else.
pub(super) fn literal_to_const_val(expr: &Expr, ty: &HirTy) -> Option<ConstVal> {
    use rokc_ast::Literal as L;
    let lit = match &expr.kind {
        ExprKind::Literal(l) => l,
        ExprKind::OpPrefix { op, operand } if op == "-" => {
            // `static N: i32 = -1;`
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

/// A static initializer that is not a (negated) literal runs once, on
/// first access, as this synthesized function (`static M: Mutex<..> =
/// Mutex::new(..)`).
fn is_lazy_static_init(v: &Expr) -> bool {
    match &v.kind {
        // Folded by the compile-time evaluator instead.
        ExprKind::Literal(AstLit::Float(_)) => true,
        ExprKind::Literal(_) => false,
        ExprKind::OpPrefix { op, operand } if op == "-" => {
            !matches!(operand.kind, ExprKind::Literal(_))
        }
        _ => true,
    }
}

fn is_lazy_init_fn(name: &str) -> bool {
    leaf_name(name).starts_with("__rok_static_init_")
}

fn lazy_init_fn_name(static_name: &str) -> String {
    match static_name.rsplit_once("::") {
        Some((m, leaf)) => format!("{m}::__rok_static_init_{leaf}"),
        None => format!("__rok_static_init_{static_name}"),
    }
}

/// `program` plus one `fn __rok_static_init_X() -> T { init }` per lazy
/// static (`None`: there is none).
fn with_lazy_static_inits(program: &Program) -> Option<Program> {
    let inits: Vec<Item> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Static(s) => s
                .value
                .as_ref()
                .filter(|v| is_lazy_static_init(v))
                .map(|v| {
                    Item::Fn(rokc_ast::FnDef {
                        vis: Visibility::Private,
                        attrs: Vec::new(),
                        name: lazy_init_fn_name(&s.name),
                        generics: rokc_ast::Generics::default(),
                        params: Vec::new(),
                        ret_ty: Some(s.ty.clone()),
                        // `return v;` (not a trailing `v`): the return type
                        // is the expected type that infers `Atomic::new(0)`.
                        body: Some(rokc_ast::Block {
                            stmts: vec![rokc_ast::Stmt {
                                kind: rokc_ast::StmtKind::Return(Some(v.clone())),
                                span: s.span,
                            }],
                            trailing: None,
                            span: s.span,
                            label: None,
                        }),
                        is_async: false,
                        is_generator: false,
                        is_unsafe: false,
                        throws: rokc_ast::ThrowsKind::None,
                        where_clause: Vec::new(),
                        span: s.span,
                    })
                }),
            _ => None,
        })
        .collect();
    if inits.is_empty() {
        return None;
    }
    let mut p = program.clone();
    p.items.extend(inits);
    Some(p)
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
    input: &crate::HirInput,
) -> HirModule {
    resolve::set_packages(input.packages.clone());
    // A prebuilt-library build: every body of that package is a root.
    let lib_pkg: Option<String> = input.lib.clone();
    let check_library = input.check_library;
    let augmented = with_lazy_static_inits(program);
    let program = augmented.as_ref().unwrap_or(program);
    // Diagnostics emitted during pre-body passes (impl-target validation
    // etc.) — folded into module.diagnostics once the module exists.
    let mut pre_diags: Vec<rokc_diagnostic::RokDiagnostic> = Vec::new();
    let err = |pre: &mut Vec<rokc_diagnostic::RokDiagnostic>, msg: String| {
        pre.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            msg,
        ));
    };
    // Spec 6.2: the parser expands `#[derive(..)]` on structs / enums
    // into impls (`rokc_parser::derive`); a union has no field-wise
    // meaning.
    for item in &program.items {
        if let Item::Union(u) = item {
            if let Some((_, at)) = rokc_parser::derive::derive_names(&u.attrs).first() {
                rokc_diagnostic::set_current_span(*at);
                err(
                    &mut pre_diags,
                    format!("cannot derive traits for union `{}` (spec 6.2.1)", u.name),
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
    let mut auto_traits: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut lang: HashMap<String, String> = HashMap::new();
    let mut type_vis: HashMap<String, Visibility> = HashMap::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
        let (name, vis) = match item {
            Item::Struct(s) => (&s.name, s.vis),
            Item::Enum(e) => (&e.name, e.vis),
            Item::Union(u) => (&u.name, u.vis),
            Item::TypeAlias(a) => (&a.name, a.vis),
            Item::Trait(t) => {
                traits.insert(t.name.clone());
                if t.attrs.iter().any(is_auto_trait_attr) {
                    auto_traits.insert(t.name.clone());
                }
                // Spec 6.4: trait slots, and a method slot (`drop_method`)
                // names its trait.
                let methods = t.items.iter().filter_map(|i| match i {
                    rokc_ast::TraitItem::Method(f) => Some(&f.attrs),
                    _ => None,
                });
                for slot in t
                    .attrs
                    .iter()
                    .chain(methods.flatten())
                    .filter_map(lang_slot)
                {
                    lang.insert(slot, t.name.clone());
                }
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
    // `Enum::Variant` keys, so `use E::{A}` / `use E::*` (and the
    // implicit `rok::core::**`) can bring variants in bare.
    let variants: std::collections::HashSet<String> = program
        .items
        .iter()
        .filter_map(|it| match it {
            Item::Enum(e) => Some(e),
            _ => None,
        })
        .flat_map(|e| e.variants.iter().map(|v| format!("{}::{}", e.name, v.name)))
        .collect();
    let names = TypeNames {
        names: type_set,
        variants,
        traits,
        auto_traits,
        lang,
        reexports: type_reexports,
        visibility: type_vis,
        uses,
        diags: std::cell::RefCell::new(Vec::new()),
        generic_aliases: program
            .items
            .iter()
            .filter_map(|it| match it {
                Item::TypeAlias(a)
                    if !a.generics.params.is_empty() || !a.where_clause.is_empty() =>
                {
                    Some((a.name.clone(), a.clone()))
                }
                _ => None,
            })
            .collect(),
        plain_aliases: program
            .items
            .iter()
            .filter_map(|it| match it {
                Item::TypeAlias(a) if a.generics.params.is_empty() => {
                    Some((a.name.clone(), a.ty.clone()))
                }
                _ => None,
            })
            .collect(),
        alias_uses: std::cell::RefCell::new(Vec::new()),
        canon_memo: std::cell::RefCell::default(),
    };
    warn_assoc_shadowing(program, &names, &mut pre_diags);
    let defaults = with_assoc_defaults(program, &names);
    let program = defaults.as_ref().unwrap_or(program);
    let assoc_sigs = with_self_assoc_sigs(program);
    let program = assoc_sigs.as_ref().unwrap_or(program);
    check_bound_names(program, &names, &mut pre_diags);

    // Pass 1a: enums. Generic enums get stashed for lazy instantiation.
    let mut enum_table: HashMap<String, EnumId> = HashMap::new();
    let mut enum_decls: Vec<&AstEnumDef> = Vec::new();
    let mut generic_enums: HashMap<String, &AstEnumDef> = HashMap::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
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
        rokc_diagnostic::set_current_span(item.span());
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
    // Unions share the struct namespace and id space; `union_kind` sends
    // init / read sites to the bitcast access path.
    let mut union_decls: Vec<&rokc_ast::UnionDef> = Vec::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
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
    // Plain structs whose fields name generic instances (`left:
    // List<i32>`) resolve them now that the instances exist.
    for (i, s) in struct_decls.iter().enumerate() {
        let module = module_of(&s.name);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        let id = StructId(u32::try_from(i).expect("StructId overflow"));
        struct_defs[i] = lower_struct_def(s, id, &struct_table, &enum_table, sc);
    }
    // Pass 1b.2: same idea for generic enums.
    instantiate_generic_enums(
        program,
        &generic_enums,
        &struct_table,
        &mut enum_table,
        &mut enum_defs,
        &names,
    );
    // Generic structs over generic enums (`List<Result<str, E>>`) could
    // not resolve their arguments before the enum instances existed:
    // instantiate again, then re-resolve the plain structs naming them.
    let before = struct_table.len();
    instantiate_generic_structs(
        program,
        &generic_structs,
        &mut struct_table,
        &mut struct_defs,
        &enum_table,
        &names,
    );
    if struct_table.len() != before {
        for (i, s) in struct_decls.iter().enumerate() {
            let module = module_of(&s.name);
            let sc = Scope {
                names: &names,
                module: &module,
            };
            let id = StructId(u32::try_from(i).expect("StructId overflow"));
            struct_defs[i] = lower_struct_def(s, id, &struct_table, &enum_table, sc);
        }
        instantiate_generic_enums(
            program,
            &generic_enums,
            &struct_table,
            &mut enum_table,
            &mut enum_defs,
            &names,
        );
    }
    // Plain enums whose payloads name generic instances (`Items(List<V>)`)
    // resolve them now that the instances exist (the first lowering gave
    // the diagnostics).
    for (i, e) in enum_decls.iter().enumerate() {
        let module = module_of(&e.name);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        let id = EnumId(u32::try_from(i).expect("EnumId overflow"));
        enum_defs[i] = lower_enum_def(e, id, &struct_table, &enum_table, sc, &mut Vec::new());
    }

    // Pass 1c: module-level `const`s, kept as AST and inlined at each
    // use; `static`s get global storage (`HirStaticDef`).
    let mut consts: HashMap<String, (Ty, Expr)> = HashMap::new();
    let mut impl_const_sets: Vec<ImplConsts> = Vec::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
        // Spec 2.9.1: an impl's `const` is `Type::NAME` (`Self::NAME`
        // inside the impl); a trait impl also gets the trait's defaults
        // (spec 2.8.3a).
        let item_consts: Vec<(String, Ty, Expr)> = match item {
            Item::Const(c) => vec![(c.name.clone(), c.ty.clone(), c.value.clone())],
            Item::Impl(i) => {
                let (keyed, set) = impl_consts(i, program, &names, &mut pre_diags);
                impl_const_sets.extend(set);
                keyed
            }
            _ => Vec::new(),
        };
        // Two trait impls may both give `S::N` (an ambiguity reported
        // where it is read, `lower_assoc_const`).
        let trait_impl = matches!(item, Item::Impl(i) if i.trait_path.is_some());
        for (key, ty, value) in item_consts {
            if consts.insert(key.clone(), (ty, value)).is_some() && !trait_impl {
                err(
                    &mut pre_diags,
                    format!("const `{key}` is defined more than once"),
                );
            }
        }
    }
    let mut static_defs: Vec<HirStaticDef> = Vec::new();
    let mut static_tys: HashMap<String, HirTy> = HashMap::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
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
            // A non-lazy initializer must const-fold to a literal.
            let lazy = s.value.as_ref().is_some_and(is_lazy_static_init);
            let init = match s.value.as_ref() {
                Some(_) if lazy => ConstVal::Unit,
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
                is_extern: false,
                init_fn: None,
                span: s.span,
            });
        }
        // Spec 5.9.3: `extern "C" { static errno: i32; }` — a C global,
        // read (and with `mut` written) like a `static`.
        if let Item::Extern(blk) = item {
            for ei in &blk.items {
                let rokc_ast::ExternItem::Static(s) = ei else {
                    continue;
                };
                if static_tys.contains_key(&s.name) {
                    err(
                        &mut pre_diags,
                        format!("static `{}` is defined more than once", s.name),
                    );
                    continue;
                }
                let sc = Scope {
                    names: &names,
                    module: "",
                };
                let ty = resolve_ty_with_structs(&s.ty, &struct_table, &enum_table, sc);
                static_tys.insert(s.name.clone(), ty.clone());
                static_defs.push(HirStaticDef {
                    name: s.name.clone(),
                    ty,
                    init: ConstVal::Unit,
                    is_mut: s.is_mut,
                    is_extern: true,
                    init_fn: None,
                    span: s.span,
                });
            }
        }
    }
    // Pass 1d: type aliases, expanded afterwards so one alias can name
    // another.
    let mut type_aliases: HashMap<String, HirTy> = HashMap::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
        if let Item::TypeAlias(a) = item {
            if !a.generics.params.is_empty() {
                continue;
            }
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
    // An alias still naming an alias after expansion is cyclic
    // (`type A = B; type B = A;`).
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

    // Pass 2: function-like declarations. Free functions first, then
    // `impl` methods (a free function `Type::method` taking `self`
    // first). Generic functions stay AST templates, monomorphized per
    // call, outside `decls` / `fn_table`.
    let mut fn_table: HashMap<String, FnSig> = HashMap::new();
    let mut extern_fns = std::collections::HashSet::new();
    let mut method_table: HashMap<(MethodTarget, String), Vec<FunctionId>> = HashMap::new();
    let mut method_info: HashMap<FunctionId, MethodInfo> = HashMap::new();
    // `(Type, TraitName)` per `impl Trait for Type`, for generic bounds.
    let mut impl_traits: std::collections::HashSet<(MethodTarget, String)> =
        std::collections::HashSet::new();
    let mut decls: Vec<MethodOrFn<'_>> = Vec::new();
    // Per decl: its body is library code (`rok::<tier>` / a dependency),
    // lowered only when reached (`lower_bodies`).
    let mut lib_decl: Vec<bool> = Vec::new();
    // Decl index → symbol path of a dependency's method (see below).
    let mut link_names: HashMap<usize, String> = HashMap::new();
    let mut generic_fns: HashMap<String, &FnDef> = HashMap::new();
    let mut generic_methods: HashMap<(String, String), Vec<GenericMethod>> = HashMap::new();
    let mut generic_trait_impls: Vec<GenericTraitImpl> = Vec::new();
    let mut intrinsics: HashMap<FunctionId, PrimOp> = HashMap::new();
    let mut unsafe_fns: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut ref_out: HashMap<FunctionId, RefOut> = HashMap::new();
    let mut extern_fn_ids: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut c_variadic: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    // `extern "rok"` declarations: the runtime's own ABI.
    let mut rok_externs: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let sig_of = |fn_def: &FnDef, id: FunctionId, self_ty: Option<&HirTy>, sc: Scope<'_>| {
        let resolve = |t: &Ty| {
            let mut r = resolve_ty_with_structs(t, &struct_table, &enum_table, sc);
            if let Some(st) = self_ty {
                substitute_params(&mut r, &HashMap::from([("Self".to_owned(), st.clone())]));
            }
            r
        };
        FnSig {
            id,
            ret_ty: resolve(&sig_ret_ast(fn_def)),
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
            param_refs: fn_def.params.iter().map(|p| p.by_ref).collect(),
            variadic: fn_def.params.last().is_some_and(|p| p.variadic),
        }
    };
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
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
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let module = module_of(&fn_def.name);
                let sc = Scope {
                    names: &names,
                    module: &module,
                };
                let sig = sig_of(fn_def, id, None, sc);
                if let Some(o) = ref_out_of(&sig) {
                    ref_out.insert(id, o);
                }
                fn_table.insert(fn_def.name.clone(), sig);
                decls.push(MethodOrFn::Fn(fn_def));
                lib_decl.push(!package_of(&module).is_empty());
            }
            Item::Extern(blk) => {
                let rok_abi = blk.abi == "rok";
                if !rok_abi && blk.abi != "C" {
                    err(
                        &mut pre_diags,
                        format!(
                            "unsupported ABI `\"{}\"` (`\"C\"`, or `\"rok\"` for the runtime)",
                            blk.abi
                        ),
                    );
                }
                for ei in &blk.items {
                    let rokc_ast::ExternItem::Fn(fn_def) = ei else {
                        continue;
                    };
                    // A repeated extern declaration names the same symbol;
                    // keep the first.
                    if fn_table.contains_key(&fn_def.name) {
                        continue;
                    }
                    extern_fns.insert(fn_def.name.clone());
                    let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                    // Spec 4.15.1: an extern function is `unsafe` to call.
                    unsafe_fns.insert(id);
                    let sc = Scope {
                        names: &names,
                        module: "",
                    };
                    fn_table.insert(fn_def.name.clone(), sig_of(fn_def, id, None, sc));
                    if rok_abi {
                        rok_externs.insert(id);
                    } else {
                        extern_fn_ids.insert(id);
                    }
                    if fn_def
                        .attrs
                        .iter()
                        .any(|a| a.path == [rokc_ast::C_VARIADIC_ATTR])
                    {
                        c_variadic.insert(id);
                    }
                    decls.push(MethodOrFn::Fn(fn_def));
                    lib_decl.push(false);
                }
            }
            _ => {}
        }
    }
    // Pre-collect every trait declaration so `impl Trait for T` blocks
    // can pick up default method bodies.
    let mut trait_defs: HashMap<String, &rokc_ast::TraitDef> = HashMap::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
        if let Item::Trait(t) = item {
            trait_defs.entry(t.name.clone()).or_insert(t);
        }
    }
    // `any Tr`: each trait's method names and supertrait keys, and
    // (filled per impl below) its implementing types in source order.
    let trait_info: HashMap<String, TraitInfo> = trait_defs
        .iter()
        .map(|(name, t)| {
            let module = module_of(name);
            let supers = t
                .supertraits
                .iter()
                .filter_map(|st| match &st.kind {
                    AstTyKind::Path(p) => {
                        let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                        Some(names.trait_key(&segs, &module))
                    }
                    _ => None,
                })
                .collect();
            let fns = || {
                t.items.iter().filter_map(|i| match i {
                    rokc_ast::TraitItem::Method(m) => Some(m),
                    _ => None,
                })
            };
            let methods = fns().map(|m| leaf_name(&m.name).to_owned()).collect();
            let params: Vec<&str> = t
                .generics
                .params
                .iter()
                .filter_map(|p| match p {
                    rokc_ast::GenericParam::Type { name, .. } => Some(name.as_str()),
                    rokc_ast::GenericParam::Const { .. } => None,
                })
                .collect();
            let assoc: Vec<&str> = t
                .items
                .iter()
                .filter_map(|i| match i {
                    rokc_ast::TraitItem::AssocType { name, .. } => Some(name.as_str()),
                    _ => None,
                })
                .collect();
            let needs = fns()
                .map(|m| {
                    let mut out = Vec::new();
                    for ty in std::iter::once(sig_ret_ast(m)).chain(
                        m.params
                            .iter()
                            .filter(|p| p.name != "self")
                            .filter_map(|p| p.ty.clone()),
                    ) {
                        ast_ty_needs(&ty, &params, &assoc, &mut out);
                    }
                    (leaf_name(&m.name).to_owned(), out)
                })
                .collect();
            (
                name.clone(),
                TraitInfo {
                    methods,
                    supers,
                    needs,
                    decls: fns()
                        .map(|m| (leaf_name(&m.name).to_owned(), m.clone()))
                        .collect(),
                    module,
                    params: params.iter().map(|p| (*p).to_owned()).collect(),
                },
            )
        })
        .collect();
    let mut trait_impl_tys: HashMap<String, Vec<HirTy>> = HashMap::new();
    let mut impl_assoc: HashMap<MethodTarget, Vec<ImplAssoc>> = HashMap::new();
    let mut neg_auto: std::collections::HashSet<(String, String)> =
        std::collections::HashSet::new();

    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
        let Item::Impl(impl_def) = item else { continue };
        let module = impl_module(impl_def);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        if !check_auto_impl(impl_def, &names, &module, &mut neg_auto, &mut pre_diags) {
            continue;
        }
        let impl_generic = !impl_def.generics.params.is_empty();
        if let (true, Some(tp)) = (impl_generic, &impl_def.trait_path) {
            let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
            let trait_key = names.trait_key(&segs, &module);
            generic_trait_impls.push(generic_trait_impl(
                impl_def,
                trait_key.clone(),
                trait_defs.get(&trait_key).copied(),
                &module,
                generic_trait_impls.len(),
                &mut pre_diags,
            ));
            continue;
        }
        // A generic inherent impl on a structural type (`impl<T, const N:
        // usize> [T; N] { .. }`): matched against the receiver like a
        // generic trait impl, with no trait (empty key).
        if impl_generic && !matches!(impl_def.self_ty.kind, AstTyKind::Path(_)) {
            generic_trait_impls.push(generic_trait_impl(
                impl_def,
                String::new(),
                None,
                &module,
                generic_trait_impls.len(),
                &mut pre_diags,
            ));
            continue;
        }
        // Inherent methods of a generic impl (and generic methods of a
        // plain one) are templates keyed by the target's generic base.
        let generic_base = match &impl_def.self_ty.kind {
            AstTyKind::Path(p) if impl_def.trait_path.is_none() => {
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                // `impl str { fn parse<T>(..) }`: a primitive's generic
                // methods key by the primitive's name.
                names.canon(&segs, &module, &[]).or_else(|| {
                    match crate::ty::resolve_ty(&impl_def.self_ty) {
                        HirTy::Prim(prim) => Some(prim.name().to_owned()),
                        _ => None,
                    }
                })
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
        // A generic impl's methods are all templates keyed by
        // `generic_base`; resolving `Base<T, E>` here would look its type
        // params up as (possibly same-named, visible) types.
        let target_ty = if impl_generic {
            HirTy::Path(vec![generic_base.clone().unwrap_or_default()])
        } else {
            resolve_ty_with_structs(&impl_def.self_ty, &struct_table, &enum_table, sc)
        };
        let target = method_target_for(&target_ty);
        // Resolve the trait (a user trait resolves to its qualified name;
        // a bootstrap trait like `core::ops::Add` keeps its last segment).
        let trait_name: Option<String> = impl_def.trait_path.as_ref().map(|tp| {
            let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
            names.trait_key(&segs, &module)
        });
        // `From<i32>` / `From<i8>` impls on one type keep their methods
        // apart by the trait's arguments (`overload_args`).
        let mut trait_args_key = String::new();
        if let (Some(tn), Some(target_key)) = (&trait_name, target.clone()) {
            // `impl Get<i32> for T { type Item = u8; }` also answers
            // `Get<i32>`, `Get<Item = u8>` and `Get<i32, Item = u8>`.
            let rty = |g: &rokc_ast::Ty| resolve_ty_with_structs(g, &struct_table, &enum_table, sc);
            let args: Vec<HirTy> = impl_def
                .trait_path
                .as_ref()
                .and_then(|tp| tp.segments.last())
                .map(|s| s.generics.iter().map(rty).collect())
                .unwrap_or_default();
            // Spec 2.10.5: omitted trait arguments take the parameter's
            // default (`trait Add<Rhs = Self>`: `impl Add for V` is
            // `impl Add<V> for V`).
            let mut args = args;
            if let Some(td) = trait_defs.get(tn) {
                for gp in td.generics.params.iter().skip(args.len()) {
                    let rokc_ast::GenericParam::Type {
                        default: Some(d), ..
                    } = gp
                    else {
                        break;
                    };
                    let is_self = matches!(&d.kind, AstTyKind::Path(p)
                        if p.segments.len() == 1 && p.segments[0].name == "Self");
                    args.push(if is_self { target_ty.clone() } else { rty(d) });
                }
            }
            let assoc: Vec<(String, HirTy)> = impl_def
                .items
                .iter()
                .filter_map(|i| match i {
                    AstImplItem::AssocType { name, ty } => Some((name.clone(), rty(ty))),
                    _ => None,
                })
                .collect();
            let full_key = bound_key(tn.clone(), &args, &[], &struct_table, &enum_table);
            if !args.is_empty() && impl_traits.contains(&(target_key.clone(), full_key.clone())) {
                err(
                    &mut pre_diags,
                    format!(
                        "`{full_key}` is implemented more than once for `{}`",
                        impl_def_display(&impl_def.self_ty)
                    ),
                );
                continue;
            }
            trait_args_key = args
                .iter()
                .map(|a| "_".to_owned() + &ty_mangle(a))
                .collect();
            for k in impl_bound_keys(tn, &args, &assoc, &struct_table, &enum_table) {
                impl_traits.insert((target_key.clone(), k));
            }
            impl_assoc.entry(target_key.clone()).or_default().extend(
                assoc
                    .iter()
                    .map(|(n, t)| (tn.clone(), args.clone(), n.clone(), t.clone())),
            );
            trait_impl_tys
                .entry(tn.clone())
                .or_default()
                .push(target_ty.clone());
        }
        let trait_def = trait_name
            .as_ref()
            .and_then(|tn| trait_defs.get(tn).copied());
        let target_display = impl_def_display(&impl_def.self_ty);
        // Methods this impl provides: their trait defaults are skipped.
        let mut explicit_methods: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        for ii in &impl_def.items {
            let m = match ii {
                AstImplItem::Method(m) => m,
                AstImplItem::Const(_) | AstImplItem::AssocType { .. } => continue,
            };
            let leaf = leaf_name(&m.name).to_owned();
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
                // `Box__get` is both the mono cache key and the name
                // diagnostics print.
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
                let slot = generic_methods
                    .entry((base.clone(), leaf.clone()))
                    .or_default();
                if slot.iter().any(|g| g.info.trait_name.is_none()) {
                    err(
                        &mut pre_diags,
                        format!("method `{leaf}` is defined more than once for `{target_display}`"),
                    );
                    continue;
                }
                slot.push(GenericMethod {
                    def,
                    self_ty: impl_def.self_ty.clone(),
                    info: MethodInfo {
                        module: module.clone(),
                        vis: m.vis,
                        trait_name: None,
                    },
                });
                continue;
            }
            if let Some(td) = trait_def {
                let tm = td.items.iter().find_map(|ti| match ti {
                    rokc_ast::TraitItem::Method(tm) if tm.name == leaf => Some(tm),
                    _ => None,
                });
                match tm {
                    None => err(
                        &mut pre_diags,
                        format!("method `{leaf}` is not a member of trait `{}`", td.name),
                    ),
                    // Spec 4.4.9: a throwing fn can't fill a non-throwing
                    // slot. The operator traits (stdlib 2.3) never throw.
                    Some(tm) if is_throwing(&m.throws) && !is_throwing(&tm.throws) => {
                        err(
                            &mut pre_diags,
                            format!(
                                "`{leaf}` throws but `{}::{leaf}` is declared without \
                                 `throws`, so an impl can't add one (spec 4.4.9){}",
                                td.name,
                                if td.attrs.iter().any(|a| a.path == ["lang"]) {
                                    " — operators don't throw; return a `Result` or use \
                                     a named method"
                                } else {
                                    ""
                                }
                            ),
                        );
                    }
                    Some(_) => {}
                }
            }
            let Some(key) = method_key(
                &fn_table,
                &method_info,
                &target_ty,
                &leaf,
                trait_name.as_deref(),
                &trait_args_key,
            ) else {
                err(
                    &mut pre_diags,
                    format!("method `{leaf}` is defined more than once for `{target_display}`"),
                );
                continue;
            };
            let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
            let sig = sig_of(m, id, Some(&target_ty), sc);
            if let Some(o) = ref_out_of(&sig) {
                ref_out.insert(id, o);
            }
            fn_table.insert(key.clone(), sig);
            if let Some(op) = intrinsic_of(m, &module, &mut pre_diags) {
                intrinsics.insert(id, op);
            }
            if let Some(t) = target.clone() {
                method_table.entry((t, leaf.clone())).or_default().push(id);
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
            // A dependency's method symbol must not depend on this
            // build's struct numbering (`Struct70__m`): a prebuilt
            // dependency and its users name it alike.
            if resolve::is_dependency(&package_of(&module)) {
                let mut name = format!("{module}::{}.{leaf}", impl_def_display(&impl_def.self_ty));
                if let Some(tp) = &impl_def.trait_path {
                    name.push_str("__by_");
                    name.push_str(&impl_def_display(&Ty {
                        kind: AstTyKind::Path(tp.clone()),
                        span: tp.span,
                    }));
                }
                link_names.insert(decls.len(), name);
            }
            decls.push(MethodOrFn::Method {
                fn_def: m,
                self_ty: target_ty.clone(),
                module: module.clone(),
                key,
                subst: HashMap::new(),
            });
            lib_decl.push(!package_of(&module).is_empty());
        }

        // Trait defaults the impl doesn't override, lowered as methods
        // with `Self = target_ty`. A missing required method is an error.
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
                let Some(key) = method_key(
                    &fn_table,
                    &method_info,
                    &target_ty,
                    &tm.name,
                    trait_name.as_deref(),
                    &trait_args_key,
                ) else {
                    err(
                        &mut pre_diags,
                        format!(
                            "method `{}` is defined more than once for `{target_display}`",
                            tm.name
                        ),
                    );
                    continue;
                };
                // A default with its own type parameters or a signature
                // naming the trait's associated types (`fn map<U>(self, f:
                // fn(Item) -> U)`) becomes a template, instantiated per
                // call with `Item` replaced by this impl's type.
                if !tm.generics.params.is_empty()
                    || sig_mentions(tm, &trait_assoc_names(trait_def))
                    || returns_self_generic(tm)
                {
                    let base = match &target_ty {
                        HirTy::Struct(id) => Some(struct_defs[id.0 as usize].name.clone()),
                        HirTy::Enum(id) => Some(enum_defs[id.0 as usize].name.clone()),
                        _ => None,
                    };
                    if let Some(base) = base {
                        let mut def = tm.clone();
                        subst_assoc_sig(&mut def, &impl_assoc_types(impl_def));
                        def.name = format!("{trait_module}::{}__{}", leaf_name(&base), tm.name);
                        let slot = generic_methods.entry((base, tm.name.clone())).or_default();
                        if !slot.is_empty() {
                            // Another trait's same-named default: its own
                            // mono cache key / symbol.
                            def.name = format!(
                                "{}__by_{}",
                                def.name,
                                leaf_name(trait_name.as_deref().unwrap_or_default())
                            );
                        }
                        slot.push(GenericMethod {
                            def,
                            self_ty: impl_def.self_ty.clone(),
                            info: MethodInfo {
                                module: trait_module.clone(),
                                vis: Visibility::Pub,
                                trait_name: trait_name.clone(),
                            },
                        });
                    }
                    // A primitive / tuple target gets no such defaults.
                    continue;
                }
                // `trait Contains<Item>` + `impl Contains<i32> for S`: the
                // default's signature sees `Item = i32`.
                let mut targs = trait_param_args(trait_def, impl_def);
                // Const arguments (`3`, `W`, `{ W + 1 }`) become literals.
                for gp in &trait_def.generics.params {
                    if let rokc_ast::GenericParam::Const { name, .. } = gp {
                        if let Some(t) = targs.get_mut(name) {
                            if let Some(v) = const_arg_value(t, &consts, sc.module) {
                                *t = const_literal_ty(v, t.span);
                            }
                        }
                    }
                }
                let body_subst: HashMap<String, HirTy> = trait_def
                    .generics
                    .params
                    .iter()
                    .filter_map(|gp| match gp {
                        rokc_ast::GenericParam::Type { name, .. } => targs.get(name).map(|t| {
                            (
                                name.clone(),
                                resolve_ty_with_structs(t, &struct_table, &enum_table, sc),
                            )
                        }),
                        rokc_ast::GenericParam::Const { name, ty } => {
                            let v = match &targs.get(name)?.kind {
                                AstTyKind::Const(c) => {
                                    super::const_eval::syntactic_int(c, &|_| None)?
                                }
                                _ => return None,
                            };
                            let prim = match resolve_ty(ty) {
                                HirTy::Prim(p) => Some(p),
                                _ => None,
                            };
                            Some((name.clone(), crate::ty::const_ty(v, prim)))
                        }
                    })
                    .collect();
                let tm: &FnDef = if targs.is_empty() {
                    tm
                } else {
                    let mut d = tm.clone();
                    subst_assoc_sig(&mut d, &targs);
                    // Leaked so `decls` can borrow it like the program's
                    // items: one small FnDef per default instance per run.
                    Box::leak(Box::new(d))
                };
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let tsc = Scope {
                    names: &names,
                    module: &trait_module,
                };
                let sig = sig_of(tm, id, Some(&target_ty), tsc);
                if let Some(o) = ref_out_of(&sig) {
                    ref_out.insert(id, o);
                }
                fn_table.insert(key.clone(), sig);
                if let Some(t) = target.clone() {
                    method_table
                        .entry((t, tm.name.clone()))
                        .or_default()
                        .push(id);
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
                    key,
                    subst: body_subst,
                });
                // A library default in a user impl is checked with it.
                lib_decl.push(!package_of(&module).is_empty());
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
            if let Some(def) = generic_fns.get(&re.full_path).copied() {
                generic_fns.entry(alias_key.clone()).or_insert(def);
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
        rokc_diagnostic::set_current_span(item.span());
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
        uninferred: std::cell::Cell::new(0),
        extra_structs: std::cell::RefCell::new(Vec::new()),
        extra_struct_table: std::cell::RefCell::new(HashMap::new()),
        extra_enums: std::cell::RefCell::new(Vec::new()),
        extra_enum_table: std::cell::RefCell::new(HashMap::new()),
        any_tags: std::cell::RefCell::new(Vec::new()),
        ref_out: std::cell::RefCell::new(ref_out),
        any_dispatch: std::cell::RefCell::new(Vec::new()),
        projecting: std::cell::RefCell::new(Vec::new()),
        const_substs: std::cell::RefCell::new(HashMap::new()),
        thunks: std::cell::RefCell::new(HashMap::new()),
        instances: std::cell::RefCell::new(Vec::new()),
        instance_warns: std::cell::RefCell::new(super::InstanceWarns::default()),
        diagnostics: std::cell::RefCell::new(Vec::new()),
        infer_vars: std::cell::RefCell::new(Vec::new()),
        infer_depth: std::cell::Cell::new(0),
        infer_floor: std::cell::Cell::new(0),
        fn_origin: std::cell::RefCell::new(HashMap::new()),
        const_lowering: std::cell::RefCell::new(std::collections::HashSet::new()),
        const_stack: std::cell::RefCell::new(Vec::new()),
    };
    let mut exports: Vec<(FunctionId, String)> = Vec::new();
    let mut prebuilt: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut c_defs: Vec<FunctionId> = Vec::new();
    for (i, d) in decls.iter().enumerate() {
        let (MethodOrFn::Fn(f) | MethodOrFn::Method { fn_def: f, .. }) = d;
        rokc_diagnostic::set_current_span(f.span);
        let id = FunctionId(u32::try_from(i).expect("FunctionId overflow"));
        if f.is_unsafe {
            unsafe_fns.insert(id);
        }
        if f.attrs
            .iter()
            .any(|a| a.path == [rokc_ast::EXTERN_C_FN_ATTR])
        {
            check_extern_c_fn(f, &mut pre_diags);
            c_defs.push(id);
        }
        if !c_variadic.contains(&id)
            && f.attrs
                .iter()
                .any(|a| a.path == [rokc_ast::C_VARIADIC_ATTR])
        {
            err(
                &mut pre_diags,
                format!(
                    "`{}`: a C variadic `...` parameter is only allowed on a declaration in an \
                     `extern \"C\" {{ .. }}` block (spec 8.6.10)",
                    f.name
                ),
            );
        }
        let module = match d {
            MethodOrFn::Fn(f) => module_of(&f.name),
            MethodOrFn::Method { module, .. } => module.clone(),
        };
        let prebuilt_fn = f.body.is_none()
            && !(extern_fn_ids.contains(&id) || rok_externs.contains(&id))
            && input.prebuilt.contains(&package_of(&module));
        if prebuilt_fn {
            prebuilt.insert(id);
        }
        if let Some(sym) = export_name(f) {
            if f.body.is_none() && !prebuilt_fn {
                err(
                    &mut pre_diags,
                    format!("`#[export_name]` on `{}` needs a function body", f.name),
                );
            } else if exports.iter().any(|(_, s)| *s == sym) {
                err(
                    &mut pre_diags,
                    format!("symbol `{sym}` is exported twice (`#[export_name]`)"),
                );
            } else {
                exports.push((id, sym));
            }
        }
    }
    for f in generic_fns.values() {
        rokc_diagnostic::set_current_span(f.span);
        if f.attrs
            .iter()
            .any(|a| a.path == [rokc_ast::EXTERN_C_FN_ATTR])
        {
            check_extern_c_fn(f, &mut pre_diags);
        }
        if export_name(f).is_some() {
            err(
                &mut pre_diags,
                format!(
                    "`#[export_name]` on generic function `{}`: only a concrete function \
                     has one symbol",
                    f.name
                ),
            );
        }
    }
    let mut key_of: HashMap<FunctionId, String> = HashMap::new();
    for (k, s) in &fn_table {
        // Re-export aliases share the id; keep the shortest (original) key.
        let e = key_of.entry(s.id).or_insert_with(|| k.clone());
        if k.len() < e.len() {
            e.clone_from(k);
        }
    }
    let main = fn_table
        .get("main")
        .map(|s| s.id)
        .filter(|id| !extern_fn_ids.contains(id) && !rok_externs.contains(id));
    let mut env = Env {
        impl_consts: impl_const_sets,
        fn_table,
        extern_fns,
        method_table,
        key_of,
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
        generic_trait_impls,
        intrinsics,
        extern_fn_ids: extern_fn_ids.clone(),
        rok_externs: rok_externs.clone(),
        c_variadic: c_variadic.clone(),
        c_defs: c_defs.iter().copied().collect(),
        prec,
        sink,
        item_visibility,
        field_vis,
        uses,
        impl_traits,
        unsafe_fns,
        neg_auto,
        trait_info,
        trait_impl_tys,
        impl_assoc,
        statics: static_tys,
        mut_statics: static_defs
            .iter()
            .filter(|s| s.is_mut)
            .map(|s| s.name.clone())
            .collect(),
        literal_shapes: literal_handlers(program, &mut pre_diags),
        names,
        decls,
    };
    check_impl_overlap(&env);
    check_derives(&env, program);
    // Eagerly instantiated generic structs whose fields name projections
    // (`Peekable<ListIter<i32>>`'s `peeked: I::Item | none`): resolve
    // them now that impls are known.
    let fixes: Vec<(usize, Vec<HirField>)> = env
        .structs
        .iter()
        .enumerate()
        .filter(|(_, d)| {
            let mut open = Vec::new();
            d.fields
                .iter()
                .for_each(|f| collect_unknown_paths(&f.ty, &mut open));
            !d.generic_args.is_empty() && !open.is_empty()
        })
        .filter_map(|(i, d)| {
            let base = enum_base_name(&d.name).to_owned();
            let def = *env.generic_structs.get(&base)?;
            let subst = generic_subst(&def.generics, &d.generic_args);
            let mut rcx = LowerCtx::new(&env, &subst, None);
            rcx.current_module = module_of(&base);
            Some((i, generic_struct_fields(def, &|t| rcx.resolve_ast_ty(t))))
        })
        .collect();
    for (i, fields) in fixes {
        env.structs[i].fields = fields;
    }
    // A static of a generic type (`static mut l: List<i32>`) is left a
    // path by the early pass: instantiate it now.
    let no_subst = HashMap::new();
    let static_fixes: Vec<(usize, HirTy)> = static_defs
        .iter()
        .enumerate()
        .filter(|(_, d)| {
            let mut open = Vec::new();
            collect_unknown_paths(&d.ty, &mut open);
            !open.is_empty()
        })
        .filter_map(|(i, d)| {
            let (ast, module) = program.items.iter().find_map(|item| match item {
                Item::Static(s) if s.name == d.name && !d.is_extern => {
                    Some((&s.ty, module_of(&s.name)))
                }
                Item::Extern(blk) if d.is_extern => blk.items.iter().find_map(|ei| match ei {
                    rokc_ast::ExternItem::Static(s) if s.name == d.name => {
                        Some((&s.ty, String::new()))
                    }
                    _ => None,
                }),
                _ => None,
            })?;
            let mut rcx = LowerCtx::new(&env, &no_subst, None);
            rcx.current_module = module;
            Some((i, rcx.resolve_ast_ty(ast)))
        })
        .collect();
    for (i, ty) in static_fixes {
        env.statics.insert(static_defs[i].name.clone(), ty.clone());
        static_defs[i].ty = ty;
    }
    let decl_roots: Vec<bool> = env
        .decls
        .iter()
        .zip(&lib_decl)
        .enumerate()
        .map(|(i, (d, &lib))| {
            let (MethodOrFn::Fn(f) | MethodOrFn::Method { fn_def: f, .. }) = d;
            let module = match d {
                MethodOrFn::Fn(f) => module_of(&f.name),
                MethodOrFn::Method { module, .. } => module.clone(),
            };
            !lib || check_library
                || exports.iter().any(|(id, _)| id.0 as usize == i)
                || is_lazy_init_fn(&f.name)
                || lib_pkg.as_ref().is_some_and(|p| package_of(&module) == *p)
        })
        .collect();
    super::const_eval::check_user_consts(&env);
    let (mut functions, unlowered) = lower_bodies(&env, &decl_roots);
    // Spec 5.3.1: an initializer evaluated now needs no lazy init.
    let folded_statics: HashMap<String, ConstVal> = static_defs
        .iter()
        .filter_map(|s| {
            let init = lazy_init_fn_name(&s.name);
            let f = functions.iter().find(|f| f.name == init)?;
            Some((s.name.clone(), super::const_eval::static_init(&env, f)?))
        })
        .collect();
    for (i, name) in link_names {
        functions[i].name = name;
    }
    check_type_bounds(&env);
    super::send_check::check(&env, &functions);
    let (any_seeds, any_exports) = super::expr::any_link(&env, lib_pkg.as_deref());
    let any_types = super::expr::any_types(&env);
    if lib_pkg.is_some() || !prebuilt.is_empty() {
        exports.extend(any_exports);
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
    super::infer::drop_var_instances(&mut structs, &mut enums);
    for s in &mut static_defs {
        if let Some(c) = folded_statics.get(&s.name) {
            s.init = c.clone();
            continue;
        }
        let init = lazy_init_fn_name(&s.name);
        s.init_fn = functions.iter().find(|f| f.name == init).map(|f| f.id);
    }
    // Per-function facts for MIR / codegen.
    let index: HashMap<FunctionId, usize> = functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, i))
        .collect();
    let mut set = |id: &FunctionId, f: &dyn Fn(&mut rokc_ir_common::FnFacts)| {
        if let Some(&i) = index.get(id) {
            f(&mut functions[i].facts);
        }
    };
    for id in &extern_fn_ids {
        let variadic = c_variadic.contains(id);
        set(id, &|f| {
            f.linkage = Linkage::Extern;
            f.abi = Abi::C { variadic };
        });
    }
    for id in &rok_externs {
        set(id, &|f| f.linkage = Linkage::Extern);
    }
    for id in &prebuilt {
        set(id, &|f| f.linkage = Linkage::Prebuilt);
    }
    for id in &c_defs {
        set(id, &|f| f.abi = Abi::C { variadic: false });
    }
    for (id, sym) in &exports {
        set(id, &|f| f.export_name = Some(sym.clone()));
    }
    if let Some(id) = &main {
        set(id, &|f| f.role = FnRole::Main);
    }
    let lazy_inits = static_defs.iter().filter_map(|s| s.init_fn);
    let roots = if lib_pkg.is_some() {
        let package = (0..decl_roots.len())
            .filter(|&i| decl_roots[i] && lib_decl[i])
            .map(|i| FunctionId(i as u32));
        let dispatchers = functions
            .iter()
            .filter(|f| f.facts.role == FnRole::AnyDispatcher)
            .map(|f| f.id);
        Some(
            package
                .chain(dispatchers)
                .chain(exports.iter().map(|(id, _)| *id))
                .chain(lazy_inits)
                .collect(),
        )
    } else {
        main.map(|m| {
            std::iter::once(m)
                .chain(exports.iter().map(|(id, _)| *id))
                .chain(lazy_inits)
                .collect()
        })
    };
    let mut module = HirModule {
        functions,
        structs,
        enums,
        statics: static_defs,
        diagnostics: pre_diags,
        roots,
        unlowered,
        any_seeds,
        any_types,
        type_visibility: names.visibility.clone(),
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
    module
        .diagnostics
        .extend(sink.instance_warns.into_inner().agreed());
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
    let list = |ts: &[Ty], sep: &str| {
        ts.iter()
            .map(impl_def_display)
            .collect::<Vec<_>>()
            .join(sep)
    };
    match &ty.kind {
        AstTyKind::Path(p) => {
            let path = p
                .segments
                .iter()
                .map(|s| s.name.as_str())
                .collect::<Vec<_>>()
                .join("::");
            match p.segments.last().map(|s| s.generics.as_slice()) {
                Some(args) if !args.is_empty() => format!("{path}<{}>", list(args, ", ")),
                _ => path,
            }
        }
        AstTyKind::Tuple(ts) => format!("({})", list(ts, ", ")),
        AstTyKind::Sum(ts) => list(ts, " | "),
        AstTyKind::None => "none".to_owned(),
        AstTyKind::Array(e, rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Int(n))) => {
            format!("[{}; {n}]", impl_def_display(e))
        }
        AstTyKind::Array(e, rokc_ast::ConstExpr::Path(p)) if p.segments.len() == 1 => {
            format!("[{}; {}]", impl_def_display(e), p.segments[0].name)
        }
        AstTyKind::Array(e, rokc_ast::ConstExpr::Expr(x)) => match &x.kind {
            ExprKind::Path(p) if p.segments.len() == 1 => {
                format!("[{}; {}]", impl_def_display(e), p.segments[0].name)
            }
            _ => format!("[{}; _]", impl_def_display(e)),
        },
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
        HirTy::Fn(a, r, _)
        | HirTy::Closure {
            args: a, ret: r, ..
        } => a.iter().any(|p| ty_mentions_any(p, aliases)) || ty_mentions_any(r, aliases),
        HirTy::Throws { ok, err } => ty_mentions_any(ok, aliases) || ty_mentions_any(err, aliases),
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
        rokc_diagnostic::set_current_span(item.span());
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
    // Each unknown name is reported at the first item that mentions it.
    // The thread-local "current span" is whatever pass ran last (usually
    // a library item), so it must not be the default here.
    let mut unknown_types: Vec<(String, rokc_diagnostic::Span)> = Vec::new();
    let mut note = |ty: &HirTy, span: rokc_diagnostic::Span| {
        let mut names = Vec::new();
        collect_unknown_paths(ty, &mut names);
        for n in names {
            if !unknown_types.iter().any(|(t, _)| *t == n) {
                unknown_types.push((n, span));
            }
        }
    };
    for s in &module.structs {
        for f in &s.fields {
            note(&f.ty, s.span);
        }
    }
    for e in &module.enums {
        for v in &e.variants {
            if let Some(t) = &v.payload_ty {
                note(t, e.span);
            }
        }
    }
    for st in &module.statics {
        note(&st.ty, st.span);
    }
    for f in &module.functions {
        note(&f.ret_ty, f.span);
        for p in &f.params {
            note(&p.ty, f.span);
        }
        for l in &f.locals {
            note(&l.ty, f.span);
        }
    }
    unknown_types.sort_by(|a, b| a.0.cmp(&b.0));
    for (t, span) in unknown_types {
        let old = rokc_diagnostic::set_current_span(span);
        module
            .diagnostics
            .push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                format!("cannot find type `{t}` in this scope"),
            ));
        rokc_diagnostic::set_current_span(old);
    }
    if module
        .diagnostics
        .iter()
        .any(rokc_diagnostic::RokDiagnostic::is_error)
    {
        return;
    }
    let bad = module.functions.iter().find(|f| {
        f.params.iter().any(|p| p.ty == HirTy::Unknown)
            || f.locals.iter().any(|l| l.ty == HirTy::Unknown)
            || f.body.as_ref().is_some_and(hir_block_has_unknown)
    });
    if let Some(f) = bad {
        let old = rokc_diagnostic::set_current_span(f.span);
        module
            .diagnostics
            .push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "internal compiler error: an expression in `{}` has no resolved type \
                 (lowering fell through without a diagnostic) — please report",
                    f.name
                ),
            ));
        rokc_diagnostic::set_current_span(old);
    }
}

pub(super) fn collect_unknown_paths(ty: &HirTy, out: &mut Vec<String>) {
    match ty {
        HirTy::Path(p) if p.as_slice() != ["none"] && crate::ty::as_const(ty).is_none() => {
            out.push(p.join("::"));
        }
        HirTy::Sum(parts) | HirTy::Tuple(parts) => {
            for p in parts {
                collect_unknown_paths(p, out);
            }
        }
        HirTy::Array(e, _) | HirTy::GcBuf(e) => collect_unknown_paths(e, out),
        HirTy::Fn(a, r, _)
        | HirTy::Closure {
            args: a, ret: r, ..
        } => {
            for p in a {
                collect_unknown_paths(p, out);
            }
            collect_unknown_paths(r, out);
        }
        HirTy::Throws { ok, err } => {
            collect_unknown_paths(ok, out);
            collect_unknown_paths(err, out);
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
        | HirStmt::Panic(e)
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
        K::Const(_) | K::Local(_) | K::StaticRef(_) | K::FnRef(_) | K::SizeOf { .. } => false,
        K::Block(b) => hir_block_has_unknown(b),
        K::PrimBinOp { lhs, rhs, .. } => hir_expr_has_unknown(lhs) || hir_expr_has_unknown(rhs),
        K::PrimUnaryOp { operand, .. } | K::Cast { operand, .. } => hir_expr_has_unknown(operand),
        K::Call { args, .. } | K::EnumVariantInit { args, .. } | K::CoroNew { args, .. } => {
            any(args)
        }
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
        | K::UnionRead { target, .. }
        | K::ArrayRepeat { value: target, .. } => hir_expr_has_unknown(target),
        K::WithField { target, value, .. } => {
            hir_expr_has_unknown(target) || hir_expr_has_unknown(value)
        }
        K::SumWrap { value, .. } => value.as_deref().is_some_and(hir_expr_has_unknown),
        K::ArrayInit { elements, .. } => any(elements),
        K::ArrayIndex { array, index, .. } => {
            hir_expr_has_unknown(array) || hir_expr_has_unknown(index)
        }
        K::UnionWrite { value, .. } | K::Suspend { value, .. } => hir_expr_has_unknown(value),
        K::BufNew { len, .. } | K::RawRead { addr: len, .. } => hir_expr_has_unknown(len),
        K::RawWrite { addr, value, .. } => {
            hir_expr_has_unknown(addr) || hir_expr_has_unknown(value)
        }
        K::BufGet { buf, index, .. } => hir_expr_has_unknown(buf) || hir_expr_has_unknown(index),
        K::BufSet {
            buf, index, value, ..
        } => {
            hir_expr_has_unknown(buf) || hir_expr_has_unknown(index) || hir_expr_has_unknown(value)
        }
        K::BufAtomic {
            buf, index, args, ..
        } => hir_expr_has_unknown(buf) || hir_expr_has_unknown(index) || any(args),
        K::MlirOp { args, regions, .. } => {
            any(args) || regions.iter().any(|(_, b)| hir_expr_has_unknown(b))
        }
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
                // A literal omitting the field fills it at the use site.
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
    // Codegen can't bitcast a primitive ↔ `[u8; N]` value yet
    // (mlir-translate rejects the cast): report it here rather than as
    // an opaque MLIR error.
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
        HirTy::GcBuf(_) => Some((8, 8)),
        HirTy::Never => Some((0, 1)),
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
        // Struct / enum sizes need the module: unknown, so the caller
        // reports the byte-array diagnostic.
        HirTy::Struct(_)
        | HirTy::Enum(_)
        | HirTy::Path(_)
        | HirTy::Unknown
        | HirTy::Any
        | HirTy::AnyTrait(_)
        | HirTy::Unit
        | HirTy::Fn(..)
        | HirTy::Closure { .. }
        | HirTy::Mlir(_)
        | HirTy::Throws { .. } => None,
    }
}

/// What a trait method's signature type depends on besides concrete
/// types: `Self`, an associated type `X` (bare, spec 2.8, or `Self::X`;
/// pushed as `Self::X`) or a trait type parameter (by name).
fn ast_ty_needs(ty: &rokc_ast::Ty, params: &[&str], assoc: &[&str], out: &mut Vec<String>) {
    let kids: Vec<&rokc_ast::Ty> = match &ty.kind {
        AstTyKind::SelfUpper => {
            out.push("Self".to_owned());
            Vec::new()
        }
        AstTyKind::Path(p) => {
            match p.segments.as_slice() {
                [s, x, ..] if s.name == "Self" => out.push(format!("Self::{}", x.name)),
                [s] | [s, _] if assoc.contains(&s.name.as_str()) => {
                    out.push(format!("Self::{}", s.name));
                }
                [s, ..] if s.name == "Self" || params.contains(&s.name.as_str()) => {
                    out.push(s.name.clone());
                }
                _ => {}
            }
            p.segments.iter().flat_map(|s| &s.generics).collect()
        }
        AstTyKind::AnyTrait(bounds) => bounds
            .iter()
            .flat_map(|b| b.segments.iter().flat_map(|s| &s.generics))
            .collect(),
        AstTyKind::Sum(parts) | AstTyKind::Tuple(parts) => parts.iter().collect(),
        AstTyKind::Fn(args, ret, _) => args.iter().chain(std::iter::once(&**ret)).collect(),
        AstTyKind::Throws { ok, err } => vec![&**ok, &**err],
        AstTyKind::Array(elem, _) => vec![&**elem],
        AstTyKind::Any | AstTyKind::None | AstTyKind::Never | AstTyKind::Const(_) => Vec::new(),
    };
    for k in kids {
        ast_ty_needs(k, params, assoc, out);
    }
}

fn is_throwing(t: &rokc_ast::ThrowsKind) -> bool {
    match t {
        rokc_ast::ThrowsKind::None => false,
        rokc_ast::ThrowsKind::Untyped => true,
        rokc_ast::ThrowsKind::Typed(v) => !v.is_empty(),
    }
}

/// `impl<..> Tr for Target` as a set of method templates (the trait's
/// default bodies included), each monomorphized per receiver like a
/// generic-impl inherent method.
fn generic_trait_impl(
    impl_def: &rokc_ast::ImplDef,
    trait_key: String,
    trait_def: Option<&rokc_ast::TraitDef>,
    module: &str,
    index: usize,
    diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> GenericTraitImpl {
    let err = |pre: &mut Vec<rokc_diagnostic::RokDiagnostic>, msg: String| {
        pre.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            msg,
        ));
    };
    let target_display = impl_def_display(&impl_def.self_ty);
    let assoc = impl_assoc_types(impl_def);
    let template = |m: &FnDef, def_module: &str| {
        let mut def = m.clone();
        subst_assoc_sig(&mut def, &assoc);
        let leaf = leaf_name(&m.name);
        // `__impl3_show` is both the mono cache key and the name
        // diagnostics print.
        def.name = if def_module.is_empty() {
            format!("__impl{index}_{leaf}")
        } else {
            format!("{def_module}::__impl{index}_{leaf}")
        };
        // The method's own (assoc-substituted) generics after the impl's.
        def.generics.params = [&impl_def.generics.params, &def.generics.params]
            .into_iter()
            .flatten()
            .cloned()
            .collect();
        def.where_clause = [&impl_def.where_clause, &def.where_clause]
            .into_iter()
            .flatten()
            .cloned()
            .collect();
        GenericMethod {
            def,
            self_ty: impl_def.self_ty.clone(),
            info: MethodInfo {
                module: def_module.to_owned(),
                vis: Visibility::Pub,
                trait_name: (!trait_key.is_empty()).then(|| trait_key.clone()),
            },
        }
    };
    let mut methods: HashMap<String, GenericMethod> = HashMap::new();
    for ii in &impl_def.items {
        let AstImplItem::Method(m) = ii else {
            continue;
        };
        let leaf = leaf_name(&m.name).to_owned();
        if let Some(td) = trait_def {
            let in_trait = td
                .items
                .iter()
                .any(|ti| matches!(ti, rokc_ast::TraitItem::Method(tm) if tm.name == leaf));
            if !in_trait {
                err(
                    diags,
                    format!("method `{leaf}` is not a member of trait `{}`", td.name),
                );
            }
        }
        if methods.insert(leaf.clone(), template(m, module)).is_some() {
            err(
                diags,
                format!("method `{leaf}` is defined more than once for `{target_display}`"),
            );
        }
    }
    if let Some(td) = trait_def {
        let trait_module = module_of(&td.name);
        for ti in &td.items {
            let rokc_ast::TraitItem::Method(tm) = ti else {
                continue;
            };
            if methods.contains_key(&tm.name) {
                continue;
            }
            if tm.body.is_none() {
                err(
                    diags,
                    format!(
                        "impl of trait `{}` for `{target_display}` is missing method `{}`",
                        td.name, tm.name
                    ),
                );
                continue;
            }
            methods.insert(tm.name.clone(), template(tm, &trait_module));
        }
    }
    GenericTraitImpl {
        trait_key,
        trait_args: impl_def
            .trait_path
            .as_ref()
            .and_then(|tp| tp.segments.last())
            .map(|s| s.generics.clone())
            .unwrap_or_default(),
        assoc: impl_def
            .items
            .iter()
            .filter_map(|i| match i {
                AstImplItem::AssocType { name, ty } => Some((name.clone(), ty.clone())),
                _ => None,
            })
            .collect(),
        generics: impl_def.generics.clone(),
        where_clause: impl_def.where_clause.clone(),
        self_ty: impl_def.self_ty.clone(),
        module: module.to_owned(),
        methods,
    }
}

/// `(Type::NAME, type, value)` for an impl's consts plus, in a trait
/// impl, the trait's defaults it leaves out. The key uses the generic
/// base (`Box::N` for `impl<T> Box<T>`) or a primitive's name.
// One key per base type: two impls of a generic base (`Box<i32>`,
// `Box<f64>`) can't give the same const different values.
fn impl_consts(
    i: &rokc_ast::ImplDef,
    program: &Program,
    names: &TypeNames<'_>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> (Vec<(String, Ty, Expr)>, Option<ImplConsts>) {
    let mut out: Vec<(String, Ty, Expr)> = i
        .items
        .iter()
        .filter_map(|it| match it {
            AstImplItem::Const(c) => {
                Some((leaf_name(&c.name).to_owned(), c.ty.clone(), c.value.clone()))
            }
            _ => None,
        })
        .collect();
    let module = impl_module(i);
    let trait_def = i.trait_path.as_ref().and_then(|tp| {
        let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
        let key = names.trait_key(&segs, &module);
        program.items.iter().find_map(|it| match it {
            Item::Trait(t)
                if t.name == key || (!key.contains("::") && leaf_name(&t.name) == key) =>
            {
                Some(t)
            }
            _ => None,
        })
    });
    if let Some(t) = trait_def.filter(|_| !i.negative) {
        for ti in &t.items {
            let rokc_ast::TraitItem::Const { name, ty, default } = ti else {
                continue;
            };
            if out.iter().any(|(n, ..)| n == name) {
                continue;
            }
            match default {
                Some(v) => out.push((name.clone(), ty.clone(), v.clone())),
                None => pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "impl of `{}` for `{}` is missing associated const `{name}` \
                         (spec 2.8.3a)",
                        leaf_name(&t.name),
                        impl_def_display(&i.self_ty)
                    ),
                )),
            }
        }
    }
    if out.is_empty() {
        return (out, None);
    }
    let params: Vec<&str> = i
        .generics
        .params
        .iter()
        .filter_map(|gp| match gp {
            rokc_ast::GenericParam::Type { name, .. } => Some(name.as_str()),
            rokc_ast::GenericParam::Const { .. } => None,
        })
        .collect();
    // `Type::N` names the const when the impl covers that one type, or
    // every instance of a generic base (`impl<T> Boxed<T>`, inherent);
    // the rest (`impl Tr for Box<i32>`, blanket `impl<T: X> Tr for T`)
    // are found from a concrete type (`T::N`, `Self::N`, `<T as Tr>::N`).
    let keyed_target = match &i.self_ty.kind {
        AstTyKind::Path(p) => {
            let args = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
            let all_params = args.len() == params.len()
                && args.iter().zip(&params).all(|(a, n)| {
                    matches!(&a.kind, AstTyKind::Path(ap)
                        if ap.segments.len() == 1 && ap.segments[0].name == *n)
                });
            if let HirTy::Prim(prim) = resolve_ty(&i.self_ty) {
                Some(prim.name().to_owned())
            } else if (params.is_empty() && args.is_empty())
                || (i.trait_path.is_none() && !args.is_empty() && all_params)
            {
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                names.canon(&segs, &module, &[])
            } else {
                None
            }
        }
        _ => None,
    };
    let trait_key = i.trait_path.as_ref().map_or_else(String::new, |tp| {
        let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
        names.trait_key(&segs, &module)
    });
    let set = ImplConsts {
        target: GenericTraitImpl {
            trait_key,
            trait_args: Vec::new(),
            assoc: Vec::new(),
            generics: i.generics.clone(),
            where_clause: i.where_clause.clone(),
            self_ty: i.self_ty.clone(),
            module,
            methods: HashMap::new(),
        },
        consts: out.clone(),
    };
    let keyed = keyed_target.map_or_else(Vec::new, |t| {
        out.into_iter()
            .map(|(n, ty, v)| (format!("{t}::{n}"), ty, v))
            .collect()
    });
    (keyed, Some(set))
}

/// Lower declaration `i` (`stub`: its signature only).
pub(super) fn lower_decl(env: &Env<'_>, i: usize, stub: bool) -> HirFunction {
    let id = FunctionId(u32::try_from(i).expect("FunctionId overflow"));
    let (MethodOrFn::Fn(f) | MethodOrFn::Method { fn_def: f, .. }) = &env.decls[i];
    let bodiless;
    let f: &FnDef = if stub {
        bodiless = FnDef {
            vis: f.vis,
            attrs: f.attrs.clone(),
            name: f.name.clone(),
            generics: f.generics.clone(),
            params: f.params.clone(),
            ret_ty: f.ret_ty.clone(),
            body: None,
            is_async: f.is_async,
            is_generator: f.is_generator,
            is_unsafe: f.is_unsafe,
            throws: f.throws.clone(),
            where_clause: f.where_clause.clone(),
            span: f.span,
        };
        &bodiless
    } else {
        f
    };
    match &env.decls[i] {
        MethodOrFn::Fn(_) => lower_fn(env, f, id, None, module_of(&f.name)),
        MethodOrFn::Method {
            self_ty,
            module,
            key,
            subst,
            ..
        } => super::mono::lower_fn_inner(
            env,
            f,
            id,
            key.clone(),
            Some(self_ty.clone()),
            module.clone(),
            subst,
        ),
    }
}

/// Pass 3: function bodies. The `roots` (user code, exports, lazy static
/// initializers) are lowered, then every decl a lowered body names —
/// calls, `fn` values, closures, coroutines; f-string helpers, operator
/// traits, iterator protocols and `any` dispatchers all resolve to these
/// — lowest id first, so user code keeps its order. A library body never
/// reached stays a body-less stub (its signature, for tools) and is
/// listed as unlowered (MIR drops it). `--check-library` lowers (and so
/// checks) every library body.
// No cache of library HIR across runs.
fn lower_bodies(env: &Env<'_>, roots: &[bool]) -> (Vec<HirFunction>, Vec<FunctionId>) {
    let decls = &env.decls;
    let lower = |i: usize, stub: bool| lower_decl(env, i, stub);
    let mut done: Vec<Option<HirFunction>> = (0..decls.len()).map(|_| None).collect();
    let mut pending: std::collections::BTreeSet<usize> =
        (0..decls.len()).filter(|&i| roots[i]).collect();
    let named = |f: &HirFunction, pending: &mut std::collections::BTreeSet<usize>| {
        let Some(body) = &f.body else { return };
        crate::each_block(body, &mut |e| {
            if let HirExprKind::Call { callee: id, .. }
            | HirExprKind::FnRef(id)
            | HirExprKind::ClosureValue { fn_id: id, .. }
            | HirExprKind::CoroNew { body_fn: id, .. } = &e.kind
            {
                pending.insert(id.0 as usize);
            }
        });
    };
    // Lifted closures / monomorphizations / dispatchers already looked at.
    let mut scanned = 0;
    loop {
        while let Some(i) = pending.pop_first() {
            if done.get(i).is_none_or(Option::is_some) {
                continue; // an extra (already lowered) or a done decl
            }
            let f = lower(i, false);
            named(&f, &mut pending);
            done[i] = Some(f);
            let extras = env.sink.extras.borrow();
            extras[scanned..]
                .iter()
                .for_each(|f| named(f, &mut pending));
            scanned = extras.len();
        }
        build_any_dispatchers(env);
        let extras = env.sink.extras.borrow();
        extras[scanned..]
            .iter()
            .for_each(|f| named(f, &mut pending));
        drop(extras);
        pending.retain(|&i| done.get(i).is_some_and(Option::is_none));
        if pending.is_empty() {
            break;
        }
        // The new bodies may add `any` tags: drop the dispatchers (the
        // last ones in) and build them again after.
        let n = env.sink.any_dispatch.borrow().len();
        let mut extras = env.sink.extras.borrow_mut();
        scanned = extras.len() - n;
        extras.truncate(scanned);
    }
    let mut unlowered = Vec::new();
    let functions = done
        .into_iter()
        .enumerate()
        .map(|(i, f)| {
            f.unwrap_or_else(|| {
                let stub = lower(i, true);
                unlowered.push(stub.id);
                stub
            })
        })
        .collect();
    (functions, unlowered)
}

/// Spec 6.2.1 / stdlib 2.5.9, 2.13.3: `#[derive(Tr)]` needs every field
/// to implement `Tr` (checked here on non-generic types; a generic one's
/// impl bounds its parameters by `Tr`), and `Copy` excludes `Drop`.
fn check_derives(env: &Env<'_>, program: &Program) {
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None);
    for item in &program.items {
        let (attrs, name, generic, fields): (_, _, _, Vec<(String, HirTy)>) = match item {
            Item::Struct(s) => (
                &s.attrs,
                &s.name,
                !s.generics.params.is_empty(),
                env.struct_table.get(&s.name).map_or_else(Vec::new, |id| {
                    ctx.struct_def(*id)
                        .fields
                        .iter()
                        .map(|f| (f.name.clone(), f.ty.clone()))
                        .collect()
                }),
            ),
            Item::Enum(e) => (
                &e.attrs,
                &e.name,
                !e.generics.params.is_empty(),
                env.enum_table.get(&e.name).map_or_else(Vec::new, |id| {
                    ctx.enum_def(*id)
                        .variants
                        .iter()
                        .flat_map(|v| {
                            super::expr::variant_arg_tys(v)
                                .into_iter()
                                .map(|t| (v.name.clone(), t))
                        })
                        .collect()
                }),
            ),
            _ => continue,
        };
        if generic {
            continue;
        }
        let self_ty = match item {
            Item::Struct(s) => env.struct_table.get(&s.name).map(|id| HirTy::Struct(*id)),
            Item::Enum(e) => env.enum_table.get(&e.name).map(|id| HirTy::Enum(*id)),
            _ => None,
        };
        for (tr, at) in rokc_parser::derive::derive_names(attrs) {
            let Some(key) = rokc_parser::derive::derivable(&tr) else {
                continue;
            };
            rokc_diagnostic::set_current_span(at);
            for (field, ty) in &fields {
                if !ctx.implements_trait(ty, key, 0) {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Meta,
                        format!(
                            "cannot derive `{tr}` for `{}`: `{field}` has type `{}`, which does \
                             not implement `{tr}` (spec 6.2.1)",
                            leaf_name(name),
                            ctx.ty_name(ty)
                        ),
                    );
                }
            }
            if tr == "Copy"
                && self_ty
                    .as_ref()
                    .is_some_and(|t| ctx.implements_trait(t, ctx.lang_trait("drop_method"), 0))
            {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Meta,
                    format!(
                        "cannot derive `Copy` for `{}`: it implements `Drop` (stdlib 2.13.3)",
                        leaf_name(name)
                    ),
                );
            }
        }
    }
}

/// Every trait named in a bound position — generic parameters, `where`
/// clauses, supertraits, `impl Tr for` — must exist (`any Tr` and
/// `fn() + Tr` check their own).
fn check_bound_names(
    program: &Program,
    names: &TypeNames<'_>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) {
    let mut check = |b: &Ty, module: &str| {
        let AstTyKind::Path(p) = &b.kind else {
            return;
        };
        let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
        let key = names.trait_key(&segs, module);
        // A bootstrap trait keys by its leaf (see `trait_key`).
        if names.traits.contains(&key) || names.traits.iter().any(|t| leaf_name(t) == key) {
            return;
        }
        rokc_diagnostic::set_current_span(b.span);
        pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Resolve,
            format!("cannot find trait `{}` (named in a bound)", segs.join("::")),
        ));
    };
    let mut generics = |g: &rokc_ast::Generics, w: &[rokc_ast::WherePred], module: &str| {
        for gp in &g.params {
            if let rokc_ast::GenericParam::Type { bounds, .. } = gp {
                bounds.iter().for_each(|b| check(b, module));
            }
        }
        for p in w {
            p.bounds.iter().for_each(|b| check(b, module));
        }
    };
    let fn_bounds =
        |f: &FnDef, generics: &mut dyn FnMut(&rokc_ast::Generics, &[rokc_ast::WherePred], &str)| {
            generics(&f.generics, &f.where_clause, &module_of(&f.name));
        };
    let mut impl_paths: Vec<(Ty, String)> = Vec::new();
    for item in &program.items {
        let module = item_module(item);
        match item {
            Item::Fn(f) => fn_bounds(f, &mut generics),
            Item::Struct(s) => generics(&s.generics, &s.where_clause, &module),
            Item::Enum(e) => generics(&e.generics, &e.where_clause, &module),
            Item::Union(u) => generics(&u.generics, &u.where_clause, &module),
            Item::TypeAlias(a) => generics(&a.generics, &a.where_clause, &module),
            Item::Trait(t) => {
                generics(&t.generics, &t.where_clause, &module);
                for s in &t.supertraits {
                    impl_paths.push((s.clone(), module.clone()));
                }
                for ti in &t.items {
                    match ti {
                        rokc_ast::TraitItem::Method(m) => fn_bounds(m, &mut generics),
                        rokc_ast::TraitItem::AssocType { bounds, .. } => {
                            impl_paths.extend(bounds.iter().map(|b| (b.clone(), module.clone())));
                        }
                        rokc_ast::TraitItem::Const { .. } => {}
                    }
                }
            }
            Item::Impl(i) => {
                let module = impl_module(i);
                generics(&i.generics, &i.where_clause, &module);
                if let Some(tp) = &i.trait_path {
                    impl_paths.push((
                        Ty {
                            kind: AstTyKind::Path(tp.clone()),
                            span: tp.span,
                        },
                        module.clone(),
                    ));
                }
                for ii in &i.items {
                    if let AstImplItem::Method(m) = ii {
                        fn_bounds(m, &mut generics);
                    }
                }
            }
            _ => {}
        }
    }
    for (t, module) in &impl_paths {
        check(t, module);
    }
}

/// Spec 2.10.4: every generic struct / union / enum instantiation must
/// meet its parameters' bounds, inline (`T: Tr`) and `where` alike.
fn check_type_bounds(env: &Env<'_>) {
    // (display name, item's module, arguments, generics, `where`, use site)
    type Inst<'d> = (
        String,
        String,
        Vec<HirTy>,
        &'d rokc_ast::Generics,
        &'d [rokc_ast::WherePred],
        rokc_diagnostic::Span,
    );
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None);
    let n_structs = env.structs.len() + env.sink.extra_structs.borrow().len();
    let n_enums = env.enums.len() + env.sink.extra_enums.borrow().len();
    let mut insts: Vec<Inst<'_>> = Vec::new();
    for i in 0..n_structs {
        let id = StructId(u32::try_from(i).expect("StructId overflow"));
        let d = ctx.struct_def(id);
        let base = d.name.split("__").next().unwrap_or_default().to_owned();
        if let Some(def) = env
            .generic_structs
            .get(&base)
            .filter(|_| !d.generic_args.is_empty())
        {
            insts.push((
                ctx.ty_name(&HirTy::Struct(id)),
                module_of(&base),
                d.generic_args,
                &def.generics,
                &def.where_clause,
                d.span,
            ));
        }
    }
    for i in 0..n_enums {
        let id = EnumId(u32::try_from(i).expect("EnumId overflow"));
        let d = ctx.enum_def(id);
        let base = enum_base_name(&d.name).to_owned();
        if let Some(def) = env
            .generic_enums
            .get(&base)
            .filter(|_| !d.generic_args.is_empty())
        {
            insts.push((
                ctx.ty_name(&HirTy::Enum(id)),
                module_of(&base),
                d.generic_args,
                &def.generics,
                &def.where_clause,
                d.span,
            ));
        }
    }
    // Spec 2.10.4: a non-generic alias's `where` holds once (at the
    // alias); a generic alias's bounds hold at each use.
    for (full, def) in &env.names.generic_aliases {
        if def.generics.params.is_empty() {
            insts.push((
                leaf_name(full).to_owned(),
                module_of(full),
                Vec::new(),
                &def.generics,
                &def.where_clause,
                def.span,
            ));
        }
    }
    let uses = env.names.alias_uses.borrow().clone();
    for (full, args, module, span) in uses {
        let Some(def) = env.names.generic_aliases.get(&full) else {
            continue;
        };
        let sc = Scope {
            names: &env.names,
            module: &module,
        };
        let mut rcx = LowerCtx::new(env, &no_subst, None);
        rcx.current_module.clone_from(&module);
        let args: Vec<HirTy> = def
            .generics
            .params
            .iter()
            .zip(&args)
            .map(|(gp, a)| match (gp, &a.kind) {
                (rokc_ast::GenericParam::Const { .. }, AstTyKind::Const(c)) => rcx
                    .eval_const(c)
                    .map_or(HirTy::Unknown, |v| crate::ty::const_ty(v, None)),
                _ => resolve_ty_with_structs(a, &env.struct_table, &env.enum_table, sc),
            })
            .collect();
        let shown: Vec<String> = args.iter().map(|a| ctx.ty_name(a)).collect();
        insts.push((
            format!("{}<{}>", leaf_name(&full), shown.join(", ")),
            module_of(&full),
            args,
            &def.generics,
            &def.where_clause,
            span,
        ));
    }
    for (shown, module, args, generics, where_clause, span) in insts {
        let subst = generic_subst(generics, &args);
        let mut rcx = LowerCtx::new(env, &subst, None);
        rcx.current_module = module;
        let mut goals: Vec<(HirTy, &Vec<Ty>)> = Vec::new();
        for gp in &generics.params {
            if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
                if let Some(t) = subst.get(name) {
                    goals.push((t.clone(), bounds));
                }
            }
        }
        for w in where_clause {
            goals.push((rcx.resolve_ast_ty(&w.ty), &w.bounds));
        }
        for (ty, bounds) in goals {
            if ty == HirTy::Unknown {
                continue;
            }
            for b in bounds {
                let AstTyKind::Path(p) = &b.kind else {
                    continue;
                };
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                let (targs, binds) = split_trait_args(
                    p.segments.last().map_or(&[][..], |s| s.generics.as_slice()),
                    |t| rcx.resolve_ast_ty(t),
                );
                let key = bound_key(
                    env.names.trait_key(&segs, &rcx.current_module),
                    &targs,
                    &binds,
                    &env.struct_table,
                    &env.enum_table,
                );
                if !rcx.implements_trait(&ty, &key, 0) {
                    let old = rokc_diagnostic::set_current_span(span);
                    rcx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "type `{}` does not satisfy trait bound `{key}` required by `{shown}` \
                             (spec 2.10.4)",
                            rcx.ty_name(&ty),
                        ),
                    );
                    rokc_diagnostic::set_current_span(old);
                }
            }
        }
    }
}

/// A type has at most one impl of a trait (spec 2.9.3): a concrete impl
/// that a generic impl also covers is a duplicate (no specialization).
fn check_impl_overlap(env: &Env<'_>) {
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None);
    for gi in &env.generic_trait_impls {
        for ty in env.trait_impl_tys.get(&gi.trait_key).into_iter().flatten() {
            if ctx.generic_impl_subst(gi, ty, 0).is_some() {
                rokc_diagnostic::set_current_span(gi.self_ty.span);
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "conflicting implementations of trait `{}` for `{}`: the concrete \
                         impl overlaps `impl<..> {} for {}` (spec 2.9.3 — one impl per \
                         trait and type; no specialization)",
                        gi.trait_key,
                        ctx.ty_name(ty),
                        gi.trait_key,
                        impl_def_display(&gi.self_ty)
                    ),
                );
            }
        }
    }
    // Two generic impls conflict when their targets (and trait
    // arguments) unify — bounds on what stays generic don't separate
    // them (`impl<T: A> X for T` / `impl<T: B> X for T` clash even if
    // no type is `A + B` yet). Targets beyond `symbolic_overlap` fall
    // back to a witness among the types the program names.
    let gis = &env.generic_trait_impls;
    let mut candidates: Option<Vec<HirTy>> = None;
    for (i, a) in gis.iter().enumerate() {
        // Inherent ones (empty key) clash when they share a method name.
        let shared = |b: &GenericTraitImpl| {
            let mut m: Vec<&String> = a
                .methods
                .keys()
                .filter(|k| b.methods.contains_key(*k))
                .collect();
            m.sort();
            m.first().map(|s| (*s).clone())
        };
        for b in gis.iter().skip(i + 1).filter(|b| {
            b.trait_key == a.trait_key && (!a.trait_key.is_empty() || shared(b).is_some())
        }) {
            let witness = symbolic_overlap(&ctx, a, b).unwrap_or_else(|| {
                let cands = candidates.get_or_insert_with(|| named_types(env));
                cands
                    .iter()
                    .find(|t| {
                        ctx.generic_impl_subst(a, t, 0).is_some()
                            && ctx.generic_impl_subst(b, t, 0).is_some()
                    })
                    .map(|t| ctx.ty_name(t))
            });
            if let (Some(t), Some(m)) = (
                &witness,
                a.trait_key.is_empty().then(|| shared(b)).flatten(),
            ) {
                rokc_diagnostic::set_current_span(b.self_ty.span);
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "duplicate method `{m}`: `impl<..> {}` and `impl<..> {}` both define it \
                         for `{t}` (bounds don't make impls disjoint)",
                        impl_def_display(&a.self_ty),
                        impl_def_display(&b.self_ty),
                    ),
                );
            } else if let Some(t) = witness {
                rokc_diagnostic::set_current_span(b.self_ty.span);
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "conflicting implementations of trait `{}`: `impl<..> {} for {}` and \
                         `impl<..> {} for {}` overlap on `{t}` — bounds don't make impls \
                         disjoint (spec 2.9.5 coherence; no specialization)",
                        a.trait_key,
                        a.trait_key,
                        impl_def_display(&a.self_ty),
                        b.trait_key,
                        impl_def_display(&b.self_ty),
                    ),
                );
            }
        }
    }
}

/// Concrete impl targets and generic struct / enum instantiations: the
/// witnesses for impl targets `symbolic_overlap` can't read.
fn named_types(env: &Env<'_>) -> Vec<HirTy> {
    let mut out: Vec<HirTy> = Vec::new();
    let named = env.trait_impl_tys.values().flatten().cloned();
    let structs = env
        .structs
        .iter()
        .filter(|s| !s.generic_args.is_empty())
        .map(|s| HirTy::Struct(s.id));
    let enums = env
        .enums
        .iter()
        .filter(|e| !e.generic_args.is_empty())
        .map(|e| HirTy::Enum(e.id));
    for t in named.chain(structs).chain(enums) {
        if !out.contains(&t) {
            out.push(t);
        }
    }
    out
}

/// Whether two generic impls of one trait overlap, structurally: unify
/// their targets (and trait arguments) with the impl parameters as
/// variables. Bounds on a type left generic are assumed satisfiable
/// (coherence is open-world); a bound on a parameter the unification
/// made concrete (`i32: A`) is checked, as for a concrete impl.
/// `Some(Some(shown))` overlaps on `shown`, `Some(None)` is disjoint,
/// `None` is a target this check can't read (fn types, aliases ..).
#[allow(clippy::option_option)] // overlap / disjoint / can't tell
fn symbolic_overlap(
    ctx: &LowerCtx<'_>,
    a: &GenericTraitImpl,
    b: &GenericTraitImpl,
) -> Option<Option<String>> {
    let names = |gi: &GenericTraitImpl, tag: &str| -> HashMap<String, String> {
        gi.generics
            .params
            .iter()
            .map(|gp| match gp {
                rokc_ast::GenericParam::Type { name, .. }
                | rokc_ast::GenericParam::Const { name, .. } => {
                    (name.clone(), format!("{tag}{name}"))
                }
            })
            .collect()
    };
    let (va, vb) = (names(a, "#a."), names(b, "#b."));
    let canon = |gi: &GenericTraitImpl, vars: &HashMap<String, String>, t: &Ty| {
        canon_ast_ty(ctx, &gi.module, vars, t)
    };
    let a_self = canon(a, &va, &a.self_ty)?;
    let b_self = canon(b, &vb, &b.self_ty)?;
    if a.trait_args.len() != b.trait_args.len() {
        return Some(None);
    }
    let mut args = Vec::new();
    for (x, y) in a.trait_args.iter().zip(&b.trait_args) {
        args.push((canon(a, &va, x)?, canon(b, &vb, y)?));
    }
    let mut u = Unifier::default();
    if u.unify(&a_self, &b_self).is_none() || args.iter().any(|(x, y)| u.unify(x, y).is_none()) {
        return Some(None);
    }
    // Bounds whose subject the unification gave a type constructor:
    // negative reasoning on known types (`List<T>: Iterator` fails when
    // no impl of `Iterator` targets `List`). A subject still a bare
    // variable is open — some type may meet any bounds.
    for (gi, vars) in [(a, &va), (b, &vb)] {
        let mut goals: Vec<(CanonTy, &Vec<Ty>)> = Vec::new();
        for gp in &gi.generics.params {
            if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
                goals.push((u.resolve(&vars[name]), bounds));
            }
        }
        for w in &gi.where_clause {
            if let Some(t) = canon(gi, vars, &w.ty) {
                goals.push((u.walk(&t), &w.bounds));
            }
        }
        for (subject, bounds) in goals {
            if matches!(subject, CanonTy::Var(_)) {
                continue;
            }
            for bound in bounds {
                let AstTyKind::Path(bp) = &bound.kind else {
                    continue;
                };
                if bp.segments.iter().any(|s| !s.generics.is_empty()) {
                    continue;
                }
                let segs: Vec<&str> = bp.segments.iter().map(|s| s.name.as_str()).collect();
                let key = ctx.env.names.trait_key(&segs, &gi.module);
                if !may_implement(ctx, &subject, &key) {
                    return Some(None);
                }
            }
        }
    }
    Some(Some(u.walk(&a_self).to_string()))
}

/// Whether `subject` (not a bare variable) may implement trait `key`: a
/// concrete type is asked directly; one with variables does when some
/// impl of `key` targets its constructor (`List<..>`, a 2-tuple ..) or
/// a bare parameter.
fn may_implement(ctx: &LowerCtx<'_>, subject: &CanonTy, key: &str) -> bool {
    if let Some(t) = canon_hir(ctx, subject) {
        return ctx.implements_trait(&t, key, 0);
    }
    let head = canon_head(subject);
    let env = ctx.env;
    let concrete = env.trait_impl_tys.get(key).into_iter().flatten().any(|t| {
        let h = match t {
            HirTy::Struct(id) => enum_base_name(&ctx.struct_def(*id).name).to_owned(),
            HirTy::Enum(id) => enum_base_name(&ctx.enum_def(*id).name).to_owned(),
            HirTy::Tuple(ts) => format!("({})", ts.len()),
            HirTy::Array(..) => "[]".to_owned(),
            HirTy::Sum(_) => "|".to_owned(),
            _ => return false,
        };
        h == head
    });
    concrete
        || env
            .generic_trait_impls
            .iter()
            .filter(|gi| gi.trait_key == key)
            .any(|gi| {
                let vars = gi
                    .generics
                    .params
                    .iter()
                    .filter_map(|gp| match gp {
                        rokc_ast::GenericParam::Type { name, .. } => {
                            Some((name.clone(), format!("#c.{name}")))
                        }
                        rokc_ast::GenericParam::Const { .. } => None,
                    })
                    .collect();
                match canon_ast_ty(ctx, &gi.module, &vars, &gi.self_ty) {
                    Some(CanonTy::Var(_)) | None => true,
                    Some(t) => canon_head(&t) == head,
                }
            })
}

/// A type's constructor for `may_implement`: a path's name, `(n)` for an
/// n-tuple, `[]`, `|`.
fn canon_head(t: &CanonTy) -> String {
    match t {
        CanonTy::Named(n, _) => n.clone(),
        CanonTy::Tuple(ts) => format!("({})", ts.len()),
        CanonTy::Array(..) => "[]".to_owned(),
        CanonTy::Sum(_) => "|".to_owned(),
        CanonTy::Var(_) => String::new(),
    }
}

/// A type for `symbolic_overlap`: paths by canonical name, impl
/// parameters as variables.
#[derive(Clone, Debug, PartialEq)]
enum CanonTy {
    Var(String),
    Named(String, Vec<CanonTy>),
    Tuple(Vec<CanonTy>),
    /// Element and length (a literal `Named` or a const parameter).
    Array(Box<CanonTy>, Box<CanonTy>),
    Sum(Vec<CanonTy>),
}

fn canon_ast_ty(
    ctx: &LowerCtx<'_>,
    module: &str,
    vars: &HashMap<String, String>,
    t: &Ty,
) -> Option<CanonTy> {
    let rec = |t: &Ty| canon_ast_ty(ctx, module, vars, t);
    Some(match &t.kind {
        AstTyKind::Path(p) => {
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            if let ([one], true) = (segs.as_slice(), p.segments[0].generics.is_empty()) {
                if let Some(v) = vars.get(*one) {
                    return Some(CanonTy::Var(v.clone()));
                }
            }
            let name = ctx
                .env
                .names
                .canon(&segs, module, &[])
                .unwrap_or_else(|| segs.join("::"));
            let args = p
                .segments
                .last()
                .map_or(Some(Vec::new()), |s| s.generics.iter().map(rec).collect())?;
            CanonTy::Named(name, args)
        }
        AstTyKind::Tuple(ts) => CanonTy::Tuple(ts.iter().map(rec).collect::<Option<_>>()?),
        AstTyKind::Sum(ts) => CanonTy::Sum(ts.iter().map(rec).collect::<Option<_>>()?),
        AstTyKind::None => CanonTy::Named("none".to_owned(), Vec::new()),
        AstTyKind::Array(e, rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Int(n))) => {
            CanonTy::Array(
                Box::new(rec(e)?),
                Box::new(CanonTy::Named(n.clone(), Vec::new())),
            )
        }
        AstTyKind::Array(e, len) => {
            let p = match len {
                rokc_ast::ConstExpr::Path(p) => p,
                rokc_ast::ConstExpr::Expr(x) => match &x.kind {
                    ExprKind::Path(p) => p,
                    _ => return None,
                },
                rokc_ast::ConstExpr::Literal(_) => return None,
            };
            let [seg] = p.segments.as_slice() else {
                return None;
            };
            let v = vars.get(&seg.name)?;
            CanonTy::Array(Box::new(rec(e)?), Box::new(CanonTy::Var(v.clone())))
        }
        _ => return None,
    })
}

/// A concrete `CanonTy` as a type: a primitive or a non-generic struct
/// / enum; `None` for anything else (the bound check gives up).
fn canon_hir(ctx: &LowerCtx<'_>, t: &CanonTy) -> Option<HirTy> {
    let CanonTy::Named(name, args) = t else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    match crate::ty::resolve_ty(&Ty {
        kind: AstTyKind::Path(AstPath {
            segments: vec![rokc_ast::PathSegment {
                name: name.clone(),
                generics: Vec::new(),
            }],
            span: rokc_diagnostic::Span::default(),
        }),
        span: rokc_diagnostic::Span::default(),
    }) {
        p @ HirTy::Prim(_) => Some(p),
        _ => ctx
            .lookup_struct(name)
            .map(HirTy::Struct)
            .or_else(|| ctx.lookup_enum(name).map(HirTy::Enum)),
    }
}

impl std::fmt::Display for CanonTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let list =
            |ts: &[Self], sep: &str| ts.iter().map(Self::to_string).collect::<Vec<_>>().join(sep);
        match self {
            Self::Var(v) => write!(f, "{}", v.rsplit('.').next().unwrap_or(v)),
            Self::Named(n, args) if args.is_empty() => {
                write!(f, "{}", n.rsplit("::").next().unwrap_or(n))
            }
            Self::Named(n, args) => {
                write!(
                    f,
                    "{}<{}>",
                    n.rsplit("::").next().unwrap_or(n),
                    list(args, ", ")
                )
            }
            Self::Tuple(ts) => write!(f, "({})", list(ts, ", ")),
            Self::Sum(ts) => write!(f, "{}", list(ts, " | ")),
            Self::Array(e, n) => write!(f, "[{e}; {n}]"),
        }
    }
}

/// First-order unification over `CanonTy` (no occurs check: the two
/// impls' variables are distinct).
#[derive(Default)]
struct Unifier {
    sub: HashMap<String, CanonTy>,
}

impl Unifier {
    fn resolve(&self, v: &str) -> CanonTy {
        match self.sub.get(v) {
            Some(CanonTy::Var(w)) => self.resolve(w),
            Some(t) => self.walk(t),
            None => CanonTy::Var(v.to_owned()),
        }
    }

    fn walk(&self, t: &CanonTy) -> CanonTy {
        match t {
            CanonTy::Var(v) => self.resolve(v),
            CanonTy::Named(n, args) => {
                CanonTy::Named(n.clone(), args.iter().map(|a| self.walk(a)).collect())
            }
            CanonTy::Tuple(ts) => CanonTy::Tuple(ts.iter().map(|a| self.walk(a)).collect()),
            CanonTy::Sum(ts) => CanonTy::Sum(ts.iter().map(|a| self.walk(a)).collect()),
            CanonTy::Array(e, n) => CanonTy::Array(Box::new(self.walk(e)), Box::new(self.walk(n))),
        }
    }

    #[allow(clippy::many_single_char_names)]
    fn unify(&mut self, x: &CanonTy, y: &CanonTy) -> Option<()> {
        match (self.walk(x), self.walk(y)) {
            (CanonTy::Var(v), CanonTy::Var(w)) if v == w => Some(()),
            (CanonTy::Var(v), t) | (t, CanonTy::Var(v)) => {
                self.sub.insert(v, t);
                Some(())
            }
            (CanonTy::Named(n, xs), CanonTy::Named(m, ys)) if n == m && xs.len() == ys.len() => {
                xs.iter().zip(&ys).try_for_each(|(p, q)| self.unify(p, q))
            }
            (CanonTy::Tuple(xs), CanonTy::Tuple(ys)) if xs.len() == ys.len() => {
                xs.iter().zip(&ys).try_for_each(|(p, q)| self.unify(p, q))
            }
            (CanonTy::Array(p, n), CanonTy::Array(q, m)) => {
                self.unify(&n, &m)?;
                self.unify(&p, &q)
            }
            // Sums only unify member-for-member in written order.
            (CanonTy::Sum(xs), CanonTy::Sum(ys)) if xs.len() == ys.len() => {
                xs.iter().zip(&ys).try_for_each(|(p, q)| self.unify(p, q))
            }
            _ => None,
        }
    }
}

/// Rules for impls of auto traits (`Send` / `Sync`): opting in is
/// `unsafe impl`; opting out is `impl !Tr for S` on a struct / enum,
/// recorded in `neg` as `(generic base, trait key)`. `unsafe impl` and
/// `!` are for auto traits only. Returns whether to go on registering
/// the impl like any other (false for opt-outs and errors).
fn check_auto_impl(
    impl_def: &rokc_ast::ImplDef,
    names: &TypeNames<'_>,
    module: &str,
    neg: &mut std::collections::HashSet<(String, String)>,
    diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> bool {
    let err = |d: &mut Vec<rokc_diagnostic::RokDiagnostic>, msg: String| {
        d.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            msg,
        ));
    };
    let Some(tp) = &impl_def.trait_path else {
        if impl_def.is_unsafe || impl_def.negative {
            err(diags, "`unsafe impl` / `impl !` needs a trait".to_owned());
        }
        return true;
    };
    let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
    let key = names.trait_key(&segs, module);
    let target = impl_def_display(&impl_def.self_ty);
    let tr = segs.join("::");
    if key == super::reflect::REFLECT {
        err(
            diags,
            format!(
                "`Reflect` is implemented by the compiler for every type; remove `impl {tr} for \
                 {target}` (spec 6.10.1)"
            ),
        );
        return false;
    }
    if !names.auto_traits.contains(&key) {
        if impl_def.is_unsafe || impl_def.negative {
            err(
                diags,
                format!(
                    "`{tr}` is not an auto trait — `unsafe impl` and `impl !Trait` are only \
                     for `Send` / `Sync`"
                ),
            );
            return false;
        }
        return true;
    }
    if impl_def.negative {
        let base = match &impl_def.self_ty.kind {
            AstTyKind::Path(p) => {
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                names.canon(&segs, module, &[])
            }
            _ => None,
        };
        match base {
            Some(b) if impl_def.items.is_empty() && !impl_def.is_unsafe => {
                neg.insert((b, key));
            }
            Some(_) => err(
                diags,
                format!("`impl !{tr} for {target}` takes no `unsafe` and has an empty body"),
            ),
            None => err(
                diags,
                format!("`impl !{tr}` target `{target}` must be a struct or enum"),
            ),
        }
        return false;
    }
    if !impl_def.is_unsafe {
        err(
            diags,
            format!(
                "`{tr}` is an auto trait the compiler derives from the fields; a manual \
                 impl for `{target}` must be `unsafe impl {tr} for {target} {{}}`"
            ),
        );
        return false;
    }
    true
}

/// Spec 5.9.10: an `extern "C" fn` definition is called from C — no
/// captures (it is an item), no generics, no `throws` (an error can't
/// cross into C; a panic aborts the process), and FFI types only (a
/// rok `str` is `(ptr, len)`, not a `char*`).
fn check_extern_c_fn(f: &FnDef, diags: &mut Vec<rokc_diagnostic::RokDiagnostic>) {
    let mut bad = |msg: String| {
        diags.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "`extern \"C\" fn {}`: {msg} (spec 5.9.10)",
                leaf_name(&f.name)
            ),
        ));
    };
    if !matches!(f.throws, rokc_ast::ThrowsKind::None) {
        bad("cannot `throws` — an error cannot cross into C".to_owned());
    }
    if !f.generics.params.is_empty() {
        bad("cannot be generic".to_owned());
    }
    if f.is_async || f.is_generator {
        bad("cannot be `async` / a generator".to_owned());
    }
    let is_str = |t: &rokc_ast::Ty| matches!(&t.kind, AstTyKind::Path(p) if p.segments.len() == 1 && p.segments[0].name == "str");
    if f.params
        .iter()
        .filter_map(|p| p.ty.as_ref())
        .chain(f.ret_ty.as_ref())
        .any(is_str)
    {
        bad("`str` is not an FFI type; pass a `Ptr<u8>` and a length".to_owned());
    }
}

/// `#[export_name("sym")]` (spec 905): the symbol it names.
fn export_name(f: &FnDef) -> Option<String> {
    let a = f.attrs.iter().find(|a| a.name() == "export_name")?;
    match &a.body {
        rokc_ast::AttrBody::Args(args) => args.iter().find_map(|x| match x {
            rokc_ast::AttrArg::Lit(rokc_ast::Literal::Str(s)) => Some(s.clone()),
            _ => None,
        }),
        _ => None,
    }
}

/// The slot a `#[lang("slot")]` attribute names.
fn lang_slot(a: &rokc_ast::Attribute) -> Option<String> {
    if a.name() != "lang" {
        return None;
    }
    match &a.body {
        rokc_ast::AttrBody::Args(args) => args.iter().find_map(|x| match x {
            rokc_ast::AttrArg::Lit(rokc_ast::Literal::Str(s)) => Some(s.clone()),
            _ => None,
        }),
        _ => None,
    }
}

/// `#[lang("send_trait")]` / `#[lang("sync_trait")]`: a structural
/// auto trait.
fn is_auto_trait_attr(a: &rokc_ast::Attribute) -> bool {
    a.name() == "lang"
        && matches!(&a.body, rokc_ast::AttrBody::Args(args) if args.iter().any(|x| matches!(
            x,
            rokc_ast::AttrArg::Lit(rokc_ast::Literal::Str(s)) if s == "send_trait" || s == "sync_trait"
        )))
}

/// `#[intrinsic("rok.OP.TYPE")]` (stdlib spec 0.3): calls of the method
/// become the primitive op; the body is only a fallback. Standard
/// library only (0.3.5).
fn intrinsic_of(
    m: &FnDef,
    module: &str,
    diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> Option<PrimOp> {
    let attr = m.attrs.iter().find(|a| a.name() == "intrinsic")?;
    let mut err = |msg: String| {
        diags.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Meta,
            msg,
        ));
        None
    };
    if !module.starts_with("rok::") {
        return err(format!(
            "`#[intrinsic]` on `{}`: the intrinsic attribute is for the standard library only \
             (stdlib spec 0.3.5)",
            m.name
        ));
    }
    let name = match &attr.body {
        rokc_ast::AttrBody::Args(args) => args.iter().find_map(|a| match a {
            rokc_ast::AttrArg::Lit(rokc_ast::Literal::Str(s)) => Some(s.clone()),
            _ => None,
        }),
        _ => None,
    };
    let op = name
        .as_deref()
        .and_then(|n| n.strip_prefix("rok."))
        .and_then(|n| n.split('.').next());
    let op = match op {
        Some("add") => PrimOp::Add,
        Some("sub") => PrimOp::Sub,
        Some("mul") => PrimOp::Mul,
        Some("div") => PrimOp::Div,
        Some("rem") => PrimOp::Rem,
        Some("and") => PrimOp::BitAnd,
        Some("or") => PrimOp::BitOr,
        Some("xor") => PrimOp::BitXor,
        Some("shl") => PrimOp::Shl,
        Some("shr") => PrimOp::Shr,
        Some("eq") => PrimOp::Eq,
        Some("ne") => PrimOp::Ne,
        Some("lt") => PrimOp::Lt,
        Some("le") => PrimOp::Le,
        Some("gt") => PrimOp::Gt,
        Some("ge") => PrimOp::Ge,
        Some("neg") => PrimOp::Neg,
        // Bitwise on integers, logical on `bool` (picked at the call).
        Some("not") => PrimOp::Not,
        Some("sqrt") => PrimOp::Sqrt,
        Some("wrapping_add") => PrimOp::WrappingAdd,
        Some("wrapping_sub") => PrimOp::WrappingSub,
        Some("wrapping_mul") => PrimOp::WrappingMul,
        Some("ctpop") => PrimOp::CountOnes,
        Some("ctlz") => PrimOp::LeadingZeros,
        Some("cttz") => PrimOp::TrailingZeros,
        Some("bswap") => PrimOp::SwapBytes,
        _ => {
            return err(format!(
                "`#[intrinsic({})]` on `{}`: unknown intrinsic — expected `rok.OP.TYPE` \
                 (stdlib spec 0.3.3)",
                name.map_or_else(String::new, |n| format!("\"{n}\"")),
                m.name
            ));
        }
    };
    let arity = if matches!(
        op,
        PrimOp::Neg
            | PrimOp::Not
            | PrimOp::Sqrt
            | PrimOp::CountOnes
            | PrimOp::LeadingZeros
            | PrimOp::TrailingZeros
            | PrimOp::SwapBytes
    ) {
        1
    } else {
        2
    };
    if m.params.len() != arity {
        return err(format!(
            "`#[intrinsic]` on `{}`: the op takes {arity} operand(s)",
            m.name
        ));
    }
    Some(op)
}

/// An impl's associated types: `type Item = T;` → `Item ↦ T`.
fn impl_assoc_types(impl_def: &rokc_ast::ImplDef) -> HashMap<String, Ty> {
    impl_def
        .items
        .iter()
        .filter_map(|i| match i {
            AstImplItem::AssocType { name, ty } => Some((name.clone(), ty.clone())),
            _ => None,
        })
        .collect()
}

/// The value of a trait's const argument: a literal, a `const` item
/// (`W`, looked up from `module` then the root) or a braced const
/// expression over those (`{ W + 1 }`).
fn const_arg_value(t: &Ty, consts: &HashMap<String, (Ty, Expr)>, module: &str) -> Option<i128> {
    fn lookup(
        name: &str,
        consts: &HashMap<String, (Ty, Expr)>,
        module: &str,
        seen: &std::cell::RefCell<Vec<String>>,
    ) -> Option<i128> {
        let key = [format!("{module}::{name}"), name.to_owned()]
            .into_iter()
            .find(|k| consts.contains_key(k))?;
        if seen.borrow().contains(&key) {
            return None;
        }
        seen.borrow_mut().push(key.clone());
        let value = rokc_ast::ConstExpr::Expr(Box::new(consts[&key].1.clone()));
        let v = super::const_eval::syntactic_int(&value, &|n| lookup(n, consts, module, seen));
        seen.borrow_mut().pop();
        v
    }
    let c = match &t.kind {
        AstTyKind::Const(c) => c.clone(),
        AstTyKind::Path(p) => rokc_ast::ConstExpr::Path(p.clone()),
        _ => return None,
    };
    let seen = std::cell::RefCell::new(Vec::new());
    super::const_eval::syntactic_int(&c, &|n| lookup(n, consts, module, &seen))
}

/// `v` as a const type argument.
fn const_literal_ty(v: i128, span: rokc_diagnostic::Span) -> Ty {
    let lit = Expr {
        kind: ExprKind::Literal(rokc_ast::Literal::Int(v.unsigned_abs().to_string())),
        span,
    };
    let e = if v < 0 {
        Expr {
            kind: ExprKind::OpPrefix {
                op: "-".to_owned(),
                operand: Box::new(lit),
            },
            span,
        }
    } else {
        lit
    };
    Ty {
        kind: AstTyKind::Const(rokc_ast::ConstExpr::Expr(Box::new(e))),
        span,
    }
}

/// Trait type parameter → the impl's argument (or the parameter's
/// default, `Self` meaning the impl target; spec 2.10.5).
fn trait_param_args(t: &rokc_ast::TraitDef, impl_def: &rokc_ast::ImplDef) -> HashMap<String, Ty> {
    let given: &[Ty] = impl_def
        .trait_path
        .as_ref()
        .and_then(|tp| tp.segments.last())
        .map_or(&[], |s| s.generics.as_slice());
    let mut out = HashMap::new();
    for (i, gp) in t.generics.params.iter().enumerate() {
        let (name, default) = match gp {
            rokc_ast::GenericParam::Type { name, default, .. } => (name, default),
            rokc_ast::GenericParam::Const { name, .. } => (name, &None),
        };
        let ty = given.get(i).cloned().or_else(|| {
            default.as_ref().map(|d| match &d.kind {
                AstTyKind::Path(p) if p.segments.len() == 1 && p.segments[0].name == "Self" => {
                    impl_def.self_ty.clone()
                }
                _ => d.clone(),
            })
        });
        if let Some(ty) = ty {
            out.insert(name.clone(), ty);
        }
    }
    out
}

fn trait_assoc_names(t: &rokc_ast::TraitDef) -> Vec<String> {
    t.items
        .iter()
        .filter_map(|i| match i {
            rokc_ast::TraitItem::AssocType { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect()
}

/// Does `m`'s signature name one of `assoc` (bare or `Self::X`)?
fn sig_mentions(m: &FnDef, assoc: &[String]) -> bool {
    let params: Vec<&str> = Vec::new();
    let names: Vec<&str> = assoc.iter().map(String::as_str).collect();
    let mut out = Vec::new();
    for p in &m.params {
        if let Some(t) = &p.ty {
            ast_ty_needs(t, &params, &names, &mut out);
        }
    }
    ast_ty_needs(&sig_ret_ast(m), &params, &names, &mut out);
    out.iter().any(|n| n.starts_with("Self::"))
}

/// Does `m` return a generic type over `Self` (`Flatten<Self>`)? Such a
/// default is instantiated only when called: the adapter type may not
/// exist for every implementor (`Flatten` needs `IntoIterator` items).
fn returns_self_generic(m: &FnDef) -> bool {
    matches!(&sig_ret_ast(m).kind, AstTyKind::Path(p)
        if p.segments.iter().any(|s| s.generics.iter().any(|g| matches!(g.kind, AstTyKind::SelfUpper))))
}

/// Replace a default method's associated-type names (`Item`,
/// `Self::Item`) in its signature with the impl's types.
fn path_ty_named(name: &str, span: rokc_diagnostic::Span) -> Ty {
    Ty {
        kind: AstTyKind::Path(rokc_ast::Path {
            segments: vec![rokc_ast::PathSegment {
                name: name.to_owned(),
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    }
}

/// Spec 2.6.4 / 2.8.3 / 2.13.4: in a trait or impl, both `X` and
/// `Self::X` name its associated type `X`, shadowing an outer `X`. An
/// impl's method signatures get the impl's type (a generic member:
/// `Self::Item | none` with `type Item = i32 | none` nests); trait and
/// impl methods are marked `ASSOC_TYPES_ATTR` so their bodies read bare
/// `X` as `Self::X`.
fn with_self_assoc_sigs(program: &Program) -> Option<Program> {
    let hit = program.items.iter().any(|it| match it {
        Item::Impl(i) => i
            .items
            .iter()
            .any(|m| matches!(m, AstImplItem::AssocType { .. })),
        Item::Trait(t) => !trait_assoc_names(t).is_empty(),
        _ => false,
    });
    if !hit {
        return None;
    }
    let mark = |d: &mut FnDef, names: Vec<String>| {
        d.attrs.push(rokc_ast::Attribute {
            path: std::iter::once(crate::ASSOC_TYPES_ATTR.to_owned())
                .chain(names)
                .collect(),
            body: rokc_ast::AttrBody::default(),
            inner: false,
            span: d.span,
        });
    };
    let mut p = program.clone();
    for it in &mut p.items {
        match it {
            Item::Impl(i) => {
                let assoc = impl_assoc_types(i);
                if assoc.is_empty() {
                    continue;
                }
                for m in &mut i.items {
                    if let AstImplItem::Method(d) = m {
                        for prm in &mut d.params {
                            if let Some(t) = &mut prm.ty {
                                subst_assoc_ty(t, &assoc);
                            }
                        }
                        if let Some(t) = &mut d.ret_ty {
                            subst_assoc_ty(t, &assoc);
                        }
                        if let rokc_ast::ThrowsKind::Typed(ts) = &mut d.throws {
                            ts.iter_mut().for_each(|t| subst_assoc_ty(t, &assoc));
                        }
                        mark(d, assoc.keys().cloned().collect());
                    }
                }
            }
            Item::Trait(t) => {
                let names = trait_assoc_names(t);
                if names.is_empty() {
                    continue;
                }
                for ti in &mut t.items {
                    if let rokc_ast::TraitItem::Method(d) = ti {
                        mark(d, names.clone());
                    }
                }
            }
            _ => {}
        }
    }
    Some(p)
}

/// Associated type defaults (`trait TryFrom<U> { type Error =
/// ConversionError; }`): an impl that omits `type X` gets the trait's
/// default, its names resolved in the trait's module and the trait's
/// parameters replaced by the impl's arguments. Everything after sees
/// an ordinary `type X = ..;` in the impl.
fn with_assoc_defaults(program: &Program, names: &TypeNames<'_>) -> Option<Program> {
    let traits: HashMap<&str, &rokc_ast::TraitDef> = program
        .items
        .iter()
        .filter_map(|it| match it {
            Item::Trait(t) => Some((t.name.as_str(), t)),
            _ => None,
        })
        .filter(|(_, t)| {
            t.items.iter().any(|i| {
                matches!(
                    i,
                    rokc_ast::TraitItem::AssocType {
                        default: Some(_),
                        ..
                    }
                )
            })
        })
        .collect();
    if traits.is_empty() {
        return None;
    }
    let mut p = program.clone();
    let mut hit = false;
    for it in &mut p.items {
        let Item::Impl(i) = it else { continue };
        let Some(tp) = &i.trait_path else { continue };
        let module = impl_module(i);
        let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
        let Some(td) = traits.get(names.trait_key(&segs, &module).as_str()) else {
            continue;
        };
        let have = impl_assoc_types(i);
        let params = trait_param_args(td, i);
        let mut added = Vec::new();
        for ti in &td.items {
            let rokc_ast::TraitItem::AssocType {
                name,
                default: Some(d),
                ..
            } = ti
            else {
                continue;
            };
            if have.contains_key(name) {
                continue;
            }
            let mut ty = d.clone();
            names.absolutize(&mut ty, &module_of(&td.name), &module, &params);
            subst_assoc_ty(&mut ty, &params);
            added.push(AstImplItem::AssocType {
                name: name.clone(),
                ty,
            });
        }
        hit |= !added.is_empty();
        i.items.extend(added);
    }
    hit.then_some(p)
}

/// Spec 2.8.3: warn when an associated type hides an outer type of the
/// same name inside its trait / impl.
fn warn_assoc_shadowing(
    program: &Program,
    names: &TypeNames<'_>,
    diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) {
    for it in &program.items {
        let (assoc, module, owner) = match it {
            Item::Impl(i) => (
                i.items
                    .iter()
                    .filter_map(|m| match m {
                        AstImplItem::AssocType { name, .. } => Some(name.clone()),
                        _ => None,
                    })
                    .collect(),
                impl_module(i),
                format!("impl for `{}`", impl_def_display(&i.self_ty)),
            ),
            Item::Trait(t) => (
                trait_assoc_names(t),
                item_module(it),
                format!("trait `{}`", leaf_name(&t.name)),
            ),
            _ => continue,
        };
        for a in assoc {
            let prim = matches!(
                crate::ty::resolve_ty(&path_ty_named(&a, it.span())),
                HirTy::Prim(_)
            );
            // A trait of that name is not a type (`trait IntoFuture { type
            // IntoFuture; }`).
            let outer = names
                .canon(&[a.as_str()], &module, &[])
                .filter(|full| !names.traits.contains(full));
            if prim || outer.is_some() {
                rokc_diagnostic::set_current_span(it.span());
                diags.push(rokc_diagnostic::RokDiagnostic::warning(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "associated type `{a}` shadows the outer type `{a}` inside the {owner}; \
                         there `{a}` and `Self::{a}` both mean the associated type (spec 2.8.3)"
                    ),
                ));
            }
        }
    }
}

fn subst_assoc_sig(def: &mut FnDef, assoc: &HashMap<String, Ty>) {
    if assoc.is_empty() {
        return;
    }
    for p in &mut def.params {
        if let Some(t) = &mut p.ty {
            subst_assoc_ty(t, assoc);
        }
    }
    if let Some(t) = &mut def.ret_ty {
        subst_assoc_ty(t, assoc);
    }
    if let rokc_ast::ThrowsKind::Typed(ts) = &mut def.throws {
        ts.iter_mut().for_each(|t| subst_assoc_ty(t, assoc));
    }
    // Bounds and defaults too: `fn chain<J: Iterator<Item = Item>>`,
    // `fn collect<C = List<Item>>`.
    for gp in &mut def.generics.params {
        if let rokc_ast::GenericParam::Type {
            bounds, default, ..
        } = gp
        {
            bounds.iter_mut().for_each(|b| subst_assoc_ty(b, assoc));
            if let Some(d) = default {
                subst_assoc_ty(d, assoc);
            }
        }
    }
    for w in &mut def.where_clause {
        w.bounds.iter_mut().for_each(|b| subst_assoc_ty(b, assoc));
    }
}

/// Replace `X` and `Self::X` by `assoc[X]` (associated types, generic
/// alias parameters).
pub(super) fn subst_assoc_ty(ty: &mut Ty, assoc: &HashMap<String, Ty>) {
    match &mut ty.kind {
        AstTyKind::Path(p) => {
            let name = match p.segments.as_slice() {
                [s] if s.generics.is_empty() => Some(s.name.clone()),
                [s, x] if s.name == "Self" && x.generics.is_empty() => Some(x.name.clone()),
                _ => None,
            };
            if let Some(t) = name.and_then(|n| assoc.get(&n)) {
                *ty = t.clone();
                return;
            }
            // `Item::IntoIter` → `List<T>::IntoIter` (a projection on
            // the impl's type).
            if let [s, x] = p.segments.as_slice() {
                if let (true, Some(AstTyKind::Path(ap))) = (
                    s.generics.is_empty() && x.generics.is_empty(),
                    assoc.get(&s.name).map(|t| &t.kind),
                ) {
                    let mut segs = ap.segments.clone();
                    segs.push(x.clone());
                    p.segments = segs;
                    return;
                }
            }
            for s in &mut p.segments {
                for g in &mut s.generics {
                    subst_assoc_ty(g, assoc);
                }
            }
        }
        AstTyKind::Sum(ps) => {
            for t in ps.iter_mut() {
                let before = matches!(&t.kind, AstTyKind::Path(p) if p.segments.len() <= 2)
                    .then(|| format!("{:?}", t.kind));
                subst_assoc_ty(t, assoc);
                // A replaced parameter stays one member (spec 2.6.4).
                if before.is_some_and(|b| b != format!("{:?}", t.kind)) {
                    let span = t.span;
                    let inner = std::mem::replace(t, path_ty_named(rokc_ast::NEST_MARK, span));
                    if let AstTyKind::Path(p) = &mut t.kind {
                        p.segments[0].generics.push(inner);
                    }
                }
            }
        }
        AstTyKind::Tuple(ps) => ps.iter_mut().for_each(|t| subst_assoc_ty(t, assoc)),
        AstTyKind::Array(e, len) => {
            subst_assoc_ty(e, assoc);
            // `[T; D]` with const parameter `D` given as `3`.
            let name = match len {
                rokc_ast::ConstExpr::Path(p) => {
                    p.segments.first().filter(|_| p.segments.len() == 1)
                }
                rokc_ast::ConstExpr::Expr(e) => match &e.kind {
                    ExprKind::Path(p) if p.segments.len() == 1 => p.segments.first(),
                    _ => None,
                },
                rokc_ast::ConstExpr::Literal(_) => None,
            };
            if let Some(AstTyKind::Const(c)) =
                name.and_then(|s| assoc.get(&s.name)).map(|t| &t.kind)
            {
                *len = c.clone();
            }
        }
        AstTyKind::Fn(args, ret, _) => {
            args.iter_mut().for_each(|t| subst_assoc_ty(t, assoc));
            subst_assoc_ty(ret, assoc);
        }
        AstTyKind::Throws { ok, err } => {
            subst_assoc_ty(ok, assoc);
            subst_assoc_ty(err, assoc);
        }
        _ => {}
    }
}

/// The `fn_table` key (and symbol) of method `leaf` of `target`: `Ty__m`,
/// or `Ty__m__by_Tr` when another trait (or an inherent impl) already
/// took that name (spec 4.9.6 picks one at the call site). `None`: the
/// same trait / inherent impl defines it twice.
fn method_key(
    fn_table: &HashMap<String, FnSig>,
    method_info: &HashMap<FunctionId, MethodInfo>,
    target: &HirTy,
    leaf: &str,
    trait_name: Option<&str>,
    trait_args: &str,
) -> Option<String> {
    let key = format!("{}__{leaf}", ty_mangle(target));
    let Some(prev) = fn_table.get(&key) else {
        return Some(key);
    };
    let prev_trait = method_info
        .get(&prev.id)
        .and_then(|i| i.trait_name.as_deref());
    // The same trait again is a duplicate unless its arguments differ
    // (checked per impl before this).
    if prev_trait == trait_name && trait_args.is_empty() {
        return None;
    }
    let alt = format!(
        "{key}__by_{}{trait_args}",
        trait_name.map_or("inherent".to_owned(), |t| t.replace("::", "_"))
    );
    (!fn_table.contains_key(&alt)).then_some(alt)
}

/// The copy-out shape of a function with `ref` parameters (spec 4.7).
pub(super) fn ref_out_of(sig: &FnSig) -> Option<RefOut> {
    let refs: Vec<(usize, HirTy)> = sig
        .param_refs
        .iter()
        .enumerate()
        .filter(|(_, r)| **r)
        .map(|(i, _)| (i, sig.param_tys[i].clone()))
        .collect();
    (!refs.is_empty()).then(|| RefOut {
        ret: sig.ret_ty.clone(),
        refs,
    })
}

/// Spec 6.5: every `#[literal]` function's signature against its
/// pattern's captures; the built-in shapes' handlers.
fn literal_handlers(
    program: &Program,
    diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> Vec<super::ShapeHandler> {
    use rokc_parser::{ArgKind, PatKind, Pattern};
    let mut out = Vec::new();
    // (pattern, priority, return type leaf) → first handler: a second
    // one is ambiguous wherever the pattern matches (6.5.5: neither the
    // slot type nor `priority` can tell them apart).
    let mut seen: HashMap<(String, i64, String), (String, rokc_diagnostic::Span)> = HashMap::new();
    for item in &program.items {
        let Item::Fn(f) = item else { continue };
        let Some(attr) = f.attrs.iter().find(|a| a.name() == "literal") else {
            continue;
        };
        let rokc_ast::AttrBody::Args(args) = &attr.body else {
            continue;
        };
        let Some(rokc_ast::AttrArg::Lit(rokc_ast::Literal::Str(text))) = args.first() else {
            continue;
        };
        let Some(pat) = Pattern::from_text(text) else {
            continue;
        };
        let priority = args
            .iter()
            .find_map(|a| match a {
                rokc_ast::AttrArg::KeyValue(k, rokc_ast::Literal::Int(v)) if k == "priority" => {
                    v.parse().ok()
                }
                _ => None,
            })
            .unwrap_or(0);
        let want = pat.args();
        let fits = want.len() == f.params.len()
            && want
                .iter()
                .zip(&f.params)
                .all(|(k, p)| !p.variadic || *k == ArgKind::Many);
        if !fits {
            let shape: Vec<&str> = want
                .iter()
                .map(|k| match k {
                    ArgKind::One => "a value",
                    ArgKind::Many => "a repetition (`...T`, an array or a List)",
                })
                .collect();
            diags.push(
                rokc_diagnostic::RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Meta,
                    format!(
                        "`#[literal({text})]` handler `{}` must take {} parameter(s): {} \
                         (spec 6.5.4)",
                        f.name,
                        want.len(),
                        if shape.is_empty() {
                            "none".to_owned()
                        } else {
                            shape.join(", ")
                        }
                    ),
                )
                .with_span(attr.span, "")
                .with_secondary(f.span, "handler declared here"),
            );
            continue;
        }
        let ret_leaf = match f.ret_ty.as_ref().map(|t| &t.kind) {
            Some(AstTyKind::Path(p)) => p.segments.last().map(|s| s.name.clone()),
            _ => None,
        };
        let key = (pat.render(), priority, ret_leaf.unwrap_or_default());
        if let Some((first, first_span)) = seen.get(&key) {
            diags.push(
                rokc_diagnostic::RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Meta,
                    format!(
                        "`#[literal({text})]` is already registered by `{first}` with the same \
                         priority and return type: every use would be ambiguous — drop one, or \
                         give one a `priority = N` (spec 6.5.5)"
                    ),
                )
                .with_span(attr.span, "")
                .with_secondary(*first_span, "first registered here"),
            );
            continue;
        }
        seen.insert(key, (f.name.clone(), attr.span));
        if let Ok(PatKind::Shape(shape)) = pat.kind() {
            out.push(super::ShapeHandler {
                shape,
                name: f.name.clone(),
                priority,
                span: attr.span,
            });
        }
    }
    out
}

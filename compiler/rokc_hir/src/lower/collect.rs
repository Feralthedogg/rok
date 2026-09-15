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

/// A concrete function whose code a prebuilt library's `.a` holds (the
/// ones an RHIR interface cuts to `;`).
fn in_archive(f: &FnDef) -> bool {
    f.generics.params.is_empty()
        && !f.is_async
        && !f.is_generator
        && !f
            .attrs
            .iter()
            .any(|a| a.name() == "inline" || a.path == [rokc_ast::EXTERN_C_FN_ATTR])
}

/// A body small enough to copy into a program for inlining
/// (`HirInput::inline_prebuilt`): at most `INLINE_EXPRS` expressions.
fn small_body(f: &FnDef) -> bool {
    const INLINE_EXPRS: usize = 40;
    struct Count(usize);
    impl crate::walk::AstVisitor for Count {
        fn expr(&mut self, _: &rokc_ast::Expr) {
            self.0 += 1;
        }
    }
    let mut n = Count(0);
    crate::walk::walk_fn(&mut n, f);
    n.0 <= INLINE_EXPRS
}

/// Package `pkg` is `p` or one of its tiers (`rok::core` is in `rok`,
/// the prebuilt standard library).
fn within(pkg: &str, p: &str) -> bool {
    pkg.strip_prefix(p)
        .is_some_and(|r| r.is_empty() || r.starts_with("::"))
}

/// One `fn __rok_static_init_X() -> T { init }` per lazy static, added
/// to `program`.
/// Spec 4.2.2 / 2.10.7: a parameter without a type is an implicit type
/// parameter (`fn id(x)` is `fn id<T#x>(x: T#x)`), monomorphized per
/// call; the body is checked per instance, and no bound is synthesized.
/// Free fns and inherent methods with a body (a trait impl's method
/// takes its types from the trait).
fn implicit_generics(program: &mut Program) {
    let fix = |f: &mut FnDef| {
        if f.body.is_none() {
            return;
        }
        for p in &mut f.params {
            if p.ty.is_some() || p.name == "self" || p.variadic {
                continue;
            }
            let name = format!("T#{}", p.name);
            let path = rokc_ast::Path {
                segments: vec![rokc_ast::PathSegment {
                    name: name.clone(),
                    generics: Vec::new(),
                }],
                span: p.span,
            };
            p.ty = Some(Ty {
                kind: AstTyKind::Path(path),
                span: p.span,
            });
            f.generics.params.push(rokc_ast::GenericParam::Type {
                name,
                bounds: Vec::new(),
                default: None,
            });
        }
    };
    for item in &mut program.items {
        match item {
            Item::Fn(f) => fix(f),
            Item::Impl(i) if i.trait_path.is_none() => {
                for it in &mut i.items {
                    if let AstImplItem::Method(f) = it {
                        fix(f);
                    }
                }
            }
            _ => {}
        }
    }
}

fn add_lazy_static_inits(program: &mut Program) {
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
    program.items.extend(inits);
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
    program: Program,
    prec: &PrecTable,
    uses: &crate::uses::UseTable,
    reexports: &[crate::uses::ReExport],
    input: &crate::HirInput,
) -> HirModule {
    resolve::set_packages(input.packages.clone());
    super::const_eval::set_pointer_width(input.pointer_width);
    crate::clear_type_names();
    // A prebuilt-library build: every body of that package is a root.
    let lib_pkg: Option<String> = input.lib.clone();
    let check_library = input.check_library;
    let mut owned = program;
    add_lazy_static_inits(&mut owned);
    implicit_generics(&mut owned);
    let program = &owned;
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

    // A field / variant name declared twice in one type.
    for item in &program.items {
        let (kind, owner, names): (&str, &str, Vec<(&str, rokc_diagnostic::Span)>) = match item {
            Item::Struct(s) => match &s.kind {
                rokc_ast::StructKind::Named(fs) => (
                    "field",
                    &s.name,
                    fs.iter().map(|f| (f.name.as_str(), f.span)).collect(),
                ),
                _ => continue,
            },
            Item::Union(u) => (
                "field",
                &u.name,
                u.fields.iter().map(|f| (f.name.as_str(), f.span)).collect(),
            ),
            Item::Enum(e) => (
                "variant",
                &e.name,
                e.variants
                    .iter()
                    .map(|v| (v.name.as_str(), v.span))
                    .collect(),
            ),
            _ => continue,
        };
        for (i, (n, at)) in names.iter().enumerate() {
            if names[..i].iter().any(|(m, _)| m == n) {
                rokc_diagnostic::set_current_span(*at);
                err(
                    &mut pre_diags,
                    format!(
                        "{kind} `{n}` is declared more than once in `{}`",
                        leaf_name(owner)
                    ),
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
        rokc_diagnostic::set_current_span(item.span());
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
    // `pub use` aliases → what they name, chains followed to the item.
    let aliases = reexport_aliases(reexports);
    let type_reexports: HashMap<String, String> = aliases
        .iter()
        .filter(|(_, end)| type_set.contains(*end))
        .map(|(a, end)| (a.clone(), end.clone()))
        .collect();
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
    // Spec 6.4: the lang slots (the driver reports their errors).
    let (lang, _) = rokc_parser::collect_lang_table(program);
    // Structural auto traits: a type has them unless a component lacks them.
    let auto_traits = ["send_trait", "sync_trait"]
        .into_iter()
        .filter_map(|s| lang.lookup(s))
        .map(|e| e.item_name.clone())
        .collect();
    let names = TypeNames {
        names: type_set,
        variants,
        traits,
        auto_traits,
        lang,
        reexports: type_reexports,
        visibility: type_vis,
        mod_vis: super::resolve::module_visibility(&program.items),
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
        unknown_spans: std::cell::RefCell::default(),
        canon_memo: std::cell::RefCell::default(),
        leaves: std::cell::OnceCell::new(),
        variant_leaves: std::cell::OnceCell::new(),
        consts: program
            .items
            .iter()
            .filter_map(|it| match it {
                Item::Const(c) => Some((c.name.clone(), (c.ty.clone(), c.value.clone()))),
                _ => None,
            })
            .collect(),
        const_leaves: std::cell::OnceCell::new(),
    };
    warn_assoc_shadowing(program, &names, &mut pre_diags);
    let defaults = assoc_defaults(program, &names);
    for (i, added) in defaults {
        if let Item::Impl(imp) = &mut owned.items[i] {
            imp.items.extend(added);
        }
    }
    impl_param_types(&mut owned, &names);
    add_self_assoc_sigs(&mut owned);
    let program = &owned;
    check_bound_names(program, &names, &mut pre_diags);
    check_niche_attrs(program, &mut pre_diags);
    check_repr_attrs(program, &mut pre_diags);

    // Pass 1a: every struct / union / enum takes its id before any type
    // is resolved; a generic one is a template, instantiated in the same
    // id space when a type first names it (`TypeDefs`). Unions share the
    // struct namespace, ids after the structs.
    let mut defs = TypeDefs::default();
    let mut enum_decls: Vec<&AstEnumDef> = Vec::new();
    let mut struct_decls: Vec<&AstStructDef> = Vec::new();
    let mut union_decls: Vec<&rokc_ast::UnionDef> = Vec::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
        match item {
            Item::Enum(e) => {
                if defs.enum_table.borrow().contains_key(&e.name)
                    || defs.generic_enums.contains_key(&e.name)
                {
                    continue;
                }
                if !e.generics.params.is_empty() {
                    defs.generic_enums.insert(e.name.clone(), e);
                    continue;
                }
                let id = EnumId(u32::try_from(enum_decls.len()).expect("EnumId overflow"));
                crate::name_type(true, id.0, &e.name, &[]);
                defs.enum_table.borrow_mut().insert(e.name.clone(), id);
                enum_decls.push(e);
            }
            Item::Struct(s) => {
                if defs.struct_table.borrow().contains_key(&s.name)
                    || defs.generic_structs.contains_key(&s.name)
                {
                    continue;
                }
                if !s.generics.params.is_empty() {
                    defs.generic_structs.insert(s.name.clone(), s);
                    continue;
                }
                let id = StructId(u32::try_from(struct_decls.len()).expect("StructId overflow"));
                crate::name_type(false, id.0, &s.name, &[]);
                defs.struct_table.borrow_mut().insert(s.name.clone(), id);
                struct_decls.push(s);
            }
            _ => {}
        }
    }
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
        if let Item::Union(u) = item {
            if defs.struct_table.borrow().contains_key(&u.name)
                || defs.generic_structs.contains_key(&u.name)
            {
                continue;
            }
            let id = StructId(
                u32::try_from(struct_decls.len() + union_decls.len()).expect("StructId overflow"),
            );
            crate::name_type(false, id.0, &u.name, &[]);
            defs.struct_table.borrow_mut().insert(u.name.clone(), id);
            union_decls.push(u);
        }
    }
    // Declared ones first (field types not resolved yet), so an instance
    // made while resolving them takes the next id.
    for (i, e) in enum_decls.iter().enumerate() {
        defs.enums.borrow_mut().push(HirEnumDef {
            id: EnumId(u32::try_from(i).expect("EnumId overflow")),
            repr: crate::Repr::default(),
            def_id: None,
            name: e.name.clone(),
            variants: Vec::new(),
            span: e.span,
            generic_args: Vec::new(),
        });
    }
    let struct_shells = struct_decls
        .iter()
        .map(|s| (&s.name, s.span))
        .chain(union_decls.iter().map(|u| (&u.name, u.span)));
    for (i, (name, span)) in struct_shells.enumerate() {
        defs.structs.borrow_mut().push(HirStructDef {
            id: StructId(u32::try_from(i).expect("StructId overflow")),
            repr: crate::Repr::default(),
            def_id: None,
            name: name.clone(),
            fields: Vec::new(),
            span,
            generic_args: Vec::new(),
            union_kind: None,
            niche: Vec::new(),
        });
    }
    for (i, e) in enum_decls.iter().enumerate() {
        let id = EnumId(u32::try_from(i).expect("EnumId overflow"));
        let module = module_of(&e.name);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        let def = lower_enum_def(e, id, &defs, sc);
        defs.enums.borrow_mut()[i] = def;
    }
    for (i, s) in struct_decls.iter().enumerate() {
        let id = StructId(u32::try_from(i).expect("StructId overflow"));
        let module = module_of(&s.name);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        let def = lower_struct_def(s, id, &defs, sc);
        defs.structs.borrow_mut()[i] = def;
    }
    for (i, u) in union_decls.iter().enumerate() {
        let i = struct_decls.len() + i;
        let id = StructId(u32::try_from(i).expect("StructId overflow"));
        let module = module_of(&u.name);
        let sc = Scope {
            names: &names,
            module: &module,
        };
        let def = lower_union_def(u, id, &defs, sc, &mut pre_diags);
        defs.structs.borrow_mut()[i] = def;
    }

    // Pass 1c: module-level `const`s, kept as AST and inlined at each
    // use; `static`s get global storage (`HirStaticDef`).
    let mut consts: HashMap<String, (Ty, Expr)> = HashMap::new();
    // Per impl item: its associated consts, for its `Impl`.
    let mut impl_const_lists: HashMap<usize, Vec<AssocConst>> = HashMap::new();
    let mut inherent_keys: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (idx, item) in program.items.iter().enumerate() {
        rokc_diagnostic::set_current_span(item.span());
        // Spec 2.9.1: an impl's `const` is `Type::NAME` (`Self::NAME`
        // inside the impl); a trait impl also gets the trait's defaults
        // (spec 2.8.3a).
        let item_consts: Vec<(String, Ty, Expr)> = match item {
            Item::Const(c) => vec![(c.name.clone(), c.ty.clone(), c.value.clone())],
            Item::Impl(i) => {
                let (keyed, all) = impl_consts(i, program, &names, &mut pre_diags);
                impl_const_lists.insert(idx, all);
                keyed
            }
            _ => Vec::new(),
        };
        // Two trait impls may both give `S::N` (an ambiguity reported
        // where it is read, `lower_assoc_const`); an inherent `S::N`
        // shadows the trait ones, as for methods.
        let trait_impl = matches!(item, Item::Impl(i) if i.trait_path.is_some());
        for (key, ty, value) in item_consts {
            if trait_impl {
                if !inherent_keys.contains(&key) {
                    consts.insert(key, (ty, value));
                }
            } else if inherent_keys.insert(key.clone()) {
                consts.insert(key, (ty, value));
            } else {
                err(
                    &mut pre_diags,
                    format!("const `{key}` is defined more than once"),
                );
            }
        }
    }
    let mut static_defs: Vec<HirStaticDef> = Vec::new();
    let mut static_asts: Vec<(&Ty, String, Option<&Expr>)> = Vec::new();
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
            // Its type (and literal initializer) once every item is
            // registered.
            static_asts.push((&s.ty, module_of(&s.name), s.value.as_ref()));
            static_tys.insert(s.name.clone(), HirTy::Unknown);
            static_defs.push(HirStaticDef {
                name: s.name.clone(),
                ty: HirTy::Unknown,
                init: ConstVal::Unit,
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
                static_asts.push((&s.ty, String::new(), None));
                static_tys.insert(s.name.clone(), HirTy::Unknown);
                static_defs.push(HirStaticDef {
                    name: s.name.clone(),
                    ty: HirTy::Unknown,
                    init: ConstVal::Unit,
                    is_mut: s.is_mut,
                    is_extern: true,
                    init_fn: None,
                    span: s.span,
                });
            }
        }
    }
    // Pass 1d: each plain type alias resolved once, for its diagnostics
    // (a use expands the alias where it is resolved).
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
            resolve_ty_with_structs(&a.ty, &defs, None, sc);
        }
    }
    // An alias naming itself, directly or through other aliases and
    // anywhere in the type (`type A = B; type B = A;`, `type T = List<T>;`).
    {
        let alias_items: HashMap<&str, &rokc_ast::TypeAliasDef> = program
            .items
            .iter()
            .filter_map(|i| match i {
                Item::TypeAlias(a) if a.generics.params.is_empty() => Some((a.name.as_str(), a)),
                _ => None,
            })
            .collect();
        let mentions = |a: &rokc_ast::TypeAliasDef| {
            struct Names(Vec<String>);
            impl crate::walk::AstVisitor for Names {
                fn ty(&mut self, t: &rokc_ast::Ty) {
                    if let rokc_ast::TyKind::Path(p) = &t.kind {
                        if let [s] = p.segments.as_slice() {
                            self.0.push(s.name.clone());
                        }
                    }
                }
            }
            let mut v = Names(Vec::new());
            crate::walk::walk_ty(&mut v, &a.ty);
            let module = module_of(&a.name);
            v.0.into_iter()
                .map(|n| {
                    if module.is_empty() {
                        n
                    } else {
                        format!("{module}::{n}")
                    }
                })
                .filter(|n| alias_items.contains_key(n.as_str()))
                .collect::<Vec<_>>()
        };
        let mut cyclic: Vec<&rokc_ast::TypeAliasDef> = alias_items
            .values()
            .filter(|a| {
                let mut stack = mentions(a);
                let mut seen = std::collections::HashSet::new();
                while let Some(n) = stack.pop() {
                    if n == a.name {
                        return true;
                    }
                    if seen.insert(n.clone()) {
                        stack.extend(mentions(alias_items[n.as_str()]));
                    }
                }
                false
            })
            .copied()
            .collect();
        cyclic.sort_by(|a, b| a.name.cmp(&b.name));
        for a in cyclic {
            rokc_diagnostic::set_current_span(a.span);
            err(&mut pre_diags, format!("type alias `{}` is cyclic", a.name));
        }
    }

    // Pass 2: function-like declarations. Free functions first, then
    // `impl` methods (a free function `Type::method` taking `self`
    // first). Generic functions stay AST templates, monomorphized per
    // call, outside `decls` / `fn_table`.
    let mut fn_table: HashMap<String, FnSig> = HashMap::new();
    let mut extern_fns = std::collections::HashSet::new();
    // Later extern declarations of a name already declared: whether
    // `extern "rok"`, the first one's id.
    let mut extern_redecls: Vec<(&FnDef, bool, FunctionId)> = Vec::new();
    let method_table: HashMap<(MethodTarget, String), Vec<FunctionId>> = HashMap::new();
    let method_info: HashMap<FunctionId, MethodInfo> = HashMap::new();
    let mut impls = Impls::default();
    let mut decls: Vec<MethodOrFn<'_>> = Vec::new();
    // Per decl: its body is library code (`rok::<tier>` / a dependency),
    // lowered only when reached (`lower_bodies`).
    let mut lib_decl: Vec<bool> = Vec::new();
    // Decl index → symbol path of a dependency's method (see below).
    let mut link_names: HashMap<usize, String> = HashMap::new();
    let std_prebuilt = input.prebuilt.iter().any(|p| p == "rok");
    let std_linked = std_prebuilt || input.lib.as_deref() == Some("rok");
    let mut generic_fns: HashMap<String, &FnDef> = HashMap::new();
    let generic_methods: HashMap<(String, String), Vec<GenericMethod>> = HashMap::new();
    // Generic impls with method templates so far (names `__impl{n}_m`).
    let mut templated = 0;
    let mut intrinsics: HashMap<FunctionId, PrimOp> = HashMap::new();
    let mut generic_intrinsics: HashMap<String, Intrinsic> = HashMap::new();
    let mut unsafe_fns: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut extern_fn_ids: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut c_variadic: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut no_safepoint: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    // `extern "rok"` declarations: the runtime's own ABI.
    let mut rok_externs: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    // A declaration's signature: its types are resolved once every item
    // is registered (`mono::decl_sig`), the rest is read off it here.
    let sig_of = |fn_def: &FnDef, id: FunctionId, sc: Scope<'_>| FnSig {
        id,
        ret_ty: HirTy::Unknown,
        param_defaults: fn_def
            .params
            .iter()
            .map(|p| p.default.clone().map(|d| in_module(sc.module, d)))
            .collect(),
        param_tys: vec![HirTy::Unknown; fn_def.params.len()],
        param_names: fn_def.params.iter().map(|p| p.name.clone()).collect(),
        param_refs: fn_def.params.iter().map(|p| p.by_ref).collect(),
        variadic: fn_def.params.last().is_some_and(|p| p.variadic),
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
                let module = module_of(&fn_def.name);
                if !fn_def.generics.params.is_empty() {
                    if let Some(i) = intrinsic_of(fn_def, &module, &mut pre_diags) {
                        generic_intrinsics.insert(fn_def.name.clone(), i);
                    }
                    generic_fns.insert(fn_def.name.clone(), fn_def);
                    continue;
                }
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                if let Some(Intrinsic::Prim(op)) = intrinsic_of(fn_def, &module, &mut pre_diags) {
                    intrinsics.insert(id, op);
                }
                let sc = Scope {
                    names: &names,
                    module: &module,
                };
                let sig = sig_of(fn_def, id, sc);
                fn_table.insert(fn_def.name.clone(), sig);
                decls.push(MethodOrFn::Fn(fn_def));
                lib_decl.push(!package_of(&module).is_empty());
            }
            Item::Extern(blk) => {
                let rok_abi = blk.abi == "rok";
                let quiet = blk.attrs.iter().any(|a| a.path == ["no_safepoint"]);
                if quiet && !rok_abi {
                    err(
                        &mut pre_diags,
                        "`#[no_safepoint]` is for `extern \"rok\"` blocks".to_owned(),
                    );
                }
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
                    // A repeated extern declaration names the same symbol:
                    // keep the first, check the signatures agree below.
                    if let Some(first) = fn_table.get(&fn_def.name) {
                        if extern_fns.contains(&fn_def.name) {
                            extern_redecls.push((fn_def, rok_abi, first.id));
                        }
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
                    fn_table.insert(fn_def.name.clone(), sig_of(fn_def, id, sc));
                    if rok_abi {
                        rok_externs.insert(id);
                        if quiet {
                            no_safepoint.insert(id);
                        }
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
    let mut neg_auto: std::collections::HashSet<(String, String)> =
        std::collections::HashSet::new();
    // Impls registered by their written target, resolved once every item
    // is (`impl_heads`).
    let mut pending: Vec<PendingImpl<'_>> = Vec::new();

    for (idx, item) in program.items.iter().enumerate() {
        rokc_diagnostic::set_current_span(item.span());
        let Item::Impl(impl_def) = item else { continue };
        let module = impl_module(impl_def);
        if !check_auto_impl(impl_def, &names, &module, &mut neg_auto, &mut pre_diags) {
            continue;
        }
        let impl_generic = !impl_def.generics.params.is_empty();
        let consts = impl_const_lists.remove(&idx).unwrap_or_default();
        let trait_name: Option<String> = impl_def.trait_path.as_ref().map(|tp| {
            let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
            names.trait_key(&segs, &module)
        });
        // A generic trait impl, or a generic inherent impl on a structural
        // type (`impl<T, const N: usize> [T; N] { .. }`, no trait: empty
        // key): matched against the receiver, its methods templates.
        if impl_generic
            && (trait_name.is_some() || !matches!(impl_def.self_ty.kind, AstTyKind::Path(_)))
        {
            let trait_key = trait_name.unwrap_or_default();
            let td = trait_defs.get(&trait_key).copied();
            let mut gi =
                generic_trait_impl(impl_def, trait_key, td, &module, templated, &mut pre_diags);
            templated += 1;
            gi.consts = consts;
            impls.all.push(gi);
            continue;
        }
        // Inherent methods of a generic impl (and generic methods of a
        // plain inherent or trait impl) are templates keyed by the
        // target's generic base.
        let generic_base = match &impl_def.self_ty.kind {
            AstTyKind::Path(p) => {
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
        pending.push(PendingImpl {
            def: impl_def,
            module: module.clone(),
            trait_name: trait_name.clone(),
            generic_base,
            at: impls.all.len(),
        });
        impls.all.push(Impl {
            trait_key: trait_name.unwrap_or_default(),
            trait_args: impl_def
                .trait_path
                .as_ref()
                .and_then(|tp| tp.segments.last())
                .map(|s| s.generics.clone())
                .unwrap_or_default(),
            assoc: impl_assoc_list(impl_def),
            generics: impl_def.generics.clone(),
            where_clause: impl_def.where_clause.clone(),
            self_ty: impl_def.self_ty.clone(),
            module,
            methods: HashMap::new(),
            consts,
            concrete: None,
        });
    }

    // Install `pub use` re-exports as fn / static table aliases (types go
    // through `TypeNames`).
    for (alias_key, end) in &aliases {
        if let Some(sig) = fn_table.get(end).cloned() {
            fn_table.entry(alias_key.clone()).or_insert(sig);
        }
        if let Some(def) = generic_fns.get(end).copied() {
            generic_fns.entry(alias_key.clone()).or_insert(def);
        }
        if let Some(ty) = static_tys.get(end).cloned() {
            static_tys.entry(alias_key.clone()).or_insert(ty);
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
        next_id: std::cell::Cell::new(0),
        mono_cache: std::cell::RefCell::new(HashMap::new()),
        mono_sigs: std::cell::RefCell::new(HashMap::new()),
        mono_depth: std::cell::Cell::new(0),
        uninferred: std::cell::Cell::new(0),
        any_tags: std::cell::RefCell::new(Vec::new()),
        ref_out: std::cell::RefCell::new(HashMap::new()),
        any_dispatch: std::cell::RefCell::new(Vec::new()),
        projecting: std::cell::RefCell::new(Vec::new()),
        thunks: std::cell::RefCell::new(HashMap::new()),
        instances: std::cell::RefCell::new(Vec::new()),
        instance_warns: std::cell::RefCell::new(super::InstanceWarns::default()),
        diagnostics: std::cell::RefCell::new(Vec::new()),
        infer_vars: std::cell::RefCell::new(Vec::new()),
        infer_depth: std::cell::Cell::new(0),
        infer_floor: std::cell::Cell::new(0),
        fn_origin: std::cell::RefCell::new(HashMap::new()),
        track_caller: std::cell::RefCell::new(std::collections::HashSet::new()),
        const_lowering: std::cell::RefCell::new(std::collections::HashSet::new()),
        const_stack: std::cell::RefCell::new(Vec::new()),
        inferred_ret: std::cell::RefCell::default(),
        inferred_fns: std::cell::RefCell::default(),
        bodies_done: std::cell::Cell::new(false),
        recursive_ret: std::cell::RefCell::default(),
        call_sites: std::cell::RefCell::default(),
        tentative_ret: std::cell::RefCell::default(),
    };
    let mut env = Env {
        infer_ret: std::collections::HashSet::new(),
        implicit_main: input.implicit_main,
        may_diverge: may_diverge(program),
        fn_table,
        fn_leaves: std::cell::OnceCell::new(),
        extern_fns,
        method_table,
        key_of: HashMap::new(),
        method_info,
        defs,
        consts,
        const_leaves: std::cell::RefCell::default(),
        generic_fns,
        generic_methods,
        intrinsics,
        generic_intrinsics,
        extern_fn_ids: extern_fn_ids.clone(),
        rok_externs: rok_externs.clone(),
        c_variadic: c_variadic.clone(),
        c_defs: std::collections::HashSet::new(),
        prec,
        sink,
        item_visibility,
        field_vis,
        uses,
        impls,
        unsafe_fns: std::collections::HashSet::new(),
        neg_auto,
        trait_info,
        statics: static_tys,
        static_leaves: std::cell::RefCell::default(),
        mut_statics: static_defs
            .iter()
            .filter(|s| s.is_mut)
            .map(|s| s.name.clone())
            .collect(),
        literal_shapes: literal_handlers(program, &mut pre_diags),
        names,
        decls,
        non_exhaustive: program
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Struct(s) if s.attrs.iter().any(|a| a.path == ["non_exhaustive"]) => {
                    Some(s.name.clone())
                }
                Item::Enum(e) if e.attrs.iter().any(|a| a.path == ["non_exhaustive"]) => {
                    Some(e.name.clone())
                }
                _ => None,
            })
            .collect(),
    };
    // Impl targets and trait arguments, now that every item is
    // registered; then each impl's methods, keyed by them.
    let heads = rokc_diagnostic::time("hir impls", || {
        impl_heads(&mut env, &pending, &trait_defs, &mut pre_diags)
    });
    let mut fn_table = std::mem::take(&mut env.fn_table);
    let mut decls = std::mem::take(&mut env.decls);
    let mut method_table = std::mem::take(&mut env.method_table);
    let mut method_info = std::mem::take(&mut env.method_info);
    let mut intrinsics = std::mem::take(&mut env.intrinsics);
    let mut generic_methods = std::mem::take(&mut env.generic_methods);
    let names = &env.names;
    let defs = &env.defs;
    for (p, head) in pending.iter().zip(heads) {
        // `None`: a repeated impl, reported.
        let Some((target_ty, provides)) = head else {
            continue;
        };
        let impl_def = p.def;
        rokc_diagnostic::set_current_span(impl_def.span);
        let module = p.module.clone();
        let sc = Scope {
            names,
            module: &module,
        };
        let impl_generic = !impl_def.generics.params.is_empty();
        let trait_name = p.trait_name.clone();
        let generic_base = p.generic_base.clone();
        let target = method_target_for(&target_ty);
        // `From<i32>` / `From<i8>` impls on one type keep their methods
        // apart by the trait's arguments (`overload_args`).
        let trait_args_key: String = provides.as_ref().map_or_else(String::new, |r| {
            r.args
                .iter()
                .map(|a| "_".to_owned() + &ty_mangle(a))
                .collect()
        });
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
                if slot
                    .iter()
                    .any(|g| g.info.trait_name.is_none() && trait_name.is_none())
                {
                    err(
                        &mut pre_diags,
                        format!("method `{leaf}` is defined more than once for `{target_display}`"),
                    );
                    continue;
                }
                // A trait impl's generic method (`fn from_iter<I>` of
                // `impl FromIterator<char> for str`): as visible as the trait.
                slot.push(GenericMethod {
                    def,
                    self_ty: impl_def.self_ty.clone(),
                    info: MethodInfo {
                        module: module.clone(),
                        vis: if trait_name.is_some() {
                            Visibility::Pub
                        } else {
                            m.vis
                        },
                        trait_name: trait_name.clone(),
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
            let sig = sig_of(m, id, sc);
            fn_table.insert(key.clone(), sig);
            if let Some(Intrinsic::Prim(op)) = intrinsic_of(m, &module, &mut pre_diags) {
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
            // dependency and its users name it alike (the standard
            // library's too, when it is prebuilt).
            if resolve::is_dependency(&package_of(&module))
                || (std_linked && !package_of(&module).is_empty())
            {
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
                fn_def: std::borrow::Cow::Borrowed(m),
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
                        HirTy::Struct(id) => {
                            Some(defs.structs.borrow()[id.0 as usize].name.clone())
                        }
                        HirTy::Enum(id) => Some(defs.enums.borrow()[id.0 as usize].name.clone()),
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
                            if let Some(v) = const_arg_value(t, names, sc.module) {
                                *t = const_literal_ty(v, t.span);
                            }
                        }
                    }
                }
                let body_subst: HashMap<String, HirTy> = trait_def
                    .generics
                    .params
                    .iter()
                    .enumerate()
                    .filter_map(|(i, gp)| match gp {
                        rokc_ast::GenericParam::Type { name, .. } => {
                            Some((name.clone(), provides.as_ref()?.args.get(i)?.clone()))
                        }
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
                            Some((name.clone(), HirTy::Const(v, prim)))
                        }
                    })
                    .collect();
                let tm: std::borrow::Cow<'_, FnDef> = if targs.is_empty() {
                    std::borrow::Cow::Borrowed(tm)
                } else {
                    let mut d = tm.clone();
                    subst_assoc_sig(&mut d, &targs);
                    std::borrow::Cow::Owned(d)
                };
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let tsc = Scope {
                    names,
                    module: &trait_module,
                };
                let sig = sig_of(&tm, id, tsc);
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
    let mut exports: Vec<(FunctionId, String)> = Vec::new();
    let mut prebuilt: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut inline_copies: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut c_defs: Vec<FunctionId> = Vec::new();
    for (i, d) in decls.iter().enumerate() {
        let f = d.def();
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
        // The prebuilt standard library's interface keeps its bodies
        // (compile-time evaluation runs them); its `.a` has the code of
        // those named alike in every build (not trait defaults, named
        // after the build's type numbering).
        let stable = matches!(d, MethodOrFn::Fn(_)) || link_names.contains_key(&i);
        let std_fn = std_prebuilt && within(&package_of(&module), "rok");
        let linked = f.body.is_none() || (std_fn && stable && in_archive(f));
        let prebuilt_fn = linked
            && !(extern_fn_ids.contains(&id) || rok_externs.contains(&id))
            && input
                .prebuilt
                .iter()
                .any(|p| within(&package_of(&module), p));
        if prebuilt_fn {
            prebuilt.insert(id);
            if input.inline_prebuilt && std_fn && f.body.is_some() && small_body(f) {
                inline_copies.insert(id);
            }
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
    for f in env.generic_fns.values() {
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
    let infer_ret: std::collections::HashSet<FunctionId> = decls
        .iter()
        .enumerate()
        .filter(|(_, d)| mono::infers_ret(d.def(), &env.may_diverge))
        .map(|(i, _)| FunctionId(u32::try_from(i).expect("FunctionId overflow")))
        .collect();
    env.fn_table = fn_table;
    env.decls = decls;
    env.method_table = method_table;
    env.method_info = method_info;
    env.intrinsics = intrinsics;
    env.generic_methods = generic_methods;
    env.key_of = key_of;
    env.infer_ret = infer_ret;
    env.unsafe_fns = unsafe_fns;
    env.c_defs = c_defs.iter().copied().collect();
    env.sink
        .next_id
        .set(u32::try_from(env.decls.len()).expect("FunctionId overflow"));
    // Struct fields and enum payloads that name projections (`peeked:
    // I::Item | none`, `v: <S as Tr>::Out`) waited for the impls: resolve
    // them now, an instance's under its arguments.
    resolve_open_members(&env, &struct_decls, &enum_decls);
    // Every declaration's signature types, now that every item and impl
    // is registered (a projection in a signature resolves too).
    let sigs: HashMap<FunctionId, FnSig> = (0..env.decls.len())
        .map(|i| {
            let id = FunctionId(u32::try_from(i).expect("FunctionId overflow"));
            let base = &env.fn_table[&env.key_of[&id]];
            (id, mono::decl_sig(&env, i, base))
        })
        .collect();
    for sig in env.fn_table.values_mut() {
        if let Some(s) = sigs.get(&sig.id) {
            sig.clone_from(s);
        }
    }
    // Spec 5.9.4: extern functions share one namespace; declaring one
    // twice with different signatures is an error. The toolchain's
    // runtime declarations (`rok::core::rt`, `extern "rok"`, 8.5) are the
    // reference: the error is at the other one.
    let no_subst = HashMap::new();
    for (f, rok_abi, first) in &extern_redecls {
        let (params, ret) = mono::sig_tys(&env, f, None, module_of(&f.name), &no_subst);
        let s = &sigs[first];
        let c_var = |f: &FnDef| {
            f.attrs
                .iter()
                .any(|a| a.path == [rokc_ast::C_VARIADIC_ATTR])
        };
        let MethodOrFn::Fn(first_def) = env.decls[first.0 as usize] else {
            continue;
        };
        if params == s.param_tys
            && ret == s.ret_ty
            && c_var(f) == c_var(first_def)
            && f.params.last().is_some_and(|p| p.variadic) == s.variadic
        {
            continue;
        }
        let cx = LowerCtx::new(&env, &no_subst, None);
        let show = |ps: &[HirTy], r: &HirTy| {
            let ps: Vec<String> = ps.iter().map(|t| cx.ty_name(t)).collect();
            format!("fn({}) -> {}", ps.join(", "), cx.ty_name(r))
        };
        let (here, other, at) = if *rok_abi && !rok_externs.contains(first) {
            (
                show(&s.param_tys, &s.ret_ty),
                show(&params, &ret),
                first_def.span,
            )
        } else {
            (show(&params, &ret), show(&s.param_tys, &s.ret_ty), f.span)
        };
        rokc_diagnostic::set_current_span(at);
        err(
            &mut pre_diags,
            format!(
                "extern function `{}` is declared twice with different signatures: `{here}` \
                 here, `{other}` elsewhere{} (spec 5.9.4)",
                f.name,
                if f.name.starts_with("rok_") {
                    "; `rok_*` symbols are the runtime's, with the signatures of spec 8.5"
                } else {
                    ""
                }
            ),
        );
    }
    let mut ref_out: Vec<(FunctionId, RefOut)> = sigs
        .values()
        .filter_map(|s| Some((s.id, ref_out_of(s)?)))
        .collect();
    ref_out.sort_by_key(|(id, _)| *id);
    env.sink.ref_out.borrow_mut().extend(ref_out);
    check_impl_overlap(&env);
    check_impl_rules(&env, program);
    let failed_derives = check_derives(&env, program);
    // Every static's type, now that every item is registered.
    let no_subst = HashMap::new();
    let static_types: Vec<HirTy> = static_defs
        .iter()
        .zip(&static_asts)
        .map(|(d, (ast, module, _))| {
            let mut rcx = LowerCtx::new(&env, &no_subst, None);
            rcx.current_module.clone_from(module);
            let old = rokc_diagnostic::set_current_span(d.span);
            let ty = rcx.resolve_ast_ty(ast);
            rokc_diagnostic::set_current_span(old);
            ty
        })
        .collect();
    for ((d, ty), (_, _, value)) in static_defs.iter_mut().zip(static_types).zip(&static_asts) {
        env.statics.insert(d.name.clone(), ty.clone());
        // A non-lazy initializer must const-fold to a literal.
        if let Some(v) = value.filter(|v| !is_lazy_static_init(v)) {
            d.init = literal_to_const_val(v, &ty).unwrap_or_else(|| {
                rokc_diagnostic::set_current_span(d.span);
                err(
                    &mut pre_diags,
                    format!(
                        "static `{}` initializer must be a literal constant (stage-1 \
                         limitation)",
                        d.name
                    ),
                );
                ConstVal::Unit
            });
        }
        d.ty = ty;
    }
    let decl_roots: Vec<bool> = env
        .decls
        .iter()
        .zip(&lib_decl)
        .enumerate()
        .map(|(i, (d, &lib))| {
            let f = d.def();
            let module = match d {
                MethodOrFn::Fn(f) => module_of(&f.name),
                MethodOrFn::Method { module, .. } => module.clone(),
            };
            !lib || check_library
                || exports.iter().any(|(id, _)| id.0 as usize == i)
                || is_lazy_init_fn(&f.name)
                || lib_pkg
                    .as_ref()
                    .is_some_and(|p| within(&package_of(&module), p))
        })
        .collect();
    assign_discriminants(&env, &enum_decls);
    rokc_diagnostic::time("hir consts", || super::const_eval::check_user_consts(&env));
    let (mut functions, unlowered) = rokc_diagnostic::time("hir bodies", || {
        lower_bodies(&env, &decl_roots, &prebuilt, &inline_copies)
    });

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
    rokc_diagnostic::time("hir send check", || {
        super::send_check::check(&env, &functions);
    });
    let (any_seeds, any_exports) = super::expr::any_link(&env, lib_pkg.as_deref());
    let any_types = super::expr::any_types(&env);
    if lib_pkg.is_some() || !prebuilt.is_empty() {
        exports.extend(any_exports);
    }
    let Env {
        defs, sink, names, ..
    } = env;
    // Append every closure body / monomorphization lifted to a top-level
    // function during expression lowering.
    functions.extend(sink.extras.into_inner());
    let mut structs = defs.structs.into_inner();
    let mut enums = defs.enums.into_inner();
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
    for id in &no_safepoint {
        set(id, &|f| f.no_safepoint = true);
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
    super::caller::lower(&mut functions, &sink.track_caller.borrow());
    // A prebuilt package's statics are initialized by its `.a`.
    let lazy_inits = static_defs
        .iter()
        .filter(|s| {
            let pkg = package_of(&module_of(&s.name));
            !input.prebuilt.iter().any(|p| within(&pkg, p))
        })
        .filter_map(|s| s.init_fn);
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
    module.diagnostics.extend(names.diags.into_inner());
    module.diagnostics.extend(sink.diagnostics.into_inner());
    module
        .diagnostics
        .extend(sink.instance_warns.into_inner().agreed());
    check_unresolved_types(&mut module, &names.unknown_spans.into_inner());
    check_value_types(&mut module);
    check_packed(&mut module);
    // The same root cause can be reached from several passes (e.g. a
    // type resolved once per instantiation sweep): report it once.
    let mut seen = std::collections::HashSet::new();
    module
        .diagnostics
        .retain(|d| seen.insert(d.message.clone()));
    // A derive that failed its field check leaves its generated impl's
    // errors (located at the attribute) as a cascade: drop them.
    module.diagnostics.retain(|d| {
        d.kind == rokc_diagnostic::ErrorKind::Meta
            || !d
                .primary
                .as_ref()
                .is_some_and(|l| failed_derives.contains(&l.span))
    });
    show_nested_fn_names(program, &mut module.diagnostics);
    module
}

/// Diagnostics name a nested fn (spec 4.10) as written: its lifted
/// name `outer/inner` (`/2` .. for a repeated name) reads `inner`.
fn show_nested_fn_names(program: &Program, diags: &mut [rokc_diagnostic::RokDiagnostic]) {
    let mut lifted: Vec<(&str, &str)> = program
        .items
        .iter()
        .filter_map(|it| match it {
            Item::Fn(f) => {
                let leaf = leaf_name(&f.name);
                let (rest, last) = leaf.rsplit_once('/')?;
                let shown = if last.starts_with(|c: char| c.is_ascii_digit()) {
                    rest.rsplit_once('/')?.1
                } else {
                    last
                };
                Some((leaf, shown))
            }
            _ => None,
        })
        .collect();
    if lifted.is_empty() {
        return;
    }
    lifted.sort_by_key(|(l, _)| std::cmp::Reverse(l.len()));
    let fix = |s: &mut String| {
        for (l, shown) in &lifted {
            if s.contains(l) {
                *s = s.replace(l, shown);
            }
        }
    };
    for d in diags {
        fix(&mut d.message);
        if let Some(p) = &mut d.primary {
            fix(&mut p.message);
        }
        d.secondary.iter_mut().for_each(|l| fix(&mut l.message));
        d.notes.iter_mut().for_each(fix);
    }
}

/// Re-resolve, with the impls known, the struct fields and enum payloads
/// left open (a projection) when their type was first defined: a declared
/// one (`structs[i]` / `enums[i]`) or a generic instance under its
/// arguments. A union's storage is fixed at registration.
fn resolve_open_members(env: &Env<'_>, structs: &[&AstStructDef], enums: &[&AstEnumDef]) {
    let open = |t: &HirTy| {
        let mut o = Vec::new();
        collect_unknown_paths(t, &mut o);
        !o.is_empty()
    };
    let struct_open: Vec<(usize, &AstStructDef, Vec<HirTy>)> = env
        .defs
        .structs
        .borrow()
        .iter()
        .enumerate()
        .filter(|(_, d)| d.union_kind.is_none() && d.fields.iter().any(|f| open(&f.ty)))
        .filter_map(|(i, d)| {
            let def = match structs.get(i) {
                Some(s) if d.generic_args.is_empty() => *s,
                _ => *env.defs.generic_structs.get(enum_base_name(&d.name))?,
            };
            Some((i, def, d.generic_args.clone()))
        })
        .collect();
    for (i, def, args) in struct_open {
        let subst = generic_subst(&def.generics, &args);
        let mut rcx = LowerCtx::new(env, &subst, None);
        rcx.current_module = module_of(enum_base_name(&def.name));
        let fields = generic_struct_fields(def, &|t| rcx.resolve_ast_ty(t));
        env.defs.structs.borrow_mut()[i].fields = fields;
    }
    let enum_open: Vec<(usize, &AstEnumDef, Vec<HirTy>)> = env
        .defs
        .enums
        .borrow()
        .iter()
        .enumerate()
        .filter(|(_, d)| {
            d.variants
                .iter()
                .any(|v| v.payload_ty.as_ref().is_some_and(open))
        })
        .filter_map(|(i, d)| {
            let def = match enums.get(i) {
                Some(e) if d.generic_args.is_empty() => *e,
                _ => *env.defs.generic_enums.get(enum_base_name(&d.name))?,
            };
            Some((i, def, d.generic_args.clone()))
        })
        .collect();
    for (i, def, args) in enum_open {
        let subst = generic_subst(&def.generics, &args);
        let mut rcx = LowerCtx::new(env, &subst, None);
        rcx.current_module = module_of(enum_base_name(&def.name));
        let payloads = generic_enum_variants(def, &|t| rcx.resolve_ast_ty(t));
        let mut all = env.defs.enums.borrow_mut();
        for (v, fresh) in all[i].variants.iter_mut().zip(payloads) {
            v.payload_ty = fresh.payload_ty;
        }
    }
}

pub(super) fn reexport_key(re: &crate::uses::ReExport) -> String {
    if re.module_path.is_empty() {
        re.short_name.clone()
    } else {
        format!("{}::{}", re.module_path, re.short_name)
    }
}

/// Each `pub use` alias key → the path its chain of re-exports ends at
/// (one that is no alias itself; a cycle stops where it closes). The
/// first re-export of a key wins.
fn reexport_aliases(reexports: &[crate::uses::ReExport]) -> HashMap<String, String> {
    let mut direct: HashMap<String, &str> = HashMap::new();
    for re in reexports {
        direct
            .entry(reexport_key(re))
            .or_insert(re.full_path.as_str());
    }
    direct
        .iter()
        .map(|(alias, first)| {
            let mut seen = std::collections::HashSet::from([alias.as_str()]);
            let mut end = *first;
            while let Some(next) = direct.get(end).copied().filter(|_| seen.insert(end)) {
                end = next;
            }
            (alias.clone(), end.to_owned())
        })
        .collect()
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
        AstTyKind::Nest(x) => impl_def_display(x),
        AstTyKind::Binding(n, t) => format!("{n} = {}", impl_def_display(t)),
        AstTyKind::QPath(q) => format!(
            "<{} as {}>::{}",
            impl_def_display(&q.self_ty),
            impl_def_display(&Ty {
                kind: AstTyKind::Path(q.trait_path.clone()),
                span: ty.span,
            }),
            q.item
        ),
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

/// struct names; generic instantiations look up their base name).
pub(super) fn collect_field_visibility(
    program: &Program,
) -> HashMap<String, HashMap<String, Visibility>> {
    let mut out: HashMap<String, HashMap<String, Visibility>> = HashMap::new();
    for item in &program.items {
        rokc_diagnostic::set_current_span(item.span());
        match item {
            Item::Struct(s) => {
                let vis: HashMap<String, Visibility> = match &s.kind {
                    AstStructKind::Named(fs) => {
                        fs.iter().map(|f| (f.name.clone(), f.vis)).collect()
                    }
                    // Positional fields are named "0", "1", ... as in `HirField`.
                    AstStructKind::Tuple(fs) => fs
                        .iter()
                        .enumerate()
                        .map(|(i, f)| (i.to_string(), f.vis))
                        .collect(),
                    AstStructKind::Unit => continue,
                };
                out.entry(s.name.clone()).or_insert(vis);
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
pub(super) fn check_unresolved_types(
    module: &mut HirModule,
    spans: &HashMap<String, rokc_diagnostic::Span>,
) {
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
    let known: Vec<String> = module
        .structs
        .iter()
        .map(|s| s.name.as_str())
        .chain(module.enums.iter().map(|e| e.name.as_str()))
        .map(|n| leaf_name(n).split("__").next().unwrap_or(n).to_owned())
        .chain(super::PRIM_NAMES.iter().map(|p| (*p).to_owned()))
        .collect();
    for (t, span) in unknown_types {
        let span = spans.get(&t).copied().unwrap_or(span);
        let old = rokc_diagnostic::set_current_span(span);
        let mut d = rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Resolve,
            format!("cannot find type `{t}` in this scope"),
        );
        if let Some(s) = rokc_diagnostic::suggest(leaf_name(&t), known.iter().map(String::as_str)) {
            d = d.with_help(format!("did you mean `{s}`?"));
        }
        module.diagnostics.push(d);
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

/// Most scalar slots one value type may flatten to: nesting a generic
/// that doubles its payload (`W<W<..>>`) grows exponentially.
const MAX_VALUE_LEAVES: u64 = 1 << 16;
/// Largest value type, in (estimated) bytes.
const MAX_VALUE_BYTES: u64 = 1 << 32;

/// A struct / enum that holds itself by value (through fields, tuples,
/// sums, arrays or payloads) has no finite size; one whose flattened
/// layout passes the caps above is refused before MIR expands it.
fn check_value_types(module: &mut HirModule) {
    use std::collections::{HashMap, HashSet};
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    enum Def {
        S(usize),
        E(usize),
    }
    struct Defs<'m> {
        m: &'m HirModule,
        structs: HashMap<StructId, usize>,
        enums: HashMap<EnumId, usize>,
    }
    impl Defs<'_> {
        fn of(&self, t: &HirTy) -> Option<Def> {
            match t {
                HirTy::Struct(id) => self.structs.get(id).copied().map(Def::S),
                HirTy::Enum(id) => self.enums.get(id).copied().map(Def::E),
                _ => None,
            }
        }
        fn children(&self, d: Def) -> Vec<&HirTy> {
            match d {
                Def::S(i) => self.m.structs[i].fields.iter().map(|f| &f.ty).collect(),
                Def::E(i) => self.m.enums[i]
                    .variants
                    .iter()
                    .filter_map(|v| v.payload_ty.as_ref())
                    .collect(),
            }
        }
        // Defs held by value, through tuples / sums / arrays.
        fn inline(&self, t: &HirTy, out: &mut Vec<Def>) {
            match t {
                HirTy::Tuple(ps) | HirTy::Sum(ps) => ps.iter().for_each(|p| self.inline(p, out)),
                HirTy::Array(e, _) => self.inline(e, out),
                t => out.extend(self.of(t)),
            }
        }
        fn edges(&self, d: Def) -> Vec<Def> {
            let mut out = Vec::new();
            for t in self.children(d) {
                self.inline(t, &mut out);
            }
            out
        }
        // Source name (`W<..>` for an instance), span, "a struct" / "an enum".
        fn name_span(&self, d: Def) -> (String, rokc_diagnostic::Span, &'static str) {
            let (name, generic, span, kind) = match d {
                Def::S(i) => {
                    let s = &self.m.structs[i];
                    (&s.name, !s.generic_args.is_empty(), s.span, "a struct")
                }
                Def::E(i) => {
                    let e = &self.m.enums[i];
                    (&e.name, !e.generic_args.is_empty(), e.span, "an enum")
                }
            };
            let base = name.split("__").next().unwrap_or(name);
            let name = if generic {
                format!("{base}<..>")
            } else {
                base.to_owned()
            };
            (name, span, kind)
        }
        // (scalar slots, estimated bytes); saturating.
        fn size(&self, t: &HirTy, memo: &mut HashMap<Def, (u64, u64)>) -> (u64, u64) {
            let add =
                |a: (u64, u64), b: (u64, u64)| (a.0.saturating_add(b.0), a.1.saturating_add(b.1));
            match t {
                HirTy::Tuple(ps) | HirTy::Sum(ps) => ps
                    .iter()
                    .fold((1, 8), |acc, p| add(acc, self.size(p, memo))),
                HirTy::Array(elem, len) => {
                    let (slots, bytes) = self.size(elem, memo);
                    (slots, bytes.saturating_mul(u64::from(*len)))
                }
                t => match self.of(t) {
                    Some(d) => {
                        if let Some(v) = memo.get(&d) {
                            return *v;
                        }
                        // Provisional entry: cycles were reported already.
                        memo.insert(d, (1, 8));
                        let v = self
                            .children(d)
                            .iter()
                            .fold((1, 8), |acc, c| add(acc, self.size(c, memo)));
                        memo.insert(d, v);
                        v
                    }
                    None => (1, 8),
                },
            }
        }
    }
    let defs = Defs {
        m: module,
        structs: module
            .structs
            .iter()
            .enumerate()
            .map(|(i, s)| (s.id, i))
            .collect(),
        enums: module
            .enums
            .iter()
            .enumerate()
            .map(|(i, e)| (e.id, i))
            .collect(),
    };
    let all: Vec<Def> = (0..module.structs.len())
        .map(Def::S)
        .chain((0..module.enums.len()).map(Def::E))
        .collect();
    let mut errs = Vec::new();
    for &d in &all {
        let mut stack = defs.edges(d);
        let mut seen = HashSet::new();
        while let Some(x) = stack.pop() {
            if x == d {
                let (name, span, kind) = defs.name_span(d);
                errs.push((
                    span,
                    format!(
                        "recursive type `{name}` has infinite size ({kind} can't contain \
                         itself by value; hold it through a reference type such as `List`)"
                    ),
                ));
                break;
            }
            if seen.insert(x) {
                stack.extend(defs.edges(x));
            }
        }
    }
    if errs.is_empty() {
        let mut memo = HashMap::new();
        for &d in &all {
            let t = match d {
                Def::S(i) => HirTy::Struct(module.structs[i].id),
                Def::E(i) => HirTy::Enum(module.enums[i].id),
            };
            let (leaves, bytes) = defs.size(&t, &mut memo);
            if leaves > MAX_VALUE_LEAVES || bytes > MAX_VALUE_BYTES {
                let (name, span, _) = defs.name_span(d);
                errs.push((
                    span,
                    format!(
                        "value type `{name}` is too large ({leaves} scalar slots, ~{bytes} \
                         bytes; the limit is {MAX_VALUE_LEAVES} slots / {MAX_VALUE_BYTES} bytes)"
                    ),
                ));
                break;
            }
        }
    }
    for (span, msg) in errs {
        let old = rokc_diagnostic::set_current_span(span);
        module
            .diagnostics
            .push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                msg,
            ));
        rokc_diagnostic::set_current_span(old);
    }
}

/// Spec 6.2.2: a `#[repr(packed)]` struct is for C data; its fields may
/// sit unaligned, where the collector cannot read a reference.
fn check_packed(module: &mut HirModule) {
    fn gc(m: &HirModule, t: &HirTy, seen: &mut Vec<HirTy>) -> bool {
        if seen.contains(t) {
            return false;
        }
        seen.push(t.clone());
        let mut rec = |t: &HirTy| gc(m, t, seen);
        match t {
            HirTy::Prim(PrimTy::Str)
            | HirTy::GcBuf(_)
            | HirTy::Any
            | HirTy::AnyTrait(_)
            | HirTy::Closure { .. } => true,
            HirTy::Fn(..) => !t.is_c_fn(),
            HirTy::Tuple(ts) | HirTy::Sum(ts) => ts.iter().any(rec),
            HirTy::Array(e, n) => *n > 0 && rec(e),
            HirTy::Throws { ok, err } => rec(ok) || rec(err),
            HirTy::Struct(id) => {
                let s = &m.structs[id.0 as usize];
                match &s.union_kind {
                    Some(u) if matches!(u.storage, crate::UnionStorage::ByteArray) => false,
                    _ => s.fields.iter().any(|f| rec(&f.ty)),
                }
            }
            HirTy::Enum(id) => m.enums[id.0 as usize]
                .variants
                .iter()
                .filter_map(|v| v.payload_ty.as_ref())
                .any(rec),
            _ => false,
        }
    }
    let bad: Vec<(rokc_diagnostic::Span, String)> = module
        .structs
        .iter()
        .filter(|s| s.repr.packed && s.fields.iter().any(|f| gc(module, &f.ty, &mut Vec::new())))
        .map(|s| {
            (
                s.span,
                s.name.split("__").next().unwrap_or(&s.name).to_owned(),
            )
        })
        .collect();
    for (span, name) in bad {
        module.diagnostics.push(
            rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`#[repr(packed)]` struct `{}` holds a GC reference (`str`, a collection, \
                     a closure ..); a packed struct is for C data (spec 6.2.2)",
                    leaf_name(&name)
                ),
            )
            .with_span(span, ""),
        );
    }
}

pub(super) fn collect_unknown_paths(ty: &HirTy, out: &mut Vec<String>) {
    match ty {
        HirTy::Path(p) => {
            out.push(p.join("::"));
        }
        // Open until inference or a binding fixes them (an inference
        // variable shows as `_`).
        HirTy::Var(_) => out.push("_".to_owned()),
        HirTy::OpenConst(n) => out.push(n.clone()),
        HirTy::NoThrow => out.push("#nothrow".to_owned()),
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
        K::BufNew { len, .. } | K::RawRead { addr: len, .. } | K::AddrOf { place: len } => {
            hir_expr_has_unknown(len)
        }
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
    defs: &TypeDefs<'_>,
    sc: Scope<'_>,
) -> HirEnumDef {
    let variants = e
        .variants
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let tag = i128::try_from(i).expect("variant index overflow");
            match &v.kind {
                // A value variant's tag is filled in once consts are known
                // (`assign_discriminants`).
                AstEnumVariantKind::Unit | AstEnumVariantKind::Value(_) => HirEnumVariant {
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
                    payload_ty: Some(resolve_ty_with_structs(&tys[0], defs, None, sc)),
                    named_fields: Vec::new(),
                    arity: 1,
                },
                // Multi-element tuple — pack into a tuple payload type.
                AstEnumVariantKind::Tuple(tys) => HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(HirTy::Tuple(
                        tys.iter()
                            .map(|t| resolve_ty_with_structs(t, defs, None, sc))
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
                            .map(|f| resolve_ty_with_structs(&f.ty, defs, None, sc))
                            .collect(),
                    )),
                    named_fields: fields.iter().map(|f| f.name.clone()).collect(),
                    arity: fields.len(),
                },
            }
        })
        .collect();
    HirEnumDef {
        id,
        repr: repr_of(&e.attrs).unwrap_or_default(),
        def_id: None,
        name: e.name.clone(),
        variants,
        span: e.span,
        generic_args: Vec::new(),
    }
}

/// `#[niche(..)]` arguments (spec 2.7.4): integer literals, `MIN` /
/// `MAX` (`i32::MIN`, `I32_MIN`), `NAN` / `INFINITY` / `NEG_INFINITY`
/// (`f64::NAN`, `F::NAN`) and ranges of them. Empty without the
/// attribute; `Err` describes the first argument it cannot read.
pub(super) fn niche_args(attrs: &[rokc_ast::Attribute]) -> Result<Vec<NicheArg>, String> {
    use rokc_ast::{AttrArg, AttrBody, Literal};
    let Some(attr) = attrs.iter().find(|a| a.name() == "niche") else {
        return Ok(Vec::new());
    };
    let AttrBody::Args(args) = &attr.body else {
        return Err("`#[niche]` takes arguments: `#[niche(0)]`".to_owned());
    };
    let val = |a: &AttrArg| -> Option<NicheVal> {
        let name = match a {
            AttrArg::Lit(Literal::Int(text)) => {
                let (body, neg) = text
                    .strip_prefix('-')
                    .map_or((text.as_str(), false), |b| (b, true));
                let (v, _) = super::expr::parse_int_literal(body)?;
                return Some(NicheVal::Int(if neg { -v } else { v }));
            }
            AttrArg::Word(w) => w.as_str(),
            AttrArg::Nested { path, body } if matches!(**body, AttrBody::Empty) => path.last()?,
            _ => return None,
        };
        Some(match name {
            "NAN" => NicheVal::Nan,
            "INFINITY" => NicheVal::Inf,
            "NEG_INFINITY" => NicheVal::NegInf,
            "MIN" => NicheVal::Min,
            "MAX" => NicheVal::Max,
            _ => {
                let (ty, end) = name.rsplit_once('_')?;
                let bits: u32 = match ty {
                    "ISIZE" | "USIZE" => 64,
                    _ => ty.get(1..)?.parse().ok()?,
                };
                let signed = match ty.as_bytes().first()? {
                    b'I' => true,
                    b'U' => false,
                    _ => return None,
                };
                if !matches!(bits, 8 | 16 | 32 | 64) {
                    return None;
                }
                NicheVal::Int(match (signed, end) {
                    (true, "MIN") => -(1i128 << (bits - 1)),
                    (true, "MAX") => (1i128 << (bits - 1)) - 1,
                    (false, "MIN") => 0,
                    (false, "MAX") => (1i128 << bits) - 1,
                    _ => return None,
                })
            }
        })
    };
    args.iter()
        .enumerate()
        .map(|(i, a)| {
            let bad = || {
                format!(
                    "`#[niche]` argument {}: expected an integer, `MIN` / `MAX`, `NAN` / \
                     `INFINITY` / `NEG_INFINITY`, or a range of them",
                    i + 1
                )
            };
            match a {
                AttrArg::Range { lo, hi, inclusive } => {
                    let lo = lo
                        .as_deref()
                        .map_or(Some(NicheVal::Min), val)
                        .ok_or_else(bad)?;
                    let hi = match (hi.as_deref().map(val), inclusive) {
                        (None, _) => NicheVal::Max,
                        (Some(Some(v)), true) => v,
                        (Some(Some(NicheVal::Int(v))), false) => NicheVal::Int(v - 1),
                        _ => return Err(bad()),
                    };
                    Ok(NicheArg::Range(lo, hi))
                }
                _ => val(a).map(NicheArg::Val).ok_or_else(bad),
            }
        })
        .collect()
}

/// `#[repr(..)]` arguments (spec 6.2.2), unchecked against the item.
pub(super) fn repr_of(attrs: &[rokc_ast::Attribute]) -> Result<crate::Repr, String> {
    use rokc_ast::{AttrArg, AttrBody, Literal};
    let mut r = crate::Repr::default();
    for attr in attrs.iter().filter(|a| a.name() == "repr") {
        let AttrBody::Args(args) = &attr.body else {
            return Err("`#[repr]` takes arguments: `#[repr(C)]`".to_owned());
        };
        for a in args {
            match a {
                AttrArg::Word(w) => match w.as_str() {
                    "C" => r.c = true,
                    "transparent" => r.transparent = true,
                    "packed" => r.packed = true,
                    w => {
                        r.int = Some(match w {
                            "u8" => PrimTy::U8,
                            "i8" => PrimTy::I8,
                            "u16" => PrimTy::U16,
                            "i16" => PrimTy::I16,
                            "u32" => PrimTy::U32,
                            "i32" => PrimTy::I32,
                            "u64" => PrimTy::U64,
                            "i64" => PrimTy::I64,
                            _ => return Err(format!("unknown `#[repr]` argument `{w}`")),
                        });
                    }
                },
                AttrArg::Nested { path, body } if path.as_slice() == ["align"] => {
                    let n = match &**body {
                        AttrBody::Args(v) => match v.as_slice() {
                            [AttrArg::Lit(Literal::Int(t))] => super::expr::parse_int_literal(t)
                                .and_then(|(v, _)| u32::try_from(v).ok()),
                            _ => None,
                        },
                        _ => None,
                    };
                    match n {
                        Some(n) if n.is_power_of_two() && n <= 1 << 29 => r.align = n,
                        _ => {
                            return Err("`align(N)` takes a power of two up to 2^29".to_owned());
                        }
                    }
                }
                _ => return Err("unknown `#[repr]` argument".to_owned()),
            }
        }
    }
    Ok(r)
}

/// `#[repr(..)]` arguments and placement (spec 6.2.2).
fn check_repr_attrs(program: &rokc_ast::Program, diags: &mut Vec<rokc_diagnostic::RokDiagnostic>) {
    for item in &program.items {
        let attrs = match item {
            Item::Struct(s) => &s.attrs,
            Item::Enum(e) => &e.attrs,
            Item::Union(u) => &u.attrs,
            _ => continue,
        };
        let Some(attr) = attrs.iter().find(|a| a.name() == "repr") else {
            continue;
        };
        rokc_diagnostic::set_current_span(attr.span);
        let msg = match (repr_of(attrs), item) {
            (Err(e), _) => Some(e),
            (Ok(r), Item::Struct(s)) => {
                let n = match &s.kind {
                    AstStructKind::Named(fs) => fs.len(),
                    AstStructKind::Tuple(fs) => fs.len(),
                    AstStructKind::Unit => 0,
                };
                if r.int.is_some() {
                    Some("an integer `#[repr]` goes on an enum, not a struct".to_owned())
                } else if r.packed && r.align != 0 {
                    Some("a struct cannot be both `packed` and `align(N)`".to_owned())
                } else if r.transparent && (r.c || r.packed || r.align != 0) {
                    Some("`#[repr(transparent)]` takes no other argument".to_owned())
                } else if r.transparent && n != 1 {
                    Some(format!(
                        "`#[repr(transparent)]` needs exactly one field, not {n}"
                    ))
                } else {
                    None
                }
            }
            (Ok(r), Item::Enum(e)) => {
                let data = e.variants.iter().any(|v| {
                    !matches!(
                        v.kind,
                        AstEnumVariantKind::Unit | AstEnumVariantKind::Value(_)
                    )
                });
                if r.packed || r.transparent || r.align != 0 {
                    Some("an enum takes only `C` or an integer `#[repr]`".to_owned())
                } else if data
                    && r.int
                        .is_some_and(|p| !matches!(p, PrimTy::I32 | PrimTy::U32))
                {
                    Some(
                        "a data-carrying enum's tag is 32 bits: only `#[repr(i32)]` / \
                         `#[repr(u32)]`"
                            .to_owned(),
                    )
                } else {
                    None
                }
            }
            (Ok(r), _) => (r.packed || r.transparent || r.align != 0 || r.int.is_some())
                .then(|| "a union takes only `#[repr(C)]`".to_owned()),
        };
        if let Some(msg) = msg {
            diags.push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                msg,
            ));
        }
    }
}

/// Value variants (spec 2.4.2): an enum with any is all value variants;
/// each value is a const integer (the const evaluator: `const fn`
/// calls, `use`d consts) that fits the tag type and is unique.
fn assign_discriminants(env: &Env<'_>, decls: &[&AstEnumDef]) {
    let no_subst = HashMap::new();
    for (i, decl) in decls.iter().enumerate() {
        let values = decl
            .variants
            .iter()
            .filter(|v| matches!(v.kind, AstEnumVariantKind::Value(_)))
            .count();
        if values == 0 {
            continue;
        }
        let mut ctx = LowerCtx::new(env, &no_subst, None);
        ctx.current_module = module_of(&decl.name);
        let err = |msg: String| {
            rokc_diagnostic::set_current_span(decl.span);
            ctx.emit_error(rokc_diagnostic::ErrorKind::Type, msg);
        };
        if values != decl.variants.len() {
            err(format!(
                "enum `{}` mixes value variants (`V = n`) with other variants; \
                 a value enum has only value variants",
                decl.name
            ));
            continue;
        }
        let id = EnumId(u32::try_from(i).expect("EnumId overflow"));
        let tag_ty = ctx.enum_def(id).repr.int.unwrap_or(PrimTy::I32);
        let mut seen: HashMap<i128, &str> = HashMap::new();
        let mut tags = Vec::new();
        for v in &decl.variants {
            let AstEnumVariantKind::Value(e) = &v.kind else {
                continue;
            };
            let c = rokc_ast::ConstExpr::Expr(Box::new(e.clone()));
            let n = match ctx.eval_const_msg(&c) {
                Ok(n) => n,
                Err(why) => {
                    err(format!(
                        "the value of `{}::{}` is not a const integer: {why}",
                        decl.name, v.name
                    ));
                    tags.push(None);
                    continue;
                }
            };
            let (lo, hi) = super::const_eval::int_range(tag_ty);
            if !(lo..=hi).contains(&n) {
                err(format!(
                    "the value {n} of `{}::{}` does not fit the tag type `{}`",
                    decl.name,
                    v.name,
                    tag_ty.name()
                ));
                tags.push(None);
                continue;
            }
            if let Some(other) = seen.insert(n, &v.name) {
                err(format!(
                    "`{}::{}` and `{}::{other}` have the same value {n}",
                    decl.name, v.name, decl.name
                ));
            }
            tags.push(Some(n));
        }
        let mut enums = env.defs.enums.borrow_mut();
        for (hv, t) in enums[i].variants.iter_mut().zip(tags) {
            if let Some(n) = t {
                hv.tag = n;
            }
        }
    }
}

/// `#[niche]` placement (spec 2.7.5): a single-field struct only.
fn check_niche_attrs(program: &rokc_ast::Program, diags: &mut Vec<rokc_diagnostic::RokDiagnostic>) {
    for item in &program.items {
        // `misplaced`: what the attribute sits on, if not one field.
        let (attrs, misplaced) = match item {
            Item::Struct(s) => {
                let n = match &s.kind {
                    AstStructKind::Named(fs) => fs.len(),
                    AstStructKind::Tuple(fs) => fs.len(),
                    AstStructKind::Unit => 0,
                };
                (
                    &s.attrs,
                    (n != 1).then(|| format!("a struct with {n} fields")),
                )
            }
            Item::Enum(e) => (&e.attrs, Some("an enum".to_owned())),
            Item::Union(u) => (&u.attrs, Some("a union".to_owned())),
            _ => continue,
        };
        let Some(attr) = attrs.iter().find(|a| a.name() == "niche") else {
            continue;
        };
        rokc_diagnostic::set_current_span(attr.span);
        let msg = match misplaced {
            None => niche_args(attrs).err(),
            Some(w) => Some(format!(
                "`#[niche]` goes on a single-field struct, not {w} (spec 2.7.5)"
            )),
        };
        if let Some(msg) = msg {
            diags.push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                msg,
            ));
        }
    }
}

pub(super) fn lower_struct_def(
    s: &AstStructDef,
    id: StructId,
    defs: &TypeDefs<'_>,
    sc: Scope<'_>,
) -> HirStructDef {
    let fields = match &s.kind {
        AstStructKind::Named(fs) => fs
            .iter()
            .map(|f| HirField {
                name: f.name.clone(),
                ty: resolve_ty_with_structs(&f.ty, defs, None, sc),
                // A literal omitting the field fills it at the use site.
                default: f.default.clone().map(|d| in_module(&module_of(&s.name), d)),
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
                ty: resolve_ty_with_structs(&f.ty, defs, None, sc),
                default: None,
            })
            .collect(),
        AstStructKind::Unit => Vec::new(),
    };
    HirStructDef {
        id,
        repr: repr_of(&s.attrs).unwrap_or_default(),
        def_id: None,
        name: s.name.clone(),
        fields,
        span: s.span,
        generic_args: Vec::new(),
        union_kind: None,
        niche: niche_args(&s.attrs).unwrap_or_default(),
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
    defs: &TypeDefs<'_>,
    sc: Scope<'_>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> HirStructDef {
    let aliases: Vec<(String, HirTy)> = u
        .fields
        .iter()
        .map(|f| {
            (
                f.name.clone(),
                resolve_ty_with_structs(&f.ty, defs, None, sc),
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
        // Every field side by side; MIR overlays them (`union_storage`).
        UnionStorage::ByteArray => HirTy::Tuple(aliases.iter().map(|(_, t)| t.clone()).collect()),
    };
    HirStructDef {
        id,
        repr: repr_of(&u.attrs).unwrap_or_default(),
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
        niche: Vec::new(),
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
            format!("union `{name}` declares no fields"),
        ));
        return UnionStorage::WidestPrim(PrimTy::U8);
    }
    let all_prim = aliases
        .iter()
        .all(|(_, t)| matches!(t, HirTy::Prim(p) if *p != PrimTy::Str));
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
    UnionStorage::ByteArray
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
        AstTyKind::QPath(q) => std::iter::once(&q.self_ty)
            .chain(q.trait_path.segments.iter().flat_map(|s| &s.generics))
            .collect(),
        AstTyKind::AnyTrait(bounds) => bounds
            .iter()
            .flat_map(|b| b.segments.iter().flat_map(|s| &s.generics))
            .collect(),
        AstTyKind::Sum(parts) | AstTyKind::Tuple(parts) => parts.iter().collect(),
        AstTyKind::Fn(args, ret, _) => args.iter().chain(std::iter::once(&**ret)).collect(),
        AstTyKind::Throws { ok, err } => vec![&**ok, &**err],
        AstTyKind::Array(elem, _) | AstTyKind::Nest(elem) | AstTyKind::Binding(_, elem) => {
            vec![&**elem]
        }
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
) -> Impl {
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
            // `trait Contains<Item>` + `impl<T> Contains<T> for L<T>`: the
            // default's signature sees `Item = T`.
            let mut tm = tm.clone();
            let mut args = trait_param_args(td, impl_def);
            supertrait_projections(&tm, td, impl_def, &mut args);
            subst_assoc_sig(&mut tm, &args);
            methods.insert(tm.name.clone(), template(&tm, &trait_module));
        }
    }
    Impl {
        trait_key,
        trait_args: impl_def
            .trait_path
            .as_ref()
            .and_then(|tp| tp.segments.last())
            .map(|s| s.generics.clone())
            .unwrap_or_default(),
        assoc: impl_assoc_list(impl_def),
        generics: impl_def.generics.clone(),
        where_clause: impl_def.where_clause.clone(),
        self_ty: impl_def.self_ty.clone(),
        module: module.to_owned(),
        methods,
        consts: Vec::new(),
        concrete: None,
    }
}

/// An impl that is not a generic trait impl, registered by its written
/// target (`at`: its `Impl`).
struct PendingImpl<'p> {
    def: &'p rokc_ast::ImplDef,
    module: String,
    trait_name: Option<String>,
    /// The target's generic base / primitive name (method templates).
    generic_base: Option<String>,
    at: usize,
}

/// Each pending impl's target and the trait ref it provides, resolved
/// once every item is registered (a generic inherent impl's target is
/// its base). A projection (`impl Tr for <A as P>::Out`) resolves
/// through the impls resolved before it, so rounds repeat while one
/// resolves; the last round reports what is left. `None`: an impl of a
/// trait (with the same arguments) its target already has.
fn impl_heads(
    env: &mut Env<'_>,
    pending: &[PendingImpl<'_>],
    trait_defs: &HashMap<String, &rokc_ast::TraitDef>,
    diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> Vec<Option<(HirTy, Option<TraitRef>)>> {
    let mut heads = vec![None; pending.len()];
    let mut left: Vec<usize> = Vec::new();
    for (i, p) in pending.iter().enumerate() {
        if p.def.generics.params.is_empty() {
            left.push(i);
        } else {
            let base = p.generic_base.clone().unwrap_or_default();
            heads[i] = Some((HirTy::Path(vec![base]), None));
        }
    }
    let open = |t: &HirTy| {
        let mut paths = Vec::new();
        collect_unknown_paths(t, &mut paths);
        *t == HirTy::Unknown || !paths.is_empty()
    };
    let mut last = false;
    let no_subst = HashMap::new();
    while !left.is_empty() {
        // One round's heads, against the impls resolved before it; one
        // still open waits (its diagnostics dropped) unless it is the last.
        let round: Vec<Option<(HirTy, Option<TraitRef>)>> = {
            let mut rcx = LowerCtx::new(env, &no_subst, None);
            left.iter()
                .map(|&i| {
                    let p = &pending[i];
                    rokc_diagnostic::set_current_span(p.def.span);
                    let mark = env.sink.diagnostics.borrow().len();
                    let td = p
                        .trait_name
                        .as_ref()
                        .and_then(|t| trait_defs.get(t).copied());
                    let (ty, provides) = impl_head(&mut rcx, p, td);
                    let unresolved = open(&ty)
                        || provides.as_ref().is_some_and(|r| {
                            r.args
                                .iter()
                                .chain(r.binds.iter().map(|(_, t)| t))
                                .any(open)
                        });
                    if unresolved && !last {
                        env.sink.diagnostics.borrow_mut().truncate(mark);
                        return None;
                    }
                    Some((ty, provides))
                })
                .collect()
        };
        let mut waiting = Vec::new();
        for (&i, head) in left.iter().zip(round) {
            let p = &pending[i];
            let Some((ty, provides)) = head else {
                waiting.push(i);
                continue;
            };
            rokc_diagnostic::set_current_span(p.def.span);
            if let Some(r) = provides.as_ref().filter(|r| !r.args.is_empty()) {
                if env
                    .impls
                    .refs_on(&ty)
                    .any(|o| o.path == r.path && o.args == r.args)
                {
                    let shown = TraitRef::new(r.path.clone(), r.args.clone(), Vec::new());
                    let shown = shown.render(&r.path, |t| match t {
                        HirTy::Struct(id) => env.defs.structs.borrow()[id.0 as usize].name.clone(),
                        HirTy::Enum(id) => env.defs.enums.borrow()[id.0 as usize].name.clone(),
                        t => ty_mangle(t),
                    });
                    diags.push(rokc_diagnostic::RokDiagnostic::error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "`{shown}` is implemented more than once for `{}`",
                            impl_def_display(&p.def.self_ty)
                        ),
                    ));
                    continue;
                }
            }
            env.impls.resolve(p.at, ty.clone(), provides.clone());
            heads[i] = Some((ty, provides));
        }
        last = waiting.len() == left.len();
        left = waiting;
    }
    heads
}

/// A concrete impl's target and, for a trait impl, the trait ref it
/// provides: `impl Get<i32> for T { type Item = u8; }` also answers
/// `Get<i32>`, `Get<Item = u8>` and `Get<i32, Item = u8>`.
fn impl_head(
    rcx: &mut LowerCtx<'_>,
    p: &PendingImpl<'_>,
    trait_def: Option<&rokc_ast::TraitDef>,
) -> (HirTy, Option<TraitRef>) {
    rcx.self_ty = None;
    rcx.current_module.clone_from(&p.module);
    let target = rcx.resolve_ast_ty(&p.def.self_ty);
    let Some(tn) = &p.trait_name else {
        return (target, None);
    };
    if method_target_for(&target).is_none() {
        return (target, None);
    }
    rcx.self_ty = Some(target.clone());
    let mut args: Vec<HirTy> = p
        .def
        .trait_path
        .as_ref()
        .and_then(|tp| tp.segments.last())
        .map(|s| s.generics.iter().map(|g| rcx.resolve_ast_ty(g)).collect())
        .unwrap_or_default();
    // Spec 2.10.5: omitted trait arguments take the parameter's default
    // (`trait Add<Rhs = Self>`: `impl Add for V` is `impl Add<V> for V`).
    if let Some(td) = trait_def {
        for gp in td.generics.params.iter().skip(args.len()) {
            let rokc_ast::GenericParam::Type {
                default: Some(d), ..
            } = gp
            else {
                break;
            };
            args.push(rcx.resolve_ast_ty(d));
        }
    }
    let assoc = impl_assoc_list(p.def)
        .iter()
        .map(|(n, t)| (n.clone(), rcx.resolve_ast_ty(t)))
        .collect();
    (target, Some(TraitRef::new(tn.clone(), args, assoc)))
}

/// An impl's `type X = T;` items, in order.
fn impl_assoc_list(impl_def: &rokc_ast::ImplDef) -> Vec<(String, Ty)> {
    impl_def
        .items
        .iter()
        .filter_map(|i| match i {
            AstImplItem::AssocType { name, ty } => Some((name.clone(), ty.clone())),
            _ => None,
        })
        .collect()
}

/// An impl's consts plus, in a trait impl, the trait's defaults it
/// leaves out: keyed `(Type::NAME, type, value)` where `Type::NAME`
/// names one (see below), and all of them. The key uses the generic
/// base (`Box::N` for `impl<T> Box<T>`) or a primitive's name.
// One key per base type: two impls of a generic base (`Box<i32>`,
// `Box<f64>`) can't give the same const different values.
fn impl_consts(
    i: &rokc_ast::ImplDef,
    program: &Program,
    names: &TypeNames<'_>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> (Vec<AssocConst>, Vec<AssocConst>) {
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
        return (Vec::new(), out);
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
    let keyed = keyed_target.map_or_else(Vec::new, |t| {
        out.iter()
            .map(|(n, ty, v)| (format!("{t}::{n}"), ty.clone(), v.clone()))
            .collect()
    });
    (keyed, out)
}

/// Lower declaration `i` (`stub`: its signature only).
pub(super) fn lower_decl(env: &Env<'_>, i: usize, stub: bool) -> HirFunction {
    let id = FunctionId(u32::try_from(i).expect("FunctionId overflow"));
    let f = env.decls[i].def();
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
/// Prebuilt functions (`linked`) keep only their signatures.
fn lower_bodies(
    env: &Env<'_>,
    roots: &[bool],
    linked: &std::collections::HashSet<FunctionId>,
    copies: &std::collections::HashSet<FunctionId>,
) -> (Vec<HirFunction>, Vec<FunctionId>) {
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
            #[allow(clippy::cast_possible_truncation)]
            let id = FunctionId(i as u32);
            let f = lower(i, linked.contains(&id) && !copies.contains(&id));
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
    env.sink.bodies_done.set(true);
    let mut unlowered = Vec::new();
    let functions = done
        .into_iter()
        .enumerate()
        .map(|(i, f)| {
            f.unwrap_or_else(|| {
                let stub = sig_stub(env, i);
                unlowered.push(stub.id);
                stub
            })
        })
        .collect();
    (functions, unlowered)
}

/// The body-less stub of unreached declaration `i`, from its resolved
/// signature (for tools; MIR drops it).
fn sig_stub(env: &Env<'_>, i: usize) -> HirFunction {
    let id = FunctionId(u32::try_from(i).expect("FunctionId overflow"));
    let f = env.decls[i].def();
    let name = match &env.decls[i] {
        MethodOrFn::Fn(f) => f.name.clone(),
        MethodOrFn::Method { key, .. } => key.clone(),
    };
    let sig = &env.fn_table[&env.key_of[&id]];
    let mut params = Vec::with_capacity(f.params.len());
    let mut locals = Vec::with_capacity(f.params.len());
    let mut refs = Vec::new();
    for (k, (p, ty)) in f.params.iter().zip(&sig.param_tys).enumerate() {
        let local = rokc_ir_common::LocalId(u32::try_from(k).expect("LocalId overflow"));
        if p.by_ref {
            refs.push(ty.clone());
        }
        locals.push(HirLocal {
            id: local,
            name: Some(p.name.clone()),
            ty: ty.clone(),
        });
        params.push(HirParam {
            name: p.name.clone(),
            local,
            ty: ty.clone(),
            by_ref: p.by_ref,
        });
    }
    HirFunction {
        id,
        def_id: None,
        name,
        params,
        locals,
        ret_ty: super::mono::ref_packed(&sig.ret_ty, &refs),
        body: None,
        is_async: false,
        is_generator: false,
        span: f.span,
        facts: rokc_ir_common::FnFacts::default(),
    }
}

/// Spec 6.2.1 / stdlib 2.5.9, 2.13.3: `#[derive(Tr)]` needs every field
/// to implement `Tr` (checked here on non-generic types; a generic one's
/// impl bounds its parameters by `Tr`), and `Copy` excludes `Drop`.
/// The spans of the derive attributes that failed.
fn check_derives(env: &Env<'_>, program: &Program) -> Vec<rokc_diagnostic::Span> {
    let mut failed = Vec::new();
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None);
    for item in &program.items {
        let (attrs, name, generic, fields): (_, _, _, Vec<(String, HirTy)>) = match item {
            Item::Struct(s) => (
                &s.attrs,
                &s.name,
                !s.generics.params.is_empty(),
                env.defs.struct_id(&s.name).map_or_else(Vec::new, |id| {
                    ctx.struct_def(id)
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
                env.defs.enum_id(&e.name).map_or_else(Vec::new, |id| {
                    ctx.enum_def(id)
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
            Item::Struct(s) => env.defs.struct_id(&s.name).map(HirTy::Struct),
            Item::Enum(e) => env.defs.enum_id(&e.name).map(HirTy::Enum),
            _ => None,
        };
        check_pod(&ctx, attrs, name, self_ty.as_ref(), &fields);
        for (tr, at) in rokc_parser::derive::derive_names(attrs) {
            let Some(key) = rokc_parser::derive::derivable(&tr) else {
                continue;
            };
            rokc_diagnostic::set_current_span(at);
            for (field, ty) in &fields {
                if !ctx.has_trait(ty, key) {
                    failed.push(at);
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
                    .is_some_and(|t| ctx.has_trait(t, ctx.lang("drop_method")))
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
    failed
}

/// A `Pod` type (stdlib 1.3.3, `#[derive(Pod)]` or a hand-written impl):
/// a `#[repr(C)]` / `#[repr(transparent)]` struct of `Pod` fields
/// without `Drop`.
fn check_pod(
    ctx: &LowerCtx<'_>,
    attrs: &[rokc_ast::Attribute],
    name: &str,
    self_ty: Option<&HirTy>,
    fields: &[(String, HirTy)],
) {
    const POD: &str = "rok::bare::mem::Pod";
    let Some(ty) = self_ty.filter(|t| ctx.has_trait(t, POD)) else {
        return;
    };
    let fail = |why: String| {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Meta,
            format!(
                "`{}` cannot be `Pod`: {why} (stdlib 1.3.3)",
                leaf_name(name)
            ),
        );
    };
    if !matches!(ty, HirTy::Struct(_)) {
        return fail("only a struct can be".to_owned());
    }
    let repr = repr_of(attrs).unwrap_or_default();
    if !repr.c && !repr.transparent {
        fail("it needs `#[repr(C)]` or `#[repr(transparent)]`".to_owned());
    }
    if ctx.has_trait(ty, ctx.lang("drop_method")) {
        fail("it implements `Drop`".to_owned());
    }
    for (field, fty) in fields {
        if !ctx.has_trait(fty, POD) {
            fail(format!(
                "`{field}` has type `{}`, which is not `Pod`",
                ctx.ty_name(fty)
            ));
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
    let n_structs = env.defs.structs.borrow().len();
    let n_enums = env.defs.enums.borrow().len();
    let mut insts: Vec<Inst<'_>> = Vec::new();
    for i in 0..n_structs {
        let id = StructId(u32::try_from(i).expect("StructId overflow"));
        let d = ctx.struct_def(id);
        let base = d.name.split("__").next().unwrap_or_default().to_owned();
        if let Some(def) = env
            .defs
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
            .defs
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
                    .map_or(HirTy::Unknown, |v| HirTy::Const(v, None)),
                _ => resolve_ty_with_structs(a, &env.defs, None, sc),
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
                let module = rcx.current_module.clone();
                let Some(want) = rcx.bound_ref(b, &module, |t| rcx.resolve_ast_ty(t)) else {
                    continue;
                };
                if !rcx.implements_trait(&ty, &want, 0) {
                    let old = rokc_diagnostic::set_current_span(span);
                    rcx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "type `{}` does not satisfy trait bound `{}` required by `{shown}` \
                             (spec 2.10.4)",
                            rcx.ty_name(&ty),
                            rcx.trait_name(&want),
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
/// Trait impls: the orphan rule (spec 2.9.5: the trait or the target
/// type is the impl's package's own), and supertraits (spec 2.8.4: a
/// type implementing a trait implements its supertraits too; a generic
/// impl's target must meet them for every instance its bounds allow).
fn check_impl_rules(env: &Env<'_>, program: &Program) {
    let no_subst = HashMap::new();
    for item in &program.items {
        let Item::Impl(i) = item else {
            continue;
        };
        let Some(tp) = &i.trait_path else {
            continue;
        };
        let module = impl_module(i);
        let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
        let key = env.names.trait_key(&segs, &module);
        let pkg = package_of(&module);
        if package_of(&module_of(&key)) != pkg && target_package(env, i, &module) != Some(pkg) {
            rokc_diagnostic::set_current_span(i.span);
            env.sink
                .diagnostics
                .borrow_mut()
                .push(rokc_diagnostic::RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "`impl {} for {}`: neither the trait nor the type is defined in this \
                         package (orphan rule, spec 2.9.5)",
                        leaf_name(&key),
                        impl_def_display(&i.self_ty)
                    ),
                ));
            continue;
        }
        if i.negative {
            continue;
        }
        let Some(info) = env.trait_info.get(&key) else {
            continue;
        };
        let mut ctx = LowerCtx::new(env, &no_subst, None);
        ctx.current_module.clone_from(&module);
        if !i.generics.params.is_empty() {
            check_generic_supers(&ctx, i, &module, &key, &info.supers);
            continue;
        }
        let target = ctx.resolve_ast_ty(&i.self_ty);
        if target == HirTy::Unknown {
            continue;
        }
        for sup in &info.supers {
            if ctx.has_trait(&target, sup) {
                continue;
            }
            rokc_diagnostic::set_current_span(i.span);
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`{}` implements `{}` but not its supertrait `{}` (spec 2.8.4)",
                    ctx.ty_name(&target),
                    leaf_name(&key),
                    leaf_name(sup)
                ),
            );
        }
    }
}

/// Spec 2.8.4 for a generic impl: its target, with the impl parameters
/// as opaque types bounded by their bounds, must implement each
/// supertrait (`impl<T: Show> Pretty for List<T>` needs `List<T>: Show`
/// from some impl whose bounds `T: Show` meets).
fn check_generic_supers(
    ctx: &LowerCtx<'_>,
    i: &rokc_ast::ImplDef,
    module: &str,
    key: &str,
    supers: &[String],
) {
    let vars: HashMap<String, String> = i
        .generics
        .params
        .iter()
        .map(|gp| match gp {
            rokc_ast::GenericParam::Type { name, .. }
            | rokc_ast::GenericParam::Const { name, .. } => (name.clone(), format!("#r.{name}")),
        })
        .collect();
    let Some(target) = canon_ast_ty(ctx, module, &vars, &i.self_ty) else {
        return;
    };
    let target = rigid(&target);
    let mut assume: HashMap<String, Vec<String>> = HashMap::new();
    let mut add = |subject: &Ty, bounds: &[Ty]| {
        let AstTyKind::Path(p) = &subject.kind else {
            return;
        };
        let [seg] = p.segments.as_slice() else {
            return;
        };
        let Some(v) = vars.get(&seg.name) else {
            return;
        };
        let have = assume.entry(v.clone()).or_default();
        for b in bounds {
            if let AstTyKind::Path(bp) = &b.kind {
                let segs: Vec<&str> = bp.segments.iter().map(|s| s.name.as_str()).collect();
                have.push(ctx.env.names.trait_key(&segs, module));
            }
        }
    };
    for gp in &i.generics.params {
        if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
            add(&path_ty_named(name, i.span), bounds);
        }
    }
    for w in &i.where_clause {
        add(&w.ty, &w.bounds);
    }
    for sup in supers {
        if entails(ctx, &target, sup, &assume, 0) {
            continue;
        }
        rokc_diagnostic::set_current_span(i.span);
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "`{}` implements `{}` but not its supertrait `{}` for every `{}` the \
                 impl allows (spec 2.8.4)",
                target.to_string().replace("#r.", ""),
                leaf_name(key),
                leaf_name(sup),
                i.generics
                    .params
                    .iter()
                    .map(|gp| match gp {
                        rokc_ast::GenericParam::Type { name, .. }
                        | rokc_ast::GenericParam::Const { name, .. } => name.as_str(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        );
    }
}

/// Impl parameters as opaque named types (`#r.T`), so unification with
/// another impl's target can bind its variables to them but not them.
fn rigid(t: &CanonTy) -> CanonTy {
    match t {
        CanonTy::Var(v) => CanonTy::Named(v.clone(), Vec::new()),
        CanonTy::Named(n, a) => CanonTy::Named(n.clone(), a.iter().map(rigid).collect()),
        CanonTy::Tuple(a) => CanonTy::Tuple(a.iter().map(rigid).collect()),
        CanonTy::Sum(a) => CanonTy::Sum(a.iter().map(rigid).collect()),
        CanonTy::Array(e, n) => CanonTy::Array(Box::new(rigid(e)), Box::new(rigid(n))),
    }
}

fn has_rigid(t: &CanonTy) -> bool {
    match t {
        CanonTy::Var(_) => false,
        CanonTy::Named(n, a) => n.starts_with("#r.") || a.iter().any(has_rigid),
        CanonTy::Tuple(a) | CanonTy::Sum(a) => a.iter().any(has_rigid),
        CanonTy::Array(e, n) => has_rigid(e) || has_rigid(n),
    }
}

/// Does `subject` implement trait `key` whatever the opaque `#r.T`s in
/// it are, given their bounds `assume`? An opaque type has its bounds
/// and their supertraits; anything else needs an impl whose target
/// unifies and whose bounds hold in turn. Structural rules (auto
/// traits, sums) and types this can't read are taken as met.
fn entails(
    ctx: &LowerCtx<'_>,
    subject: &CanonTy,
    key: &str,
    assume: &HashMap<String, Vec<String>>,
    depth: u32,
) -> bool {
    if depth > 8
        || key == super::reflect::REFLECT
        || ctx.env.names.auto_traits.contains(key)
        || !has_rigid(subject)
    {
        return true;
    }
    if let CanonTy::Named(n, args) = subject {
        if args.is_empty() && n.starts_with("#r.") {
            let mut stack: Vec<String> = assume.get(n).cloned().unwrap_or_default();
            let mut seen: Vec<String> = Vec::new();
            while let Some(h) = stack.pop() {
                if h == key {
                    return true;
                }
                if let (false, Some(info)) = (seen.contains(&h), ctx.env.trait_info.get(&h)) {
                    stack.extend(info.supers.iter().cloned());
                }
                seen.push(h);
            }
            return false;
        }
    }
    if matches!(subject, CanonTy::Sum(_)) {
        return true;
    }
    ctx.env
        .impls
        .generic()
        .filter(|gi| gi.trait_key == key)
        .any(|gi| {
            let vars: HashMap<String, String> = gi
                .generics
                .params
                .iter()
                .map(|gp| match gp {
                    rokc_ast::GenericParam::Type { name, .. }
                    | rokc_ast::GenericParam::Const { name, .. } => {
                        (name.clone(), format!("#c.{name}"))
                    }
                })
                .collect();
            let Some(target) = canon_ast_ty(ctx, &gi.module, &vars, &gi.self_ty) else {
                return true;
            };
            let mut u = Unifier::default();
            if u.unify(&target, subject).is_none() {
                return false;
            }
            let mut goals: Vec<(CanonTy, &Vec<Ty>)> = Vec::new();
            for gp in &gi.generics.params {
                if let rokc_ast::GenericParam::Type { name, bounds, .. } = gp {
                    goals.push((u.resolve(&vars[name]), bounds));
                }
            }
            for w in &gi.where_clause {
                match canon_ast_ty(ctx, &gi.module, &vars, &w.ty) {
                    Some(t) => goals.push((u.walk(&t), &w.bounds)),
                    None => return true,
                }
            }
            goals.iter().all(|(t, bounds)| {
                bounds.iter().all(|b| {
                    let AstTyKind::Path(bp) = &b.kind else {
                        return true;
                    };
                    let segs: Vec<&str> = bp.segments.iter().map(|s| s.name.as_str()).collect();
                    let k = ctx.env.names.trait_key(&segs, &gi.module);
                    entails(ctx, t, &k, assume, depth + 1)
                })
            })
        })
}

/// The package defining an impl's target type: a struct / enum's own,
/// `rok::core` for a built-in type, `None` for a bare type parameter.
fn target_package(env: &Env<'_>, i: &rokc_ast::ImplDef, module: &str) -> Option<String> {
    if let AstTyKind::Path(p) = &i.self_ty.kind {
        let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
        let param = i.generics.params.iter().any(
            |gp| matches!(gp, rokc_ast::GenericParam::Type { name, .. } if segs == [name.as_str()]),
        );
        if param {
            return None;
        }
        if let Some(full) = env.names.canon(&segs, module, &[]) {
            return Some(package_of(&module_of(&full)));
        }
    }
    Some("rok::core".to_owned())
}

fn check_impl_overlap(env: &Env<'_>) {
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None);
    for gi in env.impls.generic() {
        for ty in env.impls.tys_of(&gi.trait_key) {
            if ctx
                .generic_impl_subst(gi, ty, 0)
                .is_some_and(|s| trait_args_overlap(&ctx, gi, &s, ty))
            {
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
    let gis: Vec<&Impl> = env.impls.generic().collect();
    let mut candidates: Option<Vec<HirTy>> = None;
    for (i, a) in gis.iter().enumerate() {
        // Inherent ones (empty key) clash when they share a method name.
        let shared = |b: &Impl| {
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

/// Whether generic impl `gi`, matched on concrete target `ty` with
/// `subst`, also matches a concrete impl's trait arguments:
/// `impl<T> DotMul<List<T>> for T` and `impl DotMul<M> for M` are
/// disjoint. A parameter only the trait arguments name is open: assume
/// overlap.
fn trait_args_overlap(
    ctx: &LowerCtx<'_>,
    gi: &Impl,
    subst: &HashMap<String, HirTy>,
    ty: &HirTy,
) -> bool {
    let open = gi.generics.params.iter().any(|gp| match gp {
        rokc_ast::GenericParam::Type { name, .. } | rokc_ast::GenericParam::Const { name, .. } => {
            !subst.contains_key(name)
        }
    });
    if gi.trait_args.is_empty() || open {
        return true;
    }
    let want = ctx.generic_impl_ref(gi, subst);
    if want.args.contains(&HirTy::Unknown) {
        return true;
    }
    ctx.concrete_impls(ty)
        .any(|r| r.path == want.path && r.args == want.args)
}

/// Concrete impl targets and generic struct / enum instantiations: the
/// witnesses for impl targets `symbolic_overlap` can't read.
fn named_types(env: &Env<'_>) -> Vec<HirTy> {
    let mut out: Vec<HirTy> = Vec::new();
    let named = env.impls.all.iter().filter_map(|i| match &i.concrete {
        Some((t, Some(_))) => Some(t.clone()),
        _ => None,
    });
    let structs: Vec<HirTy> = env
        .defs
        .structs
        .borrow()
        .iter()
        .filter(|s| !s.generic_args.is_empty())
        .map(|s| HirTy::Struct(s.id))
        .collect();
    let enums: Vec<HirTy> = env
        .defs
        .enums
        .borrow()
        .iter()
        .filter(|e| !e.generic_args.is_empty())
        .map(|e| HirTy::Enum(e.id))
        .collect();
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
fn symbolic_overlap(ctx: &LowerCtx<'_>, a: &Impl, b: &Impl) -> Option<Option<String>> {
    let names = |gi: &Impl, tag: &str| -> HashMap<String, String> {
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
    let canon =
        |gi: &Impl, vars: &HashMap<String, String>, t: &Ty| canon_ast_ty(ctx, &gi.module, vars, t);
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
        return ctx.has_trait(&t, key);
    }
    let head = canon_head(subject);
    let env = ctx.env;
    let concrete = env.impls.tys_of(key).any(|t| {
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
            .impls
            .generic()
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
        AstTyKind::Nest(x) => rec(x)?,
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
            // No cyclic binding (`T` against `List<T>`): no overlap.
            (CanonTy::Var(v), t) | (t, CanonTy::Var(v)) => {
                if occurs(&v, &t) {
                    return None;
                }
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

/// Does variable `v` occur in `t` (already walked)?
fn occurs(v: &str, t: &CanonTy) -> bool {
    match t {
        CanonTy::Var(w) => w == v,
        CanonTy::Named(_, ts) | CanonTy::Tuple(ts) | CanonTy::Sum(ts) => {
            ts.iter().any(|t| occurs(v, t))
        }
        CanonTy::Array(e, n) => occurs(v, e) || occurs(v, n),
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

/// What a `#[intrinsic("rok.NAME")]` function is (stdlib spec 0.3): its
/// calls become the operation; the body is only a fallback.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    /// `rok.OP.TYPE` on a primitive's method.
    Prim(PrimOp),
    BufNew,
    BufGet,
    BufSet,
    BufSame,
    BufErase,
    PtrRead {
        volatile: bool,
    },
    PtrWrite {
        volatile: bool,
    },
    SizeOf,
    AlignOf,
    /// `rok.addr_of`: a pointer (the declared return type's) to the
    /// argument's place, or to a `ref self` receiver's.
    AddrOf,
    /// `rok.drop_in_place`: run the drop glue of the `T` a `Ptr<T>`
    /// points at.
    DropInPlace,
    /// `rok.atomic.OP`: the op `HirExprKind::BufAtomic` carries.
    Atomic(&'static str),
    AnyCast,
    MethodTable,
    MlirOp,
    MlirAttr,
}

impl Intrinsic {
    fn parse(name: &str) -> Option<Self> {
        let rest = name.strip_prefix("rok.")?;
        Some(match rest {
            "buf.new" => Self::BufNew,
            "buf.get" => Self::BufGet,
            "buf.set" => Self::BufSet,
            "buf.same" => Self::BufSame,
            "buf.erase" => Self::BufErase,
            "ptr.read" => Self::PtrRead { volatile: false },
            "ptr.write" => Self::PtrWrite { volatile: false },
            "ptr.read_volatile" => Self::PtrRead { volatile: true },
            "ptr.write_volatile" => Self::PtrWrite { volatile: true },
            "size_of" => Self::SizeOf,
            "align_of" => Self::AlignOf,
            "addr_of" => Self::AddrOf,
            "drop_in_place" => Self::DropInPlace,
            "any_cast" => Self::AnyCast,
            "method_table" => Self::MethodTable,
            "mlir.op" => Self::MlirOp,
            "mlir.attr" => Self::MlirAttr,
            _ => {
                if let Some(op) = rest.strip_prefix("atomic.") {
                    return ["load", "xchg", "add", "sub", "and", "or", "xor", "cas"]
                        .into_iter()
                        .find(|o| *o == op)
                        .map(Self::Atomic);
                }
                // `rok.OP_assign.TYPE` (stdlib 2.4.6): the op, written
                // back through the `ref self` receiver.
                let op = rest.split('.').next()?;
                Self::Prim(match op.strip_suffix("_assign").unwrap_or(op) {
                    "add" => PrimOp::Add,
                    "sub" => PrimOp::Sub,
                    "mul" => PrimOp::Mul,
                    "div" => PrimOp::Div,
                    "rem" => PrimOp::Rem,
                    "and" => PrimOp::BitAnd,
                    "or" => PrimOp::BitOr,
                    "xor" => PrimOp::BitXor,
                    "shl" => PrimOp::Shl,
                    "shr" => PrimOp::Shr,
                    "eq" => PrimOp::Eq,
                    "ne" => PrimOp::Ne,
                    "lt" => PrimOp::Lt,
                    "le" => PrimOp::Le,
                    "gt" => PrimOp::Gt,
                    "ge" => PrimOp::Ge,
                    "neg" => PrimOp::Neg,
                    // Bitwise on integers, logical on `bool` (picked at the call).
                    "not" => PrimOp::Not,
                    "sqrt" => PrimOp::Sqrt,
                    "wrapping_add" => PrimOp::WrappingAdd,
                    "wrapping_sub" => PrimOp::WrappingSub,
                    "wrapping_mul" => PrimOp::WrappingMul,
                    "ctpop" => PrimOp::CountOnes,
                    "ctlz" => PrimOp::LeadingZeros,
                    "cttz" => PrimOp::TrailingZeros,
                    "bswap" => PrimOp::SwapBytes,
                    _ => return None,
                })
            }
        })
    }
}

/// The `#[intrinsic(..)]` of `m`, declared in `module`: standard library
/// only (stdlib spec 0.3.5); a primitive op's operands are the
/// parameters.
pub(super) fn intrinsic_of(
    m: &FnDef,
    module: &str,
    diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> Option<Intrinsic> {
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
    let Some(intrinsic) = name.as_deref().and_then(Intrinsic::parse) else {
        return err(format!(
            "`#[intrinsic({})]` on `{}`: unknown intrinsic — expected `rok.OP.TYPE` \
             (stdlib spec 0.3.3)",
            name.map_or_else(String::new, |n| format!("\"{n}\"")),
            m.name
        ));
    };
    // A primitive op is a concrete method; the others take their types
    // from a generic function's arguments.
    let Intrinsic::Prim(op) = intrinsic else {
        if m.generics.params.is_empty() {
            return err(format!(
                "`#[intrinsic]` on `{}`: this intrinsic is a generic function",
                m.name
            ));
        }
        return Some(intrinsic);
    };
    if !m.generics.params.is_empty() {
        return err(format!(
            "`#[intrinsic]` on `{}`: a primitive op is not generic",
            m.name
        ));
    }
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
    let assign = name
        .as_deref()
        .is_some_and(|n| n.split('.').nth(1).is_some_and(|o| o.ends_with("_assign")));
    if assign != (arity == 2 && m.params[0].by_ref) {
        return err(format!(
            "`#[intrinsic]` on `{}`: a `rok.OP_assign.TYPE` op takes `ref self`, and only it",
            m.name
        ));
    }
    Some(intrinsic)
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
fn const_arg_value(t: &Ty, names: &TypeNames<'_>, module: &str) -> Option<i128> {
    let c = match &t.kind {
        AstTyKind::Const(c) => c.clone(),
        AstTyKind::Path(p) => rokc_ast::ConstExpr::Path(p.clone()),
        _ => return None,
    };
    names.const_int(&c, module)
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

/// `Self::X` in a default method's signature where `X` is not the
/// trait's own (a supertrait's: `Self::Item` in `DoubleEndedIterator`)
/// becomes the projection on the impl's target (`ListIter<T>::Item`).
fn supertrait_projections(
    m: &FnDef,
    t: &rokc_ast::TraitDef,
    impl_def: &rokc_ast::ImplDef,
    args: &mut HashMap<String, Ty>,
) {
    let AstTyKind::Path(target) = &impl_def.self_ty.kind else {
        return;
    };
    let mut needs = Vec::new();
    let tys = m.params.iter().filter_map(|p| p.ty.as_ref());
    for ty in tys.chain(m.ret_ty.as_ref()) {
        ast_ty_needs(ty, &[], &[], &mut needs);
    }
    let own = trait_assoc_names(t);
    for x in needs.iter().filter_map(|n| n.strip_prefix("Self::")) {
        if args.contains_key(x) || own.iter().any(|o| o == x) {
            continue;
        }
        let mut p = target.clone();
        p.segments.push(rokc_ast::PathSegment {
            name: x.to_owned(),
            generics: Vec::new(),
        });
        let ty = Ty {
            kind: AstTyKind::Path(p),
            span: impl_def.self_ty.span,
        };
        args.insert(x.to_owned(), ty);
    }
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
fn add_self_assoc_sigs(program: &mut Program) {
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
    for it in &mut program.items {
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
}

/// Associated type defaults (`trait TryFrom<U> { type Error =
/// ConversionError; }`): an impl that omits `type X` gets the trait's
/// default, its names resolved in the trait's module and the trait's
/// parameters replaced by the impl's arguments. Everything after sees
/// an ordinary `type X = ..;` in the impl. The additions, by item index.
fn assoc_defaults(program: &Program, names: &TypeNames<'_>) -> Vec<(usize, Vec<AstImplItem>)> {
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
    let mut out = Vec::new();
    if traits.is_empty() {
        return out;
    }
    for (idx, it) in program.items.iter().enumerate() {
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
        if !added.is_empty() {
            out.push((idx, added));
        }
    }
    out
}

/// The bodies without `-> T` that may diverge on every path (spec
/// 4.3.7), so their return type is inferred (`!` when lowering confirms
/// it): each ends in `throw`, a `loop`, a call of a function named like
/// one declared `-> !` or itself in this set, or a control structure
/// whose every branch does. Names are matched by leaf (an
/// over-approximation the lowering settles); a fixed point over the
/// program keeps inference from nesting through every unit call chain.
fn may_diverge(program: &Program) -> std::collections::HashSet<rokc_diagnostic::Span> {
    use std::collections::HashSet;
    fn tail_block(b: &Block, d: &HashSet<String>) -> bool {
        if let Some(t) = &b.trailing {
            return tail(t, d);
        }
        b.stmts.last().is_some_and(|s| match &s.kind {
            StmtKind::Throw(_) => true,
            StmtKind::Expr(e) => tail(e, d),
            _ => false,
        })
    }
    // A `loop` with no `break` / `return` in it (outside closures).
    fn endless(body: &Block) -> bool {
        struct V {
            depth: u32,
            exits: bool,
        }
        impl crate::walk::AstVisitor for V {
            fn stmt(&mut self, s: &rokc_ast::Stmt) {
                if self.depth == 0 && matches!(s.kind, StmtKind::Break { .. } | StmtKind::Return(_))
                {
                    self.exits = true;
                }
            }
            fn enter_body(&mut self) {
                self.depth += 1;
            }
            fn leave_body(&mut self) {
                self.depth -= 1;
            }
        }
        let mut v = V {
            depth: 0,
            exits: false,
        };
        crate::walk::walk_block(&mut v, body);
        !v.exits
    }
    fn tail(e: &Expr, d: &HashSet<String>) -> bool {
        match &e.kind {
            ExprKind::Loop { body, .. } => endless(body),
            ExprKind::Call { callee, .. } => match &callee.kind {
                ExprKind::Path(p) => p.segments.last().is_some_and(|s| d.contains(&s.name)),
                ExprKind::QPath(q) => d.contains(&q.item),
                _ => false,
            },
            ExprKind::MethodCall { method, .. } => d.contains(method),
            ExprKind::Try { operand, .. } => tail(operand, d),
            ExprKind::Block(b) | ExprKind::Unsafe(b) => tail_block(b, d),
            ExprKind::If {
                then_branch,
                else_branch: Some(eb),
                ..
            } => tail_block(then_branch, d) && tail(eb, d),
            ExprKind::Match { arms, .. } => {
                !arms.is_empty() && arms.iter().all(|a| tail(&a.body, d))
            }
            _ => false,
        }
    }
    let mut fns: Vec<&FnDef> = Vec::new();
    for it in &program.items {
        match it {
            Item::Fn(f) => fns.push(f),
            Item::Impl(i) => fns.extend(i.items.iter().filter_map(|m| match m {
                AstImplItem::Method(f) => Some(f),
                _ => None,
            })),
            Item::Trait(t) => fns.extend(t.items.iter().filter_map(|m| match m {
                rokc_ast::TraitItem::Method(f) => Some(f),
                _ => None,
            })),
            _ => {}
        }
    }
    let mut names: HashSet<String> = fns
        .iter()
        .filter(|f| {
            f.ret_ty
                .as_ref()
                .is_some_and(|t| matches!(t.kind, AstTyKind::Never))
        })
        .map(|f| leaf_name(&f.name).to_owned())
        .collect();
    let open: Vec<&FnDef> = fns
        .into_iter()
        .filter(|f| f.ret_ty.is_none() && f.body.is_some())
        .collect();
    let mut out = HashSet::new();
    loop {
        let before = out.len();
        for f in &open {
            if !out.contains(&f.span) && f.body.as_ref().is_some_and(|b| tail_block(b, &names)) {
                out.insert(f.span);
                names.insert(leaf_name(&f.name).to_owned());
            }
        }
        if out.len() == before {
            return out;
        }
    }
}

/// A trait impl method's untyped parameter takes the type the trait
/// declares at its position (trait parameters replaced by the impl's
/// arguments), not an implicit type parameter: the method implements
/// that signature.
fn impl_param_types(program: &mut Program, names: &TypeNames<'_>) {
    let traits: HashMap<&str, &rokc_ast::TraitDef> = program
        .items
        .iter()
        .filter_map(|it| match it {
            Item::Trait(t) => Some((t.name.as_str(), t)),
            _ => None,
        })
        .collect();
    let untyped = |p: &Param| p.ty.is_none() && p.name != "self" && !p.variadic;
    let mut fills: Vec<(usize, usize, usize, Ty)> = Vec::new();
    for (ii, it) in program.items.iter().enumerate() {
        let Item::Impl(i) = it else { continue };
        let Some(tp) = &i.trait_path else { continue };
        let has_untyped =
            |m: &AstImplItem| matches!(m, AstImplItem::Method(d) if d.params.iter().any(untyped));
        if !i.items.iter().any(has_untyped) {
            continue;
        }
        let module = impl_module(i);
        let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
        let Some(td) = traits.get(names.trait_key(&segs, &module).as_str()) else {
            continue;
        };
        let params = trait_param_args(td, i);
        for (mi, m) in i.items.iter().enumerate() {
            let AstImplItem::Method(d) = m else { continue };
            let decl = td.items.iter().find_map(|ti| match ti {
                rokc_ast::TraitItem::Method(t) if leaf_name(&t.name) == leaf_name(&d.name) => {
                    Some(t)
                }
                _ => None,
            });
            let Some(decl) = decl else { continue };
            let mut own = params.clone();
            for gp in &decl.generics.params {
                let (rokc_ast::GenericParam::Type { name, .. }
                | rokc_ast::GenericParam::Const { name, .. }) = gp;
                own.entry(name.clone())
                    .or_insert_with(|| path_ty_named(name, decl.span));
            }
            for (pi, (p, tp)) in d.params.iter().zip(&decl.params).enumerate() {
                let (true, Some(t)) = (untyped(p), &tp.ty) else {
                    continue;
                };
                let mut ty = t.clone();
                names.absolutize(&mut ty, &module_of(&td.name), &module, &own);
                subst_assoc_ty(&mut ty, &params);
                fills.push((ii, mi, pi, ty));
            }
        }
    }
    for (ii, mi, pi, ty) in fills {
        if let Item::Impl(i) = &mut program.items[ii] {
            if let AstImplItem::Method(d) = &mut i.items[mi] {
                d.params[pi].ty = Some(ty);
            }
        }
    }
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
                // A `Nest` (`X?`) is already one member.
                let before = matches!(&t.kind, AstTyKind::Path(p) if p.segments.len() <= 2)
                    .then(|| format!("{:?}", t.kind));
                subst_assoc_ty(t, assoc);
                // A replaced parameter stays one member (spec 2.6.4).
                if before.is_some_and(|b| b != format!("{:?}", t.kind)) {
                    let span = t.span;
                    let inner = std::mem::replace(
                        t,
                        Ty {
                            kind: AstTyKind::Never,
                            span,
                        },
                    );
                    t.kind = AstTyKind::Nest(Box::new(inner));
                }
            }
        }
        AstTyKind::Nest(x) | AstTyKind::Binding(_, x) => subst_assoc_ty(x, assoc),
        AstTyKind::QPath(q) => {
            subst_assoc_ty(&mut q.self_ty, assoc);
            for s in &mut q.trait_path.segments {
                s.generics.iter_mut().for_each(|g| subst_assoc_ty(g, assoc));
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

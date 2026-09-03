//! AST → HIR lowering.

use std::collections::HashMap;

use rokc_ast::{
    Block, CallArg, EnumDef as AstEnumDef, EnumVariantKind as AstEnumVariantKind, Expr, ExprKind,
    FnDef, ImplItem as AstImplItem, Item, Literal as AstLit,
    MatchArm as AstMatchArm, Param, Path as AstPath, Pattern as AstPattern,
    PatternKind as AstPatternKind, Program, Stmt, StmtKind, StructDef as AstStructDef,
    StructKind as AstStructKind, Ty, TyKind as AstTyKind,
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

/// Strip the leaf segment from a `module::path::name` string and
/// return the module path joined back with `::`. Returns an empty
/// string for free functions in the package root.
fn module_of(name: &str) -> String {
    match name.rsplit_once("::") {
        Some((mod_path, _)) => mod_path.to_owned(),
        None => String::new(),
    }
}

/// Best-effort const-folding of a static initializer. Accepts integer
/// and bool literals (with optional unary minus) plus string literals.
/// Returns `None` for non-literal initializers — caller falls back to
/// `ConstVal::Unit` and the codegen emits a zero-init global.
fn literal_to_const_val(expr: &Expr, ty: &HirTy) -> Option<ConstVal> {
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
                    return Some(ConstVal::Int { value: -n, ty: prim });
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
        L::Str(s) => Some(ConstVal::Str(s.clone())),
        L::RawStr(s) => Some(ConstVal::Str(s.clone())),
        L::None => Some(ConstVal::None),
        _ => None,
    }
}

fn strip_int_suffix(s: &str) -> &str {
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

fn lookup_in_use_entries_full(
    entries: &[crate::uses::UseEntry],
    segments: &[&str],
    suffix: &str,
    fn_table: &HashMap<String, FnSig>,
) -> LookupOutcome {
    let mut glob_hits: Vec<String> = Vec::new();
    for entry in entries {
        match entry {
            crate::uses::UseEntry::Single { local, full } => {
                if segments.len() == 1 && segments[0] == local && fn_table.contains_key(full) {
                    return LookupOutcome::Resolved(full.clone());
                }
                // `use foo::bar` lets `bar::baz` resolve as `foo::bar::baz`.
                if !segments.is_empty() && segments[0] == local {
                    let mut joined = full.clone();
                    for s in &segments[1..] {
                        joined.push_str("::");
                        joined.push_str(s);
                    }
                    if fn_table.contains_key(&joined) {
                        return LookupOutcome::Resolved(joined);
                    }
                }
            }
            crate::uses::UseEntry::Glob { prefix } => {
                let candidate = if prefix.is_empty() {
                    suffix.to_owned()
                } else {
                    format!("{prefix}::{suffix}")
                };
                if fn_table.contains_key(&candidate) && !glob_hits.contains(&candidate) {
                    glob_hits.push(candidate);
                }
            }
            crate::uses::UseEntry::GlobDeep { prefix } => {
                let direct = if prefix.is_empty() {
                    suffix.to_owned()
                } else {
                    format!("{prefix}::{suffix}")
                };
                if fn_table.contains_key(&direct) && !glob_hits.contains(&direct) {
                    glob_hits.push(direct);
                    continue;
                }
                let prefix_with_sep = if prefix.is_empty() {
                    String::new()
                } else {
                    format!("{prefix}::")
                };
                let suffix_with_sep = format!("::{suffix}");
                for key in fn_table.keys() {
                    if key.starts_with(&prefix_with_sep)
                        && key.ends_with(&suffix_with_sep)
                        && !glob_hits.contains(key)
                    {
                        glob_hits.push(key.clone());
                    }
                }
            }
        }
    }
    match glob_hits.len() {
        0 => LookupOutcome::None,
        1 => LookupOutcome::Resolved(glob_hits.remove(0)),
        _ => LookupOutcome::Ambiguous(glob_hits),
    }
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

#[must_use]
pub fn lower_full(
    program: &Program,
    prec: &PrecTable,
    uses: &crate::uses::UseTable,
    reexports: &[crate::uses::ReExport],
) -> HirModule {
    // Diagnostics emitted during pre-body passes (impl-target validation
    // etc.) — folded into module.diagnostics once the module exists.
    let mut pre_diags: Vec<rokc_diagnostic::RokDiagnostic> = Vec::new();
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
                pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Type,
                    "`#[derive(...)]` expansion is not yet implemented; \
                     write the trait impl by hand for now (spec 6.2)"
                        .to_owned(),
                ));
            }
        }
    }
    // Pass 1a: enums. Generic enums get stashed for lazy instantiation.
    let mut enum_table: HashMap<String, EnumId> = HashMap::new();
    let mut enum_decls: Vec<&AstEnumDef> = Vec::new();
    let mut generic_enums: HashMap<String, &AstEnumDef> = HashMap::new();
    for item in &program.items {
        if let Item::Enum(e) = item {
            if !e.generics.params.is_empty() {
                generic_enums.insert(e.name.clone(), e);
                continue;
            }
            let id = EnumId(u32::try_from(enum_decls.len()).expect("EnumId overflow"));
            enum_table.insert(e.name.clone(), id);
            enum_decls.push(e);
        }
    }
    // Pass 1b: structs (need names known so enum payload types can
    // refer to structs). Generic structs are stashed aside and
    // instantiated later as type uses surface them.
    let mut struct_table: HashMap<String, StructId> = HashMap::new();
    let mut generic_structs: HashMap<String, &AstStructDef> = HashMap::new();
    for item in &program.items {
        if let Item::Struct(s) = item {
            if !s.generics.params.is_empty() {
                generic_structs.insert(s.name.clone(), s);
                continue;
            }
            let id = StructId(u32::try_from(struct_table.len()).expect("StructId overflow"));
            struct_table.insert(s.name.clone(), id);
        }
    }

    let mut enum_defs: Vec<HirEnumDef> = Vec::with_capacity(enum_decls.len());
    for (i, e) in enum_decls.iter().enumerate() {
        let id = EnumId(u32::try_from(i).expect("EnumId overflow"));
        enum_defs.push(lower_enum_def(e, id, &struct_table, &enum_table));
    }

    // Now lower struct field types using both tables.
    let mut struct_decls: Vec<&AstStructDef> = Vec::new();
    for item in &program.items {
        if let Item::Struct(s) = item {
            if s.generics.params.is_empty() {
                struct_decls.push(s);
            }
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
            union_decls.push(u);
        }
    }
    let total_decls = struct_decls.len() + union_decls.len();
    for u in &union_decls {
        let id = StructId(
            u32::try_from(struct_table.len()).expect("StructId overflow"),
        );
        struct_table.insert(u.name.clone(), id);
    }
    let mut struct_defs: Vec<HirStructDef> = Vec::with_capacity(total_decls);
    for (i, s) in struct_decls.iter().enumerate() {
        let id = StructId(u32::try_from(i).expect("StructId overflow"));
        struct_defs.push(lower_struct_def(s, id, &struct_table, &enum_table));
    }
    for (i, u) in union_decls.iter().enumerate() {
        let id = StructId(
            u32::try_from(struct_decls.len() + i).expect("StructId overflow"),
        );
        struct_defs.push(lower_union_def(u, id, &struct_table, &enum_table, &mut pre_diags));
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
    );
    // Pass 1b.2: same idea for generic enums.
    instantiate_generic_enums(
        program,
        &generic_enums,
        &mut struct_table,
        &mut struct_defs,
        &mut enum_table,
        &mut enum_defs,
    );

    // Pass 2: collect every function-like declaration. Free functions
    // first, then `impl` methods (each method becomes a synthetic free
    // function `Type::method` with `self` as its first parameter).
    let mut fn_table: HashMap<String, FnSig> = HashMap::new();
    let mut method_table: HashMap<(MethodTarget, String), FunctionId> = HashMap::new();
    // Records `(Type, TraitName)` for each `impl Trait for Type` block
    // — feeds the generic-bound check at monomorphization time.
    let mut impl_traits: std::collections::HashSet<(MethodTarget, String)> =
        std::collections::HashSet::new();
    let mut decls: Vec<MethodOrFn<'_>> = Vec::new();
    // Pass 1c: collect module-level `const` items. Their value
    // expressions are stored as AST and inlined at each use site.
    // `static` items follow a different path — they get stable global
    // storage (`HirStaticDef`) and reads/writes go through addressof
    // + load/store at codegen time.
    let mut consts: HashMap<String, Expr> = HashMap::new();
    for item in &program.items {
        if let Item::Const(c) = item {
            consts.insert(c.name.clone(), c.value.clone());
        }
    }
    let mut static_defs: Vec<HirStaticDef> = Vec::new();
    let mut static_tys: HashMap<String, HirTy> = HashMap::new();
    for item in &program.items {
        if let Item::Static(s) = item {
            let ty = resolve_ty_with_structs(&s.ty, &struct_table, &enum_table);
            let init = s
                .value
                .as_ref()
                .and_then(|v| literal_to_const_val(v, &ty))
                .unwrap_or(ConstVal::Unit);
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
            let resolved = resolve_ty_with_structs(&a.ty, &struct_table, &enum_table);
            type_aliases.insert(a.name.clone(), resolved);
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

    // Generic functions don't get a single concrete signature — they
    // monomorphize per-call. We stash the AST aside instead of putting
    // them in `decls` / `fn_table`.
    let mut generic_fns: HashMap<String, &FnDef> = HashMap::new();
    for item in &program.items {
        match item {
            Item::Fn(fn_def) => {
                if !fn_def.generics.params.is_empty() {
                    generic_fns.insert(fn_def.name.clone(), fn_def);
                    continue;
                }
                // Spec 4.1 / 변경점 833: `xs: ...T` variadic. Stage-1
                // call-site lowering doesn't yet wrap trailing args into
                // a Slice<T>, so any call would fail with arity mismatch
                // at codegen — emit an explicit refusal up front.
                if fn_def.params.iter().any(|p| p.variadic) {
                    pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "function `{}` has a `...T` variadic parameter; \
                             call-site slicing isn't implemented yet \
                             (spec 4.1 — stage-1 limitation)",
                            fn_def.name
                        ),
                    ));
                }
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let ret_ty = match &fn_def.ret_ty {
                    Some(t) => resolve_ty_with_structs(t, &struct_table, &enum_table),
                    None => HirTy::Unit,
                };
                let param_defaults: Vec<Option<Expr>> =
                    fn_def.params.iter().map(|p| p.default.clone()).collect();
                let param_tys: Vec<HirTy> = fn_def
                    .params
                    .iter()
                    .map(|p| match &p.ty {
                        Some(t) => resolve_ty_with_structs(t, &struct_table, &enum_table),
                        None => HirTy::Any,
                    })
                    .collect();
                let param_names: Vec<String> =
                    fn_def.params.iter().map(|p| p.name.clone()).collect();
                fn_table.insert(
                    fn_def.name.clone(),
                    FnSig {
                        id,
                        ret_ty,
                        param_defaults,
                        param_tys,
                        param_names,
                    },
                );
                decls.push(MethodOrFn::Fn(fn_def));
            }
            Item::Extern(blk) => {
                for ei in &blk.items {
                    let rokc_ast::ExternItem::Fn(fn_def) = ei else { continue };
                    let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                    let ret_ty = match &fn_def.ret_ty {
                        Some(t) => resolve_ty_with_structs(t, &struct_table, &enum_table),
                        None => HirTy::Unit,
                    };
                    let param_defaults: Vec<Option<Expr>> =
                        fn_def.params.iter().map(|p| p.default.clone()).collect();
                    let param_tys: Vec<HirTy> = fn_def
                        .params
                        .iter()
                        .map(|p| match &p.ty {
                            Some(t) => resolve_ty_with_structs(t, &struct_table, &enum_table),
                            None => HirTy::Any,
                        })
                        .collect();
                    let param_names: Vec<String> =
                        fn_def.params.iter().map(|p| p.name.clone()).collect();
                    fn_table.insert(
                        fn_def.name.clone(),
                        FnSig {
                            id,
                            ret_ty,
                            param_defaults,
                            param_tys,
                            param_names,
                        },
                    );
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
            trait_defs.insert(t.name.clone(), t);
        }
    }
    // Spec 2.x / i-want 538: trait names cannot stand in a type slot
    // (`let a: Number = 32` etc.) — closed `T1 | T2` sums or generic
    // `<T: Trait>` parameters take that role. Scan every type reference
    // in fn signatures, struct fields, enum payloads, impl targets,
    // const/static declarations, and reject trait-name usages early.
    {
        let trait_names: std::collections::HashSet<&str> =
            trait_defs.keys().map(String::as_str).collect();
        let trait_set_ref = &trait_names;
        let mut visit = |ty: &rokc_ast::Ty| {
            // Walk only the outermost segment of a `Path` — generic
            // bound positions (`<T: Trait>`) and impl-trait paths use
            // separate AST shapes (Generics / Impl.trait_path), so this
            // visitor never sees them.
            if let rokc_ast::TyKind::Path(p) = &ty.kind {
                if p.segments.len() == 1 {
                    let name = &p.segments[0].name;
                    if trait_set_ref.contains(name.as_str()) {
                        pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "trait `{name}` cannot be used as a type \
                                 directly — use a closed sum (`A | B`) or \
                                 a generic parameter (`<T: {name}>`) \
                                 instead (i-want-this 538)"
                            ),
                        ));
                    }
                }
            }
        };
        for item in &program.items {
            // `impl Trait for T { ... }` — `Trait` is intentionally a
            // trait reference, so skip the trait_path on impl items.
            if let Item::Impl(_) = item {
                continue;
            }
            walk_item_tys(item, &mut visit);
        }
    }

    for item in &program.items {
        if let Item::Impl(impl_def) = item {
            let target = impl_target_key(&impl_def.self_ty, &struct_table, &enum_table);
            let target_ty = resolve_ty_with_structs(&impl_def.self_ty, &struct_table, &enum_table);
            // Spec 2.9.1: any `type_expr` is a valid impl target. impl_target_key
            // now returns Some(Mangled(...)) for non-struct/enum types, so this
            // is always Some(_) unless the resolution itself fails — which would
            // surface as a separate type-resolution diagnostic upstream.
            // Record `Type implements Trait` for the bound checker.
            if let (Some(trait_path), Some(target_key)) = (&impl_def.trait_path, target.clone()) {
                if let Some(seg) = trait_path.segments.last() {
                    impl_traits.insert((target_key, seg.name.clone()));
                }
            }
            // Names of methods this impl block explicitly provides —
            // used below to avoid double-registering a default that's
            // overridden here.
            let mut explicit_methods: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            for ii in &impl_def.items {
                let AstImplItem::Method(m) = ii else { continue };
                explicit_methods.insert(m.name.clone());
                // Spec 2.9.2: `ref self` means the receiver mutates the
                // caller's binding. Pointer-typed receivers aren't yet
                // wired through codegen, so the body would silently
                // mutate a copy — reject explicitly to block the silent
                // miscompile until ref semantics land.
                if let Some(first) = m.params.first() {
                    if first.name == "self" && first.by_ref {
                        pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "method `{}` declares `ref self`, but ref-self \
                                 semantics aren't implemented yet — mutations \
                                 would silently target a copy (spec 2.9.2)",
                                m.name
                            ),
                        ));
                    }
                }
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let ret_ty = match &m.ret_ty {
                    Some(t) => resolve_ty_with_structs(t, &struct_table, &enum_table),
                    None => HirTy::Unit,
                };
                let param_defaults: Vec<Option<Expr>> =
                    m.params.iter().map(|p| p.default.clone()).collect();
                let param_tys: Vec<HirTy> = m
                    .params
                    .iter()
                    .map(|p| {
                        if p.name == "self" {
                            target_ty.clone()
                        } else {
                            match &p.ty {
                                Some(t) => resolve_ty_with_structs(t, &struct_table, &enum_table),
                                None => HirTy::Any,
                            }
                        }
                    })
                    .collect();
                let param_names: Vec<String> =
                    m.params.iter().map(|p| p.name.clone()).collect();
                fn_table.insert(
                    format!("{}__{}", ty_mangle(&target_ty), m.name),
                    FnSig {
                        id,
                        ret_ty,
                        param_defaults,
                        param_tys,
                        param_names,
                    },
                );
                if let Some(key) = target.clone() {
                    method_table.insert((key, m.name.clone()), id);
                }
                decls.push(MethodOrFn::Method {
                    fn_def: m,
                    self_ty: target_ty.clone(),
                });
            }

            // Pull in default-method bodies from the trait this impl
            // is for, when the impl doesn't override them. Each default
            // gets specialized for `Self = target_ty` by reusing the
            // method-lowering machinery.
            if let Some(trait_path) = &impl_def.trait_path {
                let trait_name = trait_path
                    .segments
                    .last()
                    .map(|s| s.name.as_str())
                    .unwrap_or("");
                if let Some(trait_def) = trait_defs.get(trait_name) {
                    for ti in &trait_def.items {
                        let rokc_ast::TraitItem::Method(tm) = ti else { continue };
                        // Only methods with a body are defaults; skip
                        // signature-only requirements (impl must
                        // provide them, and we already handled those
                        // above; if missing we don't synthesize).
                        if tm.body.is_none() {
                            continue;
                        }
                        if explicit_methods.contains(&tm.name) {
                            continue;
                        }
                        let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                        let ret_ty = match &tm.ret_ty {
                            Some(t) => resolve_ty_with_structs(t, &struct_table, &enum_table),
                            None => HirTy::Unit,
                        };
                        let param_defaults: Vec<Option<Expr>> =
                            tm.params.iter().map(|p| p.default.clone()).collect();
                        let param_tys: Vec<HirTy> = tm
                            .params
                            .iter()
                            .map(|p| {
                                if p.name == "self" {
                                    target_ty.clone()
                                } else {
                                    match &p.ty {
                                        Some(t) => resolve_ty_with_structs(t, &struct_table, &enum_table),
                                        None => HirTy::Any,
                                    }
                                }
                            })
                            .collect();
                        let param_names: Vec<String> =
                            tm.params.iter().map(|p| p.name.clone()).collect();
                        fn_table.insert(
                            format!("{}__{}", ty_mangle(&target_ty), tm.name),
                            FnSig {
                                id,
                                ret_ty,
                                param_defaults,
                                param_tys,
                                param_names,
                            },
                        );
                        if let Some(key) = target.clone() {
                            method_table.insert((key, tm.name.clone()), id);
                        }
                        decls.push(MethodOrFn::Method {
                            fn_def: tm,
                            self_ty: target_ty.clone(),
                        });
                    }
                }
            }
        }
    }

    // Install `pub use` re-exports as table aliases. A fixed-point loop
    // handles re-exports that name another re-export's short form. Spec
    // 5.8: re-exports affect every item kind, not just functions, so
    // alias the struct/enum/trait/static tables too — without this,
    // `pub use inner::Point;` left `Point` invisible at the use site and
    // `Point { x: 7 }` silently degenerated to a unit fall-through.
    for _ in 0..3 {
        for re in reexports {
            let alias_key = if re.module_path.is_empty() {
                re.short_name.clone()
            } else {
                format!("{}::{}", re.module_path, re.short_name)
            };
            if let Some(sig) = fn_table.get(&re.full_path).cloned() {
                fn_table.entry(alias_key.clone()).or_insert(sig);
            }
            if let Some(&id) = struct_table.get(&re.full_path) {
                struct_table.entry(alias_key.clone()).or_insert(id);
            }
            if let Some(&id) = enum_table.get(&re.full_path) {
                enum_table.entry(alias_key.clone()).or_insert(id);
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
        }
    }

    // Pass 3: function bodies.
    let mut module = HirModule {
        functions: Vec::with_capacity(decls.len()),
        structs: struct_defs,
        enums: enum_defs,
        statics: static_defs,
        diagnostics: pre_diags,
    };
    let sink = ClosureSink {
        extras: std::cell::RefCell::new(Vec::new()),
        next_id: std::cell::Cell::new(u32::try_from(decls.len()).expect("FunctionId overflow")),
        mono_cache: std::cell::RefCell::new(HashMap::new()),
        mono_sigs: std::cell::RefCell::new(HashMap::new()),
        diagnostics: std::cell::RefCell::new(Vec::new()),
    };
    // Build a name → Visibility map covering every registered function,
    // method, and trait/struct/enum item the path-resolution layer might
    // need to gate. Only free functions need it for now (methods dispatch
    // on type, not on visibility), but populating both keeps lookups
    // uniform.
    let mut item_visibility: HashMap<String, Visibility> = HashMap::new();
    for item in &program.items {
        match item {
            Item::Fn(f) => {
                item_visibility.insert(f.name.clone(), f.vis);
            }
            Item::Const(c) => {
                item_visibility.insert(c.name.clone(), c.vis);
            }
            Item::Static(s) => {
                item_visibility.insert(s.name.clone(), s.vis);
            }
            Item::Struct(s) => {
                item_visibility.insert(s.name.clone(), s.vis);
            }
            Item::Enum(e) => {
                item_visibility.insert(e.name.clone(), e.vis);
            }
            Item::TypeAlias(a) => {
                item_visibility.insert(a.name.clone(), a.vis);
            }
            Item::Trait(t) => {
                item_visibility.insert(t.name.clone(), t.vis);
            }
            _ => {}
        }
    }

    for (i, decl) in decls.iter().enumerate() {
        let id = FunctionId(u32::try_from(i).expect("FunctionId overflow"));
        let func = match decl {
            MethodOrFn::Fn(fn_def) => lower_fn(
                fn_def, id, None, &fn_table, &method_table, &module.structs, &module.enums,
                &struct_table, &enum_table, &consts, &type_aliases, &generic_fns, prec, &sink,
                &item_visibility, uses, &impl_traits, &static_tys,
            ),
            MethodOrFn::Method { fn_def, self_ty } => lower_fn(
                fn_def,
                id,
                Some(self_ty.clone()),
                &fn_table,
                &method_table,
                &module.structs,
                &module.enums,
                &struct_table,
                &enum_table,
                &consts,
                &type_aliases,
                &generic_fns,
                prec,
                &sink,
                &item_visibility,
                uses,
                &impl_traits,
                &static_tys,
            ),
        };
        module.functions.push(func);
    }
    // Append every closure body lifted to a top-level function during
    // expression lowering.
    for cl in sink.extras.into_inner() {
        module.functions.push(cl);
    }
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
    // Surface every diagnostic the lowering pass collected.
    module
        .diagnostics
        .extend(sink.diagnostics.into_inner());
    module
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum MethodTarget {
    Struct(StructId),
    Enum(EnumId),
    /// Mangled HirTy for impl targets that aren't a single struct or
    /// enum (Tuple/Array/Sum/Fn/Prim per spec 2.9.1 — type_expr is any
    /// type). Keyed by `ty_mangle` so two impls on the same shape land
    /// on the same target.
    Mangled(String),
}

/// Map a runtime `HirTy` to the `MethodTarget` used in `method_table`
/// keys. Mirrors `impl_target_key`'s strategy: direct mapping for
/// Struct/Enum, mangled fallback for everything else.
fn method_target_for(ty: &HirTy) -> Option<MethodTarget> {
    match ty {
        HirTy::Struct(id) => Some(MethodTarget::Struct(*id)),
        HirTy::Enum(id) => Some(MethodTarget::Enum(*id)),
        HirTy::Unknown => None,
        other => Some(MethodTarget::Mangled(ty_mangle(other))),
    }
}

enum MethodOrFn<'a> {
    Fn(&'a FnDef),
    Method { fn_def: &'a FnDef, self_ty: HirTy },
}

fn impl_target_key(
    ty: &rokc_ast::Ty,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
) -> Option<MethodTarget> {
    if let AstTyKind::Path(p) = &ty.kind {
        if p.segments.len() == 1 {
            let seg = &p.segments[0];
            // Generic-struct/enum impl target: build the mangled instantiation name.
            if !seg.generics.is_empty() {
                let arg_tys: Vec<HirTy> = seg
                    .generics
                    .iter()
                    .map(|t| resolve_ty_with_structs(t, structs, enums))
                    .collect();
                let mangled = format!(
                    "{}__{}",
                    seg.name,
                    arg_tys.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
                );
                if let Some(id) = structs.get(&mangled) {
                    return Some(MethodTarget::Struct(*id));
                }
                if let Some(id) = enums.get(&mangled) {
                    return Some(MethodTarget::Enum(*id));
                }
            }
            if let Some(id) = structs.get(&seg.name) {
                return Some(MethodTarget::Struct(*id));
            }
            if let Some(id) = enums.get(&seg.name) {
                return Some(MethodTarget::Enum(*id));
            }
        }
    }
    // Spec 2.9.1: any type_expr is a valid impl target. For non-path
    // types (Tuple/Array/Sum/Fn/Prim) we key the method table by the
    // type's mangled shape so two impls on the same shape land on the
    // same target.
    let resolved = resolve_ty_with_structs(ty, structs, enums);
    Some(MethodTarget::Mangled(ty_mangle(&resolved)))
}


fn lower_enum_def(
    e: &AstEnumDef,
    id: EnumId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
) -> HirEnumDef {
    let variants = e
        .variants
        .iter()
        .enumerate()
        .filter_map(|(i, v)| {
            let tag = u32::try_from(i).expect("variant index overflow");
            match &v.kind {
                AstEnumVariantKind::Unit => Some(HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: None,
                    named_fields: Vec::new(),
                }),
                // Single-element tuple — store the payload type directly.
                AstEnumVariantKind::Tuple(tys) if tys.len() == 1 => Some(HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(resolve_ty_with_structs(&tys[0], structs, enums)),
                    named_fields: Vec::new(),
                }),
                // Multi-element tuple — pack into a tuple payload type.
                AstEnumVariantKind::Tuple(tys) => Some(HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(HirTy::Tuple(
                        tys.iter()
                            .map(|t| resolve_ty_with_structs(t, structs, enums))
                            .collect(),
                    )),
                    named_fields: Vec::new(),
                }),
                // Named-form variant `Move { x: i32; y: i32; }` — pack
                // into a tuple payload by declaration order, recording
                // the field names so initialiser/pattern lowering can
                // map name → tuple index. Spec 2.4.
                AstEnumVariantKind::Named(fields) => Some(HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(HirTy::Tuple(
                        fields
                            .iter()
                            .map(|f| resolve_ty_with_structs(&f.ty, structs, enums))
                            .collect(),
                    )),
                    named_fields: fields.iter().map(|f| f.name.clone()).collect(),
                }),
                _ => None,
            }
        })
        .collect();
    HirEnumDef {
        id,
        def_id: None,
        name: e.name.clone(),
        variants,
        span: e.span,
    }
}

fn lower_struct_def(
    s: &AstStructDef,
    id: StructId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
) -> HirStructDef {
    let fields = match &s.kind {
        AstStructKind::Named(fs) => fs
            .iter()
            .map(|f| HirField {
                name: f.name.clone(),
                ty: resolve_ty_with_structs(&f.ty, structs, enums),
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
                ty: resolve_ty_with_structs(&f.ty, structs, enums),
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
fn lower_union_def(
    u: &rokc_ast::UnionDef,
    id: StructId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> HirStructDef {
    let aliases: Vec<(String, HirTy)> = u
        .fields
        .iter()
        .map(|f| (f.name.clone(), resolve_ty_with_structs(&f.ty, structs, enums)))
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
fn union_storage_strategy(
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
                    PrimTy::U8
                    | PrimTy::U16
                    | PrimTy::U32
                    | PrimTy::U64
                    | PrimTy::Usize => 3,
                    PrimTy::I8
                    | PrimTy::I16
                    | PrimTy::I32
                    | PrimTy::I64
                    | PrimTy::Isize
                    | PrimTy::CChar => 2,
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
    let padded = ((size + align - 1) / align) * align;
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
    UnionStorage::ByteArray { size: padded, align }
}

/// Best-effort byte size + alignment for a `HirTy`. Returns `None` for
/// types whose size depends on layout choices we haven't pinned yet
/// (closures with environment, generic struct without monomorphization).
fn ty_size_align_bytes(ty: &HirTy) -> Option<(u32, u32)> {
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
                let pad = ((total + al - 1) / al) * al;
                total = pad + sz;
            }
            let padded = ((total + align - 1) / align) * align;
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
        HirTy::Struct(_) | HirTy::Enum(_) => None,
        HirTy::Path(_) | HirTy::Unknown | HirTy::Any | HirTy::Unit => None,
        HirTy::Fn(_, _) | HirTy::Closure { .. } => None,
    }
}

/// Match an AST parameter type against a concrete `HirTy` (the call
/// argument's inferred type) to discover bindings for generic type
/// parameters. Walks structurally — `[T; N]` against `[i32; 4]` binds
/// `T → i32`, etc.
fn unify_param_ty(
    param_ty: &rokc_ast::Ty,
    arg_ty: &HirTy,
    generic_names: &std::collections::HashSet<String>,
    subst: &mut HashMap<String, HirTy>,
) {
    unify_param_ty_with(param_ty, arg_ty, generic_names, subst, None);
}

fn unify_param_ty_with(
    param_ty: &rokc_ast::Ty,
    arg_ty: &HirTy,
    generic_names: &std::collections::HashSet<String>,
    subst: &mut HashMap<String, HirTy>,
    structs: Option<&[HirStructDef]>,
) {
    match &param_ty.kind {
        rokc_ast::TyKind::Path(p) => {
            if p.segments.len() == 1 && generic_names.contains(&p.segments[0].name) {
                subst.insert(p.segments[0].name.clone(), arg_ty.clone());
                return;
            }
            // Generic struct param `Pair<T>` against arg `Pair__i32`:
            // recover T by reading the struct's recorded generic args.
            if !p.segments[0].generics.is_empty() {
                if let HirTy::Struct(sid) = arg_ty {
                    if let Some(structs) = structs {
                        if let Some(def) = structs.get(sid.0 as usize) {
                            for (param_arg, concrete) in
                                p.segments[0].generics.iter().zip(def.generic_args.iter())
                            {
                                unify_param_ty_with(
                                    param_arg,
                                    concrete,
                                    generic_names,
                                    subst,
                                    Some(structs),
                                );
                            }
                        }
                    }
                }
            }
        }
        rokc_ast::TyKind::Array(elem, _) => {
            if let HirTy::Array(arg_elem, _) = arg_ty {
                unify_param_ty_with(elem, arg_elem, generic_names, subst, structs);
            }
        }
        rokc_ast::TyKind::Tuple(parts) => {
            if let HirTy::Tuple(arg_parts) = arg_ty {
                for (p, a) in parts.iter().zip(arg_parts.iter()) {
                    unify_param_ty_with(p, a, generic_names, subst, structs);
                }
            }
        }
        rokc_ast::TyKind::Sum(parts) => {
            if let HirTy::Sum(arg_parts) = arg_ty {
                for (p, a) in parts.iter().zip(arg_parts.iter()) {
                    unify_param_ty_with(p, a, generic_names, subst, structs);
                }
            }
        }
        rokc_ast::TyKind::Fn(args, ret) => match arg_ty {
            HirTy::Fn(arg_args, arg_ret) | HirTy::Closure { args: arg_args, ret: arg_ret, .. } => {
                for (p, a) in args.iter().zip(arg_args.iter()) {
                    unify_param_ty_with(p, a, generic_names, subst, structs);
                }
                unify_param_ty_with(ret, arg_ret, generic_names, subst, structs);
            }
            _ => {}
        },
        _ => {}
    }
}

/// Look up or generate a specialized version of a generic function.
/// Returns `(specialized_fn_id, return_type)` on success. Type-parameter
/// substitution is inferred by zipping the call's lowered argument types
/// with the AST parameter type ascriptions.
fn monomorphize(
    ctx: &mut LowerCtx<'_>,
    fn_def: &FnDef,
    args: &[HirExpr],
    _span: rokc_diagnostic::Span,
) -> Option<(FunctionId, HirTy)> {
    // Infer concrete types for each generic param by unifying the AST
    // parameter type ascription against the call's arg type. Walks into
    // arrays, tuples, sums, function types, and closures.
    let generic_names: std::collections::HashSet<String> = fn_def
        .generics
        .params
        .iter()
        .filter_map(|gp| match gp {
            rokc_ast::GenericParam::Type { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let mut subst: HashMap<String, HirTy> = HashMap::new();
    for (param, arg) in fn_def.params.iter().zip(args.iter()) {
        let Some(t) = &param.ty else { continue };
        unify_param_ty_with(t, &arg.ty, &generic_names, &mut subst, Some(ctx.structs));
    }

    // Spec 2.10.5: if a generic param has a default and no concrete type
    // got inferred for it, apply the default. Order is one pass — defaults
    // can't depend on other defaults (would need iteration).
    for gp in &fn_def.generics.params {
        if let rokc_ast::GenericParam::Type { name, default: Some(d), .. } = gp {
            if !subst.contains_key(name) {
                let resolved = resolve_ty_with_structs(d, ctx.struct_table, ctx.enum_table);
                subst.insert(name.clone(), resolved);
            }
        }
    }

    // All generic params must be inferable. Otherwise this isn't a
    // monomorphizable call (and falls through to an error path).
    let mut subst_tys: Vec<HirTy> = Vec::new();
    for gp in &fn_def.generics.params {
        if let rokc_ast::GenericParam::Type { name, .. } = gp {
            subst_tys.push(subst.get(name).cloned()?);
        }
    }

    // Check generic-bound satisfaction: for each `T: Bound` declared on
    // the fn, verify that the inferred concrete type for `T` carries an
    // `impl Bound for T` block. Bound names that don't resolve to a
    // known trait (e.g. compound or qualified) get a pass — only direct
    // single-segment bounds are checked today.
    for gp in &fn_def.generics.params {
        let rokc_ast::GenericParam::Type { name, bounds, default: _ } = gp else {
            continue;
        };
        if bounds.is_empty() {
            continue;
        }
        let Some(concrete) = subst.get(name) else { continue };
        let Some(target) = method_target_for(concrete) else { continue };
        for bound in bounds {
            let rokc_ast::TyKind::Path(p) = &bound.kind else { continue };
            let Some(seg) = p.segments.last() else { continue };
            let bound_name = seg.name.clone();
            if !ctx.impl_traits.contains(&(target.clone(), bound_name.clone())) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "type does not satisfy trait bound `{bound_name}` required by `{}`",
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
    if let Some(&existing_id) = ctx.sink.mono_cache.borrow().get(&key) {
        let ret_ty = ctx
            .sink
            .mono_sigs
            .borrow()
            .get(&existing_id)
            .map(|s| s.ret_ty.clone())
            .unwrap_or(HirTy::Unknown);
        return Some((existing_id, ret_ty));
    }

    // Allocate a fresh id and lower the FnDef under the substitution.
    let new_id = FunctionId(ctx.sink.next_id.get());
    ctx.sink.next_id.set(new_id.0 + 1);
    // Pre-cache so a recursive call inside the body finds the in-progress mono.
    ctx.sink.mono_cache.borrow_mut().insert(key, new_id);
    // Pre-resolve the return type from AST + subst so a recursive
    // `sum_down(n - 1)` inside the body sees the correct result type.
    // Use the subst-aware resolver so generic-struct returns like
    // `KV<K, V>` look up the right mangled instantiation.
    let preview_ret_ty = match &fn_def.ret_ty {
        Some(t) => {
            let mut r = resolve_ast_with_subst(t, ctx.struct_table, ctx.enum_table, &subst);
            substitute_aliases(&mut r, ctx.type_aliases);
            r
        }
        None => HirTy::Unit,
    };
    ctx.sink.mono_sigs.borrow_mut().insert(
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
        subst_tys.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
    );

    let mono_fn = lower_fn_with_subst(
        fn_def,
        new_id,
        mangled_name,
        &subst,
        ctx.fn_table,
        ctx.method_table,
        ctx.structs,
        ctx.enums,
        ctx.struct_table,
        ctx.enum_table,
        ctx.consts,
        ctx.type_aliases,
        ctx.generic_fns,
        ctx.prec,
        ctx.sink,
        ctx.item_visibility,
        ctx.uses,
        ctx.impl_traits,
        ctx.statics,
    );

    let ret_ty = mono_fn.ret_ty.clone();
    let mono_param_tys: Vec<HirTy> =
        mono_fn.params.iter().map(|p| p.ty.clone()).collect();
    let mono_param_names: Vec<String> =
        mono_fn.params.iter().map(|p| p.name.clone()).collect();
    ctx.sink.mono_sigs.borrow_mut().insert(
        new_id,
        FnSig {
            id: new_id,
            ret_ty: ret_ty.clone(),
            param_defaults: Vec::new(),
            param_tys: mono_param_tys,
            param_names: mono_param_names,
        },
    );
    ctx.sink.extras.borrow_mut().push(mono_fn);
    Some((new_id, ret_ty))
}

/// `lower_fn` plus a per-call type-parameter substitution. Used for
/// monomorphization.
#[allow(clippy::too_many_arguments)]
fn lower_fn_with_subst(
    fn_def: &FnDef,
    id: FunctionId,
    mangled_name: String,
    subst: &HashMap<String, HirTy>,
    fns: &HashMap<String, FnSig>,
    methods: &HashMap<(MethodTarget, String), FunctionId>,
    structs: &[HirStructDef],
    enums: &[HirEnumDef],
    struct_table: &HashMap<String, StructId>,
    enum_table: &HashMap<String, EnumId>,
    consts: &HashMap<String, Expr>,
    type_aliases: &HashMap<String, HirTy>,
    generic_fns: &HashMap<String, &FnDef>,
    prec: &PrecTable,
    sink: &ClosureSink,
    item_visibility: &HashMap<String, Visibility>,
    uses: &crate::uses::UseTable,
    impl_traits: &std::collections::HashSet<(MethodTarget, String)>,
    statics: &HashMap<String, HirTy>,
) -> HirFunction {
    let mut ctx = LowerCtx::new(
        fns,
        methods,
        structs,
        enums,
        struct_table,
        enum_table,
        consts,
        type_aliases,
        subst,
        generic_fns,
        None,
        prec,
        sink,
        item_visibility,
        uses,
        impl_traits,
        statics,
    );
    ctx.current_module = module_of(&fn_def.name);

    let mut params = Vec::with_capacity(fn_def.params.len());
    for p in &fn_def.params {
        params.push(lower_param(&mut ctx, p));
    }

    let mut ret_ty = match &fn_def.ret_ty {
        Some(t) => resolve_ast_with_subst(t, struct_table, enum_table, subst),
        None => HirTy::Unit,
    };
    substitute_aliases(&mut ret_ty, type_aliases);
    ctx.fn_ret_ty = ret_ty.clone();

    let body = fn_def.body.as_ref().map(|b| lower_block(&mut ctx, b));

    HirFunction {
        id,
        def_id: None,
        name: mangled_name,
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
fn resolve_ast_with_subst(
    ty: &rokc_ast::Ty,
    struct_table: &HashMap<String, StructId>,
    enum_table: &HashMap<String, EnumId>,
    subst: &HashMap<String, HirTy>,
) -> HirTy {
    match &ty.kind {
        rokc_ast::TyKind::Path(p) => {
            // Bare type-param reference — resolve directly from subst.
            if p.segments.len() == 1
                && p.segments[0].generics.is_empty()
            {
                if let Some(replacement) = subst.get(&p.segments[0].name) {
                    return replacement.clone();
                }
            }
            // Generic-struct/enum path: resolve generic args under subst,
            // then look up the mangled instantiation.
            if p.segments.len() == 1 && !p.segments[0].generics.is_empty() {
                let resolved_args: Vec<HirTy> = p.segments[0]
                    .generics
                    .iter()
                    .map(|g| resolve_ast_with_subst(g, struct_table, enum_table, subst))
                    .collect();
                let mangled = format!(
                    "{}__{}",
                    p.segments[0].name,
                    resolved_args.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
                );
                if let Some(id) = struct_table.get(&mangled) {
                    return HirTy::Struct(*id);
                }
                if let Some(id) = enum_table.get(&mangled) {
                    return HirTy::Enum(*id);
                }
            }
            // Fall back to the regular resolver, then post-substitute
            // any leaked type-param paths.
            let mut t = resolve_ty_with_structs(ty, struct_table, enum_table);
            substitute_aliases(&mut t, subst);
            t
        }
        rokc_ast::TyKind::Sum(parts) => HirTy::Sum(
            parts
                .iter()
                .map(|p| resolve_ast_with_subst(p, struct_table, enum_table, subst))
                .collect(),
        ),
        rokc_ast::TyKind::Tuple(parts) => HirTy::Tuple(
            parts
                .iter()
                .map(|p| resolve_ast_with_subst(p, struct_table, enum_table, subst))
                .collect(),
        ),
        rokc_ast::TyKind::Array(elem, len) => {
            let n = match len {
                rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Int(s)) => {
                    let cleaned: String = s.chars().filter(|c| *c != '_').collect();
                    cleaned.parse::<u32>().unwrap_or(0)
                }
                _ => 0,
            };
            HirTy::Array(
                Box::new(resolve_ast_with_subst(elem, struct_table, enum_table, subst)),
                n,
            )
        }
        rokc_ast::TyKind::Fn(args, ret) => HirTy::Fn(
            args.iter()
                .map(|a| resolve_ast_with_subst(a, struct_table, enum_table, subst))
                .collect(),
            Box::new(resolve_ast_with_subst(ret, struct_table, enum_table, subst)),
        ),
        _ => {
            let mut t = resolve_ty_with_structs(ty, struct_table, enum_table);
            substitute_aliases(&mut t, subst);
            t
        }
    }
}

/// Same as `instantiate_generic_structs` but for `enum Maybe<T>` etc.
fn instantiate_generic_enums(
    program: &Program,
    generic_enums: &HashMap<String, &AstEnumDef>,
    struct_table: &mut HashMap<String, StructId>,
    struct_defs: &mut Vec<HirStructDef>,
    enum_table: &mut HashMap<String, EnumId>,
    enum_defs: &mut Vec<HirEnumDef>,
) {
    if generic_enums.is_empty() {
        return;
    }
    for _ in 0..8 {
        let before = enum_table.len();
        for item in &program.items {
            walk_item_tys(item, &mut |ty| {
                visit_ty_for_enum_mono(
                    ty,
                    generic_enums,
                    struct_table,
                    struct_defs,
                    enum_table,
                    enum_defs,
                );
            });
        }
        if enum_table.len() == before {
            break;
        }
    }
}

fn visit_ty_for_enum_mono(
    ty: &rokc_ast::Ty,
    generic_enums: &HashMap<String, &AstEnumDef>,
    struct_table: &mut HashMap<String, StructId>,
    struct_defs: &mut Vec<HirStructDef>,
    enum_table: &mut HashMap<String, EnumId>,
    enum_defs: &mut Vec<HirEnumDef>,
) {
    match &ty.kind {
        rokc_ast::TyKind::Path(p) => {
            if p.segments.len() == 1 && !p.segments[0].generics.is_empty() {
                let name = &p.segments[0].name;
                if let Some(def) = generic_enums.get(name).copied() {
                    let arg_tys: Vec<HirTy> = p.segments[0]
                        .generics
                        .iter()
                        .map(|t| resolve_ty_with_structs(t, struct_table, enum_table))
                        .collect();
                    let mangled = format!(
                        "{}__{}",
                        name,
                        arg_tys.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
                    );
                    if !enum_table.contains_key(&mangled) {
                        let id = EnumId(
                            u32::try_from(enum_defs.len()).expect("EnumId overflow"),
                        );
                        enum_table.insert(mangled.clone(), id);
                        let mut subst: HashMap<String, HirTy> = HashMap::new();
                        for (i, gp) in def.generics.params.iter().enumerate() {
                            if let rokc_ast::GenericParam::Type { name: gn, .. } = gp {
                                if let Some(arg) = arg_tys.get(i) {
                                    subst.insert(gn.clone(), arg.clone());
                                }
                            }
                        }
                        let variants: Vec<HirEnumVariant> = def
                            .variants
                            .iter()
                            .enumerate()
                            .filter_map(|(i, v)| {
                                let tag =
                                    u32::try_from(i).expect("variant index overflow");
                                match &v.kind {
                                    rokc_ast::EnumVariantKind::Unit => Some(HirEnumVariant {
                                        name: v.name.clone(),
                                        tag,
                                        payload_ty: None,
                                        named_fields: Vec::new(),
                                    }),
                                    rokc_ast::EnumVariantKind::Tuple(tys) if tys.len() == 1 => {
                                        let t = resolve_ast_with_subst(
                                            &tys[0],
                                            struct_table,
                                            enum_table,
                                            &subst,
                                        );
                                        Some(HirEnumVariant {
                                            name: v.name.clone(),
                                            tag,
                                            payload_ty: Some(t),
                                            named_fields: Vec::new(),
                                        })
                                    }
                                    rokc_ast::EnumVariantKind::Tuple(tys) => {
                                        let parts: Vec<HirTy> = tys
                                            .iter()
                                            .map(|t| {
                                                resolve_ast_with_subst(
                                                    t,
                                                    struct_table,
                                                    enum_table,
                                                    &subst,
                                                )
                                            })
                                            .collect();
                                        Some(HirEnumVariant {
                                            name: v.name.clone(),
                                            tag,
                                            payload_ty: Some(HirTy::Tuple(parts)),
                                            named_fields: Vec::new(),
                                        })
                                    }
                                    rokc_ast::EnumVariantKind::Named(fields) => {
                                        let parts: Vec<HirTy> = fields
                                            .iter()
                                            .map(|f| {
                                                resolve_ast_with_subst(
                                                    &f.ty,
                                                    struct_table,
                                                    enum_table,
                                                    &subst,
                                                )
                                            })
                                            .collect();
                                        Some(HirEnumVariant {
                                            name: v.name.clone(),
                                            tag,
                                            payload_ty: Some(HirTy::Tuple(parts)),
                                            named_fields: fields
                                                .iter()
                                                .map(|f| f.name.clone())
                                                .collect(),
                                        })
                                    }
                                    _ => None,
                                }
                            })
                            .collect();
                        enum_defs.push(HirEnumDef {
                            id,
                            def_id: None,
                            name: mangled,
                            variants,
                            span: def.span,
                        });
                    }
                }
            }
            for seg in &p.segments {
                for g in &seg.generics {
                    visit_ty_for_enum_mono(
                        g,
                        generic_enums,
                        struct_table,
                        struct_defs,
                        enum_table,
                        enum_defs,
                    );
                }
            }
        }
        rokc_ast::TyKind::Sum(parts) | rokc_ast::TyKind::Tuple(parts) => {
            for p in parts {
                visit_ty_for_enum_mono(
                    p,
                    generic_enums,
                    struct_table,
                    struct_defs,
                    enum_table,
                    enum_defs,
                );
            }
        }
        rokc_ast::TyKind::Array(elem, _) => visit_ty_for_enum_mono(
            elem,
            generic_enums,
            struct_table,
            struct_defs,
            enum_table,
            enum_defs,
        ),
        rokc_ast::TyKind::Fn(args, ret) => {
            for a in args {
                visit_ty_for_enum_mono(
                    a,
                    generic_enums,
                    struct_table,
                    struct_defs,
                    enum_table,
                    enum_defs,
                );
            }
            visit_ty_for_enum_mono(
                ret,
                generic_enums,
                struct_table,
                struct_defs,
                enum_table,
                enum_defs,
            );
        }
        _ => {}
    }
}

/// Eager pre-pass over the program AST that finds every generic-struct
/// type usage (`Path("Pair", [T])`) and registers a fresh concrete
/// `HirStructDef` per unique substitution. The instantiation name is
/// mangled (`Pair__i32`) so subsequent type resolution treats it as
/// just another concrete struct.
fn instantiate_generic_structs(
    program: &Program,
    generic_structs: &HashMap<String, &AstStructDef>,
    struct_table: &mut HashMap<String, StructId>,
    struct_defs: &mut Vec<HirStructDef>,
    enum_table: &HashMap<String, EnumId>,
) {
    if generic_structs.is_empty() {
        return;
    }
    // Iterate to a fixpoint: instantiations themselves can reference
    // other generic structs.
    for _ in 0..8 {
        let before = struct_table.len();
        for item in &program.items {
            walk_item_tys(item, &mut |ty| {
                visit_ty_for_mono(
                    ty,
                    generic_structs,
                    struct_table,
                    struct_defs,
                    enum_table,
                );
            });
        }
        if struct_table.len() == before {
            break;
        }
    }
}

/// Visit a single AST type and instantiate any generic struct uses.
/// Recurses into composite types so nested uses are caught.
fn visit_ty_for_mono(
    ty: &rokc_ast::Ty,
    generic_structs: &HashMap<String, &AstStructDef>,
    struct_table: &mut HashMap<String, StructId>,
    struct_defs: &mut Vec<HirStructDef>,
    enum_table: &HashMap<String, EnumId>,
) {
    match &ty.kind {
        rokc_ast::TyKind::Path(p) => {
            if p.segments.len() == 1 && !p.segments[0].generics.is_empty() {
                let name = &p.segments[0].name;
                if let Some(def) = generic_structs.get(name).copied() {
                    let arg_tys: Vec<HirTy> = p.segments[0]
                        .generics
                        .iter()
                        .map(|t| resolve_ty_with_structs(t, struct_table, enum_table))
                        .collect();
                    let mangled = format!(
                        "{}__{}",
                        name,
                        arg_tys.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
                    );
                    if !struct_table.contains_key(&mangled) {
                        // Reserve the id first so a self-reference inside
                        // the struct fields (Pair<T> with field x: Pair<T>)
                        // resolves to itself rather than recursing.
                        let id = StructId(
                            u32::try_from(struct_defs.len()).expect("StructId overflow"),
                        );
                        struct_table.insert(mangled.clone(), id);
                        // Build subst { T → arg }
                        let mut subst: HashMap<String, HirTy> = HashMap::new();
                        for (i, gp) in def.generics.params.iter().enumerate() {
                            if let rokc_ast::GenericParam::Type { name: gn, .. } = gp {
                                if let Some(arg) = arg_tys.get(i) {
                                    subst.insert(gn.clone(), arg.clone());
                                }
                            }
                        }
                        // Lower fields under the substitution.
                        let fields = match &def.kind {
                            rokc_ast::StructKind::Named(named_fields) => named_fields
                                .iter()
                                .map(|f| {
                                    let t = resolve_ast_with_subst(
                                        &f.ty,
                                        struct_table,
                                        enum_table,
                                        &subst,
                                    );
                                    HirField {
                                        name: f.name.clone(),
                                        ty: t,
                                        default: f.default.clone(),
                                    }
                                })
                                .collect(),
                            _ => Vec::new(),
                        };
                        struct_defs.push(HirStructDef {
                            id,
                            def_id: None,
                            name: mangled,
                            fields,
                            span: def.span,
                            generic_args: arg_tys.clone(),
                            union_kind: None,
                        });
                    }
                }
            }
            // Recurse into generic args.
            for seg in &p.segments {
                for g in &seg.generics {
                    visit_ty_for_mono(g, generic_structs, struct_table, struct_defs, enum_table);
                }
            }
        }
        rokc_ast::TyKind::Sum(parts) | rokc_ast::TyKind::Tuple(parts) => {
            for p in parts {
                visit_ty_for_mono(p, generic_structs, struct_table, struct_defs, enum_table);
            }
        }
        rokc_ast::TyKind::Array(elem, _) => {
            visit_ty_for_mono(elem, generic_structs, struct_table, struct_defs, enum_table);
        }
        rokc_ast::TyKind::Fn(args, ret) => {
            for a in args {
                visit_ty_for_mono(a, generic_structs, struct_table, struct_defs, enum_table);
            }
            visit_ty_for_mono(ret, generic_structs, struct_table, struct_defs, enum_table);
        }
        _ => {}
    }
}

/// Walk every AST type appearing in the given top-level item, calling
/// `visitor` once per `Ty` node found. Covers the common surface used
/// for generic-struct discovery (fn signatures, struct fields, enum
/// payloads, let bindings, type ascriptions in patterns).
fn walk_item_tys<F: FnMut(&rokc_ast::Ty)>(item: &Item, visitor: &mut F) {
    match item {
        Item::Fn(f) => walk_fn_tys(f, visitor),
        Item::Struct(s) => match &s.kind {
            rokc_ast::StructKind::Named(fields) => {
                for f in fields {
                    walk_ty(&f.ty, visitor);
                }
            }
            rokc_ast::StructKind::Tuple(fields) => {
                for f in fields {
                    walk_ty(&f.ty, visitor);
                }
            }
            _ => {}
        },
        Item::Enum(e) => {
            for v in &e.variants {
                if let rokc_ast::EnumVariantKind::Tuple(tys) = &v.kind {
                    for t in tys {
                        walk_ty(t, visitor);
                    }
                }
            }
        }
        Item::Impl(impl_def) => {
            walk_ty(&impl_def.self_ty, visitor);
            for ii in &impl_def.items {
                if let rokc_ast::ImplItem::Method(m) = ii {
                    walk_fn_tys(m, visitor);
                }
            }
        }
        Item::Const(c) => walk_ty(&c.ty, visitor),
        Item::TypeAlias(a) => walk_ty(&a.ty, visitor),
        _ => {}
    }
}

fn walk_fn_tys<F: FnMut(&rokc_ast::Ty)>(f: &rokc_ast::FnDef, visitor: &mut F) {
    for p in &f.params {
        if let Some(t) = &p.ty {
            walk_ty(t, visitor);
        }
    }
    if let Some(t) = &f.ret_ty {
        walk_ty(t, visitor);
    }
    if let Some(body) = &f.body {
        walk_block_tys(body, visitor);
    }
}

fn walk_block_tys<F: FnMut(&rokc_ast::Ty)>(b: &rokc_ast::Block, visitor: &mut F) {
    for s in &b.stmts {
        walk_stmt_tys(s, visitor);
    }
    if let Some(t) = &b.trailing {
        walk_expr_tys(t, visitor);
    }
}

fn walk_stmt_tys<F: FnMut(&rokc_ast::Ty)>(s: &rokc_ast::Stmt, visitor: &mut F) {
    use rokc_ast::StmtKind as SK;
    match &s.kind {
        SK::Let { ty, init, .. } => {
            if let Some(t) = ty {
                walk_ty(t, visitor);
            }
            walk_expr_tys(init, visitor);
        }
        SK::LetTuple { ty, init, .. } => {
            if let Some(t) = ty {
                walk_ty(t, visitor);
            }
            walk_expr_tys(init, visitor);
        }
        SK::LetStruct { ty, init, .. } => {
            if let Some(t) = ty {
                walk_ty(t, visitor);
            }
            walk_expr_tys(init, visitor);
        }
        SK::Assign(a, b) => {
            walk_expr_tys(a, visitor);
            walk_expr_tys(b, visitor);
        }
        SK::CompoundAssign { target, value, .. } => {
            walk_expr_tys(target, visitor);
            walk_expr_tys(value, visitor);
        }
        SK::Expr(e) | SK::Trailing(e) => walk_expr_tys(e, visitor),
        SK::Return(e) => {
            if let Some(e) = e {
                walk_expr_tys(e, visitor);
            }
        }
        _ => {}
    }
}

fn walk_expr_tys<F: FnMut(&rokc_ast::Ty)>(e: &Expr, visitor: &mut F) {
    use ExprKind as E;
    match &e.kind {
        E::Cast(inner, ty) => {
            walk_expr_tys(inner, visitor);
            walk_ty(ty, visitor);
        }
        E::Block(b) => walk_block_tys(b, visitor),
        E::If { cond, then_branch, else_branch } => {
            walk_expr_tys(cond, visitor);
            walk_block_tys(then_branch, visitor);
            if let Some(eb) = else_branch {
                walk_expr_tys(eb, visitor);
            }
        }
        E::While { cond, body, .. } => {
            walk_expr_tys(cond, visitor);
            walk_block_tys(body, visitor);
        }
        E::For { iter, body, .. } => {
            walk_expr_tys(iter, visitor);
            walk_block_tys(body, visitor);
        }
        E::Loop { body, .. } => walk_block_tys(body, visitor),
        E::Match { scrutinee, arms } => {
            walk_expr_tys(scrutinee, visitor);
            for arm in arms {
                if let Some(g) = &arm.guard {
                    walk_expr_tys(g, visitor);
                }
                walk_expr_tys(&arm.body, visitor);
            }
        }
        E::Call { callee, args, .. } => {
            walk_expr_tys(callee, visitor);
            for a in args {
                if let rokc_ast::CallArg::Positional(e) = a {
                    walk_expr_tys(e, visitor);
                }
            }
        }
        E::MethodCall { receiver, args, type_args, .. } => {
            walk_expr_tys(receiver, visitor);
            for t in type_args {
                walk_ty(t, visitor);
            }
            for a in args {
                if let rokc_ast::CallArg::Positional(e) = a {
                    walk_expr_tys(e, visitor);
                }
            }
        }
        E::OpInfix { lhs, rhs, .. } => {
            walk_expr_tys(lhs, visitor);
            walk_expr_tys(rhs, visitor);
        }
        E::OpPrefix { operand, .. } | E::OpPostfix { operand, .. } => {
            walk_expr_tys(operand, visitor);
        }
        E::Tuple(items) | E::List(items) => {
            for i in items {
                walk_expr_tys(i, visitor);
            }
        }
        E::Field(t, _) | E::TupleField(t, _) => walk_expr_tys(t, visitor),
        E::Index(a, b) => {
            walk_expr_tys(a, visitor);
            walk_expr_tys(b, visitor);
        }
        E::StructInit { path, fields, spread } => {
            // Spec 2.10: explicit generic instantiation `Pair<i32, i32> { ... }`
            // attaches type args to the path. Synthesize a `TyKind::Path`
            // wrapper so the monomorphization walker sees the
            // instantiation even when no signature mentions the same
            // shape, then visit nested arg types.
            if path.segments.iter().any(|s| !s.generics.is_empty()) {
                let synth = rokc_ast::Ty {
                    kind: rokc_ast::TyKind::Path(path.clone()),
                    span: path.span,
                };
                walk_ty(&synth, visitor);
            }
            for (_, f) in fields {
                walk_expr_tys(f, visitor);
            }
            if let Some(s) = spread {
                walk_expr_tys(s, visitor);
            }
        }
        E::Closure { params, ret_ty, body, .. } => {
            for p in params {
                if let Some(t) = &p.ty {
                    walk_ty(t, visitor);
                }
            }
            if let Some(t) = ret_ty {
                walk_ty(t, visitor);
            }
            walk_expr_tys(body, visitor);
        }
        E::QuestionDot(t, _) => walk_expr_tys(t, visitor),
        E::NullishCoalesce(a, b) => {
            walk_expr_tys(a, visitor);
            walk_expr_tys(b, visitor);
        }
        _ => {}
    }
}

fn walk_ty<F: FnMut(&rokc_ast::Ty)>(t: &rokc_ast::Ty, visitor: &mut F) {
    visitor(t);
    match &t.kind {
        rokc_ast::TyKind::Path(p) => {
            for seg in &p.segments {
                for g in &seg.generics {
                    walk_ty(g, visitor);
                }
            }
        }
        rokc_ast::TyKind::Sum(parts) | rokc_ast::TyKind::Tuple(parts) => {
            for p in parts {
                walk_ty(p, visitor);
            }
        }
        rokc_ast::TyKind::Array(elem, _) => walk_ty(elem, visitor),
        rokc_ast::TyKind::Fn(args, ret) => {
            for a in args {
                walk_ty(a, visitor);
            }
            walk_ty(ret, visitor);
        }
        _ => {}
    }
}

/// Walk a `HirTy` substituting any unresolved `Path([alias_name])`
/// nodes with their concrete type from `aliases`. Multi-level
/// resolution is handled by the caller (a small fixed-iteration loop
/// over the alias table itself).
fn substitute_aliases(ty: &mut HirTy, aliases: &HashMap<String, HirTy>) {
    match ty {
        HirTy::Path(parts) => {
            if parts.len() == 1 {
                if let Some(replacement) = aliases.get(&parts[0]) {
                    *ty = replacement.clone();
                }
            }
        }
        HirTy::Sum(parts) | HirTy::Tuple(parts) => {
            for p in parts {
                substitute_aliases(p, aliases);
            }
        }
        HirTy::Array(elem, _) => substitute_aliases(elem, aliases),
        HirTy::Fn(args, ret) | HirTy::Closure { args, ret, .. } => {
            for a in args {
                substitute_aliases(a, aliases);
            }
            substitute_aliases(ret, aliases);
        }
        _ => {}
    }
}

// `resolve_ty` plus struct/enum name lookup.
fn resolve_ty_with_structs(
    ty: &rokc_ast::Ty,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
) -> HirTy {
    if let rokc_ast::TyKind::Path(p) = &ty.kind {
        if p.segments.len() == 1 {
            // Generic-{struct,enum} instantiation: look up under the
            // mangled name produced by the pre-pass.
            if !p.segments[0].generics.is_empty() {
                let arg_tys: Vec<HirTy> = p.segments[0]
                    .generics
                    .iter()
                    .map(|t| resolve_ty_with_structs(t, structs, enums))
                    .collect();
                let mangled = format!(
                    "{}__{}",
                    p.segments[0].name,
                    arg_tys.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
                );
                if let Some(id) = structs.get(&mangled) {
                    return HirTy::Struct(*id);
                }
                if let Some(id) = enums.get(&mangled) {
                    return HirTy::Enum(*id);
                }
            }
            if let Some(id) = structs.get(&p.segments[0].name) {
                return HirTy::Struct(*id);
            }
            if let Some(id) = enums.get(&p.segments[0].name) {
                return HirTy::Enum(*id);
            }
        }
    }
    if let rokc_ast::TyKind::Array(elem, len) = &ty.kind {
        let n = match len {
            rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Int(s)) => {
                let cleaned: String = s.chars().filter(|c| *c != '_').collect();
                cleaned.parse::<u32>().unwrap_or(0)
            }
            _ => 0,
        };
        return HirTy::Array(
            Box::new(resolve_ty_with_structs(elem, structs, enums)),
            n,
        );
    }
    // `T | U` — recurse so Path("Counter") resolves to Struct(id), not
    // an opaque path the MIR layer would treat as `Any`.
    if let rokc_ast::TyKind::Sum(parts) = &ty.kind {
        return HirTy::Sum(
            parts.iter().map(|p| resolve_ty_with_structs(p, structs, enums)).collect(),
        );
    }
    if let rokc_ast::TyKind::Tuple(parts) = &ty.kind {
        if parts.is_empty() {
            return HirTy::Unit;
        }
        return HirTy::Tuple(
            parts.iter().map(|p| resolve_ty_with_structs(p, structs, enums)).collect(),
        );
    }
    if let rokc_ast::TyKind::Fn(args, ret) = &ty.kind {
        return HirTy::Fn(
            args.iter()
                .map(|a| resolve_ty_with_structs(a, structs, enums))
                .collect(),
            Box::new(resolve_ty_with_structs(ret, structs, enums)),
        );
    }
    resolve_ty(ty)
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

fn lower_fn(
    fn_def: &FnDef,
    id: FunctionId,
    method_self_ty: Option<HirTy>,
    fns: &HashMap<String, FnSig>,
    methods: &HashMap<(MethodTarget, String), FunctionId>,
    structs: &[HirStructDef],
    enums: &[HirEnumDef],
    struct_table: &HashMap<String, StructId>,
    enum_table: &HashMap<String, EnumId>,
    consts: &HashMap<String, Expr>,
    type_aliases: &HashMap<String, HirTy>,
    generic_fns: &HashMap<String, &FnDef>,
    prec: &PrecTable,
    sink: &ClosureSink,
    item_visibility: &HashMap<String, Visibility>,
    uses: &crate::uses::UseTable,
    impl_traits: &std::collections::HashSet<(MethodTarget, String)>,
    statics: &HashMap<String, HirTy>,
) -> HirFunction {
    let empty_subst: HashMap<String, HirTy> = HashMap::new();
    let mut ctx = LowerCtx::new(
        fns,
        methods,
        structs,
        enums,
        struct_table,
        enum_table,
        consts,
        type_aliases,
        &empty_subst,
        generic_fns,
        method_self_ty.clone(),
        prec,
        sink,
        item_visibility,
        uses,
        impl_traits,
        statics,
    );
    ctx.current_module = module_of(&fn_def.name);

    let mut params = Vec::with_capacity(fn_def.params.len());
    for p in &fn_def.params {
        params.push(lower_param(&mut ctx, p));
    }

    let mut ret_ty = match &fn_def.ret_ty {
        Some(t) => resolve_ty_with_structs(t, struct_table, enum_table),
        None => HirTy::Unit,
    };
    substitute_aliases(&mut ret_ty, type_aliases);
    ctx.fn_ret_ty = ret_ty.clone();

    let body = fn_def.body.as_ref().map(|b| lower_block(&mut ctx, b));

    // Methods get a synthetic mangled name so multiple impls of the
    // same method name don't collide as MLIR symbols.
    let name = method_self_ty
        .as_ref()
        .map(|ty| format!("{}__{}", ty_mangle(ty), fn_def.name))
        .unwrap_or_else(|| fn_def.name.clone());

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

// If `slot_ty` is a Sum and `value.ty` matches one of its variants,
// wrap the value into the sum's tagged-union representation.
fn wrap_into_sum(slot_ty: &HirTy, value: HirExpr) -> HirExpr {
    let HirTy::Sum(variants) = slot_ty else { return value };
    let Some(idx) = sum_variant_index(variants, &value.ty) else { return value };
    let span = value.span;
    let is_none_variant = matches!(variants[idx], HirTy::Path(ref p) if p.as_slice() == ["none"]);
    let payload = if is_none_variant {
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

// Locate `value_ty` in a sum's variant list. Equality is structural for
// our slice (Prim same, `none` matches the special `Path(["none"])`).
fn sum_variant_index(variants: &[HirTy], value_ty: &HirTy) -> Option<usize> {
    variants.iter().position(|v| sum_variants_match(v, value_ty))
}

fn sum_variants_match(variant: &HirTy, value: &HirTy) -> bool {
    match (variant, value) {
        (HirTy::Prim(a), HirTy::Prim(b)) => a == b,
        (HirTy::Path(a), HirTy::Path(b)) => a == b,
        (HirTy::Struct(a), HirTy::Struct(b)) => a == b,
        (HirTy::Enum(a), HirTy::Enum(b)) => a == b,
        (HirTy::Path(a), _) if a.as_slice() == ["none"] => {
            matches!(value, HirTy::Path(p) if p.as_slice() == ["none"])
        }
        _ => false,
    }
}

fn ty_mangle(ty: &HirTy) -> String {
    match ty {
        HirTy::Struct(id) => format!("Struct{}", id.0),
        HirTy::Enum(id) => format!("Enum{}", id.0),
        HirTy::Prim(p) => p.name().to_owned(),
        HirTy::Unit => "Unit".to_owned(),
        HirTy::Any => "Any".to_owned(),
        HirTy::Unknown => "Unknown".to_owned(),
        HirTy::Tuple(parts) => {
            let inner: Vec<String> = parts.iter().map(ty_mangle).collect();
            format!("Tup{}of{}", parts.len(), inner.join("x"))
        }
        HirTy::Array(elem, len) => format!("Arr{}x{}", len, ty_mangle(elem)),
        HirTy::Sum(variants) => {
            let inner: Vec<String> = variants.iter().map(ty_mangle).collect();
            format!("Sum{}of{}", variants.len(), inner.join("x"))
        }
        HirTy::Fn(params, ret) => {
            let inner: Vec<String> = params.iter().map(ty_mangle).collect();
            format!("Fn{}of{}_to_{}", params.len(), inner.join("x"), ty_mangle(ret))
        }
        HirTy::Path(segs) => format!("Path_{}", segs.join("_")),
        HirTy::Closure { args, ret, env } => {
            let inner: Vec<String> = args.iter().map(ty_mangle).collect();
            format!(
                "Closure{}of{}_to_{}_env{}",
                args.len(),
                inner.join("x"),
                ty_mangle(ret),
                ty_mangle(env)
            )
        }
    }
}

fn lower_param(ctx: &mut LowerCtx<'_>, p: &Param) -> HirParam {
    let ty = if p.name == "self" {
        // Implicit `self` receiver inherits the impl target's type.
        ctx.self_ty.clone().unwrap_or(HirTy::Any)
    } else {
        p.ty.as_ref().map_or(HirTy::Any, |t| ctx.resolve_ast_ty(t))
    };
    let local = ctx.declare(Some(p.name.clone()), ty.clone());
    HirParam { name: p.name.clone(), local, ty, by_ref: p.by_ref }
}

fn lower_block(ctx: &mut LowerCtx<'_>, block: &Block) -> HirBlock {
    ctx.push_scope();
    let mut stmts = Vec::with_capacity(block.stmts.len());
    for s in &block.stmts {
        // `let (a, b, ...) = init;` desugars in HIR to a fresh tuple
        // local plus per-name index reads. Multi-stmt expansion lives
        // here so `lower_stmt` can stay 1-in / 1-out.
        // `for pat in start..end { body }` desugars in HIR to:
        //   { let __c = start; while __c < end { let pat = __c; body; __c = __c + 1; } }
        // We expand here (rather than in `lower_stmt`) so the resulting
        // HirStmts land directly in the enclosing block's stmt list.
        if let StmtKind::Expr(expr) | StmtKind::Trailing(expr) = &s.kind {
            if let ExprKind::For { label, pat, iter, body } = &expr.kind {
                if let Some(expanded) = lower_for_range(ctx, label, pat, iter, body, expr.span) {
                    stmts.extend(expanded);
                    continue;
                }
                if let Some(expanded) = lower_for_array(ctx, label, pat, iter, body, expr.span) {
                    stmts.extend(expanded);
                    continue;
                }
            }
        }

        if let StmtKind::LetStruct { path: _, fields, rest: _, ty, init } = &s.kind {
            let pre_ty = ty.as_ref().map(|t| ctx.resolve_ast_ty(t));
            if let Some(t) = &pre_ty {
                ctx.push_expected(t.clone());
            }
            let init_h = lower_expr(ctx, init);
            if pre_ty.is_some() {
                ctx.pop_expected();
            }
            let init_ty = init_h.ty.clone();
            let temp_local = ctx.declare(None, init_ty.clone());
            stmts.push(HirStmt::Let {
                local: temp_local,
                init: init_h,
            });
            let HirTy::Struct(sid) = init_ty.clone() else {
                // Source isn't a struct — bail; later passes will report.
                continue;
            };
            for (field_name, bind_name) in fields {
                let def = &ctx.structs[sid.0 as usize];
                let Some(idx) = def.fields.iter().position(|f| &f.name == field_name) else {
                    continue;
                };
                let field_ty = def.fields[idx].ty.clone();
                let read = HirExpr {
                    ty: field_ty.clone(),
                    span: s.span,
                    kind: HirExprKind::FieldRead {
                        target: Box::new(HirExpr {
                            ty: init_ty.clone(),
                            span: s.span,
                            kind: HirExprKind::Local(temp_local),
                        }),
                        struct_id: sid,
                        field_index: u32::try_from(idx).expect("field idx overflow"),
                        field_ty: field_ty.clone(),
                    },
                };
                let local = ctx.declare(Some(bind_name.clone()), field_ty);
                stmts.push(HirStmt::Let { local, init: read });
            }
            continue;
        }
        if let StmtKind::LetTuple { names, rest, ty: _, init } = &s.kind {
            let init_h = lower_expr(ctx, init);
            let init_ty = init_h.ty.clone();
            // Spec 3.15.2/3.15.3: length must match (no rest), or be ≥
            // names.len() when a `..` is present.
            if let HirTy::Tuple(ts) = &init_ty {
                let needed = names.len();
                let have = ts.len();
                if rest.is_none() {
                    if have != needed {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "tuple destructure length mismatch: pattern has {} \
                                 element{}, value has {} (spec 3.15.2)",
                                needed,
                                if needed == 1 { "" } else { "s" },
                                have
                            ),
                        );
                    }
                } else if have < needed {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "tuple destructure too short: pattern needs at least \
                             {} non-rest element{}, value has {} (spec 3.15.3)",
                            needed,
                            if needed == 1 { "" } else { "s" },
                            have
                        ),
                    );
                }
            }
            let tuple_local = ctx.declare(None, init_ty.clone());
            stmts.push(HirStmt::Let {
                local: tuple_local,
                init: init_h,
            });
            let elem_tys: Vec<HirTy> = match &init_ty {
                HirTy::Tuple(ts) => ts.clone(),
                _ => Vec::new(),
            };
            // Build the source-position → name binding mapping. With a
            // rest at index `r` and value tuple of length `N`:
            //   names[..r]      → init.0  .. init.r-1
            //   rest (if named) → tuple of init.r .. init.r + (N-needed) - 1
            //   names[r..]      → init.r+(N-needed) .. init.N-1
            let needed = names.len();
            let have = elem_tys.len();
            let rest_take = if let Some(_) = rest {
                have.saturating_sub(needed)
            } else {
                0
            };
            let rest_idx = rest.as_ref().map(|(i, _)| *i).unwrap_or(needed);

            for (i, name) in names.iter().enumerate() {
                if name == "_" {
                    continue;
                }
                let init_index = if i < rest_idx { i } else { i + rest_take };
                let elem_ty = elem_tys.get(init_index).cloned().unwrap_or(HirTy::Unknown);
                let read = HirExpr {
                    ty: elem_ty.clone(),
                    span: s.span,
                    kind: HirExprKind::TupleField {
                        target: Box::new(HirExpr {
                            ty: init_ty.clone(),
                            span: s.span,
                            kind: HirExprKind::Local(tuple_local),
                        }),
                        index: u32::try_from(init_index).expect("tuple index overflow"),
                        field_ty: elem_ty.clone(),
                    },
                };
                let local = ctx.declare(Some(name.clone()), elem_ty);
                stmts.push(HirStmt::Let { local, init: read });
            }
            // Synthesize the rest-binding's sub-tuple if it was named.
            if let Some((rest_idx, Some(rest_name))) = rest {
                let mut sub_tys: Vec<HirTy> = Vec::with_capacity(rest_take);
                let mut sub_fields: Vec<HirExpr> = Vec::with_capacity(rest_take);
                for k in 0..rest_take {
                    let src = rest_idx + k;
                    let ety = elem_tys.get(src).cloned().unwrap_or(HirTy::Unknown);
                    sub_tys.push(ety.clone());
                    sub_fields.push(HirExpr {
                        ty: ety.clone(),
                        span: s.span,
                        kind: HirExprKind::TupleField {
                            target: Box::new(HirExpr {
                                ty: init_ty.clone(),
                                span: s.span,
                                kind: HirExprKind::Local(tuple_local),
                            }),
                            index: u32::try_from(src).expect("tuple index overflow"),
                            field_ty: ety,
                        },
                    });
                }
                let rest_ty = HirTy::Tuple(sub_tys);
                let rest_local = ctx.declare(Some(rest_name.clone()), rest_ty.clone());
                stmts.push(HirStmt::Let {
                    local: rest_local,
                    init: HirExpr {
                        ty: rest_ty,
                        span: s.span,
                        kind: HirExprKind::Tuple { fields: sub_fields },
                    },
                });
            }
            continue;
        }
        if let Some(stmt) = lower_stmt(ctx, s) {
            stmts.push(stmt);
        }
    }
    // A trailing `for` expression has no value — expand it as a stmt
    // so nested for-loops still get the desugar treatment when they
    // sit at the end of a block without a trailing `;`.
    let trailing = if let Some(e) = block.trailing.as_ref() {
        if let ExprKind::For { label, pat, iter, body } = &e.kind {
            if let Some(expanded) = lower_for_range(ctx, label, pat, iter, body, e.span) {
                stmts.extend(expanded);
                None
            } else if let Some(expanded) = lower_for_array(ctx, label, pat, iter, body, e.span) {
                stmts.extend(expanded);
                None
            } else {
                Some(lower_expr(ctx, e))
            }
        } else {
            Some(lower_expr(ctx, e))
        }
    } else {
        None
    };
    ctx.pop_scope();
    HirBlock {
        stmts,
        trailing,
        label: block.label.clone(),
    }
}

fn lower_stmt(ctx: &mut LowerCtx<'_>, stmt: &Stmt) -> Option<HirStmt> {
    match &stmt.kind {
        StmtKind::Let { name, ty, init } => {
            // Spec variant 238-239: same-scope `let` redeclaration is
            // banned (typo guard, no shadowing). Different scopes still
            // create fresh bindings.
            if ctx.lookup_in_current_scope(name).is_some() {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "`{name}` is already declared in this scope. rok forbids \
                         redeclaration with `let`; use `=` to reassign or pick a \
                         different name (spec variant 238)"
                    ),
                );
            }
            // Resolve the declared type up front so the init lowering
            // can pick the right generic-enum instantiation when the
            // user wrote `Box::None` and several `Box<T>`s are in scope.
            let pre_ty = ty.as_ref().map(|t| ctx.resolve_ast_ty(t));
            if let Some(t) = &pre_ty {
                ctx.push_expected(t.clone());
            }
            let init = lower_expr(ctx, init);
            if pre_ty.is_some() {
                ctx.pop_expected();
            }
            let declared_ty = pre_ty.unwrap_or_else(|| init.ty.clone());
            // Implicit sum-type wrap: when the slot type is `A | B | ...`
            // and the initialiser's type matches one of the variants,
            // wrap the value in `{tag, payload}` so subsequent uses see
            // the sum representation.
            let init = wrap_into_sum(&declared_ty, init);
            let local = ctx.declare(Some(name.clone()), declared_ty);
            Some(HirStmt::Let { local, init })
        }
        StmtKind::Return(value) => {
            let v = value.as_ref().map(|e| {
                ctx.push_expected(ctx.fn_ret_ty.clone());
                let lowered = lower_expr(ctx, e);
                ctx.pop_expected();
                let wrapped = wrap_into_sum(&ctx.fn_ret_ty, lowered);
                // Spec 4.5/4.6: a closure with captures isn't a plain
                // `fn(...)` pointer — it's a `Closure { fn_ptr, env }`
                // pair. Returning it through a `fn(...)`-typed slot
                // would emit a struct value into a pointer slot at MIR
                // (mlir-opt rejects with a type mismatch). Diagnose so
                // the user gets a clear message instead of an opaque
                // codegen error.
                if let HirTy::Fn(_, _) = &ctx.fn_ret_ty {
                    if matches!(&wrapped.ty, HirTy::Closure { .. }) {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            "cannot return a closure through a `fn(...)` \
                             pointer return type — closures with captures \
                             aren't bare function pointers (spec 4.6). \
                             Either remove captures or change the return \
                             type to a closure-typed alias.".to_owned(),
                        );
                    }
                }
                wrapped
            });
            Some(HirStmt::Return(v))
        }
        StmtKind::Expr(expr) | StmtKind::Trailing(expr) => {
            Some(HirStmt::Expr(lower_expr(ctx, expr)))
        }
        StmtKind::Item(rokc_ast::Item::Use(u)) => {
            // Function-local `use` — flatten the tree into UseEntries
            // and push them into the current scope's local_uses list.
            // The driver's per-module `use` table doesn't know about
            // these (they're inside a function body), so we register at
            // lower time.
            let mut entries = Vec::new();
            crate::uses::flatten_tree_for_local(
                &u.tree,
                &[],
                &ctx.current_module,
                &mut entries,
            );
            for e in entries {
                ctx.add_local_use(e);
            }
            None
        }
        StmtKind::Assign(target, value) => {
            // Pre-resolve the bare-name target's slot type so we can push it
            // as the expected type before lowering the value, letting leaf
            // lowerings (e.g. `Box::None`) pick the right instantiation.
            let pre_slot = match &target.kind {
                ExprKind::Path(p) if p.segments.len() == 1 => ctx
                    .lookup(&p.segments[0].name)
                    .map(|l| ctx.local_ty(l)),
                _ => None,
            };
            let pushed = pre_slot.is_some();
            if let Some(t) = &pre_slot {
                ctx.push_expected(t.clone());
            }
            let value = lower_expr(ctx, value);
            if pushed {
                ctx.pop_expected();
            }
            match &target.kind {
                // Bare-name assignment. Wrap the value into the local's
                // sum type when assigning a primitive into a `T | none`
                // slot, mirroring the let-init behaviour.
                ExprKind::Path(p) if p.segments.len() == 1 => {
                    if let Some(local) = ctx.lookup(&p.segments[0].name) {
                        let slot_ty = ctx.local_ty(local);
                        let value = wrap_into_sum(&slot_ty, value);
                        return Some(HirStmt::Assign { local, value });
                    }
                    // Fall back to a `static` write when the bare name
                    // matches a module-level `static`.
                    if let Some(ty) = ctx.statics.get(&p.segments[0].name).cloned() {
                        let value = wrap_into_sum(&ty, value);
                        return Some(HirStmt::StaticAssign {
                            name: p.segments[0].name.clone(),
                            value,
                        });
                    }
                    // Spec variant 234-235: bare-name assign requires the
                    // name to have been previously declared (with `let`).
                    // Without this check a typo (`coutner = ...`) would
                    // silently bind nothing and silently miscompile.
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "`{}` is not declared. Use `let` to introduce a new \
                             binding (typo guard, spec variant 234)",
                            p.segments[0].name
                        ),
                    );
                    None
                }
                // `arr[idx] = value` — element store on a local array.
                ExprKind::Index(arr_expr, idx_expr) => {
                    let arr_h = lower_expr(ctx, arr_expr);
                    let idx_h = lower_expr(ctx, idx_expr);
                    let HirExprKind::Local(arr_local) = &arr_h.kind else { return None };
                    let HirTy::Array(elem, _) = &arr_h.ty else { return None };
                    return Some(HirStmt::ArrayAssign {
                        array_local: *arr_local,
                        index: idx_h,
                        value,
                        elem_ty: (**elem).clone(),
                    });
                }
                // `a.f1.f2.... = value` — peel field accesses to find the
                // root local, then thread `WithField` updates back out so
                // the rebuilt aggregate gets assigned to that local.
                ExprKind::Field(_, _) => {
                    let mut chain: Vec<&str> = Vec::new();
                    let mut cur: &Expr = target;
                    while let ExprKind::Field(inner, name) = &cur.kind {
                        chain.push(name);
                        cur = inner;
                    }
                    chain.reverse();
                    let root_h = lower_expr(ctx, cur);
                    let HirExprKind::Local(local) = &root_h.kind else {
                        return None;
                    };
                    let local = *local;
                    // Walk the chain to get each level's struct id and field index.
                    struct Step {
                        ty: HirTy,
                        struct_id: StructId,
                        field_index: u32,
                    }
                    let mut steps: Vec<Step> = Vec::new();
                    let mut step_ty = root_h.ty.clone();
                    for name in &chain {
                        let HirTy::Struct(sid) = step_ty.clone() else {
                            return None;
                        };
                        let def = &ctx.structs[sid.0 as usize];
                        let idx = def.fields.iter().position(|f| &f.name == name)?;
                        let field_ty = def.fields[idx].ty.clone();
                        steps.push(Step {
                            ty: step_ty.clone(),
                            struct_id: sid,
                            field_index: u32::try_from(idx).expect("field index overflow"),
                        });
                        step_ty = field_ty;
                    }
                    // Build WithField from innermost out. The innermost
                    // value is the assigned `value`; each outer step
                    // wraps the previous result.
                    let mut acc = value;
                    let mut targets: Vec<HirExpr> = Vec::new();
                    // Materialize parent values via field reads so each
                    // WithField has a concrete target.
                    let mut walk = root_h.clone();
                    for step in &steps[..steps.len() - 1] {
                        let next_ty = ctx.structs[step.struct_id.0 as usize].fields
                            [step.field_index as usize]
                            .ty
                            .clone();
                        let read = HirExpr {
                            ty: next_ty.clone(),
                            span: target.span,
                            kind: HirExprKind::FieldRead {
                                target: Box::new(walk.clone()),
                                struct_id: step.struct_id,
                                field_index: step.field_index,
                                field_ty: next_ty.clone(),
                            },
                        };
                        targets.push(walk.clone());
                        walk = read;
                    }
                    targets.push(walk);
                    for (i, step) in steps.iter().enumerate().rev() {
                        let parent = targets[i].clone();
                        acc = HirExpr {
                            ty: step.ty.clone(),
                            span: target.span,
                            kind: HirExprKind::WithField {
                                target: Box::new(parent),
                                struct_id: step.struct_id,
                                field_index: step.field_index,
                                value: Box::new(acc),
                            },
                        };
                    }
                    Some(HirStmt::Assign { local, value: acc })
                }
                _ => None,
            }
        }
        StmtKind::Break { label, value } => Some(HirStmt::Break {
            label: label.clone(),
            value: value.as_ref().map(|e| lower_expr(ctx, e)),
        }),
        StmtKind::Continue { label } => Some(HirStmt::Continue { label: label.clone() }),
        StmtKind::Throw(value) => {
            // Stage 1 lowering: `throw v` becomes `rok_panic(code)` then
            // an unreachable terminator. `code` is the value as i32; a
            // future stage will carry the actual thrown payload.
            let value_h = lower_expr(ctx, value);
            let code = match &value_h.ty {
                HirTy::Prim(PrimTy::I32) => value_h,
                _ => HirExpr {
                    kind: HirExprKind::Const(ConstVal::Int {
                        value: 1,
                        ty: PrimTy::I32,
                    }),
                    ty: HirTy::Prim(PrimTy::I32),
                    span: stmt.span,
                },
            };
            let panic_id = ctx.fn_table.get("rok_panic").map(|s| s.id)?;
            let call = HirExpr {
                kind: HirExprKind::Call {
                    callee: panic_id,
                    args: vec![code],
                },
                ty: HirTy::Unit,
                span: stmt.span,
            };
            // Surfaced as `HirStmt::Throw` (divergent). MIR lowers it as
            // the panic call followed by an `unreachable` terminator —
            // important for `let v = if c { 7 } else { throw 99; };` so
            // the if's else-arm doesn't try to feed unit into the merge
            // block (spec 3.14.1).
            Some(HirStmt::Throw(call))
        }
        // Other statement kinds are not yet lowered.
        _ => None,
    }
}

fn lower_expr(ctx: &mut LowerCtx<'_>, expr: &Expr) -> HirExpr {
    match &expr.kind {
        ExprKind::Literal(lit) => lower_literal(lit, expr.span),
        ExprKind::Path(p) => lower_path(ctx, p, expr.span),
        ExprKind::SelfLower => {
            if let Some(local) = ctx.lookup("self") {
                let ty = ctx.local_ty(local);
                HirExpr {
                    kind: HirExprKind::Local(local),
                    ty,
                    span: expr.span,
                }
            } else {
                HirExpr {
                    kind: HirExprKind::Const(ConstVal::Unit),
                    ty: HirTy::Unknown,
                    span: expr.span,
                }
            }
        }
        ExprKind::Block(b) => {
            let block = lower_block(ctx, b);
            // Spec 3.9.10: a labelled block's value can come from a
            // `break 'label value` inside its body, not just from a
            // trailing expression. Walk for break-value types when the
            // block carries a label.
            let break_ty = block
                .label
                .as_deref()
                .and_then(|lbl| first_break_value_ty(&block, Some(lbl)));
            let ty = block
                .trailing
                .as_ref()
                .map_or_else(|| break_ty.clone().unwrap_or(HirTy::Unit), |e| e.ty.clone());
            HirExpr {
                kind: HirExprKind::Block(Box::new(block)),
                ty,
                span: expr.span,
            }
        }
        ExprKind::OpInfix { op, lhs, rhs } => lower_infix(ctx, op, lhs, rhs, expr.span),
        ExprKind::OpPrefix { op, operand } => lower_prefix(ctx, op, operand, expr.span),
        ExprKind::Call { callee, args, trailing_closure } => {
            // Spec 4.8: trailing closure becomes the last positional arg.
            let mut all_args: Vec<rokc_ast::CallArg> = args.clone();
            if let Some(tc) = trailing_closure {
                all_args.push(rokc_ast::CallArg::Positional((**tc).clone()));
            }
            lower_call(ctx, callee, &all_args, expr.span)
        }
        ExprKind::MethodCall { receiver, method, args, trailing_closure, .. } => {
            let mut all_args: Vec<rokc_ast::CallArg> = args.clone();
            if let Some(tc) = trailing_closure {
                all_args.push(rokc_ast::CallArg::Positional((**tc).clone()));
            }
            lower_method_call(ctx, receiver, method, &all_args, expr.span)
        }
        ExprKind::If { cond, then_branch, else_branch } => {
            lower_if(ctx, cond, then_branch, else_branch.as_deref(), expr.span)
        }
        ExprKind::While { label, cond, body } => {
            let cond_h = lower_expr(ctx, cond);
            let body_h = lower_block(ctx, body);
            HirExpr {
                kind: HirExprKind::While {
                    label: label.clone(),
                    cond: Box::new(cond_h),
                    body: Box::new(body_h),
                },
                ty: HirTy::Unit,
                span: expr.span,
            }
        }
        ExprKind::Match { scrutinee, arms } => lower_match(ctx, scrutinee, arms, expr.span),
        ExprKind::Try { body, catches: _, finally } => {
            // Stage 1: no real unwind. The body runs as a normal block;
            // any `throw` inside aborts the process via `rok_panic`, so
            // catch arms are unreachable and discarded. A `finally`
            // block (when present) executes after the body — it sits
            // outside the would-be unwind path so it still runs in this
            // simplified model.
            let body_h = lower_block(ctx, body);
            let body_ty = body_h
                .trailing
                .as_ref()
                .map(|e| e.ty.clone())
                .unwrap_or(HirTy::Unit);

            // No finally → forward the body block as-is so its trailing
            // expression remains the value.
            let Some(fin) = finally else {
                return HirExpr {
                    kind: HirExprKind::Block(Box::new(body_h)),
                    ty: body_ty,
                    span: expr.span,
                };
            };

            // With finally: stash the body's value in a temp, run
            // finally's stmts, then yield the temp as the trailing
            // expression.
            let mut stmts = body_h.stmts;
            let result_local = match body_h.trailing {
                Some(t) => {
                    let local = ctx.declare(None, body_ty.clone());
                    stmts.push(HirStmt::Let { local, init: t });
                    Some(local)
                }
                None => None,
            };
            let fin_h = lower_block(ctx, fin);
            stmts.extend(fin_h.stmts);
            if let Some(t) = fin_h.trailing {
                stmts.push(HirStmt::Expr(t));
            }
            let trailing = result_local.map(|l| HirExpr {
                kind: HirExprKind::Local(l),
                ty: body_ty.clone(),
                span: expr.span,
            });
            HirExpr {
                kind: HirExprKind::Block(Box::new(HirBlock {
                    stmts,
                    trailing,
                    label: None,
                })),
                ty: body_ty,
                span: expr.span,
            }
        }
        ExprKind::StructInit { path, fields, spread: _ } => {
            lower_struct_init(ctx, path, fields, expr.span)
        }
        ExprKind::Field(target, name) => lower_field(ctx, target, name, expr.span),
        ExprKind::Tuple(items) => {
            let lowered: Vec<HirExpr> = items.iter().map(|e| lower_expr(ctx, e)).collect();
            let tys: Vec<HirTy> = lowered.iter().map(|e| e.ty.clone()).collect();
            HirExpr {
                ty: HirTy::Tuple(tys),
                span: expr.span,
                kind: HirExprKind::Tuple { fields: lowered },
            }
        }
        ExprKind::TupleField(target, index) => {
            let target_h = lower_expr(ctx, target);
            // Spec 2.7.4: tuple-form structs (`struct Foo(i32);`) expose
            // their fields via the same `.N` syntax as tuples. Struct
            // receivers consult the registered field-by-position before
            // falling back to Unknown (which would then mis-type as i64).
            let field_ty = match &target_h.ty {
                HirTy::Tuple(ts) => ts.get(*index as usize).cloned().unwrap_or(HirTy::Unknown),
                HirTy::Struct(sid) => ctx.structs[sid.0 as usize]
                    .fields
                    .get(*index as usize)
                    .map(|f| f.ty.clone())
                    .unwrap_or(HirTy::Unknown),
                _ => HirTy::Unknown,
            };
            // For struct receivers fall back to a regular field-read so
            // codegen pulls the value out of the struct slot, not a
            // tuple slot. This keeps the existing struct field-read
            // path responsible for type/index lookup.
            if let HirTy::Struct(sid) = &target_h.ty {
                let sid = *sid;
                let span = expr.span;
                return HirExpr {
                    ty: field_ty.clone(),
                    span,
                    kind: HirExprKind::FieldRead {
                        target: Box::new(target_h),
                        struct_id: sid,
                        field_index: *index,
                        field_ty,
                    },
                };
            }
            HirExpr {
                ty: field_ty.clone(),
                span: expr.span,
                kind: HirExprKind::TupleField {
                    target: Box::new(target_h),
                    index: *index,
                    field_ty,
                },
            }
        }
        ExprKind::List(items) => {
            let lowered: Vec<HirExpr> = items.iter().map(|e| lower_expr(ctx, e)).collect();
            let elem_ty = lowered
                .first()
                .map(|e| e.ty.clone())
                .unwrap_or(HirTy::Unknown);
            let len = u32::try_from(lowered.len()).unwrap_or(0);
            HirExpr {
                ty: HirTy::Array(Box::new(elem_ty.clone()), len),
                span: expr.span,
                kind: HirExprKind::ArrayInit { elem_ty, elements: lowered },
            }
        }
        ExprKind::Index(arr, idx) => {
            let arr_h = lower_expr(ctx, arr);
            let idx_h = lower_expr(ctx, idx);
            let elem_ty = match &arr_h.ty {
                HirTy::Array(t, _) => (**t).clone(),
                _ => HirTy::Unknown,
            };
            HirExpr {
                ty: elem_ty.clone(),
                span: expr.span,
                kind: HirExprKind::ArrayIndex {
                    array: Box::new(arr_h),
                    index: Box::new(idx_h),
                    elem_ty,
                },
            }
        }
        ExprKind::Loop { label, body } => {
            let body_h = lower_block(ctx, body);
            // Pick the first `break <value>` we can see in the body —
            // proper unification across multiple break sites is type
            // checking's job, which lands later.
            let result_ty = first_break_value_ty(&body_h, label.as_deref())
                .unwrap_or(HirTy::Unit);
            HirExpr {
                kind: HirExprKind::Loop {
                    label: label.clone(),
                    body: Box::new(body_h),
                    result_ty: result_ty.clone(),
                },
                ty: result_ty,
                span: expr.span,
            }
        }
        ExprKind::Closure { captures, params, ret_ty, body, .. } => {
            // Spec 4.6.2: `[ref x]` capture-list. The parser preserves
            // captures, but HIR/MIR closure lowering currently models only
            // value capture (snapshot at creation). Refusing ref captures
            // explicitly avoids the silent miscompile where the user
            // expects mutation to flow back to the outer variable.
            if captures.iter().any(|c| matches!(c, rokc_ast::CaptureSpec::Ref(_))) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    "`[ref x]` capture is not yet implemented; closures currently \
                     only support value capture (spec 4.6.2)"
                        .to_owned(),
                );
            }
            lower_closure_expr(ctx, params, ret_ty.as_ref(), body, expr.span)
        }
        ExprKind::QuestionDot(receiver, tail) => {
            let recv_h = lower_expr(ctx, receiver);
            desugar_question_dot(ctx, recv_h, tail, expr.span)
        }
        ExprKind::TryQ(inner) => {
            let inner_h = lower_expr(ctx, inner);
            desugar_try_q(ctx, inner_h, expr.span)
        }
        ExprKind::NullishCoalesce(lhs, rhs) => {
            let lhs_h = lower_expr(ctx, lhs);
            let rhs_h = lower_expr(ctx, rhs);
            desugar_nullish_coalesce(ctx, lhs_h, rhs_h, expr.span)
        }
        ExprKind::Cast(operand, ty) => {
            let operand_h = lower_expr(ctx, operand);
            // Spec 2.10.5: monomorphized bodies need `as T` to substitute
            // the concrete type for the type-param, so the cast target
            // matches the function's substituted return type. Going
            // through `resolve_ast_ty` runs the `ty_subst` pass.
            let to_ty = ctx.resolve_ast_ty(ty);
            let from_ty = operand_h.ty.clone();
            HirExpr {
                kind: HirExprKind::Cast {
                    operand: Box::new(operand_h),
                    from_ty,
                    to_ty: to_ty.clone(),
                },
                ty: to_ty,
                span: expr.span,
            }
        }
        // Stage-1 await: drop straight through to the inner expression.
        // The async runtime (`rok_task_*`) is all nullptr stubs, so any
        // real suspend semantics would mis-compile silently. When the
        // scheduler lands, this arm becomes a real coroutine suspend
        // point.
        ExprKind::Await(inner) => lower_expr(ctx, inner),
        // Spec 4.11: generator `yield N`. Coroutine runtime is a nullptr
        // stub at stage-1, so refuse explicitly rather than miscompile.
        ExprKind::Yield(_) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "`yield` is not yet implemented; generator coroutines \
                 require a scheduler that doesn't exist in stage-1 \
                 (spec 4.11)"
                    .to_owned(),
            );
            HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Unknown,
                span: expr.span,
            }
        }
        _ => HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: HirTy::Unknown,
            span: expr.span,
        },
    }
}

/// Lift a closure into an anonymous top-level function and return a
/// closure value. Captures named outer locals by value (snapshot at
/// creation time). Non-capturing closures stay as plain function
/// pointers so existing `fn(...)` types keep working.
fn lower_closure_expr(
    ctx: &mut LowerCtx<'_>,
    params: &[Param],
    ret_ty: Option<&Ty>,
    body: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // Pre-walk the AST body to find names referenced but not bound
    // inside the closure. Filter to those that resolve to outer locals.
    let mut bound: std::collections::HashSet<String> =
        params.iter().map(|p| p.name.clone()).collect();
    let mut free_names: Vec<String> = Vec::new();
    closure_free_names_expr(body, &mut bound, &mut free_names);
    let captures: Vec<(String, LocalId, HirTy)> = free_names
        .into_iter()
        .filter_map(|name| {
            ctx.lookup(&name).map(|local| {
                let ty = ctx.local_ty(local);
                (name, local, ty)
            })
        })
        .collect();

    let closure_id = FunctionId(ctx.sink.next_id.get());
    ctx.sink.next_id.set(closure_id.0 + 1);

    let declared_ret_ty = ret_ty
        .map(|t| resolve_ty_with_structs(t, ctx.struct_table, ctx.enum_table));

    let mut cl_ctx = LowerCtx::new(
        ctx.fn_table,
        ctx.method_table,
        ctx.structs,
        ctx.enums,
        ctx.struct_table,
        ctx.enum_table,
        ctx.consts,
        ctx.type_aliases,
        ctx.ty_subst,
        ctx.generic_fns,
        None,
        ctx.prec,
        ctx.sink,
        ctx.item_visibility,
        ctx.uses,
        ctx.impl_traits,
        ctx.statics,
    );
    cl_ctx.current_module = ctx.current_module.clone();

    // Closures with captures take an extra `env` parameter (a tuple of
    // captured values). The env param is declared first so its LocalId
    // is stable; closure params follow.
    let env_ty = if captures.is_empty() {
        None
    } else {
        Some(HirTy::Tuple(captures.iter().map(|(_, _, t)| t.clone()).collect()))
    };
    let env_local: Option<LocalId> = env_ty.as_ref().map(|et| {
        cl_ctx.declare(Some("__env".to_owned()), et.clone())
    });

    let mut hir_params: Vec<HirParam> = Vec::with_capacity(params.len() + 1);
    if let (Some(et), Some(el)) = (env_ty.as_ref(), env_local) {
        hir_params.push(HirParam {
            name: "__env".to_owned(),
            local: el,
            ty: et.clone(),
            by_ref: false,
        });
    }

    // Each captured name becomes a local inside the body initialised
    // from the corresponding env tuple field.
    let mut prelude: Vec<HirStmt> = Vec::new();
    for (i, (cap_name, _, cap_ty)) in captures.iter().enumerate() {
        let inner_local = cl_ctx.declare(Some(cap_name.clone()), cap_ty.clone());
        let env_local_v = env_local.expect("env local present when captures non-empty");
        let env_ty_v = env_ty.as_ref().expect("env type").clone();
        let env_expr = HirExpr {
            kind: HirExprKind::Local(env_local_v),
            ty: env_ty_v,
            span,
        };
        let field_expr = HirExpr {
            kind: HirExprKind::TupleField {
                target: Box::new(env_expr),
                index: u32::try_from(i).expect("capture index overflow"),
                field_ty: cap_ty.clone(),
            },
            ty: cap_ty.clone(),
            span,
        };
        prelude.push(HirStmt::Let {
            local: inner_local,
            init: field_expr,
        });
    }

    // Spec 4.5/4.8: when a closure appears in a context that expects a
    // function type (e.g. as an argument to a `fn(i32) -> i32`-typed
    // parameter), unannotated closure params pick up types from the
    // expected fn signature.
    let (expected_param_tys, _expected_ret_ty): (Option<Vec<HirTy>>, Option<HirTy>) =
        match ctx.current_expected() {
            Some(HirTy::Fn(args, ret)) => (Some(args.clone()), Some((**ret).clone())),
            _ => (None, None),
        };

    for (pi, p) in params.iter().enumerate() {
        let ty = match &p.ty {
            Some(t) => resolve_ty_with_structs(t, cl_ctx.struct_table, cl_ctx.enum_table),
            None => expected_param_tys
                .as_ref()
                .and_then(|v| v.get(pi).cloned())
                .unwrap_or(HirTy::Unknown),
        };
        let local = cl_ctx.declare(Some(p.name.clone()), ty.clone());
        hir_params.push(HirParam {
            name: p.name.clone(),
            local,
            ty,
            by_ref: p.by_ref,
        });
    }

    let body_h = lower_expr(&mut cl_ctx, body);
    let inferred_ret_ty = body_h.ty.clone();
    let final_ret_ty = declared_ret_ty.unwrap_or(inferred_ret_ty);

    let body_block = HirBlock {
        stmts: prelude,
        trailing: Some(body_h),
        label: None,
    };

    // The lifted function's signature includes the env param; the
    // closure-typed value's apparent signature does not (it surfaces
    // only the user-declared params). Untyped params take their type
    // from the expected `Fn(args, ret)` slot when available — same
    // propagation as the `hir_params` loop above.
    let user_arg_tys: Vec<HirTy> = params
        .iter()
        .enumerate()
        .map(|(pi, p)| match &p.ty {
            Some(t) => resolve_ty_with_structs(t, ctx.struct_table, ctx.enum_table),
            None => expected_param_tys
                .as_ref()
                .and_then(|v| v.get(pi).cloned())
                .unwrap_or(HirTy::Unknown),
        })
        .collect();

    let cl_fn = HirFunction {
        id: closure_id,
        def_id: None,
        name: format!("__closure_{}", closure_id.0),
        params: hir_params,
        locals: cl_ctx.into_locals(),
        ret_ty: final_ret_ty.clone(),
        body: Some(body_block),
        is_async: false,
        is_generator: false,
        span,
    };

    ctx.sink.extras.borrow_mut().push(cl_fn);

    if captures.is_empty() {
        let fn_ty = HirTy::Fn(user_arg_tys, Box::new(final_ret_ty));
        return HirExpr {
            kind: HirExprKind::FnRef(closure_id),
            ty: fn_ty,
            span,
        };
    }

    // Materialize the env value at the creation site: a tuple of the
    // current outer locals' values, snapshotted by-value.
    let env_ty_v = env_ty.expect("env type present when captures non-empty");
    let env_fields: Vec<HirExpr> = captures
        .iter()
        .map(|(_, outer_local, ty)| HirExpr {
            kind: HirExprKind::Local(*outer_local),
            ty: ty.clone(),
            span,
        })
        .collect();
    let env_value = HirExpr {
        kind: HirExprKind::Tuple { fields: env_fields },
        ty: env_ty_v.clone(),
        span,
    };

    let closure_ty = HirTy::Closure {
        args: user_arg_tys.clone(),
        ret: Box::new(final_ret_ty.clone()),
        env: Box::new(env_ty_v.clone()),
    };
    HirExpr {
        kind: HirExprKind::ClosureValue {
            fn_id: closure_id,
            env: Box::new(env_value),
            arg_tys: user_arg_tys,
            ret_ty: final_ret_ty,
            env_ty: env_ty_v,
        },
        ty: closure_ty,
        span,
    }
}

/// Desugar `x?.tail` to `match x { v: T => v.tail, none => none }`. The
/// scrutinee must be `T | none` for some primitive variant `T`; result
/// type is `tail_ty | none`.
fn desugar_question_dot(
    ctx: &mut LowerCtx<'_>,
    recv: HirExpr,
    tail: &rokc_ast::AccessTail,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let HirTy::Sum(variants) = recv.ty.clone() else {
        // Non-optional receiver — fall back to a regular access.
        return apply_access_tail(ctx, recv, tail, span);
    };
    let none_idx = variants
        .iter()
        .position(|v| matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]));
    let Some(none_idx) = none_idx else {
        return apply_access_tail(ctx, recv, tail, span);
    };
    // Pick the first non-none variant — this slice's sum types only
    // carry one payload variant alongside `none`.
    let some_idx = variants
        .iter()
        .position(|v| !matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]));
    let Some(some_idx) = some_idx else {
        return recv;
    };
    let payload_ty = variants[some_idx].clone();

    // `v: T` arm — bind the unwrapped value, then apply the tail.
    let bind_local = ctx.declare(None, payload_ty.clone());
    let unwrapped = HirExpr {
        kind: HirExprKind::Local(bind_local),
        ty: payload_ty.clone(),
        span,
    };
    let inner = apply_access_tail(ctx, unwrapped, tail, span);
    let inner_ty = inner.ty.clone();

    // Result is `inner_ty | none`. When the tail itself returned an
    // optional (e.g. `o?.inner` where `inner: Inner | none`), keep that
    // type — wrapping it into yet another `Sum<Sum, none>` confuses the
    // sum-payload codegen and leaves a Unit fall-through at the merge.
    // Spec 3.8.2: `?.` chains compose monadically.
    let inner_already_optional = matches!(
        &inner_ty,
        HirTy::Sum(parts) if parts.iter().any(
            |v| matches!(v, HirTy::Path(p) if p.as_slice() == ["none"])
        )
    );
    let result_ty = if inner_already_optional {
        inner_ty.clone()
    } else {
        HirTy::Sum(vec![
            inner_ty.clone(),
            HirTy::Path(vec!["none".to_owned()]),
        ])
    };
    let some_body = if inner_already_optional {
        // Tail value is already shaped like `result_ty`; pass through.
        inner
    } else {
        wrap_into_sum(&result_ty, inner)
    };
    // Locate the `none` variant within `result_ty` for the none-arm wrap.
    let none_variant_idx = if let HirTy::Sum(parts) = &result_ty {
        parts
            .iter()
            .position(|v| matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]))
            .unwrap_or(0)
    } else {
        0
    };
    let none_body = HirExpr {
        kind: HirExprKind::SumWrap {
            sum_ty: result_ty.clone(),
            variant_index: u32::try_from(none_variant_idx).expect("variant overflow"),
            value: None,
        },
        ty: result_ty.clone(),
        span,
    };

    let some_pat = HirPattern::SumVariant {
        sum_ty: recv.ty.clone(),
        variant_index: u32::try_from(some_idx).expect("variant overflow"),
        binder: Some(bind_local),
        payload_ty: Some(payload_ty),
    };
    let none_pat = HirPattern::SumVariant {
        sum_ty: recv.ty.clone(),
        variant_index: u32::try_from(none_idx).expect("variant overflow"),
        binder: None,
        payload_ty: None,
    };

    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(recv),
            arms: vec![
                HirMatchArm {
                    pat: some_pat,
                    guard: None,
                    body: some_body,
                },
                HirMatchArm {
                    pat: none_pat,
                    guard: None,
                    body: none_body,
                },
            ],
        },
        ty: result_ty,
        span,
    }
}

/// Apply an `AccessTail` to an already-lowered HIR receiver. Supports
/// the same forms `?.` does: field, tuple field, and method call.
fn apply_access_tail(
    ctx: &mut LowerCtx<'_>,
    recv: HirExpr,
    tail: &rokc_ast::AccessTail,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    match tail {
        rokc_ast::AccessTail::Field(name) => {
            // Inline the field-access lowering. Only struct receivers
            // are supported in this slice.
            let HirTy::Struct(sid) = recv.ty.clone() else {
                return HirExpr {
                    kind: HirExprKind::Const(ConstVal::Unit),
                    ty: HirTy::Unknown,
                    span,
                };
            };
            let def = &ctx.structs[sid.0 as usize];
            let Some(idx) = def.fields.iter().position(|f| &f.name == name) else {
                return HirExpr {
                    kind: HirExprKind::Const(ConstVal::Unit),
                    ty: HirTy::Unknown,
                    span,
                };
            };
            let field_ty = def.fields[idx].ty.clone();
            HirExpr {
                kind: HirExprKind::FieldRead {
                    target: Box::new(recv),
                    struct_id: sid,
                    field_index: u32::try_from(idx).expect("field overflow"),
                    field_ty: field_ty.clone(),
                },
                ty: field_ty,
                span,
            }
        }
        rokc_ast::AccessTail::TupleField(idx) => {
            let HirTy::Tuple(parts) = recv.ty.clone() else {
                return HirExpr {
                    kind: HirExprKind::Const(ConstVal::Unit),
                    ty: HirTy::Unknown,
                    span,
                };
            };
            let field_ty = parts.get(*idx as usize).cloned().unwrap_or(HirTy::Unknown);
            HirExpr {
                kind: HirExprKind::TupleField {
                    target: Box::new(recv),
                    index: *idx,
                    field_ty: field_ty.clone(),
                },
                ty: field_ty,
                span,
            }
        }
        rokc_ast::AccessTail::Method { method, args, .. } => {
            // Reuse the regular method-call lowering with the unwrapped
            // receiver as `self`. We synthesize an AST `Path(this)` expr
            // pointing at the bound local — but lower_method_call takes
            // an AST `Expr` for the receiver, so wrap accordingly.
            let HirExprKind::Local(local_id) = recv.kind else {
                return HirExpr {
                    kind: HirExprKind::Const(ConstVal::Unit),
                    ty: HirTy::Unknown,
                    span,
                };
            };
            // Look up the method directly in method_table for the
            // receiver's type, then materialize a Call.
            let Some(target) = method_target_for(&recv.ty) else {
                return HirExpr {
                    kind: HirExprKind::Const(ConstVal::Unit),
                    ty: HirTy::Unknown,
                    span,
                };
            };
            let Some(&fn_id) = ctx.method_table.get(&(target, method.clone())) else {
                return HirExpr {
                    kind: HirExprKind::Const(ConstVal::Unit),
                    ty: HirTy::Unknown,
                    span,
                };
            };
            let mangled = format!("{}__{}", ty_mangle(&recv.ty), method);
            let ret_ty = ctx
                .fn_table
                .get(&mangled)
                .map(|s| s.ret_ty.clone())
                .unwrap_or(HirTy::Unknown);
            let mut lowered: Vec<HirExpr> = Vec::with_capacity(args.len() + 1);
            lowered.push(HirExpr {
                kind: HirExprKind::Local(local_id),
                ty: recv.ty.clone(),
                span,
            });
            for a in args {
                if let rokc_ast::CallArg::Positional(e) = a {
                    lowered.push(lower_expr(ctx, e));
                }
            }
            HirExpr {
                kind: HirExprKind::Call { callee: fn_id, args: lowered },
                ty: ret_ty,
                span,
            }
        }
        rokc_ast::AccessTail::Index(_) => {
            let _ = ctx;
            HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Unknown,
                span,
            }
        }
    }
}

/// Desugar `expr?` to `match expr { v: T => v, none => return none }`.
/// The enclosing function must return a `T | none`-shaped sum so the
/// none-arm's `return none` is well-typed.
fn desugar_try_q(
    ctx: &mut LowerCtx<'_>,
    inner: HirExpr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let HirTy::Sum(variants) = inner.ty.clone() else {
        return inner;
    };
    let none_idx = variants
        .iter()
        .position(|v| matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]));
    let some_idx = variants
        .iter()
        .position(|v| !matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]));
    let (Some(none_idx), Some(some_idx)) = (none_idx, some_idx) else {
        return inner;
    };
    let payload_ty = variants[some_idx].clone();
    let bind_local = ctx.declare(None, payload_ty.clone());

    // Some-arm: yield the unwrapped value.
    let some_body = HirExpr {
        kind: HirExprKind::Local(bind_local),
        ty: payload_ty.clone(),
        span,
    };
    let some_pat = HirPattern::SumVariant {
        sum_ty: inner.ty.clone(),
        variant_index: u32::try_from(some_idx).expect("variant overflow"),
        binder: Some(bind_local),
        payload_ty: Some(payload_ty.clone()),
    };

    // None-arm: `return none` wrapped into the enclosing fn's return
    // type. lower_block sees the wrap_into_sum because we're inside a
    // `Return` HIR stmt — but for an expression-position arm body we
    // build the wrapped none manually here.
    let ret_sum = ctx.fn_ret_ty.clone();
    let none_value = if let HirTy::Sum(ret_variants) = &ret_sum {
        let ret_none_idx = ret_variants
            .iter()
            .position(|v| matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]))
            .unwrap_or(0);
        HirExpr {
            kind: HirExprKind::SumWrap {
                sum_ty: ret_sum.clone(),
                variant_index: u32::try_from(ret_none_idx).expect("variant overflow"),
                value: None,
            },
            ty: ret_sum.clone(),
            span,
        }
    } else {
        HirExpr {
            kind: HirExprKind::Const(ConstVal::None),
            ty: HirTy::Path(vec!["none".to_owned()]),
            span,
        }
    };
    let none_block = HirBlock {
        stmts: vec![HirStmt::Return(Some(none_value))],
        trailing: None,
        label: None,
    };
    let none_body = HirExpr {
        kind: HirExprKind::Block(Box::new(none_block)),
        ty: payload_ty.clone(),
        span,
    };
    let none_pat = HirPattern::SumVariant {
        sum_ty: inner.ty.clone(),
        variant_index: u32::try_from(none_idx).expect("variant overflow"),
        binder: None,
        payload_ty: None,
    };

    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(inner),
            arms: vec![
                HirMatchArm {
                    pat: some_pat,
                    guard: None,
                    body: some_body,
                },
                HirMatchArm {
                    pat: none_pat,
                    guard: None,
                    body: none_body,
                },
            ],
        },
        ty: payload_ty,
        span,
    }
}

/// Desugar `lhs ?? rhs` to `match lhs { v: T => v, none => rhs }`.
fn desugar_nullish_coalesce(
    ctx: &mut LowerCtx<'_>,
    lhs: HirExpr,
    rhs: HirExpr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let HirTy::Sum(variants) = lhs.ty.clone() else {
        return lhs;
    };
    let none_idx = variants
        .iter()
        .position(|v| matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]));
    let some_idx = variants
        .iter()
        .position(|v| !matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]));
    let (Some(none_idx), Some(some_idx)) = (none_idx, some_idx) else {
        return lhs;
    };
    let payload_ty = variants[some_idx].clone();
    let result_ty = rhs.ty.clone();

    let bind_local = ctx.declare(None, payload_ty.clone());
    let some_body = HirExpr {
        kind: HirExprKind::Local(bind_local),
        ty: payload_ty.clone(),
        span,
    };

    let some_pat = HirPattern::SumVariant {
        sum_ty: lhs.ty.clone(),
        variant_index: u32::try_from(some_idx).expect("variant overflow"),
        binder: Some(bind_local),
        payload_ty: Some(payload_ty),
    };
    let none_pat = HirPattern::SumVariant {
        sum_ty: lhs.ty.clone(),
        variant_index: u32::try_from(none_idx).expect("variant overflow"),
        binder: None,
        payload_ty: None,
    };

    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(lhs),
            arms: vec![
                HirMatchArm {
                    pat: some_pat,
                    guard: None,
                    body: some_body,
                },
                HirMatchArm {
                    pat: none_pat,
                    guard: None,
                    body: rhs,
                },
            ],
        },
        ty: result_ty,
        span,
    }
}

/// Walk an AST expression collecting all simple-path names that are
/// referenced but not bound within the walked tree. `bound` carries the
/// in-scope names; it is mutated as we enter and leave nested scopes.
/// The collector is best-effort: only the expression forms used in
/// closure bodies in the current test surface are covered.
fn closure_free_names_expr(
    expr: &Expr,
    bound: &mut std::collections::HashSet<String>,
    out: &mut Vec<String>,
) {
    use rokc_ast::CallArg as Arg;
    match &expr.kind {
        ExprKind::Path(p) if p.segments.len() == 1 => {
            let name = &p.segments[0].name;
            if !bound.contains(name) && !out.contains(name) {
                out.push(name.clone());
            }
        }
        ExprKind::Path(_) | ExprKind::Literal(_) | ExprKind::SelfLower
        | ExprKind::SelfUpper => {}
        ExprKind::Block(b) => {
            let saved = bound.clone();
            for s in &b.stmts {
                closure_free_names_stmt(s, bound, out);
            }
            if let Some(t) = &b.trailing {
                closure_free_names_expr(t, bound, out);
            }
            *bound = saved;
        }
        ExprKind::OpInfix { lhs, rhs, .. } => {
            closure_free_names_expr(lhs, bound, out);
            closure_free_names_expr(rhs, bound, out);
        }
        ExprKind::OpPrefix { operand, .. } | ExprKind::OpPostfix { operand, .. } => {
            closure_free_names_expr(operand, bound, out);
        }
        ExprKind::Call { callee, args, .. } => {
            closure_free_names_expr(callee, bound, out);
            for a in args {
                if let Arg::Positional(e) = a {
                    closure_free_names_expr(e, bound, out);
                }
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            closure_free_names_expr(receiver, bound, out);
            for a in args {
                if let Arg::Positional(e) = a {
                    closure_free_names_expr(e, bound, out);
                }
            }
        }
        ExprKind::If { cond, then_branch, else_branch } => {
            closure_free_names_expr(cond, bound, out);
            let saved = bound.clone();
            for s in &then_branch.stmts {
                closure_free_names_stmt(s, bound, out);
            }
            if let Some(t) = &then_branch.trailing {
                closure_free_names_expr(t, bound, out);
            }
            *bound = saved;
            if let Some(e) = else_branch {
                closure_free_names_expr(e, bound, out);
            }
        }
        ExprKind::While { cond, body, .. } => {
            closure_free_names_expr(cond, bound, out);
            let saved = bound.clone();
            for s in &body.stmts {
                closure_free_names_stmt(s, bound, out);
            }
            if let Some(t) = &body.trailing {
                closure_free_names_expr(t, bound, out);
            }
            *bound = saved;
        }
        ExprKind::Loop { body, .. } => {
            let saved = bound.clone();
            for s in &body.stmts {
                closure_free_names_stmt(s, bound, out);
            }
            if let Some(t) = &body.trailing {
                closure_free_names_expr(t, bound, out);
            }
            *bound = saved;
        }
        ExprKind::Match { scrutinee, arms } => {
            closure_free_names_expr(scrutinee, bound, out);
            for arm in arms {
                let saved = bound.clone();
                pattern_bound_names(&arm.pat, bound);
                if let Some(g) = &arm.guard {
                    closure_free_names_expr(g, bound, out);
                }
                closure_free_names_expr(&arm.body, bound, out);
                *bound = saved;
            }
        }
        ExprKind::Tuple(items) | ExprKind::List(items) => {
            for e in items {
                closure_free_names_expr(e, bound, out);
            }
        }
        ExprKind::TupleField(t, _) | ExprKind::Field(t, _) => {
            closure_free_names_expr(t, bound, out);
        }
        ExprKind::Index(arr, idx) => {
            closure_free_names_expr(arr, bound, out);
            closure_free_names_expr(idx, bound, out);
        }
        ExprKind::StructInit { fields, spread, .. } => {
            for (_, e) in fields {
                closure_free_names_expr(e, bound, out);
            }
            if let Some(s) = spread {
                closure_free_names_expr(s, bound, out);
            }
        }
        ExprKind::Cast(e, _) => {
            closure_free_names_expr(e, bound, out);
        }
        ExprKind::Closure { params: nested_params, body: nested_body, .. } => {
            // Names bound by the nested closure shouldn't leak into our
            // free-name list; nested captures of *our* outer locals do.
            let saved = bound.clone();
            for p in nested_params {
                bound.insert(p.name.clone());
            }
            closure_free_names_expr(nested_body, bound, out);
            *bound = saved;
        }
        _ => {}
    }
}

fn closure_free_names_stmt(
    s: &Stmt,
    bound: &mut std::collections::HashSet<String>,
    out: &mut Vec<String>,
) {
    match &s.kind {
        StmtKind::Let { name, init, .. } => {
            closure_free_names_expr(init, bound, out);
            bound.insert(name.clone());
        }
        StmtKind::LetTuple { names, init, .. } => {
            closure_free_names_expr(init, bound, out);
            for n in names {
                if n != "_" {
                    bound.insert(n.clone());
                }
            }
        }
        StmtKind::LetStruct { fields, init, .. } => {
            closure_free_names_expr(init, bound, out);
            for (_, bind) in fields {
                bound.insert(bind.clone());
            }
        }
        StmtKind::Assign(target, value) => {
            closure_free_names_expr(target, bound, out);
            closure_free_names_expr(value, bound, out);
        }
        StmtKind::CompoundAssign { target, value, .. } => {
            closure_free_names_expr(target, bound, out);
            closure_free_names_expr(value, bound, out);
        }
        StmtKind::Expr(e) | StmtKind::Trailing(e) => {
            closure_free_names_expr(e, bound, out);
        }
        StmtKind::Return(e) => {
            if let Some(e) = e {
                closure_free_names_expr(e, bound, out);
            }
        }
        _ => {}
    }
}

fn pattern_bound_names(pat: &AstPattern, bound: &mut std::collections::HashSet<String>) {
    match &pat.kind {
        AstPatternKind::Binding { name, sub } => {
            bound.insert(name.clone());
            if let Some(s) = sub {
                pattern_bound_names(s, bound);
            }
        }
        AstPatternKind::Tuple(parts) => {
            for p in parts {
                pattern_bound_names(p, bound);
            }
        }
        AstPatternKind::Struct { fields, .. } => {
            for fp in fields {
                if let Some(p) = &fp.pat {
                    pattern_bound_names(p, bound);
                } else {
                    bound.insert(fp.name.clone());
                }
            }
        }
        AstPatternKind::EnumVariant { args, .. } => {
            for a in args {
                pattern_bound_names(a, bound);
            }
        }
        AstPatternKind::Or(alts) => {
            if let Some(first) = alts.first() {
                pattern_bound_names(first, bound);
            }
        }
        AstPatternKind::TypeCheck { binder: Some(name), .. } => {
            bound.insert(name.clone());
        }
        _ => {}
    }
}

/// Walk one loop's body looking for the first `break value;` whose
/// label targets this loop. Skips nested loops (they own their breaks).
fn first_break_value_ty(b: &HirBlock, label: Option<&str>) -> Option<HirTy> {
    fn walk_block(b: &HirBlock, label: Option<&str>) -> Option<HirTy> {
        for s in &b.stmts {
            if let Some(t) = walk_stmt(s, label) {
                return Some(t);
            }
        }
        b.trailing.as_ref().and_then(|t| walk_expr(t, label))
    }

    fn walk_stmt(s: &HirStmt, label: Option<&str>) -> Option<HirTy> {
        match s {
            HirStmt::Break { label: bl, value } => {
                // Exact match: an unlabeled break belongs only to an
                // unlabeled outer; `break 'L` belongs only to the loop
                // labeled `'L`.
                if bl.as_deref() == label {
                    value.as_ref().map(|v| v.ty.clone())
                } else {
                    None
                }
            }
            HirStmt::Let { init, .. } => walk_expr(init, label),
            HirStmt::Assign { value, .. } => walk_expr(value, label),
            HirStmt::Expr(e) | HirStmt::Return(Some(e)) => walk_expr(e, label),
            _ => None,
        }
    }

    fn walk_expr(e: &HirExpr, label: Option<&str>) -> Option<HirTy> {
        match &e.kind {
            HirExprKind::Block(b) => walk_block(b, label),
            HirExprKind::If { cond, then_block, else_branch } => {
                walk_expr(cond, label)
                    .or_else(|| walk_block(then_block, label))
                    .or_else(|| else_branch.as_deref().and_then(|e| walk_expr(e, label)))
            }
            HirExprKind::PrimBinOp { lhs, rhs, .. } => {
                walk_expr(lhs, label).or_else(|| walk_expr(rhs, label))
            }
            HirExprKind::PrimUnaryOp { operand, .. } => walk_expr(operand, label),
            HirExprKind::Call { args, .. } => args.iter().find_map(|a| walk_expr(a, label)),
            // For an unlabeled outer, nested loops own all their breaks —
            // skip. For a labeled outer, recurse so a `break 'outer …`
            // inside a nested loop is reachable, but stop at any inner
            // loop that shadows the label.
            HirExprKind::While { label: inner, body, .. } => {
                if label.is_some() && inner.as_deref() != label {
                    walk_block(body, label)
                } else {
                    None
                }
            }
            HirExprKind::Loop { label: inner, body, .. } => {
                if label.is_some() && inner.as_deref() != label {
                    walk_block(body, label)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    walk_block(b, label)
}

// `Foo { field: value, ... }` — fields are placed in declaration order;
// missing slots get a unit placeholder pending type checking.
fn lower_struct_init(
    ctx: &mut LowerCtx<'_>,
    path: &AstPath,
    fields: &[(String, Expr)],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // `EnumName::Variant { x: ..., y: ... }` — enum named-form variant
    // initialiser (spec 2.4). Pack fields into the variant's tuple
    // payload according to declaration order.
    if path.segments.len() == 2 {
        if let Some(&enum_id) = ctx.enum_table.get(&path.segments[0].name) {
            let def = &ctx.enums[enum_id.0 as usize];
            if let Some((idx, variant)) = def
                .variants
                .iter()
                .enumerate()
                .find(|(_, v)| v.name == path.segments[1].name)
            {
                if !variant.named_fields.is_empty() {
                    let field_names = variant.named_fields.clone();
                    let field_tys: Vec<HirTy> = match &variant.payload_ty {
                        Some(HirTy::Tuple(parts)) => parts.clone(),
                        _ => Vec::new(),
                    };
                    let mut by_name: HashMap<String, Expr> =
                        fields.iter().map(|(n, e)| (n.clone(), e.clone())).collect();
                    let mut payload_args: Vec<HirExpr> = Vec::with_capacity(field_names.len());
                    for (i, fname) in field_names.iter().enumerate() {
                        match by_name.remove(fname) {
                            Some(e) => {
                                let lowered = lower_expr(ctx, &e);
                                let target_ty = field_tys
                                    .get(i)
                                    .cloned()
                                    .unwrap_or_else(|| lowered.ty.clone());
                                payload_args.push(wrap_into_sum(&target_ty, lowered));
                            }
                            None => {
                                ctx.emit_error(
                                    rokc_diagnostic::ErrorKind::Type,
                                    format!(
                                        "enum variant `{}::{}` is missing field \
                                         `{fname}` (spec 2.4)",
                                        path.segments[0].name, path.segments[1].name
                                    ),
                                );
                                payload_args.push(HirExpr {
                                    kind: HirExprKind::Const(ConstVal::Unit),
                                    ty: field_tys.get(i).cloned().unwrap_or(HirTy::Unknown),
                                    span,
                                });
                            }
                        }
                    }
                    if !by_name.is_empty() {
                        let extra: Vec<&String> = by_name.keys().collect();
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "enum variant `{}::{}` has unknown field(s) {extra:?} \
                                 (spec 2.4)",
                                path.segments[0].name, path.segments[1].name
                            ),
                        );
                    }
                    return HirExpr {
                        kind: HirExprKind::EnumVariantInit {
                            enum_id,
                            variant_index: u32::try_from(idx).expect("variant overflow"),
                            args: payload_args,
                        },
                        ty: HirTy::Enum(enum_id),
                        span,
                    };
                }
            }
        }
    }
    // Look up exact match first; fall back to a generic-instantiation
    // search keyed on the lowered field-value types.
    let bare_name = path.segments.last().map(|s| s.name.clone()).unwrap_or_default();
    let direct = ctx.struct_table.get(&bare_name).copied();
    let struct_id = if let Some(id) = direct {
        id
    } else {
        // Pre-lower the field values to discover their concrete types,
        // then assemble the mangled name `Pair__i32` and retry.
        let mut field_types: HashMap<String, HirTy> = HashMap::new();
        for (n, v) in fields {
            let lowered = lower_expr(ctx, v);
            field_types.insert(n.clone(), lowered.ty);
        }
        let prefix = format!("{bare_name}__");
        let candidate = ctx
            .struct_table
            .keys()
            .filter(|k| k.starts_with(&prefix))
            .find_map(|name| {
                let id = ctx.struct_table.get(name).copied()?;
                let def = &ctx.structs[id.0 as usize];
                let all_match = def.fields.iter().all(|f| {
                    let Some(ft) = field_types.get(&f.name) else {
                        return false;
                    };
                    if ft == &f.ty {
                        return true;
                    }
                    // Sum-typed field: any non-none variant matches.
                    if let HirTy::Sum(variants) = &f.ty {
                        return variants.iter().any(|v| v == ft)
                            || matches!(ft, HirTy::Path(p) if p.as_slice() == ["none"]);
                    }
                    false
                });
                if all_match { Some(id) } else { None }
            });
        let Some(id) = candidate else {
            return HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Unknown,
                span,
            };
        };
        id
    };
    let def = &ctx.structs[struct_id.0 as usize];
    // Spec 2.x / i-want 322: `union { ... }` initialiser. Exactly one
    // declared field gets its value cast/bitcast into the synthetic
    // `__data` storage slot.
    if let Some(union_kind) = def.union_kind.clone() {
        if fields.len() != 1 {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "union `{}` initialiser must list exactly one field \
                     (spec 2.x — got {})",
                    def.name,
                    fields.len()
                ),
            );
            return HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Struct(struct_id),
                span,
            };
        }
        let (fname, value) = &fields[0];
        let alias_ty = union_kind
            .aliases
            .iter()
            .find(|(n, _)| n == fname)
            .map(|(_, t)| t.clone());
        let Some(field_ty) = alias_ty else {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "union `{}` has no field `{fname}` (spec 2.x)",
                    def.name
                ),
            );
            return HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Struct(struct_id),
                span,
            };
        };
        // Lower with the field's declared type as expected hint so
        // bare literals (`5` → `i32` for `fd: i32`) pick the right type.
        ctx.push_expected(field_ty.clone());
        let lowered = lower_expr(ctx, value);
        ctx.pop_expected();
        let storage_ty = def.fields[0].ty.clone();
        let casted = HirExpr {
            kind: HirExprKind::UnionWrite {
                struct_id,
                from_ty: lowered.ty.clone(),
                storage_ty: storage_ty.clone(),
                value: Box::new(lowered),
            },
            ty: storage_ty,
            span,
        };
        return HirExpr {
            kind: HirExprKind::StructInit {
                struct_id,
                fields: vec![casted],
            },
            ty: HirTy::Struct(struct_id),
            span,
        };
    }
    // Mark which fields the user explicitly provided so we can apply
    // defaults (or emit a "missing field" diagnostic) for the rest.
    let provided: std::collections::HashSet<&str> =
        fields.iter().map(|(n, _)| n.as_str()).collect();
    // Pre-clone field metadata so we don't borrow ctx.structs across
    // the lowering loop (which needs &mut ctx).
    let field_metas: Vec<(String, HirTy, Option<Expr>)> = def
        .fields
        .iter()
        .map(|f| (f.name.clone(), f.ty.clone(), f.default.clone()))
        .collect();
    let def_name = def.name.clone();
    let mut ordered: Vec<HirExpr> = field_metas
        .iter()
        .map(|(_, ty, _)| HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: ty.clone(),
            span,
        })
        .collect();
    for (name, value) in fields {
        let lowered = lower_expr(ctx, value);
        if let Some(idx) = field_metas.iter().position(|(fname, _, _)| fname == name) {
            let target_ty = field_metas[idx].1.clone();
            // Wrap a primitive value into a sum-typed field so e.g.
            // `Slot { value: 8 }` materialises the (tag, payload) shape.
            let wrapped = wrap_into_sum(&target_ty, lowered);
            ordered[idx] = wrapped;
        }
    }
    // Spec 2.x / i-want 942-950: missing fields fall back to their
    // declared default expression. No default → explicit "missing
    // field" error so the user doesn't get a silent unit fall-through
    // (probe `204_6_default_field_missing` covers the diagnostic path).
    for (idx, (fname, ty, default)) in field_metas.iter().enumerate() {
        if provided.contains(fname.as_str()) {
            continue;
        }
        match default {
            Some(default_expr) => {
                let lowered = lower_expr(ctx, default_expr);
                ordered[idx] = wrap_into_sum(ty, lowered);
            }
            None => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "struct `{def_name}` is missing field `{fname}` and \
                         no default is declared (spec 2.x / i-want 942-950)"
                    ),
                );
            }
        }
    }
    HirExpr {
        kind: HirExprKind::StructInit { struct_id, fields: ordered },
        ty: HirTy::Struct(struct_id),
        span,
    }
}

// `expr.field` on a struct.
fn lower_field(
    ctx: &mut LowerCtx<'_>,
    target: &Expr,
    name: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let target_h = lower_expr(ctx, target);
    let Some(struct_id) = (match &target_h.ty {
        HirTy::Struct(id) => Some(*id),
        _ => None,
    }) else {
        return HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: HirTy::Unknown,
            span,
        };
    };
    let def = &ctx.structs[struct_id.0 as usize];
    // Spec 2.x / i-want 322: union field read goes through `UnionRead`
    // so MIR/codegen can issue the right cast/bitcast against the
    // single `__data` storage slot.
    if let Some(union_kind) = def.union_kind.clone() {
        let storage_ty = def.fields[0].ty.clone();
        let Some(field_ty) = union_kind
            .aliases
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, t)| t.clone())
        else {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "union `{}` has no field `{name}` (spec 2.x)",
                    def.name
                ),
            );
            return HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Unknown,
                span,
            };
        };
        return HirExpr {
            kind: HirExprKind::UnionRead {
                struct_id,
                target: Box::new(target_h),
                field_name: name.to_owned(),
                storage_ty,
                field_ty: field_ty.clone(),
            },
            ty: field_ty,
            span,
        };
    }
    let Some(idx) = def.fields.iter().position(|f| f.name == name) else {
        return HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: HirTy::Unknown,
            span,
        };
    };
    let field_ty = def.fields[idx].ty.clone();
    HirExpr {
        kind: HirExprKind::FieldRead {
            target: Box::new(target_h),
            struct_id,
            field_index: u32::try_from(idx).expect("field index overflow"),
            field_ty: field_ty.clone(),
        },
        ty: field_ty,
        span,
    }
}

// `for name in start..end { body }` → counter local + while loop.
// Returns `None` for forms not yet supported (non-range iter, complex
// pattern, etc.) so the caller can fall through to the placeholder.
//
// `label` is the source `'outer:` annotation on the `for`; we forward it
// to the synthesized `While` so `break 'outer` / `continue 'outer` inside
// the body resolve correctly. Without this the labelled break would jump
// to no matching frame and the lowered code would crash at runtime
// (probe `313_4_label_break_outer`, exit 133 SIGTRAP).
fn lower_for_range(
    ctx: &mut LowerCtx<'_>,
    label: &Option<String>,
    pat: &AstPattern,
    iter: &Expr,
    body: &Block,
    span: rokc_diagnostic::Span,
) -> Option<Vec<HirStmt>> {
    let ExprKind::Range { start: Some(start_e), end: Some(end_e), inclusive } = &iter.kind else {
        return None;
    };
    let AstPatternKind::Binding { name, sub: None } = &pat.kind else {
        return None;
    };

    let start_h = lower_expr(ctx, start_e);
    let end_h = lower_expr(ctx, end_e);
    let elem_ty = start_h.ty.clone();
    let HirTy::Prim(prim) = elem_ty.clone() else { return None };
    if !prim.is_int() {
        return None;
    }

    let counter = ctx.declare(None, elem_ty.clone());
    let mut out = Vec::new();
    out.push(HirStmt::Let { local: counter, init: start_h });

    // Build `__c < end` (or `<=` for inclusive).
    let cmp_op = if *inclusive { PrimOp::Le } else { PrimOp::Lt };
    let cond = HirExpr {
        ty: HirTy::Prim(PrimTy::Bool),
        span,
        kind: HirExprKind::PrimBinOp {
            op: cmp_op,
            lhs: Box::new(HirExpr {
                ty: elem_ty.clone(),
                span,
                kind: HirExprKind::Local(counter),
            }),
            rhs: Box::new(end_h),
        },
    };

    // The user body — wrapped in a fresh scope so `name` and the
    // increment are local to each iteration.
    ctx.push_scope();
    let user_local = ctx.declare(Some(name.clone()), elem_ty.clone());
    let mut body_stmts: Vec<HirStmt> = Vec::new();
    // Snapshot then increment first so `continue` in the body jumps to
    // the cond check without skipping the increment.
    let snap = ctx.declare(None, elem_ty.clone());
    body_stmts.push(HirStmt::Let {
        local: snap,
        init: HirExpr {
            ty: elem_ty.clone(),
            span,
            kind: HirExprKind::Local(counter),
        },
    });
    let one = HirExpr {
        ty: elem_ty.clone(),
        span,
        kind: HirExprKind::Const(ConstVal::Int { value: 1, ty: prim }),
    };
    let next = HirExpr {
        ty: elem_ty.clone(),
        span,
        kind: HirExprKind::PrimBinOp {
            op: PrimOp::Add,
            lhs: Box::new(HirExpr {
                ty: elem_ty.clone(),
                span,
                kind: HirExprKind::Local(counter),
            }),
            rhs: Box::new(one),
        },
    };
    body_stmts.push(HirStmt::Assign { local: counter, value: next });
    body_stmts.push(HirStmt::Let {
        local: user_local,
        init: HirExpr {
            ty: elem_ty.clone(),
            span,
            kind: HirExprKind::Local(snap),
        },
    });
    // Use lower_block so nested for-loops in the body get expanded too.
    let lowered_body = lower_block(ctx, body);
    body_stmts.extend(lowered_body.stmts);
    if let Some(t) = lowered_body.trailing {
        body_stmts.push(HirStmt::Expr(t));
    }
    ctx.pop_scope();

    let body_block = HirBlock { stmts: body_stmts, trailing: None, label: None };
    let while_expr = HirExpr {
        ty: HirTy::Unit,
        span,
        kind: HirExprKind::While {
            label: label.clone(),
            cond: Box::new(cond),
            body: Box::new(body_block),
        },
    };
    out.push(HirStmt::Expr(while_expr));
    Some(out)
}

/// Desugar `for x in arr { body }` (where `arr: [T; N]`) to:
///   {
///     let __arr = arr;
///     let __i: i32 = 0;
///     while __i < N {
///       let x = __arr[__i];
///       body;
///       __i = __i + 1;
///     }
///   }
fn lower_for_array(
    ctx: &mut LowerCtx<'_>,
    label: &Option<String>,
    pat: &AstPattern,
    iter: &Expr,
    body: &Block,
    span: rokc_diagnostic::Span,
) -> Option<Vec<HirStmt>> {
    let AstPatternKind::Binding { name, sub: None } = &pat.kind else {
        return None;
    };
    let iter_h = lower_expr(ctx, iter);
    let HirTy::Array(elem_ty, len) = iter_h.ty.clone() else {
        return None;
    };
    // Array iteration only supports a path-to-local source for now; the
    // backend stores arrays in dimensioned memref slots that aren't
    // copy-by-assignment friendly.
    let HirExprKind::Local(arr_local) = iter_h.kind else {
        return None;
    };
    let elem_ty = (*elem_ty).clone();
    let idx_prim = PrimTy::I32;
    let idx_hir_ty = HirTy::Prim(idx_prim);

    let counter = ctx.declare(None, idx_hir_ty.clone());

    let mut out = Vec::new();
    out.push(HirStmt::Let {
        local: counter,
        init: HirExpr {
            ty: idx_hir_ty.clone(),
            span,
            kind: HirExprKind::Const(ConstVal::Int { value: 0, ty: idx_prim }),
        },
    });

    let cond = HirExpr {
        ty: HirTy::Prim(PrimTy::Bool),
        span,
        kind: HirExprKind::PrimBinOp {
            op: PrimOp::Lt,
            lhs: Box::new(HirExpr {
                ty: idx_hir_ty.clone(),
                span,
                kind: HirExprKind::Local(counter),
            }),
            rhs: Box::new(HirExpr {
                ty: idx_hir_ty.clone(),
                span,
                kind: HirExprKind::Const(ConstVal::Int {
                    value: i128::from(len),
                    ty: idx_prim,
                }),
            }),
        },
    };

    ctx.push_scope();
    let user_local = ctx.declare(Some(name.clone()), elem_ty.clone());
    let mut body_stmts: Vec<HirStmt> = Vec::new();
    // Snapshot the counter before incrementing so `continue` inside
    // the body jumps to the cond check without skipping the increment.
    let snap = ctx.declare(None, idx_hir_ty.clone());
    body_stmts.push(HirStmt::Let {
        local: snap,
        init: HirExpr {
            ty: idx_hir_ty.clone(),
            span,
            kind: HirExprKind::Local(counter),
        },
    });
    let next = HirExpr {
        ty: idx_hir_ty.clone(),
        span,
        kind: HirExprKind::PrimBinOp {
            op: PrimOp::Add,
            lhs: Box::new(HirExpr {
                ty: idx_hir_ty.clone(),
                span,
                kind: HirExprKind::Local(counter),
            }),
            rhs: Box::new(HirExpr {
                ty: idx_hir_ty.clone(),
                span,
                kind: HirExprKind::Const(ConstVal::Int { value: 1, ty: idx_prim }),
            }),
        },
    };
    body_stmts.push(HirStmt::Assign { local: counter, value: next });
    let elem_read = HirExpr {
        ty: elem_ty.clone(),
        span,
        kind: HirExprKind::ArrayIndex {
            array: Box::new(HirExpr {
                ty: HirTy::Array(Box::new(elem_ty.clone()), len),
                span,
                kind: HirExprKind::Local(arr_local),
            }),
            index: Box::new(HirExpr {
                ty: idx_hir_ty.clone(),
                span,
                kind: HirExprKind::Local(snap),
            }),
            elem_ty: elem_ty.clone(),
        },
    };
    body_stmts.push(HirStmt::Let { local: user_local, init: elem_read });
    // Use lower_block so nested for-loops in the body get expanded too.
    let lowered_body = lower_block(ctx, body);
    body_stmts.extend(lowered_body.stmts);
    if let Some(t) = lowered_body.trailing {
        body_stmts.push(HirStmt::Expr(t));
    }
    ctx.pop_scope();

    let body_block = HirBlock { stmts: body_stmts, trailing: None, label: None };
    let while_expr = HirExpr {
        ty: HirTy::Unit,
        span,
        kind: HirExprKind::While {
            label: label.clone(),
            cond: Box::new(cond),
            body: Box::new(body_block),
        },
    };
    out.push(HirStmt::Expr(while_expr));
    Some(out)
}

fn lower_match(
    ctx: &mut LowerCtx<'_>,
    scrutinee: &Expr,
    arms: &[AstMatchArm],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let scrut_h = lower_expr(ctx, scrutinee);
    let scrut_ty = scrut_h.ty.clone();

    // Spec 3.12.5: exhaustiveness check. Bool needs both true/false (or
    // a catch-all). Primitive ints/floats/str need a catch-all (range
    // is infinite). Sum/enum exhaustiveness is left to a fuller pass.
    check_match_exhaustiveness(ctx, &scrut_ty, arms);

    let mut arm_h: Vec<HirMatchArm> = Vec::with_capacity(arms.len());
    for arm in arms {
        ctx.push_scope();
        let pat = lower_pattern(ctx, &arm.pat, &scrut_ty);
        let guard = arm.guard.as_ref().map(|g| lower_expr(ctx, g));
        let body = lower_expr(ctx, &arm.body);
        ctx.pop_scope();
        arm_h.push(HirMatchArm { pat, guard, body });
    }

    // Result type: take the first arm body's type as a hint. Proper
    // unification across arms lands with type checking.
    let result_ty = arm_h
        .first()
        .map(|a| a.body.ty.clone())
        .unwrap_or(HirTy::Unit);

    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(scrut_h),
            arms: arm_h,
        },
        ty: result_ty,
        span,
    }
}

/// Spec 3.12.5: enforce that match arms cover the scrutinee's type.
/// Stage-1 covers the easy cases; richer checks (sum/enum variants, or
/// patterns spanning multiple alts) land later.
fn check_match_exhaustiveness(
    ctx: &LowerCtx<'_>,
    scrut_ty: &HirTy,
    arms: &[AstMatchArm],
) {
    let has_catch_all = arms
        .iter()
        .any(|a| a.guard.is_none() && pattern_is_catch_all(&a.pat));
    match scrut_ty {
        HirTy::Prim(PrimTy::Bool) => {
            if has_catch_all {
                return;
            }
            let mut saw_true = false;
            let mut saw_false = false;
            for arm in arms {
                if arm.guard.is_some() {
                    continue;
                }
                pattern_collect_bool_literals(&arm.pat, &mut saw_true, &mut saw_false);
            }
            if !(saw_true && saw_false) {
                let missing = match (saw_true, saw_false) {
                    (true, false) => "false",
                    (false, true) => "true",
                    _ => "true and false",
                };
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "non-exhaustive match on `bool`: `{missing}` not covered \
                         (spec 3.12.5)"
                    ),
                );
            }
        }
        HirTy::Prim(p) if p.is_int() || p.is_float() || matches!(p, PrimTy::Str | PrimTy::CChar) => {
            if !has_catch_all {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "non-exhaustive match on `{}`: a catch-all arm \
                         (`_` or a binding) is required because the value \
                         range is infinite (spec 3.12.5)",
                        p.name()
                    ),
                );
            }
        }
        _ => {
            // Sum/Tuple/Struct/Enum/Array/etc.: left to a richer pass.
        }
    }
}

fn pattern_is_catch_all(pat: &AstPattern) -> bool {
    match &pat.kind {
        AstPatternKind::Wildcard => true,
        AstPatternKind::Binding { sub: None, .. } => true,
        AstPatternKind::Or(alts) => alts.iter().any(pattern_is_catch_all),
        _ => false,
    }
}

fn pattern_collect_bool_literals(pat: &AstPattern, saw_t: &mut bool, saw_f: &mut bool) {
    match &pat.kind {
        AstPatternKind::Literal(rokc_ast::Literal::Bool(true)) => *saw_t = true,
        AstPatternKind::Literal(rokc_ast::Literal::Bool(false)) => *saw_f = true,
        AstPatternKind::Or(alts) => {
            for a in alts {
                pattern_collect_bool_literals(a, saw_t, saw_f);
            }
        }
        _ => {}
    }
}

fn lower_pattern(
    ctx: &mut LowerCtx<'_>,
    pat: &AstPattern,
    scrut_ty: &HirTy,
) -> HirPattern {
    match &pat.kind {
        AstPatternKind::Wildcard => HirPattern::Wildcard,
        AstPatternKind::Binding { name, sub: None } if name == "_" => HirPattern::Wildcard,
        AstPatternKind::Binding { name, sub: None } => {
            // Spec 3.11.4: when an enclosing or-pattern shares this name
            // across alternatives, reuse the preset local and check that
            // each alt binds the same type.
            if let Some(map) = ctx.or_pattern_binders.last() {
                if let Some(&local) = map.get(name) {
                    let existing = ctx.local_ty(local);
                    if matches!(existing, HirTy::Unknown) {
                        ctx.locals[local.0 as usize].ty = scrut_ty.clone();
                    } else if existing != *scrut_ty {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "or-pattern binding `{name}` has inconsistent \
                                 types across alternatives (spec 3.11.4)"
                            ),
                        );
                    }
                    return HirPattern::Binding {
                        local,
                        ty: scrut_ty.clone(),
                    };
                }
            }
            let local = ctx.declare(Some(name.clone()), scrut_ty.clone());
            HirPattern::Binding {
                local,
                ty: scrut_ty.clone(),
            }
        }
        AstPatternKind::Literal(AstLit::None) => {
            // `none` against a sum scrutinee → match the none variant.
            if let HirTy::Sum(variants) = scrut_ty {
                if let Some(idx) = variants
                    .iter()
                    .position(|v| matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]))
                {
                    return HirPattern::SumVariant {
                        sum_ty: scrut_ty.clone(),
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        binder: None,
                        payload_ty: None,
                    };
                }
            }
            HirPattern::Literal {
                value: ConstVal::None,
                prim: PrimTy::Bool,
            }
        }
        AstPatternKind::Literal(lit) => match literal_to_const(lit, scrut_ty) {
            Some((value, prim)) => HirPattern::Literal { value, prim },
            None => HirPattern::Wildcard,
        },
        AstPatternKind::TypeCheck { binder, ty } => {
            // `name: T` — narrow a sum scrutinee to variant `T`. Run
            // through `resolve_ast_ty` so generics-substitution sees `T`.
            let target_ty = ctx.resolve_ast_ty(ty);
            if let HirTy::Sum(variants) = scrut_ty {
                if let Some(idx) = sum_variant_index(variants, &target_ty) {
                    let bind_local = binder.as_ref().map(|name| {
                        ctx.declare(Some(name.clone()), target_ty.clone())
                    });
                    return HirPattern::SumVariant {
                        sum_ty: scrut_ty.clone(),
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        binder: bind_local,
                        payload_ty: Some(target_ty),
                    };
                }
            }
            HirPattern::Wildcard
        }
        AstPatternKind::Or(alts) => {
            // Spec 3.11.4: every alternative must bind the same set of
            // names. Pre-allocate one shared local per name (with type
            // resolved during the first alt's lowering and checked for
            // consistency on subsequent alts).
            let mut alt_name_sets: Vec<std::collections::HashSet<String>> =
                alts.iter().map(|a| {
                    let mut s = std::collections::HashSet::new();
                    pattern_bound_names(a, &mut s);
                    s
                }).collect();
            let bound_names = alt_name_sets.first().cloned().unwrap_or_default();
            for (i, set) in alt_name_sets.iter_mut().enumerate().skip(1) {
                if *set != bound_names {
                    let missing: Vec<_> = bound_names.difference(set).cloned().collect();
                    let extra: Vec<_> = set.difference(&bound_names).cloned().collect();
                    let mut detail = String::new();
                    if !missing.is_empty() {
                        detail.push_str(&format!(" missing {missing:?}"));
                    }
                    if !extra.is_empty() {
                        detail.push_str(&format!(" extra {extra:?}"));
                    }
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "or-pattern alternatives bind different name sets \
                             (alternative {i}:{detail}, spec 3.11.4)"
                        ),
                    );
                }
            }
            let mut shared: HashMap<String, LocalId> = HashMap::new();
            for name in &bound_names {
                let local = ctx.declare(Some(name.clone()), HirTy::Unknown);
                shared.insert(name.clone(), local);
            }
            ctx.or_pattern_binders.push(shared);
            let lowered: Vec<HirPattern> = alts
                .iter()
                .map(|a| lower_pattern(ctx, a, scrut_ty))
                .collect();
            ctx.or_pattern_binders.pop();
            HirPattern::Or(lowered)
        }
        // `Color::Red` or `Result::Ok(n)` patterns.
        AstPatternKind::EnumVariant { path, args } => {
            if path.segments.len() == 2 {
                // Try bare enum name; fall back to the scrutinee's
                // enum type so generic-enum patterns find the right
                // mangled instantiation.
                let enum_id_opt = ctx
                    .enum_table
                    .get(&path.segments[0].name)
                    .copied()
                    .or_else(|| match scrut_ty {
                        HirTy::Enum(eid) => {
                            let def = &ctx.enums[eid.0 as usize];
                            let prefix = format!("{}__", path.segments[0].name);
                            if def.name == path.segments[0].name
                                || def.name.starts_with(&prefix)
                            {
                                Some(*eid)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    });
                if let Some(enum_id) = enum_id_opt {
                    let payload_ty = ctx.enums[enum_id.0 as usize]
                        .variants
                        .iter()
                        .find(|v| v.name == path.segments[1].name)
                        .and_then(|v| v.payload_ty.clone());
                    let def = &ctx.enums[enum_id.0 as usize];
                    if let Some(idx) = def
                        .variants
                        .iter()
                        .position(|v| v.name == path.segments[1].name)
                    {
                        // Multi-arg variants pack their args into a tuple
                        // payload — destructure the tuple element types
                        // so each sub-pattern lowers against its own type.
                        let payload = payload_ty.unwrap_or(HirTy::Unknown);
                        let lowered_args: Vec<HirPattern> = if args.len() > 1 {
                            if let HirTy::Tuple(field_tys) = &payload {
                                args.iter()
                                    .zip(field_tys.iter())
                                    .map(|(p, t)| lower_pattern(ctx, p, t))
                                    .collect()
                            } else {
                                args.iter()
                                    .map(|p| lower_pattern(ctx, p, &payload))
                                    .collect()
                            }
                        } else {
                            args.iter()
                                .map(|p| lower_pattern(ctx, p, &payload))
                                .collect()
                        };
                        return HirPattern::EnumVariant {
                            enum_id,
                            variant_index: u32::try_from(idx).expect("variant overflow"),
                            args: lowered_args,
                        };
                    }
                }
            }
            HirPattern::Wildcard
        }
        AstPatternKind::Tuple(pats) => {
            if let HirTy::Tuple(elem_tys) = scrut_ty {
                if pats.len() == elem_tys.len() {
                    let lowered: Vec<HirPattern> = pats
                        .iter()
                        .zip(elem_tys.iter())
                        .map(|(p, t)| lower_pattern(ctx, p, t))
                        .collect();
                    return HirPattern::Tuple(lowered);
                }
            }
            HirPattern::Wildcard
        }
        AstPatternKind::Range { start, end, inclusive } => {
            // Pick the scrutinee's primitive so the compare op is well-typed.
            let prim = match scrut_ty {
                HirTy::Prim(p) => *p,
                _ => return HirPattern::Wildcard,
            };
            let s_const = start
                .as_ref()
                .and_then(|lit| literal_to_const(lit, scrut_ty))
                .map(|(v, _)| v);
            let e_const = end
                .as_ref()
                .and_then(|lit| literal_to_const(lit, scrut_ty))
                .map(|(v, _)| v);
            HirPattern::Range {
                start: s_const,
                end: e_const,
                inclusive: *inclusive,
                prim,
            }
        }
        AstPatternKind::Struct { path, fields, .. } => {
            // `EnumName::Variant { x, y }` — enum named-form variant
            // pattern. Map each field name to its position in the
            // variant's tuple payload (spec 2.4) and lower as an
            // `EnumVariant` pattern.
            if path.segments.len() == 2 {
                if let Some(&enum_id) = ctx.enum_table.get(&path.segments[0].name) {
                    let def = &ctx.enums[enum_id.0 as usize];
                    if let Some((idx, variant)) = def
                        .variants
                        .iter()
                        .enumerate()
                        .find(|(_, v)| v.name == path.segments[1].name)
                    {
                        if !variant.named_fields.is_empty() {
                            let field_names = variant.named_fields.clone();
                            let field_tys: Vec<HirTy> = match &variant.payload_ty {
                                Some(HirTy::Tuple(parts)) => parts.clone(),
                                _ => Vec::new(),
                            };
                            let mut by_name: HashMap<String, &rokc_ast::FieldPattern> =
                                fields.iter().map(|fp| (fp.name.clone(), fp)).collect();
                            let mut args: Vec<HirPattern> =
                                Vec::with_capacity(field_names.len());
                            for (i, fname) in field_names.iter().enumerate() {
                                let ty = field_tys
                                    .get(i)
                                    .cloned()
                                    .unwrap_or(HirTy::Unknown);
                                match by_name.remove(fname) {
                                    Some(fp) => match &fp.pat {
                                        Some(p) => args.push(lower_pattern(ctx, p, &ty)),
                                        None => {
                                            let local = ctx.declare(
                                                Some(fp.name.clone()),
                                                ty.clone(),
                                            );
                                            args.push(HirPattern::Binding { local, ty });
                                        }
                                    },
                                    None => args.push(HirPattern::Wildcard),
                                }
                            }
                            return HirPattern::EnumVariant {
                                enum_id,
                                variant_index: u32::try_from(idx)
                                    .expect("variant overflow"),
                                args,
                            };
                        }
                    }
                }
            }
            let struct_id = match path.segments.last() {
                Some(seg) => ctx.struct_table.get(&seg.name).copied(),
                None => None,
            };
            let Some(struct_id) = struct_id else {
                return HirPattern::Wildcard;
            };
            let def = &ctx.structs[struct_id.0 as usize];
            let mut lowered: Vec<(u32, HirPattern)> = Vec::new();
            for fp in fields {
                let Some(idx) = def.fields.iter().position(|f| f.name == fp.name) else {
                    continue;
                };
                let field_ty = def.fields[idx].ty.clone();
                let sub = match &fp.pat {
                    Some(p) => lower_pattern(ctx, p, &field_ty),
                    // Shorthand `Foo { x }` — bind a local of the field's name.
                    None => {
                        let local = ctx.declare(Some(fp.name.clone()), field_ty.clone());
                        HirPattern::Binding {
                            local,
                            ty: field_ty,
                        }
                    }
                };
                lowered.push((u32::try_from(idx).expect("field index overflow"), sub));
            }
            HirPattern::Struct {
                struct_id,
                fields: lowered,
            }
        }
        // Range / struct patterns land later.
        _ => HirPattern::Wildcard,
    }
}

/// Convert an AST literal that appears in a pattern to a `ConstVal` plus
/// the primitive type the comparison should use. Falls back to `None`
/// when the literal can't be matched against the scrutinee at the
/// primitive level (e.g. string vs i32).
fn literal_to_const(lit: &AstLit, scrut_ty: &HirTy) -> Option<(ConstVal, PrimTy)> {
    match lit {
        AstLit::Int(text) => {
            // Bare literals (no suffix) take their type from the scrutinee
            // so `match x { 0 => ... }` works against any integer `x`.
            let suffixed = has_int_suffix(text);
            let (value, mut ty) = parse_int_literal(text)?;
            if !suffixed {
                if let HirTy::Prim(p) = scrut_ty {
                    if p.is_int() {
                        ty = *p;
                    }
                }
            }
            Some((ConstVal::Int { value, ty }, ty))
        }
        AstLit::Bool(b) => Some((ConstVal::Bool(*b), PrimTy::Bool)),
        AstLit::None => Some((ConstVal::None, PrimTy::Bool)),
        AstLit::Char(s) | AstLit::CChar(s) => parse_char_literal(s)
            .map(|c| (ConstVal::Char(c), PrimTy::CChar)),
        AstLit::Float(_) | AstLit::Str(_) | AstLit::RawStr(_) | AstLit::FStr(_) => None,
    }
}

// Decode common escape sequences inside a `"..."` literal body. Unknown
// escapes are passed through verbatim so unfamiliar sequences surface
// to the user rather than getting silently dropped.
fn decode_str_escapes(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\\' && i + 1 < bytes.len() {
            let c = bytes[i + 1];
            match c {
                b'n' => { out.push('\n'); i += 2; continue; }
                b't' => { out.push('\t'); i += 2; continue; }
                b'r' => { out.push('\r'); i += 2; continue; }
                b'0' => { out.push('\0'); i += 2; continue; }
                b'\\' => { out.push('\\'); i += 2; continue; }
                b'"' => { out.push('"'); i += 2; continue; }
                b'\'' => { out.push('\''); i += 2; continue; }
                b'x' if i + 3 < bytes.len() => {
                    if let Ok(byte) = u8::from_str_radix(&s[i + 2..i + 4], 16) {
                        out.push(byte as char);
                        i += 4;
                        continue;
                    }
                }
                _ => {}
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }
    out
}

fn has_int_suffix(text: &str) -> bool {
    const SUFFIXES: &[&str] = &[
        "isize", "usize", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
    ];
    SUFFIXES.iter().any(|s| text.ends_with(s))
}

/// Spec 3.14.1: `throw` / `return` / `break` / `continue` are divergent.
/// A block whose final statement is one of these (and that has no
/// trailing expression) yields no value. Used by `lower_if` to ignore
/// the divergent branch's apparent unit type when picking a result type.
///
/// Checked on the AST because Throw lowers to a `rok_panic` call (a
/// `HirStmt::Expr`) and we'd lose the divergence signal otherwise.
fn ast_block_diverges(b: &Block) -> bool {
    if b.trailing.is_some() {
        return false;
    }
    matches!(
        b.stmts.last().map(|s| &s.kind),
        Some(StmtKind::Throw(_) | StmtKind::Return(_) | StmtKind::Break { .. } | StmtKind::Continue { .. })
    )
}

fn ast_expr_diverges(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Block(b) => ast_block_diverges(b),
        _ => false,
    }
}

fn lower_if(
    ctx: &mut LowerCtx<'_>,
    cond: &Expr,
    then_block: &Block,
    else_branch: Option<&Expr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let cond_h = lower_expr(ctx, cond);
    let mut then_h = lower_block(ctx, then_block);
    let mut else_h = else_branch.map(|e| Box::new(lower_expr(ctx, e)));

    // Result type: the trailing expression of the then-block (or unit).
    // Spec 3.14.1: `throw` (and `return`/`break`/`continue`) are divergent
    // — when one branch ends in such a statement and has no trailing
    // expression, the if's result type is taken from the other branch.
    // Without this, `let v = if c { 7 } else { throw 99; };` ends up
    // as `Unknown` and codegen miscompiles.
    let then_ty = then_h
        .trailing
        .as_ref()
        .map_or(HirTy::Unit, |e| e.ty.clone());
    let else_ty = else_h
        .as_ref()
        .map_or(HirTy::Unit, |e| e.ty.clone());
    let then_diverges = ast_block_diverges(then_block);
    let else_diverges = matches!(else_branch, Some(eb) if ast_expr_diverges(eb));
    let result_ty = if else_branch.is_some() {
        if then_diverges {
            else_ty
        } else if else_diverges {
            then_ty
        } else if then_ty == else_ty {
            then_ty
        } else {
            // Spec 변경점 1019: 분기 타입이 다르면 결과는 자동 합 타입
            // (`if c { 7 } else { 3.14 }` → `i32 | f64`). 두 분기 값을
            // sum 표현으로 wrap 해서 codegen 단계의 merge param 타입을
            // 일치시킨다. MIR 의 widest-payload 선택 + cast 가 이종
            // payload (`i32 | f64`) 도 처리.
            let sum = HirTy::Sum(vec![then_ty.clone(), else_ty.clone()]);
            if let Some(t) = then_h.trailing.take() {
                then_h.trailing = Some(wrap_into_sum(&sum, t));
            }
            if let Some(boxed) = else_h.take() {
                else_h = Some(Box::new(wrap_if_block_trailing(*boxed, &sum)));
            }
            sum
        }
    } else {
        HirTy::Unit
    };

    HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(cond_h),
            then_block: Box::new(then_h),
            else_branch: else_h,
        },
        ty: result_ty,
        span,
    }
}

// For an else branch — typically a Block expression — wrap the block's
// trailing expression into the unifying sum. Falls back to wrapping the
// whole expression when the else isn't a block (e.g. `else if`).
fn wrap_if_block_trailing(expr: HirExpr, sum_ty: &HirTy) -> HirExpr {
    match expr.kind {
        HirExprKind::Block(mut b) => {
            if let Some(t) = b.trailing.take() {
                b.trailing = Some(wrap_into_sum(sum_ty, t));
            }
            HirExpr {
                ty: sum_ty.clone(),
                kind: HirExprKind::Block(b),
                span: expr.span,
            }
        }
        _ => wrap_into_sum(sum_ty, expr),
    }
}

// `recv.method(args)` → Call to `Type__method(recv, args)` if the
// receiver's type maps to an inherent impl. Otherwise produces a unit
// placeholder until the resolver can take over.
fn lower_method_call(
    ctx: &mut LowerCtx<'_>,
    receiver: &Expr,
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let recv_h = lower_expr(ctx, receiver);
    let Some(target) = method_target_for(&recv_h.ty) else {
        // Receiver type isn't dispatchable (Unknown / Any). Diagnose so
        // the user sees the method-call attempt instead of silently
        // collapsing to a unit value (spec 3.5.2).
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "method `{method}` cannot be dispatched on a value of \
                 unresolved type (spec 3.5.2)"
            ),
        );
        return HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: HirTy::Unknown,
            span,
        };
    };
    let Some(&fn_id) = ctx.method_table.get(&(target, method.to_owned())) else {
        // Spec 3.5.2: a missing method is a hard error, not a silent
        // unit return. Without this diagnostic `big.into()` (where
        // `into` isn't an impl method on i64) would build and yield 0
        // — a silent miscompile.
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "no method `{method}` found for type `{}` (spec 3.5.2). \
                 Either add `impl {{ fn {method}(...) {{...}} }}` or import \
                 a trait that provides it.",
                ty_mangle(&recv_h.ty)
            ),
        );
        return HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: HirTy::Unknown,
            span,
        };
    };
    // Reverse-lookup the signature for the return type via the
    // synthetic fn name, so call-result typing stays consistent with
    // free-function calls.
    let mangled = format!("{}__{}", ty_mangle(&recv_h.ty), method);
    let ret_ty = ctx
        .fn_table
        .get(&mangled)
        .map(|s| s.ret_ty.clone())
        .unwrap_or(HirTy::Unknown);

    // Spec 4.5/4.8: callee param types should hint untyped closure args
    // (trailing closure on a method call too). Same propagation as
    // free-function calls. Receiver counts as param 0.
    let expected_param_tys: Vec<HirTy> = ctx
        .fn_table
        .get(&mangled)
        .map(|s| s.param_tys.clone())
        .unwrap_or_default();

    let mut lowered = Vec::with_capacity(args.len() + 1);
    lowered.push(recv_h);
    for (i, a) in args.iter().enumerate() {
        if let CallArg::Positional(e) = a {
            // Receiver took slot 0, so user args map to slots 1, 2, ...
            let slot = i + 1;
            let pushed = if let Some(t) = expected_param_tys.get(slot) {
                if !matches!(t, HirTy::Any | HirTy::Unknown) {
                    ctx.push_expected(t.clone());
                    true
                } else {
                    false
                }
            } else {
                false
            };
            let lh = lower_expr(ctx, e);
            if pushed {
                ctx.pop_expected();
            }
            lowered.push(lh);
        }
    }
    // Apply parameter defaults for missing args. The receiver counts
    // as the first arg, so defaults skip past index 0.
    if let Some(sig) = ctx.fn_table.get(&mangled).cloned() {
        while lowered.len() < sig.param_defaults.len() {
            let i = lowered.len();
            let Some(default_expr) = &sig.param_defaults[i] else {
                break;
            };
            lowered.push(lower_expr(ctx, default_expr));
        }
    }
    HirExpr {
        kind: HirExprKind::Call { callee: fn_id, args: lowered },
        ty: ret_ty,
        span,
    }
}

fn lower_call(
    ctx: &mut LowerCtx<'_>,
    callee: &Expr,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // Spec 4.5/4.8: callee param types should hint untyped closure args.
    // Look up the callee's signature *before* lowering arguments so the
    // expected-type stack carries the right hint into each argument.
    // Falls back to no hint when the callee isn't statically resolvable
    // (indirect/closure call etc.) — those still work without inference.
    let callee_sig: Option<FnSig> = if let ExprKind::Path(p) = &callee.kind {
        let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
        ctx.resolve_fn_name(&segs)
            .and_then(|full| ctx.fn_table.get(&full).cloned())
            .or_else(|| {
                if p.segments.len() == 1 {
                    ctx.fn_table.get(&p.segments[0].name).cloned()
                } else {
                    None
                }
            })
    } else {
        None
    };
    let expected_param_tys: Vec<HirTy> = callee_sig
        .as_ref()
        .map(|s| s.param_tys.clone())
        .unwrap_or_default();

    // Spec 4.1: reorder named arguments (`f(name: 42)`) into positional
    // slots based on the callee's `param_names`. When the callee can't
    // be statically resolved we still accept Positional args; Named/
    // Spread fall through to the default Positional handling for now.
    let reordered_args: Vec<CallArg> = if let Some(sig) = &callee_sig {
        if !sig.param_names.is_empty()
            && args.iter().any(|a| matches!(a, CallArg::Named { .. }))
        {
            let mut slots: Vec<Option<Expr>> = vec![None; sig.param_names.len()];
            let mut next_pos = 0usize;
            for a in args {
                match a {
                    CallArg::Positional(e) => {
                        if next_pos < slots.len() {
                            slots[next_pos] = Some(e.clone());
                            next_pos += 1;
                        }
                    }
                    CallArg::Named { name, value } => {
                        if let Some(idx) =
                            sig.param_names.iter().position(|n| n == name)
                        {
                            if slots[idx].is_some() {
                                ctx.emit_error(
                                    rokc_diagnostic::ErrorKind::Type,
                                    format!(
                                        "argument `{name}` provided more than \
                                         once (spec 4.1)"
                                    ),
                                );
                            }
                            slots[idx] = Some(value.clone());
                        } else {
                            ctx.emit_error(
                                rokc_diagnostic::ErrorKind::Type,
                                format!(
                                    "callee has no parameter named `{name}` \
                                     (spec 4.1)"
                                ),
                            );
                        }
                    }
                    CallArg::Spread(e) => {
                        // Spread is unimplemented at lower level; pass
                        // through as positional so existing dispatch keeps
                        // working until spec 4.x spread lands.
                        if next_pos < slots.len() {
                            slots[next_pos] = Some(e.clone());
                            next_pos += 1;
                        }
                    }
                }
            }
            slots
                .into_iter()
                .filter_map(|s| s.map(CallArg::Positional))
                .collect()
        } else {
            args.to_vec()
        }
    } else {
        args.to_vec()
    };
    let args = reordered_args.as_slice();

    let mut lowered_args: Vec<HirExpr> = Vec::new();
    let mut idx = 0usize;
    for a in args {
        match a {
            CallArg::Positional(e) => {
                let pushed = if let Some(t) = expected_param_tys.get(idx) {
                    if !matches!(t, HirTy::Any | HirTy::Unknown) {
                        ctx.push_expected(t.clone());
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };
                let lh = lower_expr(ctx, e);
                if pushed {
                    ctx.pop_expected();
                }
                lowered_args.push(lh);
                idx += 1;
            }
            CallArg::Spread(e) => {
                // Spec 4.1 / variant 838: `f(..args)` — tuple spread.
                // Lower the inner expression once, then synthesize a
                // `TupleField` access per element. Stage-1 supports
                // tuple values whose shape is statically known; List/
                // Dict spreads are separate milestones.
                let lh = lower_expr(ctx, e);
                if let HirTy::Tuple(parts) = lh.ty.clone() {
                    let span = lh.span;
                    for (i, part_ty) in parts.iter().enumerate() {
                        let field = HirExpr {
                            kind: HirExprKind::TupleField {
                                target: Box::new(lh.clone()),
                                index: u32::try_from(i).expect("tuple field overflow"),
                                field_ty: part_ty.clone(),
                            },
                            ty: part_ty.clone(),
                            span,
                        };
                        lowered_args.push(field);
                        idx += 1;
                    }
                } else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        "spread `f(..x)` only supports tuple values in stage-1 \
                         (List/Dict spread are separate milestones, spec 4.1)"
                            .to_owned(),
                    );
                }
            }
            _ => {}
        }
    }

    // Module-qualified call. `inner::helper(args)` — and arbitrary deeper
    // paths — resolve via the module-aware fn-name resolver. Visibility
    // is enforced before falling through to existing 2-segment paths
    // (which handle `EnumName::Variant` and `Type::method`).
    if let ExprKind::Path(p) = &callee.kind {
        if !p.segments.is_empty() {
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            if let Some(full) = ctx.resolve_fn_name(&segs) {
                let def_module = module_of(&full);
                let vis = ctx
                    .item_visibility
                    .get(&full)
                    .copied()
                    .unwrap_or(Visibility::Pub);
                if ctx.is_visible(&def_module, vis) {
                    if let Some(sig) = ctx.fn_table.get(&full).cloned() {
                        while lowered_args.len() < sig.param_defaults.len() {
                            let i = lowered_args.len();
                            let Some(default_expr) = &sig.param_defaults[i] else {
                                break;
                            };
                            lowered_args.push(lower_expr(ctx, default_expr));
                        }
                        // Spec 3.14 / 4.x: when a param's declared type is a
                        // sum (`i32 | none` etc.) and the caller passed a
                        // raw variant value, wrap it into the sum's tagged
                        // representation. Without this the call site emits
                        // a type-mismatched argument and codegen rejects.
                        let coerced_args: Vec<HirExpr> = lowered_args
                            .into_iter()
                            .enumerate()
                            .map(|(i, a)| match sig.param_tys.get(i) {
                                Some(t) => wrap_into_sum(t, a),
                                None => a,
                            })
                            .collect();
                        return HirExpr {
                            kind: HirExprKind::Call {
                                callee: sig.id,
                                args: coerced_args,
                            },
                            ty: sig.ret_ty,
                            span,
                        };
                    }
                } else {
                    // spec 5.6: non-`pub` items aren't reachable across
                    // module boundaries. Emit an explicit error rather
                    // than letting the call silently fall through to
                    // method/enum constructor disambiguation.
                    let where_ = if ctx.current_module.is_empty() {
                        "<root>".to_owned()
                    } else {
                        ctx.current_module.clone()
                    };
                    let def_loc = if def_module.is_empty() {
                        "<root>".to_owned()
                    } else {
                        def_module.clone()
                    };
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Module,
                        format!(
                            "function `{full}` is private to module `{def_loc}` and \
                             cannot be called from `{where_}` (spec 5.6 — add `pub` \
                             to expose it)"
                        ),
                    );
                    return HirExpr {
                        kind: HirExprKind::Const(ConstVal::Unit),
                        ty: HirTy::Unit,
                        span,
                    };
                }
            }
        }
    }

    // `Foo(arg, ...)` — tuple-struct constructor (spec 2.7.4). Field
    // names are positional ("0", "1", …) so the call args fill them
    // by index; types are wrapped into sum slots when applicable.
    if let ExprKind::Path(p) = &callee.kind {
        if p.segments.len() == 1 {
            if let Some(&struct_id) = ctx.struct_table.get(&p.segments[0].name) {
                let def = &ctx.structs[struct_id.0 as usize];
                let is_tuple_form = !def.fields.is_empty()
                    && def
                        .fields
                        .iter()
                        .enumerate()
                        .all(|(i, f)| f.name == i.to_string());
                if is_tuple_form && lowered_args.len() == def.fields.len() {
                    let field_tys: Vec<HirTy> =
                        def.fields.iter().map(|f| f.ty.clone()).collect();
                    let ordered: Vec<HirExpr> = lowered_args
                        .into_iter()
                        .zip(field_tys.iter())
                        .map(|(a, t)| wrap_into_sum(t, a))
                        .collect();
                    return HirExpr {
                        kind: HirExprKind::StructInit {
                            struct_id,
                            fields: ordered,
                        },
                        ty: HirTy::Struct(struct_id),
                        span,
                    };
                }
            }
        }
    }

    // `EnumName::Variant(payload)` — tuple-form enum constructor.
    if let ExprKind::Path(p) = &callee.kind {
        if p.segments.len() == 2 {
            // Try bare name first; fall back to a generic-instantiation
            // search keyed on the lowered arg types.
            let mut enum_id_opt = ctx.enum_table.get(&p.segments[0].name).copied();
            if enum_id_opt.is_none() {
                let prefix = format!("{}__", p.segments[0].name);
                enum_id_opt = ctx
                    .enum_table
                    .iter()
                    .filter(|(k, _)| k.starts_with(&prefix))
                    .find_map(|(_, &id)| {
                        let def = &ctx.enums[id.0 as usize];
                        let variant = def.variants.iter().find(|v| v.name == p.segments[1].name)?;
                        let payload_match = match &variant.payload_ty {
                            None => lowered_args.is_empty(),
                            Some(HirTy::Tuple(parts)) => {
                                parts.len() == lowered_args.len()
                                    && parts.iter().zip(lowered_args.iter()).all(|(p, a)| p == &a.ty)
                            }
                            Some(t) => {
                                lowered_args.len() == 1 && t == &lowered_args[0].ty
                            }
                        };
                        if payload_match { Some(id) } else { None }
                    });
            }
            if let Some(enum_id) = enum_id_opt {
                let def = &ctx.enums[enum_id.0 as usize];
                if let Some(idx) = def
                    .variants
                    .iter()
                    .position(|v| v.name == p.segments[1].name)
                {
                    return HirExpr {
                        kind: HirExprKind::EnumVariantInit {
                            enum_id,
                            variant_index: u32::try_from(idx).expect("variant overflow"),
                            args: lowered_args,
                        },
                        ty: HirTy::Enum(enum_id),
                        span,
                    };
                }
            }
            // `Type::method(args)` — static method call on a struct or
            // enum, dispatched through the method_table. Falls back to
            // a single matching generic-instantiation when the bare
            // name isn't registered (e.g. `Stack::new()` with one
            // `Stack<...>` instantiation in scope).
            let target = if let Some(sid) = ctx.struct_table.get(&p.segments[0].name).copied() {
                Some(MethodTarget::Struct(sid))
            } else if let Some(&eid) = ctx.enum_table.get(&p.segments[0].name) {
                Some(MethodTarget::Enum(eid))
            } else {
                let prefix = format!("{}__", p.segments[0].name);
                let method_name = &p.segments[1].name;
                let candidates: Vec<MethodTarget> = ctx
                    .struct_table
                    .iter()
                    .filter(|(k, _)| k.starts_with(&prefix))
                    .filter_map(|(_, &id)| {
                        let key = (MethodTarget::Struct(id), method_name.clone());
                        if ctx.method_table.contains_key(&key) {
                            Some(MethodTarget::Struct(id))
                        } else {
                            None
                        }
                    })
                    .chain(
                        ctx.enum_table
                            .iter()
                            .filter(|(k, _)| k.starts_with(&prefix))
                            .filter_map(|(_, &id)| {
                                let key = (MethodTarget::Enum(id), method_name.clone());
                                if ctx.method_table.contains_key(&key) {
                                    Some(MethodTarget::Enum(id))
                                } else {
                                    None
                                }
                            }),
                    )
                    .collect();
                if candidates.len() == 1 {
                    Some(candidates[0].clone())
                } else {
                    None
                }
            };
            if let Some(target) = target {
                let method_name = p.segments[1].name.clone();
                let prefix = match &target {
                    MethodTarget::Struct(sid) => format!("Struct{}", sid.0),
                    MethodTarget::Enum(eid) => format!("Enum{}", eid.0),
                    MethodTarget::Mangled(s) => s.clone(),
                };
                if let Some(&fn_id) = ctx.method_table.get(&(target, method_name.clone())) {
                    let mangled_name = format!("{}__{}", prefix, method_name);
                    // Apply parameter defaults for missing args.
                    if let Some(sig) = ctx.fn_table.get(&mangled_name).cloned() {
                        while lowered_args.len() < sig.param_defaults.len() {
                            let i = lowered_args.len();
                            let Some(default_expr) = &sig.param_defaults[i] else {
                                break;
                            };
                            lowered_args.push(lower_expr(ctx, default_expr));
                        }
                    }
                    let ret_ty = ctx
                        .fn_table
                        .get(&mangled_name)
                        .map(|s| s.ret_ty.clone())
                        .unwrap_or(HirTy::Unknown);
                    return HirExpr {
                        kind: HirExprKind::Call {
                            callee: fn_id,
                            args: lowered_args,
                        },
                        ty: ret_ty,
                        span,
                    };
                }
            }
        }
    }

    // Field-of-fn-pointer call: `(s.f)(args)` where `f: fn(...) -> R`.
    if let ExprKind::Field(_, _) = &callee.kind {
        let callee_h = lower_expr(ctx, callee);
        if let HirTy::Fn(_, ret) = callee_h.ty.clone() {
            let ret_ty = (*ret).clone();
            return HirExpr {
                kind: HirExprKind::CallIndirect {
                    callee: Box::new(callee_h),
                    args: lowered_args,
                    ret_ty: ret_ty.clone(),
                },
                ty: ret_ty,
                span,
            };
        }
    }

    // Local of `fn(...)` or closure type → indirect call. Closures
    // package an env alongside the function pointer; non-capturing
    // function pointers don't.
    if let ExprKind::Path(p) = &callee.kind {
        if p.segments.len() == 1 {
            if let Some(local) = ctx.lookup(&p.segments[0].name) {
                let local_ty = ctx.local_ty(local);
                match local_ty.clone() {
                    HirTy::Fn(_, ret) => {
                        let callee_h = HirExpr {
                            kind: HirExprKind::Local(local),
                            ty: local_ty,
                            span: callee.span,
                        };
                        let ret_ty = (*ret).clone();
                        return HirExpr {
                            kind: HirExprKind::CallIndirect {
                                callee: Box::new(callee_h),
                                args: lowered_args,
                                ret_ty: ret_ty.clone(),
                            },
                            ty: ret_ty,
                            span,
                        };
                    }
                    HirTy::Closure { args: arg_tys, ret, env } => {
                        let callee_h = HirExpr {
                            kind: HirExprKind::Local(local),
                            ty: local_ty,
                            span: callee.span,
                        };
                        let ret_ty = (*ret).clone();
                        return HirExpr {
                            kind: HirExprKind::CallClosure {
                                closure: Box::new(callee_h),
                                args: lowered_args,
                                arg_tys,
                                ret_ty: ret_ty.clone(),
                                env_ty: (*env).clone(),
                            },
                            ty: ret_ty,
                            span,
                        };
                    }
                    _ => {}
                }
            }
        }
    }

    // Generic function call — monomorphize on demand using the
    // inferred concrete arg types.
    if let ExprKind::Path(p) = &callee.kind {
        if p.segments.len() == 1 {
            if let Some(generic_def) = ctx.generic_fns.get(&p.segments[0].name).copied() {
                if let Some((mono_id, ret_ty)) =
                    monomorphize(ctx, generic_def, &lowered_args, span)
                {
                    return HirExpr {
                        kind: HirExprKind::Call { callee: mono_id, args: lowered_args },
                        ty: ret_ty,
                        span,
                    };
                }
            }
        }
    }

    let sig = match &callee.kind {
        ExprKind::Path(p) if p.segments.len() == 1 => {
            ctx.fn_table
                .get(&p.segments[0].name)
                .cloned()
                .or_else(|| {
                    // Recursive call to a previously-instantiated mono.
                    None
                })
        }
        _ => None,
    };
    let Some(sig) = sig else {
        return HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: HirTy::Unknown,
            span,
        };
    };
    // Pad missing positional args from declared parameter defaults.
    while lowered_args.len() < sig.param_defaults.len() {
        let i = lowered_args.len();
        let Some(default_expr) = &sig.param_defaults[i] else {
            break;
        };
        lowered_args.push(lower_expr(ctx, default_expr));
    }
    HirExpr {
        kind: HirExprKind::Call { callee: sig.id, args: lowered_args },
        ty: sig.ret_ty,
        span,
    }
}

fn lower_infix(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    lhs: &Expr,
    rhs: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // Spec 3.2 / 3.1: `&&` and `||` short-circuit. Desugar before
    // lowering rhs so that side effects in rhs only run when needed.
    //   a && b  →  if a { b } else { false }
    //   a || b  →  if a { true } else { b }
    // The previous `arith.andi`/`arith.ori` lowering evaluated both
    // sides eagerly, silently violating spec.
    if op == "&&" || op == "||" {
        return lower_short_circuit(ctx, op, lhs, rhs, span);
    }

    let lhs_h = lower_expr(ctx, lhs);
    let rhs_h = lower_expr(ctx, rhs);

    // Spec 0.4 / 3.1: `a + b` desugars to a trait method call. The
    // language does not know operator semantics — they are stdlib's job.
    // Try trait dispatch first (works for Struct/Enum and any type whose
    // mangled shape has a method registered, including primitive types
    // once stdlib provides `impl Add for i32` etc.). Only fall back to
    // a hardcoded PrimOp when no trait is wired up — this preserves
    // stage-1 semantics until stdlib's primitive impls land.
    if let Some(call) = dispatch_user_op(ctx, op, Fixity::Infix, &lhs_h, Some(&rhs_h), span) {
        return call;
    }
    if let (HirTy::Prim(lp), HirTy::Prim(rp)) = (&lhs_h.ty, &rhs_h.ty) {
        if lp == rp {
            if let Some((primop, result_ty)) = infix_for_prim(op, *lp) {
                return HirExpr {
                    kind: HirExprKind::PrimBinOp {
                        op: primop,
                        lhs: Box::new(lhs_h),
                        rhs: Box::new(rhs_h),
                    },
                    ty: result_ty,
                    span,
                };
            }
        }
    }
    HirExpr {
        kind: HirExprKind::Const(ConstVal::Unit),
        ty: HirTy::Unknown,
        span,
    }
}

fn lower_short_circuit(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    lhs: &Expr,
    rhs: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let lhs_h = lower_expr(ctx, lhs);
    let rhs_h = lower_expr(ctx, rhs);
    let mk_const_bool = |b: bool| HirExpr {
        kind: HirExprKind::Const(ConstVal::Bool(b)),
        ty: bool_ty.clone(),
        span,
    };
    let mk_block = |trailing: HirExpr| HirBlock {
        stmts: Vec::new(),
        trailing: Some(trailing),
        label: None,
    };
    let (then_expr, else_expr) = if op == "&&" {
        (rhs_h, mk_const_bool(false))
    } else {
        (mk_const_bool(true), rhs_h)
    };
    HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(lhs_h),
            then_block: Box::new(mk_block(then_expr)),
            else_branch: Some(Box::new(else_expr)),
        },
        ty: bool_ty,
        span,
    }
}

fn lower_prefix(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    operand: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let operand_h = lower_expr(ctx, operand);
    // Spec 0.4: trait dispatch first; PrimOp is the stage-1 fallback when
    // no `impl Neg for i32` (etc.) is registered yet.
    if let Some(call) = dispatch_user_op(ctx, op, Fixity::Prefix, &operand_h, None, span) {
        return call;
    }
    if let HirTy::Prim(p) = &operand_h.ty {
        if let Some((primop, result_ty)) = prefix_for_prim(op, *p) {
            return HirExpr {
                kind: HirExprKind::PrimUnaryOp {
                    op: primop,
                    operand: Box::new(operand_h),
                },
                ty: result_ty,
                span,
            };
        }
    }
    HirExpr {
        kind: HirExprKind::Const(ConstVal::Unit),
        ty: HirTy::Unknown,
        span,
    }
}

// Try to dispatch an operator to an inherent method on the lhs type.
// Used by both infix (with `rhs`) and prefix (without).
fn dispatch_user_op(
    ctx: &LowerCtx<'_>,
    sym: &str,
    fixity: Fixity,
    lhs: &HirExpr,
    rhs: Option<&HirExpr>,
    span: rokc_diagnostic::Span,
) -> Option<HirExpr> {
    let entry = ctx.prec.lookup(sym, fixity)?;
    let target = match &lhs.ty {
        HirTy::Struct(id) => MethodTarget::Struct(*id),
        HirTy::Enum(id) => MethodTarget::Enum(*id),
        _ => return None,
    };
    let &fn_id = ctx.method_table.get(&(target, entry.method_name.clone()))?;
    let mangled = format!("{}__{}", ty_mangle(&lhs.ty), entry.method_name);
    let ret_ty = ctx
        .fn_table
        .get(&mangled)
        .map(|s| s.ret_ty.clone())
        .unwrap_or(HirTy::Unknown);
    let mut args = Vec::with_capacity(2);
    args.push(lhs.clone());
    if let Some(r) = rhs {
        args.push(r.clone());
    }
    Some(HirExpr {
        kind: HirExprKind::Call { callee: fn_id, args },
        ty: ret_ty,
        span,
    })
}

/// Map an infix operator symbol + primitive operand type to a primitive
/// op and its result type. Returns `None` if the combination isn't valid
/// for primitives (in which case dispatch goes through trait lookup —
/// not yet implemented).
fn infix_for_prim(sym: &str, prim: PrimTy) -> Option<(PrimOp, HirTy)> {
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let same_ty = HirTy::Prim(prim);
    let arith = |op: PrimOp| Some((op, same_ty.clone()));
    let cmp = |op: PrimOp| Some((op, bool_ty.clone()));

    match sym {
        "+" if prim.is_int() || prim.is_float() => arith(PrimOp::Add),
        "-" if prim.is_int() || prim.is_float() => arith(PrimOp::Sub),
        "*" if prim.is_int() || prim.is_float() => arith(PrimOp::Mul),
        "/" if prim.is_int() || prim.is_float() => arith(PrimOp::Div),
        "%" if prim.is_int() || prim.is_float() => arith(PrimOp::Rem),
        "&" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitAnd),
        "|" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitOr),
        "^" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitXor),
        "<<" if prim.is_int() => arith(PrimOp::Shl),
        ">>" if prim.is_int() => arith(PrimOp::Shr),
        "==" => cmp(PrimOp::Eq),
        "!=" => cmp(PrimOp::Ne),
        "<" if prim.is_int() || prim.is_float() => cmp(PrimOp::Lt),
        "<=" if prim.is_int() || prim.is_float() => cmp(PrimOp::Le),
        ">" if prim.is_int() || prim.is_float() => cmp(PrimOp::Gt),
        ">=" if prim.is_int() || prim.is_float() => cmp(PrimOp::Ge),
        "&&" if matches!(prim, PrimTy::Bool) => cmp(PrimOp::LogicalAnd),
        "||" if matches!(prim, PrimTy::Bool) => cmp(PrimOp::LogicalOr),
        _ => None,
    }
}

fn prefix_for_prim(sym: &str, prim: PrimTy) -> Option<(PrimOp, HirTy)> {
    let same_ty = HirTy::Prim(prim);
    match sym {
        "-" if prim.is_signed_int() || prim.is_float() => Some((PrimOp::Neg, same_ty)),
        "!" if matches!(prim, PrimTy::Bool) => Some((PrimOp::LogicalNot, same_ty)),
        "~" if prim.is_int() => Some((PrimOp::Not, same_ty)),
        _ => None,
    }
}

fn lower_path(ctx: &mut LowerCtx<'_>, path: &AstPath, span: rokc_diagnostic::Span) -> HirExpr {
    if path.segments.len() == 1 {
        if let Some(local) = ctx.lookup(&path.segments[0].name) {
            let ty = ctx.local_ty(local);
            return HirExpr {
                kind: HirExprKind::Local(local),
                ty,
                span,
            };
        }
        // Module-level `const NAME: T = expr;` reference — inline the
        // const's value expression at this use site.
        if let Some(const_expr) = ctx.consts.get(&path.segments[0].name).cloned() {
            return lower_expr(ctx, &const_expr);
        }
        // Module-level `static NAME: T = init;` reference — emits a
        // load through the global address rather than inlining.
        if let Some(ty) = ctx.statics.get(&path.segments[0].name).cloned() {
            return HirExpr {
                kind: HirExprKind::StaticRef(path.segments[0].name.clone()),
                ty,
                span,
            };
        }
    }
    // `EnumName::Variant` (unit form). Tuple variants come through
    // `lower_call` because the parser wraps them in a Call expression.
    if path.segments.len() == 2 {
        // Prefer the expected-type instantiation if one is in scope.
        let mut enum_id_opt: Option<EnumId> = None;
        if let Some(HirTy::Enum(eid)) = ctx.current_expected() {
            let def = &ctx.enums[eid.0 as usize];
            let prefix = format!("{}__", path.segments[0].name);
            if (def.name == path.segments[0].name || def.name.starts_with(&prefix))
                && def.variants.iter().any(|v| v.name == path.segments[1].name)
            {
                enum_id_opt = Some(*eid);
            }
        }
        if enum_id_opt.is_none() {
            enum_id_opt = ctx.enum_table.get(&path.segments[0].name).copied();
        }
        if enum_id_opt.is_none() {
            let prefix = format!("{}__", path.segments[0].name);
            enum_id_opt = ctx
                .enum_table
                .iter()
                .filter(|(k, _)| k.starts_with(&prefix))
                .find_map(|(_, &id)| {
                    let def = &ctx.enums[id.0 as usize];
                    let variant = def.variants.iter().find(|v| v.name == path.segments[1].name)?;
                    if variant.payload_ty.is_none() {
                        Some(id)
                    } else {
                        None
                    }
                });
        }
        if let Some(enum_id) = enum_id_opt {
            let def = &ctx.enums[enum_id.0 as usize];
            if let Some(idx) = def.variants.iter().position(|v| v.name == path.segments[1].name) {
                return HirExpr {
                    kind: HirExprKind::EnumVariantInit {
                        enum_id,
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        args: Vec::new(),
                    },
                    ty: HirTy::Enum(enum_id),
                    span,
                };
            }
        }
    }
    HirExpr {
        kind: HirExprKind::UnresolvedPath(
            path.segments.iter().map(|s| s.name.clone()).collect(),
        ),
        ty: HirTy::Unknown,
        span,
    }
}

fn lower_literal(lit: &AstLit, span: rokc_diagnostic::Span) -> HirExpr {
    match lit {
        AstLit::Int(text) => match parse_int_literal(text) {
            Some((value, ty)) => HirExpr {
                kind: HirExprKind::Const(ConstVal::Int { value, ty }),
                ty: HirTy::Prim(ty),
                span,
            },
            None => HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Unknown,
                span,
            },
        },
        AstLit::Float(text) => match parse_float_literal(text) {
            Some((bits, ty)) => HirExpr {
                kind: HirExprKind::Const(ConstVal::Float { bits, ty }),
                ty: HirTy::Prim(ty),
                span,
            },
            None => HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Unknown,
                span,
            },
        },
        AstLit::Bool(b) => HirExpr {
            kind: HirExprKind::Const(ConstVal::Bool(*b)),
            ty: HirTy::Prim(PrimTy::Bool),
            span,
        },
        AstLit::Str(s) => HirExpr {
            kind: HirExprKind::Const(ConstVal::Str(decode_str_escapes(s))),
            ty: HirTy::Prim(PrimTy::Str),
            span,
        },
        AstLit::RawStr(s) => HirExpr {
            kind: HirExprKind::Const(ConstVal::Str(s.clone())),
            ty: HirTy::Prim(PrimTy::Str),
            span,
        },
        AstLit::None => HirExpr {
            kind: HirExprKind::Const(ConstVal::None),
            ty: HirTy::Path(vec!["none".to_owned()]),
            span,
        },
        AstLit::Char(s) => match parse_char_literal(s) {
            Some(c) => HirExpr {
                kind: HirExprKind::Const(ConstVal::Char(c)),
                ty: HirTy::Prim(PrimTy::CChar),
                span,
            },
            None => HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Unknown,
                span,
            },
        },
        AstLit::CChar(s) => match parse_char_literal(s) {
            Some(c) => HirExpr {
                kind: HirExprKind::Const(ConstVal::Char(c)),
                ty: HirTy::Prim(PrimTy::CChar),
                span,
            },
            None => HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: HirTy::Unknown,
                span,
            },
        },
        AstLit::FStr(_) => HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: HirTy::Unknown,
            span,
        },
    }
}

// `'A'` lexer payload is the character text (without quotes). Decode the
// first escape sequence or return the char's codepoint.
fn parse_char_literal(text: &str) -> Option<u32> {
    let mut chars = text.chars();
    let first = chars.next()?;
    if first != '\\' {
        if chars.next().is_some() {
            return None;
        }
        return Some(first as u32);
    }
    match chars.next()? {
        'n' => Some(0x0A),
        't' => Some(0x09),
        'r' => Some(0x0D),
        '\\' => Some(0x5C),
        '\'' => Some(0x27),
        '"' => Some(0x22),
        '0' => Some(0x00),
        _ => None,
    }
}

/// Parse an integer literal. Bare (unsuffixed) integer literals fall
/// back to `i32` — the most common integer type in rok programs.
fn parse_int_literal(text: &str) -> Option<(i128, PrimTy)> {
    const SUFFIXES: &[(&str, PrimTy)] = &[
        ("isize", PrimTy::Isize),
        ("usize", PrimTy::Usize),
        ("i64", PrimTy::I64),
        ("u64", PrimTy::U64),
        ("i32", PrimTy::I32),
        ("u32", PrimTy::U32),
        ("i16", PrimTy::I16),
        ("u16", PrimTy::U16),
        ("i8", PrimTy::I8),
        ("u8", PrimTy::U8),
    ];

    let (digits, ty) = SUFFIXES
        .iter()
        .find_map(|(suf, ty)| text.strip_suffix(suf).map(|d| (d, *ty)))
        .unwrap_or((text, PrimTy::I32));

    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    let (radix, body) = if let Some(rest) = cleaned.strip_prefix("0x").or_else(|| cleaned.strip_prefix("0X")) {
        (16u32, rest.to_owned())
    } else if let Some(rest) = cleaned.strip_prefix("0b").or_else(|| cleaned.strip_prefix("0B")) {
        (2u32, rest.to_owned())
    } else if let Some(rest) = cleaned.strip_prefix("0o").or_else(|| cleaned.strip_prefix("0O")) {
        (8u32, rest.to_owned())
    } else {
        (10u32, cleaned)
    };

    let value = i128::from_str_radix(&body, radix).ok()?;
    Some((value, ty))
}

fn parse_float_literal(text: &str) -> Option<(u64, PrimTy)> {
    const SUFFIXES: &[(&str, PrimTy)] = &[("f32", PrimTy::F32), ("f64", PrimTy::F64)];
    let (digits, ty) = SUFFIXES
        .iter()
        .find_map(|(suf, ty)| text.strip_suffix(suf).map(|d| (d, *ty)))
        .unwrap_or((text, PrimTy::F64));

    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    let bits = match ty {
        PrimTy::F32 => u64::from(cleaned.parse::<f32>().ok()?.to_bits()),
        _ => cleaned.parse::<f64>().ok()?.to_bits(),
    };
    Some((bits, ty))
}

/// Lowering context: scoped name → local-id map plus the running list of
/// local declarations. Carries the module-level function table so call
/// sites can resolve callees by name without a full resolver pass.
/// Shared mutable sink for closures lifted into anonymous top-level
/// functions, and for generic-function monomorphizations. Lowering
/// pushes here as it walks expressions.
struct ClosureSink {
    extras: std::cell::RefCell<Vec<HirFunction>>,
    next_id: std::cell::Cell<u32>,
    /// Cached monomorphizations: `(generic_fn_name, concrete_type_args)`
    /// → specialized `FunctionId`.
    mono_cache: std::cell::RefCell<HashMap<(String, Vec<String>), FunctionId>>,
    /// Specialized `FnSig` per monomorphization for call-site lookup.
    mono_sigs: std::cell::RefCell<HashMap<FunctionId, FnSig>>,
    /// Diagnostics emitted during lowering — surfaced through
    /// `HirModule.diagnostics` so the driver can fail the build on
    /// errors (visibility violations, glob conflicts, ...).
    diagnostics: std::cell::RefCell<Vec<rokc_diagnostic::RokDiagnostic>>,
}

struct LowerCtx<'a> {
    locals: Vec<HirLocal>,
    scopes: Vec<HashMap<String, LocalId>>,
    fn_table: &'a HashMap<String, FnSig>,
    method_table: &'a HashMap<(MethodTarget, String), FunctionId>,
    structs: &'a [HirStructDef],
    enums: &'a [HirEnumDef],
    struct_table: &'a HashMap<String, StructId>,
    enum_table: &'a HashMap<String, EnumId>,
    /// Module-level `const NAME: T = expr;` items. A bare `Path(NAME)`
    /// resolves to the const's value expression inlined at the use site.
    consts: &'a HashMap<String, Expr>,
    /// Module-level type aliases. Walked over every `HirTy` produced
    /// from AST resolution so downstream code never sees `Path([alias])`.
    type_aliases: &'a HashMap<String, HirTy>,
    /// Per-monomorphization type-parameter substitution. Empty for
    /// non-generic functions. `T` → concrete `HirTy` overrides the
    /// alias table when both contain the same name.
    ty_subst: &'a HashMap<String, HirTy>,
    /// Generic function templates keyed by name. lower_call queries
    /// this when the callee path matches a generic function.
    generic_fns: &'a HashMap<String, &'a FnDef>,
    self_ty: Option<HirTy>,
    prec: &'a PrecTable,
    sink: &'a ClosureSink,
    /// Enclosing function's return type. `return v;` wraps `v` into a
    /// matching sum type when the return type names one.
    fn_ret_ty: HirTy,
    /// Stack of expected types pushed by let/assign/return so leaf
    /// lowerings (e.g. `Box::None`) can pick the right instantiation
    /// when multiple match the bare name.
    expected_ty_stack: Vec<HirTy>,
    /// Module path of the function currently being lowered, joined with
    /// `::`. Empty string for free functions in the package root.
    /// Path resolution prepends this to bare-name lookups so a function
    /// inside `mod inner { ... }` resolves siblings without qualification.
    current_module: String,
    /// Visibility of every registered fn (both free and methods), keyed
    /// by the fn's full name (mangled with `::` for module path). Empty
    /// when the fn predates the visibility-tracking pass.
    item_visibility: &'a HashMap<String, Visibility>,
    /// Per-module `use` table — feeds into bare-name and unresolved
    /// path lookups. Empty when no `use` declarations were collected.
    uses: &'a crate::uses::UseTable,
    /// Set of `(Type, TraitName)` pairs declared by `impl Trait for Type`
    /// blocks. Consulted at monomorphization time to enforce generic
    /// trait bounds.
    impl_traits: &'a std::collections::HashSet<(MethodTarget, String)>,
    /// Module-level `static` items by name → declared type. Used by
    /// `lower_path` to emit a `StaticRef` (read) and by lower_stmt's
    /// assign path to emit a `StaticAssign` (write).
    statics: &'a HashMap<String, HirTy>,
    /// Function-/block-scoped `use` entries. Mirrors `scopes`: each
    /// `push_scope` pushes an empty Vec, `pop_scope` pops it. Resolution
    /// walks this stack top-down before consulting module-level uses.
    local_uses: Vec<Vec<crate::uses::UseEntry>>,
    /// Or-pattern shared binders. Each Or-pattern lowering pushes a map
    /// of `name → preset LocalId` so each alternative's `Binding` reuses
    /// the same local instead of allocating a fresh one. Spec 3.11.4 —
    /// `E::A(x) | E::B(x)` must bind `x` once, with consistent type.
    or_pattern_binders: Vec<HashMap<String, LocalId>>,
}

impl<'a> LowerCtx<'a> {
    fn new(
        fn_table: &'a HashMap<String, FnSig>,
        method_table: &'a HashMap<(MethodTarget, String), FunctionId>,
        structs: &'a [HirStructDef],
        enums: &'a [HirEnumDef],
        struct_table: &'a HashMap<String, StructId>,
        enum_table: &'a HashMap<String, EnumId>,
        consts: &'a HashMap<String, Expr>,
        type_aliases: &'a HashMap<String, HirTy>,
        ty_subst: &'a HashMap<String, HirTy>,
        generic_fns: &'a HashMap<String, &'a FnDef>,
        self_ty: Option<HirTy>,
        prec: &'a PrecTable,
        sink: &'a ClosureSink,
        item_visibility: &'a HashMap<String, Visibility>,
        uses: &'a crate::uses::UseTable,
        impl_traits: &'a std::collections::HashSet<(MethodTarget, String)>,
        statics: &'a HashMap<String, HirTy>,
    ) -> Self {
        Self {
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            fn_table,
            method_table,
            structs,
            enums,
            struct_table,
            enum_table,
            consts,
            type_aliases,
            ty_subst,
            generic_fns,
            self_ty,
            prec,
            sink,
            fn_ret_ty: HirTy::Unit,
            expected_ty_stack: Vec::new(),
            current_module: String::new(),
            item_visibility,
            uses,
            local_uses: vec![Vec::new()],
            impl_traits,
            statics,
            or_pattern_binders: Vec::new(),
        }
    }

    /// Push a lowering-time diagnostic onto the shared sink. Drained
    /// into `HirModule.diagnostics` at the end of the lower pass.
    fn emit_error(&self, kind: rokc_diagnostic::ErrorKind, msg: String) {
        self.sink
            .diagnostics
            .borrow_mut()
            .push(rokc_diagnostic::RokDiagnostic::error(kind, msg));
    }

    /// Resolve a callee name (single- or multi-segment path) to a fully
    /// qualified fn-table key. Tries the absolute path first, then
    /// re-roots under the caller's current module and walks up its
    /// ancestors, then consults the caller module's `use` entries.
    /// Returns `None` if no resolution found. Glob ambiguities (5.5.6 /
    /// 5.5.12) emit a diagnostic and pick the first candidate.
    fn resolve_fn_name(&self, segments: &[&str]) -> Option<String> {
        // Spec 5.7.2/5.7.3: `pkg::a::b` is package-root absolute,
        // `sup::a` walks one parent module up. Resolve those root forms
        // first so the rest of the lookup just sees ordinary module
        // segments.
        let resolved_segs: Vec<&str> = match segments.first().copied() {
            Some("pkg") => segments[1..].to_vec(),
            Some("sup") => {
                let mut parts: Vec<&str> = if self.current_module.is_empty() {
                    Vec::new()
                } else {
                    self.current_module.split("::").collect()
                };
                let mut i = 0;
                while i < segments.len() && segments[i] == "sup" {
                    if !parts.is_empty() {
                        parts.pop();
                    }
                    i += 1;
                }
                parts.extend(segments[i..].iter().copied());
                parts
            }
            _ => segments.to_vec(),
        };
        let segments = resolved_segs.as_slice();
        let suffix = segments.join("::");
        if self.fn_table.contains_key(&suffix) {
            return Some(suffix);
        }
        // Walk caller's module-path ancestors (longest prefix first).
        let mut cur: Vec<&str> = if self.current_module.is_empty() {
            Vec::new()
        } else {
            self.current_module.split("::").collect()
        };
        loop {
            if !cur.is_empty() {
                let mut candidate = cur.join("::");
                candidate.push_str("::");
                candidate.push_str(&suffix);
                if self.fn_table.contains_key(&candidate) {
                    return Some(candidate);
                }
            }
            if cur.is_empty() {
                break;
            }
            cur.pop();
        }
        // Function-local `use` entries first (innermost scope wins),
        // then the module-level table. Detect ambiguous glob hits.
        let try_set = |entries: &[crate::uses::UseEntry]| -> LookupOutcome {
            lookup_in_use_entries_full(entries, segments, &suffix, self.fn_table)
        };
        for scope in self.local_uses.iter().rev() {
            match try_set(scope) {
                LookupOutcome::Resolved(s) => return Some(s),
                LookupOutcome::Ambiguous(hits) => {
                    self.report_ambiguous(&suffix, &hits);
                    return Some(hits.into_iter().next().unwrap());
                }
                LookupOutcome::None => {}
            }
        }
        if let Some(entries) = self.uses.get(&self.current_module) {
            match try_set(entries) {
                LookupOutcome::Resolved(s) => return Some(s),
                LookupOutcome::Ambiguous(hits) => {
                    self.report_ambiguous(&suffix, &hits);
                    return Some(hits.into_iter().next().unwrap());
                }
                LookupOutcome::None => {}
            }
        }
        None
    }

    fn report_ambiguous(&self, name: &str, hits: &[String]) {
        let where_ = if self.current_module.is_empty() {
            "<root>".to_owned()
        } else {
            self.current_module.clone()
        };
        self.emit_error(
            rokc_diagnostic::ErrorKind::Module,
            format!(
                "name `{name}` is ambiguous in module `{where_}` — multiple glob imports \
                 resolve it: {}",
                hits.join(", ")
            ),
        );
    }


    /// Visibility check: can a caller in `self.current_module` see an
    /// item declared in `def_module` with the given visibility?
    fn is_visible(&self, def_module: &str, vis: Visibility) -> bool {
        match vis {
            // Single-package compilation today: everything reaching out
            // (Pub) or staying within the package (Pkg) is reachable.
            Visibility::Pub | Visibility::Pkg => true,
            Visibility::Sub => {
                if def_module.is_empty() {
                    return true;
                }
                self.current_module == def_module
                    || self
                        .current_module
                        .starts_with(&format!("{def_module}::"))
            }
            Visibility::Private => self.current_module == def_module,
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
    /// monomorphization substitution and module-level alias map.
    fn resolve_ast_ty(&self, ty: &rokc_ast::Ty) -> HirTy {
        // For `Pair<T>` paths, substitute `T` in the generic args
        // up front so we can look up the right mangled instantiation.
        if let rokc_ast::TyKind::Path(p) = &ty.kind {
            if p.segments.len() == 1 && !p.segments[0].generics.is_empty() {
                let resolved_args: Vec<HirTy> = p.segments[0]
                    .generics
                    .iter()
                    .map(|g| self.resolve_ast_ty(g))
                    .collect();
                let mangled = format!(
                    "{}__{}",
                    p.segments[0].name,
                    resolved_args.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
                );
                if let Some(id) = self.struct_table.get(&mangled) {
                    return HirTy::Struct(*id);
                }
                if let Some(id) = self.enum_table.get(&mangled) {
                    return HirTy::Enum(*id);
                }
            }
        }
        let mut t = resolve_ty_with_structs(ty, self.struct_table, self.enum_table);
        substitute_aliases(&mut t, self.ty_subst);
        substitute_aliases(&mut t, self.type_aliases);
        t
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

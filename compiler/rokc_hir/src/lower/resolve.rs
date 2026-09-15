//! Name resolution: the module-aware path resolver shared by the value
//! and type namespaces, visibility, and AST type → `HirTy` resolution.

#[allow(clippy::wildcard_imports)]
use super::*;

/// The module path of `module::path::name` (`""` at the package root).
pub(super) fn module_of(name: &str) -> String {
    match name.rsplit_once("::") {
        Some((mod_path, _)) => mod_path.to_owned(),
        None => String::new(),
    }
}

pub(super) fn lookup_in_use_entries_full(
    entries: &[crate::uses::UseEntry],
    segments: &[&str],
    suffix: &str,
    set: &NameSet<'_>,
) -> LookupOutcome {
    let mut glob_hits: Vec<String> = Vec::new();
    for entry in entries {
        match entry {
            crate::uses::UseEntry::Single { local, full } => {
                if segments.len() == 1 && segments[0] == local && (set.exists)(full) {
                    return LookupOutcome::Resolved(full.clone());
                }
                // `use foo::bar` lets `bar::baz` resolve as `foo::bar::baz`.
                if !segments.is_empty() && segments[0] == local {
                    let mut joined = full.clone();
                    for s in &segments[1..] {
                        joined.push_str("::");
                        joined.push_str(s);
                    }
                    if (set.exists)(&joined) {
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
                if (set.exists)(&candidate)
                    && (set.visible)(&candidate)
                    && !glob_hits.contains(&candidate)
                {
                    glob_hits.push(candidate);
                }
            }
            crate::uses::UseEntry::GlobDeep { prefix } => {
                let direct = if prefix.is_empty() {
                    suffix.to_owned()
                } else {
                    format!("{prefix}::{suffix}")
                };
                if (set.exists)(&direct) && (set.visible)(&direct) && !glob_hits.contains(&direct) {
                    glob_hits.push(direct);
                    continue;
                }
                let prefix_with_sep = if prefix.is_empty() {
                    String::new()
                } else {
                    format!("{prefix}::")
                };
                let suffix_with_sep = format!("::{suffix}");
                let leaf = suffix.rsplit("::").next().unwrap_or(suffix);
                for key in (set.keys)(leaf) {
                    if key.starts_with(&prefix_with_sep)
                        && key.ends_with(&suffix_with_sep)
                        && (set.visible)(&key)
                        && !glob_hits.contains(&key)
                    {
                        glob_hits.push(key);
                    }
                }
            }
        }
    }
    // Deterministic order regardless of HashMap iteration.
    glob_hits.sort();
    match glob_hits.len() {
        0 => LookupOutcome::None,
        1 => LookupOutcome::Resolved(glob_hits.remove(0)),
        _ => LookupOutcome::Ambiguous(glob_hits),
    }
}

/// Module-aware path resolution shared by the value (fn) and type
/// namespaces. Order: `pkg::` / `sup::` / `rok::` roots are absolute;
/// otherwise the current module (no ancestor walk, spec 5.7); then
/// function-local `use`s (innermost scope first); then the module-level
/// `use` table. `Err(hits)` = ambiguous glob import (hits sorted).
pub(super) fn resolve_name(
    segments: &[&str],
    module: &str,
    local_uses: &[Vec<crate::uses::UseEntry>],
    uses: &crate::uses::UseTable,
    set: &NameSet<'_>,
) -> Result<Option<String>, Vec<String>> {
    // A lone `pkg` / `sup` / `rok` is an ordinary name (`fn sup()`); as
    // a path root it needs something after it.
    let rooted = root_path(segments, module).filter(|_| segments.len() > 1);
    if segments.first() == Some(&"sup") {
        if let Some(p) = rooted {
            return Ok(Some(p.join("::")).filter(|k| (set.exists)(k)));
        }
    }
    let absolute = rooted.is_some();
    let resolved: Vec<String> =
        rooted.unwrap_or_else(|| segments.iter().map(|s| (*s).to_owned()).collect());
    let resolved_segs: Vec<&str> = resolved.iter().map(String::as_str).collect();
    let segments = resolved_segs.as_slice();
    let suffix = segments.join("::");
    // Spec 5.7: no implicit ancestor walk — the current module (its items
    // and child modules), then the `rok::` virtual root; parents need
    // `sup::` or a `use`.
    let candidate = if module.is_empty() || absolute {
        suffix.clone()
    } else {
        format!("{module}::{suffix}")
    };
    if (set.exists)(&candidate) {
        return Ok(Some(candidate));
    }
    // A dependency's name is a top-level name in every module (902.3).
    if !absolute && segments.first().is_some_and(|s| is_dependency(s)) && (set.exists)(&suffix) {
        return Ok(Some(suffix));
    }
    for scope in local_uses.iter().rev() {
        match lookup_in_use_entries_full(scope, segments, &suffix, set) {
            LookupOutcome::Resolved(s) => return Ok(Some(s)),
            LookupOutcome::Ambiguous(hits) => return Err(hits),
            LookupOutcome::None => {}
        }
    }
    if let Some(entries) = uses.get(module) {
        match lookup_in_use_entries_full(entries, segments, &suffix, set) {
            LookupOutcome::Resolved(s) => return Ok(Some(s)),
            LookupOutcome::Ambiguous(hits) => return Err(hits),
            LookupOutcome::None => {}
        }
    }
    // Every module has an implicit `use rok::core::**;` (stdlib spec 0.1),
    // consulted last so the module's own names and imports shadow it.
    let core = [crate::uses::UseEntry::GlobDeep {
        prefix: CORE_PREFIX.to_owned(),
    }];
    match lookup_in_use_entries_full(&core, segments, &suffix, set) {
        LookupOutcome::Resolved(s) => Ok(Some(s)),
        LookupOutcome::Ambiguous(hits) => Err(hits),
        LookupOutcome::None => Ok(None),
    }
}

/// The absolute path a rooted path names from `module` (spec 5.7):
/// `pkg::` starts at the package root (a dependency's own inside it),
/// each leading `sup::` goes up one module, `rok::` is absolute. `None`
/// for any other first segment. Shared by expression / type paths and
/// `use` trees.
pub fn root_path(segments: &[&str], module: &str) -> Option<Vec<String>> {
    let owned = |s: &[&str]| s.iter().map(|x| (*x).to_owned()).collect::<Vec<_>>();
    match *segments.first()? {
        "pkg" => {
            let package = package_of(module);
            let mut out = Vec::new();
            if is_dependency(&package) {
                out.push(package);
            }
            out.extend(owned(&segments[1..]));
            Some(out)
        }
        "sup" => {
            let mut parts: Vec<String> = if module.is_empty() {
                Vec::new()
            } else {
                module.split("::").map(str::to_owned).collect()
            };
            let ups = segments.iter().take_while(|s| **s == "sup").count();
            for _ in 0..ups {
                parts.pop();
            }
            parts.extend(owned(&segments[ups..]));
            Some(parts)
        }
        "rok" => Some(owned(segments)),
        _ => None,
    }
}

/// The compiler-known GC buffer type (`HirTy::GcBuf`), declared in core
/// so the name resolves.
pub const GC_BUF: &str = "rok::core::collections::raw::GcBuf";
pub const MLIR_TYPE: &str = "rok::bare::mlir::__mlir_type";

/// Core traits the compiler names that have no lang slot (stdlib 0.4).
pub const COPY_TRAIT: &str = "rok::core::marker::Copy";
pub const EQ_TRAIT: &str = "rok::core::cmp::Eq";
pub const DEFAULT_TRAIT: &str = "rok::core::marker::Default";

/// A string literal (`"arith.addi"`), as a const type argument or an
/// expression.
pub(super) fn str_lit_of(e: &rokc_ast::Expr) -> Option<&str> {
    match &e.kind {
        rokc_ast::ExprKind::Literal(rokc_ast::Literal::Str(s) | rokc_ast::Literal::RawStr(s)) => {
            Some(s)
        }
        _ => None,
    }
}

pub(super) fn str_targ(t: &rokc_ast::Ty) -> Option<&str> {
    match &t.kind {
        AstTyKind::Const(rokc_ast::ConstExpr::Expr(e)) => str_lit_of(e),
        AstTyKind::Const(rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Str(s))) => Some(s),
        _ => None,
    }
}

/// `__mlir_type<"text">` (stdlib bare 1.9): an opaque MLIR type.
pub(super) fn mlir_ty(full: &str, generics: &[rokc_ast::Ty]) -> Option<HirTy> {
    match (full, generics) {
        (MLIR_TYPE, [t]) => str_targ(t).map(|s| HirTy::Mlir(s.to_owned())),
        _ => None,
    }
}

/// Module path the driver mounts `library/core` under.
pub const CORE_PREFIX: &str = "rok::core";

/// Can code in `cur_module` see an item declared in `def_module` with
/// visibility `vis`? (spec 5.6)
pub(super) fn visible_from(cur_module: &str, def_module: &str, vis: Visibility) -> bool {
    match vis {
        Visibility::Pub => true,
        // Spec 5.6.4: the package the item is declared in.
        Visibility::Pkg => package_of(cur_module) == package_of(def_module),
        Visibility::Sub => {
            package_of(cur_module) == package_of(def_module)
                && (def_module.is_empty()
                    || cur_module == def_module
                    || cur_module.starts_with(&format!("{def_module}::")))
        }
        // Spec 5.6.2: no keyword = visible in the declaring module only.
        Visibility::Private => cur_module == def_module,
    }
}

thread_local! {
    /// The dependency packages' top-level names (`HirInput::packages`), set
    /// by `lower_full` for the program being lowered.
    static PACKAGES: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
}

pub fn set_packages(names: Vec<String>) {
    PACKAGES.with(|p| *p.borrow_mut() = names);
}

pub fn is_dependency(name: &str) -> bool {
    PACKAGES.with(|p| p.borrow().iter().any(|n| n == name))
}

/// The package `module` belongs to: `rok::<tier>` (each library tier is
/// its own package, spec 5.7), a dependency's name, or `""` — the
/// package being compiled.
pub(super) fn package_of(module: &str) -> String {
    let mut parts = module.split("::");
    match parts.next() {
        Some("rok") => format!("rok::{}", parts.next().unwrap_or_default()),
        Some(first) if is_dependency(first) => first.to_owned(),
        _ => String::new(),
    }
}

pub(super) const fn module_display(m: &str) -> &str {
    if m.is_empty() { "<root>" } else { m }
}

/// Module path → visibility of its `mod`, from the flattened
/// module stubs (`Item::Mod` named by its full path).
pub fn module_visibility(items: &[Item]) -> HashMap<String, Visibility> {
    items
        .iter()
        .filter_map(|i| match i {
            Item::Mod(m) => Some((m.name.clone(), m.vis)),
            _ => None,
        })
        .collect()
}

/// Spec 5.6.2 / 5.6.13: the first module on `full`'s path that code in
/// `cur` can't see (a module is visible inside itself and below).
pub fn hidden_module(
    mod_vis: &HashMap<String, Visibility>,
    cur: &str,
    full: &str,
) -> Option<String> {
    let def = module_of(full);
    def.match_indices("::")
        .map(|(i, _)| &def[..i])
        .chain((!def.is_empty()).then_some(def.as_str()))
        .filter(|m| cur != *m && !cur.starts_with(&format!("{m}::")))
        .find(|m| {
            // A private module is visible throughout its parent.
            let vis = |v| match v {
                Visibility::Private => Visibility::Sub,
                v => v,
            };
            mod_vis
                .get(*m)
                .is_some_and(|&v| !visible_from(cur, &module_of(m), vis(v)))
        })
        .map(str::to_owned)
}

pub fn hidden_module_msg(full: &str, module: &str, cur: &str) -> String {
    format!(
        "`{full}` is not visible from `{}`: module `{module}` is private to `{}` \
         (spec 5.6.13 — add `pub` to the `mod` to expose it)",
        module_display(cur),
        module_display(&module_of(module))
    )
}

/// Order of reach for spec 5.8.4: a re-export may not be wider than its
/// item.
pub const fn visibility_rank(v: Visibility) -> u8 {
    match v {
        Visibility::Private => 0,
        Visibility::Sub => 1,
        Visibility::Pkg => 2,
        Visibility::Pub => 3,
    }
}

/// Module path of an item after the driver flattened the module tree
/// (`a::b::name` → `a::b`). Impl blocks carry it on their methods.
pub(super) fn item_module(item: &Item) -> String {
    match item {
        Item::Fn(f) => module_of(&f.name),
        Item::Struct(s) => module_of(&s.name),
        Item::Enum(e) => module_of(&e.name),
        Item::Union(u) => module_of(&u.name),
        Item::Const(c) => module_of(&c.name),
        Item::Static(s) => module_of(&s.name),
        Item::TypeAlias(a) => module_of(&a.name),
        Item::Trait(t) => module_of(&t.name),
        Item::Impl(i) => impl_module(i),
        _ => String::new(),
    }
}

pub(super) fn impl_module(i: &rokc_ast::ImplDef) -> String {
    i.module.clone()
}

/// Leaf of a driver-qualified name (`a::b::f` → `f`).
pub(super) fn leaf_name(name: &str) -> &str {
    name.rsplit_once("::").map_or(name, |(_, l)| l)
}

/// Map a runtime `HirTy` to the `MethodTarget` used in `method_table`
/// keys. Mirrors `impl_target_key`'s strategy: direct mapping for
/// Struct/Enum, mangled fallback for everything else.
pub(super) fn method_target_for(ty: &HirTy) -> Option<MethodTarget> {
    match ty {
        HirTy::Struct(id) => Some(MethodTarget::Struct(*id)),
        HirTy::Enum(id) => Some(MethodTarget::Enum(*id)),
        HirTy::Unknown => None,
        other => Some(MethodTarget::Mangled(ty_mangle(other))),
    }
}

/// Replace the generic parameters (and `Self`) `params` binds in `ty`:
/// a parameter bound to a sum with `none` stays one member of a sum
/// that has its own `none` — `T | none` with `T = i32 | none` is the
/// nested optional `(i32 | none)?` (spec 2.6.4).
pub(super) fn substitute_params(ty: &mut HirTy, params: &HashMap<String, HirTy>) {
    let rec = |t: &mut HirTy| substitute_params(t, params);
    match ty {
        HirTy::Path(parts) => {
            if parts.len() == 1 {
                if let Some(replacement) = params.get(&parts[0]) {
                    *ty = replacement.clone();
                }
            }
        }
        HirTy::Sum(parts) => {
            // A parameter may have become a sum (or a member already
            // present): back to the canon.
            parts.iter_mut().for_each(rec);
            *ty = HirTy::sum(std::mem::take(parts));
        }
        HirTy::Tuple(parts) => parts.iter_mut().for_each(rec),
        HirTy::Array(elem, _) | HirTy::GcBuf(elem) => rec(elem),
        HirTy::Fn(args, ret, _) | HirTy::Closure { args, ret, .. } => {
            args.iter_mut().for_each(rec);
            rec(ret);
        }
        // Re-normalize: a `rethrows` error parameter may have become
        // "no error".
        HirTy::Throws { ok, err } => {
            rec(ok);
            rec(err);
            *ty = crate::ty::throws_ty((**ok).clone(), (**err).clone());
        }
        _ => {}
    }
}

/// Instance `full<args>` of a generic struct or enum (made on first use,
/// its field types resolved under the instance's substitution in the
/// template's module, their errors at `sc.at`). `None` while an argument
/// is not concrete (an unbound parameter, an unknown name).
pub(super) fn instance(
    defs: &TypeDefs<'_>,
    full: &str,
    args: Vec<HirTy>,
    sc: Scope<'_>,
    span: rokc_diagnostic::Span,
) -> Option<HirTy> {
    let mut open = Vec::new();
    args.iter()
        .for_each(|a| collect::collect_unknown_paths(a, &mut open));
    if !open.is_empty() || args.contains(&HirTy::Unknown) {
        return None;
    }
    let module = module_of(full);
    let sc = Scope {
        module: &module,
        ..sc
    };
    if defs.generic_structs.contains_key(full) {
        return defs
            .instantiate_struct(full, args, span, |def, subst| {
                mono::generic_struct_fields(def, &|t| {
                    resolve_ty_with_structs(t, defs, Some(subst), sc)
                })
            })
            .map(HirTy::Struct);
    }
    defs.instantiate_enum(full, args, span, |def, subst| {
        mono::generic_enum_variants(def, &|t| resolve_ty_with_structs(t, defs, Some(subst), sc))
    })
    .map(HirTy::Enum)
}

/// `resolve_ty` plus module-aware struct / enum / alias name lookup, a
/// generic one instantiated (spec 2.10); `params` binds generic
/// parameters by name (a generic instance's field types). Unresolvable
/// names stay `HirTy::Path` (reported by `check_unresolved_types` if they
/// survive).
pub(super) fn resolve_ty_with_structs(
    ty: &rokc_ast::Ty,
    defs: &TypeDefs<'_>,
    params: Option<&TySubst>,
    sc: Scope<'_>,
) -> HirTy {
    let rec = |t: &rokc_ast::Ty| resolve_ty_with_structs(t, defs, params, sc);
    match &ty.kind {
        AstTyKind::Path(p) => {
            if let ([seg], Some(params)) = (p.segments.as_slice(), params) {
                if let Some(t) = params.get(&seg.name).filter(|_| seg.generics.is_empty()) {
                    return t.clone();
                }
            }
            let prim = resolve_ty(ty);
            if matches!(prim, HirTy::Prim(_)) {
                return prim;
            }
            if let Some(t) = sc.names.expand_alias(ty, sc.module, sc.at) {
                return rec(&t);
            }
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            let generics = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
            let Some(full) = sc.names.canon(&segs, sc.module, &[], sc.at) else {
                if !p.span.is_dummy() {
                    sc.names
                        .unknown_spans
                        .borrow_mut()
                        .entry(segs.join("::"))
                        .or_insert(p.span);
                }
                return HirTy::Path(segs.iter().map(|s| (*s).to_owned()).collect());
            };
            if sc.names.traits.contains(&full) {
                let written = segs.join("::");
                sc.names.error_help(
                    sc.at,
                    format!("trait `{full}` cannot be used as a type directly"),
                    format!(
                        "use `any {written}` for a value of any type implementing it, or a \
                         generic parameter `<T: {written}>`"
                    ),
                );
                return HirTy::Any;
            }
            if let (GC_BUF, [elem]) = (full.as_str(), generics) {
                return HirTy::GcBuf(Box::new(rec(elem)));
            }
            if let Some(t) = mlir_ty(&full, generics) {
                return t;
            }
            if generics.is_empty() {
                // Depth-capped: a cyclic alias stays a path and is
                // reported by the alias pass.
                if let Some(t) = sc
                    .names
                    .plain_aliases
                    .get(&full)
                    .filter(|_| sc.names.alias_depth.get() < 32)
                {
                    let module = module_of(&full);
                    let inner = Scope {
                        module: &module,
                        ..sc
                    };
                    let depth = &sc.names.alias_depth;
                    depth.set(depth.get() + 1);
                    let r = resolve_ty_with_structs(t, defs, None, inner);
                    depth.set(depth.get() - 1);
                    return r;
                }
            }
            if !generics.is_empty() {
                let args: Vec<HirTy> = generics.iter().map(rec).collect();
                return instance(defs, &full, args, sc, ty.span)
                    .unwrap_or_else(|| HirTy::Path(vec![full]));
            }
            if let Some(id) = defs.struct_id(&full) {
                return HirTy::Struct(id);
            }
            if let Some(id) = defs.enum_id(&full) {
                return HirTy::Enum(id);
            }
            // Type alias (substituted later) or a generic base used
            // without arguments.
            HirTy::Path(vec![full])
        }
        AstTyKind::Array(elem, len) => {
            // `[T; N]` / `[T; M * N]` under bound const parameters.
            let n = params
                .and_then(|ps| {
                    super::const_eval::syntactic_int(len, &|name| {
                        ps.get(name).and_then(HirTy::as_const).map(|c| c.0)
                    })
                })
                .or_else(|| sc.names.const_int(len, sc.module))
                .and_then(|n| u32::try_from(n).ok());
            let Some(n) = n else {
                // Located at the type: field types resolve outside any item pass.
                let at = if ty.span.is_dummy() { sc.at } else { ty.span };
                sc.names.error(
                    at,
                    "array length must be a compile-time integer (spec 2.11.5)".to_owned(),
                );
                return HirTy::Any;
            };
            HirTy::Array(Box::new(rec(elem)), n)
        }
        // `T | U` — recurse so Path("Counter") resolves to Struct(id), not
        // an opaque path the MIR layer would treat as `Any`.
        AstTyKind::Sum(parts) => {
            crate::ty::written_sum(parts, |n| params.is_some_and(|ps| ps.contains_key(n)), rec)
        }
        AstTyKind::Nest(x) => rec(x),
        AstTyKind::Tuple(parts) if parts.is_empty() => HirTy::Unit,
        AstTyKind::Tuple(parts) => HirTy::Tuple(parts.iter().map(rec).collect()),
        AstTyKind::Fn(args, ret, b) => HirTy::Fn(
            args.iter().map(rec).collect(),
            Box::new(rec(ret)),
            sc.names.fn_bounds(b, sc.module, sc.at),
        ),
        AstTyKind::AnyTrait(bounds) => {
            let mut refs = Vec::with_capacity(bounds.len());
            for b in bounds {
                let segs: Vec<&str> = b.segments.iter().map(|s| s.name.as_str()).collect();
                let key = sc.names.trait_key(&segs, sc.module, sc.at);
                let user_trait = sc.names.traits.contains(&key);
                // Bootstrap traits key by their last segment (see
                // `trait_key`); anything else must name a declared trait.
                if !user_trait && !sc.names.traits.iter().any(|t| leaf_name(t) == key) {
                    sc.names.error(
                        sc.at,
                        format!(
                            "`{}` in `any {}` is not a trait — `any` bounds must name traits",
                            segs.join("::"),
                            segs.join("::")
                        ),
                    );
                    return HirTy::Unknown;
                }
                refs.push(trait_ref(sc.names, b, sc.module, sc.at, rec));
            }
            HirTy::any(refs)
        }
        AstTyKind::Throws { ok, err } => crate::ty::throws_ty(rec(ok), rec(err)),
        _ => resolve_ty(ty),
    }
}

/// Trait path `p` as written in `module` (`Get<i32, Item = u8>`), its
/// type arguments resolved by `rec`; its errors go to `at`.
pub(super) fn trait_ref(
    names: &TypeNames<'_>,
    p: &rokc_ast::Path,
    module: &str,
    at: rokc_diagnostic::Span,
    rec: impl FnMut(&rokc_ast::Ty) -> HirTy,
) -> TraitRef {
    let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
    let generics = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
    let (args, binds) = trait_args(generics, rec);
    TraitRef::new(names.trait_key(&segs, module, at), args, binds)
}

/// A trait path's generic arguments: positional ones and `Name = Ty`
/// associated-type bindings, each resolved by `rec`.
pub(super) fn trait_args(
    generics: &[rokc_ast::Ty],
    mut rec: impl FnMut(&rokc_ast::Ty) -> HirTy,
) -> (Vec<HirTy>, Vec<(String, HirTy)>) {
    let mut args = Vec::new();
    let mut binds = Vec::new();
    for g in generics {
        match rokc_ast::as_assoc_binding(g) {
            Some((n, t)) => binds.push((n.to_owned(), rec(t))),
            None => args.push(rec(g)),
        }
    }
    (args, binds)
}

/// Table key of a generic instantiation: `a::Pair` + `[i32, bool]` →
/// `a::Pair__i32_bool`.
pub(super) fn mangle_inst(base: &str, args: &[HirTy]) -> String {
    format!(
        "{base}__{}",
        args.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
    )
}

pub(super) fn ty_mangle(ty: &HirTy) -> String {
    match ty {
        HirTy::GcBuf(t) => format!("GcBuf{}", ty_mangle(t)),
        HirTy::Never => "Never".to_owned(),
        HirTy::Mlir(t) => format!(
            "Mlir{}",
            t.chars()
                .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
                .collect::<String>()
        ),
        HirTy::Struct(id) => format!("Struct{}", id.0),
        HirTy::Enum(id) => format!("Enum{}", id.0),
        HirTy::Prim(p) => p.name().to_owned(),
        HirTy::Unit => "Unit".to_owned(),
        HirTy::Any => "Any".to_owned(),
        HirTy::AnyTrait(bounds) => {
            let keys: Vec<String> = bounds
                .iter()
                .map(|b| b.render(&b.path, ty_mangle))
                .collect();
            format!("AnyOf{}", keys.join("_").replace("::", "_"))
        }
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
        HirTy::Fn(params, ret, _) => {
            let inner: Vec<String> = params.iter().map(ty_mangle).collect();
            format!(
                "Fn{}of{}_to_{}",
                params.len(),
                inner.join("x"),
                ty_mangle(ret)
            )
        }
        HirTy::Const(v, _) => format!("C{}", v.to_string().replace('-', "m")),
        HirTy::Path(segs) => format!("Path_{}", segs.join("_")),
        HirTy::None => "Path_none".to_owned(),
        HirTy::NoThrow => "Path_#nothrow".to_owned(),
        HirTy::OpenConst(n) => format!("Path_#{n}"),
        HirTy::Var(v) => format!("Path_#var_{v}"),
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
        HirTy::Throws { ok, err } => format!("Throws{}_or_{}", ty_mangle(ok), ty_mangle(err)),
    }
}

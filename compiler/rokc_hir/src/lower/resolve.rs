//! Name resolution: the module-aware path resolver shared by the value
//! and type namespaces, visibility, and AST type → `HirTy` resolution.

#[allow(clippy::wildcard_imports)]
use super::*;

/// Strip the leaf segment from a `module::path::name` string and
/// return the module path joined back with `::`. Returns an empty
/// string for free functions in the package root.
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
                if (set.exists)(&candidate) && !glob_hits.contains(&candidate) {
                    glob_hits.push(candidate);
                }
            }
            crate::uses::UseEntry::GlobDeep { prefix } => {
                let direct = if prefix.is_empty() {
                    suffix.to_owned()
                } else {
                    format!("{prefix}::{suffix}")
                };
                if (set.exists)(&direct) && !glob_hits.contains(&direct) {
                    glob_hits.push(direct);
                    continue;
                }
                let prefix_with_sep = if prefix.is_empty() {
                    String::new()
                } else {
                    format!("{prefix}::")
                };
                let suffix_with_sep = format!("::{suffix}");
                for key in (set.keys)() {
                    if key.starts_with(&prefix_with_sep)
                        && key.ends_with(&suffix_with_sep)
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
    let absolute = matches!(segments.first().copied(), Some("pkg" | "rok"));
    let resolved_segs: Vec<&str> = match segments.first().copied() {
        Some("pkg") => segments[1..].to_vec(),
        Some("sup") => {
            let mut parts: Vec<&str> = if module.is_empty() {
                Vec::new()
            } else {
                module.split("::").collect()
            };
            let mut i = 0;
            while i < segments.len() && segments[i] == "sup" {
                parts.pop();
                i += 1;
            }
            parts.extend(segments[i..].iter().copied());
            return Ok(Some(parts.join("::")).filter(|k| (set.exists)(k)));
        }
        _ => segments.to_vec(),
    };
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

/// The compiler-known GC buffer type (`HirTy::GcBuf`), declared in core
/// so the name resolves.
pub const GC_BUF: &str = "rok::core::collections::raw::GcBuf";

/// Module path the driver mounts `library/core` under.
pub const CORE_PREFIX: &str = "rok::core";

/// Can code in `cur_module` see an item declared in `def_module` with
/// visibility `vis`? (spec 5.6)
pub(super) fn visible_from(cur_module: &str, def_module: &str, vis: Visibility) -> bool {
    match vis {
        // Single-package compilation today: everything reaching out
        // (Pub) or staying within the package (Pkg) is reachable.
        Visibility::Pub | Visibility::Pkg => true,
        Visibility::Sub => {
            def_module.is_empty()
                || cur_module == def_module
                || cur_module.starts_with(&format!("{def_module}::"))
        }
        // Spec 5.6.2: no keyword = visible in the declaring module only.
        Visibility::Private => cur_module == def_module,
    }
}

pub(super) const fn module_display(m: &str) -> &str {
    if m.is_empty() { "<root>" } else { m }
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
    let marked = i
        .attrs
        .iter()
        .filter(|a| a.path == [crate::IMPL_MODULE_ATTR])
        .find_map(|a| match &a.body {
            rokc_ast::AttrBody::Args(args) => args.iter().find_map(|x| match x {
                rokc_ast::AttrArg::Lit(rokc_ast::Literal::Str(s)) => Some(s.clone()),
                _ => None,
            }),
            _ => None,
        });
    marked
        .or_else(|| {
            i.items.iter().find_map(|it| match it {
                AstImplItem::Method(m) => Some(module_of(&m.name)),
                _ => None,
            })
        })
        .unwrap_or_default()
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

/// Walk a `HirTy` substituting any unresolved `Path([alias_name])`
/// nodes with their concrete type from `aliases`. Multi-level
/// resolution is handled by the caller (a small fixed-iteration loop
/// over the alias table itself). An alias of a sum spreads into a sum
/// it is a member of (spec 2.6.4).
pub(super) fn substitute_aliases(ty: &mut HirTy, aliases: &HashMap<String, HirTy>) {
    substitute(ty, aliases, false);
}

/// `substitute_aliases` for generic parameters (and `Self`): a
/// parameter bound to a sum with `none` stays one member of a sum that
/// has its own `none` — `T | none` with `T = i32 | none` is the nested
/// optional `(i32 | none)?` (spec 2.6.4).
pub(super) fn substitute_params(ty: &mut HirTy, params: &HashMap<String, HirTy>) {
    substitute(ty, params, true);
}

fn substitute(ty: &mut HirTy, map: &HashMap<String, HirTy>, nest: bool) {
    let rec = |t: &mut HirTy| substitute(t, map, nest);
    match ty {
        HirTy::Path(parts) => {
            if parts.len() == 1 {
                if let Some(replacement) = map.get(&parts[0]) {
                    *ty = replacement.clone();
                }
            }
        }
        HirTy::Sum(parts) => {
            // An alias / type parameter may have become a sum (or a
            // member already present): back to the canon.
            let mut out = Vec::new();
            for mut p in std::mem::take(parts) {
                let named = matches!(&p, HirTy::Path(n) if n.len() == 1 && map.contains_key(&n[0]));
                rec(&mut p);
                if named && !nest {
                    p.spread(&mut out);
                } else {
                    out.push(p);
                }
            }
            *ty = HirTy::sum(out);
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

thread_local! {
    /// Plain-alias expansion depth (a cyclic alias stops at the cap).
    static ALIAS_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// `resolve_ty` plus module-aware struct / enum / alias name lookup.
/// Unresolvable names stay `HirTy::Path` (generic params get substituted
/// later; anything left over is reported by `check_unresolved_types`).
pub(super) fn resolve_ty_with_structs(
    ty: &rokc_ast::Ty,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    sc: Scope<'_>,
) -> HirTy {
    let rec = |t: &rokc_ast::Ty| resolve_ty_with_structs(t, structs, enums, sc);
    match &ty.kind {
        // Untyped `throws` (spec 4.14) = `throws (any Error)`.
        AstTyKind::Path(p)
            if p.segments.len() == 1 && p.segments[0].name == rokc_ast::UNTYPED_THROWS_MARK =>
        {
            rec(&rokc_ast::Ty {
                kind: AstTyKind::AnyTrait(vec![rokc_ast::Path {
                    segments: vec![rokc_ast::PathSegment {
                        name: "Error".to_owned(),
                        generics: Vec::new(),
                    }],
                    span: ty.span,
                }]),
                span: ty.span,
            })
        }
        AstTyKind::Path(p) => {
            let prim = resolve_ty(ty);
            if matches!(prim, HirTy::Prim(_)) {
                return prim;
            }
            if let Some(t) = sc.names.expand_alias(ty, sc.module) {
                return rec(&t);
            }
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            let generics = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
            let Some(full) = sc.names.canon(&segs, sc.module, &[]) else {
                return HirTy::Path(segs.iter().map(|s| (*s).to_owned()).collect());
            };
            if sc.names.traits.contains(&full) {
                sc.names.error(format!(
                    "trait `{full}` cannot be used as a type directly — use a closed \
                     sum (`A | B`) or a generic parameter (`<T: {full}>`) instead \
                     (i-want-this 538)"
                ));
                return HirTy::Any;
            }
            if let (GC_BUF, [elem]) = (full.as_str(), generics) {
                return HirTy::GcBuf(Box::new(rec(elem)));
            }
            if generics.is_empty() {
                // Depth-capped: a cyclic alias stays a path and is
                // reported by the alias pass.
                if let Some(t) = sc
                    .names
                    .plain_aliases
                    .get(&full)
                    .filter(|_| ALIAS_DEPTH.get() < 32)
                {
                    let module = module_of(&full);
                    let inner = Scope {
                        names: sc.names,
                        module: &module,
                    };
                    ALIAS_DEPTH.set(ALIAS_DEPTH.get() + 1);
                    let r = resolve_ty_with_structs(t, structs, enums, inner);
                    ALIAS_DEPTH.set(ALIAS_DEPTH.get() - 1);
                    return r;
                }
            }
            if !generics.is_empty() {
                let args: Vec<HirTy> = generics.iter().map(rec).collect();
                let mangled = mangle_inst(&full, &args);
                if let Some(id) = structs.get(&mangled) {
                    return HirTy::Struct(*id);
                }
                if let Some(id) = enums.get(&mangled) {
                    return HirTy::Enum(*id);
                }
                return HirTy::Path(vec![full]);
            }
            if let Some(id) = structs.get(&full) {
                return HirTy::Struct(*id);
            }
            if let Some(id) = enums.get(&full) {
                return HirTy::Enum(*id);
            }
            // Type alias (substituted later) or a generic base used
            // without arguments.
            HirTy::Path(vec![full])
        }
        AstTyKind::Array(elem, len) => {
            let n = crate::ty::eval_const_with(len, &|_| None).and_then(|n| u32::try_from(n).ok());
            let Some(n) = n else {
                sc.names.error(
                    "array length must be an integer literal (stage-1 limitation)".to_owned(),
                );
                return HirTy::Any;
            };
            HirTy::Array(Box::new(rec(elem)), n)
        }
        // `T | U` — recurse so Path("Counter") resolves to Struct(id), not
        // an opaque path the MIR layer would treat as `Any`.
        AstTyKind::Sum(parts) => crate::ty::written_sum(parts, |_| false, rec),
        AstTyKind::Tuple(parts) if parts.is_empty() => HirTy::Unit,
        AstTyKind::Tuple(parts) => HirTy::Tuple(parts.iter().map(rec).collect()),
        AstTyKind::Fn(args, ret, b) => HirTy::Fn(
            args.iter().map(rec).collect(),
            Box::new(rec(ret)),
            sc.names.fn_bounds(b, sc.module),
        ),
        AstTyKind::AnyTrait(bounds) => {
            let mut keys: Vec<String> = Vec::with_capacity(bounds.len());
            for b in bounds {
                let segs: Vec<&str> = b.segments.iter().map(|s| s.name.as_str()).collect();
                let key = sc.names.trait_key(&segs, sc.module);
                let user_trait = sc.names.traits.contains(&key);
                // Bootstrap traits key by their last segment (see
                // `trait_key`); anything else must name a declared trait.
                if !user_trait && !sc.names.traits.iter().any(|t| leaf_name(t) == key) {
                    sc.names.error(format!(
                        "`{}` in `any {}` is not a trait — `any` bounds must name traits (D4)",
                        segs.join("::"),
                        segs.join("::")
                    ));
                    return HirTy::Unknown;
                }
                let (args, binds) = split_trait_args(
                    b.segments.last().map_or(&[][..], |s| s.generics.as_slice()),
                    rec,
                );
                keys.push(bound_key(key, &args, &binds, structs, enums));
            }
            keys.sort();
            keys.dedup();
            HirTy::AnyTrait(keys)
        }
        AstTyKind::Throws { ok, err } => crate::ty::throws_ty(rec(ok), rec(err)),
        _ => resolve_ty(ty),
    }
}

/// `any` bound / impl key with the trait's generic arguments
/// (`Index<i32>`); a struct or enum argument prints by its name.
pub(super) fn bound_key(
    key: String,
    args: &[HirTy],
    binds: &[(String, HirTy)],
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
) -> String {
    if args.is_empty() && binds.is_empty() {
        return key;
    }
    let name = |t: &HirTy| {
        match t {
            HirTy::Struct(id) => structs
                .iter()
                .filter(|(_, v)| *v == id)
                .map(|(k, _)| k)
                .min(),
            HirTy::Enum(id) => enums.iter().filter(|(_, v)| *v == id).map(|(k, _)| k).min(),
            _ => None,
        }
        .map_or_else(|| ty_mangle(t), Clone::clone)
    };
    let mut binds = binds.to_vec();
    binds.sort_by(|a, b| a.0.cmp(&b.0));
    let parts: Vec<String> = args
        .iter()
        .map(name)
        .chain(binds.iter().map(|(n, t)| format!("{n} = {}", name(t))))
        .collect();
    format!("{key}<{}>", parts.join(", "))
}

/// Every bound key an impl of trait `tn` with trait arguments `args`
/// and associated types `assoc` answers: `Get`, `Get<i32>`,
/// `Get<Item = u8>`, `Get<i32, Item = u8>`, ...
pub(super) fn impl_bound_keys(
    tn: &str,
    args: &[HirTy],
    assoc: &[(String, HirTy)],
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
) -> Vec<String> {
    let mut keys = vec![tn.to_owned()];
    // ponytail: every subset of the bindings — 2^n keys; fine for the
    // one or two associated types traits have.
    for mask in 0..1u32 << assoc.len().min(8) {
        let binds: Vec<(String, HirTy)> = assoc
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, b)| b.clone())
            .collect();
        for a in [args, &[]] {
            keys.push(bound_key(tn.to_owned(), a, &binds, structs, enums));
        }
    }
    keys
}

/// A trait path's generic arguments: positional ones and `Name = Ty`
/// associated-type bindings, each resolved by `rec`.
pub(super) fn split_trait_args(
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
        HirTy::Struct(id) => format!("Struct{}", id.0),
        HirTy::Enum(id) => format!("Enum{}", id.0),
        HirTy::Prim(p) => p.name().to_owned(),
        HirTy::Unit => "Unit".to_owned(),
        HirTy::Any => "Any".to_owned(),
        HirTy::AnyTrait(bounds) => format!("AnyOf{}", bounds.join("_").replace("::", "_")),
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
        HirTy::Path(segs) if segs.first().is_some_and(|s| s == "#const") => {
            format!(
                "C{}",
                segs.get(1).map_or("", |v| v.as_str()).replace('-', "m")
            )
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
        HirTy::Throws { ok, err } => format!("Throws{}_or_{}", ty_mangle(ok), ty_mangle(err)),
    }
}

//! `match`, patterns and exhaustiveness.

#[allow(clippy::wildcard_imports)]
use super::*;

pub(super) fn lower_match(
    ctx: &mut LowerCtx<'_>,
    scrutinee: &Expr,
    arms: &[AstMatchArm],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let scrut_h = lower_expected(ctx, scrutinee, HirTy::Unknown);
    let scrut_ty = scrut_h.ty.clone();
    if scrut_ty == HirTy::Unknown {
        return scrut_h;
    }
    // A known slot type (`let x: T = match ...`) unifies the arms.
    let expected = ctx
        .current_expected()
        .cloned()
        .filter(|t| *t != HirTy::Unknown);
    let mut arm_h: Vec<HirMatchArm> = Vec::with_capacity(arms.len());
    for arm in arms {
        ctx.push_scope();
        let pat = lower_pattern(ctx, &arm.pat, &scrut_ty);
        let guard = arm.guard.as_ref().map(|g| lower_cond(ctx, g));
        let body = lower_expr(ctx, &arm.body);
        ctx.pop_scope();
        arm_h.push(HirMatchArm { pat, guard, body });
    }
    // Spec 3.12.5: exhaustiveness.
    check_match_exhaustiveness(ctx, &scrut_ty, &arm_h);

    // Result type: the expected slot, else the first arm that produces
    // a value; every other value-producing arm must agree.
    let result_ty = expected.unwrap_or_else(|| {
        arm_h
            .iter()
            .find(|a| !hir_expr_diverges(&a.body))
            .map_or(HirTy::Unit, |a| a.body.ty.clone())
    });
    // `let x: T = v else { ... };` is parsed as a two-arm match whose
    // second arm is the else block (parser desugar).
    let is_let_else = matches!(
        arms.first().map(|a| &a.pat.kind),
        Some(AstPatternKind::Binding { name, .. } | AstPatternKind::TypeCheck { binder: Some(name), .. })
            if name == "__letelse_v"
    );
    let mut out = Vec::with_capacity(arm_h.len());
    for (i, mut a) in arm_h.into_iter().enumerate() {
        // A unit-typed match (statement position) discards arm values.
        if !hir_expr_diverges(&a.body) && (result_ty != HirTy::Unit || is_let_else) {
            if is_let_else && i == 1 {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    "the `else` block of `let ... else` must diverge (end in `return`, \
                     `break`, `continue` or `throw`) (spec 3.15)"
                        .to_owned(),
                );
            } else {
                a.body = coerce(ctx, &result_ty, a.body, &|| format!("match arm {}", i + 1));
            }
        }
        out.push(a);
    }
    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(scrut_h),
            arms: out,
        },
        ty: result_ty,
        span,
    }
}

/// Matches every value of its type (no refutable sub-pattern).
pub(super) fn hir_pattern_irrefutable(p: &HirPattern) -> bool {
    match p {
        HirPattern::Wildcard | HirPattern::Binding { .. } => true,
        HirPattern::Tuple(parts) => parts.iter().all(hir_pattern_irrefutable),
        HirPattern::Struct { fields, .. } => fields.iter().all(|(_, p)| hir_pattern_irrefutable(p)),
        HirPattern::Or(alts) => alts.iter().any(hir_pattern_irrefutable),
        HirPattern::Literal { .. }
        | HirPattern::Range { .. }
        | HirPattern::EnumVariant { .. }
        | HirPattern::SumVariant { .. } => false,
    }
}

/// Enum variants / sum variants fully covered by `p`.
pub(super) fn covered_variants(p: &HirPattern, out: &mut Vec<u32>) {
    match p {
        HirPattern::EnumVariant {
            variant_index,
            args,
            ..
        } if args.iter().all(hir_pattern_irrefutable) => {
            out.push(*variant_index);
        }
        HirPattern::SumVariant { variant_index, .. } => out.push(*variant_index),
        HirPattern::Or(alts) => {
            for a in alts {
                covered_variants(a, out);
            }
        }
        _ => {}
    }
}

/// Spec 3.12.5: the arms must cover the scrutinee's type. Bool needs
/// both literals; enums / sums need every variant (an arm with a guard
/// covers nothing); other types need a catch-all.
pub(super) fn check_match_exhaustiveness(
    ctx: &LowerCtx<'_>,
    scrut_ty: &HirTy,
    arms: &[HirMatchArm],
) {
    let unguarded: Vec<&HirPattern> = arms
        .iter()
        .filter(|a| a.guard.is_none())
        .map(|a| &a.pat)
        .collect();
    if unguarded.iter().any(|p| hir_pattern_irrefutable(p)) {
        return;
    }
    let missing: Vec<String> = match scrut_ty {
        HirTy::Prim(PrimTy::Bool) => {
            fn bools(p: &HirPattern, seen: &mut [bool; 2]) {
                match p {
                    HirPattern::Literal {
                        value: ConstVal::Bool(b),
                        ..
                    } => seen[usize::from(*b)] = true,
                    HirPattern::Or(alts) => alts.iter().for_each(|a| bools(a, seen)),
                    _ => {}
                }
            }
            let mut seen = [false, false];
            for p in &unguarded {
                bools(p, &mut seen);
            }
            [("false", seen[0]), ("true", seen[1])]
                .iter()
                .filter(|(_, s)| !s)
                .map(|(n, _)| format!("`{n}`"))
                .collect()
        }
        HirTy::Enum(eid) => {
            let mut covered = Vec::new();
            for p in &unguarded {
                covered_variants(p, &mut covered);
            }
            let def = &ctx.env.enums[eid.0 as usize];
            let base = enum_base_name(&def.name);
            def.variants
                .iter()
                .enumerate()
                .filter(|(i, _)| !covered.contains(&u32::try_from(*i).expect("variant overflow")))
                .map(|(_, v)| format!("`{base}::{}`", v.name))
                .collect()
        }
        HirTy::Sum(variants) => {
            let mut covered = Vec::new();
            for p in &unguarded {
                covered_variants(p, &mut covered);
            }
            variants
                .iter()
                .enumerate()
                .filter(|(i, _)| !covered.contains(&u32::try_from(*i).expect("variant overflow")))
                .map(|(_, v)| format!("`{}`", ctx.ty_name(v)))
                .collect()
        }
        other => vec![format!(
            "values of `{}` (add a `_` arm)",
            ctx.ty_name(other)
        )],
    };
    if !missing.is_empty() {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "non-exhaustive match on `{}`: {} not covered (spec 3.12.5)",
                ctx.ty_name(scrut_ty),
                missing.join(", ")
            ),
        );
    }
}

pub(super) fn lower_pattern(
    ctx: &mut LowerCtx<'_>,
    pat: &AstPattern,
    scrut_ty: &HirTy,
) -> HirPattern {
    let p = lower_pattern_inner(ctx, pat, scrut_ty);
    // A pattern that failed to lower still declares its names (as
    // poisoned locals) so their uses don't cascade into "cannot find".
    if matches!(p, HirPattern::Wildcard) {
        for name in pattern_bound_names(pat) {
            if ctx.lookup_in_current_scope(&name).is_none() {
                ctx.declare(Some(name), HirTy::Unknown);
            }
        }
    }
    p
}

#[allow(clippy::cognitive_complexity)] // one arm per pattern kind
pub(super) fn lower_pattern_inner(
    ctx: &mut LowerCtx<'_>,
    pat: &AstPattern,
    scrut_ty: &HirTy,
) -> HirPattern {
    let mismatch = |ctx: &LowerCtx<'_>, what: String| {
        if *scrut_ty != HirTy::Unknown {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "{what} can't match a value of type `{}`",
                    ctx.ty_name(scrut_ty)
                ),
            );
        }
        HirPattern::Wildcard
    };
    match &pat.kind {
        AstPatternKind::Wildcard => HirPattern::Wildcard,
        AstPatternKind::Binding { name, sub: None } if name == "_" => HirPattern::Wildcard,
        AstPatternKind::Binding { name, sub: None } => {
            // Spec 3.11.4: when an enclosing or-pattern shares this name
            // across alternatives, reuse the preset local and check that
            // each alt binds the same type.
            if let Some(&local) = ctx.or_pattern_binders.last().and_then(|m| m.get(name)) {
                let existing = ctx.local_ty(local);
                if matches!(existing, HirTy::Unknown) {
                    ctx.locals[local.0 as usize].ty = scrut_ty.clone();
                } else if existing != *scrut_ty {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "or-pattern binding `{name}` has inconsistent types across \
                             alternatives (spec 3.11.4)"
                        ),
                    );
                }
                return HirPattern::Binding {
                    local,
                    ty: scrut_ty.clone(),
                };
            }
            let local = ctx.declare(Some(name.clone()), scrut_ty.clone());
            HirPattern::Binding {
                local,
                ty: scrut_ty.clone(),
            }
        }
        AstPatternKind::Binding { name, sub: Some(_) } => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("`{name} @ pattern` bindings are not supported yet (stage-1 limitation)"),
            );
            HirPattern::Wildcard
        }
        AstPatternKind::Literal(AstLit::None) => {
            // `none` against a sum scrutinee → match the none variant.
            if let HirTy::Sum(variants) = scrut_ty {
                if let Some(idx) = variants.iter().position(is_none_ty) {
                    return HirPattern::SumVariant {
                        sum_ty: scrut_ty.clone(),
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        binder: None,
                        payload_ty: None,
                    };
                }
            }
            mismatch(ctx, "a `none` pattern".to_owned())
        }
        AstPatternKind::Literal(lit) => match literal_to_const(ctx, lit, scrut_ty) {
            Some((value, prim)) => HirPattern::Literal { value, prim },
            None => mismatch(ctx, "this literal pattern".to_owned()),
        },
        AstPatternKind::TypeCheck { binder, ty } => {
            // `name: T` — narrow a sum scrutinee to variant `T` (or, on a
            // non-sum of exactly type `T`, bind it).
            let target_ty = ctx.resolve_ast_ty(ty);
            let bind = |ctx: &mut LowerCtx<'_>| {
                binder
                    .as_ref()
                    .map(|name| ctx.declare(Some(name.clone()), target_ty.clone()))
            };
            if let HirTy::Sum(variants) = scrut_ty {
                if let Some(idx) = sum_variant_index(variants, &target_ty) {
                    let bind_local = bind(ctx);
                    return HirPattern::SumVariant {
                        sum_ty: scrut_ty.clone(),
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        binder: bind_local,
                        payload_ty: Some(target_ty),
                    };
                }
            } else if *scrut_ty == target_ty {
                return match bind(ctx) {
                    Some(local) => HirPattern::Binding {
                        local,
                        ty: target_ty,
                    },
                    None => HirPattern::Wildcard,
                };
            }
            mismatch(ctx, format!("type pattern `{}`", ctx.ty_name(&target_ty)))
        }
        AstPatternKind::Or(alts) => {
            // Spec 3.11.4: every alternative must bind the same set of
            // names. Pre-allocate one shared local per name (with type
            // resolved during the first alt's lowering and checked for
            // consistency on subsequent alts).
            let name_sets: Vec<std::collections::BTreeSet<String>> =
                alts.iter().map(pattern_bound_names).collect();
            let bound_names = name_sets.first().cloned().unwrap_or_default();
            for (i, set) in name_sets.iter().enumerate().skip(1) {
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
            let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
            let (enum_id, idx) = match resolve_enum_variant(ctx, &segs, Some(scrut_ty), None) {
                EnumRes::Found(e, i) => (e, i),
                EnumRes::Error => return HirPattern::Wildcard,
                EnumRes::NotEnum => {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("cannot find enum variant `{}`", segs.join("::")),
                    );
                    return HirPattern::Wildcard;
                }
            };
            if *scrut_ty != HirTy::Enum(enum_id) {
                return mismatch(ctx, format!("pattern `{}`", segs.join("::")));
            }
            let variant = ctx.env.enums[enum_id.0 as usize].variants[idx].clone();
            let slots = variant_arg_tys(&variant);
            if args.len() != slots.len() {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "pattern `{}` has {} field{}, but the variant has {}",
                        segs.join("::"),
                        args.len(),
                        if args.len() == 1 { "" } else { "s" },
                        slots.len()
                    ),
                );
                return HirPattern::Wildcard;
            }
            let lowered_args: Vec<HirPattern> = args
                .iter()
                .zip(&slots)
                .map(|(p, t)| lower_pattern(ctx, p, t))
                .collect();
            HirPattern::EnumVariant {
                enum_id,
                variant_index: u32::try_from(idx).expect("variant overflow"),
                args: lowered_args,
            }
        }
        AstPatternKind::Tuple(pats) => match scrut_ty {
            HirTy::Tuple(elem_tys) if pats.len() == elem_tys.len() => HirPattern::Tuple(
                pats.iter()
                    .zip(elem_tys.iter())
                    .map(|(p, t)| lower_pattern(ctx, p, t))
                    .collect(),
            ),
            _ => mismatch(ctx, format!("a {}-tuple pattern", pats.len())),
        },
        AstPatternKind::Range {
            start,
            end,
            inclusive,
        } => {
            let prim = match scrut_ty {
                HirTy::Prim(p) if p.is_int() => *p,
                _ => return mismatch(ctx, "a range pattern".to_owned()),
            };
            let bound = |ctx: &LowerCtx<'_>, lit: &Option<AstLit>| match lit {
                None => Some(None),
                Some(l) => literal_to_const(ctx, l, scrut_ty).map(|(v, _)| Some(v)),
            };
            match (bound(ctx, start), bound(ctx, end)) {
                (Some(s), Some(e)) => HirPattern::Range {
                    start: s,
                    end: e,
                    inclusive: *inclusive,
                    prim,
                },
                _ => mismatch(ctx, "this range pattern".to_owned()),
            }
        }
        AstPatternKind::Struct { path, fields, .. } => {
            let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
            // `EnumName::Variant { x, y }` — enum named-form variant
            // pattern. Map each field name to its position in the
            // variant's tuple payload (spec 2.4).
            match resolve_enum_variant(ctx, &segs, Some(scrut_ty), None) {
                EnumRes::Error => return HirPattern::Wildcard,
                EnumRes::Found(enum_id, idx) => {
                    if *scrut_ty != HirTy::Enum(enum_id) {
                        return mismatch(ctx, format!("pattern `{}`", segs.join("::")));
                    }
                    let variant = ctx.env.enums[enum_id.0 as usize].variants[idx].clone();
                    let field_tys = variant_arg_tys(&variant);
                    let mut args = vec![HirPattern::Wildcard; variant.named_fields.len()];
                    for fp in fields {
                        let Some(i) = variant.named_fields.iter().position(|n| *n == fp.name)
                        else {
                            ctx.emit_error(
                                rokc_diagnostic::ErrorKind::Type,
                                format!(
                                    "enum variant `{}` has no field `{}`",
                                    segs.join("::"),
                                    fp.name
                                ),
                            );
                            continue;
                        };
                        let ty = field_tys[i].clone();
                        args[i] = if let Some(p) = &fp.pat {
                            lower_pattern(ctx, p, &ty)
                        } else {
                            let local = ctx.declare(Some(fp.name.clone()), ty.clone());
                            HirPattern::Binding { local, ty }
                        };
                    }
                    return HirPattern::EnumVariant {
                        enum_id,
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        args,
                    };
                }
                EnumRes::NotEnum => {}
            }
            let struct_id = ctx
                .canon_type(&segs)
                .and_then(|full| ctx.lookup_struct(&full));
            let Some(struct_id) = struct_id else {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!("cannot find struct `{}` in this scope", segs.join("::")),
                );
                return HirPattern::Wildcard;
            };
            if *scrut_ty != HirTy::Struct(struct_id) {
                return mismatch(ctx, format!("struct pattern `{}`", segs.join("::")));
            }
            let def = ctx.struct_def(struct_id);
            let mut lowered: Vec<(u32, HirPattern)> = Vec::new();
            for fp in fields {
                let Some(idx) = def.fields.iter().position(|f| f.name == fp.name) else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("struct `{}` has no field `{}`", def.name, fp.name),
                    );
                    continue;
                };
                ctx.check_field_visible(struct_id, &fp.name);
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
        AstPatternKind::Rest(_) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "a rest pattern `..` is only allowed in tuple destructuring `let`".to_owned(),
            );
            HirPattern::Wildcard
        }
    }
}

/// Names bound by a pattern (sorted, for or-pattern consistency).
pub(super) fn pattern_bound_names(pat: &AstPattern) -> std::collections::BTreeSet<String> {
    struct Names(std::collections::BTreeSet<String>);
    impl crate::walk::AstVisitor for Names {
        fn bind(&mut self, name: &str) {
            self.0.insert(name.to_owned());
        }
    }
    let mut n = Names(std::collections::BTreeSet::new());
    match &pat.kind {
        // Spec 3.11.4: alternatives bind the same names; the first one
        // stands for the whole or-pattern.
        AstPatternKind::Or(alts) => {
            if let Some(first) = alts.first() {
                crate::walk::walk_pat(&mut n, first);
            }
        }
        _ => crate::walk::walk_pat(&mut n, pat),
    }
    n.0
}

/// Convert an AST literal that appears in a pattern to a `ConstVal` plus
/// the primitive type the comparison should use. `None` when the
/// literal's type doesn't fit the scrutinee (the caller reports).
pub(super) fn literal_to_const(
    ctx: &LowerCtx<'_>,
    lit: &AstLit,
    scrut_ty: &HirTy,
) -> Option<(ConstVal, PrimTy)> {
    let HirTy::Prim(sp) = scrut_ty else {
        return None;
    };
    match lit {
        AstLit::Int(text) => {
            // Bare literals take the scrutinee's type.
            let (value, mut ty) = parse_int_literal(text)?;
            if !has_int_suffix(text) {
                ty = *sp;
            }
            if ty != *sp || !sp.is_int() {
                return None;
            }
            if !int_fits(value, ty) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!("literal `{text}` out of range for `{}`", ty.name()),
                );
            }
            Some((ConstVal::Int { value, ty }, ty))
        }
        AstLit::Bool(b) if *sp == PrimTy::Bool => Some((ConstVal::Bool(*b), PrimTy::Bool)),
        AstLit::Char(s) if *sp == PrimTy::Char => {
            parse_char_literal(s).map(|c| (ConstVal::Char(c), PrimTy::Char))
        }
        // An ASCII `'a'` against a `c_char` scrutinee takes that type.
        AstLit::Char(s) if *sp == PrimTy::CChar => parse_char_literal(s)
            .filter(|c| *c < 0x80)
            .map(|c| (ConstVal::Char(c), PrimTy::CChar)),
        AstLit::CChar(s) if *sp == PrimTy::CChar => {
            parse_char_literal(s).map(|c| (ConstVal::Char(c), PrimTy::CChar))
        }
        // String / float literal patterns would need value equality the
        // backend doesn't lower yet.
        _ => None,
    }
}

/// Does `v` fit in primitive integer type `p`? (64-bit target)
pub(super) fn int_fits(v: i128, p: PrimTy) -> bool {
    let bits = p.bit_width(64);
    if bits == 0 || bits >= 128 {
        return true;
    }
    if p.is_signed_int() {
        let lim = 1i128 << (bits - 1);
        (-lim..lim).contains(&v)
    } else {
        (0..(1i128 << bits)).contains(&v)
    }
}

//! HIR → MIR type lowering.

use rokc_hir::{HirModule, HirTy};
use rokc_ir_common::PrimTy;

use crate::MirTy;

#[must_use]
pub fn lower_ty(ty: &HirTy) -> MirTy {
    match ty {
        HirTy::Unknown | HirTy::Path(_) | HirTy::Any => MirTy::Any,
        HirTy::Unit => MirTy::Unit,
        HirTy::Prim(p) => MirTy::Prim(*p),
        // `any Tr`: `(i32 tag, usize heap pointer)`.
        HirTy::AnyTrait(_) => {
            MirTy::Tuple(vec![MirTy::Prim(PrimTy::I32), MirTy::Prim(PrimTy::Usize)])
        }
        HirTy::Sum(parts) => sum_layout(&non_none(parts).map(lower_ty).collect::<Vec<_>>()),
        HirTy::Tuple(parts) => MirTy::Tuple(parts.iter().map(lower_ty).collect()),
        // Struct types need the field shape; this stub only allocates
        // the marker — see `lower_ty_in` for the concrete shape.
        HirTy::Struct(id) => MirTy::Struct(*id, Vec::new()),
        // Unit-only enums lower to a plain i32 tag (caller without
        // module context can't see payloads).
        HirTy::Enum(_) => MirTy::Prim(PrimTy::I32),
        HirTy::Array(elem, n) => MirTy::Array(Box::new(lower_ty(elem)), *n),
        HirTy::Fn(args, ret) => {
            MirTy::Fn(args.iter().map(lower_ty).collect(), Box::new(lower_ty(ret)))
        }
        // Closure layout: `{fn_ptr, env}` 2-tuple. The lifted function
        // takes env as its first parameter, so its full signature is
        // `(env, args...) -> ret`.
        HirTy::Closure { args, ret, env } => {
            let env_ty = lower_ty(env);
            let mut fn_args = vec![env_ty.clone()];
            fn_args.extend(args.iter().map(lower_ty));
            MirTy::Tuple(vec![MirTy::Fn(fn_args, Box::new(lower_ty(ret))), env_ty])
        }
        HirTy::Throws { ok, err } => carrier(lower_ty(ok), lower_ty(err)),
    }
}

/// Return value of a throwing function: `(is_err: bool, ok, err)`, with
/// a unit `ok` left out (HIR reads the fields at the same indices).
// ponytail: both payloads stored side by side; a union needs the
// byte-array aggregate storage `unify_payload` also waits for.
fn carrier(ok: MirTy, err: MirTy) -> MirTy {
    let mut fields = vec![MirTy::Prim(PrimTy::Bool)];
    if ok != MirTy::Unit {
        fields.push(ok);
    }
    fields.push(err);
    MirTy::Tuple(fields)
}

// Like `lower_ty` but resolves struct/enum ids to their concrete shape.
#[must_use]
pub fn lower_ty_in(ty: &HirTy, module: &HirModule) -> MirTy {
    match ty {
        HirTy::Struct(id) => {
            let def = &module.structs[id.0 as usize];
            MirTy::Struct(
                *id,
                def.fields
                    .iter()
                    .map(|f| lower_ty_in(&f.ty, module))
                    .collect(),
            )
        }
        HirTy::Sum(parts) => sum_layout(
            &non_none(parts)
                .map(|p| lower_ty_in(p, module))
                .collect::<Vec<_>>(),
        ),
        HirTy::Tuple(parts) => MirTy::Tuple(parts.iter().map(|t| lower_ty_in(t, module)).collect()),
        HirTy::Enum(id) => sum_layout(&enum_payloads(
            &module.enums[id.0 as usize].variants,
            module,
        )),
        HirTy::Array(elem, n) => MirTy::Array(Box::new(lower_ty_in(elem, module)), *n),
        HirTy::Fn(args, ret) => MirTy::Fn(
            args.iter().map(|a| lower_ty_in(a, module)).collect(),
            Box::new(lower_ty_in(ret, module)),
        ),
        HirTy::Closure { args, ret, env } => {
            let env_ty = lower_ty_in(env, module);
            let mut fn_args = vec![env_ty.clone()];
            fn_args.extend(args.iter().map(|a| lower_ty_in(a, module)));
            MirTy::Tuple(vec![
                MirTy::Fn(fn_args, Box::new(lower_ty_in(ret, module))),
                env_ty,
            ])
        }
        HirTy::Throws { ok, err } => carrier(lower_ty_in(ok, module), lower_ty_in(err, module)),
        _ => lower_ty(ty),
    }
}

fn non_none(variants: &[HirTy]) -> impl Iterator<Item = &HirTy> {
    variants
        .iter()
        .filter(|v| !matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]))
}

/// The single tagged-union layout shared by enums and sums:
/// `(i32 tag, payload)`, or a bare `i32` tag when nothing carries data.
/// `payloads` excludes `none` / unit variants.
#[must_use]
pub fn sum_layout(payloads: &[MirTy]) -> MirTy {
    match unify_payload(payloads).or_else(|| payloads.first().cloned()) {
        Some(p) => MirTy::Tuple(vec![MirTy::Prim(PrimTy::I32), p]),
        None => MirTy::Prim(PrimTy::I32),
    }
}

/// Payload slot able to hold every variant. Identical payloads share
/// their type; differing scalar payloads share an unsigned integer as
/// wide as the widest one, written / read through `RValue::Bitcast`.
/// Other mixes (aggregate vs scalar, two different aggregates) have no
/// layout yet → `None`.
// ponytail: scalar-only union; aggregate unions need byte-array storage
// with max size/align once MIR grows memory-backed values.
#[must_use]
pub fn unify_payload(payloads: &[MirTy]) -> Option<MirTy> {
    let first = payloads.first()?;
    if payloads.iter().all(|p| p == first) {
        return Some(first.clone());
    }
    let mut bits = 0;
    for p in payloads {
        match p {
            MirTy::Prim(q) if !matches!(q, PrimTy::Str) => bits = bits.max(q.bit_width(64)),
            _ => return None,
        }
    }
    Some(MirTy::Prim(match bits {
        8 => PrimTy::U8,
        16 => PrimTy::U16,
        32 => PrimTy::U32,
        _ => PrimTy::U64,
    }))
}

fn enum_payloads(variants: &[rokc_hir::HirEnumVariant], module: &HirModule) -> Vec<MirTy> {
    variants
        .iter()
        .filter_map(|v| v.payload_ty.as_ref().map(|p| lower_ty_in(p, module)))
        .collect()
}

// Returns the unified payload `MirTy` for an enum, or `None` if the
// enum has no payload-bearing variants.
#[must_use]
pub fn enum_payload_ty(id: rokc_hir::EnumId, module: &HirModule) -> Option<MirTy> {
    match sum_layout(&enum_payloads(
        &module.enums[id.0 as usize].variants,
        module,
    )) {
        MirTy::Tuple(mut parts) => parts.pop(),
        _ => None,
    }
}

/// Enums whose variant payloads have no shared layout (see
/// `unify_payload`), as `(name, payload types)`.
#[must_use]
pub fn enums_without_layout(module: &HirModule) -> Vec<(String, Vec<MirTy>)> {
    module
        .enums
        .iter()
        .filter_map(|e| {
            let ps = enum_payloads(&e.variants, module);
            (!ps.is_empty() && unify_payload(&ps).is_none()).then(|| (e.name.clone(), ps))
        })
        .collect()
}

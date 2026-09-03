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
        HirTy::Sum(parts) => MirTy::Sum(parts.iter().map(lower_ty).collect()),
        HirTy::Tuple(parts) => MirTy::Tuple(parts.iter().map(lower_ty).collect()),
        // Struct types need the field shape; this stub only allocates
        // the marker — see `lower_ty_in` for the concrete shape.
        HirTy::Struct(id) => MirTy::Struct(*id, Vec::new()),
        // Unit-only enums lower to a plain i32 tag (caller without
        // module context can't see payloads).
        HirTy::Enum(_) => MirTy::Prim(PrimTy::I32),
        HirTy::Array(elem, n) => MirTy::Array(Box::new(lower_ty(elem)), *n),
        HirTy::Fn(args, ret) => MirTy::Fn(
            args.iter().map(lower_ty).collect(),
            Box::new(lower_ty(ret)),
        ),
        // Closure layout: `{fn_ptr, env}` 2-tuple. The lifted function
        // takes env as its first parameter, so its full signature is
        // `(env, args...) -> ret`.
        HirTy::Closure { args, ret, env } => {
            let env_ty = lower_ty(env);
            let mut fn_args = vec![env_ty.clone()];
            fn_args.extend(args.iter().map(lower_ty));
            MirTy::Tuple(vec![
                MirTy::Fn(fn_args, Box::new(lower_ty(ret))),
                env_ty,
            ])
        }
    }
}

// Like `lower_ty` but resolves struct/enum ids to their concrete shape.
#[must_use]
pub fn lower_ty_in(ty: &HirTy, module: &HirModule) -> MirTy {
    match ty {
        HirTy::Struct(id) => {
            let def = &module.structs[id.0 as usize];
            MirTy::Struct(*id, def.fields.iter().map(|f| lower_ty_in(&f.ty, module)).collect())
        }
        // Sum types share enum's `(i32 tag, payload)` layout. Payload =
        // first non-`none` variant's primitive type, or i32 if all
        // variants are `none`.
        HirTy::Sum(parts) => match sum_payload_hir_ty(parts) {
            Some(p) => MirTy::Tuple(vec![
                MirTy::Prim(PrimTy::I32),
                lower_ty_in(p, module),
            ]),
            None => MirTy::Prim(PrimTy::I32),
        },
        HirTy::Tuple(parts) => {
            MirTy::Tuple(parts.iter().map(|t| lower_ty_in(t, module)).collect())
        }
        HirTy::Enum(id) => {
            let def = &module.enums[id.0 as usize];
            match largest_int_payload(&def.variants, module) {
                Some(p) => MirTy::Tuple(vec![MirTy::Prim(PrimTy::I32), p]),
                None => MirTy::Prim(PrimTy::I32),
            }
        }
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
        _ => lower_ty(ty),
    }
}

// Pick the unified payload type for a sum. Strategy: skip `none`
// sentinels, then prefer the widest primitive (so heterogeneous sums
// like `i32 | f64` reserve enough storage for every variant). When
// multiple variants share the same width, the first wins. Falls back
// to the first non-`none` variant when nothing is primitive.
fn sum_payload_hir_ty(variants: &[HirTy]) -> Option<&HirTy> {
    let non_none: Vec<&HirTy> = variants
        .iter()
        .filter(|v| !matches!(v, HirTy::Path(p) if p.as_slice() == ["none"]))
        .collect();
    let widest = non_none.iter().copied().max_by_key(|v| match v {
        HirTy::Prim(p) => p.bit_width(64),
        _ => 0,
    });
    widest.or_else(|| non_none.first().copied())
}

// Pick a unified payload type for an enum. Strategy: first variant
// with a payload wins. Heterogeneous payload types across variants
// aren't supported — every variant must share one payload type.
fn largest_int_payload(
    variants: &[rokc_hir::HirEnumVariant],
    module: &HirModule,
) -> Option<MirTy> {
    variants
        .iter()
        .find_map(|v| v.payload_ty.as_ref().map(|p| lower_ty_in(p, module)))
}

// Returns the unified payload `MirTy` for an enum, or `None` if the
// enum has no payload-bearing variants.
#[must_use]
pub fn enum_payload_ty(id: rokc_hir::EnumId, module: &HirModule) -> Option<MirTy> {
    let def = &module.enums[id.0 as usize];
    largest_int_payload(&def.variants, module)
}

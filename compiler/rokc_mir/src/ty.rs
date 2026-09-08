//! HIR → MIR type lowering.

use rokc_hir::{HirModule, HirTy};
use rokc_ir_common::PrimTy;

use crate::MirTy;

#[must_use]
pub fn lower_ty(ty: &HirTy) -> MirTy {
    match ty {
        HirTy::Unknown | HirTy::Path(_) | HirTy::Any => MirTy::Any,
        // `!` has no values; a diverging call returns nothing.
        HirTy::Unit | HirTy::Never => MirTy::Unit,
        HirTy::Prim(p) => MirTy::Prim(*p),
        // `any Tr`: `(i32 tag, GC pointer to the boxed value)`.
        HirTy::AnyTrait(_) => MirTy::Tuple(vec![MirTy::Prim(PrimTy::I32), MirTy::GcRef]),
        HirTy::Sum(parts) => sum_layout(&non_none(parts).map(lower_ty).collect::<Vec<_>>()),
        HirTy::Tuple(parts) => MirTy::Tuple(parts.iter().map(lower_ty).collect()),
        // Struct types need the field shape; this stub only allocates
        // the marker — see `lower_ty_in` for the concrete shape.
        HirTy::Struct(id) => MirTy::Struct(*id, Vec::new()),
        // Unit-only enums lower to a plain i32 tag (caller without
        // module context can't see payloads).
        HirTy::Enum(_) => MirTy::Prim(PrimTy::I32),
        HirTy::Array(elem, n) => MirTy::Array(Box::new(lower_ty(elem)), *n),
        // Spec 4.4: every function value — named fn or closure — is
        // `{code, env}`: `code` takes the `GcRef` env first; a named fn's
        // env is null, a closure's is its boxed captures. Bounds (`+ Send`)
        // don't change the layout.
        HirTy::Fn(args, ret, _) | HirTy::Closure { args, ret, .. } => {
            fat_fn(args.iter().map(lower_ty).collect(), lower_ty(ret))
        }
        HirTy::Throws { ok, err } => carrier(lower_ty(ok), lower_ty(err)),
        HirTy::GcBuf(_) => MirTy::GcRef,
    }
}

/// `{code: fn(GcRef env, args..) -> ret, env: GcRef}`.
#[must_use]
pub fn fat_fn(args: Vec<MirTy>, ret: MirTy) -> MirTy {
    MirTy::Tuple(vec![code_ty(args, ret), MirTy::GcRef])
}

/// The code pointer of a function value: the env comes first.
#[must_use]
pub fn code_ty(args: Vec<MirTy>, ret: MirTy) -> MirTy {
    let mut all = vec![MirTy::GcRef];
    all.extend(args);
    MirTy::Fn(all, Box::new(ret))
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
        HirTy::Fn(args, ret, _) | HirTy::Closure { args, ret, .. } => fat_fn(
            args.iter().map(|a| lower_ty_in(a, module)).collect(),
            lower_ty_in(ret, module),
        ),
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
/// wide as the widest one; any other mix (aggregates, `str`) shares a
/// byte-array union `[uN; k]` with the max size and max align (N bits
/// = max align). Both are written / read through `RValue::Bitcast`.
#[must_use]
pub fn unify_payload(payloads: &[MirTy]) -> Option<MirTy> {
    let first = payloads.first()?;
    if payloads.iter().all(|p| p == first) {
        return Some(first.clone());
    }
    let uint = |bytes: u32| {
        MirTy::Prim(match bytes {
            1 => PrimTy::U8,
            2 => PrimTy::U16,
            4 => PrimTy::U32,
            _ => PrimTy::U64,
        })
    };
    if payloads
        .iter()
        .all(|p| matches!(p, MirTy::Prim(q) if *q != PrimTy::Str))
    {
        let bytes = payloads.iter().map(|p| size_align(p).0).max()?;
        return Some(uint(bytes.max(1)));
    }
    let (size, align) = payloads
        .iter()
        .map(size_align)
        .fold((0, 1), |(s, a), (ps, pa)| (s.max(ps), a.max(pa)));
    // A union that can hold a GC reference is all `GcRef` words (a
    // `GcRef` is word-aligned, so it always lands on one), so the
    // collector sees it; non-reference bits there are ignored by it.
    let elem = if payloads.iter().any(has_gc_ref) {
        MirTy::GcRef
    } else {
        uint(align)
    };
    Some(MirTy::Array(Box::new(elem), size.div_ceil(align)))
}

/// `ty` contains a word the collector must see: a `GcRef`, or a `str`
/// (whose pointer may point into a GC string, like codegen's `gc_paths`).
#[must_use]
pub fn has_gc_ref(ty: &MirTy) -> bool {
    match ty {
        MirTy::GcRef | MirTy::Prim(PrimTy::Str) => true,
        MirTy::Tuple(ps) | MirTy::Struct(_, ps) => ps.iter().any(has_gc_ref),
        MirTy::Array(t, _) => has_gc_ref(t),
        MirTy::Sum(ps) => has_gc_ref(&sum_layout(ps)),
        _ => false,
    }
}

/// `(size, align)` in bytes under the C / LLVM default layout of a
/// 64-bit target.
// ponytail: 64-bit pointers assumed (MIR doesn't know the target);
// thread the pointer width through once a 32-bit target exists.
#[must_use]
pub fn size_align(ty: &MirTy) -> (u32, u32) {
    match ty {
        MirTy::Unit => (0, 1),
        MirTy::Any | MirTy::GcRef | MirTy::Fn(_, _) => (8, 8),
        MirTy::Prim(PrimTy::Str) => (16, 8),
        MirTy::Prim(p) => {
            let b = p.bit_width(64) / 8;
            (b, b)
        }
        MirTy::Sum(parts) => size_align(&sum_layout(parts)),
        MirTy::Array(elem, n) => {
            let (s, a) = size_align(elem);
            (s * n, a)
        }
        MirTy::Tuple(fields) | MirTy::Struct(_, fields) => {
            let (mut size, mut align) = (0u32, 1u32);
            for f in fields {
                let (s, a) = size_align(f);
                size = size.next_multiple_of(a) + s;
                align = align.max(a);
            }
            (size.next_multiple_of(align), align)
        }
    }
}

fn enum_payloads(variants: &[rokc_hir::HirEnumVariant], module: &HirModule) -> Vec<MirTy> {
    variants
        .iter()
        .filter_map(|v| v.payload_ty.as_ref().map(|p| lower_ty_in(p, module)))
        // A unit payload (`Poll<()>::Ready(())`) takes no space.
        .filter(|t| *t != MirTy::Unit)
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

#[cfg(test)]
mod tests {
    use super::*;

    const fn p(t: PrimTy) -> MirTy {
        MirTy::Prim(t)
    }

    #[test]
    fn c_layout_sizes() {
        assert_eq!(size_align(&MirTy::Unit), (0, 1));
        assert_eq!(size_align(&p(PrimTy::Bool)), (1, 1));
        assert_eq!(size_align(&p(PrimTy::Str)), (16, 8));
        // (i8, i64, i16): padding after i8 and at the tail.
        let t = MirTy::Tuple(vec![p(PrimTy::I8), p(PrimTy::I64), p(PrimTy::I16)]);
        assert_eq!(size_align(&t), (24, 8));
        assert_eq!(
            size_align(&MirTy::Array(Box::new(p(PrimTy::U16)), 3)),
            (6, 2)
        );
    }

    #[test]
    fn sum_layouts() {
        // No payload: a bare tag.
        assert_eq!(sum_layout(&[]), p(PrimTy::I32));
        let i32_ = p(PrimTy::I32);
        // Differing scalars share an unsigned int as wide as the widest.
        assert_eq!(
            sum_layout(&[p(PrimTy::I8), p(PrimTy::F64)]),
            MirTy::Tuple(vec![i32_.clone(), p(PrimTy::U64)])
        );
        // Identical payloads keep their type.
        assert_eq!(
            sum_layout(&[p(PrimTy::Str), p(PrimTy::Str)]),
            MirTy::Tuple(vec![i32_, p(PrimTy::Str)])
        );
        // Aggregates without references: a byte-array union.
        let pair = MirTy::Tuple(vec![p(PrimTy::I32), p(PrimTy::I32)]);
        assert_eq!(
            unify_payload(&[pair, p(PrimTy::I16)]),
            Some(MirTy::Array(Box::new(p(PrimTy::U32)), 2))
        );
    }

    #[test]
    fn str_in_a_union_stays_gc_visible() {
        // Regression: `enum E { S(str), P(i64, i64) }` once unified to
        // `[u64; 2]`, so a collection freed the runtime string.
        assert!(has_gc_ref(&p(PrimTy::Str)));
        let pair = MirTy::Tuple(vec![p(PrimTy::I64), p(PrimTy::I64)]);
        assert_eq!(
            unify_payload(&[p(PrimTy::Str), pair]),
            Some(MirTy::Array(Box::new(MirTy::GcRef), 2))
        );
        assert!(!has_gc_ref(&p(PrimTy::I64)));
        assert!(has_gc_ref(&MirTy::Sum(vec![p(PrimTy::I64), MirTy::GcRef])));
    }
}

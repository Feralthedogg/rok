//! HIR → MIR type lowering.

use rokc_hir::{HirModule, HirTy};
use rokc_ir_common::PrimTy;

use crate::{MirTy, Target};

/// Struct id marking the MIR type of an `any Tr` value, so the
/// collector's `ScanTable` gets an `ANY_SLOT` (802 §8.2.7) for it.
pub const ANY_STRUCT: rokc_hir::StructId = rokc_hir::StructId(u32::MAX);

/// `any Tr`: `(i32 tag, payload word)`. The payload is the value itself
/// when [`any_inline`], else a GC reference to a boxed copy.
#[must_use]
pub fn any_ty() -> MirTy {
    MirTy::Struct(ANY_STRUCT, vec![MirTy::Prim(PrimTy::I32), MirTy::GcRef])
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
/// a unit `ok` left out (HIR reads the fields at the same indices). The
/// payloads sit side by side, not in a union: `ref` parameters ride the
/// ok slot on the error path too.
fn carrier(ok: MirTy, err: MirTy) -> MirTy {
    let mut fields = vec![MirTy::Prim(PrimTy::Bool)];
    if ok != MirTy::Unit {
        fields.push(ok);
    }
    fields.push(err);
    MirTy::Tuple(fields)
}

/// The MIR type of `ty` on `target`.
#[must_use]
pub fn lower_ty(ty: &HirTy, module: &HirModule, target: &Target) -> MirTy {
    let lower = |t: &HirTy| lower_ty(t, module, target);
    match ty {
        HirTy::Unknown
        | HirTy::Path(_)
        | HirTy::Any
        | HirTy::None
        | HirTy::Const(..)
        | HirTy::OpenConst(_)
        | HirTy::NoThrow
        | HirTy::Var(_) => MirTy::Any,
        // `!` has no values; a diverging call returns nothing.
        HirTy::Unit | HirTy::Never => MirTy::Unit,
        HirTy::Prim(p) => MirTy::Prim(*p),
        HirTy::AnyTrait(_) => any_ty(),
        HirTy::Struct(id) => {
            let def = &module.structs[id.0 as usize];
            let fields = match &def.union_kind {
                Some(u) if matches!(u.storage, rokc_hir::UnionStorage::ByteArray) => {
                    vec![union_storage(&u.aliases, module, target)]
                }
                _ => def.fields.iter().map(|f| lower(&f.ty)).collect(),
            };
            MirTy::Struct(*id, fields)
        }
        HirTy::Sum(parts) => match crate::lower::niche::sum_niche(ty, module, target) {
            Some((m, n)) => crate::lower::niche::sum_repr(m, &n, module, target),
            None => sum_layout(
                &parts
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| !v.is_none())
                    .map(|(i, v)| (sum_tag(ty, i as u32), lower(v)))
                    .collect::<Vec<_>>(),
                target,
            ),
        },
        HirTy::Tuple(parts) => MirTy::Tuple(parts.iter().map(lower).collect()),
        HirTy::Enum(id) => {
            let def = &module.enums[id.0 as usize];
            match sum_layout(&enum_payloads(&def.variants, module, target), target) {
                // `#[repr(u8)]` ..: a fieldless enum is its tag.
                MirTy::Prim(PrimTy::I32) => MirTy::Prim(def.repr.int.unwrap_or(PrimTy::I32)),
                l => l,
            }
        }
        HirTy::Array(elem, n) => MirTy::Array(Box::new(lower(elem)), *n),
        // Spec 4.4: every function value (named fn or closure) is
        // `{code, env}`: `code` takes the `GcRef` env first; a named fn's
        // env is null. A C function pointer is the bare code pointer.
        HirTy::Fn(args, ret, _) if ty.is_c_fn() => {
            MirTy::Fn(args.iter().map(lower).collect(), Box::new(lower(ret)))
        }
        HirTy::Fn(args, ret, _) | HirTy::Closure { args, ret, .. } => {
            fat_fn(args.iter().map(lower).collect(), lower(ret))
        }
        HirTy::Throws { ok, err } => carrier(lower(ok), lower(err)),
        HirTy::GcBuf(_) => MirTy::GcRef,
        HirTy::Mlir(t) => MirTy::Mlir(t.clone()),
    }
}

/// Stored tag of member `index` of `sum_ty`. A sum with `none` stores
/// `none` as tag 0 and shifts the members before it up by one, so
/// zeroed memory (a fresh `GcBuf` / `List` slot) reads back as `none`.
/// HIR keeps the canonical member index (`none` last); only the bits
/// differ. A niche sum (`lower::niche`) has no tag field but tests as
/// these tags too. Other types (enums, `any`) store the index as is.
#[must_use]
pub fn sum_tag(sum_ty: &HirTy, index: u32) -> u32 {
    let HirTy::Sum(parts) = sum_ty else {
        return index;
    };
    match parts.iter().position(HirTy::is_none).map(|k| k as u32) {
        Some(k) if index == k => 0,
        Some(k) if index < k => index + 1,
        _ => index,
    }
}

/// The single tagged-union layout shared by enums and sums:
/// `(i32 tag, payload)`, or a bare `i32` tag when nothing carries data.
/// `payloads` are `(stored tag, payload)`, without `none` / unit
/// variants.
#[must_use]
pub fn sum_layout(payloads: &[(u32, MirTy)], target: &Target) -> MirTy {
    match unify_payload(payloads, target) {
        Some(p) => MirTy::Tuple(vec![MirTy::Prim(PrimTy::I32), p]),
        None => MirTy::Prim(PrimTy::I32),
    }
}

/// Payload slot able to hold every variant. Identical payloads share
/// their type; differing scalar payloads share an unsigned integer as
/// wide as the widest one; any other mix (aggregates, `str`) shares a
/// byte-array union `[uN; k]` with the max size and max align (N bits
/// = max align), or a [`MirTy::Union`] when a payload holds a GC
/// reference. All are written / read through `RValue::Bitcast`.
#[must_use]
pub fn unify_payload(variants: &[(u32, MirTy)], target: &Target) -> Option<MirTy> {
    let payloads: Vec<&MirTy> = variants.iter().map(|(_, p)| p).collect();
    let first = *payloads.first()?;
    if payloads.iter().all(|p| *p == first) {
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
        let bytes = payloads.iter().map(|p| target.size_align(p).0).max()?;
        return Some(uint(bytes.max(1)));
    }
    let (size, align) = payloads
        .iter()
        .map(|p| target.size_align(p))
        .fold((0, 1), |(s, a), (ps, pa)| (s.max(ps), a.max(pa)));
    // A union that can hold a GC reference is pointer-width words (a
    // `GcRef` is word-aligned, so it always lands on one) that keep the
    // variants: the collector decodes the tag and scans only the active
    // variant's reference words.
    if payloads.iter().any(|p| target.has_gc_ref(p)) {
        let w = target.pointer_width / 8;
        return Some(MirTy::Union(variants.to_vec(), size.div_ceil(w)));
    }
    Some(MirTy::Array(Box::new(uint(align)), size.div_ceil(align)))
}

/// Storage of a byte-array `union`: every field overlaid at offset 0,
/// sized and aligned for the largest. Words a field may keep a
/// reference in are a bare [`MirTy::Union`], scanned as ambiguous.
fn union_storage(fields: &[(String, HirTy)], module: &HirModule, target: &Target) -> MirTy {
    let tys: Vec<(u32, MirTy)> = (0u32..)
        .zip(fields.iter().map(|(_, t)| lower_ty(t, module, target)))
        .collect();
    let (size, align) = tys
        .iter()
        .map(|(_, t)| target.size_align(t))
        .fold((1, 1), |(s, a), (ps, pa)| (s.max(ps), a.max(pa)));
    if tys.iter().any(|(_, t)| target.has_gc_ref(t)) {
        let w = target.pointer_width / 8;
        return MirTy::Union(tys, size.div_ceil(w));
    }
    // Words of the alignment, up to 8; a more aligned member raises
    // the union struct's own alignment (`union_align`).
    let (word, w) = match align {
        1 => (PrimTy::U8, 1),
        2 => (PrimTy::U16, 2),
        4 => (PrimTy::U32, 4),
        _ => (PrimTy::U64, 8),
    };
    MirTy::Array(Box::new(MirTy::Prim(word)), size.div_ceil(w))
}

/// The alignment of a byte-array union's most aligned member, when past
/// what its storage words give (8): the union struct is aligned so.
#[must_use]
pub fn union_align(def: &rokc_hir::HirStructDef, module: &HirModule, target: &Target) -> u32 {
    let Some(u) = def.union_kind.as_ref() else {
        return 0;
    };
    if !matches!(u.storage, rokc_hir::UnionStorage::ByteArray) {
        return 0;
    }
    let align = u
        .aliases
        .iter()
        .map(|(_, t)| target.size_align(&lower_ty(t, module, target)).1)
        .max()
        .unwrap_or(1);
    if align > 8 { align } else { 0 }
}

/// `(tag, payload)` of the variants that carry data (the tag is the
/// variant index).
fn enum_payloads(
    variants: &[rokc_hir::HirEnumVariant],
    module: &HirModule,
    target: &Target,
) -> Vec<(u32, MirTy)> {
    variants
        .iter()
        .enumerate()
        .filter_map(|(i, v)| {
            v.payload_ty
                .as_ref()
                .map(|p| (i as u32, lower_ty(p, module, target)))
        })
        // A unit payload (`Poll<()>::Ready(())`) takes no space.
        .filter(|(_, t)| *t != MirTy::Unit)
        .collect()
}

/// The shared payload slot of enum `id`; `None` without payloads.
#[must_use]
pub fn enum_payload_ty(id: rokc_hir::EnumId, module: &HirModule, target: &Target) -> Option<MirTy> {
    match sum_layout(
        &enum_payloads(&module.enums[id.0 as usize].variants, module, target),
        target,
    ) {
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

    /// Payloads tagged 0, 1, ..
    fn tagged(ps: &[MirTy]) -> Vec<(u32, MirTy)> {
        ps.iter()
            .cloned()
            .enumerate()
            .map(|(i, p)| (i as u32, p))
            .collect()
    }

    fn x64() -> Target {
        Target::new(Some("x86_64-unknown-linux-gnu"))
    }

    #[test]
    fn sum_layouts() {
        let t = x64();
        // No payload: a bare tag.
        assert_eq!(sum_layout(&tagged(&[]), &t), p(PrimTy::I32));
        let i32_ = p(PrimTy::I32);
        // Differing scalars share an unsigned int as wide as the widest.
        assert_eq!(
            sum_layout(&tagged(&[p(PrimTy::I8), p(PrimTy::F64)]), &t),
            MirTy::Tuple(vec![i32_.clone(), p(PrimTy::U64)])
        );
        // Identical payloads keep their type.
        assert_eq!(
            sum_layout(&tagged(&[p(PrimTy::Str), p(PrimTy::Str)]), &t),
            MirTy::Tuple(vec![i32_, p(PrimTy::Str)])
        );
        // Aggregates without references: a byte-array union.
        let pair = MirTy::Tuple(vec![p(PrimTy::I32), p(PrimTy::I32)]);
        assert_eq!(
            unify_payload(&tagged(&[pair, p(PrimTy::I16)]), &t),
            Some(MirTy::Array(Box::new(p(PrimTy::U32)), 2))
        );
    }

    #[test]
    fn c_fn_or_none_is_a_bare_pointer() {
        let (t, m) = (x64(), HirModule::default());
        let i64_ = HirTy::Prim(PrimTy::I64);
        let c_fn = HirTy::Fn(
            vec![i64_.clone()],
            Box::new(i64_.clone()),
            rokc_hir::FnBounds {
                c_abi: true,
                ..rokc_hir::FnBounds::default()
            },
        );
        let none = HirTy::None;
        let thin = MirTy::Fn(vec![p(PrimTy::I64)], Box::new(p(PrimTy::I64)));
        let niche = |s: &HirTy| crate::lower::niche::sum_niche(s, &m, &t).map(|(_, n)| n);
        for parts in [
            vec![c_fn.clone(), none.clone()],
            vec![none.clone(), c_fn.clone()],
        ] {
            let sum = HirTy::Sum(parts);
            assert_eq!(niche(&sum).map(|n| n.bits), Some(0));
            assert_eq!(lower_ty(&sum, &m, &t), thin);
            // Non-null tests as the fn member's stored tag.
            assert_eq!(sum_tag(&sum, sum_tag_index(&sum, &c_fn)), 1);
        }
        assert!(!t.has_gc_ref(&thin));
        // A wider sum keeps the tagged layout.
        let wide = HirTy::Sum(vec![c_fn, i64_, none.clone()]);
        assert!(niche(&wide).is_none());
        assert!(matches!(lower_ty(&wide, &m, &t), MirTy::Tuple(_)));
        // A rok `fn` value or none is no niche.
        let rok_fn = HirTy::Fn(vec![], Box::new(HirTy::Unit), rokc_hir::FnBounds::default());
        assert!(niche(&HirTy::Sum(vec![rok_fn, none])).is_none());
    }

    fn sum_tag_index(sum: &HirTy, member: &HirTy) -> u32 {
        let HirTy::Sum(parts) = sum else {
            unreachable!()
        };
        parts.iter().position(|m| m == member).unwrap() as u32
    }

    #[test]
    fn str_in_a_union_stays_gc_visible() {
        // `enum E { S(str), P(i64, i64) }` once unified to `[u64; 2]`, so a
        // collection freed the runtime string.
        let t = x64();
        assert!(t.has_gc_ref(&p(PrimTy::Str)));
        let pair = MirTy::Tuple(vec![p(PrimTy::I64), p(PrimTy::I64)]);
        let vs = tagged(&[p(PrimTy::Str), pair]);
        assert_eq!(unify_payload(&vs, &t), Some(MirTy::Union(vs, 2)));
        assert!(!t.has_gc_ref(&p(PrimTy::I64)));
    }

    #[test]
    fn unions_follow_the_pointer_width() {
        // `str | i64` on a 32-bit target: an 8-byte `str`, 4-aligned.
        let t = Target::new(Some("i686-unknown-linux-gnu"));
        let vs = tagged(&[p(PrimTy::Str), p(PrimTy::I64)]);
        assert_eq!(unify_payload(&vs, &t), Some(MirTy::Union(vs, 2)));
    }
}

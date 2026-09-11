//! Type lowering: AST `Ty` → `HirTy`.
//!
//! Primitive type names are recognised by spelling, not through the
//! library's `#[lang]` slots.

use rokc_ast::{Path, Ty, TyKind};
use rokc_ir_common::PrimTy;

use crate::HirTy;

/// A written sum `A | B | ..` (spec 2.6.4): a member that is itself a
/// written sum (or an alias of one) spreads into the set, so
/// `(i32 | none) | none` is `i32 | none`. A generic member (`param`
/// names a type parameter; `Self`, `<T as Tr>::X`, `T::X`, `#nest<X>`) stays one
/// member, so `HirTy::sum` keeps it a nested layer when it overlaps the
/// written members: `T | none` with `T = i32 | none` is `(i32 | none)?`.
pub fn written_sum(
    parts: &[Ty],
    param: impl Fn(&str) -> bool,
    rec: impl Fn(&Ty) -> HirTy,
) -> HirTy {
    let generic = |t: &Ty| match &t.kind {
        TyKind::SelfUpper => true,
        TyKind::Path(p) => p
            .segments
            .first()
            .is_some_and(|s| s.name == "Self" || s.name == rokc_ast::QPATH_MARK || param(&s.name)),
        _ => false,
    };
    let mut out = Vec::new();
    for p in parts {
        if let Some(inner) = p.nest_inner() {
            out.push(rec(inner));
        } else if generic(p) {
            out.push(rec(p));
        } else {
            rec(p).spread(&mut out);
        }
    }
    HirTy::sum(out)
}

/// Resolve an AST type to HIR. Unknown paths are kept as `HirTy::Path`
/// for later resolution.
#[must_use]
pub fn resolve_ty(ty: &Ty) -> HirTy {
    match &ty.kind {
        TyKind::Path(path) => resolve_path_ty(path),
        TyKind::Never => HirTy::Never,
        TyKind::Sum(parts) => written_sum(parts, |_| false, resolve_ty),
        TyKind::Tuple(parts) => {
            if parts.is_empty() {
                HirTy::Unit
            } else {
                HirTy::Tuple(parts.iter().map(resolve_ty).collect())
            }
        }
        // Plain `any` = `any ()`: tag + payload, no bound.
        TyKind::Any => HirTy::AnyTrait(Vec::new()),
        TyKind::AnyTrait(bounds) => HirTy::AnyTrait(
            bounds
                .iter()
                .map(|b| {
                    b.segments
                        .iter()
                        .map(|s| s.name.as_str())
                        .collect::<Vec<_>>()
                        .join("::")
                })
                .collect(),
        ),
        TyKind::None => HirTy::Path(vec!["none".to_owned()]),
        TyKind::SelfUpper => HirTy::Path(vec!["Self".to_owned()]),
        TyKind::Array(elem, len) => {
            let n = const_expr_to_u32(len).unwrap_or(0);
            HirTy::Array(Box::new(resolve_ty(elem)), n)
        }
        // Name-free resolution (prim probes) drops `+ Send` bounds.
        TyKind::Fn(args, ret, _) => HirTy::Fn(
            args.iter().map(resolve_ty).collect(),
            Box::new(resolve_ty(ret)),
            Vec::new(),
        ),
        TyKind::Throws { ok, err } => throws_ty(resolve_ty(ok), resolve_ty(err)),
        TyKind::Const(c) => {
            const_expr_to_u32(c).map_or(HirTy::Unknown, |v| const_ty(v.into(), None))
        }
    }
}

/// A const generic argument carried in a type substitution (spec 2.11):
/// `Path(["#const", value, prim])` (`#` cannot start a user name; `prim`
/// is empty until the parameter's declared type is known).
#[must_use]
pub fn const_ty(value: i128, prim: Option<PrimTy>) -> HirTy {
    HirTy::Path(vec![
        "#const".to_owned(),
        value.to_string(),
        prim.map_or_else(String::new, |p| p.name().to_owned()),
    ])
}

/// The value (and declared type, if known) of a `const_ty`.
#[must_use]
pub fn as_const(t: &HirTy) -> Option<(i128, Option<PrimTy>)> {
    let HirTy::Path(p) = t else { return None };
    match p.as_slice() {
        [tag, v, prim] if tag == "#const" => Some((v.parse().ok()?, {
            use PrimTy as P;
            [
                P::I8,
                P::I16,
                P::I32,
                P::I64,
                P::Isize,
                P::U8,
                P::U16,
                P::U32,
                P::U64,
                P::Usize,
                P::Bool,
                P::CChar,
            ]
            .into_iter()
            .find(|q| q.name() == prim)
        })),
        _ => None,
    }
}

/// What a `rethrows` error parameter binds to for a non-throwing
/// argument (`#` cannot start a user identifier).
pub const NOTHROW: &str = "#nothrow";

pub fn nothrow_ty() -> HirTy {
    HirTy::Path(vec![NOTHROW.to_owned()])
}

/// `throws (err) -> ok`, normalized: nested error sums are flattened and
/// deduplicated, `NOTHROW` parts dropped — no error left means a plain
/// `ok` (a `rethrows` instance with non-throwing arguments).
pub fn throws_ty(ok: HirTy, err: HirTy) -> HirTy {
    let parts: Vec<HirTy> = match HirTy::sum([err]) {
        HirTy::Sum(ps) => ps,
        t => vec![t],
    };
    let parts: Vec<HirTy> = parts
        .into_iter()
        .filter(|p| !matches!(p, HirTy::Path(p) if p.len() == 1 && p[0] == NOTHROW))
        .collect();
    if parts.is_empty() {
        return ok;
    }
    let err = HirTy::sum(parts);
    HirTy::Throws {
        ok: Box::new(ok),
        err: Box::new(err),
    }
}

// Name-free: literals and arithmetic over them.
fn const_expr_to_u32(c: &rokc_ast::ConstExpr) -> Option<u32> {
    crate::lower::const_eval::syntactic_int(c, &|_| None).and_then(|v| u32::try_from(v).ok())
}

fn resolve_path_ty(path: &Path) -> HirTy {
    if path.segments.len() == 1 {
        if let Some(prim) = match path.segments[0].name.as_str() {
            "i8" => Some(PrimTy::I8),
            "i16" => Some(PrimTy::I16),
            "i32" => Some(PrimTy::I32),
            "i64" => Some(PrimTy::I64),
            "isize" => Some(PrimTy::Isize),
            "u8" => Some(PrimTy::U8),
            "u16" => Some(PrimTy::U16),
            "u32" => Some(PrimTy::U32),
            "u64" => Some(PrimTy::U64),
            "usize" => Some(PrimTy::Usize),
            "f32" => Some(PrimTy::F32),
            "f64" => Some(PrimTy::F64),
            "bool" => Some(PrimTy::Bool),
            "c_char" => Some(PrimTy::CChar),
            "char" => Some(PrimTy::Char),
            "str" => Some(PrimTy::Str),
            _ => None,
        } {
            return HirTy::Prim(prim);
        }
    }
    HirTy::Path(path.segments.iter().map(|s| s.name.clone()).collect())
}

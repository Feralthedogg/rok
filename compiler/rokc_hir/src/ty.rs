//! Type lowering: AST `Ty` → `HirTy`.
//!
//! Primitive type names (`i32`, `f64`, `bool`, ...) are recognised here
//! so the rest of the compiler can lower without first running the stdlib
//! bootstrap. Once the stdlib registers `#[lang(...)]` markers these
//! mappings can be derived from the `DefTable` instead.

use rokc_ast::{Path, Ty, TyKind};
use rokc_ir_common::PrimTy;

use crate::HirTy;

/// Resolve an AST type to HIR. Unknown paths are kept as `HirTy::Path`
/// for later resolution.
#[must_use]
pub fn resolve_ty(ty: &Ty) -> HirTy {
    match &ty.kind {
        TyKind::Path(path) => resolve_path_ty(path),
        TyKind::Never => HirTy::Never,
        TyKind::Sum(parts) => HirTy::Sum(parts.iter().map(resolve_ty).collect()),
        TyKind::Tuple(parts) => {
            if parts.is_empty() {
                HirTy::Unit
            } else {
                HirTy::Tuple(parts.iter().map(resolve_ty).collect())
            }
        }
        // Plain `any` = `any ()`: tag + payload with no bound (D4).
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
        // ponytail: name-free resolution (prim probes) drops `+ Send` bounds.
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
    fn flatten(t: HirTy, out: &mut Vec<HirTy>) {
        match t {
            HirTy::Sum(parts) => parts.into_iter().for_each(|p| flatten(p, out)),
            HirTy::Path(p) if p.len() == 1 && p[0] == NOTHROW => {}
            t if !out.contains(&t) => out.push(t),
            _ => {}
        }
    }
    let mut parts = Vec::new();
    flatten(err, &mut parts);
    let err = match parts.len() {
        0 => return ok,
        1 => parts.pop().expect("one part"),
        _ => HirTy::Sum(parts),
    };
    HirTy::Throws {
        ok: Box::new(ok),
        err: Box::new(err),
    }
}

// Name-free: literals and arithmetic over them.
fn const_expr_to_u32(c: &rokc_ast::ConstExpr) -> Option<u32> {
    eval_const_with(c, &|_| None).and_then(|v| u32::try_from(v).ok())
}

/// A const expression (spec 2.11.5) over decimal literals, names
/// `lookup` knows, unary `-` and `+ - * / %`.
pub fn eval_const_with(
    c: &rokc_ast::ConstExpr,
    lookup: &dyn Fn(&str) -> Option<i128>,
) -> Option<i128> {
    fn lit(s: &str) -> Option<i128> {
        let s: String = s.chars().filter(|c| *c != '_').collect();
        let (radix, body) = match s.get(..2) {
            Some("0x") => (16, &s[2..]),
            Some("0o") => (8, &s[2..]),
            Some("0b") => (2, &s[2..]),
            _ => (10, s.as_str()),
        };
        // An `i32` / `usize` style suffix.
        let end = body.find(['i', 'u']).unwrap_or(body.len());
        i128::from_str_radix(&body[..end], radix).ok()
    }
    fn expr(e: &rokc_ast::Expr, lookup: &dyn Fn(&str) -> Option<i128>) -> Option<i128> {
        use rokc_ast::ExprKind as K;
        match &e.kind {
            K::Literal(rokc_ast::Literal::Int(s)) => lit(s),
            K::Path(p) if p.segments.len() == 1 => lookup(&p.segments[0].name),
            K::OpPrefix { op, operand } if op == "-" => expr(operand, lookup).map(|v| -v),
            K::OpInfix { op, lhs, rhs } => {
                let (a, b) = (expr(lhs, lookup)?, expr(rhs, lookup)?);
                match op.as_str() {
                    "+" => a.checked_add(b),
                    "-" => a.checked_sub(b),
                    "*" => a.checked_mul(b),
                    "/" => a.checked_div(b),
                    "%" => a.checked_rem(b),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    match c {
        rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Int(s)) => lit(s),
        rokc_ast::ConstExpr::Path(p) if p.segments.len() == 1 => lookup(&p.segments[0].name),
        rokc_ast::ConstExpr::Literal(_) | rokc_ast::ConstExpr::Path(_) => None,
        rokc_ast::ConstExpr::Expr(e) => expr(e, lookup),
    }
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

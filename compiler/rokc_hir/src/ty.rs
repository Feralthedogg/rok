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
        TyKind::Sum(parts) => HirTy::Sum(parts.iter().map(resolve_ty).collect()),
        TyKind::Tuple(parts) => {
            if parts.is_empty() {
                HirTy::Unit
            } else {
                HirTy::Tuple(parts.iter().map(resolve_ty).collect())
            }
        }
        TyKind::Any => HirTy::Any,
        TyKind::None => HirTy::Path(vec!["none".to_owned()]),
        TyKind::SelfUpper => HirTy::Path(vec!["Self".to_owned()]),
        TyKind::Array(elem, len) => {
            let n = const_expr_to_u32(len).unwrap_or(0);
            HirTy::Array(Box::new(resolve_ty(elem)), n)
        }
        TyKind::Fn(args, ret) => HirTy::Fn(
            args.iter().map(resolve_ty).collect(),
            Box::new(resolve_ty(ret)),
        ),
    }
}

// Best-effort: only literal integers are supported as array length so far.
fn const_expr_to_u32(c: &rokc_ast::ConstExpr) -> Option<u32> {
    let rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Int(s)) = c else {
        return None;
    };
    let cleaned: String = s.chars().take_while(|c| c.is_ascii_digit() || *c == '_').collect();
    let cleaned: String = cleaned.chars().filter(|c| *c != '_').collect();
    cleaned.parse::<u32>().ok()
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

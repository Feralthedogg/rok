//! `f"..."` (refs-lang 1.7.3, stdlib 2.10) by the holes' types:
//!
//! ```text
//! f"a {x:>8.2} b {s:^5}"   (x: f64, s: str)
//!   ==>  { let #f0 = x; let #f1 = s;
//!          rok::core::fmt::fstr_join(["a ",
//!              Format::format(#f0, FormatSpec::parse(">8.2")), " b ",
//!              fstr_str(#f1.display(), #f1.display(), "^5")]) }
//! ```
//!
//! Holes (and `${..}` spec expressions) are evaluated left to right into
//! temps, then formatted: an empty spec is `display()`, `?` alone is
//! `debug()`; a number (every integer and float type, `int` / `float`
//! included) goes through `core::fmt::Format`, any other value through
//! `fstr_str`. A static spec is checked here against the hole's type
//! with the runtime's own parser; a dynamic one (`${..}`, joined into the
//! spec text at run time) is checked when formatting. The pieces are
//! joined in one allocation.

use super::bignum::Big;
#[allow(clippy::wildcard_imports)]
use super::*;
use crate::fmt_spec;
use rokc_ast::{FStringPart, SpecPiece};
use rokc_diagnostic::Span;

pub(super) fn lower_fstring(ctx: &mut LowerCtx<'_>, parts: &[FStringPart], span: Span) -> HirExpr {
    ctx.push_scope();
    let mut stmts = Vec::new();
    let mut pieces = Vec::new();
    for part in parts {
        match part {
            FStringPart::Lit(text) => {
                pieces.push(mk(ExprKind::Literal(AstLit::Str(text.clone())), span));
            }
            FStringPart::Hole { expr, spec } => {
                let at = point(expr.span);
                let Some(value) = bind(ctx, &mut stmts, expr) else {
                    continue;
                };
                let ty = ctx.local_ty(local_of(ctx, &value));
                // The spec as text, or as a `str` expression when dynamic.
                let mut text = String::new();
                let mut dynamic = Vec::new();
                for piece in spec {
                    match piece {
                        SpecPiece::Text(t) => {
                            text.push_str(t);
                            dynamic.push(str_lit(t, at));
                        }
                        SpecPiece::Expr(e) => {
                            if let Some(v) = bind(ctx, &mut stmts, e) {
                                dynamic.push(method(v, "display", point(e.span)));
                            }
                        }
                    }
                }
                let is_dynamic = spec.iter().any(|p| matches!(p, SpecPiece::Expr(_)));
                let outer = rokc_diagnostic::set_current_span(at);
                let piece = if is_dynamic {
                    let spec_expr = join(dynamic, at);
                    // The type letter is unknown until run time: a non-number
                    // gets both renderings unless the spec visibly ends in `?`.
                    let letter = if text.ends_with('?') { b'?' } else { 0 };
                    Some(format(ctx, value, &ty, spec_expr, letter, true, at))
                } else {
                    static_piece(ctx, value, &ty, &text, at)
                };
                rokc_diagnostic::set_current_span(outer);
                if let Some(p) = piece {
                    pieces.push(p);
                }
            }
        }
    }
    let tail = lower_expr(ctx, &join(pieces, span));
    ctx.pop_scope();
    HirExpr {
        ty: HirTy::Prim(PrimTy::Str),
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing: Some(tail),
            label: None,
        })),
        span,
    }
}

/// `let #fN = e;` — the temp's path, or `None` when `e` didn't type.
fn bind(ctx: &mut LowerCtx<'_>, stmts: &mut Vec<HirStmt>, e: &Expr) -> Option<Expr> {
    // A hole has no expected type: the f-string's own `str` slot is not it.
    ctx.push_expected(HirTy::Unknown);
    let init = lower_expr(ctx, e);
    ctx.pop_expected();
    if init.ty == HirTy::Unknown {
        return None;
    }
    let name = format!("#f{}", ctx.locals.len());
    let local = ctx.declare(Some(name.clone()), init.ty.clone());
    stmts.push(HirStmt::Let { local, init });
    let at = point(e.span);
    Some(mk(ExprKind::Path(path(&[&name], at)), at))
}

/// The empty span at the start of `s`: diagnostics about the code made
/// for a hole land on the hole, but it covers no source (editor hover
/// finds the user's expression).
const fn point(s: Span) -> Span {
    Span { end: s.start, ..s }
}

fn local_of(ctx: &LowerCtx<'_>, e: &Expr) -> LocalId {
    let ExprKind::Path(p) = &e.kind else {
        unreachable!("a bound temp")
    };
    ctx.lookup(&p.segments[0].name).expect("bound temp")
}

/// A hole with a static spec: checked against the value's type here.
fn static_piece(ctx: &LowerCtx<'_>, value: Expr, ty: &HirTy, text: &str, at: Span) -> Option<Expr> {
    if text.is_empty() {
        return Some(method(value, "display", at));
    }
    if text == "?" {
        return Some(method(value, "debug", at));
    }
    let spec = match fmt_spec::parse(text) {
        Ok(s) => s,
        Err(why) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("invalid format spec `{text}`: {why} (refs-lang 1.7.3)"),
            );
            return None;
        }
    };
    let (int, float) = match (ty, super::bignum::big_of(ctx, ty)) {
        (HirTy::Prim(p), _) => (p.is_int(), p.is_float()),
        (_, Some(b)) => (b == Big::Int, b == Big::Float),
        _ => (false, false),
    };
    let needs = match spec.ty {
        b'b' | b'o' | b'x' | b'X' if !int => Some("an integer (stdlib 2.10.5)"),
        b'e' | b'E' | b'f' if !int && !float => Some("a number (stdlib 2.10.6)"),
        _ => None,
    };
    if let Some(needs) = needs {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "format type `{}` needs {needs}, found `{}`",
                char::from(spec.ty),
                ctx.ty_name(ty)
            ),
        );
        return None;
    }
    // Nothing to apply: the plain `Display` (a non-number's sign / `0` /
    // `#` flags do nothing).
    let plain = matches!(spec.ty, 0 | b's' | b'd' | b'g')
        && spec.width.is_none()
        && spec.precision.is_none()
        && (!(int || float) || (spec.sign != b'+' && spec.sign != b' '));
    if plain {
        return Some(method(value, "display", at));
    }
    Some(format(
        ctx,
        value,
        ty,
        str_lit(text, at),
        spec.ty,
        false,
        at,
    ))
}

/// The call formatting `value` per `spec` (a `str` expression): for a
/// number, `Format::format(value, FormatSpec::parse(spec))`; otherwise
/// `fstr_str(display, debug, spec)`. `letter` is the spec's type letter
/// when known (`0` otherwise).
fn format(
    ctx: &LowerCtx<'_>,
    value: Expr,
    ty: &HirTy,
    spec: Expr,
    letter: u8,
    dynamic: bool,
    at: Span,
) -> Expr {
    let call = |names: &[&str], args: Vec<Expr>| {
        mk(
            ExprKind::Call {
                callee: Box::new(mk(ExprKind::Path(path(names, at)), at)),
                args: args.into_iter().map(CallArg::Positional).collect(),
                trailing_closure: None,
            },
            at,
        )
    };
    let number = match ty {
        HirTy::Prim(p) => p.is_int() || p.is_float(),
        _ => super::bignum::big_of(ctx, ty).is_some(),
    };
    if number {
        let spec = call(&["rok", "core", "fmt", "FormatSpec", "parse"], vec![spec]);
        return call(
            &["rok", "core", "fmt", "Format", "format"],
            vec![value, spec],
        );
    }
    let display = ctx.lang_trait("display_trait");
    let debug = ctx.lang_trait("debug_trait");
    let (disp, dbg) = if letter == b'?' {
        let d = method(value, "debug", at);
        (d.clone(), d)
    } else if dynamic && ctx.implements_trait(ty, debug, 0) && ctx.implements_trait(ty, display, 0)
    {
        (
            method(value.clone(), "display", at),
            method(value, "debug", at),
        )
    } else if dynamic && !ctx.implements_trait(ty, display, 0) {
        let d = method(value, "debug", at);
        (d.clone(), d)
    } else {
        let d = method(value, "display", at);
        (d.clone(), d)
    };
    call(&["rok", "core", "fmt", "fstr_str"], vec![disp, dbg, spec])
}

/// The pieces as one `str`: `""`, the piece itself, `a + b`, or
/// `fstr_join([..])` for three or more.
fn join(mut pieces: Vec<Expr>, at: Span) -> Expr {
    match pieces.len() {
        0 => str_lit("", at),
        1 => pieces.pop().expect("one piece"),
        2 => {
            let rhs = pieces.pop().expect("two pieces");
            let lhs = pieces.pop().expect("two pieces");
            mk(
                ExprKind::OpInfix {
                    op: "+".to_owned(),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                at,
            )
        }
        _ => mk(
            ExprKind::Call {
                callee: Box::new(mk(
                    ExprKind::Path(path(&["rok", "core", "fmt", "fstr_join"], at)),
                    at,
                )),
                args: vec![CallArg::Positional(mk(ExprKind::List(pieces), at))],
                trailing_closure: None,
            },
            at,
        ),
    }
}

const fn mk(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}

fn path(names: &[&str], span: Span) -> AstPath {
    AstPath {
        segments: names
            .iter()
            .map(|n| rokc_ast::PathSegment {
                name: (*n).to_owned(),
                generics: Vec::new(),
            })
            .collect(),
        span,
    }
}

/// A `str` literal of `text`, taken as is (no escapes).
fn str_lit(text: &str, at: Span) -> Expr {
    mk(ExprKind::Literal(AstLit::RawStr(text.to_owned())), at)
}

fn method(recv: Expr, name: &str, span: Span) -> Expr {
    mk(
        ExprKind::MethodCall {
            receiver: Box::new(recv),
            method: name.to_owned(),
            type_args: Vec::new(),
            args: Vec::new(),
            trailing_closure: None,
        },
        span,
    )
}

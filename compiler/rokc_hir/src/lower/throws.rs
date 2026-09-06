//! Value-based errors (spec 4.14 as revised by decision D3): `throws`
//! signatures, `throw`, prefix `try` / `try?` / `try!`, postfix `catch`
//! / `finally`.
//!
//! A function declared `throws (E) -> T` returns the carrier
//! `HirTy::Throws { ok: T, err: E }` (MIR: `(is_err, T, E)`). Nothing
//! unwinds: a call under `try` tests `is_err` and on error `raise`s the
//! payload, which walks the enclosing `err_frames` innermost-first — a
//! `finally` frame runs its block inline, the first `catch` frame that
//! may take the error type parks the value and `break`s out of the catch
//! body to its dispatch — and with no frame left returns the error from
//! the function (converted to its `throws` type). `return` / `break` /
//! `continue` run the `finally` blocks they leave the same way.

#[allow(clippy::wildcard_imports)]
use super::*;

use super::desugar::{optional_parts, sum_none};

pub(super) enum ErrFrame {
    Catch(CatchFrame),
    Finally {
        block: Block,
        /// `try` nesting and breakable count where the `finally` sits;
        /// its block is lowered in that context at every exit.
        try_depth: u32,
        breakables: usize,
    },
}

pub(super) struct CatchFrame {
    /// The catch body runs in a block with this label; a raise breaks
    /// out of it.
    label: String,
    /// Error type each `catch` arm can take (`None` = any type), plus
    /// the local recording which parked error was raised. `None` for
    /// `try?` / `try!` / throwing `main`, which take every error.
    arms: Option<(Vec<Option<HirTy>>, LocalId)>,
    /// Distinct error types raised into this frame, each parked in its
    /// own local.
    errs: Vec<(HirTy, LocalId)>,
    /// Some raise reached this frame.
    hit: bool,
}

impl CatchFrame {
    fn takes(&self, ety: &HirTy) -> bool {
        self.arms
            .as_ref()
            .is_none_or(|(filters, _)| filters.iter().any(|f| may_take(f.as_ref(), ety)))
    }
}

/// Can an arm whose pattern names type `filter` (`None`: any) match an
/// error of type `ety`? An unresolved filter is kept so lowering the
/// arm reports it.
fn may_take(filter: Option<&HirTy>, ety: &HirTy) -> bool {
    let parts = |t: &HirTy| match t {
        HirTy::Sum(vs) => vs.clone(),
        t => vec![t.clone()],
    };
    match filter {
        None | Some(HirTy::Path(_) | HirTy::Unknown) => true,
        Some(f) => {
            let ps = parts(ety);
            parts(f).iter().any(|x| ps.contains(x))
        }
    }
}

/// The AST return type callers see: `ret_ty` (unit when absent),
/// wrapped in `Throws` when the fn declares `throws (E)`.
pub(super) fn sig_ret_ast(f: &FnDef) -> Ty {
    let ok = f.ret_ty.clone().unwrap_or(Ty {
        kind: AstTyKind::Tuple(Vec::new()),
        span: f.span,
    });
    let rokc_ast::ThrowsKind::Typed(errs) = &f.throws else {
        return ok;
    };
    let err = match errs.as_slice() {
        [] => return ok,
        [one] => one.clone(),
        many => Ty {
            kind: AstTyKind::Sum(many.to_vec()),
            span: f.span,
        },
    };
    Ty {
        span: ok.span,
        kind: AstTyKind::Throws {
            ok: Box::new(ok),
            err: Box::new(err),
        },
    }
}

/// An error type parameter not bound yet (a `rethrows` one, `#E0`, or a
/// plain `E`) → `Unknown`, so a call-argument hint `fn(i32) throws (E)
/// -> i32` still types a closure argument (whose error type is then
/// inferred).
pub(super) fn erase_unbound_errors(ty: &mut HirTy) {
    match ty {
        HirTy::Throws { ok, err } => {
            let unbound = |t: &HirTy| matches!(t, HirTy::Path(_));
            if unbound(err) || matches!(&**err, HirTy::Sum(vs) if vs.iter().any(unbound)) {
                **err = HirTy::Unknown;
            }
            erase_unbound_errors(ok);
        }
        HirTy::Fn(args, ret) | HirTy::Closure { args, ret, .. } => {
            args.iter_mut().for_each(erase_unbound_errors);
            erase_unbound_errors(ret);
        }
        HirTy::Sum(ts) | HirTy::Tuple(ts) => ts.iter_mut().for_each(erase_unbound_errors),
        _ => {}
    }
}

fn fresh_label(ctx: &mut LowerCtx<'_>) -> String {
    ctx.next_synth += 1;
    format!("#catch{}", ctx.next_synth)
}

const fn unit_value(span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr {
        kind: HirExprKind::Const(ConstVal::Unit),
        ty: HirTy::Unit,
        span,
    }
}

/// Placeholder for the unused payload slot of a carrier (codegen
/// materializes zero / undef).
fn undef(ty: &HirTy, span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr {
        kind: HirExprKind::Const(ConstVal::Unit),
        ty: ty.clone(),
        span,
    }
}

fn block_expr(stmts: Vec<HirStmt>, span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing: None,
            label: None,
        })),
        ty: HirTy::Unit,
        span,
    }
}

/// Carrier field index of the error payload (the unit `ok` slot is left
/// out, matching `rokc_mir`'s layout).
fn err_index(ok: &HirTy) -> u32 {
    if *ok == HirTy::Unit { 1 } else { 2 }
}

/// Build a carrier: `Ok(v)` → `(false, v, _)`, `Err(e)` → `(true, _, e)`.
fn carrier(
    ok: &HirTy,
    err: &HirTy,
    value: Result<HirExpr, HirExpr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let (is_err, ok_v, err_v) = match value {
        Ok(v) => (false, v, undef(err, span)),
        Err(e) => (true, undef(ok, span), e),
    };
    let mut lets = Vec::new();
    let mut fields = vec![HirExpr {
        kind: HirExprKind::Const(ConstVal::Bool(is_err)),
        ty: HirTy::Prim(PrimTy::Bool),
        span,
    }];
    if *ok == HirTy::Unit {
        // No slot, but keep the value's side effects.
        if !matches!(ok_v.kind, HirExprKind::Const(_)) {
            lets.push(HirStmt::Expr(ok_v));
        }
    } else {
        fields.push(ok_v);
    }
    fields.push(err_v);
    let ty = HirTy::Throws {
        ok: Box::new(ok.clone()),
        err: Box::new(err.clone()),
    };
    super::expr::with_lets(
        lets,
        HirExpr {
            kind: HirExprKind::Tuple { fields },
            ty,
            span,
        },
    )
}

/// A call whose type is a `throws` carrier: `{ let t = call; if
/// t.is_err { raise(t.err) } t.ok }`. It must sit under a `try`.
pub(super) fn unpack_call(ctx: &mut LowerCtx<'_>, call: HirExpr) -> HirExpr {
    let HirTy::Throws { ok, err } = call.ty.clone() else {
        return call;
    };
    let span = call.span;
    let carrier_ty = call.ty.clone();
    let tmp = ctx.declare(None, carrier_ty.clone());
    let field = |index: u32, ty: &HirTy| HirExpr {
        kind: HirExprKind::TupleField {
            target: Box::new(hir_local(tmp, &carrier_ty, span)),
            index,
            field_ty: ty.clone(),
        },
        ty: ty.clone(),
        span,
    };
    let mut stmts = vec![HirStmt::Let {
        local: tmp,
        init: call,
    }];
    if ctx.try_depth == 0 {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "this call can throw `{}` and must be marked with `try` (`try f()`; \
                 `try? f()` / `try! f()` to drop / panic on the error) (spec 4.14)",
                ctx.ty_name(&err)
            ),
        );
    } else {
        let raised = raise(ctx, field(err_index(&ok), &err), span);
        stmts.push(HirStmt::Expr(HirExpr {
            kind: HirExprKind::If {
                cond: Box::new(field(0, &HirTy::Prim(PrimTy::Bool))),
                then_block: Box::new(HirBlock {
                    stmts: raised,
                    trailing: None,
                    label: None,
                }),
                else_branch: None,
            },
            ty: HirTy::Unit,
            span,
        }));
    }
    let trailing = (*ok != HirTy::Unit).then(|| field(1, &ok));
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing,
            label: None,
        })),
        ty: *ok,
        span,
    }
}

/// Route error value `err` from the current point (see module doc).
/// The returned statements never complete normally.
pub(super) fn raise(
    ctx: &mut LowerCtx<'_>,
    err: HirExpr,
    span: rokc_diagnostic::Span,
) -> Vec<HirStmt> {
    let ety = err.ty.clone();
    let tmp = ctx.declare(None, ety.clone());
    let mut out = vec![HirStmt::Let {
        local: tmp,
        init: err,
    }];
    let value = hir_local(tmp, &ety, span);
    if ety == HirTy::Unknown {
        out.push(HirStmt::Return(None));
        return out;
    }
    // Under `catch` arms a sum error is raised variant by variant, so
    // each variant finds its own handler (or propagates on its own).
    if let HirTy::Sum(variants) = &ety {
        let has_arms = ctx
            .err_frames
            .iter()
            .any(|f| matches!(f, ErrFrame::Catch(c) if c.arms.is_some()));
        if has_arms {
            let arms = variants
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    let b = ctx.declare(None, v.clone());
                    let body = block_expr(raise(ctx, hir_local(b, v, span), span), span);
                    HirMatchArm {
                        pat: HirPattern::SumVariant {
                            sum_ty: ety.clone(),
                            variant_index: u32::try_from(i).expect("variant overflow"),
                            binder: Some(b),
                            payload_ty: Some(v.clone()),
                        },
                        guard: None,
                        body,
                    }
                })
                .collect();
            out.push(HirStmt::Expr(HirExpr {
                kind: HirExprKind::Match {
                    scrutinee: Box::new(value),
                    arms,
                },
                ty: HirTy::Unit,
                span,
            }));
            return out;
        }
    }
    for i in (0..ctx.err_frames.len()).rev() {
        let (label, which) = match &ctx.err_frames[i] {
            ErrFrame::Finally {
                block, try_depth, ..
            } => {
                let (block, td) = (block.clone(), *try_depth);
                out.push(run_finally(ctx, i, &block, td));
                continue;
            }
            ErrFrame::Catch(c) if c.takes(&ety) => (c.label.clone(), c.arms.as_ref().map(|a| a.1)),
            ErrFrame::Catch(_) => continue,
        };
        if let Some(which) = which {
            let parked = match &ctx.err_frames[i] {
                ErrFrame::Catch(c) => c.errs.iter().position(|(t, _)| *t == ety),
                ErrFrame::Finally { .. } => None,
            };
            let k = parked.unwrap_or_else(|| {
                let local = ctx.declare(None, ety.clone());
                let ErrFrame::Catch(c) = &mut ctx.err_frames[i] else {
                    unreachable!("frame {i} is a catch")
                };
                c.errs.push((ety.clone(), local));
                c.errs.len() - 1
            });
            let ErrFrame::Catch(c) = &ctx.err_frames[i] else {
                unreachable!("frame {i} is a catch")
            };
            out.push(HirStmt::Assign {
                local: c.errs[k].1,
                value,
            });
            out.push(HirStmt::Assign {
                local: which,
                value: hir_int(
                    i128::try_from(k).expect("error index fits"),
                    PrimTy::I32,
                    span,
                ),
            });
        }
        if let ErrFrame::Catch(c) = &mut ctx.err_frames[i] {
            c.hit = true;
        }
        out.push(HirStmt::Break {
            label: Some(label),
            value: None,
        });
        return out;
    }
    // No frame takes it: it leaves the function.
    if let Some(found) = &mut ctx.throws_probe {
        if !found.contains(&ety) {
            found.push(ety);
        }
    } else if let Some(decl) = ctx.fn_throws.clone() {
        if let Some(v) = convert_err(ctx, value, &decl) {
            let ok = ctx.fn_ret_ty.clone();
            out.push(HirStmt::Return(Some(carrier(&ok, &decl, Err(v), span))));
            return out;
        }
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "error `{}` is not covered by the enclosing function's `throws ({})` — \
                 catch it or add it to the `throws` list (spec 4.14)",
                ctx.ty_name(&ety),
                ctx.ty_name(&decl)
            ),
        );
    } else if ctx.implicit_main {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "error `{}` is not handled: top-level statements can't throw — catch it \
                 or use an explicit `fn main() throws ({0})` (spec 4.16)",
                ctx.ty_name(&ety)
            ),
        );
    } else {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "error `{}` is not handled: catch it, or declare `throws ({0})` on the \
                 enclosing function (spec 4.14)",
                ctx.ty_name(&ety)
            ),
        );
    }
    out.push(HirStmt::Return(None));
    out
}

/// Error `value` as a `to`-typed error: itself, injected into the sum
/// `to`, or (a sum whose variants all occur in `to`) re-wrapped variant
/// by variant. `None` when `to` can't hold it.
fn convert_err(ctx: &mut LowerCtx<'_>, value: HirExpr, to: &HirTy) -> Option<HirExpr> {
    let from = value.ty.clone();
    if from == *to {
        return Some(value);
    }
    match (&from, to) {
        (HirTy::Sum(vs), HirTy::Sum(ws)) if vs.iter().all(|v| ws.contains(v)) => {
            let span = value.span;
            let arms = vs
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    let b = ctx.declare(None, v.clone());
                    HirMatchArm {
                        pat: HirPattern::SumVariant {
                            sum_ty: from.clone(),
                            variant_index: u32::try_from(i).expect("variant overflow"),
                            binder: Some(b),
                            payload_ty: Some(v.clone()),
                        },
                        guard: None,
                        body: wrap_into_sum(to, hir_local(b, v, span)),
                    }
                })
                .collect();
            Some(HirExpr {
                kind: HirExprKind::Match {
                    scrutinee: Box::new(value),
                    arms,
                },
                ty: to.clone(),
                span,
            })
        }
        (_, HirTy::Sum(ws)) if ws.contains(&from) => Some(wrap_into_sum(to, value)),
        // Into `any Error` (untyped `throws`), boxing a concrete error.
        _ if coercible(ctx, to, &from) => {
            let boxed = box_into_any(ctx, to, value);
            Some(wrap_into_sum(to, boxed))
        }
        _ => None,
    }
}

/// Lower frame `i`'s `finally` block inline, outside that frame and
/// everything nested in it (a raise inside it goes outward).
fn run_finally(ctx: &mut LowerCtx<'_>, i: usize, block: &Block, try_depth: u32) -> HirStmt {
    let inner = ctx.err_frames.split_off(i);
    let saved = std::mem::replace(&mut ctx.try_depth, try_depth);
    ctx.push_expected(HirTy::Unit);
    let b = lower_block(ctx, block);
    ctx.pop_expected();
    ctx.try_depth = saved;
    ctx.err_frames.extend(inner);
    HirStmt::Expr(HirExpr {
        kind: HirExprKind::Block(Box::new(b)),
        ty: HirTy::Unit,
        span: block.span,
    })
}

/// `jump` (a `return` / `break` / `continue` carrying `value`) after the
/// `finally` blocks it leaves: every one for a `return` (`depth` =
/// `None`), else those inside breakable number `depth`.
pub(super) fn exit_through(
    ctx: &mut LowerCtx<'_>,
    depth: Option<usize>,
    value: Option<HirExpr>,
    jump: impl FnOnce(Option<HirExpr>) -> HirStmt,
    span: rokc_diagnostic::Span,
) -> HirStmt {
    let fins: Vec<usize> = (0..ctx.err_frames.len())
        .rev()
        .filter(|&i| {
            matches!(&ctx.err_frames[i], ErrFrame::Finally { breakables, .. }
                if depth.is_none_or(|d| *breakables > d))
        })
        .collect();
    if fins.is_empty() {
        return jump(value);
    }
    let mut stmts = Vec::new();
    let value = value.and_then(|v| {
        if v.ty == HirTy::Unit {
            stmts.push(HirStmt::Expr(v));
            return None;
        }
        let ty = v.ty.clone();
        let t = ctx.declare(None, ty.clone());
        stmts.push(HirStmt::Let { local: t, init: v });
        Some(hir_local(t, &ty, span))
    });
    for i in fins {
        let ErrFrame::Finally {
            block, try_depth, ..
        } = &ctx.err_frames[i]
        else {
            unreachable!("filtered to finally frames")
        };
        let (block, td) = (block.clone(), *try_depth);
        stmts.push(run_finally(ctx, i, &block, td));
    }
    stmts.push(jump(value));
    HirStmt::Expr(block_expr(stmts, span))
}

/// `return value` from the current point: wrapped into the ok carrier in
/// a throwing function, after the `finally` blocks it leaves.
pub(super) fn lower_return(
    ctx: &mut LowerCtx<'_>,
    value: Option<HirExpr>,
    span: rokc_diagnostic::Span,
) -> HirStmt {
    let value = match ctx.fn_throws.clone() {
        Some(err) => {
            let ok = ctx.fn_ret_ty.clone();
            let v = value.unwrap_or_else(|| unit_value(span));
            Some(carrier(&ok, &err, Ok(v), span))
        }
        None => value,
    };
    exit_through(ctx, None, value, HirStmt::Return, span)
}

/// Index in `ctx.breakables` of the target of a `break` / `continue`.
pub(super) fn jump_index(ctx: &LowerCtx<'_>, label: Option<&str>, needs_loop: bool) -> usize {
    ctx.breakables
        .iter()
        .rposition(|(bl, is_loop)| match label {
            None => *is_loop,
            Some(l) => bl.as_deref() == Some(l) && (*is_loop || !needs_loop),
        })
        .unwrap_or(usize::MAX)
}

/// `throw value;` — the value's type must be one the enclosing catch /
/// function `throws` accepts (checked when it is routed).
pub(super) fn lower_throw(
    ctx: &mut LowerCtx<'_>,
    value: &Expr,
    span: rokc_diagnostic::Span,
) -> HirStmt {
    let in_catch = ctx
        .err_frames
        .iter()
        .any(|f| matches!(f, ErrFrame::Catch(_)));
    let expected = if in_catch {
        HirTy::Unknown
    } else {
        ctx.fn_throws.clone().unwrap_or(HirTy::Unknown)
    };
    let v = lower_expected(ctx, value, expected);
    let stmts = raise(ctx, v, span);
    HirStmt::Expr(block_expr(stmts, span))
}

/// Push a frame that takes every error (`try?` / `try!` / throwing
/// `main`).
pub(super) fn catch_all_frame(ctx: &mut LowerCtx<'_>) {
    let label = fresh_label(ctx);
    ctx.err_frames.push(ErrFrame::Catch(CatchFrame {
        label,
        arms: None,
        errs: Vec::new(),
        hit: false,
    }));
}

fn pop_catch(ctx: &mut LowerCtx<'_>) -> CatchFrame {
    match ctx.err_frames.pop() {
        Some(ErrFrame::Catch(c)) => c,
        _ => unreachable!("frames are pushed and popped in pairs"),
    }
}

/// `'done: { '<frame>: { break 'done body }; handler }` — a raise into
/// the frame breaks out of the inner block into the handler; normal
/// completion skips it.
fn shell(
    ctx: &mut LowerCtx<'_>,
    frame: &CatchFrame,
    body: HirExpr,
    result_ty: HirTy,
    handler: (Vec<HirStmt>, Option<HirExpr>),
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let done = fresh_label(ctx);
    let inner_stmts = if hir_expr_diverges(&body) {
        vec![HirStmt::Expr(body)]
    } else if result_ty == HirTy::Unit {
        vec![
            HirStmt::Expr(body),
            HirStmt::Break {
                label: Some(done.clone()),
                value: None,
            },
        ]
    } else {
        vec![HirStmt::Break {
            label: Some(done.clone()),
            value: Some(body),
        }]
    };
    let inner = HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: inner_stmts,
            trailing: None,
            label: Some(frame.label.clone()),
        })),
        ty: HirTy::Unit,
        span,
    };
    let (handler_stmts, trailing) = handler;
    let mut stmts = vec![HirStmt::Expr(inner)];
    stmts.extend(handler_stmts);
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing,
            label: Some(done),
        })),
        ty: result_ty,
        span,
    }
}

/// `msg` to stderr through never-returning runtime hook `hook(msg, len)`.
pub(super) fn hook_call(
    ctx: &LowerCtx<'_>,
    hook: &str,
    msg: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let Some(sig) = ctx.env.fn_table.get(hook) else {
        return ctx.error_expr(
            span,
            format!("internal: runtime hook `{hook}` is not declared"),
        );
    };
    let len = i128::try_from(msg.len()).expect("message length fits i128");
    HirExpr {
        kind: HirExprKind::Call {
            callee: sig.id,
            args: vec![
                HirExpr {
                    kind: HirExprKind::Const(ConstVal::Str(msg.to_owned())),
                    ty: HirTy::Prim(PrimTy::Str),
                    span,
                },
                hir_int(len, PrimTy::Usize, span),
            ],
        },
        ty: HirTy::Unit,
        span,
    }
}

/// Prefix `try e` / `try? e` / `try! e`.
pub(super) fn lower_try(
    ctx: &mut LowerCtx<'_>,
    kind: rokc_ast::TryKind,
    operand: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    use rokc_ast::TryKind;
    let expected = ctx.current_expected().cloned().unwrap_or(HirTy::Unknown);
    if kind == TryKind::Plain {
        ctx.try_depth += 1;
        let e = lower_expected(ctx, operand, expected);
        ctx.try_depth -= 1;
        return e;
    }
    // `let x: i32 | none = try? f()` — the operand's slot is the payload.
    let inner_expected = match (kind, optional_parts(&expected)) {
        (TryKind::Optional, Some((_, some))) => super::desugar::without_none(&some),
        (TryKind::Optional, None) if expected != HirTy::Unit => HirTy::Unknown,
        _ => expected.clone(),
    };
    catch_all_frame(ctx);
    ctx.try_depth += 1;
    let body = lower_expected(ctx, operand, inner_expected);
    ctx.try_depth -= 1;
    let frame = pop_catch(ctx);
    if kind == TryKind::Force {
        if !frame.hit {
            return body;
        }
        let panic = hook_call(
            ctx,
            "rok_panic",
            "try! failed: the expression threw an error",
            span,
        );
        let ty = body.ty.clone();
        return shell(
            ctx,
            &frame,
            body,
            ty,
            (vec![HirStmt::Panic(panic)], None),
            span,
        );
    }
    // `try?` in statement position just drops the error.
    if expected == HirTy::Unit || body.ty == HirTy::Unit {
        if !frame.hit {
            return body;
        }
        return shell(ctx, &frame, body, HirTy::Unit, (Vec::new(), None), span);
    }
    let result_ty = if optional_parts(&body.ty).is_some() || body.ty == HirTy::Unknown {
        body.ty.clone()
    } else {
        HirTy::Sum(vec![body.ty.clone(), none_ty()])
    };
    let body = wrap_into_sum(&result_ty, body);
    if !frame.hit {
        return body;
    }
    let none = sum_none(&result_ty, span);
    shell(ctx, &frame, body, result_ty, (Vec::new(), Some(none)), span)
}

/// Wrap a throwing `main`'s body (spec 4.16.3): an error escaping it
/// prints a message and exits with status 1.
pub(super) fn uncaught_in_main(
    ctx: &mut LowerCtx<'_>,
    block: HirBlock,
    span: rokc_diagnostic::Span,
) -> HirBlock {
    let frame = pop_catch(ctx);
    if !frame.hit {
        return block;
    }
    let ty = if block.trailing.is_some() {
        ctx.fn_ret_ty.clone()
    } else {
        HirTy::Unit
    };
    let body = HirExpr {
        kind: HirExprKind::Block(Box::new(block)),
        ty: ty.clone(),
        span,
    };
    // ponytail: fixed message; printing the error value needs Display
    // dispatch (and `any Error`, D4).
    let report = hook_call(
        ctx,
        "rok_uncaught_error",
        "error: `main` returned an uncaught error",
        span,
    );
    let valued = ty != HirTy::Unit;
    let wrapped = shell(
        ctx,
        &frame,
        body,
        ty,
        (vec![HirStmt::Panic(report)], None),
        span,
    );
    // A unit / diverging body stays a statement: falling off the end of
    // an `i32` main is not a unit return.
    let (stmts, trailing) = if valued {
        (Vec::new(), Some(wrapped))
    } else {
        (vec![HirStmt::Expr(wrapped)], None)
    };
    HirBlock {
        stmts,
        trailing,
        label: None,
    }
}

/// A throwing function's body yields the ok carrier.
pub(super) fn finish_throwing_body(ctx: &LowerCtx<'_>, block: &mut HirBlock) {
    let Some(err) = ctx.fn_throws.clone() else {
        return;
    };
    let ok = ctx.fn_ret_ty.clone();
    match block.trailing.take() {
        Some(t) if hir_expr_diverges(&t) => block.trailing = Some(t),
        Some(t) => {
            let span = t.span;
            block.trailing = Some(carrier(&ok, &err, Ok(t), span));
        }
        None if hir_block_diverges(block) => {}
        None => {
            let span = rokc_diagnostic::Span::DUMMY;
            block.trailing = Some(carrier(&ok, &err, Ok(unit_value(span)), span));
        }
    }
}

/// Postfix `body catch pat { .. } ... finally { .. }`.
pub(super) fn lower_catch(
    ctx: &mut LowerCtx<'_>,
    body: &Expr,
    arms: &[rokc_ast::CatchArm],
    finally: Option<&Block>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let expected = ctx.current_expected().cloned().unwrap_or(HirTy::Unknown);
    if let Some(fin) = finally {
        ctx.err_frames.push(ErrFrame::Finally {
            block: fin.clone(),
            try_depth: ctx.try_depth,
            breakables: ctx.breakables.len(),
        });
    }
    let value = if arms.is_empty() {
        lower_expected(ctx, body, expected)
    } else {
        lower_catch_arms(ctx, body, arms, &expected, span)
    };
    if finally.is_none() {
        return value;
    }
    let Some(ErrFrame::Finally { block, .. }) = ctx.err_frames.pop() else {
        unreachable!("frames are pushed and popped in pairs")
    };
    if hir_expr_diverges(&value) {
        return value;
    }
    // Normal completion (body or handler value): run `finally`, then
    // yield the value.
    ctx.push_expected(HirTy::Unit);
    let fin = lower_block(ctx, &block);
    ctx.pop_expected();
    let ty = value.ty.clone();
    let mut stmts = Vec::new();
    let trailing = if ty == HirTy::Unit {
        stmts.push(HirStmt::Expr(value));
        None
    } else {
        let t = ctx.declare(None, ty.clone());
        stmts.push(HirStmt::Let {
            local: t,
            init: value,
        });
        Some(hir_local(t, &ty, span))
    };
    stmts.push(HirStmt::Expr(HirExpr {
        kind: HirExprKind::Block(Box::new(fin)),
        ty: HirTy::Unit,
        span,
    }));
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing,
            label: None,
        })),
        ty,
        span,
    }
}

fn lower_catch_arms(
    ctx: &mut LowerCtx<'_>,
    body: &Expr,
    arms: &[rokc_ast::CatchArm],
    expected: &HirTy,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let filters: Vec<Option<HirTy>> = arms.iter().map(|a| arm_filter(ctx, &a.pat)).collect();
    let which = ctx.declare(None, HirTy::Prim(PrimTy::I32));
    let label = fresh_label(ctx);
    ctx.err_frames.push(ErrFrame::Catch(CatchFrame {
        label,
        arms: Some((filters.clone(), which)),
        errs: Vec::new(),
        hit: false,
    }));
    let body_h = lower_expected(ctx, body, expected.clone());
    let frame = pop_catch(ctx);
    if frame.errs.is_empty() {
        // ponytail: arms that can never run aren't type-checked; a
        // "no error reaches this catch" warning needs warning plumbing.
        return body_h;
    }
    // Dispatch on the parked error: `if #which == k { match #err_k {
    // <arms that can take E_k>, _ => throw #err_k } } else ...`, built as
    // AST so arm patterns / bodies lower like any `match`. The `#` names
    // can't clash with user identifiers.
    ctx.next_synth += 1;
    let n = ctx.next_synth;
    ctx.push_scope();
    let which_name = format!("#which{n}");
    bind_name(ctx, &which_name, which);
    let mut branches = Vec::with_capacity(frame.errs.len());
    for (k, (ety, local)) in frame.errs.iter().enumerate() {
        let name = format!("#err{n}_{k}");
        bind_name(ctx, &name, *local);
        branches.push(dispatch_one(ctx, arms, &filters, ety, &name, span));
    }
    let mut chain = branches.pop().expect("at least one parked error");
    for (k, b) in branches.into_iter().enumerate().rev() {
        chain = Expr {
            kind: ExprKind::If {
                cond: Box::new(Expr {
                    kind: ExprKind::OpInfix {
                        op: "==".to_owned(),
                        lhs: Box::new(path_expr(&which_name, span)),
                        rhs: Box::new(Expr {
                            kind: ExprKind::Literal(AstLit::Int(k.to_string())),
                            span,
                        }),
                    },
                    span,
                }),
                then_branch: Block {
                    stmts: Vec::new(),
                    trailing: Some(Box::new(b)),
                    span,
                    label: None,
                },
                else_branch: Some(Box::new(chain)),
            },
            span,
        };
    }
    let body_div = hir_expr_diverges(&body_h);
    let hint = if *expected != HirTy::Unknown || body_div {
        expected.clone()
    } else {
        body_h.ty.clone()
    };
    let handler = lower_expected(ctx, &chain, hint.clone());
    ctx.pop_scope();
    let result_ty = if hint == HirTy::Unknown {
        handler.ty.clone()
    } else {
        hint
    };
    let fit = |ctx: &mut LowerCtx<'_>, e: HirExpr, what: &'static str| {
        if result_ty == HirTy::Unit || hir_expr_diverges(&e) {
            e
        } else {
            coerce(ctx, &result_ty, e, &|| what.to_owned())
        }
    };
    let body_h = fit(ctx, body_h, "the `catch` body");
    let handler = fit(ctx, handler, "the `catch` handler");
    shell(
        ctx,
        &frame,
        body_h,
        result_ty,
        (Vec::new(), Some(handler)),
        span,
    )
}

fn bind_name(ctx: &mut LowerCtx<'_>, name: &str, local: LocalId) {
    if let Some(scope) = ctx.scopes.last_mut() {
        scope.insert(name.to_owned(), local);
    }
}

fn path_expr(name: &str, span: rokc_diagnostic::Span) -> Expr {
    Expr {
        kind: ExprKind::Path(AstPath {
            segments: vec![rokc_ast::PathSegment {
                name: name.to_owned(),
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    }
}

/// `match <err> { <arms that can take ety>, _ => throw <err> }`; the
/// rethrow arm is left out when the arms cover `ety`.
fn dispatch_one(
    ctx: &LowerCtx<'_>,
    arms: &[rokc_ast::CatchArm],
    filters: &[Option<HirTy>],
    ety: &HirTy,
    err_name: &str,
    span: rokc_diagnostic::Span,
) -> Expr {
    let mut m_arms: Vec<AstMatchArm> = arms
        .iter()
        .zip(filters)
        .filter(|(_, f)| may_take(f.as_ref(), ety))
        .map(|(a, _)| AstMatchArm {
            pat: a.pat.clone(),
            guard: None,
            body: Expr {
                kind: ExprKind::Block(a.body.clone()),
                span: a.body.span,
            },
        })
        .collect();
    if !covers(ctx, &m_arms, ety) {
        m_arms.push(AstMatchArm {
            pat: AstPattern {
                kind: AstPatternKind::Wildcard,
                span,
            },
            guard: None,
            body: Expr {
                kind: ExprKind::Block(Block {
                    stmts: vec![Stmt {
                        kind: StmtKind::Throw(path_expr(err_name, span)),
                        span,
                    }],
                    trailing: None,
                    span,
                    label: None,
                }),
                span,
            },
        });
    }
    Expr {
        kind: ExprKind::Match {
            scrutinee: Box::new(path_expr(err_name, span)),
            arms: m_arms,
        },
        span,
    }
}

/// Do `arms` match every value of `ety`? A catch-all / binding, a type
/// pattern of exactly `ety`, type patterns over every variant of a sum,
/// or plain variant patterns over every variant of an enum.
fn covers(ctx: &LowerCtx<'_>, arms: &[AstMatchArm], ety: &HirTy) -> bool {
    let irrefutable = |p: &AstPattern| {
        matches!(
            p.kind,
            AstPatternKind::Wildcard | AstPatternKind::Binding { sub: None, .. }
        )
    };
    let mut tys = Vec::new();
    let mut variants = Vec::new();
    for a in arms {
        match &a.pat.kind {
            _ if irrefutable(&a.pat) => return true,
            AstPatternKind::TypeCheck { ty, .. } => {
                let t = ctx.resolve_ast_ty(ty);
                if t == *ety {
                    return true;
                }
                tys.push(t);
            }
            AstPatternKind::EnumVariant { path, args } if args.iter().all(irrefutable) => {
                let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
                if let EnumRes::Found(_, i) = resolve_enum_variant(ctx, &segs, Some(ety), None) {
                    variants.push(i);
                }
            }
            _ => {}
        }
    }
    match ety {
        HirTy::Sum(vs) => vs.iter().all(|v| tys.contains(v)),
        HirTy::Enum(eid) => (0..ctx.enum_def(*eid).variants.len()).all(|i| variants.contains(&i)),
        _ => false,
    }
}

/// The error type a catch arm's pattern names (`None`: any type).
fn arm_filter(ctx: &LowerCtx<'_>, pat: &AstPattern) -> Option<HirTy> {
    match &pat.kind {
        AstPatternKind::TypeCheck { ty, .. } => Some(ctx.resolve_ast_ty(ty)),
        AstPatternKind::EnumVariant { path, .. } | AstPatternKind::Struct { path, .. } => {
            let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
            if let Some(e) = ctx
                .enum_path(&segs)
                .and_then(|(full, _)| ctx.lookup_enum(&full))
            {
                return Some(HirTy::Enum(e));
            }
            ctx.canon_type(&segs)
                .and_then(|full| ctx.lookup_struct(&full))
                .map(HirTy::Struct)
        }
        _ => None,
    }
}

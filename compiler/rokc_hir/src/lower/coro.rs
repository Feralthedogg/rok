//! Coroutines (spec 4.11 generators, 4.12 async, 4.13 streams).
//!
//! A coroutine block `yield { .. }` / `async { .. }` / `async yield { .. }`
//! is lifted like a closure into a body function marked `is_generator` /
//! `is_async`, whose return type is the *step* value one resume hands
//! back: `T | none` (generator), `Poll<T>` (async), `Poll<T | none>`
//! (stream) — inside the `throws` carrier when the body may throw. `yield`
//! and a pending `await` become `HirExprKind::Suspend` of a step value;
//! MIR (`rokc_mir::coro`) turns the body into a resumable state machine.
//! The block's value is a library wrapper holding the coroutine
//! (`CoroNew`, a function value whose env is the frame):
//!
//! | form            | wrapper (`throws (E)` form)                       |
//! |-----------------|---------------------------------------------------|
//! | `yield`         | `iter::GenIter<T>` (`TryGenIter<T, E>`)           |
//! | `async`         | `future::AsyncFuture<T>` (`TryAsyncFuture<T, E>`) |
//! | `async yield`   | `stream::AsyncStream<T>` (`TryAsyncStream<T, E>`) |
//!
//! `yield fn` / `async fn` are rewritten by the driver into a plain `fn`
//! returning the wrapper whose body is such a block (labelled
//! `FN_BLOCK_LABEL`); `yield ||` / `async ||` are closures returning one.
//!
//! The body function:
//! ```text
//! fn __coro_N(__env?, #ctx?) -> step {
//!     <captures>
//!     let #r = if true { '#coro: { body } } else { undef };
//!     suspend_final <final step: none / Ready(#r) / Ready(none)>;
//! }
//! ```
//! `return v` breaks out of `'#coro`; an escaping error returns the
//! error carrier (MIR then parks the coroutine at its final point). The
//! `if true` keeps the final point reachable when the body diverges.

use rokc_ast::{Block, CallArg, Expr, ExprKind};
use rokc_ir_common::{ConstVal, PrimTy};

use super::desugar::{closure_ctx, may_throw};
use super::expr::{hir_local, method_call_on, pick_method};
use super::throws::{carrier, unit_value};
use super::{LowerCtx, lower_expected, wrap_into_sum};
use crate::{
    HirBlock, HirExpr, HirExprKind, HirFunction, HirMatchArm, HirParam, HirPattern, HirStmt, HirTy,
};

/// Label of the block the driver wraps a `yield fn` / `async fn` body in
/// (its params are then the function's own, assignable).
pub const FN_BLOCK_LABEL: &str = "#coro_fn";
/// The body block of an `async ||` / `yield ||` closure: its `[ref x]`
/// captures (the closure's boxed cells) pass into the coroutine as the
/// same cells, so every call's future shares them (spec 4.6.2).
const CLOSURE_BLOCK_LABEL: &str = "#coro_closure";
const BODY_LABEL: &str = "#coro";
const CTX: &str = "#ctx";
const CONTEXT: &str = "rok::core::future::Context";
const POLL: &str = "rok::core::future::Poll";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CoroKind {
    Gen,
    Async,
    Stream,
}

impl CoroKind {
    const fn wrapper(self, throws: bool) -> &'static str {
        match (self, throws) {
            (Self::Gen, false) => "rok::core::iter::GenIter",
            (Self::Gen, true) => "rok::core::iter::TryGenIter",
            (Self::Async, false) => "rok::core::future::AsyncFuture",
            (Self::Async, true) => "rok::core::future::TryAsyncFuture",
            (Self::Stream, false) => "rok::core::stream::AsyncStream",
            (Self::Stream, true) => "rok::core::stream::TryAsyncStream",
        }
    }
    const fn is_async(self) -> bool {
        !matches!(self, Self::Gen)
    }
    const fn yields(self) -> bool {
        !matches!(self, Self::Async)
    }
}

/// The coroutine a body is being lowered for.
#[derive(Clone, Debug)]
pub(super) struct CoroCtx {
    pub kind: CoroKind,
    /// Item type of a generator / stream (`Unknown` until the first
    /// `yield` fixes it).
    pub item: HirTy,
    /// Probe pass: types are still being inferred, build no step values.
    pub probe: bool,
}

impl CoroCtx {
    /// The step type: what one resume hands back (without the carrier).
    pub fn step_ty(&self, ctx: &LowerCtx<'_>, out: &HirTy) -> HirTy {
        let opt = HirTy::sum([self.item.clone(), super::none_ty()]);
        match self.kind {
            CoroKind::Gen => opt,
            CoroKind::Async => poll_ty(ctx, out.clone()),
            CoroKind::Stream => poll_ty(ctx, opt),
        }
    }
}

fn poll_ty(ctx: &LowerCtx<'_>, t: HirTy) -> HirTy {
    ctx.instantiate_enum(POLL, vec![t])
        .map_or(HirTy::Unknown, HirTy::Enum)
}

/// `Poll::<variant>(args)` for `poll` = `Poll<..>`.
fn poll_variant(ctx: &LowerCtx<'_>, poll: &HirTy, name: &str, args: Vec<HirExpr>) -> HirExpr {
    let span = rokc_diagnostic::Span::DUMMY;
    let HirTy::Enum(id) = poll else {
        return super::poison(span);
    };
    let idx = ctx
        .enum_def(*id)
        .variants
        .iter()
        .position(|v| v.name == name)
        .expect("Poll variant");
    HirExpr {
        kind: HirExprKind::EnumVariantInit {
            enum_id: *id,
            variant_index: u32::try_from(idx).expect("variant index"),
            args,
        },
        ty: poll.clone(),
        span,
    }
}

/// A step value, wrapped into the ok carrier when the body throws.
fn step(ctx: &LowerCtx<'_>, value: HirExpr) -> HirExpr {
    match ctx.fn_throws.clone() {
        Some(err) => carrier(&value.ty.clone(), &err, Ok(value), value_span()),
        None => value,
    }
}

const fn value_span() -> rokc_diagnostic::Span {
    rokc_diagnostic::Span::DUMMY
}

fn suspend(value: HirExpr, is_final: bool, span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr {
        kind: HirExprKind::Suspend {
            value: Box::new(value),
            is_final,
        },
        ty: HirTy::Unit,
        span,
    }
}

/// `return v` inside a coroutine: leave the body with `v`.
pub(super) fn coro_return(value: Option<HirExpr>) -> HirStmt {
    HirStmt::Break {
        label: Some(BODY_LABEL.to_owned()),
        value,
    }
}

/// `yield e;` (spec 4.11.2).
pub(super) fn lower_yield(
    ctx: &mut LowerCtx<'_>,
    value: Option<&Expr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let Some(coro) = ctx.coro.clone().filter(|c| c.kind.yields()) else {
        return ctx.error_expr(
            span,
            "`yield` outside a generator: use it in a `yield fn` / `yield { .. }` / \
             `async yield` body (spec 4.11)"
                .to_owned(),
        );
    };
    let v = match value {
        Some(e) => {
            let v = lower_expected(ctx, e, coro.item.clone());
            if coro.item == HirTy::Unknown {
                v
            } else {
                super::coerce(ctx, &coro.item, v, &|| "the yielded value".to_owned())
            }
        }
        None => unit_value(span),
    };
    if coro.item == HirTy::Unknown && v.ty != HirTy::Unknown {
        if let Some(c) = &mut ctx.coro {
            c.item = v.ty.clone();
        }
    }
    let coro = ctx.coro.clone().expect("in a coroutine");
    if coro.probe {
        return HirExpr {
            kind: HirExprKind::Block(Box::new(HirBlock {
                stmts: vec![HirStmt::Expr(v)],
                trailing: None,
                label: None,
            })),
            ty: HirTy::Unit,
            span,
        };
    }
    let opt = HirTy::sum([coro.item.clone(), super::none_ty()]);
    let some = wrap_into_sum(&opt, v);
    let value = match coro.kind {
        CoroKind::Stream => {
            let poll = poll_ty(ctx, opt);
            poll_variant(ctx, &poll, "Ready", vec![some])
        }
        _ => some,
    };
    suspend(step(ctx, value), false, span)
}

/// `await e` (spec 4.12.2, stdlib 2.20.3): poll `e` (or
/// `e.into_future()`) until it is ready, suspending with `Pending` in
/// between. A throwing `poll` (a `throws` async body) must sit under a
/// `try`, like any throwing call.
pub(super) fn lower_await(
    ctx: &mut LowerCtx<'_>,
    e: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // `let v: T = await e`: `e` is expected to be a future of `T` (an
    // `AsyncFuture<T>` hint, so `await s.collect()` picks `T`), not a `T`.
    let hint = ctx
        .current_expected()
        .filter(|t| !matches!(t, HirTy::Unknown | HirTy::Unit))
        .cloned()
        .and_then(|t| ctx.instantiate_struct(CoroKind::Async.wrapper(false), vec![t]))
        .map_or(HirTy::Unknown, HirTy::Struct);
    let fut = super::lower_expected(ctx, e, hint);
    let has_poll =
        |ctx: &LowerCtx<'_>, t: &HirTy| matches!(pick_method(ctx, t, "poll", None), Ok(Some(_)));
    let fut = if fut.ty == HirTy::Unknown || has_poll(ctx, &fut.ty) {
        fut
    } else {
        method_call_on(ctx, fut, "into_future", &[], span)
    };
    if fut.ty == HirTy::Unknown {
        return fut;
    }
    let fty = fut.ty.clone();
    let f = ctx.declare(None, fty.clone());
    let lp = poll_loop(ctx, f, &fty, "poll", span);
    HirExpr {
        ty: lp.ty.clone(),
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: vec![HirStmt::Let {
                local: f,
                init: fut,
            }],
            trailing: Some(lp),
            label: None,
        })),
        span,
    }
}

/// `loop { match f.<method>(ref #ctx) { Ready(v) => break v, Pending =>
/// suspend Pending } }` over the value `fut` (kept in a local, so a
/// `ref self` poll writes its state back).
pub(super) fn poll_loop(
    ctx: &mut LowerCtx<'_>,
    f: rokc_ir_common::LocalId,
    fty: &HirTy,
    method: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    if !ctx.coro.as_ref().is_some_and(|c| c.kind.is_async()) {
        return ctx.error_expr(
            span,
            "`await` outside an async body: use it in an `async fn` / `async { .. }` / \
             `async ||` body (spec 4.12.10)"
                .to_owned(),
        );
    }
    let ctx_arg = CallArg::Ref(Expr {
        kind: ExprKind::Path(rokc_ast::Path {
            segments: vec![rokc_ast::PathSegment {
                name: CTX.to_owned(),
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    });
    let polled = method_call_on(ctx, hir_local(f, fty, span), method, &[ctx_arg], span);
    let HirTy::Enum(pid) = polled.ty else {
        if polled.ty == HirTy::Unknown {
            return polled;
        }
        return ctx.error_expr(
            span,
            format!(
                "`{method}` must return `Poll<T>`, found `{}`",
                ctx.ty_name(&polled.ty)
            ),
        );
    };
    let def = ctx.enum_def(pid);
    let (Some(ready), Some(pending), Some(out)) = (
        def.variants.iter().position(|v| v.name == "Ready"),
        def.variants.iter().position(|v| v.name == "Pending"),
        def.generic_args.first().cloned(),
    ) else {
        return ctx.error_expr(span, "`await` needs a `Poll<T>`".to_owned());
    };
    let v = ctx.declare(None, out.clone());
    let coro = ctx.coro.clone().expect("in a coroutine");
    let pending_step = if coro.probe {
        unit_value(span)
    } else {
        let out_ty = ctx.fn_ret_ty.clone();
        let poll = coro.step_ty(ctx, &out_ty);
        step(ctx, poll_variant(ctx, &poll, "Pending", Vec::new()))
    };
    let block = |stmts: Vec<HirStmt>| HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing: None,
            label: None,
        })),
        ty: HirTy::Unit,
        span,
    };
    let arms = vec![
        HirMatchArm {
            pat: HirPattern::EnumVariant {
                enum_id: pid,
                variant_index: u32::try_from(ready).expect("variant"),
                args: vec![HirPattern::Binding {
                    local: v,
                    ty: out.clone(),
                }],
            },
            guard: None,
            body: block(
                cancel_check(ctx, "unwinding", span)
                    .into_iter()
                    .chain([HirStmt::Break {
                        label: None,
                        value: Some(hir_local(v, &out, span)),
                    }])
                    .collect(),
            ),
        },
        HirMatchArm {
            pat: HirPattern::EnumVariant {
                enum_id: pid,
                variant_index: u32::try_from(pending).expect("variant"),
                args: Vec::new(),
            },
            guard: None,
            body: block(
                cancel_check(ctx, "cancel_requested", span)
                    .into_iter()
                    .chain([HirStmt::Expr(if coro.probe {
                        pending_step
                    } else {
                        suspend(pending_step, false, span)
                    })])
                    .collect(),
            ),
        },
    ];
    let m = HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(polled),
            arms,
        },
        ty: HirTy::Unit,
        span,
    };
    let lp = HirExpr {
        kind: HirExprKind::Loop {
            label: None,
            body: Box::new(HirBlock {
                stmts: vec![HirStmt::Expr(m)],
                trailing: None,
                label: None,
            }),
            result_ty: out.clone(),
        },
        ty: out.clone(),
        span,
    };
    // Checks: on entry, after a ready poll (an awaited coroutine may
    // have left because of the cancel: `unwinding`, not the bare flag —
    // a hand-written future's value, like a received message or a lock
    // guard, is kept and the next check leaves) and before suspending
    // (after a resume the awaited future is polled first, so a nested
    // coroutine leaves through its own cleanups before this one).
    let Some(entry) = cancel_check(ctx, "cancel_requested", span) else {
        return lp;
    };
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: vec![entry],
            trailing: Some(lp),
            label: None,
        })),
        ty: out,
        span,
    }
}

/// A cancellation point (stdlib 2.18.4, refs-lang 7.7.10): `if
/// task::<check>(#ctx) { <leave the body like a return> }`, `check`
/// being `cancel_requested` or (after a ready poll) `unwinding`.
/// The exit runs the `finally` / `using` cleanups it passes; the
/// coroutine's result is a zero value the executor drops. `None` in the
/// probe pass.
fn cancel_check(
    ctx: &mut LowerCtx<'_>,
    check: &str,
    span: rokc_diagnostic::Span,
) -> Option<HirStmt> {
    if ctx.coro.as_ref().is_none_or(|c| c.probe) {
        return None;
    }
    let path = |names: &[&str]| Expr {
        kind: ExprKind::Path(rokc_ast::Path {
            segments: names
                .iter()
                .map(|n| rokc_ast::PathSegment {
                    name: (*n).to_owned(),
                    generics: Vec::new(),
                })
                .collect(),
            span,
        }),
        span,
    };
    let call = Expr {
        kind: ExprKind::Call {
            callee: Box::new(path(&["rok", "core", "task", check])),
            args: vec![CallArg::Positional(path(&[CTX]))],
            trailing_closure: None,
        },
        span,
    };
    let cond = super::expr::lower_expr(ctx, &call);
    if cond.ty != HirTy::Prim(PrimTy::Bool) {
        return None;
    }
    let out = ctx.fn_ret_ty.clone();
    let value = (out != HirTy::Unit).then_some(HirExpr {
        kind: HirExprKind::Const(ConstVal::Unit),
        ty: out,
        span,
    });
    let exit = super::throws::exit_through(ctx, None, value, coro_return, span);
    Some(HirStmt::Expr(HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(cond),
            then_block: Box::new(HirBlock {
                stmts: vec![exit],
                trailing: None,
                label: None,
            }),
            else_branch: None,
        },
        ty: HirTy::Unit,
        span,
    }))
}

/// `async || body` = `|| async { body }` (spec 4.11.5 / 4.12.5): the
/// closure body to lift (the body itself for a plain closure).
pub(super) fn closure_body(body: &Expr, is_async: bool, is_generator: bool) -> Expr {
    if !(is_async || is_generator) {
        return body.clone();
    }
    let block = match &body.kind {
        ExprKind::Block(b) => b.clone(),
        _ => Block {
            stmts: Vec::new(),
            trailing: Some(Box::new(body.clone())),
            span: body.span,
            label: None,
        },
    };
    // A labelled body (`'a: { .. }`) keeps its label on an inner block.
    let block = if block.label.is_some() {
        Block {
            stmts: Vec::new(),
            trailing: Some(Box::new(Expr {
                kind: ExprKind::Block(block),
                span: body.span,
            })),
            span: body.span,
            label: Some(CLOSURE_BLOCK_LABEL.to_owned()),
        }
    } else {
        Block {
            label: Some(CLOSURE_BLOCK_LABEL.to_owned()),
            ..block
        }
    };
    let kind = match (is_async, is_generator) {
        (true, true) => ExprKind::AsyncYieldBlock(block),
        (true, false) => ExprKind::AsyncBlock(block),
        _ => ExprKind::YieldBlock(block),
    };
    Expr {
        kind,
        span: body.span,
    }
}

/// A coroutine block expression.
pub(super) fn lower_coro_expr(
    ctx: &LowerCtx<'_>,
    kind: &ExprKind,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    match kind {
        ExprKind::AsyncBlock(b) => lower_coro_block(ctx, CoroKind::Async, b, span),
        ExprKind::YieldBlock(b) => lower_coro_block(ctx, CoroKind::Gen, b, span),
        ExprKind::AsyncYieldBlock(b) => lower_coro_block(ctx, CoroKind::Stream, b, span),
        _ => unreachable!("not a coroutine block"),
    }
}

/// `yield { .. }` / `async { .. }` / `async yield { .. }`.
fn lower_coro_block<'a>(
    ctx: &LowerCtx<'a>,
    kind: CoroKind,
    body: &Block,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let from_fn = body.label.as_deref() == Some(FN_BLOCK_LABEL);
    let from_closure = body.label.as_deref() == Some(CLOSURE_BLOCK_LABEL);
    let body_expr = Expr {
        kind: ExprKind::Block(Block {
            label: None,
            ..body.clone()
        }),
        span: body.span,
    };
    // Item / output and error types: from the expected wrapper type
    // (a `yield fn` / `async fn` signature, an annotated `let`), else
    // inferred.
    let (mut val_ty, mut throws) = (HirTy::Unknown, None);
    // The probe's errors, re-reported when it cannot infer a type (else
    // the body's real error would vanish behind a poisoned value).
    let mut probe_diags = Vec::new();
    if let Some(HirTy::Struct(sid)) = ctx.current_expected().cloned() {
        let def = ctx.struct_def(sid);
        for t in [false, true] {
            let base = kind.wrapper(t);
            if def.name == super::mangle_inst(base, &def.generic_args) {
                val_ty = def.generic_args.first().cloned().unwrap_or(HirTy::Unknown);
                throws = def.generic_args.get(1).cloned();
            }
        }
    }
    let captures: Vec<(String, rokc_ir_common::LocalId, HirTy, bool)> =
        crate::walk::free_names(&[], &body_expr)
            .into_iter()
            .filter_map(|name| {
                let local = ctx.lookup(&name)?;
                if from_closure && ctx.boxed.contains(&local) {
                    return Some((name, local, ctx.local_ty(local), true));
                }
                let ty = ctx.var_ty(local);
                Some((name, local, ty, false))
            })
            .collect();

    let make_ctx = |ctx: &LowerCtx<'a>,
                    val: &HirTy,
                    throws: &Option<HirTy>,
                    probe: bool|
     -> (LowerCtx<'a>, Vec<HirParam>, Vec<HirStmt>) {
        let (mut c, mut params, prelude, _) = closure_ctx(ctx, &[], &captures, None, span);
        if from_fn {
            c.value_captured.clear();
            // 4.16.5: an async implicit `main`'s body keeps its rules.
            c.implicit_main = ctx.implicit_main;
        }
        if kind.is_async() {
            let cty = ctx
                .lookup_struct(CONTEXT)
                .map_or(HirTy::Unknown, HirTy::Struct);
            let l = c.declare(Some(CTX.to_owned()), cty.clone());
            params.push(HirParam {
                name: CTX.to_owned(),
                local: l,
                ty: cty,
                by_ref: false,
            });
        }
        let (item, out) = if kind.yields() {
            (val.clone(), HirTy::Unit)
        } else {
            (HirTy::Unit, val.clone())
        };
        c.coro = Some(CoroCtx { kind, item, probe });
        c.infer_ret = out == HirTy::Unknown;
        c.fn_ret_ty = out;
        c.fn_throws.clone_from(throws);
        (c, params, prelude)
    };

    // Probe pass: infer what the body yields / returns and throws.
    let needs_throws = throws.is_none() && may_throw(&body_expr);
    if val_ty == HirTy::Unknown || needs_throws {
        let seen = ctx.env.sink.diagnostics.borrow().len();
        let extras = ctx.env.sink.extras.borrow().len();
        let (mut probe, ..) = make_ctx(ctx, &val_ty, &throws, true);
        if needs_throws {
            probe.throws_probe = Some(Vec::new());
        }
        let hint = probe.fn_ret_ty.clone();
        let value = lower_expected(&mut probe, &body_expr, hint);
        probe_diags = ctx.env.sink.diagnostics.borrow_mut().split_off(seen);
        let mut lifted = ctx.env.sink.extras.borrow_mut();
        if lifted[extras..].iter().all(|f| {
            ["__closure_", "__thunk_", "__coro_"]
                .iter()
                .any(|p| f.name.starts_with(p))
        }) {
            let gone: Vec<_> = lifted[extras..].iter().map(|f| f.id).collect();
            ctx.env
                .sink
                .thunks
                .borrow_mut()
                .retain(|_, id| !gone.contains(id));
            lifted.truncate(extras);
        }
        drop(lifted);
        if val_ty == HirTy::Unknown {
            val_ty = if kind.yields() {
                probe
                    .coro
                    .as_ref()
                    .map_or(HirTy::Unknown, |c| c.item.clone())
            } else {
                match probe.fn_ret_ty {
                    HirTy::Unknown => value.ty,
                    t => t,
                }
            };
            if val_ty == HirTy::Never {
                val_ty = HirTy::Unit;
            }
            if val_ty == HirTy::Unknown && kind.yields() {
                val_ty = HirTy::Unit;
            }
        }
        if needs_throws {
            let errs = probe.throws_probe.take().unwrap_or_default();
            throws = match crate::ty::throws_ty(HirTy::Unit, HirTy::Sum(errs)) {
                HirTy::Throws { err, .. } => Some(*err),
                _ => None,
            };
        }
    }
    if val_ty == HirTy::Unknown {
        ctx.env.sink.diagnostics.borrow_mut().extend(probe_diags);
        return super::poison(span);
    }

    let body_id = rokc_ir_common::FunctionId(ctx.env.sink.next_id.get());
    ctx.env.sink.next_id.set(body_id.0 + 1);
    let (mut c, params, prelude) = make_ctx(ctx, &val_ty, &throws, false);
    let out = c.fn_ret_ty.clone();
    let body_h = lower_expected(&mut c, &body_expr, out.clone());
    let body_h = if super::hir_expr_diverges(&body_h) || out == HirTy::Unit {
        body_h
    } else {
        super::coerce(&mut c, &out, body_h, &|| "the async body".to_owned())
    };
    let coro = c.coro.clone().expect("coroutine ctx");
    let step_ty = coro.step_ty(&c, &out);
    let r = c.declare(None, out.clone());
    let labelled = HirExpr {
        ty: out.clone(),
        span,
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: Vec::new(),
            trailing: Some(body_h),
            label: Some(BODY_LABEL.to_owned()),
        })),
    };
    let run = HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(HirExpr {
                kind: HirExprKind::Const(ConstVal::Bool(true)),
                ty: HirTy::Prim(PrimTy::Bool),
                span,
            }),
            then_block: Box::new(HirBlock {
                stmts: Vec::new(),
                trailing: Some(labelled),
                label: None,
            }),
            else_branch: Some(Box::new(HirExpr {
                kind: HirExprKind::Const(ConstVal::Unit),
                ty: out.clone(),
                span,
            })),
        },
        ty: out.clone(),
        span,
    };
    let opt = HirTy::sum([coro.item, super::none_ty()]);
    let none = || super::desugar::sum_none(&opt, span);
    let final_value = match kind {
        CoroKind::Gen => none(),
        CoroKind::Async => poll_variant(&c, &step_ty, "Ready", vec![hir_local(r, &out, span)]),
        CoroKind::Stream => poll_variant(&c, &step_ty, "Ready", vec![none()]),
    };
    let final_value = step(&c, final_value);
    let ret_ty = final_value.ty.clone();
    let mut stmts = prelude;
    stmts.push(if out == HirTy::Unit {
        HirStmt::Expr(run)
    } else {
        HirStmt::Let {
            local: r,
            init: run,
        }
    });
    stmts.push(HirStmt::Expr(suspend(final_value, true, span)));
    let resume_tys: Vec<HirTy> = params
        .iter()
        .filter(|p| p.name == CTX)
        .map(|p| p.ty.clone())
        .collect();
    ctx.env.sink.extras.borrow_mut().push(HirFunction {
        id: body_id,
        def_id: None,
        name: format!("__coro_{}", body_id.0),
        params,
        locals: c.into_locals(),
        ret_ty: ret_ty.clone(),
        body: Some(HirBlock {
            stmts,
            trailing: None,
            label: None,
        }),
        is_async: kind.is_async(),
        is_generator: kind.yields(),
        span,
        facts: rokc_ir_common::FnFacts::default(),
    });

    let env = (!captures.is_empty()).then(|| {
        let fields: Vec<HirExpr> = captures
            .iter()
            .map(|(_, l, ty, by_ref)| {
                if *by_ref {
                    hir_local(*l, ty, span)
                } else {
                    ctx.read_local(*l, span)
                }
            })
            .collect();
        HirExpr {
            ty: HirTy::Tuple(captures.iter().map(|(_, _, t, _)| t.clone()).collect()),
            kind: HirExprKind::Tuple { fields },
            span,
        }
    });
    let mut args = vec![val_ty];
    args.extend(throws.clone());
    let Some(sid) = ctx.instantiate_struct(kind.wrapper(throws.is_some()), args) else {
        return ctx.error_expr(
            span,
            format!(
                "`{}` is missing from the core library",
                kind.wrapper(throws.is_some())
            ),
        );
    };
    let field_ty = ctx
        .struct_def(sid)
        .fields
        .first()
        .map_or(HirTy::Unknown, |f| f.ty.clone());
    let coro_fn = HirExpr {
        kind: HirExprKind::CoroNew {
            body_fn: body_id,
            args: env.into_iter().collect(),
        },
        ty: match &field_ty {
            HirTy::Fn(_, _, bounds) => HirTy::Fn(resume_tys, Box::new(ret_ty), bounds.clone()),
            _ => field_ty,
        },
        span,
    };
    HirExpr {
        kind: HirExprKind::StructInit {
            struct_id: sid,
            fields: vec![coro_fn],
        },
        ty: HirTy::Struct(sid),
        span,
    }
}

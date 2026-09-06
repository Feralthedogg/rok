//! Desugarings: closures, `?` / `??` / `?.`, and `for` loops.

#[allow(clippy::wildcard_imports)]
use super::*;

/// Lift a closure into an anonymous top-level function and return a
/// closure value. Captures named outer locals by value (snapshot at
/// creation time). Non-capturing closures stay as plain function
/// pointers so existing `fn(...)` types keep working.
pub(super) fn lower_closure_expr(
    ctx: &LowerCtx<'_>,
    params: &[Param],
    ret_ty: Option<&Ty>,
    body: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // Names referenced but not bound inside the closure (exhaustive AST
    // walk), filtered to those that resolve to outer locals.
    let captures: Vec<(String, LocalId, HirTy)> = crate::walk::free_names(params, body)
        .into_iter()
        .filter_map(|name| {
            let local = ctx.lookup(&name)?;
            Some((name, local, ctx.local_ty(local)))
        })
        .collect();

    let closure_id = FunctionId(ctx.env.sink.next_id.get());
    ctx.env.sink.next_id.set(closure_id.0 + 1);

    // Spec 4.5/4.8: in a context expecting a function type (e.g. an
    // argument to a `fn(i32) -> i32` parameter), unannotated params and
    // the return type come from the expected signature.
    let (expected_param_tys, mut expected_ret): (Option<Vec<HirTy>>, Option<HirTy>) =
        match ctx.current_expected() {
            Some(HirTy::Fn(args, ret) | HirTy::Closure { args, ret, .. }) => {
                (Some(args.clone()), Some((**ret).clone()))
            }
            _ => (None, None),
        };
    // An expected `fn(..) throws (E) -> T`: the body's value is a `T`; an
    // unknown `E` (a `rethrows` parameter) is inferred like no `E`.
    let mut expected_err = None;
    if let Some(HirTy::Throws { ok, err }) = expected_ret.clone() {
        expected_ret = Some(*ok);
        expected_err = Some(*err).filter(|e| *e != HirTy::Unknown);
    }
    let declared_ret = ret_ty.map(|t| ctx.resolve_ast_ty(t));
    // `return` inside the closure targets the closure: its declared (or
    // expected) return type, else the first `return` value's type.
    let mut fixed_ret = declared_ret.or_else(|| expected_ret.filter(|t| *t != HirTy::Unknown));

    // A closure that may throw needs its error type and its value type
    // before the body is lowered (both shape its error returns): take the
    // expected ones, else lower the body once as a probe — errors that
    // escape it, and the type it returns.
    let mut throws = expected_err;
    if (throws.is_some() || may_throw(body)) && (throws.is_none() || fixed_ret.is_none()) {
        let seen = ctx.env.sink.diagnostics.borrow().len();
        let (mut probe, ..) =
            closure_ctx(ctx, params, &captures, expected_param_tys.as_ref(), span);
        probe.fn_ret_ty = fixed_ret.clone().unwrap_or(HirTy::Unknown);
        probe.infer_ret = fixed_ret.is_none();
        probe.throws_probe = Some(Vec::new());
        let hint = probe.fn_ret_ty.clone();
        let value = lower_expected(&mut probe, body, hint);
        ctx.env.sink.diagnostics.borrow_mut().truncate(seen);
        let errs = probe.throws_probe.take().unwrap_or_default();
        if throws.is_none() {
            throws = match crate::ty::throws_ty(HirTy::Unit, HirTy::Sum(errs)) {
                HirTy::Throws { err, .. } => Some(*err),
                _ => None,
            };
        }
        if throws.is_some() && fixed_ret.is_none() {
            fixed_ret = Some(match probe.fn_ret_ty {
                HirTy::Unknown => value.ty,
                t => t,
            });
        }
    }

    let (mut cl_ctx, hir_params, prelude, user_arg_tys) =
        closure_ctx(ctx, params, &captures, expected_param_tys.as_ref(), span);
    cl_ctx.fn_ret_ty = fixed_ret.clone().unwrap_or(HirTy::Unknown);
    cl_ctx.infer_ret = fixed_ret.is_none();
    cl_ctx.fn_throws.clone_from(&throws);
    let ret_hint = cl_ctx.fn_ret_ty.clone();
    let body_h = lower_expected(&mut cl_ctx, body, ret_hint);
    let diverges = hir_expr_diverges(&body_h);
    let final_ret_ty = match (fixed_ret, cl_ctx.fn_ret_ty.clone()) {
        // A `return` fixed the type; a value-producing body must agree.
        (None, HirTy::Unknown) => body_h.ty.clone(),
        (Some(t), _) | (None, t) => t,
    };
    let body_h = if diverges || (body_h.ty == HirTy::Unit && final_ret_ty == HirTy::Unit) {
        body_h
    } else {
        coerce(&cl_ctx, &final_ret_ty, body_h, &|| {
            "the closure body".to_owned()
        })
    };

    let mut body_block = HirBlock {
        stmts: prelude,
        trailing: Some(body_h),
        label: None,
    };
    cl_ctx.fn_ret_ty = final_ret_ty.clone();
    finish_throwing_body(&cl_ctx, &mut body_block);
    let final_ret_ty = match throws {
        Some(err) => HirTy::Throws {
            ok: Box::new(final_ret_ty),
            err: Box::new(err),
        },
        None => final_ret_ty,
    };
    let cl_fn = HirFunction {
        id: closure_id,
        def_id: None,
        name: format!("__closure_{}", closure_id.0),
        params: hir_params,
        locals: cl_ctx.into_locals(),
        ret_ty: final_ret_ty.clone(),
        body: Some(body_block),
        is_async: false,
        is_generator: false,
        span,
    };
    ctx.env.sink.extras.borrow_mut().push(cl_fn);

    let env_ty = (!captures.is_empty())
        .then(|| HirTy::Tuple(captures.iter().map(|(_, _, t)| t.clone()).collect()));
    let Some(env_ty_v) = env_ty else {
        return HirExpr {
            kind: HirExprKind::FnRef(closure_id),
            ty: HirTy::Fn(user_arg_tys, Box::new(final_ret_ty)),
            span,
        };
    };
    // Materialize the env value at the creation site: a tuple of the
    // current outer locals' values, snapshotted by-value.
    let env_value = HirExpr {
        kind: HirExprKind::Tuple {
            fields: captures
                .iter()
                .map(|(_, outer_local, ty)| HirExpr {
                    kind: HirExprKind::Local(*outer_local),
                    ty: ty.clone(),
                    span,
                })
                .collect(),
        },
        ty: env_ty_v.clone(),
        span,
    };
    HirExpr {
        kind: HirExprKind::ClosureValue {
            fn_id: closure_id,
            env: Box::new(env_value),
            arg_tys: user_arg_tys.clone(),
            ret_ty: final_ret_ty.clone(),
            env_ty: env_ty_v.clone(),
        },
        ty: HirTy::Closure {
            args: user_arg_tys,
            ret: Box::new(final_ret_ty),
            env: Box::new(env_ty_v),
        },
        span,
    }
}

/// Does a closure body contain a `throw` or a plain `try` (so its error
/// type must be inferred)? Nested closures count too — a harmless
/// over-approximation that only costs a probe.
fn may_throw(body: &Expr) -> bool {
    struct V(bool);
    impl crate::walk::AstVisitor for V {
        fn expr(&mut self, e: &Expr) {
            if let ExprKind::Try {
                kind: rokc_ast::TryKind::Plain,
                ..
            } = e.kind
            {
                self.0 = true;
            }
        }
        fn stmt(&mut self, s: &Stmt) {
            if matches!(s.kind, StmtKind::Throw(_)) {
                self.0 = true;
            }
        }
    }
    let mut v = V(false);
    crate::walk::walk_expr(&mut v, body);
    v.0
}

/// A fresh lowering context for a closure body: the `env` parameter
/// (a tuple of the captured values) with one local per capture, then
/// the closure's own parameters. Returns the context, the parameters,
/// the capture prelude and the user-visible argument types.
fn closure_ctx<'a>(
    ctx: &LowerCtx<'a>,
    params: &[Param],
    captures: &[(String, LocalId, HirTy)],
    expected_param_tys: Option<&Vec<HirTy>>,
    span: rokc_diagnostic::Span,
) -> (LowerCtx<'a>, Vec<HirParam>, Vec<HirStmt>, Vec<HirTy>) {
    let mut cl_ctx = LowerCtx::new(ctx.env, ctx.ty_subst, ctx.self_ty.clone());
    cl_ctx.current_module.clone_from(&ctx.current_module);
    cl_ctx.local_uses.clone_from(&ctx.local_uses);

    // Closures with captures take an extra `env` parameter (a tuple of
    // captured values). The env param is declared first so its LocalId
    // is stable; closure params follow.
    let env_ty = (!captures.is_empty())
        .then(|| HirTy::Tuple(captures.iter().map(|(_, _, t)| t.clone()).collect()));
    let mut hir_params: Vec<HirParam> = Vec::with_capacity(params.len() + 1);
    let mut prelude: Vec<HirStmt> = Vec::new();
    if let Some(et) = &env_ty {
        let env_local = cl_ctx.declare(Some("__env".to_owned()), et.clone());
        hir_params.push(HirParam {
            name: "__env".to_owned(),
            local: env_local,
            ty: et.clone(),
            by_ref: false,
        });
        // Each captured name becomes a local inside the body initialised
        // from the corresponding env tuple field.
        for (i, (cap_name, _, cap_ty)) in captures.iter().enumerate() {
            let inner_local = cl_ctx.declare(Some(cap_name.clone()), cap_ty.clone());
            prelude.push(HirStmt::Let {
                local: inner_local,
                init: HirExpr {
                    kind: HirExprKind::TupleField {
                        target: Box::new(HirExpr {
                            kind: HirExprKind::Local(env_local),
                            ty: et.clone(),
                            span,
                        }),
                        index: u32::try_from(i).expect("capture index overflow"),
                        field_ty: cap_ty.clone(),
                    },
                    ty: cap_ty.clone(),
                    span,
                },
            });
        }
    }

    let mut user_arg_tys: Vec<HirTy> = Vec::with_capacity(params.len());
    for (pi, p) in params.iter().enumerate() {
        let ty = match &p.ty {
            Some(t) => ctx.resolve_ast_ty(t),
            None => match expected_param_tys.as_ref().and_then(|v| v.get(pi)) {
                Some(t) if *t != HirTy::Unknown => t.clone(),
                _ => {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "cannot infer the type of closure parameter `{}` — annotate \
                             it (`|{}: i32| ...`)",
                            p.name, p.name
                        ),
                    );
                    HirTy::Unknown
                }
            },
        };
        let local = cl_ctx.declare(Some(p.name.clone()), ty.clone());
        hir_params.push(HirParam {
            name: p.name.clone(),
            local,
            ty: ty.clone(),
            by_ref: p.by_ref,
        });
        user_arg_tys.push(ty);
    }
    (cl_ctx, hir_params, prelude, user_arg_tys)
}

/// `T | none`-shaped sum: index of `none` plus the non-none variants.
pub(super) fn optional_parts(ty: &HirTy) -> Option<(usize, Vec<(usize, HirTy)>)> {
    let HirTy::Sum(variants) = ty else {
        return None;
    };
    let none_idx = variants.iter().position(is_none_ty)?;
    let some: Vec<(usize, HirTy)> = variants
        .iter()
        .enumerate()
        .filter(|(_, v)| !is_none_ty(v))
        .map(|(i, v)| (i, v.clone()))
        .collect();
    Some((none_idx, some))
}

/// The value type left after removing `none`: the single payload, or a
/// sum of the remaining variants.
pub(super) fn without_none(some: &[(usize, HirTy)]) -> HirTy {
    match some {
        [(_, t)] => t.clone(),
        many => HirTy::Sum(many.iter().map(|(_, t)| t.clone()).collect()),
    }
}

/// `match scrut { v: T_k => wrap(v), ..., none => none_body }` with one
/// arm per non-none variant; each payload is re-wrapped into `result_ty`.
#[allow(clippy::too_many_arguments)] // match pieces are independent inputs; a bundle struct only adds noise
pub(super) fn optional_match(
    ctx: &mut LowerCtx<'_>,
    scrut: HirExpr,
    none_idx: usize,
    some: &[(usize, HirTy)],
    some_body: &mut dyn FnMut(&mut LowerCtx<'_>, HirExpr) -> HirExpr,
    none_body: HirExpr,
    result_ty: HirTy,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let sum_ty = scrut.ty.clone();
    let mut arms = Vec::with_capacity(some.len() + 1);
    for (idx, payload_ty) in some {
        let bind_local = ctx.declare(None, payload_ty.clone());
        let value = HirExpr {
            kind: HirExprKind::Local(bind_local),
            ty: payload_ty.clone(),
            span,
        };
        arms.push(HirMatchArm {
            pat: HirPattern::SumVariant {
                sum_ty: sum_ty.clone(),
                variant_index: u32::try_from(*idx).expect("variant overflow"),
                binder: Some(bind_local),
                payload_ty: Some(payload_ty.clone()),
            },
            guard: None,
            body: some_body(ctx, value),
        });
    }
    arms.push(HirMatchArm {
        pat: HirPattern::SumVariant {
            sum_ty,
            variant_index: u32::try_from(none_idx).expect("variant overflow"),
            binder: None,
            payload_ty: None,
        },
        guard: None,
        body: none_body,
    });
    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(scrut),
            arms,
        },
        ty: result_ty,
        span,
    }
}

pub(super) fn sum_none(sum_ty: &HirTy, span: rokc_diagnostic::Span) -> HirExpr {
    wrap_into_sum(
        sum_ty,
        HirExpr {
            kind: HirExprKind::Const(ConstVal::None),
            ty: none_ty(),
            span,
        },
    )
}

/// Desugar `x?.tail` to `match x { v: T => v.tail, none => none }`. The
/// scrutinee must be `T | none` with one payload variant; the result is
/// `tail_ty | none` (or the tail's own optional type — spec 3.8.2: `?.`
/// chains compose monadically).
pub(super) fn desugar_question_dot(
    ctx: &mut LowerCtx<'_>,
    recv: HirExpr,
    tail: &rokc_ast::AccessTail,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    if recv.ty == HirTy::Unknown {
        return recv;
    }
    let Some((none_idx, some)) = optional_parts(&recv.ty) else {
        // Non-optional receiver — a plain access.
        return apply_access_tail(ctx, recv, tail, span);
    };
    if some.len() != 1 {
        return ctx.error_expr(
            span,
            format!(
                "`?.` needs a `T | none` receiver with a single payload type, found `{}`",
                ctx.ty_name(&recv.ty)
            ),
        );
    }
    // Lower the tail once against a placeholder local to learn its type.
    let payload_ty = some[0].1.clone();
    let bind_local = ctx.declare(None, payload_ty.clone());
    let unwrapped = HirExpr {
        kind: HirExprKind::Local(bind_local),
        ty: payload_ty.clone(),
        span,
    };
    let inner = apply_access_tail(ctx, unwrapped, tail, span);
    if inner.ty == HirTy::Unknown {
        return inner;
    }
    let inner_optional = optional_parts(&inner.ty).is_some();
    let result_ty = if inner_optional {
        inner.ty.clone()
    } else {
        HirTy::Sum(vec![inner.ty.clone(), none_ty()])
    };
    let some_body = if inner_optional {
        inner
    } else {
        wrap_into_sum(&result_ty, inner)
    };
    let none_body = sum_none(&result_ty, span);
    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(recv.clone()),
            arms: vec![
                HirMatchArm {
                    pat: HirPattern::SumVariant {
                        sum_ty: recv.ty.clone(),
                        variant_index: u32::try_from(some[0].0).expect("variant overflow"),
                        binder: Some(bind_local),
                        payload_ty: Some(payload_ty),
                    },
                    guard: None,
                    body: some_body,
                },
                HirMatchArm {
                    pat: HirPattern::SumVariant {
                        sum_ty: recv.ty,
                        variant_index: u32::try_from(none_idx).expect("variant overflow"),
                        binder: None,
                        payload_ty: None,
                    },
                    guard: None,
                    body: none_body,
                },
            ],
        },
        ty: result_ty,
        span,
    }
}

/// Apply an `AccessTail` to an already-lowered HIR receiver. Supports
/// the same forms `?.` does: field, tuple field, and method call.
pub(super) fn apply_access_tail(
    ctx: &mut LowerCtx<'_>,
    recv: HirExpr,
    tail: &rokc_ast::AccessTail,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    match tail {
        rokc_ast::AccessTail::Field(name) => field_access(ctx, recv, name, span),
        rokc_ast::AccessTail::TupleField(idx) => match recv.ty.clone() {
            HirTy::Tuple(parts) => match parts.get(*idx as usize) {
                Some(field_ty) => HirExpr {
                    kind: HirExprKind::TupleField {
                        target: Box::new(recv),
                        index: *idx,
                        field_ty: field_ty.clone(),
                    },
                    ty: field_ty.clone(),
                    span,
                },
                None => ctx.error_expr(
                    span,
                    format!("tuple index {idx} out of range for a {}-tuple", parts.len()),
                ),
            },
            other => ctx.error_expr(
                span,
                format!("no field `{idx}` on type `{}`", ctx.ty_name(&other)),
            ),
        },
        rokc_ast::AccessTail::Method { method, args, .. } => {
            let call = method_call_on(ctx, recv, method, args, span);
            unpack_call(ctx, call)
        }
        rokc_ast::AccessTail::Index(_) => ctx.error_expr(
            span,
            "`?.[index]` is not supported yet (stage-1 limitation)".to_owned(),
        ),
    }
}

/// Desugar `expr?` (spec 3.14): unwrap the payload of a `T | none` value
/// or propagate `none` out of the enclosing function, which must itself
/// return a sum containing `none`. With several payload variants the
/// value keeps the remaining sum (`A | B | none` → `A | B`).
pub(super) fn desugar_try_q(
    ctx: &mut LowerCtx<'_>,
    inner: HirExpr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    if inner.ty == HirTy::Unknown {
        return inner;
    }
    let Some((none_idx, some)) = optional_parts(&inner.ty) else {
        return ctx.error_expr(
            span,
            format!(
                "`?` only works on `T | none`, found `{}` — to propagate errors use `throws` \
                 and `try` (spec 3.14 / 4.14)",
                ctx.ty_name(&inner.ty)
            ),
        );
    };
    let ret_ty = ctx.fn_ret_ty.clone();
    if optional_parts(&ret_ty).is_none() {
        return ctx.error_expr(
            span,
            format!(
                "`?` propagates `none`, but the enclosing function returns `{}` — its \
                 return type must include `none`",
                ctx.ty_name(&ret_ty)
            ),
        );
    }
    let value_ty = without_none(&some);
    let ret = lower_return(ctx, Some(sum_none(&ret_ty, span)), span);
    let none_body = HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: vec![ret],
            trailing: None,
            label: None,
        })),
        ty: value_ty.clone(),
        span,
    };
    let vt = value_ty.clone();
    optional_match(
        ctx,
        inner,
        none_idx,
        &some,
        &mut |_, v| wrap_into_sum(&vt, v),
        none_body,
        value_ty,
        span,
    )
}

/// Desugar `lhs ?? rhs` to `match lhs { v: T => v, none => rhs }`; the
/// default must have the payload type.
pub(super) fn desugar_nullish_coalesce(
    ctx: &mut LowerCtx<'_>,
    lhs: HirExpr,
    rhs: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let Some((none_idx, some)) = optional_parts(&lhs.ty) else {
        let rhs_h = lower_expected(ctx, rhs, HirTy::Unknown);
        if lhs.ty == HirTy::Unknown || rhs_h.ty == HirTy::Unknown {
            return poison(span);
        }
        return ctx.error_expr(
            span,
            format!(
                "`??` needs an optional left operand (`T | none`), found `{}`",
                ctx.ty_name(&lhs.ty)
            ),
        );
    };
    let value_ty = without_none(&some);
    let rhs_h = lower_expected(ctx, rhs, value_ty.clone());
    let rhs_h = coerce(ctx, &value_ty, rhs_h, &|| "the `??` default".to_owned());
    let vt = value_ty.clone();
    optional_match(
        ctx,
        lhs,
        none_idx,
        &some,
        &mut |_, v| wrap_into_sum(&vt, v),
        rhs_h,
        value_ty,
        span,
    )
}

/// Bind an irrefutable `for` / destructuring pattern to `value`:
/// a name, `_`, or (nested) tuples of those.
pub(super) fn bind_irrefutable(
    ctx: &mut LowerCtx<'_>,
    pat: &AstPattern,
    value: HirExpr,
    stmts: &mut Vec<HirStmt>,
) {
    let span = value.span;
    match (&pat.kind, value.ty.clone()) {
        (AstPatternKind::Binding { name, sub: None }, ty) => {
            if name == "_" {
                return;
            }
            let local = ctx.declare(Some(name.clone()), ty);
            stmts.push(HirStmt::Let { local, init: value });
        }
        (AstPatternKind::Tuple(pats), HirTy::Tuple(tys)) if pats.len() == tys.len() => {
            let tmp = ctx.declare(None, value.ty.clone());
            let tuple_ty = value.ty.clone();
            stmts.push(HirStmt::Let {
                local: tmp,
                init: value,
            });
            for (i, (p, t)) in pats.iter().zip(tys).enumerate() {
                let read = HirExpr {
                    kind: HirExprKind::TupleField {
                        target: Box::new(hir_local(tmp, &tuple_ty, span)),
                        index: u32::try_from(i).expect("tuple index overflow"),
                        field_ty: t.clone(),
                    },
                    ty: t.clone(),
                    span,
                };
                bind_irrefutable(ctx, p, read, stmts);
            }
        }
        (AstPatternKind::Wildcard, _) | (_, HirTy::Unknown) => {}
        (_, ty) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "this pattern can't destructure a value of type `{}` here — `for` \
                     bindings must be a name, `_`, or a tuple of those",
                    ctx.ty_name(&ty)
                ),
            );
        }
    }
}

/// `for pat in iter { body }` (spec 3.9). Supported iterables: an integer
/// range `a..b` / `a..=b` (bounds evaluated once) and any array value.
/// Everything else is rejected — never silently skipped.
///
/// Desugars to a block `{ <setup>; while <cond> { <step>; let pat = ..;
/// body } }` with the step before the body so `continue` can't skip it.
/// `label` goes on the synthesized `While` so `break 'outer` /
/// `continue 'outer` inside the body resolve correctly.
pub(super) fn lower_for(
    ctx: &mut LowerCtx<'_>,
    label: Option<&String>,
    pat: &AstPattern,
    iter: &Expr,
    body: &Block,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let mut out: Vec<HirStmt> = Vec::new();
    ctx.push_scope();
    ctx.breakables.push((label.cloned(), true));
    let while_expr = match &iter.kind {
        ExprKind::Range {
            start: Some(start_e),
            end: Some(end_e),
            inclusive,
        } => lower_for_range(
            ctx, label, pat, start_e, end_e, *inclusive, body, span, &mut out,
        ),
        ExprKind::Range { .. } => Some(ctx.error_expr(
            span,
            "`for` over an unbounded range needs both bounds (`a..b`)".to_owned(),
        )),
        _ => {
            let iter_h = lower_expected(ctx, iter, HirTy::Unknown);
            match iter_h.ty.clone() {
                HirTy::Array(elem, len) => Some(lower_for_array(
                    ctx,
                    label,
                    pat,
                    iter_h,
                    (*elem).clone(),
                    len,
                    body,
                    span,
                    &mut out,
                )),
                HirTy::Unknown => None,
                other => Some(ctx.error_expr(
                    span,
                    format!(
                        "cannot iterate over a value of type `{}` — `for` supports integer \
                         ranges (`a..b`) and arrays (stage-1 limitation)",
                        ctx.ty_name(&other)
                    ),
                )),
            }
        }
    };
    ctx.breakables.pop();
    ctx.pop_scope();
    match while_expr {
        Some(w) => out.push(HirStmt::Expr(w)),
        None => return poison(span),
    }
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: out,
            trailing: None,
            label: None,
        })),
        ty: HirTy::Unit,
        span,
    }
}

/// Integer range loop. Exclusive: `c < end`. Inclusive uses a `go` flag
/// so `a..=MAX` terminates instead of wrapping.
#[allow(clippy::too_many_arguments)]
pub(super) fn lower_for_range(
    ctx: &mut LowerCtx<'_>,
    label: Option<&String>,
    pat: &AstPattern,
    start_e: &Expr,
    end_e: &Expr,
    inclusive: bool,
    body: &Block,
    span: rokc_diagnostic::Span,
    out: &mut Vec<HirStmt>,
) -> Option<HirExpr> {
    let (start_h, end_h) = lower_sibling_pair(ctx, start_e, end_e, HirTy::Unknown);
    if start_h.ty == HirTy::Unknown || end_h.ty == HirTy::Unknown {
        return None;
    }
    let elem_ty = start_h.ty.clone();
    let prim = match &elem_ty {
        HirTy::Prim(p) if p.is_int() && start_h.ty == end_h.ty => *p,
        _ => {
            return Some(ctx.error_expr(
                span,
                format!(
                    "range bounds must be integers of the same type, found `{}` and `{}`",
                    ctx.ty_name(&start_h.ty),
                    ctx.ty_name(&end_h.ty)
                ),
            ));
        }
    };
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let counter = ctx.declare(None, elem_ty.clone());
    let end = ctx.declare(None, elem_ty.clone());
    out.push(HirStmt::Let {
        local: counter,
        init: start_h,
    });
    out.push(HirStmt::Let {
        local: end,
        init: end_h,
    });
    let c = || hir_local(counter, &elem_ty, span);
    let e = || hir_local(end, &elem_ty, span);
    let inc = |c: HirExpr| {
        hir_binop(
            PrimOp::Add,
            c,
            hir_int(1, prim, span),
            elem_ty.clone(),
            span,
        )
    };

    let mut body_stmts: Vec<HirStmt> = Vec::new();
    let snap = ctx.declare(None, elem_ty.clone());
    body_stmts.push(HirStmt::Let {
        local: snap,
        init: c(),
    });
    let cond = if inclusive {
        // go = start <= end; while go { snap = c; go = c < end; if go { c += 1 } ... }
        let go = ctx.declare(None, bool_ty.clone());
        out.push(HirStmt::Let {
            local: go,
            init: hir_binop(PrimOp::Le, c(), e(), bool_ty.clone(), span),
        });
        body_stmts.push(HirStmt::Assign {
            local: go,
            value: hir_binop(PrimOp::Lt, c(), e(), bool_ty.clone(), span),
        });
        body_stmts.push(HirStmt::Expr(HirExpr {
            kind: HirExprKind::If {
                cond: Box::new(hir_local(go, &bool_ty, span)),
                then_block: Box::new(HirBlock {
                    stmts: vec![HirStmt::Assign {
                        local: counter,
                        value: inc(c()),
                    }],
                    trailing: None,
                    label: None,
                }),
                else_branch: None,
            },
            ty: HirTy::Unit,
            span,
        }));
        hir_local(go, &bool_ty, span)
    } else {
        body_stmts.push(HirStmt::Assign {
            local: counter,
            value: inc(c()),
        });
        hir_binop(PrimOp::Lt, c(), e(), bool_ty, span)
    };
    bind_irrefutable(ctx, pat, hir_local(snap, &elem_ty, span), &mut body_stmts);
    let lowered_body = lower_loop_body(ctx, body);
    body_stmts.push(HirStmt::Expr(HirExpr {
        kind: HirExprKind::Block(Box::new(lowered_body)),
        ty: HirTy::Unit,
        span,
    }));
    Some(HirExpr {
        ty: HirTy::Unit,
        span,
        kind: HirExprKind::While {
            label: label.cloned(),
            cond: Box::new(cond),
            body: Box::new(HirBlock {
                stmts: body_stmts,
                trailing: None,
                label: None,
            }),
        },
    })
}

/// `for x in arr` over a `[T; N]` value: the array is bound to a local
/// once, then indexed by a counter.
#[allow(clippy::too_many_arguments)]
pub(super) fn lower_for_array(
    ctx: &mut LowerCtx<'_>,
    label: Option<&String>,
    pat: &AstPattern,
    iter_h: HirExpr,
    elem_ty: HirTy,
    len: u32,
    body: &Block,
    span: rokc_diagnostic::Span,
    out: &mut Vec<HirStmt>,
) -> HirExpr {
    let arr_ty = iter_h.ty.clone();
    let arr_local = if let HirExprKind::Local(l) = iter_h.kind {
        l
    } else {
        let l = ctx.declare(None, arr_ty.clone());
        out.push(HirStmt::Let {
            local: l,
            init: iter_h,
        });
        l
    };
    let idx_prim = PrimTy::I32;
    let idx_ty = HirTy::Prim(idx_prim);
    let counter = ctx.declare(None, idx_ty.clone());
    out.push(HirStmt::Let {
        local: counter,
        init: hir_int(0, idx_prim, span),
    });
    let cond = hir_binop(
        PrimOp::Lt,
        hir_local(counter, &idx_ty, span),
        hir_int(i128::from(len), idx_prim, span),
        HirTy::Prim(PrimTy::Bool),
        span,
    );
    let mut body_stmts: Vec<HirStmt> = Vec::new();
    let snap = ctx.declare(None, idx_ty.clone());
    body_stmts.push(HirStmt::Let {
        local: snap,
        init: hir_local(counter, &idx_ty, span),
    });
    body_stmts.push(HirStmt::Assign {
        local: counter,
        value: hir_binop(
            PrimOp::Add,
            hir_local(counter, &idx_ty, span),
            hir_int(1, idx_prim, span),
            idx_ty.clone(),
            span,
        ),
    });
    let elem_read = HirExpr {
        ty: elem_ty.clone(),
        span,
        kind: HirExprKind::ArrayIndex {
            array: Box::new(hir_local(arr_local, &arr_ty, span)),
            index: Box::new(hir_local(snap, &idx_ty, span)),
            elem_ty,
        },
    };
    bind_irrefutable(ctx, pat, elem_read, &mut body_stmts);
    let lowered_body = lower_loop_body(ctx, body);
    body_stmts.push(HirStmt::Expr(HirExpr {
        kind: HirExprKind::Block(Box::new(lowered_body)),
        ty: HirTy::Unit,
        span,
    }));
    HirExpr {
        ty: HirTy::Unit,
        span,
        kind: HirExprKind::While {
            label: label.cloned(),
            cond: Box::new(cond),
            body: Box::new(HirBlock {
                stmts: body_stmts,
                trailing: None,
                label: None,
            }),
        },
    }
}

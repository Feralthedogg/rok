//! Blocks, statements and expressions.

#[allow(clippy::wildcard_imports)]
use super::*;

pub(super) fn lower_block(ctx: &mut LowerCtx<'_>, block: &Block) -> HirBlock {
    ctx.push_scope();
    let mut stmts = Vec::with_capacity(block.stmts.len());
    for s in &block.stmts {
        match &s.kind {
            StmtKind::LetStruct {
                path,
                fields,
                rest: _,
                ty,
                init,
            } => {
                lower_let_struct(ctx, path, fields, ty.as_ref(), init, s.span, &mut stmts);
            }
            StmtKind::LetTuple {
                names,
                rest,
                ty,
                init,
            } => {
                lower_let_tuple(
                    ctx,
                    names,
                    rest.as_ref(),
                    ty.as_ref(),
                    init,
                    s.span,
                    &mut stmts,
                );
            }
            _ => {
                if let Some(stmt) = lower_stmt(ctx, s) {
                    stmts.push(stmt);
                }
            }
        }
    }
    // The trailing expression is the block's value: it inherits the
    // block's expected type.
    let trailing = block.trailing.as_ref().map(|e| lower_expr(ctx, e));
    ctx.pop_scope();
    HirBlock {
        stmts,
        trailing,
        label: block.label.clone(),
    }
}

/// `let S { f1, f2: alias, .. } [: T] = init;` → temp local + one field
/// read per binding.
pub(super) fn lower_let_struct(
    ctx: &mut LowerCtx<'_>,
    path: &AstPath,
    fields: &[(String, String)],
    ty: Option<&Ty>,
    init: &Expr,
    span: rokc_diagnostic::Span,
    stmts: &mut Vec<HirStmt>,
) {
    let pre_ty = ty.map(|t| ctx.resolve_ast_ty(t));
    let init_h = lower_expected(ctx, init, pre_ty.clone().unwrap_or(HirTy::Unknown));
    let init_h = match &pre_ty {
        Some(t) => coerce(ctx, t, init_h, &|| "the destructured value".to_owned()),
        None => init_h,
    };
    let init_ty = init_h.ty.clone();
    let temp_local = ctx.declare(None, init_ty.clone());
    stmts.push(HirStmt::Let {
        local: temp_local,
        init: init_h,
    });
    let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
    let named = ctx
        .canon_type(&segs)
        .and_then(|full| ctx.lookup_struct(&full));
    let sid = match (&init_ty, named) {
        (HirTy::Unknown, _) => {
            // Init failed (reported); bind the names so later uses don't
            // cascade into "cannot find value".
            for (_, bind) in fields {
                ctx.declare(Some(bind.clone()), HirTy::Unknown);
            }
            return;
        }
        (HirTy::Struct(sid), Some(n)) if *sid == n => *sid,
        (HirTy::Struct(sid), None) if path.segments.is_empty() => *sid,
        _ => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "struct pattern `{}` does not match the value's type `{}`",
                    segs.join("::"),
                    ctx.ty_name(&init_ty)
                ),
            );
            for (_, bind) in fields {
                ctx.declare(Some(bind.clone()), HirTy::Unknown);
            }
            return;
        }
    };
    let def = ctx.struct_def(sid);
    for (field_name, bind_name) in fields {
        let Some(idx) = def.fields.iter().position(|f| &f.name == field_name) else {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "struct `{}` has no field `{field_name}`",
                    ctx.ty_name(&init_ty)
                ),
            );
            ctx.declare(Some(bind_name.clone()), HirTy::Unknown);
            continue;
        };
        ctx.check_field_visible(sid, field_name);
        let field_ty = def.fields[idx].ty.clone();
        let read = HirExpr {
            ty: field_ty.clone(),
            span,
            kind: HirExprKind::FieldRead {
                target: Box::new(HirExpr {
                    ty: init_ty.clone(),
                    span,
                    kind: HirExprKind::Local(temp_local),
                }),
                struct_id: sid,
                field_index: u32::try_from(idx).expect("field idx overflow"),
                field_ty: field_ty.clone(),
            },
        };
        let local = ctx.declare(Some(bind_name.clone()), field_ty);
        stmts.push(HirStmt::Let { local, init: read });
    }
}

/// `let (a, b, ..rest) [: T] = init;` → fresh tuple local plus per-name
/// index reads (spec 3.15.2 / 3.15.3).
pub(super) fn lower_let_tuple(
    ctx: &mut LowerCtx<'_>,
    names: &[String],
    rest: Option<&(usize, Option<String>)>,
    ty: Option<&Ty>,
    init: &Expr,
    span: rokc_diagnostic::Span,
    stmts: &mut Vec<HirStmt>,
) {
    let pre_ty = ty.map(|t| ctx.resolve_ast_ty(t));
    let init_h = lower_expected(ctx, init, pre_ty.clone().unwrap_or(HirTy::Unknown));
    let init_h = match &pre_ty {
        Some(t) => coerce(ctx, t, init_h, &|| "the destructured value".to_owned()),
        None => init_h,
    };
    let init_ty = init_h.ty.clone();
    let elem_tys: Vec<HirTy> = match &init_ty {
        HirTy::Tuple(ts) => ts.clone(),
        HirTy::Unknown => vec![HirTy::Unknown; names.len()],
        other => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "tuple destructure of a non-tuple value of type `{}`",
                    ctx.ty_name(other)
                ),
            );
            vec![HirTy::Unknown; names.len()]
        }
    };
    // Spec 3.15.2/3.15.3: length must match (no rest), or be ≥
    // names.len() when a `..` is present.
    let needed = names.len();
    let have = elem_tys.len();
    if rest.is_none() && have != needed {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "tuple destructure length mismatch: pattern has {needed} element{}, value \
                 has {have} (spec 3.15.2)",
                if needed == 1 { "" } else { "s" }
            ),
        );
    } else if rest.is_some() && have < needed {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "tuple destructure too short: pattern needs at least {needed} non-rest \
                 element{}, value has {have} (spec 3.15.3)",
                if needed == 1 { "" } else { "s" }
            ),
        );
    }
    let tuple_local = ctx.declare(None, init_ty.clone());
    stmts.push(HirStmt::Let {
        local: tuple_local,
        init: init_h,
    });
    // Source-position → name mapping. With a rest at index `r` and a
    // value tuple of length `N`:
    //   names[..r]      → init.0  .. init.r-1
    //   rest (if named) → tuple of init.r .. init.r + (N-needed) - 1
    //   names[r..]      → init.r+(N-needed) .. init.N-1
    let rest_take = if rest.is_some() {
        have.saturating_sub(needed)
    } else {
        0
    };
    let rest_idx = rest.map_or(needed, |(i, _)| *i);
    let read = |index: usize, ety: HirTy| HirExpr {
        ty: ety.clone(),
        span,
        kind: HirExprKind::TupleField {
            target: Box::new(HirExpr {
                ty: init_ty.clone(),
                span,
                kind: HirExprKind::Local(tuple_local),
            }),
            index: u32::try_from(index).expect("tuple index overflow"),
            field_ty: ety,
        },
    };
    for (i, name) in names.iter().enumerate() {
        if name == "_" {
            continue;
        }
        let init_index = if i < rest_idx { i } else { i + rest_take };
        let elem_ty = elem_tys.get(init_index).cloned().unwrap_or(HirTy::Unknown);
        let init = read(init_index, elem_ty.clone());
        let local = ctx.declare(Some(name.clone()), elem_ty);
        stmts.push(HirStmt::Let { local, init });
    }
    // Synthesize the rest-binding's sub-tuple if it was named.
    if let Some((rest_idx, Some(rest_name))) = rest {
        let sub: Vec<HirExpr> = (0..rest_take)
            .map(|k| {
                let src = rest_idx + k;
                read(src, elem_tys.get(src).cloned().unwrap_or(HirTy::Unknown))
            })
            .collect();
        let rest_ty = HirTy::Tuple(sub.iter().map(|e| e.ty.clone()).collect());
        let rest_local = ctx.declare(Some(rest_name.clone()), rest_ty.clone());
        stmts.push(HirStmt::Let {
            local: rest_local,
            init: HirExpr {
                ty: rest_ty,
                span,
                kind: HirExprKind::Tuple { fields: sub },
            },
        });
    }
}

pub(super) fn lower_stmt(ctx: &mut LowerCtx<'_>, stmt: &Stmt) -> Option<HirStmt> {
    match &stmt.kind {
        StmtKind::Let { name, ty, init } => {
            // Spec variant 238-239: same-scope `let` redeclaration is
            // banned (typo guard, no shadowing). Different scopes still
            // create fresh bindings.
            if ctx.lookup_in_current_scope(name).is_some() {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "`{name}` is already declared in this scope. rok forbids \
                         redeclaration with `let`; use `=` to reassign or pick a \
                         different name (spec variant 238)"
                    ),
                );
            }
            // The declared type (if any) is the init's expected type, so
            // literals and generic-enum leaves (`Box::None`) pick it up.
            let pre_ty = ty.as_ref().map(|t| ctx.resolve_ast_ty(t));
            let init = lower_expected(ctx, init, pre_ty.clone().unwrap_or(HirTy::Unknown));
            let (declared_ty, init) = if let Some(t) = pre_ty {
                let init = coerce(ctx, &t, init, &|| format!("`let {name}`"));
                (t, init)
            } else {
                check_let_inferable(ctx, name, &init);
                (init.ty.clone(), init)
            };
            let local = ctx.declare(Some(name.clone()), declared_ty);
            Some(HirStmt::Let { local, init })
        }
        StmtKind::Return(_) if ctx.implicit_main => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "`return` is not allowed in top-level statements (spec 4.16.4); use \
                 `env::exit(code)` or an explicit `fn main() -> i32`"
                    .to_owned(),
            );
            None
        }
        StmtKind::Return(value) => {
            let ret = ctx.fn_ret_ty.clone();
            let value = if let Some(e) = value {
                let lowered = lower_expected(ctx, e, ret.clone());
                // A closure without a declared return type takes it from
                // its first `return`.
                if ret == HirTy::Unknown && ctx.infer_ret {
                    ctx.fn_ret_ty = lowered.ty.clone();
                    Some(lowered)
                } else if matches!((&ret, &lowered.ty), (HirTy::Fn(..), HirTy::Closure { .. })) {
                    // Spec 4.5/4.6: a capturing closure is a `{fn_ptr, env}`
                    // pair, not a bare `fn(...)` pointer.
                    Some(
                        ctx.error_expr(
                            lowered.span,
                            "cannot return a closure through a `fn(...)` pointer return type — \
                         closures with captures aren't bare function pointers (spec 4.6)"
                                .to_owned(),
                        ),
                    )
                } else {
                    Some(coerce(ctx, &ret, lowered, &|| {
                        "the return value".to_owned()
                    }))
                }
            } else {
                if !matches!(ret, HirTy::Unit | HirTy::Unknown) {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "`return;` without a value in a function returning `{}`",
                            ctx.ty_name(&ret)
                        ),
                    );
                }
                None
            };
            Some(lower_return(ctx, value, stmt.span))
        }
        // Statement position: the value is discarded (expected `()`), so
        // `if` / `match` arms needn't agree on a type.
        StmtKind::Expr(expr) | StmtKind::Trailing(expr) => {
            Some(HirStmt::Expr(lower_expected(ctx, expr, HirTy::Unit)))
        }
        StmtKind::Item(rokc_ast::Item::Use(u)) => {
            // Function-local `use` — flatten the tree into UseEntries
            // and push them into the current scope's local_uses list.
            let mut entries = Vec::new();
            crate::uses::flatten_tree_for_local(&u.tree, &[], &ctx.current_module, &mut entries);
            for e in entries {
                ctx.add_local_use(e);
            }
            None
        }
        StmtKind::Item(_) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "items (fn / struct / impl ...) declared inside a function body are not \
                 supported yet — move them to module level (stage-1 limitation)"
                    .to_owned(),
            );
            None
        }
        StmtKind::Assign(target, value) => lower_assign(ctx, target, value, stmt.span),
        StmtKind::CompoundAssign { target, op, value } => {
            // The parser desugars `a op= b` to `a = a op b`; keep a
            // working path should a front end hand us the raw form.
            let op = op.trim_end_matches('=').to_owned();
            let combined = Expr {
                span: stmt.span,
                kind: ExprKind::OpInfix {
                    op,
                    lhs: Box::new(target.clone()),
                    rhs: Box::new(value.clone()),
                },
            };
            lower_assign(ctx, target, &combined, stmt.span)
        }
        StmtKind::LetTuple { .. } | StmtKind::LetStruct { .. } => {
            unreachable!("destructuring lets are expanded by lower_block")
        }
        StmtKind::Break { label, value } => {
            check_jump_target(ctx, "break", label.as_deref(), false);
            let value = value
                .as_ref()
                .map(|e| lower_expected(ctx, e, HirTy::Unknown));
            let depth = jump_index(ctx, label.as_deref(), false);
            let label = label.clone();
            Some(exit_through(
                ctx,
                Some(depth),
                value,
                |value| HirStmt::Break { label, value },
                stmt.span,
            ))
        }
        StmtKind::Continue { label } => {
            check_jump_target(ctx, "continue", label.as_deref(), true);
            let depth = jump_index(ctx, label.as_deref(), true);
            let label = label.clone();
            Some(exit_through(
                ctx,
                Some(depth),
                None,
                |_| HirStmt::Continue { label },
                stmt.span,
            ))
        }
        StmtKind::Throw(value) => Some(lower_throw(ctx, value, stmt.span)),
    }
}

/// D1: an un-annotated `let` takes its initializer's static type, so
/// the initializer must have one. `none` alone and an initializer that
/// never produces a value don't (empty `[]` and differing `if` / `match`
/// branches are rejected where they are lowered).
fn check_let_inferable(ctx: &LowerCtx<'_>, name: &str, init: &HirExpr) {
    let why = if is_none_ty(&init.ty) {
        format!("`none` alone has no value type — write `let {name}: T | none = none;`")
    } else if hir_expr_diverges(init) {
        "the initializer never produces a value (it always returns / breaks / loops)".to_owned()
    } else {
        return;
    };
    ctx.emit_error(
        rokc_diagnostic::ErrorKind::Type,
        format!("cannot infer the type of `{name}`: {why}"),
    );
}

/// `target = value;` for a local / static, a struct-field chain rooted
/// at a local, or an element of a local array.
pub(super) fn lower_assign(
    ctx: &mut LowerCtx<'_>,
    target: &Expr,
    value: &Expr,
    span: rokc_diagnostic::Span,
) -> Option<HirStmt> {
    match &target.kind {
        // Bare-name assignment (local, else `static`).
        ExprKind::Path(p) if p.segments.len() == 1 => {
            let name = &p.segments[0].name;
            if let Some(local) = ctx.lookup(name) {
                let slot_ty = ctx.local_ty(local);
                let v = lower_expected(ctx, value, slot_ty.clone());
                let value = coerce(ctx, &slot_ty, v, &|| format!("assignment to `{name}`"));
                return Some(HirStmt::Assign { local, value });
            }
            let segs = [name.as_str()];
            if let Some(full) = ctx.resolve_in(&segs, &ctx.env.statics) {
                ctx.check_item_visible(&full, "static");
                let ty = ctx.env.statics[&full].clone();
                let v = lower_expected(ctx, value, ty.clone());
                let value = coerce(ctx, &ty, v, &|| format!("assignment to `{name}`"));
                return Some(HirStmt::StaticAssign { name: full, value });
            }
            // Spec variant 234-235: bare-name assign requires the name to
            // have been previously declared (with `let`).
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`{name}` is not declared. Use `let` to introduce a new \
                     binding (typo guard, spec variant 234)"
                ),
            );
            None
        }
        // `arr[idx] = value` — element store on a local array.
        ExprKind::Index(arr_expr, idx_expr) => {
            let arr_h = lower_expected(ctx, arr_expr, HirTy::Unknown);
            let idx_h = lower_expected(ctx, idx_expr, HirTy::Unknown);
            let elem = match (&arr_h.kind, &arr_h.ty) {
                (HirExprKind::Local(l), HirTy::Array(elem, _)) => Some((*l, (**elem).clone())),
                (_, HirTy::Unknown) => return None,
                _ => None,
            };
            let Some((array_local, elem_ty)) = elem else {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "indexed assignment needs a local array variable as target \
                         (found `{}`)",
                        ctx.ty_name(&arr_h.ty)
                    ),
                );
                return None;
            };
            check_index_ty(ctx, &idx_h);
            let v = lower_expected(ctx, value, elem_ty.clone());
            let value = coerce(ctx, &elem_ty, v, &|| "the array element".to_owned());
            Some(HirStmt::ArrayAssign {
                array_local,
                index: idx_h,
                value,
                elem_ty,
            })
        }
        // `a.f1.f2.... = value` — peel field accesses to find the root
        // local, then thread `WithField` updates back out so the rebuilt
        // aggregate gets assigned to that local.
        ExprKind::Field(_, _) => {
            struct Step {
                ty: HirTy,
                struct_id: StructId,
                field_index: u32,
            }
            let mut chain: Vec<&str> = Vec::new();
            let mut cur: &Expr = target;
            while let ExprKind::Field(inner, name) = &cur.kind {
                chain.push(name);
                cur = inner;
            }
            chain.reverse();
            let root_h = lower_expected(ctx, cur, HirTy::Unknown);
            if root_h.ty == HirTy::Unknown {
                return None;
            }
            let HirExprKind::Local(local) = root_h.kind else {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    "field assignment needs a local variable at the root of the target \
                     (`v.f = x`)"
                        .to_owned(),
                );
                return None;
            };
            // Walk the chain to get each level's struct id and field index.
            let mut steps: Vec<Step> = Vec::new();
            let mut step_ty = root_h.ty.clone();
            for name in &chain {
                let HirTy::Struct(sid) = step_ty.clone() else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("no field `{name}` on type `{}`", ctx.ty_name(&step_ty)),
                    );
                    return None;
                };
                let def = ctx.struct_def(sid);
                if def.union_kind.is_some() {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "assigning a field of union `{}` is not implemented yet — \
                             re-initialize the whole union",
                            def.name
                        ),
                    );
                    return None;
                }
                let Some(idx) = def.fields.iter().position(|f| f.name == *name) else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("struct `{}` has no field `{name}`", ctx.ty_name(&step_ty)),
                    );
                    return None;
                };
                ctx.check_field_visible(sid, name);
                steps.push(Step {
                    ty: step_ty.clone(),
                    struct_id: sid,
                    field_index: u32::try_from(idx).expect("field index overflow"),
                });
                step_ty = def.fields[idx].ty.clone();
            }
            let last_name = chain.last().copied().unwrap_or_default().to_owned();
            let v = lower_expected(ctx, value, step_ty.clone());
            let mut acc = coerce(ctx, &step_ty, v, &|| format!("field `{last_name}`"));
            // Materialize parent values via field reads so each
            // WithField has a concrete target.
            let mut targets: Vec<HirExpr> = Vec::new();
            let mut walk = root_h;
            for step in &steps[..steps.len() - 1] {
                let next_ty = ctx.struct_def(step.struct_id).fields[step.field_index as usize]
                    .ty
                    .clone();
                let read = HirExpr {
                    ty: next_ty.clone(),
                    span: target.span,
                    kind: HirExprKind::FieldRead {
                        target: Box::new(walk.clone()),
                        struct_id: step.struct_id,
                        field_index: step.field_index,
                        field_ty: next_ty,
                    },
                };
                targets.push(walk);
                walk = read;
            }
            targets.push(walk);
            for (i, step) in steps.iter().enumerate().rev() {
                acc = HirExpr {
                    ty: step.ty.clone(),
                    span: target.span,
                    kind: HirExprKind::WithField {
                        target: Box::new(targets[i].clone()),
                        struct_id: step.struct_id,
                        field_index: step.field_index,
                        value: Box::new(acc),
                    },
                };
            }
            Some(HirStmt::Assign { local, value: acc })
        }
        _ => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("invalid assignment target (spec 3.4) at line {}", span.line),
            );
            None
        }
    }
}

/// `break` / `continue` must target an enclosing loop (or, for a
/// labelled `break`, a labelled block); MIR would otherwise emit an
/// `unreachable` terminator in its place.
pub(super) fn check_jump_target(
    ctx: &LowerCtx<'_>,
    kw: &str,
    label: Option<&str>,
    needs_loop: bool,
) {
    let ok = match label {
        None => ctx.breakables.iter().any(|(_, is_loop)| *is_loop),
        Some(l) => ctx
            .breakables
            .iter()
            .any(|(bl, is_loop)| bl.as_deref() == Some(l) && (*is_loop || !needs_loop)),
    };
    if !ok {
        let what = label.map_or_else(
            || "a loop".to_owned(),
            |l| format!("a loop labelled `'{l}`"),
        );
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!("`{kw}` outside of {what}"),
        );
    }
}

/// Array indices are integers.
pub(super) fn check_index_ty(ctx: &LowerCtx<'_>, idx: &HirExpr) {
    if !matches!(&idx.ty, HirTy::Prim(p) if p.is_int()) && idx.ty != HirTy::Unknown {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "array index must be an integer, found `{}`",
                ctx.ty_name(&idx.ty)
            ),
        );
    }
}

pub(super) fn lower_expr(ctx: &mut LowerCtx<'_>, expr: &Expr) -> HirExpr {
    let span = expr.span;
    let unsupported = |ctx: &LowerCtx<'_>, what: &str| {
        ctx.error_expr(
            span,
            format!("{what} is not supported yet (stage-1 limitation)"),
        )
    };
    match &expr.kind {
        ExprKind::Literal(lit) => lower_literal(ctx, lit, false, span),
        ExprKind::Path(p) => lower_path(ctx, p, span),
        ExprKind::SelfLower => match ctx.lookup("self") {
            Some(local) => HirExpr {
                kind: HirExprKind::Local(local),
                ty: ctx.local_ty(local),
                span,
            },
            None => ctx.error_expr(span, "`self` is only available inside methods".to_owned()),
        },
        ExprKind::SelfUpper => ctx.error_expr(span, "`Self` is a type, not a value".to_owned()),
        ExprKind::Block(b) => {
            let labelled = b.label.is_some();
            if labelled {
                ctx.breakables.push((b.label.clone(), false));
            }
            let block = lower_block(ctx, b);
            if labelled {
                ctx.breakables.pop();
            }
            // Spec 3.9.10: a labelled block's value can come from a
            // `break 'label value` inside its body, not just from a
            // trailing expression.
            let break_ty = block
                .label
                .as_deref()
                .and_then(|lbl| first_break_value_ty(&block, Some(lbl)));
            let ty = block
                .trailing
                .as_ref()
                .map_or_else(|| break_ty.clone().unwrap_or(HirTy::Unit), |e| e.ty.clone());
            HirExpr {
                kind: HirExprKind::Block(Box::new(block)),
                ty,
                span,
            }
        }
        ExprKind::OpInfix { op, lhs, rhs } => lower_infix(ctx, op, lhs, rhs, span),
        ExprKind::OpPrefix { op, operand } => lower_prefix(ctx, op, operand, span),
        ExprKind::OpPostfix { op, .. } => ctx.error_expr(
            span,
            format!("postfix operator `{op}` has no implementation"),
        ),
        ExprKind::Call {
            callee,
            args,
            trailing_closure,
        } => {
            // Spec 4.8: trailing closure becomes the last positional arg.
            let mut all_args: Vec<rokc_ast::CallArg> = args.clone();
            if let Some(tc) = trailing_closure {
                all_args.push(rokc_ast::CallArg::Positional((**tc).clone()));
            }
            let call = lower_call(ctx, callee, &all_args, span);
            unpack_call(ctx, call)
        }
        ExprKind::MethodCall {
            receiver,
            method,
            args,
            trailing_closure,
            ..
        } => {
            let mut all_args: Vec<rokc_ast::CallArg> = args.clone();
            if let Some(tc) = trailing_closure {
                all_args.push(rokc_ast::CallArg::Positional((**tc).clone()));
            }
            let call = lower_method_call(ctx, receiver, method, &all_args, span);
            unpack_call(ctx, call)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => lower_if(ctx, cond, then_branch, else_branch.as_deref(), span),
        ExprKind::While { label, cond, body } => {
            let cond_h = lower_cond(ctx, cond);
            ctx.breakables.push((label.clone(), true));
            let body_h = lower_loop_body(ctx, body);
            ctx.breakables.pop();
            HirExpr {
                kind: HirExprKind::While {
                    label: label.clone(),
                    cond: Box::new(cond_h),
                    body: Box::new(body_h),
                },
                ty: HirTy::Unit,
                span,
            }
        }
        ExprKind::For {
            label,
            pat,
            iter,
            body,
        } => lower_for(ctx, label.as_ref(), pat, iter, body, span),
        ExprKind::Match { scrutinee, arms } => lower_match(ctx, scrutinee, arms, span),
        ExprKind::Try { kind, operand } => lower_try(ctx, *kind, operand, span),
        ExprKind::Catch {
            body,
            catches,
            finally,
        } => lower_catch(ctx, body, catches, finally.as_ref(), span),
        ExprKind::StructInit {
            path,
            fields,
            spread,
        } => {
            if spread.is_some() {
                return unsupported(ctx, "struct update syntax `..base`");
            }
            lower_struct_init(ctx, path, fields, span)
        }
        ExprKind::Field(target, name) => lower_field(ctx, target, name, span),
        ExprKind::Tuple(items) if items.is_empty() => HirExpr {
            kind: HirExprKind::Const(ConstVal::Unit),
            ty: HirTy::Unit,
            span,
        },
        ExprKind::Tuple(items) => {
            let expected: Option<Vec<HirTy>> = match ctx.current_expected() {
                Some(HirTy::Tuple(ts)) if ts.len() == items.len() => Some(ts.clone()),
                _ => None,
            };
            let lowered: Vec<HirExpr> = items
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    let slot = expected.as_ref().map_or(HirTy::Unknown, |ts| ts[i].clone());
                    let v = lower_expected(ctx, e, slot.clone());
                    wrap_into_sum(&slot, v)
                })
                .collect();
            let tys: Vec<HirTy> = lowered.iter().map(|e| e.ty.clone()).collect();
            HirExpr {
                ty: HirTy::Tuple(tys),
                span,
                kind: HirExprKind::Tuple { fields: lowered },
            }
        }
        ExprKind::TupleField(target, index) => {
            let target_h = lower_expected(ctx, target, HirTy::Unknown);
            let i = *index as usize;
            match target_h.ty.clone() {
                HirTy::Tuple(ts) => match ts.get(i) {
                    Some(field_ty) => HirExpr {
                        ty: field_ty.clone(),
                        span,
                        kind: HirExprKind::TupleField {
                            target: Box::new(target_h),
                            index: *index,
                            field_ty: field_ty.clone(),
                        },
                    },
                    None => ctx.error_expr(
                        span,
                        format!("tuple index {index} out of range for a {}-tuple", ts.len()),
                    ),
                },
                // Spec 2.7.4: tuple-form structs (`struct Foo(i32);`)
                // expose their fields via the same `.N` syntax.
                HirTy::Struct(sid) => {
                    let def = ctx.struct_def(sid);
                    match def.fields.get(i) {
                        Some(f) if f.name == i.to_string() => HirExpr {
                            ty: f.ty.clone(),
                            span,
                            kind: HirExprKind::FieldRead {
                                target: Box::new(target_h),
                                struct_id: sid,
                                field_index: *index,
                                field_ty: f.ty.clone(),
                            },
                        },
                        _ => ctx.error_expr(
                            span,
                            format!("struct `{}` has no field `{index}`", def.name),
                        ),
                    }
                }
                HirTy::Unknown => target_h,
                other => ctx.error_expr(
                    span,
                    format!("no field `{index}` on type `{}`", ctx.ty_name(&other)),
                ),
            }
        }
        ExprKind::List(items) => {
            let expected_elem = match ctx.current_expected() {
                Some(HirTy::Array(e, _)) => Some((**e).clone()),
                _ => None,
            };
            let mut elem_ty = expected_elem;
            let mut lowered: Vec<HirExpr> = Vec::with_capacity(items.len());
            for (i, e) in items.iter().enumerate() {
                let v = lower_expected(ctx, e, elem_ty.clone().unwrap_or(HirTy::Unknown));
                let v = if let Some(t) = &elem_ty {
                    coerce(ctx, t, v, &|| format!("array element {i}"))
                } else {
                    elem_ty = Some(v.ty.clone());
                    v
                };
                lowered.push(v);
            }
            let Some(elem_ty) = elem_ty else {
                return ctx.error_expr(
                    span,
                    "cannot infer the element type of an empty array literal — annotate \
                     the binding (`let a: [i32; 0] = [];`)"
                        .to_owned(),
                );
            };
            let len = u32::try_from(lowered.len()).expect("array literal length overflow");
            HirExpr {
                ty: HirTy::Array(Box::new(elem_ty.clone()), len),
                span,
                kind: HirExprKind::ArrayInit {
                    elem_ty,
                    elements: lowered,
                },
            }
        }
        ExprKind::Index(arr, idx) => {
            let arr_h = lower_expected(ctx, arr, HirTy::Unknown);
            let idx_h = lower_expected(ctx, idx, HirTy::Unknown);
            check_index_ty(ctx, &idx_h);
            let elem_ty = match &arr_h.ty {
                HirTy::Array(t, _) => (**t).clone(),
                HirTy::Unknown => return arr_h,
                other => {
                    return ctx.error_expr(
                        span,
                        format!("cannot index into a value of type `{}`", ctx.ty_name(other)),
                    );
                }
            };
            HirExpr {
                ty: elem_ty.clone(),
                span,
                kind: HirExprKind::ArrayIndex {
                    array: Box::new(arr_h),
                    index: Box::new(idx_h),
                    elem_ty,
                },
            }
        }
        ExprKind::Loop { label, body } => {
            ctx.breakables.push((label.clone(), true));
            let body_h = lower_loop_body(ctx, body);
            ctx.breakables.pop();
            // Pick the first `break <value>` we can see in the body.
            let result_ty = first_break_value_ty(&body_h, label.as_deref()).unwrap_or(HirTy::Unit);
            HirExpr {
                kind: HirExprKind::Loop {
                    label: label.clone(),
                    body: Box::new(body_h),
                    result_ty: result_ty.clone(),
                },
                ty: result_ty,
                span,
            }
        }
        ExprKind::Closure {
            captures,
            params,
            ret_ty,
            body,
            is_async,
            is_generator,
        } => {
            // Spec 4.6.2: `[ref x]` capture-list. Only value capture
            // (snapshot at creation) is modelled; refuse ref captures so
            // mutation isn't silently lost.
            if captures
                .iter()
                .any(|c| matches!(c, rokc_ast::CaptureSpec::Ref(_)))
            {
                return ctx.error_expr(
                    span,
                    "`[ref x]` capture is not yet implemented; closures currently \
                     only support value capture (spec 4.6.2)"
                        .to_owned(),
                );
            }
            if *is_async || *is_generator {
                return unsupported(ctx, "an async / generator closure");
            }
            lower_closure_expr(ctx, params, ret_ty.as_ref(), body, span)
        }
        ExprKind::QuestionDot(receiver, tail) => {
            let recv_h = lower_expected(ctx, receiver, HirTy::Unknown);
            desugar_question_dot(ctx, recv_h, tail, span)
        }
        ExprKind::TryQ(inner) => {
            let inner_h = lower_expected(ctx, inner, HirTy::Unknown);
            desugar_try_q(ctx, inner_h, span)
        }
        ExprKind::NullishCoalesce(lhs, rhs) => {
            let lhs_h = lower_expected(ctx, lhs, HirTy::Unknown);
            desugar_nullish_coalesce(ctx, lhs_h, rhs, span)
        }
        ExprKind::Cast(operand, ty) => {
            let operand_h = lower_expected(ctx, operand, HirTy::Unknown);
            // Spec 2.10.5: monomorphized bodies need `as T` to substitute
            // the concrete type for the type-param (`resolve_ast_ty`).
            let to_ty = ctx.resolve_ast_ty(ty);
            let from_ty = operand_h.ty.clone();
            let castable = |t: &HirTy| matches!(t, HirTy::Prim(p) if p.is_int() || p.is_float() || matches!(p, PrimTy::Bool | PrimTy::CChar | PrimTy::Char));
            if !(from_ty == to_ty
                || matches!(from_ty, HirTy::Unknown)
                || matches!(to_ty, HirTy::Unknown)
                || (castable(&from_ty) && castable(&to_ty)))
            {
                return ctx.error_expr(
                    span,
                    format!(
                        "cannot cast `{}` as `{}` (only numeric / bool / char casts)",
                        ctx.ty_name(&from_ty),
                        ctx.ty_name(&to_ty)
                    ),
                );
            }
            HirExpr {
                kind: HirExprKind::Cast {
                    operand: Box::new(operand_h),
                    from_ty,
                    to_ty: to_ty.clone(),
                },
                ty: to_ty,
                span,
            }
        }
        // Stage-1 await: drop straight through to the inner expression.
        // The async runtime (`rok_task_*`) is all nullptr stubs; when the
        // scheduler lands, this arm becomes a real suspend point.
        ExprKind::Await(inner) => lower_expr(ctx, inner),
        // Spec 4.11: generator `yield N`. Coroutine runtime is a nullptr
        // stub at stage-1, so refuse explicitly rather than miscompile.
        ExprKind::Yield(_) => ctx.error_expr(
            span,
            "`yield` is not yet implemented; generator coroutines require a scheduler \
             that doesn't exist in stage-1 (spec 4.11)"
                .to_owned(),
        ),
        ExprKind::Range { .. } => unsupported(
            ctx,
            "a range value outside a `for` loop header (`for i in a..b`)",
        ),
        ExprKind::Dict(_) => unsupported(ctx, "a dict literal"),
        ExprKind::Set(_) => unsupported(ctx, "a set literal"),
        ExprKind::Is(operand, pat) => lower_is(ctx, operand, pat, span),
        ExprKind::Slice { .. } => unsupported(ctx, "slicing (`a[i:j]`)"),
        ExprKind::LetElse { .. } => unsupported(ctx, "`let ... else` in expression position"),
        ExprKind::AsyncBlock(_) | ExprKind::YieldBlock(_) | ExprKind::AsyncYieldBlock(_) => {
            unsupported(ctx, "an async / generator block")
        }
        ExprKind::Spread(_) => unsupported(ctx, "a spread expression here"),
        ExprKind::Discard(_) => unsupported(ctx, "a discard expression"),
    }
}

/// `if` / `while` conditions are `bool`.
pub(super) fn lower_cond(ctx: &mut LowerCtx<'_>, cond: &Expr) -> HirExpr {
    let c = lower_expected(ctx, cond, HirTy::Prim(PrimTy::Bool));
    coerce(ctx, &HirTy::Prim(PrimTy::Bool), c, &|| {
        "the condition".to_owned()
    })
}

/// Loop bodies yield no value (expected `()`).
pub(super) fn lower_loop_body(ctx: &mut LowerCtx<'_>, body: &Block) -> HirBlock {
    ctx.push_expected(HirTy::Unit);
    let b = lower_block(ctx, body);
    ctx.pop_expected();
    b
}

/// Walk one loop's body looking for the first `break value;` whose
/// label targets this loop. Skips nested loops (they own their breaks).
pub(super) fn first_break_value_ty(b: &HirBlock, label: Option<&str>) -> Option<HirTy> {
    fn walk_block(b: &HirBlock, label: Option<&str>) -> Option<HirTy> {
        for s in &b.stmts {
            if let Some(t) = walk_stmt(s, label) {
                return Some(t);
            }
        }
        b.trailing.as_ref().and_then(|t| walk_expr(t, label))
    }

    fn walk_stmt(s: &HirStmt, label: Option<&str>) -> Option<HirTy> {
        match s {
            HirStmt::Break { label: bl, value } => {
                // Exact match: an unlabeled break belongs only to an
                // unlabeled outer; `break 'L` belongs only to the loop
                // labeled `'L`.
                if bl.as_deref() == label {
                    value.as_ref().map(|v| v.ty.clone())
                } else {
                    None
                }
            }
            HirStmt::Let { init, .. } => walk_expr(init, label),
            HirStmt::Assign { value, .. } => walk_expr(value, label),
            HirStmt::Expr(e) | HirStmt::Return(Some(e)) => walk_expr(e, label),
            _ => None,
        }
    }

    fn walk_expr(e: &HirExpr, label: Option<&str>) -> Option<HirTy> {
        match &e.kind {
            HirExprKind::Block(b) => walk_block(b, label),
            HirExprKind::If {
                cond,
                then_block,
                else_branch,
            } => walk_expr(cond, label)
                .or_else(|| walk_block(then_block, label))
                .or_else(|| else_branch.as_deref().and_then(|e| walk_expr(e, label))),
            HirExprKind::PrimBinOp { lhs, rhs, .. } => {
                walk_expr(lhs, label).or_else(|| walk_expr(rhs, label))
            }
            HirExprKind::PrimUnaryOp { operand, .. } => walk_expr(operand, label),
            HirExprKind::Call { args, .. } => args.iter().find_map(|a| walk_expr(a, label)),
            // For an unlabeled outer, nested loops own all their breaks —
            // skip. For a labeled outer, recurse so a `break 'outer …`
            // inside a nested loop is reachable, but stop at any inner
            // loop that shadows the label.
            HirExprKind::While {
                label: inner, body, ..
            }
            | HirExprKind::Loop {
                label: inner, body, ..
            } => {
                if label.is_some() && inner.as_deref() != label {
                    walk_block(body, label)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    walk_block(b, label)
}

pub(super) fn enum_base_name(name: &str) -> &str {
    name.split("__").next().unwrap_or(name)
}

/// Resolve an enum variant path. For a generic enum the instantiation
/// comes from `hint` (expected / scrutinee type), else from the single
/// instantiation whose variant payload fits `arg_tys`.
pub(super) fn resolve_enum_variant(
    ctx: &LowerCtx<'_>,
    segs: &[&str],
    hint: Option<&HirTy>,
    arg_tys: Option<&[HirTy]>,
) -> EnumRes {
    let Some((full, vname)) = ctx.enum_path(segs) else {
        return EnumRes::NotEnum;
    };
    let variant_of = |eid: EnumId| {
        ctx.enum_def(eid)
            .variants
            .iter()
            .position(|v| v.name == vname)
    };
    let eid = if let Some(HirTy::Enum(h)) = hint
        .filter(|h| matches!(h, HirTy::Enum(e) if enum_base_name(&ctx.enum_def(*e).name) == full))
    {
        *h
    } else if let Some(eid) = ctx.lookup_enum(&full) {
        eid
    } else {
        let insts = ctx.enum_instantiations(&full);
        if insts.is_empty() {
            return EnumRes::NotEnum;
        }
        let fits: Vec<EnumId> = insts
            .into_iter()
            .filter(|&eid| {
                let Some(vi) = variant_of(eid) else {
                    return false;
                };
                let v = &ctx.enum_def(eid).variants[vi];
                match (arg_tys, &v.payload_ty) {
                    (None, None) => true,
                    (Some(args), Some(p)) => {
                        let parts: Vec<HirTy> = match (v.arity, p) {
                            (1, t) => vec![t.clone()],
                            (_, HirTy::Tuple(ps)) => ps.clone(),
                            (_, t) => vec![t.clone()],
                        };
                        parts.len() == args.len()
                            && parts
                                .iter()
                                .zip(args)
                                .all(|(p, a)| ty_compatible(p, a) && *a != HirTy::Unknown)
                    }
                    _ => false,
                }
            })
            .collect();
        match fits.as_slice() {
            [one] => *one,
            [] => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "no instantiation of generic enum `{full}` matches `{}`",
                        segs.join("::")
                    ),
                );
                return EnumRes::Error;
            }
            _ => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "cannot infer the type arguments of `{full}` for `{}` — annotate the \
                         binding with the concrete type",
                        segs.join("::")
                    ),
                );
                return EnumRes::Error;
            }
        }
    };
    if let Some(i) = variant_of(eid) {
        EnumRes::Found(eid, i)
    } else {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!("enum `{full}` has no variant `{vname}`"),
        );
        EnumRes::Error
    }
}

/// Payload slot types of a variant, one per constructor argument.
pub(super) fn variant_arg_tys(v: &HirEnumVariant) -> Vec<HirTy> {
    match (&v.payload_ty, v.arity) {
        (None, _) => Vec::new(),
        (Some(t), 1) => vec![t.clone()],
        (Some(HirTy::Tuple(ps)), _) => ps.clone(),
        (Some(t), _) => vec![t.clone()],
    }
}

// `Foo { field: value, ... }` — fields are placed in declaration order.
pub(super) fn lower_struct_init(
    ctx: &mut LowerCtx<'_>,
    path: &AstPath,
    fields: &[(String, Expr)],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
    {
        let mut seen = std::collections::HashSet::new();
        for (n, _) in fields {
            if !seen.insert(n.as_str()) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "field `{n}` specified more than once in `{}` literal",
                        segs.join("::")
                    ),
                );
            }
        }
    }
    // `EnumName::Variant { x: ..., y: ... }` — enum named-form variant
    // initialiser (spec 2.4). Pack fields into the variant's tuple
    // payload according to declaration order.
    let hint = ctx.current_expected().cloned();
    match resolve_enum_variant(ctx, &segs, hint.as_ref(), None) {
        EnumRes::Error => return poison(span),
        EnumRes::Found(enum_id, idx) => {
            let variant = ctx.enum_def(enum_id).variants[idx].clone();
            if variant.named_fields.is_empty() {
                return ctx.error_expr(
                    span,
                    format!("`{}` is not a struct-like enum variant", segs.join("::")),
                );
            }
            let field_tys = variant_arg_tys(&variant);
            let mut payload_args: Vec<Option<HirExpr>> = vec![None; variant.named_fields.len()];
            for (n, e) in fields {
                match variant.named_fields.iter().position(|f| f == n) {
                    Some(i) => {
                        let v = lower_expected(ctx, e, field_tys[i].clone());
                        payload_args[i] =
                            Some(coerce(ctx, &field_tys[i], v, &|| format!("field `{n}`")));
                    }
                    None => {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "enum variant `{}` has no field `{n}` (spec 2.4)",
                                segs.join("::")
                            ),
                        );
                    }
                }
            }
            let mut args = Vec::with_capacity(payload_args.len());
            for (i, a) in payload_args.into_iter().enumerate() {
                if let Some(a) = a {
                    args.push(a);
                } else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "enum variant `{}` is missing field `{}` (spec 2.4)",
                            segs.join("::"),
                            variant.named_fields[i]
                        ),
                    );
                    args.push(poison(span));
                }
            }
            return HirExpr {
                kind: HirExprKind::EnumVariantInit {
                    enum_id,
                    variant_index: u32::try_from(idx).expect("variant overflow"),
                    args,
                },
                ty: HirTy::Enum(enum_id),
                span,
            };
        }
        EnumRes::NotEnum => {}
    }

    let Some(full) = ctx.canon_type(&segs) else {
        for (_, e) in fields {
            lower_expected(ctx, e, HirTy::Unknown);
        }
        return ctx.error_expr(
            span,
            format!("cannot find struct `{}` in this scope", segs.join("::")),
        );
    };
    // Values lowered before the struct is known (generic inference);
    // reused below so each field expression is evaluated exactly once.
    let mut pre: Vec<Option<HirExpr>> = vec![None; fields.len()];
    let explicit_generics = path.segments.last().is_some_and(|s| !s.generics.is_empty());
    let struct_id = if explicit_generics {
        let synth = Ty {
            kind: AstTyKind::Path(path.clone()),
            span: path.span,
        };
        match ctx.resolve_ast_ty(&synth) {
            HirTy::Struct(id) => id,
            _ => {
                return ctx.error_expr(
                    span,
                    format!(
                        "cannot instantiate `{}` with these type arguments",
                        segs.join("::")
                    ),
                );
            }
        }
    } else if let Some(id) = ctx.lookup_struct(&full) {
        id
    } else if let Some(def) = ctx.env.generic_structs.get(&full).copied() {
        // `Box { v: 5 }`: the expected type picks the instantiation;
        // otherwise infer the type arguments from the field values.
        match &hint {
            Some(HirTy::Struct(h))
                if enum_base_name(&ctx.struct_def(*h).name) == full
                    && !ctx.struct_def(*h).generic_args.is_empty() =>
            {
                *h
            }
            _ => {
                let AstStructKind::Named(decl_fields) = &def.kind else {
                    return ctx
                        .error_expr(span, format!("`{full}` is not a struct with named fields"));
                };
                let generic_names: std::collections::HashSet<String> = def
                    .generics
                    .params
                    .iter()
                    .filter_map(|gp| match gp {
                        rokc_ast::GenericParam::Type { name, .. } => Some(name.clone()),
                        rokc_ast::GenericParam::Const { .. } => None,
                    })
                    .collect();
                let mut subst: HashMap<String, HirTy> = HashMap::new();
                for (i, (n, e)) in fields.iter().enumerate() {
                    let v = lower_expected(ctx, e, HirTy::Unknown);
                    if let Some(df) = decl_fields.iter().find(|f| f.name == *n) {
                        unify_param_ty_with(&df.ty, &v.ty, &generic_names, &mut subst, ctx);
                    }
                    pre[i] = Some(v);
                }
                let mut args = Vec::new();
                for gp in &def.generics.params {
                    if let rokc_ast::GenericParam::Type { name, default, .. } = gp {
                        match subst
                            .get(name)
                            .cloned()
                            .or_else(|| default.as_ref().map(|d| ctx.resolve_ast_ty(d)))
                        {
                            Some(t) if t != HirTy::Unknown => args.push(t),
                            Some(_) => return poison(span),
                            None => {
                                return ctx.error_expr(
                                    span,
                                    format!(
                                        "cannot infer type parameter `{name}` of `{full}` — \
                                         write `{}<...> {{ ... }}`",
                                        segs.join("::")
                                    ),
                                );
                            }
                        }
                    }
                }
                match ctx.instantiate_struct(&full, args) {
                    Some(id) => id,
                    None => return poison(span),
                }
            }
        }
    } else {
        return ctx.error_expr(span, format!("`{full}` is not a struct"));
    };
    let def = ctx.struct_def(struct_id);
    let ty_display = ctx.ty_name(&HirTy::Struct(struct_id));
    // Spec 2.x / i-want 322: `union { ... }` initialiser. Exactly one
    // declared field gets its value cast/bitcast into the synthetic
    // `__data` storage slot.
    if let Some(union_kind) = def.union_kind.clone() {
        if fields.len() != 1 {
            return ctx.error_expr(
                span,
                format!(
                    "union `{}` initialiser must list exactly one field (spec 2.x — got {})",
                    def.name,
                    fields.len()
                ),
            );
        }
        let (fname, value) = &fields[0];
        let Some(field_ty) = union_kind
            .aliases
            .iter()
            .find(|(n, _)| n == fname)
            .map(|(_, t)| t.clone())
        else {
            return ctx.error_expr(
                span,
                format!("union `{}` has no field `{fname}` (spec 2.x)", def.name),
            );
        };
        ctx.check_field_visible(struct_id, fname);
        let lowered = lower_expected(ctx, value, field_ty.clone());
        let lowered = coerce(ctx, &field_ty, lowered, &|| format!("field `{fname}`"));
        let storage_ty = def.fields[0].ty.clone();
        let casted = HirExpr {
            kind: HirExprKind::UnionWrite {
                struct_id,
                from_ty: lowered.ty.clone(),
                storage_ty: storage_ty.clone(),
                value: Box::new(lowered),
            },
            ty: storage_ty,
            span,
        };
        return HirExpr {
            kind: HirExprKind::StructInit {
                struct_id,
                fields: vec![casted],
            },
            ty: HirTy::Struct(struct_id),
            span,
        };
    }
    let mut ordered: Vec<Option<HirExpr>> = vec![None; def.fields.len()];
    for (i, (name, value)) in fields.iter().enumerate() {
        let Some(idx) = def.fields.iter().position(|f| f.name == *name) else {
            if pre[i].is_none() {
                lower_expected(ctx, value, HirTy::Unknown);
            }
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("struct `{ty_display}` has no field `{name}`"),
            );
            continue;
        };
        ctx.check_field_visible(struct_id, name);
        let target_ty = def.fields[idx].ty.clone();
        let lowered = match pre[i].take() {
            Some(v) => v,
            None => lower_expected(ctx, value, target_ty.clone()),
        };
        ordered[idx] = Some(coerce(ctx, &target_ty, lowered, &|| {
            format!("field `{name}`")
        }));
    }
    // Spec 2.x / i-want 942-950: missing fields fall back to their
    // declared default expression; no default → "missing field" error.
    let mut out = Vec::with_capacity(ordered.len());
    for (f, v) in def.fields.iter().zip(ordered) {
        match (v, &f.default) {
            (Some(v), _) => out.push(v),
            (None, Some(default_expr)) => {
                let lowered = lower_expected(ctx, default_expr, f.ty.clone());
                out.push(coerce(ctx, &f.ty, lowered, &|| {
                    format!("the default of field `{}`", f.name)
                }));
            }
            (None, None) => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "struct `{ty_display}` is missing field `{}` and no default is \
                         declared (spec 2.x / i-want 942-950)",
                        f.name
                    ),
                );
                out.push(poison(span));
            }
        }
    }
    HirExpr {
        kind: HirExprKind::StructInit {
            struct_id,
            fields: out,
        },
        ty: HirTy::Struct(struct_id),
        span,
    }
}

// `expr.field` on a struct.
pub(super) fn lower_field(
    ctx: &mut LowerCtx<'_>,
    target: &Expr,
    name: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let target_h = lower_expected(ctx, target, HirTy::Unknown);
    field_access(ctx, target_h, name, span)
}

/// Read field `name` of an already-lowered struct / union value.
pub(super) fn field_access(
    ctx: &LowerCtx<'_>,
    target_h: HirExpr,
    name: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let struct_id = match &target_h.ty {
        HirTy::Struct(id) => *id,
        HirTy::Unknown => return target_h,
        other => {
            return ctx.error_expr(
                span,
                format!("no field `{name}` on type `{}`", ctx.ty_name(other)),
            );
        }
    };
    let def = ctx.struct_def(struct_id);
    // Spec 2.x / i-want 322: union field read goes through `UnionRead`
    // so MIR/codegen can issue the right cast/bitcast against the
    // single `__data` storage slot.
    if let Some(union_kind) = def.union_kind.clone() {
        let storage_ty = def.fields[0].ty.clone();
        let Some(field_ty) = union_kind
            .aliases
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, t)| t.clone())
        else {
            return ctx.error_expr(
                span,
                format!("union `{}` has no field `{name}` (spec 2.x)", def.name),
            );
        };
        ctx.check_field_visible(struct_id, name);
        return HirExpr {
            kind: HirExprKind::UnionRead {
                struct_id,
                target: Box::new(target_h),
                field_name: name.to_owned(),
                storage_ty,
                field_ty: field_ty.clone(),
            },
            ty: field_ty,
            span,
        };
    }
    let Some(idx) = def.fields.iter().position(|f| f.name == name) else {
        return ctx.error_expr(
            span,
            format!(
                "struct `{}` has no field `{name}`",
                ctx.ty_name(&HirTy::Struct(struct_id))
            ),
        );
    };
    ctx.check_field_visible(struct_id, name);
    let field_ty = def.fields[idx].ty.clone();
    HirExpr {
        kind: HirExprKind::FieldRead {
            target: Box::new(target_h),
            struct_id,
            field_index: u32::try_from(idx).expect("field index overflow"),
            field_ty: field_ty.clone(),
        },
        ty: field_ty,
        span,
    }
}

/// An unsuffixed numeric literal (optionally negated): its type comes
/// from context.
pub(super) fn is_untyped_literal(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Literal(AstLit::Int(t)) => !has_int_suffix(t),
        ExprKind::Literal(AstLit::Float(t)) => !t.ends_with("f32") && !t.ends_with("f64"),
        ExprKind::OpPrefix { op, operand } if op == "-" => is_untyped_literal(operand),
        _ => false,
    }
}

/// Lower two sibling operands that must share a type: an untyped
/// literal on either side takes the other side's type. Evaluation stays
/// left-to-right except when the left side is a literal (no effects).
pub(super) fn lower_sibling_pair(
    ctx: &mut LowerCtx<'_>,
    lhs: &Expr,
    rhs: &Expr,
    lhs_expected: HirTy,
) -> (HirExpr, HirExpr) {
    if is_untyped_literal(lhs) && !is_untyped_literal(rhs) {
        let r = lower_expected(ctx, rhs, lhs_expected);
        let l = lower_expected(ctx, lhs, r.ty.clone());
        (l, r)
    } else {
        let l = lower_expected(ctx, lhs, lhs_expected);
        let r = lower_expected(ctx, rhs, l.ty.clone());
        (l, r)
    }
}

pub(super) fn hir_local(local: LocalId, ty: &HirTy, span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr {
        kind: HirExprKind::Local(local),
        ty: ty.clone(),
        span,
    }
}

pub(super) const fn hir_int(value: i128, prim: PrimTy, span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr {
        kind: HirExprKind::Const(ConstVal::Int { value, ty: prim }),
        ty: HirTy::Prim(prim),
        span,
    }
}

pub(super) fn hir_binop(
    op: PrimOp,
    lhs: HirExpr,
    rhs: HirExpr,
    ty: HirTy,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    HirExpr {
        kind: HirExprKind::PrimBinOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
        ty,
        span,
    }
}

// Decode a `"..."` literal body (spec 1.7.1). The lexer already
// rejected malformed escapes, so the fallback is never taken.
pub(super) fn decode_str_escapes(s: &str) -> String {
    rokc_ast::escape::unescape(s, rokc_ast::escape::EscapeMode::Str)
        .unwrap_or_else(|_| s.to_owned())
}

pub(super) fn has_int_suffix(text: &str) -> bool {
    const SUFFIXES: &[&str] = &[
        "isize", "usize", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
    ];
    SUFFIXES.iter().any(|s| text.ends_with(s))
}

pub(super) fn lower_if(
    ctx: &mut LowerCtx<'_>,
    cond: &Expr,
    then_block: &Block,
    else_branch: Option<&Expr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // Spec 2.2.6: `if x is T { .. }` narrows the local `x` to `T` inside
    // the then-block — lowered as `match x { x: T => { .. }, _ => else }`.
    // ponytail: only a bare local as the whole condition narrows (not
    // `x is T && ..`); assigning to `x` inside the block writes the
    // narrowed copy.
    let narrow = match &cond.kind {
        ExprKind::Is(operand, pat) => match (&operand.kind, &pat.kind) {
            (ExprKind::Path(p), AstPatternKind::TypeCheck { binder: None, ty })
                if p.segments.len() == 1 && ctx.lookup(&p.segments[0].name).is_some() =>
            {
                Some((operand, &p.segments[0].name, ty))
            }
            _ => None,
        },
        _ => None,
    };
    let mut cond_h = None;
    let mut narrow_h = None;
    if let Some((operand, name, ty)) = narrow {
        let scrut = lower_expected(ctx, operand, HirTy::Unknown);
        ctx.push_scope();
        let pat = rokc_ast::Pattern {
            kind: AstPatternKind::TypeCheck {
                binder: Some(name.clone()),
                ty: ty.clone(),
            },
            span: cond.span,
        };
        let pat_h = lower_pattern(ctx, &pat, &scrut.ty);
        narrow_h = Some((scrut, pat_h));
    } else {
        cond_h = Some(lower_cond(ctx, cond));
    }
    let expected = ctx
        .current_expected()
        .cloned()
        .filter(|t| *t != HirTy::Unknown);
    let mut then_h = lower_block(ctx, then_block);
    if narrow_h.is_some() {
        ctx.pop_scope();
    }
    // `if` → `match` for a narrowing condition.
    let build = |cond_h: Option<HirExpr>,
                 then_h: HirBlock,
                 else_h: Option<HirExpr>,
                 ty: HirTy,
                 narrow_h: Option<(HirExpr, HirPattern)>| {
        let kind = match (cond_h, narrow_h) {
            (_, Some((scrut, pat))) => {
                let empty = || HirExpr {
                    kind: HirExprKind::Block(Box::new(HirBlock {
                        stmts: Vec::new(),
                        trailing: None,
                        label: None,
                    })),
                    ty: HirTy::Unit,
                    span,
                };
                HirExprKind::Match {
                    scrutinee: Box::new(scrut),
                    arms: vec![
                        HirMatchArm {
                            pat,
                            guard: None,
                            body: HirExpr {
                                kind: HirExprKind::Block(Box::new(then_h)),
                                ty: ty.clone(),
                                span,
                            },
                        },
                        HirMatchArm {
                            pat: HirPattern::Wildcard,
                            guard: None,
                            body: else_h.unwrap_or_else(empty),
                        },
                    ],
                }
            }
            (cond_h, None) => HirExprKind::If {
                cond: Box::new(cond_h.expect("if condition")),
                then_block: Box::new(then_h),
                else_branch: else_h.map(Box::new),
            },
        };
        HirExpr { kind, ty, span }
    };
    let Some(else_e) = else_branch else {
        // No else: the if is a statement; any then-value is discarded.
        return build(cond_h, then_h, None, HirTy::Unit, narrow_h);
    };
    let mut else_h = lower_expr(ctx, else_e);
    // Spec 3.14.1: a diverging branch (`return` / `throw` / ...) takes
    // the other branch's type.
    let then_ty = then_h
        .trailing
        .as_ref()
        .map_or(HirTy::Unit, |e| e.ty.clone());
    let else_ty = else_h.ty.clone();
    let then_div = hir_block_diverges(&then_h);
    let else_div = hir_expr_diverges(&else_h);
    let result_ty = if expected == Some(HirTy::Unit) {
        // Statement position: branch values are discarded.
        HirTy::Unit
    } else if then_div {
        else_ty
    } else if else_div || then_ty == else_ty {
        then_ty
    } else if then_ty == HirTy::Unknown || else_ty == HirTy::Unknown {
        HirTy::Unknown
    } else if let Some(t) =
        expected.filter(|t| coercible(ctx, t, &then_ty) && coercible(ctx, t, &else_ty))
    {
        t
    } else {
        // D1: branches of different types are an error, not an inferred
        // sum — the slot's annotation must name the sum.
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "`if` branches have different types `{}` and `{}` — rok does not infer a \
                 sum type; annotate the slot (`let v: {} | {} = if ...`)",
                ctx.ty_name(&then_ty),
                ctx.ty_name(&else_ty),
                ctx.ty_name(&then_ty),
                ctx.ty_name(&else_ty)
            ),
        );
        HirTy::Unknown
    };
    if matches!(result_ty, HirTy::Sum(_) | HirTy::AnyTrait(_)) {
        let what = || "the `if` branch".to_owned();
        if let Some(t) = then_h.trailing.take() {
            then_h.trailing = Some(coerce(ctx, &result_ty, t, &what));
        }
        else_h = match else_h.kind {
            HirExprKind::Block(mut b) => {
                if let Some(t) = b.trailing.take() {
                    b.trailing = Some(coerce(ctx, &result_ty, t, &what));
                }
                HirExpr {
                    ty: result_ty.clone(),
                    kind: HirExprKind::Block(b),
                    span: else_h.span,
                }
            }
            _ => coerce(ctx, &result_ty, else_h, &what),
        };
    }
    build(cond_h, then_h, Some(else_h), result_ty, narrow_h)
}

/// Spec 2.2.5: `v is T` — `match v { _: T => true, _ => false }`.
fn lower_is(
    ctx: &mut LowerCtx<'_>,
    operand: &Expr,
    pat: &rokc_ast::Pattern,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let scrut = lower_expected(ctx, operand, HirTy::Unknown);
    if scrut.ty == HirTy::Unknown {
        return scrut;
    }
    ctx.push_scope();
    let pat_h = lower_pattern(ctx, pat, &scrut.ty);
    ctx.pop_scope();
    let lit = |b: bool| HirExpr {
        kind: HirExprKind::Const(ConstVal::Bool(b)),
        ty: HirTy::Prim(PrimTy::Bool),
        span,
    };
    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(scrut),
            arms: vec![
                HirMatchArm {
                    pat: pat_h,
                    guard: None,
                    body: lit(true),
                },
                HirMatchArm {
                    pat: HirPattern::Wildcard,
                    guard: None,
                    body: lit(false),
                },
            ],
        },
        ty: HirTy::Prim(PrimTy::Bool),
        span,
    }
}

/// Lower call arguments against a signature: named arguments go to
/// their parameter slot (spec 4.1), tuple spreads fill consecutive
/// slots, missing trailing parameters take their defaults, and every
/// argument is checked against its parameter type. `receiver` fills
/// slot 0 (method calls).
pub(super) fn lower_args_for(
    ctx: &mut LowerCtx<'_>,
    sig: &FnSig,
    callee: &str,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> (Vec<HirExpr>, Vec<HirStmt>) {
    let n = sig.param_tys.len();
    let mut lets: Vec<HirStmt> = Vec::new();
    let mut slots: Vec<Option<ArgSrc<'_>>> = (0..n).map(|_| None).collect();
    let mut next = 0usize;
    let mut extra = 0usize;
    if let Some(r) = receiver {
        if n > 0 {
            slots[0] = Some(ArgSrc::Lowered(r));
        }
        next = 1;
    }
    for a in args {
        match a {
            CallArg::Positional(e) => {
                if next < n {
                    slots[next] = Some(ArgSrc::Ast(e));
                } else {
                    lower_expected(ctx, e, HirTy::Unknown);
                    extra += 1;
                }
                next += 1;
            }
            CallArg::Named { name, value } => {
                match sig.param_names.iter().position(|p| p == name) {
                    Some(i) if slots[i].is_none() => slots[i] = Some(ArgSrc::Ast(value)),
                    Some(_) => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("argument `{name}` provided more than once (spec 4.1)"),
                    ),
                    None => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("`{callee}` has no parameter named `{name}` (spec 4.1)"),
                    ),
                }
            }
            CallArg::Spread(e) => {
                // Spec 4.1 / variant 838: `f(..t)` with a tuple value.
                let lh = lower_expected(ctx, e, HirTy::Unknown);
                match lh.ty.clone() {
                    HirTy::Tuple(parts) => {
                        // Evaluate the tuple once into a temp, then read
                        // its fields.
                        let tuple_ty = lh.ty.clone();
                        let tmp = ctx.declare(None, tuple_ty.clone());
                        lets.push(HirStmt::Let {
                            local: tmp,
                            init: lh,
                        });
                        for (i, part_ty) in parts.iter().enumerate() {
                            let field = HirExpr {
                                kind: HirExprKind::TupleField {
                                    target: Box::new(hir_local(tmp, &tuple_ty, span)),
                                    index: u32::try_from(i).expect("tuple field overflow"),
                                    field_ty: part_ty.clone(),
                                },
                                ty: part_ty.clone(),
                                span,
                            };
                            if next < n {
                                slots[next] = Some(ArgSrc::Lowered(field));
                            } else {
                                extra += 1;
                            }
                            next += 1;
                        }
                    }
                    HirTy::Unknown => {}
                    other => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "spread `f(..x)` needs a tuple value, found `{}` (List/Dict \
                             spread are separate milestones, spec 4.1)",
                            ctx.ty_name(&other)
                        ),
                    ),
                }
            }
        }
    }
    if extra > 0 {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "`{callee}` takes {n} argument(s) but {} were supplied",
                n + extra
            ),
        );
    }
    let mut out = Vec::with_capacity(n);
    for (i, slot) in slots.into_iter().enumerate() {
        let pty = sig.param_tys[i].clone();
        let pname = sig.param_names.get(i).cloned().unwrap_or_default();
        let v = match slot {
            Some(ArgSrc::Ast(e)) => lower_expected(ctx, e, pty.clone()),
            Some(ArgSrc::Lowered(h)) => h,
            None => {
                if let Some(d) = sig.param_defaults.get(i).cloned().flatten() {
                    lower_expected(ctx, &d, pty.clone())
                } else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("missing argument `{pname}` in call to `{callee}`"),
                    );
                    poison(span)
                }
            }
        };
        out.push(coerce(ctx, &pty, v, &|| {
            format!("argument `{pname}` of `{callee}`")
        }));
    }
    (out, lets)
}

/// `Call` to a statically known function with checked arguments.
pub(super) fn call_sig(
    ctx: &mut LowerCtx<'_>,
    sig: &FnSig,
    callee: &str,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let (lowered, lets) = lower_args_for(ctx, sig, callee, receiver, args, span);
    with_lets(
        lets,
        HirExpr {
            kind: HirExprKind::Call {
                callee: sig.id,
                args: lowered,
            },
            ty: sig.ret_ty.clone(),
            span,
        },
    )
}

/// `{ lets; e }` — temporaries a spread argument introduced, so the
/// spread tuple is evaluated once.
pub(super) fn with_lets(lets: Vec<HirStmt>, e: HirExpr) -> HirExpr {
    if lets.is_empty() {
        return e;
    }
    let (ty, span) = (e.ty.clone(), e.span);
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: lets,
            trailing: Some(e),
            label: None,
        })),
        ty,
        span,
    }
}

// `recv.method(args)` → Call to `Type__method(recv, args)`.
pub(super) fn lower_method_call(
    ctx: &mut LowerCtx<'_>,
    receiver: &Expr,
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let recv_h = lower_expected(ctx, receiver, HirTy::Unknown);
    method_call_on(ctx, recv_h, method, args, span)
}

/// Method call on an already-lowered receiver (also used by `?.`).
pub(super) fn method_call_on(
    ctx: &mut LowerCtx<'_>,
    recv_h: HirExpr,
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let lower_args_only = |ctx: &mut LowerCtx<'_>| discard_args(ctx, args);
    if recv_h.ty == HirTy::Unknown {
        lower_args_only(ctx);
        return recv_h;
    }
    if let HirTy::AnyTrait(bounds) = recv_h.ty.clone() {
        return any_method_call(ctx, recv_h, &bounds, method, args, span);
    }
    let found = method_target_for(&recv_h.ty)
        .and_then(|t| ctx.env.method_table.get(&(t, method.to_owned())).copied());
    let Some(fn_id) = found else {
        if let Some(gm) = generic_method_for(ctx, &recv_h.ty, method) {
            check_method_info_visible(ctx, &gm.info, method);
            if gm.def.params.first().map(|p| p.name.as_str()) != Some("self") {
                lower_args_only(ctx);
                return ctx.error_expr(
                    span,
                    format!(
                        "`{method}` is an associated function, not a method — call it as \
                         `{}::{method}(...)`",
                        ctx.ty_name(&recv_h.ty)
                    ),
                );
            }
            return call_generic(
                ctx,
                &gm.def,
                Some(&gm.self_ty),
                Some(recv_h),
                args,
                method,
                span,
            );
        }
        lower_args_only(ctx);
        // Spec 3.5.2: a missing method is a hard error, not a silent
        // unit return.
        return ctx.error_expr(
            span,
            format!(
                "no method `{method}` found for type `{}` (spec 3.5.2). Either add \
                 `impl {{ fn {method}(...) {{...}} }}` or import a trait that provides it.",
                ctx.ty_name(&recv_h.ty)
            ),
        );
    };
    check_method_visible(ctx, fn_id, method);
    let key = format!("{}__{}", ty_mangle(&recv_h.ty), method);
    let sig = ctx.env.fn_table[&key].clone();
    if sig.param_names.first().map(String::as_str) != Some("self") {
        lower_args_only(ctx);
        return ctx.error_expr(
            span,
            format!(
                "`{method}` is an associated function, not a method — call it as \
                 `{}::{method}(...)`",
                ctx.ty_name(&recv_h.ty)
            ),
        );
    }
    call_sig(ctx, &sig, method, Some(recv_h), args, span)
}

/// `v.m(args)` on an `any Tr` value (D4). Only methods of the bound
/// traits and their supertraits are callable; the call becomes a switch
/// on the tag over every implementor in the program:
/// `match v { x: T1 => T1::m(x, args), x: T2 => T2::m(x, args), ... }`.
fn any_method_call(
    ctx: &mut LowerCtx<'_>,
    recv_h: HirExpr,
    bounds: &[String],
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let mut seen: Vec<String> = Vec::new();
    let mut stack = bounds.to_vec();
    // The trait declaring `method`, and whether the bound gave its args.
    let mut provider: Option<(String, bool)> = None;
    while let Some(t) = stack.pop() {
        let base = bound_base(&t).to_owned();
        if seen.contains(&base) {
            continue;
        }
        if let Some(info) = ctx.env.trait_info.get(&base) {
            if provider.is_none() && info.methods.iter().any(|m| m == method) {
                provider = Some((base.clone(), t.contains('<')));
            }
            stack.extend(info.supers.iter().cloned());
        }
        seen.push(base);
    }
    let recv_ty = recv_h.ty.clone();
    let Some((provider, has_args)) = provider else {
        discard_args(ctx, args);
        return ctx.error_expr(
            span,
            format!(
                "no method `{method}` on `{}` — only methods of its trait bound(s) and their \
                 supertraits can be called on an `any` value; narrow it with a type pattern \
                 (`match v {{ x: T => ... }}`) to reach other methods (D4)",
                ctx.ty_name(&recv_ty)
            ),
        );
    };
    // Every implementor shares one signature only if it doesn't depend
    // on the implementing type (`Self`) or on unfixed trait arguments.
    let info = &ctx.env.trait_info[&provider];
    let why = if info.self_methods.iter().any(|m| m == method) {
        Some(
            "its signature mentions `Self`, which is a different type for each implementor"
                .to_owned(),
        )
    } else if !has_args && info.param_methods.iter().any(|m| m == method) {
        Some(format!(
            "its signature uses type parameters of `{provider}` that the bound leaves open — \
             name them (`any {provider}<..>`)"
        ))
    } else {
        None
    };
    if let Some(why) = why {
        discard_args(ctx, args);
        return ctx.error_expr(
            span,
            format!(
                "cannot call `{method}` on `{}`: {why}; narrow the value with `is` or a type \
                 pattern first (D4)",
                ctx.ty_name(&recv_ty)
            ),
        );
    }
    let mut impls: Vec<HirTy> = Vec::new();
    for t in ctx
        .env
        .trait_impl_tys
        .get(bound_base(&bounds[0]))
        .into_iter()
        .flatten()
    {
        if !impls.contains(t) && bounds.iter().all(|b| ctx.implements(t, b)) {
            impls.push(t.clone());
        }
    }
    let Some(first) = impls.first() else {
        discard_args(ctx, args);
        return ctx.error_expr(
            span,
            format!(
                "`{}` has no implementing type in this program, so `{method}` can never be \
                 called on it",
                ctx.ty_name(&recv_ty)
            ),
        );
    };
    let Some(sig0) = ctx
        .env
        .fn_table
        .get(&format!("{}__{method}", ty_mangle(first)))
        .cloned()
    else {
        discard_args(ctx, args);
        return ctx.error_expr(
            span,
            format!("internal: no `{method}` for an `any` implementor"),
        );
    };
    // Receiver and arguments are evaluated once, into temporaries.
    let mut sig = sig0.clone();
    sig.param_tys[0] = recv_ty.clone();
    let (lowered, mut lets) = lower_args_for(ctx, &sig, method, Some(recv_h), args, span);
    let temps: Vec<(LocalId, HirTy)> = lowered
        .into_iter()
        .map(|a| {
            let l = ctx.declare(None, a.ty.clone());
            let ty = a.ty.clone();
            lets.push(HirStmt::Let { local: l, init: a });
            (l, ty)
        })
        .collect();
    let mut arms = Vec::with_capacity(impls.len());
    for t in impls {
        let Some(target) = method_target_for(&t) else {
            continue;
        };
        let Some(&fn_id) = ctx.env.method_table.get(&(target, method.to_owned())) else {
            continue;
        };
        let bind = ctx.declare(None, t.clone());
        let mut call_args = vec![hir_local(bind, &t, span)];
        call_args.extend(temps[1..].iter().map(|(l, ty)| hir_local(*l, ty, span)));
        arms.push(HirMatchArm {
            pat: HirPattern::SumVariant {
                sum_ty: recv_ty.clone(),
                variant_index: ctx.any_tag(&t),
                binder: Some(bind),
                payload_ty: Some(t),
            },
            guard: None,
            body: HirExpr {
                kind: HirExprKind::Call {
                    callee: fn_id,
                    args: call_args,
                },
                ty: sig0.ret_ty.clone(),
                span,
            },
        });
    }
    with_lets(
        lets,
        HirExpr {
            kind: HirExprKind::Match {
                scrutinee: Box::new(hir_local(temps[0].0, &recv_ty, span)),
                arms,
            },
            ty: sig0.ret_ty,
            span,
        },
    )
}

/// Spec 5.6 for methods: an inherent method without `pub` is private to
/// the module of its impl block.
pub(super) fn check_method_visible(ctx: &LowerCtx<'_>, fn_id: FunctionId, method: &str) {
    if let Some(info) = ctx.env.method_info.get(&fn_id) {
        check_method_info_visible(ctx, info, method);
    }
}

/// Generic-impl method `method` for a receiver of type `ty`, looked up
/// by the receiver's generic base (`Box__i32` → `Box`).
pub(super) fn generic_method_for<'e>(
    ctx: &LowerCtx<'e>,
    ty: &HirTy,
    method: &str,
) -> Option<&'e GenericMethod> {
    let (name, generic_args) = match ty {
        HirTy::Struct(id) => {
            let d = ctx.struct_def(*id);
            (d.name, d.generic_args)
        }
        HirTy::Enum(id) => {
            let d = ctx.enum_def(*id);
            (d.name, d.generic_args)
        }
        _ => return None,
    };
    let base = if generic_args.is_empty() {
        name
    } else {
        enum_base_name(&name).to_owned()
    };
    ctx.env.generic_methods.get(&(base, method.to_owned()))
}

pub(super) fn check_method_info_visible(ctx: &LowerCtx<'_>, info: &MethodInfo, method: &str) {
    if !ctx.is_visible(&info.module, info.vis) {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Module,
            format!(
                "method `{method}` is private to module `{}` and cannot be called from `{}` \
                 (spec 5.6 — add `pub` to expose it)",
                module_display(&info.module),
                module_display(&ctx.current_module)
            ),
        );
    }
}

/// Call through a function-pointer or closure value.
pub(super) fn call_value(
    ctx: &mut LowerCtx<'_>,
    callee_h: HirExpr,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let (arg_tys, ret, env) = match callee_h.ty.clone() {
        HirTy::Fn(a, r) => (a, *r, None),
        HirTy::Closure { args, ret, env } => (args, *ret, Some(*env)),
        HirTy::Unknown => {
            discard_args(ctx, args);
            return callee_h;
        }
        other => {
            return ctx.error_expr(
                span,
                format!("a value of type `{}` is not callable", ctx.ty_name(&other)),
            );
        }
    };
    if args.iter().any(|a| !matches!(a, CallArg::Positional(_))) {
        return ctx.error_expr(
            span,
            "named / spread arguments need a statically known callee (spec 4.1)".to_owned(),
        );
    }
    let sig = FnSig {
        id: FunctionId(u32::MAX),
        ret_ty: ret.clone(),
        param_defaults: vec![None; arg_tys.len()],
        param_tys: arg_tys.clone(),
        param_names: (0..arg_tys.len()).map(|i| format!("#{}", i + 1)).collect(),
    };
    let (lowered, lets) = lower_args_for(ctx, &sig, "the function value", None, args, span);
    let kind = match env {
        None => HirExprKind::CallIndirect {
            callee: Box::new(callee_h),
            args: lowered,
            ret_ty: ret.clone(),
        },
        Some(env_ty) => HirExprKind::CallClosure {
            closure: Box::new(callee_h),
            args: lowered,
            arg_tys,
            ret_ty: ret.clone(),
            env_ty,
        },
    };
    with_lets(
        lets,
        HirExpr {
            kind,
            ty: ret,
            span,
        },
    )
}

/// Call a generic function (or generic-impl method, with its impl
/// target `self_ty`) by monomorphizing on the argument types. Each
/// argument is lowered against its parameter type under the bindings
/// inferred so far, so `r.unwrap_or(-1)` types `-1` from `r`.
/// `receiver` fills slot 0 (method calls).
pub(super) fn call_generic(
    ctx: &mut LowerCtx<'_>,
    def: &FnDef,
    self_ty: Option<&Ty>,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    callee: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let mut subst: HashMap<String, HirTy> = HashMap::new();
    let mut lowered: Vec<HirExpr> = Vec::with_capacity(args.len() + 1);
    if let Some(r) = receiver {
        bind_from_arg(ctx, def, self_ty, 0, &r.ty, &mut subst);
        lowered.push(r);
    }
    for a in args {
        let CallArg::Positional(e) = a else {
            return ctx.error_expr(
                span,
                format!("named / spread arguments to generic `{callee}` are not supported yet"),
            );
        };
        let i = lowered.len();
        let hint = def
            .params
            .get(i)
            .and_then(|p| p.ty.as_ref())
            .map_or(HirTy::Unknown, |t| {
                // Type params not bound yet stay opaque paths — never
                // resolved as same-named types visible from `def`.
                let mut partial = subst.clone();
                for gp in &def.generics.params {
                    if let rokc_ast::GenericParam::Type { name, .. } = gp {
                        partial
                            .entry(name.clone())
                            .or_insert_with(|| HirTy::Path(vec![name.clone()]));
                    }
                }
                let mut ty = resolve_in_mono(ctx, def, &partial, None, t);
                erase_unbound_errors(&mut ty);
                let mut leftover = Vec::new();
                collect_unknown_paths(&ty, &mut leftover);
                if leftover.is_empty() {
                    ty
                } else {
                    HirTy::Unknown
                }
            });
        let h = lower_expected(ctx, e, hint);
        bind_from_arg(ctx, def, self_ty, i, &h.ty, &mut subst);
        lowered.push(h);
    }
    if lowered.len() != def.params.len() {
        return ctx.error_expr(
            span,
            format!(
                "`{callee}` takes {} argument(s) but {} were supplied",
                def.params.len(),
                lowered.len()
            ),
        );
    }
    let Some((mono_id, ret_ty)) = monomorphize(ctx, def, self_ty, &lowered, span) else {
        return poison(span);
    };
    let param_tys = ctx
        .env
        .sink
        .mono_sigs
        .borrow()
        .get(&mono_id)
        .map(|s| s.param_tys.clone())
        .unwrap_or_default();
    let lowered: Vec<HirExpr> = lowered
        .into_iter()
        .enumerate()
        .map(|(i, a)| match param_tys.get(i) {
            Some(t) => coerce(ctx, t, a, &|| format!("argument {} of `{callee}`", i + 1)),
            None => a,
        })
        .collect();
    HirExpr {
        kind: HirExprKind::Call {
            callee: mono_id,
            args: lowered,
        },
        ty: ret_ty,
        span,
    }
}

pub(super) fn lower_call(
    ctx: &mut LowerCtx<'_>,
    callee: &Expr,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let ExprKind::Path(p) = &callee.kind else {
        // `(s.f)(x)`, `make()(x)`, ...: call through the value.
        let callee_h = lower_expected(ctx, callee, HirTy::Unknown);
        return call_value(ctx, callee_h, args, span);
    };
    let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
    let display = segs.join("::");

    // A local of `fn(...)` / closure type shadows items.
    if let [name] = segs.as_slice() {
        if let Some(local) = ctx.lookup(name) {
            let callee_h = hir_local(local, &ctx.local_ty(local), callee.span);
            return call_value(ctx, callee_h, args, span);
        }
    }

    // Free function / extern / re-export, module-aware (spec 5.x).
    if let Some(full) = ctx.resolve_fn_name(&segs) {
        ctx.check_item_visible(&full, "function");
        let sig = ctx.env.fn_table[&full].clone();
        return call_sig(ctx, &sig, &full, None, args, span);
    }

    // Generic function — monomorphize on the argument types.
    if let Some(full) = ctx.resolve_in(&segs, &ctx.env.generic_fns) {
        ctx.check_item_visible(&full, "function");
        let generic_def = ctx.env.generic_fns[&full];
        return call_generic(ctx, generic_def, None, None, args, &full, span);
    }

    // `Box::get(b)` / `Box::new(v)` — generic-impl method by path.
    if let Some((method, ty_segs)) = segs.split_last() {
        let env = ctx.env;
        let gm = ctx
            .canon_type(ty_segs)
            .filter(|_| !ty_segs.is_empty())
            .and_then(|full| env.generic_methods.get(&(full, (*method).to_owned())));
        if let Some(gm) = gm {
            check_method_info_visible(ctx, &gm.info, method);
            return call_generic(ctx, &gm.def, Some(&gm.self_ty), None, args, &display, span);
        }
    }

    // `Foo(arg, ...)` — tuple-struct constructor (spec 2.7.4).
    if let Some(sid) = ctx
        .canon_type(&segs)
        .and_then(|full| ctx.lookup_struct(&full))
    {
        let def = ctx.struct_def(sid);
        let is_tuple_form = !def.fields.is_empty()
            && def
                .fields
                .iter()
                .enumerate()
                .all(|(i, f)| f.name == i.to_string());
        if !is_tuple_form {
            return ctx.error_expr(
                span,
                format!("`{display}` is not a tuple struct — use `{display} {{ field: ... }}`"),
            );
        }
        let sig = FnSig {
            id: FunctionId(u32::MAX),
            ret_ty: HirTy::Struct(sid),
            param_defaults: vec![None; def.fields.len()],
            param_tys: def.fields.iter().map(|f| f.ty.clone()).collect(),
            param_names: def.fields.iter().map(|f| f.name.clone()).collect(),
        };
        let (fields, lets) = lower_args_for(ctx, &sig, &display, None, args, span);
        return with_lets(
            lets,
            HirExpr {
                kind: HirExprKind::StructInit {
                    struct_id: sid,
                    fields,
                },
                ty: HirTy::Struct(sid),
                span,
            },
        );
    }

    // `EnumName::Variant(payload)` — tuple-form enum constructor. For a
    // generic enum without an expected type, the instantiation is
    // picked from the argument types.
    let hint = ctx.current_expected().cloned();
    let is_generic_enum_base = ctx
        .enum_path(&segs)
        .is_some_and(|(full, _)| ctx.lookup_enum(&full).is_none());
    let pre_args: Option<Vec<HirExpr>> = if is_generic_enum_base
        && !matches!(&hint, Some(HirTy::Enum(_)))
        && args.iter().all(|a| matches!(a, CallArg::Positional(_)))
    {
        Some(
            args.iter()
                .map(|a| match a {
                    CallArg::Positional(e) => lower_expected(ctx, e, HirTy::Unknown),
                    _ => unreachable!("checked positional"),
                })
                .collect(),
        )
    } else {
        None
    };
    let arg_tys: Option<Vec<HirTy>> = pre_args
        .as_ref()
        .map(|v| v.iter().map(|e| e.ty.clone()).collect());
    match resolve_enum_variant(ctx, &segs, hint.as_ref(), arg_tys.as_deref()) {
        EnumRes::Error => return poison(span),
        EnumRes::Found(enum_id, idx) => {
            let variant = ctx.enum_def(enum_id).variants[idx].clone();
            let slots = variant_arg_tys(&variant);
            if !variant.named_fields.is_empty() {
                return ctx.error_expr(
                    span,
                    format!("`{display}` has named fields — use `{display} {{ ... }}`"),
                );
            }
            let mut lets = Vec::new();
            let args_h = if let Some(pre) = pre_args {
                if pre.len() != slots.len() {
                    return ctx.error_expr(
                        span,
                        format!(
                            "`{display}` takes {} argument(s) but {} were supplied",
                            slots.len(),
                            pre.len()
                        ),
                    );
                }
                pre.into_iter()
                    .zip(&slots)
                    .enumerate()
                    .map(|(i, (a, t))| {
                        coerce(ctx, t, a, &|| format!("argument {} of `{display}`", i + 1))
                    })
                    .collect()
            } else {
                let sig = FnSig {
                    id: FunctionId(u32::MAX),
                    ret_ty: HirTy::Enum(enum_id),
                    param_defaults: vec![None; slots.len()],
                    param_tys: slots.clone(),
                    param_names: (0..slots.len()).map(|i| format!("#{}", i + 1)).collect(),
                };
                let (a, l) = lower_args_for(ctx, &sig, &display, None, args, span);
                lets = l;
                a
            };
            return with_lets(
                lets,
                HirExpr {
                    kind: HirExprKind::EnumVariantInit {
                        enum_id,
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        args: args_h,
                    },
                    ty: HirTy::Enum(enum_id),
                    span,
                },
            );
        }
        EnumRes::NotEnum => {}
    }

    // `Type::method(args)` — static call through the method table. A
    // generic base (`Stack::new()`) resolves when exactly one
    // instantiation provides the method.
    if let Some((method, ty_segs)) = segs.split_last() {
        if !ty_segs.is_empty() {
            if let Some(full) = ctx.canon_type(ty_segs) {
                let method = (*method).to_owned();
                let mut targets: Vec<MethodTarget> = Vec::new();
                if let Some(sid) = ctx.lookup_struct(&full) {
                    targets.push(MethodTarget::Struct(sid));
                } else if let Some(eid) = ctx.lookup_enum(&full) {
                    targets.push(MethodTarget::Enum(eid));
                } else {
                    targets.extend(
                        LowerCtx::instantiations(&ctx.env.struct_table, &full)
                            .into_iter()
                            .map(MethodTarget::Struct),
                    );
                    targets.extend(
                        ctx.enum_instantiations(&full)
                            .into_iter()
                            .map(MethodTarget::Enum),
                    );
                }
                let hits: Vec<(MethodTarget, FunctionId)> = targets
                    .into_iter()
                    .filter_map(|t| {
                        ctx.env
                            .method_table
                            .get(&(t.clone(), method.clone()))
                            .map(|&id| (t, id))
                    })
                    .collect();
                match hits.as_slice() {
                    [(target, fn_id)] => {
                        check_method_visible(ctx, *fn_id, &method);
                        let prefix = match target {
                            MethodTarget::Struct(sid) => format!("Struct{}", sid.0),
                            MethodTarget::Enum(eid) => format!("Enum{}", eid.0),
                            MethodTarget::Mangled(s) => s.clone(),
                        };
                        let sig = ctx.env.fn_table[&format!("{prefix}__{method}")].clone();
                        return call_sig(ctx, &sig, &display, None, args, span);
                    }
                    [] => {
                        return ctx.error_expr(
                            span,
                            format!("no associated function `{method}` on `{full}`"),
                        );
                    }
                    _ => {
                        return ctx.error_expr(
                            span,
                            format!(
                                "`{display}` is ambiguous: several instantiations of `{full}` \
                                 provide `{method}` — name the type arguments"
                            ),
                        );
                    }
                }
            }
        }
    }

    discard_args(ctx, args);
    ctx.error_expr(
        span,
        format!("cannot find function `{display}` in this scope"),
    )
}

/// Lower call arguments only for their diagnostics (the call itself
/// failed to resolve).
pub(super) fn discard_args(ctx: &mut LowerCtx<'_>, args: &[CallArg]) {
    for a in args {
        let (CallArg::Positional(e) | CallArg::Named { value: e, .. } | CallArg::Spread(e)) = a;
        lower_expected(ctx, e, HirTy::Unknown);
    }
}

pub(super) fn is_arith_op(op: &str) -> bool {
    matches!(
        op,
        "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>"
    )
}

pub(super) fn lower_infix(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    lhs: &Expr,
    rhs: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // Spec 3.2 / 3.1: `&&` and `||` short-circuit. Desugar before
    // lowering rhs so that side effects in rhs only run when needed.
    if op == "&&" || op == "||" {
        return lower_short_circuit(ctx, op, lhs, rhs, span);
    }
    // Arithmetic operands share the result's type (so `let x: i64 = 1 + 2`
    // types both literals as i64); comparison operands don't.
    let lhs_expected = if is_arith_op(op) {
        ctx.current_expected().cloned().unwrap_or(HirTy::Unknown)
    } else {
        HirTy::Unknown
    };
    let (lhs_h, rhs_h) = lower_sibling_pair(ctx, lhs, rhs, lhs_expected);
    if lhs_h.ty == HirTy::Unknown || rhs_h.ty == HirTy::Unknown {
        return poison(span);
    }
    // Spec 0.4 / 3.1: `a + b` on a user type desugars to the operator
    // trait's method (`impl Add for T`).
    if matches!(lhs_h.ty, HirTy::Struct(_) | HirTy::Enum(_)) {
        return dispatch_user_op(ctx, op, Fixity::Infix, lhs_h, Some(rhs_h), span);
    }
    if let (HirTy::Prim(lp), HirTy::Prim(rp)) = (&lhs_h.ty, &rhs_h.ty) {
        if lp == rp {
            if let Some((primop, result_ty)) = infix_for_prim(op, *lp) {
                return hir_binop(primop, lhs_h, rhs_h, result_ty, span);
            }
        }
    }
    ctx.error_expr(
        span,
        format!(
            "operator `{op}` cannot be applied to `{}` and `{}`",
            ctx.ty_name(&lhs_h.ty),
            ctx.ty_name(&rhs_h.ty)
        ),
    )
}

pub(super) fn lower_short_circuit(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    lhs: &Expr,
    rhs: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let lhs_h = lower_cond(ctx, lhs);
    let rhs_h = lower_cond(ctx, rhs);
    let mk_const_bool = |b: bool| HirExpr {
        kind: HirExprKind::Const(ConstVal::Bool(b)),
        ty: bool_ty.clone(),
        span,
    };
    let mk_block = |trailing: HirExpr| HirBlock {
        stmts: Vec::new(),
        trailing: Some(trailing),
        label: None,
    };
    //   a && b  →  if a { b } else { false }
    //   a || b  →  if a { true } else { b }
    let (then_expr, else_expr) = if op == "&&" {
        (rhs_h, mk_const_bool(false))
    } else {
        (mk_const_bool(true), rhs_h)
    };
    HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(lhs_h),
            then_block: Box::new(mk_block(then_expr)),
            else_branch: Some(Box::new(else_expr)),
        },
        ty: bool_ty,
        span,
    }
}

pub(super) fn lower_prefix(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    operand: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // `-5` / `-1.5`: a negative literal (range-checked as negative).
    if op == "-" {
        if let ExprKind::Literal(lit @ (AstLit::Int(_) | AstLit::Float(_))) = &operand.kind {
            return lower_literal(ctx, lit, true, span);
        }
    }
    let operand_h = lower_expr(ctx, operand);
    if operand_h.ty == HirTy::Unknown {
        return operand_h;
    }
    if matches!(operand_h.ty, HirTy::Struct(_) | HirTy::Enum(_)) {
        return dispatch_user_op(ctx, op, Fixity::Prefix, operand_h, None, span);
    }
    if let HirTy::Prim(p) = &operand_h.ty {
        if let Some((primop, result_ty)) = prefix_for_prim(op, *p) {
            return HirExpr {
                kind: HirExprKind::PrimUnaryOp {
                    op: primop,
                    operand: Box::new(operand_h),
                },
                ty: result_ty,
                span,
            };
        }
    }
    ctx.error_expr(
        span,
        format!(
            "operator `{op}` cannot be applied to `{}`",
            ctx.ty_name(&operand_h.ty)
        ),
    )
}

/// Dispatch an operator on a user type to its operator-trait method
/// (spec 0.4: `a + b` ≡ `Add::add(a, b)`). The method must come from a
/// trait impl (`impl Add for T`) — an inherent method that merely has
/// the right name doesn't make the type support the operator.
pub(super) fn dispatch_user_op(
    ctx: &LowerCtx<'_>,
    sym: &str,
    fixity: Fixity,
    lhs: HirExpr,
    rhs: Option<HirExpr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let ty_name = ctx.ty_name(&lhs.ty);
    let Some(entry) = ctx.env.prec.lookup(sym, fixity) else {
        return ctx.error_expr(
            span,
            format!("operator `{sym}` cannot be applied to `{ty_name}`"),
        );
    };
    let method = entry.method_name.clone();
    let op_trait = &entry.trait_name;
    // The impl must be of the library trait that registered the operator,
    // not a user trait that happens to share its name.
    // ponytail: matches `rok::<tier>::…::<trait>`; record the defining
    // module in OpEntry once user code can declare operators.
    let is_op_trait =
        |t: &str| t.starts_with("rok::") && t.rsplit("::").next() == Some(op_trait.as_str());
    let fn_id = method_target_for(&lhs.ty)
        .and_then(|t| ctx.env.method_table.get(&(t, method.clone())).copied())
        .filter(|id| {
            ctx.env
                .method_info
                .get(id)
                .and_then(|i| i.trait_name.as_deref())
                .is_some_and(is_op_trait)
        });
    let Some(fn_id) = fn_id else {
        return ctx.error_expr(
            span,
            format!(
                "operator `{sym}` cannot be applied to `{ty_name}`: it needs \
                 `impl {op_trait} for {ty_name}` (`{method}` from any other trait or an \
                 inherent `fn {method}` is not enough)"
            ),
        );
    };
    let sig = ctx.env.fn_table[&format!("{}__{method}", ty_mangle(&lhs.ty))].clone();
    let expected_arity = if rhs.is_some() { 2 } else { 1 };
    if sig.param_tys.len() != expected_arity {
        return ctx.error_expr(
            span,
            format!(
                "`{method}` for `{ty_name}` must take {expected_arity} parameter(s) to implement \
                 operator `{sym}`"
            ),
        );
    }
    let mut args = vec![lhs];
    if let Some(r) = rhs {
        let pty = sig.param_tys[1].clone();
        args.push(coerce(ctx, &pty, r, &|| {
            format!("the right operand of `{sym}`")
        }));
    }
    HirExpr {
        kind: HirExprKind::Call {
            callee: fn_id,
            args,
        },
        ty: sig.ret_ty,
        span,
    }
}

/// Map an infix operator symbol + primitive operand type to a primitive
/// op and its result type. `None` if the combination isn't valid for
/// primitives.
pub(super) fn infix_for_prim(sym: &str, prim: PrimTy) -> Option<(PrimOp, HirTy)> {
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let same_ty = HirTy::Prim(prim);
    let arith = |op: PrimOp| Some((op, same_ty.clone()));
    let cmp = |op: PrimOp| Some((op, bool_ty.clone()));
    let num = prim.is_int() || prim.is_float();
    match sym {
        "+" if num => arith(PrimOp::Add),
        "-" if num => arith(PrimOp::Sub),
        "*" if num => arith(PrimOp::Mul),
        "/" if num => arith(PrimOp::Div),
        "%" if num => arith(PrimOp::Rem),
        "&" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitAnd),
        "|" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitOr),
        "^" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitXor),
        "<<" if prim.is_int() => arith(PrimOp::Shl),
        ">>" if prim.is_int() => arith(PrimOp::Shr),
        // `str` equality would compare pointers, not contents.
        "==" | "≡" if prim != PrimTy::Str => cmp(PrimOp::Eq),
        "!=" | "≠" if prim != PrimTy::Str => cmp(PrimOp::Ne),
        "<" if num => cmp(PrimOp::Lt),
        "<=" | "≤" if num => cmp(PrimOp::Le),
        ">" if num => cmp(PrimOp::Gt),
        ">=" | "≥" if num => cmp(PrimOp::Ge),
        _ => None,
    }
}

pub(super) fn prefix_for_prim(sym: &str, prim: PrimTy) -> Option<(PrimOp, HirTy)> {
    let same_ty = HirTy::Prim(prim);
    match sym {
        "-" if prim.is_signed_int() || prim.is_float() => Some((PrimOp::Neg, same_ty)),
        "!" if matches!(prim, PrimTy::Bool) => Some((PrimOp::LogicalNot, same_ty)),
        "~" if prim.is_int() => Some((PrimOp::Not, same_ty)),
        _ => None,
    }
}

pub(super) fn lower_path(
    ctx: &mut LowerCtx<'_>,
    path: &AstPath,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
    if let [name] = segs.as_slice() {
        if let Some(local) = ctx.lookup(name) {
            return hir_local(local, &ctx.local_ty(local), span);
        }
    }
    // Module-level `const NAME: T = expr;` — inline the value at the
    // use site, typed by the const's declaration.
    if let Some(full) = ctx.resolve_in(&segs, &ctx.env.consts) {
        ctx.check_item_visible(&full, "const");
        let (ty, value) = ctx.env.consts[&full].clone();
        let module = module_of(&full);
        let sc = Scope {
            names: &ctx.env.names,
            module: &module,
        };
        let ty = resolve_ty_with_structs(&ty, &ctx.env.struct_table, &ctx.env.enum_table, sc);
        let v = lower_expected(ctx, &value, ty.clone());
        return coerce(ctx, &ty, v, &|| format!("const `{full}`"));
    }
    // Module-level `static` — a load through the global address.
    if let Some(full) = ctx.resolve_in(&segs, &ctx.env.statics) {
        ctx.check_item_visible(&full, "static");
        let ty = ctx.env.statics[&full].clone();
        return HirExpr {
            kind: HirExprKind::StaticRef(full),
            ty,
            span,
        };
    }
    // A function used as a value → function pointer.
    if let Some(full) = ctx.resolve_fn_name(&segs) {
        ctx.check_item_visible(&full, "function");
        let sig = ctx.env.fn_table[&full].clone();
        return HirExpr {
            kind: HirExprKind::FnRef(sig.id),
            ty: HirTy::Fn(sig.param_tys, Box::new(sig.ret_ty)),
            span,
        };
    }
    if ctx.resolve_in(&segs, &ctx.env.generic_fns).is_some() {
        return ctx.error_expr(
            span,
            format!(
                "generic function `{}` can only be called, not used as a value",
                segs.join("::")
            ),
        );
    }
    // `EnumName::Variant` (unit form). Tuple variants come through
    // `lower_call` because the parser wraps them in a Call expression.
    let hint = ctx.current_expected().cloned();
    match resolve_enum_variant(ctx, &segs, hint.as_ref(), None) {
        EnumRes::Found(enum_id, idx) => {
            let variant = &ctx.enum_def(enum_id).variants[idx];
            if variant.payload_ty.is_some() {
                return ctx.error_expr(
                    span,
                    format!(
                        "enum variant `{}` takes arguments: `{}(...)`",
                        segs.join("::"),
                        segs.join("::")
                    ),
                );
            }
            return HirExpr {
                kind: HirExprKind::EnumVariantInit {
                    enum_id,
                    variant_index: u32::try_from(idx).expect("variant overflow"),
                    args: Vec::new(),
                },
                ty: HirTy::Enum(enum_id),
                span,
            };
        }
        EnumRes::Error => return poison(span),
        EnumRes::NotEnum => {}
    }
    ctx.error_expr(
        span,
        format!("cannot find value `{}` in this scope", segs.join("::")),
    )
}

/// Integer type an unsuffixed literal takes from its expected slot.
pub(super) fn expected_prim(ctx: &LowerCtx<'_>, want: fn(PrimTy) -> bool) -> Option<PrimTy> {
    match ctx.current_expected()? {
        HirTy::Prim(p) if want(*p) => Some(*p),
        // `let x: i64 | none = 5` — the sum's single matching variant.
        HirTy::Sum(vs) => {
            let mut hits = vs.iter().filter_map(|v| match v {
                HirTy::Prim(p) if want(*p) => Some(*p),
                _ => None,
            });
            let first = hits.next()?;
            hits.next().is_none().then_some(first)
        }
        _ => None,
    }
}

/// Lower a literal (`negate` = it sits under a unary minus). Unsuffixed
/// numbers take the expected type (else `i32` / `f64`); integers are
/// range-checked against their final type.
pub(super) fn lower_literal(
    ctx: &LowerCtx<'_>,
    lit: &AstLit,
    negate: bool,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let konst = |kind: ConstVal, ty: HirTy| HirExpr {
        kind: HirExprKind::Const(kind),
        ty,
        span,
    };
    match lit {
        AstLit::Int(text) => {
            let Some((value, suffix_ty)) = parse_int_literal(text) else {
                return ctx.error_expr(span, format!("malformed integer literal `{text}`"));
            };
            let ty = if has_int_suffix(text) {
                suffix_ty
            } else {
                expected_prim(ctx, |p| {
                    p.is_int() && !matches!(p, PrimTy::CChar | PrimTy::Char)
                })
                .unwrap_or(PrimTy::I32)
            };
            let value = if negate { -value } else { value };
            if negate && !ty.is_signed_int() {
                return ctx.error_expr(
                    span,
                    format!(
                        "cannot negate unsigned literal `{text}` of type `{}`",
                        ty.name()
                    ),
                );
            }
            if !int_fits(value, ty) {
                let shown = if negate {
                    format!("-{text}")
                } else {
                    text.clone()
                };
                return ctx.error_expr(
                    span,
                    format!("integer literal `{shown}` out of range for `{}`", ty.name()),
                );
            }
            konst(ConstVal::Int { value, ty }, HirTy::Prim(ty))
        }
        AstLit::Float(text) => {
            let suffixed = text.ends_with("f32") || text.ends_with("f64");
            let ty = if suffixed {
                parse_float_literal(text).map_or(PrimTy::F64, |(_, t)| t)
            } else {
                expected_prim(ctx, PrimTy::is_float).unwrap_or(PrimTy::F64)
            };
            let digits = text.trim_end_matches("f32").trim_end_matches("f64");
            let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
            let Ok(v) = cleaned.parse::<f64>() else {
                return ctx.error_expr(span, format!("malformed float literal `{text}`"));
            };
            let v = if negate { -v } else { v };
            let bits = if ty == PrimTy::F32 {
                #[allow(clippy::cast_possible_truncation)]
                u64::from((v as f32).to_bits())
            } else {
                v.to_bits()
            };
            konst(ConstVal::Float { bits, ty }, HirTy::Prim(ty))
        }
        AstLit::Bool(b) => konst(ConstVal::Bool(*b), HirTy::Prim(PrimTy::Bool)),
        AstLit::Str(s) => konst(
            ConstVal::Str(decode_str_escapes(s)),
            HirTy::Prim(PrimTy::Str),
        ),
        AstLit::RawStr(s) => konst(ConstVal::Str(s.clone()), HirTy::Prim(PrimTy::Str)),
        AstLit::None => konst(ConstVal::None, none_ty()),
        AstLit::Char(s) => match parse_char_literal(s) {
            // An ASCII `'a'` flowing into a `c_char` slot takes that type.
            Some(c) if c < 0x80 && expected_prim(ctx, |p| p == PrimTy::CChar).is_some() => {
                konst(ConstVal::Char(c), HirTy::Prim(PrimTy::CChar))
            }
            Some(c) => konst(ConstVal::Char(c), HirTy::Prim(PrimTy::Char)),
            None => ctx.error_expr(span, format!("unsupported character literal `'{s}'`")),
        },
        AstLit::CChar(s) => match parse_char_literal(s) {
            Some(c) => konst(ConstVal::Char(c), HirTy::Prim(PrimTy::CChar)),
            None => ctx.error_expr(span, format!("unsupported character literal `c'{s}'`")),
        },
        AstLit::FStr(_) => ctx.error_expr(
            span,
            "f-string literals are not supported yet (stage-1 limitation)".to_owned(),
        ),
    }
}

// `'A'` / `c'A'` payload is the body as written (without quotes);
// decode it with the shared escape table (spec 1.8).
pub(super) fn parse_char_literal(text: &str) -> Option<u32> {
    let decoded = rokc_ast::escape::unescape(text, rokc_ast::escape::EscapeMode::CChar).ok()?;
    let mut chars = decoded.chars();
    let c = chars.next()?;
    chars.next().is_none().then_some(c as u32)
}

/// Parse an integer literal. Bare (unsuffixed) integer literals fall
/// back to `i32` — the most common integer type in rok programs.
pub(super) fn parse_int_literal(text: &str) -> Option<(i128, PrimTy)> {
    const SUFFIXES: &[(&str, PrimTy)] = &[
        ("isize", PrimTy::Isize),
        ("usize", PrimTy::Usize),
        ("i64", PrimTy::I64),
        ("u64", PrimTy::U64),
        ("i32", PrimTy::I32),
        ("u32", PrimTy::U32),
        ("i16", PrimTy::I16),
        ("u16", PrimTy::U16),
        ("i8", PrimTy::I8),
        ("u8", PrimTy::U8),
    ];

    let (digits, ty) = SUFFIXES
        .iter()
        .find_map(|(suf, ty)| text.strip_suffix(suf).map(|d| (d, *ty)))
        .unwrap_or((text, PrimTy::I32));

    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    let (radix, body) = if let Some(rest) = cleaned
        .strip_prefix("0x")
        .or_else(|| cleaned.strip_prefix("0X"))
    {
        (16u32, rest.to_owned())
    } else if let Some(rest) = cleaned
        .strip_prefix("0b")
        .or_else(|| cleaned.strip_prefix("0B"))
    {
        (2u32, rest.to_owned())
    } else if let Some(rest) = cleaned
        .strip_prefix("0o")
        .or_else(|| cleaned.strip_prefix("0O"))
    {
        (8u32, rest.to_owned())
    } else {
        (10u32, cleaned)
    };

    let value = i128::from_str_radix(&body, radix).ok()?;
    Some((value, ty))
}

pub(super) fn parse_float_literal(text: &str) -> Option<(u64, PrimTy)> {
    const SUFFIXES: &[(&str, PrimTy)] = &[("f32", PrimTy::F32), ("f64", PrimTy::F64)];
    let (digits, ty) = SUFFIXES
        .iter()
        .find_map(|(suf, ty)| text.strip_suffix(suf).map(|d| (d, *ty)))
        .unwrap_or((text, PrimTy::F64));

    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    let bits = match ty {
        PrimTy::F32 => u64::from(cleaned.parse::<f32>().ok()?.to_bits()),
        _ => cleaned.parse::<f64>().ok()?.to_bits(),
    };
    Some((bits, ty))
}

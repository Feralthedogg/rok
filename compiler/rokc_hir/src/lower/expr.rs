//! Blocks, statements and expressions.

#[allow(clippy::wildcard_imports)]
use super::*;

pub(super) fn lower_block(ctx: &mut LowerCtx<'_>, block: &Block) -> HirBlock {
    ctx.push_scope();
    let mut stmts = Vec::with_capacity(block.stmts.len());
    for (i, s) in block.stmts.iter().enumerate() {
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
            StmtKind::LetPattern { pat, ty, init } => {
                let value = match ty.as_ref().map(|t| ctx.resolve_ast_ty(t)) {
                    Some(t) => {
                        let v = lower_expected(ctx, init, t.clone());
                        coerce(ctx, &t, v, &|| "the destructured value".to_owned())
                    }
                    None => lower_expected(ctx, init, HirTy::Unknown),
                };
                super::desugar::bind_irrefutable(ctx, pat, value, &mut stmts);
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
            StmtKind::Let {
                name,
                ty: None,
                init,
            } => {
                let rest = &block.stmts[i + 1..];
                stmts.extend(super::infer::lower_let(ctx, s, name, init, rest, block));
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
        stmts.push(ctx.declare_var(bind_name, field_ty, read, span));
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
        stmts.push(ctx.declare_var(name, elem_ty, init, span));
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
        let init = HirExpr {
            ty: rest_ty.clone(),
            span,
            kind: HirExprKind::Tuple { fields: sub },
        };
        stmts.push(ctx.declare_var(rest_name, rest_ty, init, span));
    }
}

pub(super) fn lower_stmt(ctx: &mut LowerCtx<'_>, stmt: &Stmt) -> Option<HirStmt> {
    // Diagnostics raised while lowering default to this location.
    let outer = rokc_diagnostic::set_current_span(stmt.span);
    let s = lower_stmt_inner(ctx, stmt);
    rokc_diagnostic::set_current_span(outer);
    s
}

fn lower_stmt_inner(ctx: &mut LowerCtx<'_>, stmt: &Stmt) -> Option<HirStmt> {
    match &stmt.kind {
        StmtKind::Let { name, ty, init } => {
            // Same-scope redeclaration is an error (typo guard, no
            // shadowing); an inner scope makes a fresh binding.
            if name != "_" && ctx.lookup_in_current_scope(name).is_some() {
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
            Some(ctx.declare_var(name, declared_ty, init, stmt.span))
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
        StmtKind::Expr(expr) => Some(HirStmt::Expr(lower_expected(ctx, expr, HirTy::Unit))),
        // A block-like statement without `;` before more statements
        // (`if c { 1 } else { 2 }  next();`) must not produce a value.
        StmtKind::Trailing(expr) => {
            let h = lower_expected(ctx, expr, HirTy::Unit);
            if let Some(t) = arm_value_ty(&h) {
                let old = rokc_diagnostic::set_current_span(stmt.span);
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "this block-like statement leaves a value of type `{}` without `;`: a \
                         statement must be `()` (add `;` to discard it, or make it the \
                         block's last expression)",
                        ctx.ty_name(&t)
                    ),
                );
                rokc_diagnostic::set_current_span(old);
            }
            Some(HirStmt::Expr(h))
        }
        StmtKind::Item(rokc_ast::Item::Use(u)) => {
            // Function-local `use`: visible in the current scope only.
            let mut entries = Vec::new();
            crate::uses::flatten_tree_for_local(&u.tree, &ctx.current_module, &mut entries);
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
        StmtKind::Assign(target, value) => {
            let a = lower_assign(ctx, target, value, stmt.span);
            write_through(ctx, a, stmt.span)
        }
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
            let a = lower_assign(ctx, target, &combined, stmt.span);
            write_through(ctx, a, stmt.span)
        }
        StmtKind::LetTuple { .. } | StmtKind::LetStruct { .. } | StmtKind::LetPattern { .. } => {
            unreachable!("destructuring lets are expanded by lower_block")
        }
        StmtKind::Break { label, value } => {
            check_jump_target(ctx, "break", label.as_deref(), false);
            let depth = jump_index(ctx, label.as_deref(), false);
            let value = if let Some(e) = value {
                Some(lower_break_value(ctx, depth, e))
            } else {
                match ctx.break_tys.get(&depth).cloned() {
                    None => {
                        ctx.break_tys.insert(depth, (HirTy::Unit, true));
                    }
                    Some((t, _)) if t != HirTy::Unit => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "`break` without a value, but this loop's `break` values are \
                             `{}` (spec 3.13.1)",
                            ctx.ty_name(&t)
                        ),
                    ),
                    Some(_) => {}
                }
                None
            };
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

/// A method call's receiver. One whose generic parameter nothing fixed
/// (`B::new().with(1)`) is retried with the call's expected type when
/// that makes it exactly the expected type — a chain of methods that
/// return their receiver's type (builders).
fn lower_receiver(ctx: &mut LowerCtx<'_>, receiver: &Expr) -> HirExpr {
    let mark = ctx.probe_mark();
    let recv = lower_expected(ctx, receiver, HirTy::Unknown);
    if ctx.env.sink.uninferred.get() == mark.uninferred {
        return recv;
    }
    let Some(expected) = ctx
        .current_expected()
        .filter(|t| !matches!(t, HirTy::Unknown | HirTy::Unit | HirTy::Any))
        .cloned()
    else {
        return recv;
    };
    let retry = ctx.probe_mark();
    let mut probe = ctx.clone();
    let fits = lower_expected(&mut probe, receiver, expected.clone()).ty == expected
        && ctx.env.sink.diagnostics.borrow().len() == retry.diagnostics;
    ctx.rollback(&retry);
    if !fits {
        return recv;
    }
    ctx.rollback(&mark);
    lower_expected(ctx, receiver, expected)
}

/// An un-annotated `let` takes its initializer's static type, so
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
        // Spec 4.2.7: `_ = e;` evaluates `e` and discards it.
        ExprKind::Path(p) if p.segments.len() == 1 && p.segments[0].name == "_" => {
            let v = lower_expected(ctx, value, HirTy::Unknown);
            Some(HirStmt::Expr(v))
        }
        ExprKind::Path(p) if p.segments.len() == 1 => {
            let name = &p.segments[0].name;
            if let Some(local) = ctx.lookup(name) {
                if ctx.value_captured.contains(&local) {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "`{name}` is value-captured; to mutate the outer variable, add \
                             `[ref {name}]` to the closure's capture list (spec 4.6.4)"
                        ),
                    );
                }
                let slot_ty = ctx.var_ty(local);
                let v = lower_expected(ctx, value, slot_ty.clone());
                let value = coerce(ctx, &slot_ty, v, &|| format!("assignment to `{name}`"));
                return Some(ctx.store_local(local, value));
            }
            let segs = [name.as_str()];
            if let Some(full) = ctx.resolve_in(&segs, &ctx.env.statics) {
                ctx.check_item_visible(&full, "static");
                if !ctx.env.mut_statics.contains(&full) {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "cannot assign to static `{name}`: statics are immutable \
                             (spec 5.3); only an `extern` `static mut` can be written"
                        ),
                    );
                }
                let ty = ctx.env.statics[&full].clone();
                let v = lower_expected(ctx, value, ty.clone());
                let value = coerce(ctx, &ty, v, &|| format!("assignment to `{name}`"));
                return Some(HirStmt::StaticAssign { name: full, value });
            }
            // Only `let` declares; assigning an undeclared name is an error.
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
            // A struct / enum stores through `IndexSet::index_set`.
            if let HirTy::GcBuf(elem) = arr_h.ty.clone() {
                let set = buf_access(ctx, arr_h, *elem, idx_expr, Some(value), target.span);
                return Some(HirStmt::Expr(set));
            }
            if matches!(arr_h.ty, HirTy::Struct(_) | HirTy::Enum(_)) {
                let rest = [CallArg::Positional(value.clone())];
                let span = target.span;
                return Some(HirStmt::Expr(index_call(
                    ctx,
                    arr_h,
                    "index_set",
                    idx_expr,
                    &rest,
                    span,
                )));
            }
            let idx_h = match arr_h.ty {
                HirTy::Array(_, n) => array_position(ctx, idx_expr, n),
                _ => lower_expected(ctx, idx_expr, HirTy::Unknown),
            };
            let elem = match (&arr_h.kind, &arr_h.ty) {
                (HirExprKind::Local(l), HirTy::Array(elem, _)) => Some((*l, (**elem).clone())),
                (_, HirTy::Unknown) => return None,
                _ => None,
            };
            // `s.arr[i] = v` / `xs[j][i] = v` on a value array that isn't
            // a local: copy the array, store into the copy, write it back.
            if elem.is_none()
                && matches!(arr_h.ty, HirTy::Array(..))
                && matches!(arr_expr.kind, ExprKind::Field(..) | ExprKind::Index(..))
            {
                return Some(rewrite_index_store(
                    ctx,
                    idx_expr,
                    |copy, i| {
                        let store = Expr {
                            kind: ExprKind::Index(Box::new(copy.clone()), Box::new(i.clone())),
                            span: target.span,
                        };
                        vec![
                            let_stmt(copy, (**arr_expr).clone()),
                            assign_stmt(store, value.clone()),
                            assign_stmt((**arr_expr).clone(), copy.clone()),
                        ]
                    },
                    target.span,
                ));
            }
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
        // A tuple struct's field is `s.0`.
        ExprKind::Field(_, _) | ExprKind::TupleField(_, _) => {
            // `struct_id` is `None` for a plain tuple's element (`t.0 = x`).
            struct Step {
                ty: HirTy,
                struct_id: Option<StructId>,
                field_index: u32,
            }
            let mut chain: Vec<String> = Vec::new();
            let mut cur: &Expr = target;
            loop {
                match &cur.kind {
                    ExprKind::Field(inner, name) => {
                        chain.push(name.clone());
                        cur = inner;
                    }
                    ExprKind::TupleField(inner, i) => {
                        chain.push(i.to_string());
                        cur = inner;
                    }
                    _ => break,
                }
            }
            chain.reverse();
            // `xs[i].f = v`: the element is a value, so read it, update
            // the copy and store it back (`xs[i] = copy`).
            if let ExprKind::Index(arr, idx) = &cur.kind {
                let field_target = |elem: &Expr| {
                    chain.iter().fold(elem.clone(), |acc, name| Expr {
                        kind: ExprKind::Field(Box::new(acc), name.clone()),
                        span: target.span,
                    })
                };
                return Some(rewrite_index_store(
                    ctx,
                    idx,
                    |elem, i| {
                        let at = Expr {
                            kind: ExprKind::Index(arr.clone(), Box::new(i.clone())),
                            span: cur.span,
                        };
                        vec![
                            let_stmt(elem, at.clone()),
                            assign_stmt(field_target(elem), value.clone()),
                            assign_stmt(at, elem.clone()),
                        ]
                    },
                    target.span,
                ));
            }
            let root_h = lower_expected(ctx, cur, HirTy::Unknown);
            if root_h.ty == HirTy::Unknown {
                return None;
            }
            if super::mono::place_root(&root_h).is_none() {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    "field assignment needs a local variable at the root of the target \
                     (`v.f = x`)"
                        .to_owned(),
                );
                return None;
            }
            let root_place = root_h.clone();
            let mut steps: Vec<Step> = Vec::new();
            let mut step_ty = root_h.ty.clone();
            // Spec 2.5.2: writing a union field (safe) rebuilds the union
            // from that field; it must be the last step of the target.
            let mut union_value: Option<HirExpr> = None;
            for (ci, name) in chain.iter().enumerate() {
                if let HirTy::Tuple(parts) = &step_ty {
                    if let Some(i) = name.parse::<usize>().ok().filter(|i| *i < parts.len()) {
                        let next = parts[i].clone();
                        steps.push(Step {
                            ty: step_ty.clone(),
                            struct_id: None,
                            field_index: u32::try_from(i).expect("tuple field overflow"),
                        });
                        step_ty = next;
                        continue;
                    }
                }
                let HirTy::Struct(sid) = step_ty.clone() else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("no field `{name}` on type `{}`", ctx.ty_name(&step_ty)),
                    );
                    return None;
                };
                let def = ctx.struct_def(sid);
                if let Some(uk) = &def.union_kind {
                    let Some(fty) = uk
                        .aliases
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, t)| t.clone())
                    else {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!("union `{}` has no field `{name}` (spec 2.5)", def.name),
                        );
                        return None;
                    };
                    if ci + 1 != chain.len() {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "cannot assign through union field `{name}`: read it (in \
                                 `unsafe`), change the copy, and write the field back"
                            ),
                        );
                        return None;
                    }
                    ctx.check_field_visible(sid, name);
                    let v = lower_expected(ctx, value, fty.clone());
                    let v = coerce(ctx, &fty, v, &|| format!("union field `{name}`"));
                    let storage_ty = def.fields[0].ty.clone();
                    union_value = Some(HirExpr {
                        kind: HirExprKind::StructInit {
                            struct_id: sid,
                            fields: vec![HirExpr {
                                kind: HirExprKind::UnionWrite {
                                    struct_id: sid,
                                    from_ty: v.ty.clone(),
                                    storage_ty: storage_ty.clone(),
                                    value: Box::new(v),
                                },
                                ty: storage_ty,
                                span,
                            }],
                        },
                        ty: HirTy::Struct(sid),
                        span,
                    });
                    break;
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
                    struct_id: Some(sid),
                    field_index: u32::try_from(idx).expect("field index overflow"),
                });
                step_ty = def.fields[idx].ty.clone();
            }
            let last_name = chain.last().cloned().unwrap_or_default();
            let mut acc = match union_value {
                // `u.f = x` with `u` a local: replace the whole union.
                Some(u) if steps.is_empty() => {
                    return super::mono::assign_place(ctx, &root_place, u);
                }
                Some(u) => u,
                None => {
                    let v = lower_expected(ctx, value, step_ty.clone());
                    coerce(ctx, &step_ty, v, &|| format!("field `{last_name}`"))
                }
            };
            // Materialize parent values via field reads so each
            // WithField has a concrete target.
            let mut targets: Vec<HirExpr> = Vec::new();
            let read = |ctx: &LowerCtx<'_>, from: &HirExpr, step: &Step| {
                let (kind, ty) = match (step.struct_id, &step.ty) {
                    (Some(sid), _) => {
                        let ty = ctx.struct_def(sid).fields[step.field_index as usize]
                            .ty
                            .clone();
                        let kind = HirExprKind::FieldRead {
                            target: Box::new(from.clone()),
                            struct_id: sid,
                            field_index: step.field_index,
                            field_ty: ty.clone(),
                        };
                        (kind, ty)
                    }
                    (None, HirTy::Tuple(parts)) => {
                        let ty = parts[step.field_index as usize].clone();
                        let kind = HirExprKind::TupleField {
                            target: Box::new(from.clone()),
                            index: step.field_index,
                            field_ty: ty.clone(),
                        };
                        (kind, ty)
                    }
                    (None, _) => unreachable!("a tuple step is on a tuple"),
                };
                HirExpr {
                    kind,
                    ty,
                    span: target.span,
                }
            };
            let mut walk = root_h;
            for step in &steps[..steps.len() - 1] {
                let next = read(ctx, &walk, step);
                targets.push(walk);
                walk = next;
            }
            targets.push(walk);
            for (i, step) in steps.iter().enumerate().rev() {
                let kind = match (step.struct_id, &step.ty) {
                    (Some(sid), _) => HirExprKind::WithField {
                        target: Box::new(targets[i].clone()),
                        struct_id: sid,
                        field_index: step.field_index,
                        value: Box::new(acc),
                    },
                    // A tuple is rebuilt with the one element replaced.
                    (None, HirTy::Tuple(parts)) => {
                        let mut acc = Some(acc);
                        let fields = (0..parts.len())
                            .map(|j| {
                                let j = u32::try_from(j).expect("tuple field overflow");
                                if j == step.field_index {
                                    acc.take().expect("replaced once")
                                } else {
                                    read(
                                        ctx,
                                        &targets[i],
                                        &Step {
                                            ty: step.ty.clone(),
                                            struct_id: None,
                                            field_index: j,
                                        },
                                    )
                                }
                            })
                            .collect();
                        HirExprKind::Tuple { fields }
                    }
                    (None, _) => unreachable!("a tuple step is on a tuple"),
                };
                acc = HirExpr {
                    ty: step.ty.clone(),
                    span: target.span,
                    kind,
                };
            }
            super::mono::assign_place(ctx, &root_place, acc)
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

fn tmp_path(what: &str, span: rokc_diagnostic::Span) -> Expr {
    static N: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    Expr {
        kind: ExprKind::Path(rokc_ast::Path {
            segments: vec![rokc_ast::PathSegment {
                name: format!("#{what}{n}"),
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    }
}

fn path_name(e: &Expr) -> String {
    let ExprKind::Path(p) = &e.kind else {
        unreachable!("temp is a path")
    };
    p.segments[0].name.clone()
}

fn let_stmt(name: &Expr, init: Expr) -> Stmt {
    Stmt {
        span: init.span,
        kind: StmtKind::Let {
            name: path_name(name),
            ty: None,
            init,
        },
    }
}

const fn assign_stmt(target: Expr, value: Expr) -> Stmt {
    Stmt {
        span: target.span,
        kind: StmtKind::Assign(target, value),
    }
}

/// `{ let #i = idx; <body(#tmp, #i)> }` — a store through a value
/// element that has no local to write in place: `body` copies it into
/// `#tmp`, updates the copy and writes it back. The index is evaluated
/// once.
fn rewrite_index_store(
    ctx: &mut LowerCtx<'_>,
    idx: &Expr,
    body: impl FnOnce(&Expr, &Expr) -> Vec<Stmt>,
    span: rokc_diagnostic::Span,
) -> HirStmt {
    let tmp = tmp_path("tmp", span);
    // A literal / name index is read as is (and keeps its expected
    // `usize` type); anything else goes through a temp.
    let mut stmts = Vec::new();
    let i = if matches!(idx.kind, ExprKind::Literal(_) | ExprKind::Path(_)) {
        idx.clone()
    } else {
        let i = tmp_path("idx", span);
        stmts.push(let_stmt(&i, idx.clone()));
        i
    };
    stmts.extend(body(&tmp, &i));
    let block = Expr {
        kind: ExprKind::Block(Block {
            stmts,
            trailing: None,
            span,
            label: None,
        }),
        span,
    };
    HirStmt::Expr(lower_expr(ctx, &block))
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
    let outer = rokc_diagnostic::set_current_span(expr.span);
    let e = lower_expr_inner(ctx, expr);
    rokc_diagnostic::set_current_span(outer);
    if e.ty != HirTy::Never || hir_expr_diverges(&e) {
        return e;
    }
    // A call of a `-> !` function: emit it as a never-returning call
    // (MIR: call + `unreachable`) typed as the slot it sits in.
    let span = e.span;
    let ty = match ctx.current_expected() {
        Some(t) if *t != HirTy::Unknown => t.clone(),
        _ => HirTy::Never,
    };
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: vec![HirStmt::Panic(HirExpr {
                ty: HirTy::Unit,
                ..e
            })],
            trailing: None,
            label: None,
        })),
        ty,
        span,
    }
}

/// `operand as ty` (spec 2.10.5): numeric / bool / char casts.
fn lower_cast(
    ctx: &mut LowerCtx<'_>,
    operand: &Expr,
    ty: &Ty,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let mark = ctx.probe_mark();
    let operand_h = lower_expected(ctx, operand, HirTy::Unknown);
    // In a monomorphized body `as T` names the concrete type.
    let to_ty = ctx.resolve_ast_ty(ty);
    let from_ty = operand_h.ty.clone();
    // `int` / `float`: a conversion call (stdlib 2.11.1).
    if super::bignum::big_of(ctx, &from_ty).is_some()
        || super::bignum::big_of(ctx, &to_ty).is_some()
    {
        ctx.rollback(&mark);
        return super::bignum::cast(ctx, operand, &from_ty, &to_ty, ty, span);
    }
    let castable = |t: &HirTy| matches!(t, HirTy::Prim(p) if p.is_int() || p.is_float() || matches!(p, PrimTy::Bool | PrimTy::CChar | PrimTy::Char));
    if !(from_ty == to_ty
        || matches!(from_ty, HirTy::Unknown)
        || matches!(to_ty, HirTy::Unknown)
        || (castable(&from_ty) && castable(&to_ty)))
    {
        return ctx.error_expr(
            span,
            format!(
                "cannot cast `{}` as `{}` (only numeric / bool / char casts){}",
                ctx.ty_name(&from_ty),
                ctx.ty_name(&to_ty),
                optional_cast_hint(ty)
            ),
        );
    }
    // Like Rust: only `u8` (always a scalar value) casts to
    // `char`; a wider value may be a surrogate or past U+10FFFF.
    if to_ty == HirTy::Prim(PrimTy::Char)
        && !matches!(
            from_ty,
            HirTy::Unknown | HirTy::Prim(PrimTy::U8 | PrimTy::Char)
        )
    {
        return ctx.error_expr(
            span,
            format!(
                "only `u8` can be cast as `char`, not `{}`; use `char::from_u32(n)` \
                 (`char | none`) for a wider value",
                ctx.ty_name(&from_ty)
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

/// `x as T?` casts to the type `T?` (spec 2.6.5); say so when the cast
/// fails, since `?` propagation was likely meant.
fn optional_cast_hint(ty: &Ty) -> &'static str {
    let optional = matches!(&ty.kind, AstTyKind::Sum(ps)
        if matches!(ps.as_slice(), [n, t] if n.nest_inner().is_some()
            && matches!(t.kind, AstTyKind::None)));
    if optional {
        "; the trailing `?` is part of the type `T?` — to propagate, write `(x as T)?`"
    } else {
        ""
    }
}

fn lower_expr_inner(ctx: &mut LowerCtx<'_>, expr: &Expr) -> HirExpr {
    let span = expr.span;
    let unsupported = |ctx: &LowerCtx<'_>, what: &str| {
        ctx.error_expr(
            span,
            format!("{what} is not supported yet (stage-1 limitation)"),
        )
    };
    match &expr.kind {
        ExprKind::Literal(lit) => super::bignum::literal(ctx, lit, false, span)
            .unwrap_or_else(|| lower_literal(ctx, lit, false, span)),
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
        ExprKind::Unsafe(b) => {
            ctx.unsafe_depth += 1;
            let block = Expr {
                kind: ExprKind::Block(b.clone()),
                span,
            };
            let e = lower_expr_inner(ctx, &block);
            ctx.unsafe_depth -= 1;
            e
        }
        ExprKind::Block(b) => {
            let labelled = b.label.is_some();
            let idx = ctx.breakables.len();
            if labelled {
                open_break_target(ctx, idx);
                ctx.breakables.push((b.label.clone(), false));
            }
            let block = lower_block(ctx, b);
            // Spec 3.9.10: a labelled block's value can come from a
            // `break 'label value` inside its body, not just from a
            // trailing expression.
            let break_ty = if labelled {
                ctx.breakables.pop();
                ctx.break_tys.remove(&idx).map(|(t, _)| t)
            } else {
                None
            };
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
        ExprKind::OpPostfix { op, operand } => {
            let operand_h = lower_expr(ctx, operand);
            if operand_h.ty == HirTy::Unknown {
                return operand_h;
            }
            dispatch_user_op(ctx, op, Fixity::Postfix, operand_h, None, span)
        }
        ExprKind::Call {
            callee,
            args,
            trailing_closure,
        } => {
            // Spec 4.8: trailing closure becomes the last arg.
            let all_args = with_trailing_closure(args, trailing_closure.as_deref());
            if let ExprKind::Path(p) = &callee.kind {
                check_direct_drop_path(ctx, p);
            }
            let call = match &callee.kind {
                ExprKind::Path(p) if p.segments[0].name == rokc_ast::QPATH_MARK => {
                    qpath_call(ctx, &p.segments, &all_args, span)
                }
                _ => lower_call(ctx, callee, &all_args, span),
            };
            unpack_call(ctx, call)
        }
        ExprKind::MethodCall {
            receiver,
            method,
            args,
            trailing_closure,
            type_args,
        } => {
            let all_args = with_trailing_closure(args, trailing_closure.as_deref());
            let recv_h = literal_conv_receiver(ctx, receiver, method)
                .unwrap_or_else(|| lower_receiver(ctx, receiver));
            ctx.method_type_args.clone_from(type_args);
            let method = match drop_method(ctx, &recv_h.ty, method, span) {
                Ok(m) => m,
                Err(e) => return e,
            };
            if method == rokc_ast::USING_DROP_METHOD {
                let stmts = drop_glue(ctx, recv_h, span, 0);
                return HirExpr {
                    kind: HirExprKind::Block(Box::new(HirBlock {
                        stmts,
                        trailing: None,
                        label: None,
                    })),
                    ty: HirTy::Unit,
                    span,
                };
            }
            let call = method_call_on(ctx, recv_h, method, &all_args, span);
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
            ctx.push_expected(HirTy::Unit);
            let body_h = lower_narrowed_block(ctx, cond, body);
            ctx.pop_expected();
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
            is_await,
        } => lower_for(ctx, label.as_ref(), pat, iter, body, *is_await, span),
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
                        Some(f) if f.name == i.to_string() => {
                            ctx.check_field_visible(sid, &f.name);
                            HirExpr {
                                ty: f.ty.clone(),
                                span,
                                kind: HirExprKind::FieldRead {
                                    target: Box::new(target_h),
                                    struct_id: sid,
                                    field_index: *index,
                                    field_ty: f.ty.clone(),
                                },
                            }
                        }
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
        ExprKind::List(items) => lower_list_lit(ctx, items, span),
        ExprKind::ArrayRepeat { value, len } => lower_array_repeat(ctx, value, len, span),
        // `xs[a..b]` / `xs[..]` (stdlib 2.9.7 spelling) is `xs[a:b]` / `xs[:]`.
        ExprKind::Index(arr, idx)
            if matches!(
                &idx.kind,
                ExprKind::Range {
                    inclusive: false,
                    ..
                }
            ) =>
        {
            let ExprKind::Range { start, end, .. } = &idx.kind else {
                unreachable!()
            };
            lower_slice(ctx, arr, start.as_deref(), end.as_deref(), None, span)
        }
        ExprKind::Index(arr, idx) => {
            let arr_h = lower_expected(ctx, arr, HirTy::Unknown);
            // A struct / enum indexes through `Index::index` (spec 3.6).
            if matches!(arr_h.ty, HirTy::Struct(_) | HirTy::Enum(_)) {
                return index_call(ctx, arr_h, "index", idx, &[], span);
            }
            // `GcBuf<T>`'s `Index` is the unchecked `rok.buf.get` primitive.
            if let HirTy::GcBuf(elem) = arr_h.ty.clone() {
                return buf_access(ctx, arr_h, *elem, idx, None, span);
            }
            let idx_h = match arr_h.ty {
                HirTy::Array(_, n) => array_position(ctx, idx, n),
                _ => lower_expected(ctx, idx, HirTy::Unknown),
            };
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
            let idx = ctx.breakables.len();
            open_break_target(ctx, idx);
            ctx.breakables.push((label.clone(), true));
            let body_h = lower_loop_body(ctx, body);
            ctx.breakables.pop();
            let result_ty = ctx.break_tys.remove(&idx).map_or(HirTy::Unit, |(t, _)| t);
            // No `break` out: `loop {}` has type `!`.
            let ty = if block_breaks_out(&body_h, label.as_deref(), true) {
                result_ty.clone()
            } else {
                HirTy::Never
            };
            HirExpr {
                kind: HirExprKind::Loop {
                    label: label.clone(),
                    body: Box::new(body_h),
                    result_ty,
                },
                ty,
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
            let body = super::coro::closure_body(body, *is_async, *is_generator);
            lower_closure_expr(ctx, captures, params, ret_ty.as_ref(), &body, span)
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
        ExprKind::Cast(operand, ty) => lower_cast(ctx, operand, ty, span),
        ExprKind::Await(inner) => super::coro::lower_await(ctx, inner, span),
        ExprKind::InModule(module, inner) => {
            let module = std::mem::replace(&mut ctx.current_module, module.clone());
            let scopes = std::mem::replace(&mut ctx.scopes, vec![HashMap::new()]);
            let e = lower_expr(ctx, inner);
            ctx.scopes = scopes;
            ctx.current_module = module;
            e
        }
        ExprKind::Yield(value) => super::coro::lower_yield(ctx, value.as_deref(), span),
        ExprKind::Range {
            start,
            end,
            inclusive,
        } => lower_range_value(ctx, start.as_deref(), end.as_deref(), *inclusive, span),
        ExprKind::Dict(pairs) => {
            let items: Vec<Expr> = pairs
                .iter()
                .map(|(k, v)| Expr {
                    kind: ExprKind::Tuple(vec![k.clone(), v.clone()]),
                    span: k.span,
                })
                .collect();
            let args = vec![rokc_ast::LitArg::Many(items)];
            lower_shape(ctx, rokc_parser::Shape::Dict, args, "`Dict`", span)
        }
        ExprKind::Set(xs) => {
            let args = vec![rokc_ast::LitArg::Many(xs.clone())];
            lower_shape(ctx, rokc_parser::Shape::Set, args, "`Set`", span)
        }
        ExprKind::MagicLiteral(cands) => lower_magic(ctx, cands, span),
        ExprKind::Is(operand, pat) => lower_is(ctx, operand, pat, span),
        ExprKind::Slice {
            target,
            start,
            end,
            step,
        } => lower_slice(
            ctx,
            target,
            start.as_deref(),
            end.as_deref(),
            step.as_deref(),
            span,
        ),
        ExprKind::LetElse { .. } => unsupported(ctx, "`let ... else` in expression position"),
        ExprKind::AsyncBlock(_) | ExprKind::YieldBlock(_) | ExprKind::AsyncYieldBlock(_) => {
            super::coro::lower_coro_expr(ctx, &expr.kind, span)
        }
        ExprKind::Spread(_) => unsupported(ctx, "a spread expression here"),
        ExprKind::Discard(_) => unsupported(ctx, "a discard expression"),
        ExprKind::FString(parts) => super::fstring::lower_fstring(ctx, parts, span),
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

/// A `loop` / labelled block about to be lowered at `breakables`
/// index `idx`: an annotated slot (`let v: T = loop { .. }`) types its
/// `break` values.
pub(super) fn open_break_target(ctx: &mut LowerCtx<'_>, idx: usize) {
    ctx.break_tys.remove(&idx);
    if let Some(t) = ctx
        .current_expected()
        .filter(|t| !matches!(t, HirTy::Unknown | HirTy::Unit))
    {
        ctx.break_tys.insert(idx, (t.clone(), false));
    }
}

/// `break value` to the target at `depth`: the value takes the target's
/// slot type, or (unannotated) the first `break`'s type, which every
/// other `break` must match, as for `if` / `match` arms.
pub(super) fn lower_break_value(ctx: &mut LowerCtx<'_>, depth: usize, e: &Expr) -> HirExpr {
    let slot = ctx.break_tys.get(&depth).cloned();
    let v = lower_expected(
        ctx,
        e,
        slot.as_ref().map_or(HirTy::Unknown, |(t, _)| t.clone()),
    );
    match slot {
        None => {
            if v.ty != HirTy::Unknown && !hir_expr_diverges(&v) {
                ctx.break_tys.insert(depth, (v.ty.clone(), true));
            }
            v
        }
        Some((t, true)) if v.ty != HirTy::Unknown && !coercible(ctx, &t, &v.ty) => ctx.error_expr(
            v.span,
            format!(
                "`break` values have different types `{}` and `{}` — rok does not infer \
                     a sum type; annotate the slot (`let v: {} | {} = loop ...`)",
                ctx.ty_name(&t),
                ctx.ty_name(&v.ty),
                ctx.ty_name(&t),
                ctx.ty_name(&v.ty)
            ),
        ),
        Some((t, _)) => coerce(ctx, &t, v, &|| "this `break` value".to_owned()),
    }
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
    let of_full = |e: &EnumId| enum_base_name(&ctx.enum_def(*e).name) == full;
    // The expected type, or the one member of an expected sum
    // (`-> Result<T, E> | none`) that is an instance of this enum.
    let hinted: Option<EnumId> = match hint {
        Some(HirTy::Enum(e)) if of_full(e) => Some(*e),
        Some(HirTy::Sum(parts)) => {
            let mut hits = parts.iter().filter_map(|p| match p {
                HirTy::Enum(e) if of_full(e) => Some(*e),
                _ => None,
            });
            hits.next().filter(|_| hits.next().is_none())
        }
        _ => None,
    };
    let eid = if let Some(h) = hinted {
        h
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
                ctx.emit_uninferred(format!(
                    "cannot infer the type arguments of `{full}` for `{}` — annotate the \
                     binding with the concrete type",
                    segs.join("::")
                ));
                return EnumRes::Error;
            }
        }
    };
    if let Some(i) = variant_of(eid) {
        EnumRes::Found(eid, i)
    } else if pick_method(ctx, &HirTy::Enum(eid), &vname, None).is_ok_and(|p| p.is_some()) {
        // `Mode::default()`: an associated function, not a variant.
        EnumRes::NotEnum
    } else {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!("enum `{full}` has no variant `{vname}`"),
        );
        EnumRes::Error
    }
}

/// `segs` names an enum (or generic enum base) that has no variant of
/// that name — so `E::f(..)` is an associated function call.
fn enum_lacks_variant(ctx: &LowerCtx<'_>, segs: &[&str]) -> bool {
    let Some((full, vname)) = ctx.enum_path(segs) else {
        return false;
    };
    let ids = ctx
        .lookup_enum(&full)
        .map_or_else(|| ctx.enum_instantiations(&full), |e| vec![e]);
    !ids.is_empty()
        && ids
            .iter()
            .all(|&e| ctx.enum_def(e).variants.iter().all(|v| v.name != vname))
}

/// Payload slot types of a variant, one per constructor argument.
pub(super) fn variant_arg_tys(v: &HirEnumVariant) -> Vec<HirTy> {
    match (&v.payload_ty, v.arity) {
        (None, _) => Vec::new(),
        // A named-field variant's payload is always the tuple of fields.
        (Some(HirTy::Tuple(ps)), _) if !v.named_fields.is_empty() => ps.clone(),
        (Some(t), 1) => vec![t.clone()],
        (Some(HirTy::Tuple(ps)), _) => ps.clone(),
        (Some(t), _) => vec![t.clone()],
    }
}

fn check_duplicate_fields(ctx: &LowerCtx<'_>, segs: &[&str], fields: &[(String, Expr)]) {
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

/// A struct's declared `(field, type)`s; a tuple struct's are `0`, `1`, ...
fn struct_decl_fields(def: &AstStructDef) -> Vec<(String, &Ty)> {
    match &def.kind {
        AstStructKind::Named(fs) => fs.iter().map(|f| (f.name.clone(), &f.ty)).collect(),
        AstStructKind::Tuple(fs) => fs
            .iter()
            .enumerate()
            .map(|(i, f)| (i.to_string(), &f.ty))
            .collect(),
        AstStructKind::Unit => Vec::new(),
    }
}

pub(super) fn lower_struct_init(
    ctx: &mut LowerCtx<'_>,
    path: &AstPath,
    fields: &[(String, Expr)],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
    check_duplicate_fields(ctx, &segs, fields);
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
                let decl_fields = struct_decl_fields(def);
                let generic_names: std::collections::HashSet<String> = def
                    .generics
                    .params
                    .iter()
                    .map(|gp| match gp {
                        rokc_ast::GenericParam::Type { name, .. }
                        | rokc_ast::GenericParam::Const { name, .. } => name.clone(),
                    })
                    .collect();
                let mut subst: HashMap<String, HirTy> = HashMap::new();
                for (i, (n, e)) in fields.iter().enumerate() {
                    let v = lower_expected(ctx, e, HirTy::Unknown);
                    if let Some((_, ty)) = decl_fields.iter().find(|(name, _)| name == n) {
                        unify_param_ty_with(ty, &v.ty, &generic_names, &mut subst, ctx);
                    }
                    pre[i] = Some(v);
                }
                let mut args = Vec::new();
                for gp in &def.generics.params {
                    if let rokc_ast::GenericParam::Const { name, ty } = gp {
                        let c = subst
                            .get(name)
                            .and_then(crate::ty::as_const)
                            .and_then(|(v, _)| super::mono::typed_const(ctx, name, ty, v));
                        let Some(c) = c else {
                            ctx.emit_uninferred(format!(
                                "cannot infer const parameter `{name}` of `{full}` — \
                                 annotate the binding (`let v: {}<..> = ..`)",
                                segs.join("::")
                            ));
                            return poison(span);
                        };
                        args.push(c);
                    }
                    if let rokc_ast::GenericParam::Type { name, default, .. } = gp {
                        match subst
                            .get(name)
                            .cloned()
                            .or_else(|| default.as_ref().map(|d| ctx.resolve_ast_ty(d)))
                        {
                            Some(t) if t != HirTy::Unknown => args.push(t),
                            Some(_) => return poison(span),
                            None if ctx.infer_vars => args.push(super::infer::fresh(ctx)),
                            None => {
                                ctx.emit_uninferred(format!(
                                    "cannot infer type parameter `{name}` of `{full}` — \
                                     write `{}<...> {{ ... }}`",
                                    segs.join("::")
                                ));
                                return poison(span);
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
    // `union { f: v }`: exactly one field, cast/bitcast into the
    // synthetic `__data` slot.
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
    // A missing field takes its declared default, else it is an error.
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
    // A union field read is a `UnionRead`: a cast/bitcast of the one
    // `__data` slot.
    if let Some(union_kind) = def.union_kind.clone() {
        // Spec 4.15.2: reinterpreting the bits can make an invalid value
        // (a bad `bool`, a forged GC reference).
        if ctx.unsafe_depth == 0 {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "reading field `{name}` of union `{}` needs an `unsafe` block \
                     (spec 4.15.2: the bits may not be a valid `{name}`)",
                    leaf_name(&def.name)
                ),
            );
        }
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

/// An untyped literal built from integers only (`1`, `-1`, `1 + 1`).
fn is_untyped_int(e: &Expr) -> bool {
    fn no_float(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Literal(l) => !matches!(l, AstLit::Float(_)),
            ExprKind::OpPrefix { operand, .. } => no_float(operand),
            ExprKind::OpInfix { lhs, rhs, .. } => no_float(lhs) && no_float(rhs),
            _ => true,
        }
    }
    is_untyped_literal(e) && no_float(e)
}

/// An unsuffixed numeric literal (optionally negated): its type comes
/// from context.
pub(super) fn is_untyped_literal(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Literal(AstLit::Int(t)) => !has_int_suffix(t),
        ExprKind::Literal(AstLit::Float(t)) => !t.ends_with("f32") && !t.ends_with("f64"),
        ExprKind::OpPrefix { op, operand } if op == "-" => is_untyped_literal(operand),
        // `1 + 1`: arithmetic on untyped literals stays untyped.
        ExprKind::OpInfix { op, lhs, rhs }
            if matches!(op.as_str(), "+" | "-" | "*" | "/" | "%") =>
        {
            is_untyped_literal(lhs) && is_untyped_literal(rhs)
        }
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
    let cond_h = lower_cond(ctx, cond);
    let expected = ctx
        .current_expected()
        .cloned()
        .filter(|t| *t != HirTy::Unknown);
    let mut then_h = lower_narrowed_block(ctx, cond, then_block);
    let build = |cond_h: HirExpr, then_h: HirBlock, else_h: Option<HirExpr>, ty: HirTy| HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(cond_h),
            then_block: Box::new(then_h),
            else_branch: else_h.map(Box::new),
        },
        ty,
        span,
    };
    let Some(else_e) = else_branch else {
        // No else: the if is a statement; any then-value is discarded.
        return build(cond_h, then_h, None, HirTy::Unit);
    };
    let mut else_h = lower_expr(ctx, else_e);
    // An unsuffixed integer literal branch takes the other branch's
    // integer type: `if c { 1 } else { n }` with `n: usize`.
    let int_ty = |h: &HirTy| match h {
        HirTy::Prim(p) if p.is_int() => Some(h.clone()),
        _ => None,
    };
    let then_lit = then_block.trailing.as_deref().filter(|e| is_untyped_int(e));
    let else_lit = match &else_e.kind {
        ExprKind::Block(b) => b.trailing.as_deref().filter(|e| is_untyped_int(e)),
        _ => None,
    };
    if let (Some(lit), Some(t)) = (then_lit, int_ty(&else_h.ty)) {
        if then_h.trailing.as_ref().is_some_and(|e| e.ty != t) {
            then_h.trailing = Some(lower_expected(ctx, lit, t));
        }
    } else if let (Some(lit), Some(t)) = (
        else_lit,
        then_h.trailing.as_ref().and_then(|e| int_ty(&e.ty)),
    ) {
        if else_h.ty != t {
            let v = lower_expected(ctx, lit, t.clone());
            if let HirExprKind::Block(b) = &mut else_h.kind {
                b.trailing = Some(v);
            }
            else_h.ty = t;
        }
    }
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
        // Branches of different types are an error, not an inferred
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
    build(cond_h, then_h, Some(else_h), result_ty)
}

/// Spec 2.2.6 narrowing: every `x is T` conjunct of `cond` (`x` a local,
/// `cond` = `a && b && ..`) — the locals that are `T` wherever `cond`
/// is known true.
fn narrowings(ctx: &LowerCtx<'_>, cond: &Expr) -> Vec<(String, rokc_ast::Ty)> {
    match &cond.kind {
        ExprKind::OpInfix { op, lhs, rhs } if op == "&&" => {
            let mut v = narrowings(ctx, lhs);
            v.extend(narrowings(ctx, rhs));
            v
        }
        ExprKind::Is(operand, pat) => match (&operand.kind, &pat.kind) {
            (ExprKind::Path(p), AstPatternKind::TypeCheck { binder: None, ty })
                if p.segments.len() == 1
                    && ctx.lookup(&p.segments[0].name).is_some_and(|l| {
                        // An enum's `x is E::V` is a variant test: no narrowing.
                        !ctx.boxed.contains(&l) && !matches!(ctx.local_ty(l), HirTy::Enum(_))
                    }) =>
            {
                vec![(p.segments[0].name.clone(), ty.clone())]
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

/// In the current (fresh) scope, rebind each narrowed local as `T`:
/// `let x = match x { x: T => x };` (the test already passed, so the
/// one-arm match is exhaustive at run time). Assignments to the new
/// binding write through to the original (`narrowed`).
fn bind_narrowed(ctx: &mut LowerCtx<'_>, cond: &Expr) -> Vec<HirStmt> {
    let mut lets = Vec::new();
    for (name, ty) in narrowings(ctx, cond) {
        let Some(orig) = ctx.lookup(&name) else {
            continue;
        };
        let orig_ty = ctx.local_ty(orig);
        let pat = rokc_ast::Pattern {
            kind: AstPatternKind::TypeCheck {
                binder: Some(name.clone()),
                ty,
            },
            span: cond.span,
        };
        let pat_h = lower_pattern(ctx, &pat, &orig_ty);
        // A narrowing rebinding is never a `[ref]` cell.
        ctx.pending_cells.clear();
        let resums = ctx.take_resums(cond.span);
        let Some(new) = ctx.lookup_in_current_scope(&name) else {
            continue;
        };
        let new_ty = ctx.local_ty(new);
        ctx.narrowed.insert(new, (orig, orig_ty.clone()));
        lets.push(HirStmt::Let {
            local: new,
            init: HirExpr {
                kind: HirExprKind::Match {
                    scrutinee: Box::new(hir_local(orig, &orig_ty, cond.span)),
                    arms: vec![HirMatchArm {
                        pat: pat_h,
                        guard: None,
                        body: with_lets(resums, hir_local(new, &new_ty, cond.span)),
                    }],
                },
                ty: new_ty,
                span: cond.span,
            },
        });
    }
    lets
}

/// A block that runs only when `cond` held, with its narrowings bound.
pub(super) fn lower_narrowed_block(ctx: &mut LowerCtx<'_>, cond: &Expr, block: &Block) -> HirBlock {
    ctx.push_scope();
    let lets = bind_narrowed(ctx, cond);
    let mut b = lower_block(ctx, block);
    ctx.pop_scope();
    if !lets.is_empty() {
        b.stmts.splice(0..0, lets);
    }
    b
}

/// Write-through for an assignment to a narrowed binding: also store
/// the new value, converted back, into the original slot.
fn write_through(
    ctx: &mut LowerCtx<'_>,
    stmt: Option<HirStmt>,
    span: rokc_diagnostic::Span,
) -> Option<HirStmt> {
    let local = match &stmt {
        Some(HirStmt::Assign { local, .. }) => *local,
        Some(HirStmt::ArrayAssign { array_local, .. }) => *array_local,
        _ => return stmt,
    };
    if !ctx.narrowed.contains_key(&local) {
        return stmt;
    }
    // A narrowing of a narrowing writes back through every level.
    let mut stmts = vec![stmt?];
    let mut cur = local;
    while let Some((orig, orig_ty)) = ctx.narrowed.get(&cur).cloned() {
        let ty = ctx.local_ty(cur);
        let back = coerce(ctx, &orig_ty, hir_local(cur, &ty, span), &|| {
            "the narrowed slot".to_owned()
        });
        stmts.push(HirStmt::Assign {
            local: orig,
            value: back,
        });
        cur = orig;
    }
    Some(HirStmt::Expr(HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing: None,
            label: None,
        })),
        ty: HirTy::Unit,
        span,
    }))
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
    let lit = |b: bool| HirExpr {
        kind: HirExprKind::Const(ConstVal::Bool(b)),
        ty: HirTy::Prim(PrimTy::Bool),
        span,
    };
    // `e is Enum::Variant` on an enum value: a variant test (any
    // payload), not a type test.
    let variant_pat;
    let pat = match (&scrut.ty, &pat.kind) {
        (
            HirTy::Enum(_),
            AstPatternKind::TypeCheck {
                binder: None,
                ty:
                    rokc_ast::Ty {
                        kind: rokc_ast::TyKind::Path(path),
                        ..
                    },
            },
        ) if path.segments.len() >= 2 => {
            variant_pat = rokc_ast::Pattern {
                kind: AstPatternKind::EnumVariant {
                    path: path.clone(),
                    args: vec![rokc_ast::Pattern {
                        kind: AstPatternKind::Rest(None),
                        span: pat.span,
                    }],
                },
                span: pat.span,
            };
            &variant_pat
        }
        _ => pat,
    };
    // A static (non-`any`, non-sum) operand: the answer is known now.
    if let (false, AstPatternKind::TypeCheck { ty, .. }) = (
        matches!(scrut.ty, HirTy::AnyTrait(_) | HirTy::Sum(_)),
        &pat.kind,
    ) {
        let same = ctx.resolve_ast_ty(ty) == scrut.ty;
        return with_lets(vec![HirStmt::Expr(scrut)], lit(same));
    }
    ctx.push_scope();
    let pat_h = lower_pattern(ctx, pat, &scrut.ty);
    // `is` binders aren't `[ref]` cells (no scope to start
    // one in); capturing one by `ref` is reported at the closure.
    ctx.pending_cells.clear();
    // An `is v: A | B` sub-sum binder stays unconverted; the
    // `if x is (A | B)` narrowing form converts.
    ctx.pending_resums.clear();
    ctx.pop_scope();
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

thread_local! {
    /// Source positions of trailing closures (spec 4.8): such an argument
    /// fills the callee's last parameter (4.8.3), past defaulted or named
    /// ones (4.8.9), not the next positional slot.
    static TRAILING_CLOSURES: std::cell::RefCell<std::collections::HashSet<(u32, u32)>> =
        std::cell::RefCell::default();
}

fn is_trailing_closure(e: &Expr) -> bool {
    TRAILING_CLOSURES.with(|t| t.borrow().contains(&(e.span.file, e.span.start)))
}

/// `args` plus the trailing closure as the last positional argument.
fn with_trailing_closure(args: &[CallArg], tc: Option<&Expr>) -> Vec<CallArg> {
    let mut all = args.to_vec();
    if let Some(tc) = tc {
        TRAILING_CLOSURES.with(|t| t.borrow_mut().insert((tc.span.file, tc.span.start)));
        all.push(CallArg::Positional(tc.clone()));
    }
    all
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
    let (out, lets, _) = lower_args_ref(ctx, sig, callee, receiver, args, span);
    (out, lets)
}

/// `lower_args_for`, also returning each `ref` parameter's argument
/// place (by parameter index) for the copy-out (spec 4.7).
#[allow(clippy::cognitive_complexity)]
pub(super) fn lower_args_ref(
    ctx: &mut LowerCtx<'_>,
    sig: &FnSig,
    callee: &str,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> (Vec<HirExpr>, Vec<HirStmt>, Vec<Option<HirExpr>>) {
    let has_receiver = receiver.is_some();
    let explicit_recv = ctx.explicit_recv.take();
    let n = sig.param_tys.len();
    let mut lets: Vec<HirStmt> = Vec::new();
    let mut slots: Vec<Option<ArgSrc<'_>>> = (0..n).map(|_| None).collect();
    let mut next = 0usize;
    let mut extra = 0usize;
    let mut c_varargs: Vec<HirExpr> = Vec::new();
    if let Some(r) = receiver {
        if n > 0 {
            slots[0] = Some(ArgSrc::Lowered(r));
        }
        next = 1;
    }
    // Spec 4.2.5: a variadic `...T` (the last slot) takes every argument
    // from its position on, spreads included.
    let var_at = if sig.variadic { n - 1 } else { usize::MAX };
    let mut var_parts: Vec<VarPart<'_>> = Vec::new();
    // Slot → its argument's written position (spec 4.2.8).
    let mut written: Vec<Option<usize>> = vec![None; n];
    for (k, a) in args.iter().enumerate() {
        match a {
            CallArg::Positional(e) | CallArg::Ref(e) | CallArg::Spread(e) if next >= var_at => {
                var_parts.push(if matches!(a, CallArg::Spread(_)) {
                    VarPart::Spread(e)
                } else {
                    VarPart::Arg(e)
                });
                next += 1;
            }
            CallArg::Positional(e)
                if !sig.variadic
                    && n > next
                    && slots[n - 1].is_none()
                    && is_trailing_closure(e) =>
            {
                slots[n - 1] = Some(ArgSrc::Ast(e));
                written[n - 1] = Some(k);
                next = n;
            }
            CallArg::Positional(e) | CallArg::Ref(e) => {
                if next < n {
                    written[next] = Some(k);
                    slots[next] = Some(if matches!(a, CallArg::Ref(_)) {
                        ArgSrc::Ref(e)
                    } else {
                        ArgSrc::Ast(e)
                    });
                } else {
                    c_varargs.push(lower_expected(ctx, e, HirTy::Unknown));
                }
                next += 1;
            }
            CallArg::Named { name, value } => {
                match sig.param_names.iter().position(|p| p == name) {
                    Some(i) if slots[i].is_none() => {
                        slots[i] = Some(ArgSrc::Ast(value));
                        written[i] = Some(k);
                    }
                    Some(i) => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "argument `{}` provided more than once (spec 4.1)",
                            sig.param_names.get(i).map_or(name.as_str(), String::as_str)
                        ),
                    ),
                    None => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("`{callee}` has no parameter named `{name}` (spec 4.1)"),
                    ),
                }
            }
            CallArg::Spread(e) => {
                // `f(..t)` with a tuple value (spec 4.1).
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
                            if next >= var_at {
                                var_parts.push(VarPart::Value(field));
                            } else if next < n {
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
    if sig.variadic && slots[var_at].is_none() {
        let elem = variadic_elem(ctx, &sig.param_tys[var_at]);
        slots[var_at] = Some(ArgSrc::Lowered(lower_variadic(ctx, elem, var_parts, span)));
    }
    let c_varargs = check_arity(ctx, sig, callee, extra, c_varargs);
    let mut out = Vec::with_capacity(n);
    let mut places: Vec<Option<HirExpr>> = vec![None; n];
    // Names other (non-`ref`) arguments read, for the exclusivity check.
    let mut reads: Vec<(usize, Vec<String>)> = Vec::new();
    for (i, slot) in slots.into_iter().enumerate() {
        let pty = sig.param_tys[i].clone();
        let pname = sig.param_names.get(i).cloned().unwrap_or_default();
        let by_ref = sig.param_refs.get(i).copied().unwrap_or(false);
        let is_receiver = i == 0 && has_receiver;
        match &slot {
            Some(ArgSrc::Ref(_)) if !by_ref => ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "argument `{pname}` of `{callee}` is passed with `ref`, but the parameter \
                     is not `ref` (spec 4.7.3)"
                ),
            ),
            Some(ArgSrc::Ast(_)) if by_ref && !is_receiver => ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "parameter `{pname}` of `{callee}` is `ref` — pass `ref x` at the call \
                     site (spec 4.7.3)"
                ),
            ),
            Some(ArgSrc::Ast(e)) => reads.push((i, crate::walk::free_names(&[], e))),
            _ => {}
        }
        let v = match slot {
            Some(ArgSrc::Ast(e)) => lower_expected(ctx, e, pty.clone()),
            Some(ArgSrc::Ref(e)) => {
                let h = lower_expected(ctx, e, pty.clone());
                if super::mono::place_root(&h).is_some() {
                    places[i] = Some(h.clone());
                } else if h.ty != HirTy::Unknown {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "`ref` argument `{pname}` of `{callee}` must name a variable or \
                             a field of one (spec 4.7)"
                        ),
                    );
                }
                h
            }
            Some(ArgSrc::Lowered(h)) => {
                if is_receiver {
                    check_path_receiver(ctx, explicit_recv, by_ref, &h, &pname, callee);
                }
                if is_receiver && by_ref {
                    places[i] = Some(h.clone());
                }
                h
            }
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
        // A mismatch points at the argument, not the whole call.
        let at = (v.span != rokc_diagnostic::Span::DUMMY)
            .then(|| rokc_diagnostic::set_current_span(v.span));
        out.push(coerce(ctx, &pty, v, &|| {
            format!("argument `{pname}` of `{callee}`")
        }));
        if let Some(old) = at {
            rokc_diagnostic::set_current_span(old);
        }
    }
    check_ref_exclusive(ctx, callee, &out, &places, &reads, has_receiver);
    // Spec 4.2.8: arguments run in written order. Named ones out of
    // parameter order (`f(b: g(), a: h())`) are evaluated into temps in
    // that order, after the receiver.
    let mut order: Vec<(usize, usize)> = written
        .iter()
        .enumerate()
        .filter_map(|(i, w)| w.filter(|_| places[i].is_none()).map(|w| (w, i)))
        .collect();
    if order.windows(2).any(|w| w[0].0 > w[1].0) {
        order.sort_unstable();
        let recv = (has_receiver && places.first().is_some_and(Option::is_none)).then_some(0);
        for i in recv.into_iter().chain(order.into_iter().map(|(_, i)| i)) {
            let v = std::mem::replace(&mut out[i], poison(span));
            let ty = v.ty.clone();
            let tmp = ctx.declare(None, ty.clone());
            lets.push(HirStmt::Let {
                local: tmp,
                init: v,
            });
            out[i] = hir_local(tmp, &ty, span);
        }
    }
    out.extend(c_varargs);
    (out, lets, places)
}

const LIST: &str = "rok::core::collections::list::List";

/// One trailing argument of a variadic `...T` call (spec 4.2.5).
pub(super) enum VarPart<'e> {
    Arg(&'e Expr),
    /// `..x`: a tuple's fields, or a `List` / `Slice` / array's elements.
    Spread(&'e Expr),
    /// A field of a tuple spread that started in a fixed slot.
    Value(HirExpr),
}

/// The element type `T` of the `Slice<T>` a variadic parameter takes
/// (`Unknown` when `ty` is not one yet).
pub(super) fn variadic_elem(ctx: &LowerCtx<'_>, ty: &HirTy) -> HirTy {
    match ty {
        HirTy::Struct(sid) => ctx
            .struct_def(*sid)
            .generic_args
            .first()
            .cloned()
            .unwrap_or(HirTy::Unknown),
        _ => HirTy::Unknown,
    }
}

/// Spec 4.2.5 / 4.2.6: a variadic call's trailing arguments as the one
/// `Slice<T>` value its `...T` parameter takes. `elem` is `T`, or
/// `Unknown` (an open type parameter: the first argument's type).
/// Plain arguments and tuple fields become a fixed array viewed as a
/// slice; a `List` / `Slice` / array spread makes it a fresh `List` of
/// every argument in order.
pub(super) fn lower_variadic(
    ctx: &mut LowerCtx<'_>,
    mut elem: HirTy,
    parts: Vec<VarPart<'_>>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let mut stmts: Vec<HirStmt> = Vec::new();
    // Each argument once into a temp, in order: (is a spread collection, temp).
    let mut temps: Vec<(bool, String, HirTy)> = Vec::new();
    let temp = |ctx: &mut LowerCtx<'_>, stmts: &mut Vec<HirStmt>, init: HirExpr| {
        let name = format!("#va{}", ctx.locals.len());
        let ty = init.ty.clone();
        let local = ctx.declare(Some(name.clone()), ty.clone());
        stmts.push(HirStmt::Let { local, init });
        (name, ty)
    };
    let one = |ctx: &mut LowerCtx<'_>, elem: &mut HirTy, v: HirExpr| {
        if *elem == HirTy::Unknown {
            elem.clone_from(&v.ty);
            v
        } else {
            coerce(ctx, elem, v, &|| "variadic argument".to_owned())
        }
    };
    for part in parts {
        let v = match part {
            VarPart::Arg(e) => lower_expected(ctx, e, elem.clone()),
            VarPart::Value(v) => v,
            VarPart::Spread(e) => {
                let h = lower_expected(ctx, e, HirTy::Unknown);
                match h.ty.clone() {
                    HirTy::Tuple(fields) => {
                        let (name, ty) = temp(ctx, &mut stmts, h);
                        let local = ctx.lookup(&name).expect("temp just declared");
                        for (k, fty) in fields.iter().enumerate() {
                            let field = HirExpr {
                                kind: HirExprKind::TupleField {
                                    target: Box::new(hir_local(local, &ty, span)),
                                    index: u32::try_from(k).expect("tuple field overflow"),
                                    field_ty: fty.clone(),
                                },
                                ty: fty.clone(),
                                span,
                            };
                            let v = one(ctx, &mut elem, field);
                            let (name, ty) = temp(ctx, &mut stmts, v);
                            temps.push((false, name, ty));
                        }
                    }
                    HirTy::Array(..) | HirTy::Struct(_) => {
                        if elem == HirTy::Unknown {
                            elem = match &h.ty {
                                HirTy::Array(t, _) => (**t).clone(),
                                t => variadic_elem(ctx, t),
                            };
                        }
                        let (name, ty) = temp(ctx, &mut stmts, h);
                        temps.push((true, name, ty));
                    }
                    HirTy::Unknown => {}
                    other => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "spread into a variadic `...T` needs a tuple, a `List`, a `Slice` or \
                             an array, found `{}` (spec 4.2.6)",
                            ctx.ty_name(&other)
                        ),
                    ),
                }
                continue;
            }
        };
        let v = one(ctx, &mut elem, v);
        let (name, ty) = temp(ctx, &mut stmts, v);
        temps.push((false, name, ty));
    }
    // No argument fixed `T` (`count()`): the call reports it uninferred.
    if elem == HirTy::Unknown {
        return poison(span);
    }
    let path = |name: &str| super::throws::path_expr(name, span);
    let ast = |kind: ExprKind| Expr { kind, span };
    let slice_of = |target: Expr| {
        ast(ExprKind::Slice {
            target: Box::new(target),
            start: None,
            end: None,
            step: None,
        })
    };
    let trailing = if temps.iter().all(|(many, ..)| !many) {
        // `[a, b, c][:]`: a fixed array (built here, not by the list
        // literal handler, which is itself variadic) viewed as a slice.
        let n = u32::try_from(temps.len()).expect("variadic argument count overflow");
        let elements = temps
            .iter()
            .map(|(_, name, ty)| {
                let local = ctx.lookup(name).expect("temp declared");
                hir_local(local, ty, span)
            })
            .collect();
        let arr = HirExpr {
            kind: HirExprKind::ArrayInit {
                elem_ty: elem.clone(),
                elements,
            },
            ty: HirTy::Array(Box::new(elem), n),
            span,
        };
        let (name, _) = temp(ctx, &mut stmts, arr);
        lower_expected(ctx, &slice_of(path(&name)), HirTy::Unknown)
    } else {
        // `let l = List::new(); l.push(a); for x in xs { l.push(x); } l[:]`
        let new = ast(ExprKind::Call {
            callee: Box::new(super::bignum::path_expr(LIST, "new", span)),
            args: Vec::new(),
            trailing_closure: None,
        });
        let list_ty = ctx
            .instantiate_struct(LIST, vec![elem])
            .map_or(HirTy::Unknown, HirTy::Struct);
        let init = lower_expected(ctx, &new, list_ty);
        let (list, _) = temp(ctx, &mut stmts, init);
        let push = |x: Expr| {
            ast(ExprKind::MethodCall {
                receiver: Box::new(path(&list)),
                method: "push".to_owned(),
                type_args: Vec::new(),
                args: vec![CallArg::Positional(x)],
                trailing_closure: None,
            })
        };
        for (many, name, _) in &temps {
            let e = if *many {
                let x = format!("#vx{}", ctx.locals.len());
                ast(ExprKind::For {
                    label: None,
                    pat: rokc_ast::Pattern {
                        kind: rokc_ast::PatternKind::Binding {
                            name: x.clone(),
                            sub: None,
                        },
                        span,
                    },
                    iter: Box::new(path(name)),
                    body: rokc_ast::Block {
                        stmts: Vec::new(),
                        trailing: Some(Box::new(push(path(&x)))),
                        span,
                        label: None,
                    },
                    is_await: false,
                })
            } else {
                push(path(name))
            };
            let h = lower_expected(ctx, &e, HirTy::Unknown);
            stmts.push(HirStmt::Expr(h));
        }
        lower_expected(ctx, &slice_of(path(&list)), HirTy::Unknown)
    };
    HirExpr {
        ty: trailing.ty.clone(),
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing: Some(trailing),
            label: None,
        })),
        span,
    }
}

/// Report surplus arguments, unless `sig` is C variadic: then `surplus`
/// are its `...` arguments, returned promoted.
fn check_arity(
    ctx: &LowerCtx<'_>,
    sig: &FnSig,
    callee: &str,
    extra: usize,
    surplus: Vec<HirExpr>,
) -> Vec<HirExpr> {
    if ctx.env.c_variadic.contains(&sig.id) {
        return surplus
            .into_iter()
            .map(|a| c_vararg_promote(ctx, callee, a))
            .collect();
    }
    let extra = extra + surplus.len();
    if extra > 0 {
        let n = sig.param_tys.len();
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "`{callee}` takes {n} argument(s) but {} were supplied",
                n + extra
            ),
        );
    }
    Vec::new()
}

/// An argument past a C variadic declaration's parameters (spec 8.6.10)
/// gets C's default argument promotions: integers narrower than `int`
/// (and `bool`) widen to `i32`, `f32` to `f64`. Aggregates are refused
/// (no `va_arg` of a rok struct on the C side to match).
fn c_vararg_promote(ctx: &LowerCtx<'_>, callee: &str, a: HirExpr) -> HirExpr {
    let to = match &a.ty {
        HirTy::Prim(
            PrimTy::I8 | PrimTy::I16 | PrimTy::U8 | PrimTy::U16 | PrimTy::CChar | PrimTy::Bool,
        ) => PrimTy::I32,
        HirTy::Prim(PrimTy::F32) => PrimTy::F64,
        HirTy::Prim(_) | HirTy::Fn(..) | HirTy::Unknown => return a,
        other => {
            let name = ctx.ty_name(other);
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`{callee}`: a `{name}` cannot be passed as a C variadic `...` argument \
                     (only numbers, `bool`, `char`, `str` and C function pointers; spec 8.6.10)"
                ),
            );
            return a;
        }
    };
    let span = a.span;
    let from_ty = a.ty.clone();
    HirExpr {
        kind: HirExprKind::Cast {
            operand: Box::new(a),
            from_ty,
            to_ty: HirTy::Prim(to),
        },
        ty: HirTy::Prim(to),
        span,
    }
}

/// A path call's first argument standing in for `self` (`T::m(ref x)`,
/// `Tr::m(x)`): `ref` exactly when `self` is `ref` (spec 4.7.3 — only
/// the method-call receiver is implicit). `explicit` is `None` for a
/// method call.
fn check_path_receiver(
    ctx: &LowerCtx<'_>,
    explicit: Option<bool>,
    by_ref: bool,
    arg: &HirExpr,
    pname: &str,
    callee: &str,
) {
    match explicit {
        Some(false) if by_ref => ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "parameter `{pname}` of `{callee}` is `ref` — pass `ref x` at the call site \
                 (spec 4.7.3)"
            ),
        ),
        Some(true) if !by_ref => ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "argument `{pname}` of `{callee}` is passed with `ref`, but the parameter is \
                 not `ref` (spec 4.7.3)"
            ),
        ),
        Some(true) if super::mono::place_root(arg).is_none() && arg.ty != HirTy::Unknown => ctx
            .emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`ref` argument `{pname}` of `{callee}` must name a variable or a field of \
                     one (spec 4.7)"
                ),
            ),
        _ => {}
    }
}

/// Field indices from the root of a place (`p.a.b` → `[a, b]`).
fn field_path(e: &HirExpr) -> Vec<u32> {
    match &e.kind {
        HirExprKind::FieldRead {
            target,
            field_index,
            ..
        } => {
            let mut v = field_path(target);
            v.push(*field_index);
            v
        }
        _ => Vec::new(),
    }
}

/// Spec 4.7.10: during one call a variable may be passed as `ref` only
/// once, and not also be read through another argument — reported when
/// visible syntactically (the root variable of each place).
fn check_ref_exclusive(
    ctx: &LowerCtx<'_>,
    callee: &str,
    args: &[HirExpr],
    places: &[Option<HirExpr>],
    reads: &[(usize, Vec<String>)],
    has_receiver: bool,
) {
    let roots: Vec<(usize, LocalId)> = places
        .iter()
        .enumerate()
        .filter_map(|(i, p)| Some((i, super::mono::place_root(p.as_ref()?)?)))
        .collect();
    let name = |l: LocalId| {
        ctx.locals
            .get(l.0 as usize)
            .and_then(|x| x.name.clone())
            .unwrap_or_default()
    };
    // Field paths: `ref p.x, ref p.y` are disjoint, `ref p, ref p.x` not.
    let paths: Vec<Vec<u32>> = places
        .iter()
        .flatten()
        .filter(|p| super::mono::place_root(p).is_some())
        .map(field_path)
        .collect();
    for (k, (_, a)) in roots.iter().enumerate() {
        let overlaps = |j: usize| {
            let (p, q) = (&paths[j], &paths[k]);
            let n = p.len().min(q.len());
            p[..n] == q[..n]
        };
        if (0..k).any(|j| roots[j].1 == *a && overlaps(j)) {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`{}` is passed as `ref` twice in one call to `{callee}` (spec 4.7.10)",
                    name(*a)
                ),
            );
            return;
        }
    }
    let receiver_read = if has_receiver && places.first().is_some_and(Option::is_none) {
        args.first().and_then(super::mono::place_root)
    } else {
        None
    };
    // Only a whole-variable `ref x` is checked against reads;
    // `ref p.a` beside a read of `p.b` is fine, and telling it from a read
    // of `p.a` would need per-field read analysis.
    for (k, (_, root)) in roots.iter().enumerate() {
        if !paths[k].is_empty() {
            continue;
        }
        let n = name(*root);
        let read = receiver_read == Some(*root)
            || reads.iter().any(|(_, names)| {
                names
                    .iter()
                    .any(|x| *x == n && ctx.lookup(x) == Some(*root))
            });
        if read {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`{n}` is passed as `ref` to `{callee}` and also read by another argument \
                     of the same call (spec 4.7.10)"
                ),
            );
        }
    }
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
    if ctx.env.unsafe_fns.contains(&sig.id) {
        check_unsafe_call(ctx, callee);
    }
    let (lowered, lets, places) = lower_args_ref(ctx, sig, callee, receiver, args, span);
    let out = ctx.env.sink.ref_out.borrow().get(&sig.id).cloned();
    if let Some(out) = out {
        let tys: Vec<HirTy> = out.refs.iter().map(|(_, t)| t.clone()).collect();
        let call = HirExpr {
            kind: HirExprKind::Call {
                callee: sig.id,
                args: lowered,
            },
            ty: super::mono::ref_packed(&out.ret, &tys),
            span,
        };
        let v = super::mono::ref_unpack(ctx, call, &out, &places);
        return with_lets(lets, v);
    }
    // A C function's `fn` parameter is a bare code pointer (an
    // `extern "rok"` one takes the whole `{code, env}`).
    if ctx.env.extern_fn_ids.contains(&sig.id) {
        for a in &lowered {
            // An `extern "C" fn` value is already a C function pointer.
            if matches!(a.ty, HirTy::Fn(..) | HirTy::Closure { .. })
                && !a.ty.is_c_fn()
                && !matches!(a.kind, HirExprKind::FnRef(_))
            {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "`{callee}` is a C function: a `fn` argument must name a function \
                         (a C callback has no room for a closure's captures, spec 5.9)"
                    ),
                );
            }
        }
    }
    // Stdlib spec 0.3.2: an intrinsic method's call is its primitive op.
    let kind = match (
        ctx.env.intrinsics.get(&sig.id),
        <[HirExpr; 2]>::try_from(lowered),
    ) {
        (Some(&op), Ok([lhs, rhs])) => HirExprKind::PrimBinOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
        (Some(&op), Err(mut one)) if one.len() == 1 => {
            let operand = one.remove(0);
            let op = if op == PrimOp::Not && operand.ty == HirTy::Prim(PrimTy::Bool) {
                PrimOp::LogicalNot
            } else {
                op
            };
            HirExprKind::PrimUnaryOp {
                op,
                operand: Box::new(operand),
            }
        }
        (_, Ok(two)) => HirExprKind::Call {
            callee: sig.id,
            args: two.into(),
        },
        (_, Err(args)) => HirExprKind::Call {
            callee: sig.id,
            args,
        },
    };
    check_const_overflow(ctx, &kind, &sig.ret_ty, span);
    with_lets(
        lets,
        HirExpr {
            kind,
            ty: sig.ret_ty.clone(),
            span,
        },
    )
}

/// The type of a value an `if` / `match` / block arm leaves (lowered in
/// statement position, the value is otherwise silently dropped).
fn arm_value_ty(e: &HirExpr) -> Option<HirTy> {
    let block = |b: &HirBlock| b.trailing.as_ref().and_then(arm_value_ty);
    match &e.kind {
        HirExprKind::Block(b) => block(b),
        HirExprKind::If {
            then_block,
            else_branch,
            ..
        } => block(then_block).or_else(|| else_branch.as_deref().and_then(arm_value_ty)),
        HirExprKind::Match { arms, .. } => arms.iter().find_map(|a| arm_value_ty(&a.body)),
        _ if matches!(e.ty, HirTy::Unit | HirTy::Never | HirTy::Unknown) => None,
        _ => Some(e.ty.clone()),
    }
}

/// The value of integer arithmetic over literals (`2 * 200`), if it is
/// one; `None` past an overflow (reported where it happened).
fn const_int(e: &HirExpr) -> Option<i128> {
    let HirTy::Prim(p) = e.ty else {
        return None;
    };
    if !p.is_int() {
        return None;
    }
    let v = match &e.kind {
        HirExprKind::Const(ConstVal::Int { value, .. }) => *value,
        HirExprKind::Const(ConstVal::UInt { value, .. }) => i128::try_from(*value).ok()?,
        HirExprKind::PrimUnaryOp {
            op: PrimOp::Neg,
            operand,
        } => const_int(operand)?.checked_neg()?,
        HirExprKind::PrimBinOp { op, lhs, rhs } => {
            const_arith(*op, const_int(lhs)?, const_int(rhs)?)?
        }
        _ => return None,
    };
    super::pattern::int_fits(v, p).then_some(v)
}

const fn const_arith(op: PrimOp, a: i128, b: i128) -> Option<i128> {
    match op {
        PrimOp::Add => a.checked_add(b),
        PrimOp::Sub => a.checked_sub(b),
        PrimOp::Mul => a.checked_mul(b),
        PrimOp::Div => a.checked_div(b),
        PrimOp::Rem => a.checked_rem(b),
        _ => None,
    }
}

/// `let m: u8 = 2 * 200;`: integer arithmetic folded from literals that
/// leaves its type (or divides by zero) is a compile error.
fn check_const_overflow(
    ctx: &LowerCtx<'_>,
    kind: &HirExprKind,
    ty: &HirTy,
    span: rokc_diagnostic::Span,
) {
    let HirTy::Prim(p) = *ty else {
        return;
    };
    let (op, lhs, rhs) = match kind {
        HirExprKind::PrimBinOp { op, lhs, rhs } => (*op, lhs, rhs),
        _ => return,
    };
    if !p.is_int()
        || !matches!(
            op,
            PrimOp::Add | PrimOp::Sub | PrimOp::Mul | PrimOp::Div | PrimOp::Rem
        )
    {
        return;
    }
    let (Some(a), Some(b)) = (const_int(lhs), const_int(rhs)) else {
        return;
    };
    let msg = match const_arith(op, a, b) {
        None if b == 0 => format!("constant expression divides by zero (`{a}` by `0`)"),
        Some(v) if super::pattern::int_fits(v, p) => return,
        Some(v) => format!(
            "constant expression overflows `{}`: the result is {v}",
            p.name()
        ),
        None => format!("constant expression overflows `{}`", p.name()),
    };
    let old = rokc_diagnostic::set_current_span(span);
    ctx.emit_error(rokc_diagnostic::ErrorKind::Type, msg);
    rokc_diagnostic::set_current_span(old);
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

/// Explicit `::<..>` arguments of a call of generic `def`, bound by
/// position to its own type parameters — those `self_ty` (an impl
/// target) does not fix. More arguments than parameters is an error;
/// fewer leave the rest to inference (`ptr_cast::<u8>(p)`, 1.2.2).
pub(super) fn bind_explicit(
    ctx: &LowerCtx<'_>,
    def: &FnDef,
    self_ty: Option<&Ty>,
    targs: &[Ty],
    callee: &str,
) -> Result<HashMap<String, HirTy>, String> {
    let own: Vec<&String> = def
        .generics
        .params
        .iter()
        .map(|gp| {
            let (rokc_ast::GenericParam::Type { name, .. }
            | rokc_ast::GenericParam::Const { name, .. }) = gp;
            name
        })
        .filter(|n| !self_ty.is_some_and(|t| ast_ty_mentions(t, n)))
        .collect();
    if targs.len() > own.len() {
        return Err(format!(
            "`{}` takes {} generic argument(s) but {} were supplied",
            leaf_name(callee),
            own.len(),
            targs.len()
        ));
    }
    Ok(own
        .into_iter()
        .zip(targs)
        .map(|(n, t)| (n.clone(), ctx.resolve_ast_ty(t)))
        .collect())
}

/// Does AST type `ty` name `name` (a type parameter)?
fn ast_ty_mentions(ty: &Ty, name: &str) -> bool {
    let rec = |t: &Ty| ast_ty_mentions(t, name);
    match &ty.kind {
        AstTyKind::Path(p) => p
            .segments
            .iter()
            .any(|s| s.name == name || s.generics.iter().any(rec)),
        AstTyKind::Sum(ts) | AstTyKind::Tuple(ts) => ts.iter().any(rec),
        AstTyKind::Fn(a, r, _) => a.iter().any(rec) || rec(r),
        AstTyKind::Throws { ok, err } => rec(ok) || rec(err),
        AstTyKind::Array(e, _) => rec(e),
        _ => false,
    }
}

/// `x.drop()` is banned when it is `Drop::drop`; the `using` desugar's
/// `x.#drop()` is `drop` on a type that must implement `Drop`
/// (spec 3.17.7).
fn drop_method<'m>(
    ctx: &LowerCtx<'_>,
    recv_ty: &HirTy,
    method: &'m str,
    span: rokc_diagnostic::Span,
) -> Result<&'m str, HirExpr> {
    match method {
        rokc_ast::USING_DROP_METHOD => {
            if *recv_ty != HirTy::Unknown && !needs_drop(ctx, recv_ty, 0) {
                return Err(ctx.error_expr(
                    span,
                    format!(
                        "`using` needs a resource whose type implements `Drop`; `{}` does not \
                         implement `Drop` nor hold a `Drop` field (spec 3.17.7)",
                        ctx.ty_name(recv_ty)
                    ),
                ));
            }
            Ok(method)
        }
        "drop" if is_drop_method(ctx, recv_ty) => {
            direct_drop_error(ctx, span).map_or(Ok("drop"), Err)
        }
        m => Ok(m),
    }
}

/// Nesting past which drop glue stops looking (types are finite; this
/// bounds the work on deep ones).
const DROP_GLUE_DEPTH: u32 = 64;

/// Does releasing a `ty` run any `Drop::drop` — its own, or one of a
/// field / tuple element / payload's (stdlib spec 2.13.4)?
fn needs_drop(ctx: &LowerCtx<'_>, ty: &HirTy, depth: u32) -> bool {
    if depth > DROP_GLUE_DEPTH {
        return false;
    }
    if ctx.implements_trait(ty, ctx.lang_trait("drop_method"), 0) {
        return true;
    }
    let any = |ts: &[HirTy]| ts.iter().any(|t| needs_drop(ctx, t, depth + 1));
    match ty {
        HirTy::Struct(sid) => {
            let fields: Vec<HirTy> = ctx
                .struct_def(*sid)
                .fields
                .iter()
                .map(|f| f.ty.clone())
                .collect();
            any(&fields)
        }
        HirTy::Enum(eid) => {
            let tys: Vec<HirTy> = ctx
                .enum_def(*eid)
                .variants
                .iter()
                .flat_map(variant_arg_tys)
                .collect();
            any(&tys)
        }
        HirTy::Tuple(ts) | HirTy::Sum(ts) => any(ts),
        _ => false,
    }
}

/// What a `using` exit runs for `value` (stdlib spec 2.13.4): its own
/// `drop`, then each `Drop`-carrying field / tuple element in reverse
/// declaration order, recursively; an enum / sum releases the payload
/// of the variant it holds.
fn drop_glue(
    ctx: &mut LowerCtx<'_>,
    value: HirExpr,
    span: rokc_diagnostic::Span,
    depth: u32,
) -> Vec<HirStmt> {
    let mut out = Vec::new();
    if !needs_drop(ctx, &value.ty, depth) {
        return out;
    }
    let ty = value.ty.clone();
    if ctx.implements_trait(&ty, ctx.lang_trait("drop_method"), 0) {
        out.push(HirStmt::Expr(method_call_on(
            ctx,
            value.clone(),
            "drop",
            &[],
            span,
        )));
    }
    let block = |stmts: Vec<HirStmt>| HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing: None,
            label: None,
        })),
        ty: HirTy::Unit,
        span,
    };
    let unit_arm = || HirMatchArm {
        pat: HirPattern::Wildcard,
        guard: None,
        body: block(Vec::new()),
    };
    match &ty {
        HirTy::Struct(sid) => {
            let fields: Vec<HirTy> = ctx
                .struct_def(*sid)
                .fields
                .iter()
                .map(|f| f.ty.clone())
                .collect();
            for (i, fty) in fields.iter().enumerate().rev() {
                let field = HirExpr {
                    kind: HirExprKind::FieldRead {
                        target: Box::new(value.clone()),
                        struct_id: *sid,
                        field_index: u32::try_from(i).expect("field overflow"),
                        field_ty: fty.clone(),
                    },
                    ty: fty.clone(),
                    span,
                };
                out.extend(drop_glue(ctx, field, span, depth + 1));
            }
        }
        HirTy::Tuple(ts) => {
            for (i, t) in ts.iter().enumerate().rev() {
                let elem = HirExpr {
                    kind: HirExprKind::TupleField {
                        target: Box::new(value.clone()),
                        index: u32::try_from(i).expect("tuple field overflow"),
                        field_ty: t.clone(),
                    },
                    ty: t.clone(),
                    span,
                };
                out.extend(drop_glue(ctx, elem, span, depth + 1));
            }
        }
        HirTy::Enum(eid) => {
            let variants = ctx.enum_def(*eid).variants;
            let mut arms = Vec::new();
            for (vi, v) in variants.iter().enumerate() {
                let tys = variant_arg_tys(v);
                if !tys.iter().any(|t| needs_drop(ctx, t, depth + 1)) {
                    continue;
                }
                let locals: Vec<LocalId> =
                    tys.iter().map(|t| ctx.declare(None, t.clone())).collect();
                let mut stmts = Vec::new();
                for (l, t) in locals.iter().zip(&tys).rev() {
                    stmts.extend(drop_glue(ctx, hir_local(*l, t, span), span, depth + 1));
                }
                arms.push(HirMatchArm {
                    pat: HirPattern::EnumVariant {
                        enum_id: *eid,
                        variant_index: u32::try_from(vi).expect("variant overflow"),
                        args: locals
                            .iter()
                            .zip(&tys)
                            .map(|(l, t)| HirPattern::Binding {
                                local: *l,
                                ty: t.clone(),
                            })
                            .collect(),
                    },
                    guard: None,
                    body: block(stmts),
                });
            }
            arms.push(unit_arm());
            out.push(HirStmt::Expr(HirExpr {
                kind: HirExprKind::Match {
                    scrutinee: Box::new(value),
                    arms,
                },
                ty: HirTy::Unit,
                span,
            }));
        }
        HirTy::Sum(ts) => {
            let mut arms = Vec::new();
            for (vi, t) in ts.iter().enumerate() {
                if !needs_drop(ctx, t, depth + 1) {
                    continue;
                }
                let l = ctx.declare(None, t.clone());
                let stmts = drop_glue(ctx, hir_local(l, t, span), span, depth + 1);
                arms.push(HirMatchArm {
                    pat: HirPattern::SumVariant {
                        sum_ty: ty.clone(),
                        variant_index: u32::try_from(vi).expect("variant overflow"),
                        binder: Some(l),
                        payload_ty: Some(t.clone()),
                    },
                    guard: None,
                    body: block(stmts),
                });
            }
            arms.push(unit_arm());
            out.push(HirStmt::Expr(HirExpr {
                kind: HirExprKind::Match {
                    scrutinee: Box::new(value),
                    arms,
                },
                ty: HirTy::Unit,
                span,
            }));
        }
        _ => {}
    }
    out
}

/// Does `ty`'s `drop` method come from `Drop`?
fn is_drop_method(ctx: &LowerCtx<'_>, ty: &HirTy) -> bool {
    let trait_name = match pick_method(ctx, ty, "drop", None) {
        Ok(Some(MethodPick::Concrete(id))) => ctx
            .env
            .method_info
            .get(&id)
            .and_then(|i| i.trait_name.clone()),
        Ok(Some(MethodPick::Generic(gm))) => gm.info.trait_name.clone(),
        _ => None,
    };
    trait_name.as_deref() == Some(ctx.lang_trait("drop_method"))
}

/// Spec 2.13.4: `Drop::drop` runs only when a `using` block exits;
/// calling it directly is an error. `unsafe` code in the bare tier
/// (`drop_in_place`) is exempt.
fn direct_drop_error(ctx: &LowerCtx<'_>, span: rokc_diagnostic::Span) -> Option<HirExpr> {
    if ctx.unsafe_depth > 0 && ctx.current_module.starts_with("rok::bare") {
        return None;
    }
    Some(
        ctx.error_expr(
            span,
            "`Drop::drop` cannot be called directly; it runs when a `using` block exits \
         (spec 2.13.4) — expose a method such as `close()` to release early"
                .to_owned(),
        ),
    )
}

/// `Drop::drop(x)` / `File::drop(f)` / `T::drop(x)`.
fn check_direct_drop_path(ctx: &LowerCtx<'_>, p: &rokc_ast::Path) {
    let [prefix @ .., last] = p.segments.as_slice() else {
        return;
    };
    if last.name != "drop" || prefix.is_empty() {
        return;
    }
    let segs: Vec<&str> = prefix.iter().map(|s| s.name.as_str()).collect();
    let is_drop =
        ctx.env.names.trait_key(&segs, &ctx.current_module) == ctx.lang_trait("drop_method") || {
            let ty = ctx.resolve_ast_ty(&rokc_ast::Ty {
                kind: rokc_ast::TyKind::Path(rokc_ast::Path {
                    segments: prefix.to_vec(),
                    span: p.span,
                }),
                span: p.span,
            });
            is_drop_method(ctx, &ty)
        };
    if is_drop {
        direct_drop_error(ctx, p.span);
    }
}

/// Traits a sum type has when all its variants do (spec 2.13.6, 2.5.7,
/// 2.10.9: `T | none` is `Clone` / `Debug` / ... when `T` is).
pub(super) const SUM_TRAITS: &[&str] = &[
    "rok::core::marker::Clone",
    "rok::core::marker::Copy",
    "rok::core::fmt::Debug",
    "rok::core::ops::PartialEq",
    "rok::core::cmp::Eq",
    "rok::core::cmp::Hash",
    "rok::core::ops::PartialOrd",
    "rok::core::cmp::Ord",
];

/// Their methods, dispatched on the variant by `sum_structural_call`.
const SUM_METHODS: &[&str] = &[
    "clone", "fmt", "eq", "ne", "hash", "lt", "gt", "le", "ge", "cmp",
];

/// `x.clone()` / `Debug::fmt(x, ref f)` / `.eq(y)` / `.ne(y)` / `.hash()` / `.lt(y)`
/// (`gt` / `le` / `ge`) / `.cmp(y)` on a sum `x`: a `match` over the
/// variants calling the variant's method (`eq` is false across variants;
/// `none` clones to itself, shows as `none`, equals `none`, hashes to its
/// tag). Ordering is by variant (the sum's canonical member order,
/// `HirTy::sum`), then payload — like a derived enum's.
/// `lowered_rhs` is a binary method's already lowered argument (an
/// operator's right operand); otherwise it comes from `args`.
fn sum_structural_call(
    ctx: &mut LowerCtx<'_>,
    recv: HirExpr,
    method: &str,
    args: &[CallArg],
    lowered_rhs: Option<HirExpr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let HirTy::Sum(variants) = recv.ty.clone() else {
        return recv;
    };
    let sum_ty = recv.ty.clone();
    let binary = matches!(method, "eq" | "ne" | "lt" | "gt" | "le" | "ge" | "cmp");
    let bool_c = |b: bool| HirExpr {
        kind: HirExprKind::Const(ConstVal::Bool(b)),
        ty: HirTy::Prim(PrimTy::Bool),
        span,
    };
    let ordering = |ctx: &mut LowerCtx<'_>, variant: &str| {
        let segments = ["rok", "core", "cmp", "Ordering", variant]
            .iter()
            .map(|n| rokc_ast::PathSegment {
                name: (*n).to_owned(),
                generics: Vec::new(),
            })
            .collect();
        lower_expr(
            ctx,
            &Expr {
                kind: ExprKind::Path(AstPath { segments, span }),
                span,
            },
        )
    };
    let result_ty = match method {
        "clone" => sum_ty.clone(),
        "fmt" => HirTy::Unit,
        "hash" => HirTy::Prim(PrimTy::U64),
        "cmp" => ordering(ctx, "Equal").ty,
        _ => HirTy::Prim(PrimTy::Bool),
    };
    // The result when the two sides are different variants (`less`: the
    // left one comes first) or both `none`.
    let across = |ctx: &mut LowerCtx<'_>, less: bool| match method {
        "cmp" => ordering(ctx, if less { "Less" } else { "Greater" }),
        "lt" | "le" => bool_c(less),
        "gt" | "ge" => bool_c(!less),
        _ => bool_c(method == "ne"),
    };
    let same_none = |ctx: &mut LowerCtx<'_>| match method {
        "cmp" => ordering(ctx, "Equal"),
        _ => bool_c(matches!(method, "eq" | "le" | "ge")),
    };
    let mut stmts = Vec::new();
    let s = ctx.declare(None, sum_ty.clone());
    stmts.push(HirStmt::Let {
        local: s,
        init: recv,
    });
    let rhs = if binary {
        let v = if let Some(v) = lowered_rhs {
            v
        } else {
            let [CallArg::Positional(e)] = args else {
                discard_args(ctx, args);
                return ctx.error_expr(span, format!("`{method}` takes one argument"));
            };
            lower_expected(ctx, e, sum_ty.clone())
        };
        let v = coerce(ctx, &sum_ty, v, &|| format!("the argument of `{method}`"));
        let r = ctx.declare(None, sum_ty.clone());
        stmts.push(HirStmt::Let { local: r, init: v });
        Some(r)
    } else {
        if method != "fmt" {
            discard_args(ctx, args);
        }
        None
    };
    let path = |name: &str| Expr {
        kind: ExprKind::Path(AstPath {
            segments: vec![rokc_ast::PathSegment {
                name: name.to_owned(),
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    };
    let call = |m: &str, arg: Option<&str>| Expr {
        kind: ExprKind::MethodCall {
            receiver: Box::new(path("#a")),
            method: m.to_owned(),
            type_args: Vec::new(),
            args: arg
                .map(|a| CallArg::Positional(path(a)))
                .into_iter()
                .collect(),
            trailing_closure: None,
        },
        span,
    };
    let arm_pat = |ctx: &mut LowerCtx<'_>, i: usize, name: &str| {
        let vt = &variants[i];
        let none = is_none_ty(vt);
        let binder = (!none).then(|| ctx.declare(Some(name.to_owned()), vt.clone()));
        HirPattern::SumVariant {
            sum_ty: sum_ty.clone(),
            variant_index: u32::try_from(i).expect("variant overflow"),
            binder,
            payload_ty: (!none).then(|| vt.clone()),
        }
    };
    let mut arms = Vec::new();
    for (i, vt) in variants.iter().enumerate() {
        ctx.push_scope();
        let pat = arm_pat(ctx, i, "#a");
        let none = is_none_ty(vt);
        let body = match (method, rhs) {
            ("clone", _) if none => hir_local(s, &sum_ty, span),
            ("clone", _) => {
                let v = lower_expr(ctx, &call("clone", None));
                wrap_into_sum(&sum_ty, v)
            }
            ("fmt", _) => {
                // `Debug::fmt(#a, ref f)`, or `none` written.
                let fmt_path = |names: &[&str]| Expr {
                    kind: ExprKind::Path(AstPath {
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
                let (callee, first) = if none {
                    let lit = Expr {
                        kind: ExprKind::Literal(AstLit::Str("none".to_owned())),
                        span,
                    };
                    (&["rok", "core", "fmt", "Formatter", "write_str"][..], lit)
                } else {
                    (&["rok", "core", "fmt", "Debug", "fmt"][..], path("#a"))
                };
                let mut call_args = args.to_vec();
                if none {
                    call_args.push(CallArg::Positional(first));
                } else {
                    call_args.insert(0, CallArg::Positional(first));
                }
                let c = Expr {
                    kind: ExprKind::Call {
                        callee: Box::new(fmt_path(callee)),
                        args: call_args,
                        trailing_closure: None,
                    },
                    span,
                };
                lower_expr(ctx, &c)
            }
            ("hash", _) => {
                let tag = hir_int(i128::try_from(i).unwrap_or(0), PrimTy::U64, span);
                if none {
                    tag
                } else {
                    let h = lower_expr(ctx, &call("hash", None));
                    HirExpr {
                        kind: HirExprKind::PrimBinOp {
                            op: PrimOp::BitXor,
                            lhs: Box::new(h),
                            rhs: Box::new(tag),
                        },
                        ty: HirTy::Prim(PrimTy::U64),
                        span,
                    }
                }
            }
            (_, Some(r)) => {
                // Same variant on the right: compare payloads; otherwise
                // the variant order decides (`eq` / `ne` don't care which
                // side comes first).
                let eq_like = matches!(method, "eq" | "ne");
                let mut inner = Vec::new();
                for j in 0..variants.len() {
                    if j != i && eq_like {
                        continue;
                    }
                    ctx.push_scope();
                    let inner_pat = arm_pat(ctx, j, "#b");
                    let body = if j != i {
                        across(ctx, i < j)
                    } else if none {
                        same_none(ctx)
                    } else {
                        lower_expr(ctx, &call(method, Some("#b")))
                    };
                    ctx.pop_scope();
                    inner.push(HirMatchArm {
                        pat: inner_pat,
                        guard: None,
                        body,
                    });
                }
                if eq_like {
                    inner.push(HirMatchArm {
                        pat: HirPattern::Wildcard,
                        guard: None,
                        body: across(ctx, false),
                    });
                }
                HirExpr {
                    kind: HirExprKind::Match {
                        scrutinee: Box::new(hir_local(r, &sum_ty, span)),
                        arms: inner,
                    },
                    ty: result_ty.clone(),
                    span,
                }
            }
            _ => lower_expr(ctx, &call(method, None)),
        };
        ctx.pop_scope();
        let body = coerce(ctx, &result_ty, body, &|| {
            format!("`{method}` of a sum value")
        });
        arms.push(HirMatchArm {
            pat,
            guard: None,
            body,
        });
    }
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts,
            trailing: Some(HirExpr {
                kind: HirExprKind::Match {
                    scrutinee: Box::new(hir_local(s, &sum_ty, span)),
                    arms,
                },
                ty: result_ty.clone(),
                span,
            }),
            label: None,
        })),
        ty: result_ty,
        span,
    }
}

/// `Ord`'s provided `min` / `max` / `clamp` on a sum (whose `Ord` is
/// compiler-dispatched, `sum_structural_call`): `a.min(b)` is `if a <= b
/// { a } else { b }`, `a.clamp(lo, hi)` is `if a < lo { lo } else if a >
/// hi { hi } else { a }` — the trait's default bodies.
fn sum_min_max(
    ctx: &mut LowerCtx<'_>,
    recv: HirExpr,
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let ty = recv.ty.clone();
    let want = if method == "clamp" { 2 } else { 1 };
    if args.len() != want || args.iter().any(|a| !matches!(a, CallArg::Positional(_))) {
        discard_args(ctx, args);
        return ctx.error_expr(span, format!("`{method}` takes {want} argument(s)"));
    }
    let mut stmts = Vec::new();
    let mut local = |ctx: &mut LowerCtx<'_>, init: HirExpr| {
        let l = ctx.declare(None, ty.clone());
        stmts.push(HirStmt::Let { local: l, init });
        l
    };
    let a = local(ctx, recv);
    let mut ls = Vec::new();
    for arg in args {
        let CallArg::Positional(e) = arg else {
            unreachable!("checked above")
        };
        let v = lower_expected(ctx, e, ty.clone());
        let v = coerce(ctx, &ty, v, &|| format!("the argument of `{method}`"));
        ls.push(local(ctx, v));
    }
    let get = |l: LocalId| hir_local(l, &ty, span);
    let test = |ctx: &mut LowerCtx<'_>, op: &str, l: LocalId, r: LocalId| {
        sum_structural_call(ctx, get(l), op, &[], Some(get(r)), span)
    };
    let pick = |cond: HirExpr, then: HirExpr, other: HirExpr| HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(cond),
            then_block: Box::new(HirBlock {
                stmts: Vec::new(),
                trailing: Some(then),
                label: None,
            }),
            else_branch: Some(Box::new(other)),
        },
        ty: ty.clone(),
        span,
    };
    let value = match (method, ls.as_slice()) {
        ("min", [b]) => pick(test(ctx, "le", a, *b), get(a), get(*b)),
        ("max", [b]) => pick(test(ctx, "ge", a, *b), get(a), get(*b)),
        (_, [lo, hi]) => {
            let above = pick(test(ctx, "gt", a, *hi), get(*hi), get(a));
            pick(test(ctx, "lt", a, *lo), get(*lo), above)
        }
        _ => unreachable!("arity checked above"),
    };
    with_lets(stmts, value)
}

pub(super) fn method_call_on(
    ctx: &mut LowerCtx<'_>,
    recv_h: HirExpr,
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let lower_args_only = |ctx: &mut LowerCtx<'_>| discard_args(ctx, args);
    let type_args = std::mem::take(&mut ctx.method_type_args);
    if recv_h.ty == HirTy::Unknown {
        lower_args_only(ctx);
        return recv_h;
    }
    if matches!(recv_h.ty, HirTy::Sum(_)) && SUM_METHODS.contains(&method) {
        return sum_structural_call(ctx, recv_h, method, args, None, span);
    }
    let recv_h = if matches!(recv_h.ty, HirTy::Sum(_)) {
        match super::reflect::method_call(ctx, recv_h, method, args) {
            Ok(r) => return r,
            Err(r) => r,
        }
    } else {
        recv_h
    };
    if matches!(recv_h.ty, HirTy::Sum(_)) && matches!(method, "min" | "max" | "clamp") {
        return sum_min_max(ctx, recv_h, method, args, span);
    }
    if let HirTy::AnyTrait(bounds) = recv_h.ty.clone() {
        return any_method_call(ctx, recv_h, &bounds, method, None, args, span);
    }
    let pick = match pick_method(ctx, &recv_h.ty, method, None) {
        Ok(p) => p,
        Err(msg) => {
            lower_args_only(ctx);
            return ctx.error_expr(span, msg);
        }
    };
    let fn_id = match pick {
        Some(MethodPick::Concrete(id)) => Some(id),
        Some(MethodPick::Generic(_)) | None => None,
    };
    let Some(fn_id) = fn_id else {
        let gm = match pick {
            Some(MethodPick::Generic(gm)) => Some(gm),
            _ => None,
        };
        if let Some(gm) = gm {
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
            match bind_explicit(ctx, &gm.def, Some(&gm.self_ty), &type_args, method) {
                Ok(bound) => ctx.explicit_generics = bound,
                Err(msg) => {
                    lower_args_only(ctx);
                    return ctx.error_expr(span, msg);
                }
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
        // A generic impl that would provide it but whose bound fails:
        // name the bound rather than "no method".
        let unmet = ctx.env.generic_trait_impls.iter().find_map(|gi| {
            if !gi.methods.contains_key(method) {
                return None;
            }
            ctx.generic_impl_match(gi, &recv_h.ty, 0)
                .err()
                .flatten()
                .map(|b| (gi, b))
        });
        if let Some((gi, (bty, bound))) = unmet {
            return ctx.error_expr(
                span,
                format!(
                    "method `{method}` of the generic impl of `{}` does not apply to `{}`: \
                     its bound needs `{}: {bound}`, which does not hold",
                    gi.trait_key,
                    ctx.ty_name(&recv_h.ty),
                    ctx.ty_name(&bty)
                ),
            );
        }
        // Spec 3.5.2: a missing method is a hard error, not a silent
        // unit return — unless `Reflect` (every type's) answers it.
        let recv_h = match super::reflect::method_call(ctx, recv_h, method, args) {
            Ok(r) => return r,
            Err(r) => r,
        };
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
    if !type_args.is_empty() {
        lower_args_only(ctx);
        return ctx.error_expr(
            span,
            format!(
                "`{method}` takes no generic arguments, but `::<..>` gives {}",
                type_args.len()
            ),
        );
    }
    let sig = ctx.sig_by_id(fn_id);
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

/// `v.m(args)` on an `any Tr` value. Only methods of the bound
/// traits and their supertraits are callable; the call becomes a switch
/// on the tag over every implementor in the program:
/// `match v { x: T1 => T1::m(x, args), x: T2 => T2::m(x, args), ... }`.
fn any_method_call(
    ctx: &mut LowerCtx<'_>,
    recv_h: HirExpr,
    bounds: &[String],
    method: &str,
    only: Option<&str>,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let mut seen: Vec<String> = Vec::new();
    let mut stack = bounds.to_vec();
    // The trait declaring `method`, and the bound that named it (with
    // its arguments / bindings; a supertrait reached indirectly has none).
    let mut provider: Option<(String, String)> = None;
    while let Some(t) = stack.pop() {
        let base = bound_base(&t).to_owned();
        if seen.contains(&base) {
            continue;
        }
        if let Some(info) = ctx.env.trait_info.get(&base) {
            if provider.is_none()
                && only.is_none_or(|k| k == base)
                && info.methods.iter().any(|m| m == method)
            {
                provider = Some((base.clone(), t.clone()));
            }
            stack.extend(info.supers.iter().cloned());
        }
        seen.push(base);
    }
    let recv_ty = recv_h.ty.clone();
    let Some((provider, bound)) = provider else {
        if let Ok(r) = super::reflect::method_call(ctx, recv_h, method, args) {
            return r;
        }
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
    if method == "fmt" && is_fmt_trait(ctx, &provider) {
        return any_fmt(ctx, recv_h, &provider, args, span);
    }
    // Every implementor shares one signature only if it doesn't depend
    // on the implementing type (`Self`), on trait arguments the bound
    // leaves open, or on associated types it doesn't bind.
    let fixed = bound.split_once('<').map_or("", |(_, rest)| rest);
    let has_args = !fixed.is_empty() && !fixed.split(", ").next().unwrap_or("").contains(" = ");
    let needs = ctx.env.trait_info[&provider]
        .needs
        .get(method)
        .cloned()
        .unwrap_or_default();
    let no_self = ctx.env.trait_info[&provider]
        .decls
        .get(method)
        .is_some_and(|d| d.params.first().is_none_or(|p| p.name != "self"));
    let why = no_self.then(|| {
        "it takes no `self`, so there is no value to dispatch on (not object-safe)".to_owned()
    });
    let why = why.or_else(|| {
        needs.iter().find_map(|n| {
            if n == "Self" {
                Some(
                    "its signature mentions `Self`, which is a different type for each implementor"
                        .to_owned(),
                )
            } else if let Some(x) = n.strip_prefix("Self::") {
                (!fixed.contains(&format!("{x} = "))).then(|| {
                    format!(
                        "its signature uses `Self::{x}`, which the bound leaves open — bind it \
                     (`any {provider}<{x} = ..>`)"
                    )
                })
            } else {
                (!has_args).then(|| {
                    format!(
                        "its signature uses type parameters of `{provider}` that the bound leaves \
                     open — name them (`any {provider}<..>`)"
                    )
                })
            }
        })
    });
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
    // The signature, the same for every implementor (checked above):
    // a concrete impl's, else the trait declaration's.
    let concrete = ctx
        .env
        .trait_impl_tys
        .get(bound_base(&bounds[0]))
        .into_iter()
        .flatten()
        .find(|t| bounds.iter().all(|b| ctx.implements(t, b)))
        .and_then(|t| match pick_method(ctx, t, method, Some(&provider)) {
            Ok(Some(MethodPick::Concrete(id))) => Some(ctx.sig_by_id(id)),
            _ => None,
        })
        .map(|sig| (sig.param_tys[1..].to_vec(), sig.ret_ty.clone()));
    let Some((params, ret)) = concrete.or_else(|| trait_decl_sig(ctx, &provider, &bound, method))
    else {
        discard_args(ctx, args);
        return ctx.error_expr(
            span,
            format!(
                "cannot call `{method}` on `{}`: its signature can't be fixed from the bound \
                 `{bound}` (D4)",
                ctx.ty_name(&recv_ty)
            ),
        );
    };
    let mut param_tys = vec![recv_ty.clone()];
    param_tys.extend(params);
    let sig = FnSig {
        id: FunctionId(u32::MAX),
        ret_ty: ret.clone(),
        param_defaults: vec![None; param_tys.len()],
        param_names: (0..param_tys.len()).map(|i| format!("#{i}")).collect(),
        param_refs: Vec::new(),
        param_tys,
        variadic: false,
    };
    let (lowered, lets) = lower_args_for(ctx, &sig, method, Some(recv_h), args, span);
    let id = any_dispatcher(ctx, &recv_ty, &provider, method, &sig, span);
    with_lets(
        lets,
        HirExpr {
            kind: HirExprKind::Call {
                callee: id,
                args: lowered,
            },
            ty: ret,
            span,
        },
    )
}

fn is_fmt_trait(ctx: &LowerCtx<'_>, key: &str) -> bool {
    key == ctx.lang_trait("display_trait") || key == ctx.lang_trait("debug_trait")
}

/// `Display::fmt(v, ref f)` / `Debug::fmt` on an `any` value: the
/// dispatcher renders the value's text (`build_dispatcher`), which is
/// then written to `f`.
fn any_fmt(
    ctx: &mut LowerCtx<'_>,
    recv_h: HirExpr,
    provider: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let str_ty = HirTy::Prim(PrimTy::Str);
    let sig = FnSig {
        id: FunctionId(u32::MAX),
        ret_ty: str_ty.clone(),
        param_defaults: vec![None],
        param_names: vec!["#0".to_owned()],
        param_refs: Vec::new(),
        param_tys: vec![recv_h.ty.clone()],
        variadic: false,
    };
    let id = any_dispatcher(ctx, &recv_h.ty, provider, "fmt", &sig, span);
    let text = HirExpr {
        kind: HirExprKind::Call {
            callee: id,
            args: vec![recv_h],
        },
        ty: str_ty.clone(),
        span,
    };
    ctx.push_scope();
    let name = format!("#t{}", ctx.locals.len());
    let local = ctx.declare(Some(name.clone()), str_ty);
    let path = |names: &[&str]| Expr {
        kind: ExprKind::Path(AstPath {
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
    let mut call_args = args.to_vec();
    call_args.push(CallArg::Positional(path(&[&name])));
    let write = Expr {
        kind: ExprKind::Call {
            callee: Box::new(path(&["rok", "core", "fmt", "Formatter", "write_str"])),
            args: call_args,
            trailing_closure: None,
        },
        span,
    };
    let write = lower_expr(ctx, &write);
    ctx.pop_scope();
    with_lets(vec![HirStmt::Let { local, init: text }], write)
}

/// `method`'s signature from trait `provider`'s declaration, with the
/// trait's parameters and associated types filled in from `bound`
/// (`Source<i32, Item = u8>`). `None` when an argument can't be read
/// back from the bound key.
fn trait_decl_sig(
    ctx: &LowerCtx<'_>,
    provider: &str,
    bound: &str,
    method: &str,
) -> Option<(Vec<HirTy>, HirTy)> {
    let info = &ctx.env.trait_info[provider];
    let def = info.decls.get(method)?;
    let mut subst: HashMap<String, HirTy> = HashMap::new();
    if let Some((_, inner)) = bound.split_once('<') {
        let mut positional = info.params.iter();
        for part in inner.strip_suffix('>')?.split(", ") {
            let (name, ty) = match part.split_once(" = ") {
                Some((n, t)) => (n.to_owned(), t),
                None => (positional.next()?.clone(), part),
            };
            subst.insert(name, bound_arg_ty(ctx, ty)?);
        }
    }
    let mut rc = LowerCtx::new(ctx.env, &subst, None);
    rc.current_module.clone_from(&info.module);
    let resolve = |t: &Ty| {
        let mut t = t.clone();
        strip_self_assoc(&mut t);
        rc.resolve_ast_ty(&t)
    };
    let params = def
        .params
        .iter()
        .filter(|p| p.name != "self")
        .map(|p| p.ty.as_ref().map_or(HirTy::Unknown, resolve))
        .collect();
    Some((params, resolve(&sig_ret_ast(def))))
}

/// A type named in a bound key (see `bound_key`): a primitive, a struct
/// / enum table key, a `Struct3` / `Enum2` id, or any other type by the
/// mangled name `bound_key` recorded.
fn bound_arg_ty(ctx: &LowerCtx<'_>, name: &str) -> Option<HirTy> {
    if let Some(t) = super::resolve::bound_arg(name) {
        return Some(t);
    }
    let ast = Ty {
        kind: AstTyKind::Path(AstPath {
            segments: vec![rokc_ast::PathSegment {
                name: name.to_owned(),
                generics: Vec::new(),
            }],
            span: rokc_diagnostic::Span::default(),
        }),
        span: rokc_diagnostic::Span::default(),
    };
    if let t @ HirTy::Prim(_) = resolve_ty(&ast) {
        return Some(t);
    }
    if let Some(id) = ctx.lookup_struct(name) {
        return Some(HirTy::Struct(id));
    }
    if let Some(id) = ctx.lookup_enum(name) {
        return Some(HirTy::Enum(id));
    }
    if let Some(n) = name.strip_prefix("Struct").and_then(|n| n.parse().ok()) {
        return Some(HirTy::Struct(StructId(n)));
    }
    let n = name.strip_prefix("Enum")?.parse().ok()?;
    Some(HirTy::Enum(EnumId(n)))
}

/// `Self::Item` → `Item` (the associated type, bound by name).
fn strip_self_assoc(ty: &mut Ty) {
    match &mut ty.kind {
        AstTyKind::Path(p) => {
            if p.segments.len() >= 2 && p.segments[0].name == "Self" {
                p.segments.remove(0);
            }
            for s in &mut p.segments {
                s.generics.iter_mut().for_each(strip_self_assoc);
            }
        }
        AstTyKind::Sum(parts) | AstTyKind::Tuple(parts) => {
            parts.iter_mut().for_each(strip_self_assoc);
        }
        AstTyKind::Fn(args, ret, _) => {
            args.iter_mut().for_each(strip_self_assoc);
            strip_self_assoc(ret);
        }
        AstTyKind::Throws { ok, err } => {
            strip_self_assoc(ok);
            strip_self_assoc(err);
        }
        AstTyKind::Array(elem, _) => strip_self_assoc(elem),
        _ => {}
    }
}

/// One dispatcher function per (`any` type, method): its body — a
/// `match` on the tag over every stored type that implements the
/// bounds — is built by `build_any_dispatchers` once the program's
/// stored types are known (closed world).
#[derive(Clone)]
pub(super) struct AnyDispatch {
    pub(super) id: FunctionId,
    recv_ty: HirTy,
    /// The trait declaring `method` (each implementor's method of it,
    /// whatever other traits share the name).
    trait_key: String,
    method: String,
    params: Vec<HirTy>,
    ret: HirTy,
    span: rokc_diagnostic::Span,
}

pub(super) fn any_dispatcher(
    ctx: &LowerCtx<'_>,
    recv_ty: &HirTy,
    trait_key: &str,
    method: &str,
    sig: &FnSig,
    span: rokc_diagnostic::Span,
) -> FunctionId {
    let mut all = ctx.env.sink.any_dispatch.borrow_mut();
    if let Some(d) = all
        .iter()
        .find(|d| d.recv_ty == *recv_ty && d.method == method && d.trait_key == trait_key)
    {
        return d.id;
    }
    let id = FunctionId(ctx.env.sink.next_id.get());
    ctx.env.sink.next_id.set(id.0 + 1);
    all.push(AnyDispatch {
        id,
        recv_ty: recv_ty.clone(),
        trait_key: trait_key.to_owned(),
        method: method.to_owned(),
        params: sig.param_tys[1..].to_vec(),
        ret: sig.ret_ty.clone(),
        span,
    });
    id
}

/// `any` across separately compiled packages (spec 904). Dispatchers are
/// closed-world, so (1) each one gets a stable symbol `rok.any.<hash>`
/// (weak in a prebuilt library, strong in its user, which wins), and
/// (2) a prebuilt library `lib` describes its stored types and its
/// dispatchers as rok source `seeds` for its RHIR: compiled by its user,
/// they put the library's types into the user's dispatchers and make
/// the user build every dispatcher the library calls.
/// Returns `(seeds as (module, text), dispatcher exports)`.
// A seed names its types as `ty_name` prints them; a type it
// can't name (closures) is skipped, and one not visible from the
// module of its first `lib` type fails the user's build.
#[allow(clippy::type_complexity)] // two lists, each read once
pub(super) fn any_link(
    env: &Env<'_>,
    lib: Option<&str>,
) -> (Vec<(String, String)>, Vec<(FunctionId, String)>) {
    let empty = HashMap::new();
    let c = LowerCtx::new(env, &empty, None);
    let dispatch = env.sink.any_dispatch.borrow().clone();
    let names = |tys: &[HirTy]| tys.iter().map(|t| c.ty_name(t)).collect::<Vec<_>>();
    let exports = dispatch
        .iter()
        .map(|d| {
            let key = format!(
                "{}|{}|{}|{}|{}",
                c.ty_name(&d.recv_ty),
                d.trait_key,
                d.method,
                names(&d.params).join(","),
                c.ty_name(&d.ret)
            );
            (
                d.id,
                format!("rok.any.{:016x}", rokc_core::hash::fnv(key.as_bytes())),
            )
        })
        .collect();
    let Some(lib) = lib else {
        return (Vec::new(), exports);
    };
    let under = format!("{lib}::");
    // The module of the first `lib` item a type names (else the root).
    let home = |text: &str| -> String {
        text.split(|ch: char| !(ch.is_alphanumeric() || ch == '_' || ch == ':'))
            .find(|w| w.starts_with(&under))
            .map_or_else(|| lib.to_owned(), module_of)
    };
    let nameable = |s: &str| {
        !["closure", "{unknown}", "Self", "#", "GcBuf"]
            .iter()
            .any(|b| s.contains(b))
    };
    let mut seeds = Vec::new();
    let stored: Vec<HirTy> = env
        .sink
        .any_tags
        .borrow()
        .iter()
        .map(|(t, _)| t.clone())
        .collect();
    for t in stored {
        let name = c.ty_name(&t);
        if matches!(t, HirTy::AnyTrait(_)) || !nameable(&name) {
            continue;
        }
        let n = seeds.len();
        seeds.push((
            home(&name),
            format!(
                "#[export_name(\"__rok_seed_{lib}_{n}\")]\nfn __rok_seed_{n}(x: {name}) -> any {{ return x; }}\n"
            ),
        ));
    }
    for d in &dispatch {
        let recv = c.ty_name(&d.recv_ty);
        let params = names(&d.params);
        if !nameable(&recv) || !params.iter().all(|p| nameable(p)) {
            continue;
        }
        let n = seeds.len();
        let decl: Vec<String> = params
            .iter()
            .enumerate()
            .map(|(i, p)| format!(", a{i}: {p}"))
            .collect();
        let args: Vec<String> = (0..params.len()).map(|i| format!("a{i}")).collect();
        let (throws, try_) = if matches!(d.ret, HirTy::Throws { .. }) {
            (" throws", "try ")
        } else {
            ("", "")
        };
        // A `fmt` dispatcher renders text (`any_fmt`); an f-string makes it.
        let body = if d.method == "fmt" && is_fmt_trait(&c, &d.trait_key) {
            let q = if d.trait_key == c.lang_trait("debug_trait") {
                ":?"
            } else {
                ""
            };
            format!("let _ = f\"{{x{q}}}\";")
        } else {
            format!("{try_}x.{}({});", d.method, args.join(", "))
        };
        seeds.push((
            home(&recv),
            format!(
                "#[export_name(\"__rok_seed_{lib}_{n}\")]\nfn __rok_seed_{n}(x: {recv}{}){throws} {{ {body} }}\n",
                decl.concat(),
            ),
        ));
    }
    (seeds, exports)
}

/// Every type the program stores into an `any` slot that source can
/// name (`HirModule::any_types`), as `ty_name` prints it.
pub(super) fn any_types(env: &Env<'_>) -> Vec<String> {
    let empty = HashMap::new();
    let c = LowerCtx::new(env, &empty, None);
    let stored: Vec<HirTy> = env
        .sink
        .any_tags
        .borrow()
        .iter()
        .map(|(t, _)| t.clone())
        .collect();
    stored
        .iter()
        .filter(|t| !matches!(t, HirTy::AnyTrait(_)))
        .map(|t| c.ty_name(t))
        .filter(|s| {
            !["closure", "{unknown}", "Self", "#", "GcBuf"]
                .iter()
                .any(|b| s.contains(b))
        })
        .collect()
}

/// Build every dispatcher's body (see `AnyDispatch`). A body can
/// instantiate generic methods that store new types into `any` (or ask
/// for new dispatchers), so rebuild until nothing new appears.
pub(super) fn build_any_dispatchers(env: &Env<'_>) {
    loop {
        let (n_tags, todo) = (
            env.sink.any_tags.borrow().len(),
            env.sink.any_dispatch.borrow().clone(),
        );
        let fns: Vec<HirFunction> = todo.iter().map(|d| build_dispatcher(env, d)).collect();
        if env.sink.any_tags.borrow().len() == n_tags
            && env.sink.any_dispatch.borrow().len() == todo.len()
        {
            env.sink.extras.borrow_mut().extend(fns);
            return;
        }
    }
}

fn build_dispatcher(env: &Env<'_>, d: &AnyDispatch) -> HirFunction {
    let span = d.span;
    let empty = HashMap::new();
    let mut c = LowerCtx::new(env, &empty, None);
    let HirTy::AnyTrait(bounds) = &d.recv_ty else {
        unreachable!("dispatcher on a non-`any` type")
    };
    let mut params = vec![HirParam {
        name: "#recv".to_owned(),
        local: c.declare(Some("#recv".to_owned()), d.recv_ty.clone()),
        ty: d.recv_ty.clone(),
        by_ref: false,
    }];
    for (i, t) in d.params.iter().enumerate() {
        let name = format!("#a{i}");
        params.push(HirParam {
            name: name.clone(),
            local: c.declare(Some(name), t.clone()),
            ty: t.clone(),
            by_ref: false,
        });
    }
    let args: Vec<CallArg> = (0..d.params.len())
        .map(|i| {
            CallArg::Positional(Expr {
                kind: ExprKind::Path(AstPath {
                    segments: vec![rokc_ast::PathSegment {
                        name: format!("#a{i}"),
                        generics: Vec::new(),
                    }],
                    span,
                }),
                span,
            })
        })
        .collect();
    let stored: Vec<HirTy> = env
        .sink
        .any_tags
        .borrow()
        .iter()
        .map(|(t, _)| t.clone())
        .collect();
    let mut arms = Vec::new();
    for t in stored {
        if matches!(t, HirTy::AnyTrait(_)) || !bounds.iter().all(|b| c.implements_trait(&t, b, 0)) {
            continue;
        }
        c.push_scope();
        let x = c.declare(Some("#x".to_owned()), t.clone());
        let recv = hir_local(x, &t, span);
        let call = if d.method == "fmt" && is_fmt_trait(&c, &d.trait_key) {
            // The text, `f"{x}"` / `f"{x:?}"` (`any_fmt`).
            let debug = d.trait_key == c.lang_trait("debug_trait");
            let hole = rokc_ast::FStringPart::Hole {
                expr: Expr {
                    kind: ExprKind::Path(AstPath {
                        segments: vec![rokc_ast::PathSegment {
                            name: "#x".to_owned(),
                            generics: Vec::new(),
                        }],
                        span,
                    }),
                    span,
                },
                spec: if debug {
                    vec![rokc_ast::SpecPiece::Text("?".to_owned())]
                } else {
                    Vec::new()
                },
            };
            super::fstring::lower_fstring(&mut c, &[hole], span)
        } else if d.trait_key == super::reflect::REFLECT {
            super::reflect::dynamic(&mut c, recv, &d.method)
        } else {
            call_impl_method(
                &mut c,
                &t,
                &d.method,
                Some(&d.trait_key),
                Some(recv),
                &args,
                &d.method,
                span,
            )
            .unwrap_or_else(|| poison(span))
        };
        let body = coerce(&mut c, &d.ret, call, &|| {
            format!("`{}` of an `any` value", d.method)
        });
        c.pop_scope();
        arms.push(HirMatchArm {
            pat: HirPattern::SumVariant {
                sum_ty: d.recv_ty.clone(),
                variant_index: c.any_tag(&t),
                binder: Some(x),
                payload_ty: Some(t),
            },
            guard: None,
            body,
        });
    }
    let m = HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(hir_local(params[0].local, &d.recv_ty, span)),
            arms,
        },
        ty: d.ret.clone(),
        span,
    };
    let body = if d.ret == HirTy::Unit {
        HirBlock {
            stmts: vec![HirStmt::Expr(m)],
            trailing: None,
            label: None,
        }
    } else {
        HirBlock {
            stmts: Vec::new(),
            trailing: Some(m),
            label: None,
        }
    };
    HirFunction {
        id: d.id,
        def_id: None,
        name: format!("__any_{}_{}", d.method, d.id.0),
        params,
        locals: c.into_locals(),
        ret_ty: d.ret.clone(),
        body: Some(body),
        is_async: false,
        is_generator: false,
        span,
        facts: rokc_ir_common::FnFacts {
            role: rokc_ir_common::FnRole::AnyDispatcher,
            ..rokc_ir_common::FnFacts::default()
        },
    }
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
) -> &'e [GenericMethod] {
    let (name, generic_args) = match ty {
        HirTy::Struct(id) => {
            let d = ctx.struct_def(*id);
            (d.name, d.generic_args)
        }
        HirTy::Enum(id) => {
            let d = ctx.enum_def(*id);
            (d.name, d.generic_args)
        }
        HirTy::Prim(p) => (p.name().to_owned(), Vec::new()),
        _ => return &[],
    };
    let base = if generic_args.is_empty() {
        name
    } else {
        enum_base_name(&name).to_owned()
    };
    ctx.env
        .generic_methods
        .get(&(base, method.to_owned()))
        .map_or(&[], Vec::as_slice)
}

/// A method candidate for a receiver type: a concrete function or a
/// generic template.
#[derive(Clone, Copy)]
pub(super) enum MethodPick<'e> {
    Concrete(FunctionId),
    Generic(&'e GenericMethod),
}

/// Method `method` of type `ty` (spec 3.5.2 / 4.9.6), from a trait
/// `trait_key` when given: an inherent method first; else the trait
/// methods, where a trait defined in, or explicitly `use`d by, the
/// current package beats one visible only through the implicit
/// `rok::core::**`; any other tie is an ambiguity error.
pub(super) fn pick_method<'e>(
    ctx: &LowerCtx<'e>,
    ty: &HirTy,
    method: &str,
    trait_key: Option<&str>,
) -> Result<Option<MethodPick<'e>>, String> {
    let env = ctx.env;
    let mut cands: Vec<(Option<&'e str>, MethodPick<'e>)> = Vec::new();
    if let Some(ids) =
        method_target_for(ty).and_then(|t| env.method_table.get(&(t, method.to_owned())))
    {
        for id in ids {
            let tn = env
                .method_info
                .get(id)
                .and_then(|i| i.trait_name.as_deref());
            cands.push((tn, MethodPick::Concrete(*id)));
        }
    }
    for gm in generic_method_for(ctx, ty, method) {
        cands.push((gm.info.trait_name.as_deref(), MethodPick::Generic(gm)));
    }
    for gi in &env.generic_trait_impls {
        if let Some(gm) = gi.methods.get(method) {
            if ctx.generic_impl_subst(gi, ty, 0).is_some() {
                // An empty key: a generic inherent impl (`impl<..> [T; N]`).
                let key = Some(gi.trait_key.as_str()).filter(|k| !k.is_empty());
                cands.push((key, MethodPick::Generic(gm)));
            }
        }
    }
    if let Some(k) = trait_key {
        cands.retain(|(t, _)| *t == Some(k));
    }
    if let Some((_, p)) = cands.iter().find(|(t, _)| t.is_none()) {
        return Ok(Some(*p));
    }
    if cands.len() > 1 {
        let own: Vec<_> = cands
            .iter()
            .filter(|(t, _)| t.is_some_and(|t| !core_only_trait(ctx, t)))
            .copied()
            .collect();
        if own.len() == 1 {
            return Ok(Some(own[0].1));
        }
        let mut traits: Vec<String> = cands
            .iter()
            .map(|(t, _)| format!("`{}`", t.unwrap_or_default()))
            .collect();
        traits.sort();
        traits.dedup();
        let leaf = |t: &str| leaf_name(t).to_owned();
        return Err(format!(
            "method `{method}` on `{}` is ambiguous: traits {} all provide it — call it as \
             `Trait::{method}(x)` (e.g. `{}::{method}(x)`) (spec 4.9.6)",
            ctx.ty_name(ty),
            traits.join(", "),
            leaf(cands[0].0.unwrap_or_default())
        ));
    }
    Ok(cands.first().map(|(_, p)| *p))
}

/// Is trait `key` from another package and not named by a `use` here
/// (a core trait seen from user code only through the implicit
/// `use rok::core::**`, or a user trait seen from core)?
fn core_only_trait(ctx: &LowerCtx<'_>, key: &str) -> bool {
    let pkg = super::resolve::package_of;
    if pkg(&module_of(key)) == pkg(&ctx.current_module) {
        return false;
    }
    let named = |e: &crate::uses::UseEntry| match e {
        crate::uses::UseEntry::Single { full, .. } => full == key,
        crate::uses::UseEntry::Glob { prefix } => module_of(key) == *prefix,
        crate::uses::UseEntry::GlobDeep { prefix } => key.starts_with(&format!("{prefix}::")),
    };
    !ctx.local_uses
        .iter()
        .flatten()
        .chain(ctx.env.uses.get(&ctx.current_module).into_iter().flatten())
        .any(named)
}

/// Method `method` of the generic trait impl covering `ty` (`impl<T>
/// Tr for Box<T>`, blanket `impl<T: B> Tr for T`). Two covering impls
/// are an error.
pub(super) fn generic_trait_method_for<'e>(
    ctx: &LowerCtx<'e>,
    ty: &HirTy,
    method: &str,
) -> Result<Option<&'e GenericMethod>, String> {
    let env = ctx.env;
    let hits: Vec<&'e GenericTraitImpl> = env
        .generic_trait_impls
        .iter()
        .filter(|gi| gi.methods.contains_key(method))
        .filter(|gi| ctx.generic_impl_subst(gi, ty, 0).is_some())
        .collect();
    match hits.as_slice() {
        [] => Ok(None),
        [gi] => Ok(gi.methods.get(method)),
        _ => Err(format!(
            "method `{method}` on `{}` is ambiguous: generic impls of {} all cover it",
            ctx.ty_name(ty),
            hits.iter()
                .map(|gi| format!("`{}`", gi.trait_key))
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
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
        HirTy::Fn(a, r, b) => {
            if b.iter().any(|k| k == rokc_ast::UNSAFE_FN_MARK) {
                check_unsafe_call(ctx, "(unsafe fn value)");
            }
            (a, *r, None)
        }
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
        param_refs: Vec::new(),
        variadic: false,
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
/// Spec 4.15.3: an `unsafe fn` (or C function) is called only from an
/// `unsafe fn` body or an `unsafe { }` block.
fn check_unsafe_call(ctx: &LowerCtx<'_>, callee: &str) {
    if ctx.unsafe_depth == 0 {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "call to unsafe function `{}` outside an `unsafe` block or `unsafe fn` \
                 (spec 4.15; C functions are implicitly unsafe)",
                leaf_name(callee)
            ),
        );
    }
}

pub(super) fn call_generic(
    ctx: &mut LowerCtx<'_>,
    def: &FnDef,
    self_ty: Option<&Ty>,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    callee: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    call_generic_on(ctx, def, self_ty, None, receiver, args, callee, span)
}

/// `call_generic` with `Self` known up front (`self_hint`): a generic
/// impl's static method binds the impl's parameters from it.
#[allow(clippy::too_many_arguments)]
pub(super) fn call_generic_on(
    ctx: &mut LowerCtx<'_>,
    def: &FnDef,
    self_ty: Option<&Ty>,
    self_hint: Option<&HirTy>,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    callee: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    if args
        .iter()
        .all(|a| matches!(a, CallArg::Positional(_) | CallArg::Ref(_)))
    {
        return call_generic_positional(ctx, def, self_ty, self_hint, receiver, args, callee, span);
    }
    let mut lets = Vec::new();
    let offset = usize::from(receiver.is_some());
    let Some(args) = generic_positional_args(ctx, def, offset, args, callee, &mut lets) else {
        return poison(span);
    };
    let call = call_generic_positional(ctx, def, self_ty, self_hint, receiver, &args, callee, span);
    if lets.is_empty() {
        return call;
    }
    HirExpr {
        ty: call.ty.clone(),
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: lets,
            trailing: Some(call),
            label: None,
        })),
        span,
    }
}

/// A generic call's named (`name: v`) and spread (`..t`) arguments as
/// positional ones in parameter order (spec 4.1): a skipped parameter
/// takes its default, a spread tuple is evaluated once into a temp (a
/// `let` in `lets`) whose fields fill consecutive slots, a trailing
/// closure fills the last parameter (4.8.3). `offset` parameters (the
/// receiver) come first. `None` after an error.
fn generic_positional_args(
    ctx: &mut LowerCtx<'_>,
    def: &FnDef,
    offset: usize,
    args: &[CallArg],
    callee: &str,
    lets: &mut Vec<HirStmt>,
) -> Option<Vec<CallArg>> {
    let params = def.params.get(offset..).unwrap_or_default();
    let n = params.len();
    let mut slots: Vec<Option<CallArg>> = vec![None; n];
    let (mut next, mut extra) = (0usize, 0usize);
    // Spec 4.2.6: a variadic `...T` takes every argument past its slot
    // (spread tuple fields too); `call_generic_positional` wraps them.
    let variadic = params.last().is_some_and(|p| p.variadic);
    let mut rest: Vec<CallArg> = Vec::new();
    let mut ok = true;
    for a in args {
        match a {
            CallArg::Positional(e)
                if !variadic && n > next && slots[n - 1].is_none() && is_trailing_closure(e) =>
            {
                slots[n - 1] = Some(a.clone());
                next = n;
            }
            CallArg::Positional(_) | CallArg::Ref(_) => {
                match slots.get_mut(next) {
                    Some(s) => *s = Some(a.clone()),
                    None if variadic => rest.push(a.clone()),
                    None => extra += 1,
                }
                next += 1;
            }
            CallArg::Named { name, value } => match params.iter().position(|p| p.name == *name) {
                Some(i) if slots[i].is_none() => {
                    slots[i] = Some(CallArg::Positional(value.clone()));
                }
                Some(_) => {
                    ok = false;
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("argument `{name}` provided more than once (spec 4.1)"),
                    );
                }
                None => {
                    ok = false;
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("`{callee}` has no parameter named `{name}` (spec 4.1)"),
                    );
                }
            },
            // In the variadic slot: `lower_variadic` expands it.
            CallArg::Spread(_) if variadic && next + 1 >= n => {
                match slots.get_mut(next) {
                    Some(s) => *s = Some(a.clone()),
                    None => rest.push(a.clone()),
                }
                next += 1;
            }
            CallArg::Spread(e) => {
                let h = lower_expected(ctx, e, HirTy::Unknown);
                let HirTy::Tuple(parts) = h.ty.clone() else {
                    if h.ty != HirTy::Unknown {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "spread `f(..x)` needs a tuple value, found `{}` (spec 4.1)",
                                ctx.ty_name(&h.ty)
                            ),
                        );
                    }
                    return None;
                };
                let name = format!("#spread{}", ctx.locals.len());
                let local = ctx.declare(Some(name.clone()), h.ty.clone());
                lets.push(HirStmt::Let { local, init: h });
                for k in 0..parts.len() {
                    let field = Expr {
                        kind: ExprKind::TupleField(
                            Box::new(super::throws::path_expr(&name, e.span)),
                            u32::try_from(k).expect("tuple field overflow"),
                        ),
                        span: e.span,
                    };
                    match slots.get_mut(next) {
                        Some(s) => *s = Some(CallArg::Positional(field)),
                        None if variadic => rest.push(CallArg::Positional(field)),
                        None => extra += 1,
                    }
                    next += 1;
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
        return None;
    }
    let mut out = Vec::with_capacity(n);
    for (slot, p) in slots.into_iter().zip(params) {
        match (slot, &p.default) {
            (Some(a), _) => out.push(a),
            (None, _) if p.variadic => {}
            (None, Some(d)) => {
                out.push(CallArg::Positional(in_module(&module_of(&def.name), d.clone())));
            }
            (None, None) => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!("missing argument `{}` in call to `{callee}`", p.name),
                );
                ok = false;
            }
        }
    }
    out.extend(rest);
    ok.then_some(out)
}

/// `call_generic_on` with positional (and `ref`) arguments only.
#[allow(clippy::too_many_arguments)]
fn call_generic_positional(
    ctx: &mut LowerCtx<'_>,
    def: &FnDef,
    self_ty: Option<&Ty>,
    self_hint: Option<&HirTy>,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    callee: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    if def.is_unsafe {
        check_unsafe_call(ctx, callee);
    }
    // Spec 4.2.5: the trailing arguments of a variadic `...T` call are
    // one `Slice<T>` argument, built once the other arguments are in
    // (`lower_variadic`).
    let (args, tail) = match def.params.last().filter(|p| p.variadic) {
        Some(_) => {
            let k = (def.params.len() - 1).saturating_sub(usize::from(receiver.is_some()));
            args.split_at_checked(k)
                .map_or((args, None), |(a, t)| (a, Some(t)))
        }
        None => (args, None),
    };
    // A method's `Self` is its receiver's type.
    let recv_ty = receiver
        .as_ref()
        .filter(|_| self_hint.is_none() && self_ty.is_some())
        .map(|r| r.ty.clone());
    let self_hint = self_hint.or(recv_ty.as_ref());
    // Explicit `::<..>` arguments apply to this call only, not to the
    // generic calls inside its arguments.
    let explicit = std::mem::take(&mut ctx.explicit_generics);
    let mut subst: HashMap<String, HirTy> = explicit.clone();
    if let (Some(t), Some(hint)) = (self_ty, self_hint) {
        bind_self(ctx, def, t, hint, &mut subst);
    }
    let mut lowered: Vec<HirExpr> = Vec::with_capacity(args.len() + 1);
    let mut places: Vec<Option<HirExpr>> = vec![None; def.params.len()];
    let has_receiver = receiver.is_some();
    let explicit_recv = ctx.explicit_recv.take();
    if let Some(r) = receiver {
        let by_ref = def.params.first().is_some_and(|p| p.by_ref);
        check_path_receiver(ctx, explicit_recv, by_ref, &r, "self", callee);
        bind_from_arg(ctx, def, self_ty, 0, &r.ty, &mut subst);
        if let (Some(p), true) = (
            places.first_mut(),
            def.params.first().is_some_and(|p| p.by_ref),
        ) {
            *p = Some(r.clone());
        }
        lowered.push(r);
    }
    let mut reads: Vec<(usize, Vec<String>)> = Vec::new();
    let mut deferred: Vec<(usize, &Expr)> = Vec::new();
    for a in args {
        let (CallArg::Positional(e) | CallArg::Ref(e)) = a else {
            unreachable!("named / spread arguments are made positional first")
        };
        let i = lowered.len();
        let is_ref = matches!(a, CallArg::Ref(_));
        let by_ref = def.params.get(i).is_some_and(|p| p.by_ref);
        if is_ref != by_ref {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                if is_ref {
                    format!(
                        "argument {} of `{callee}` is passed with `ref`, but the parameter is \
                         not `ref` (spec 4.7.3)",
                        i + 1
                    )
                } else {
                    format!(
                        "parameter {} of `{callee}` is `ref` — pass `ref x` at the call site \
                         (spec 4.7.3)",
                        i + 1
                    )
                },
            );
        }
        if !is_ref {
            reads.push((i, crate::walk::free_names(&[], e)));
        }
        let hint = generic_arg_hint(ctx, def, &subst, i, e);
        // An untyped literal for a still-open `T` waits for the other
        // arguments: `range(0, n)` with `n: i64` binds `T = i64`.
        // ... only when a sibling argument of the same bare `T` can bind
        // it (`fold(0, |a, x| ..)` keeps `B` from the literal).
        let bare = |k: usize| {
            def.params
                .get(k)
                .and_then(|p| p.ty.as_ref())
                .and_then(|t| match &t.kind {
                    rokc_ast::TyKind::Path(p) if p.segments.len() == 1 => {
                        Some(p.segments[0].name.as_str())
                    }
                    _ => None,
                })
                .filter(|n| {
                    def.generics.params.iter().any(
                        |g| matches!(g, rokc_ast::GenericParam::Type { name, .. } if name == n),
                    )
                })
        };
        let offset = usize::from(has_receiver);
        let bare_param = bare(i).is_some_and(|n| {
            args.iter().enumerate().any(|(j, a)| {
                j + offset != i
                    && bare(j + offset) == Some(n)
                    && matches!(a, CallArg::Positional(x) if !is_untyped_literal(x))
            })
        });
        if hint == HirTy::Unknown && !is_ref && bare_param && is_untyped_literal(e) {
            deferred.push((i, e));
            lowered.push(poison(e.span));
            continue;
        }
        let h = lower_expected(ctx, e, hint);
        bind_from_arg(ctx, def, self_ty, i, &h.ty, &mut subst);
        if is_ref && super::mono::place_root(&h).is_some() {
            if let Some(p) = places.get_mut(i) {
                *p = Some(h.clone());
            }
        } else if is_ref && h.ty != HirTy::Unknown {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`ref` argument {} of `{callee}` must name a variable or a field of one \
                     (spec 4.7)",
                    i + 1
                ),
            );
        }
        lowered.push(h);
    }
    for (i, e) in deferred {
        let hint = generic_arg_hint(ctx, def, &subst, i, e);
        let h = lower_expected(ctx, e, hint);
        bind_from_arg(ctx, def, self_ty, i, &h.ty, &mut subst);
        lowered[i] = h;
    }
    // Missing trailing arguments take their declared defaults, lowered
    // at the call site like a non-generic call's (`ordering = SeqCst`).
    while let Some(d) = def
        .params
        .get(lowered.len())
        .and_then(|p| p.default.clone())
        .map(|d| in_module(&module_of(&def.name), d))
    {
        let h = lower_expected(ctx, &d, HirTy::Unknown);
        bind_from_arg(ctx, def, self_ty, lowered.len(), &h.ty, &mut subst);
        lowered.push(h);
    }
    if let Some(tail) = tail.filter(|_| lowered.len() + 1 == def.params.len()) {
        let i = lowered.len();
        let hint = generic_arg_hint(ctx, def, &subst, i, &super::throws::path_expr("#", span));
        let elem = variadic_elem(ctx, &hint);
        let parts = tail
            .iter()
            .filter_map(|a| match a {
                CallArg::Positional(e) | CallArg::Ref(e) => Some(VarPart::Arg(e)),
                CallArg::Spread(e) => Some(VarPart::Spread(e)),
                CallArg::Named { .. } => None,
            })
            .collect();
        let h = lower_variadic(ctx, elem, parts, span);
        bind_from_arg(ctx, def, self_ty, i, &h.ty, &mut subst);
        lowered.push(h);
    }
    check_ref_exclusive(ctx, callee, &lowered, &places, &reads, has_receiver);
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
    ctx.explicit_generics = explicit;
    let mono = monomorphize_on(ctx, def, self_ty, self_hint, &lowered, span);
    ctx.explicit_generics.clear();
    let Some((mono_id, ret_ty)) = mono else {
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
    let out = ctx.env.sink.ref_out.borrow().get(&mono_id).cloned();
    if let Some(out) = out {
        let tys: Vec<HirTy> = out.refs.iter().map(|(_, t)| t.clone()).collect();
        let call = HirExpr {
            kind: HirExprKind::Call {
                callee: mono_id,
                args: lowered,
            },
            ty: super::mono::ref_packed(&out.ret, &tys),
            span,
        };
        return super::mono::ref_unpack(ctx, call, &out, &places);
    }
    HirExpr {
        kind: HirExprKind::Call {
            callee: mono_id,
            args: lowered,
        },
        ty: ret_ty,
        span,
    }
}

/// The expected type of argument `i` of a generic call, under the
/// parameters bound so far.
fn generic_arg_hint(
    ctx: &LowerCtx<'_>,
    def: &FnDef,
    subst: &HashMap<String, HirTy>,
    i: usize,
    e: &Expr,
) -> HirTy {
    let hint = def
        .params
        .get(i)
        .and_then(|p| p.ty.as_ref())
        .map_or(HirTy::Unknown, |t| {
            // Type params not bound yet stay opaque paths — never
            // resolved as same-named types visible from `def`.
            let mut partial = subst.clone();
            for gp in &def.generics.params {
                match gp {
                    rokc_ast::GenericParam::Type { name, .. } => {
                        partial
                            .entry(name.clone())
                            .or_insert_with(|| HirTy::Path(vec![name.clone()]));
                    }
                    // An unbound const parameter: `#N` (no value yet).
                    rokc_ast::GenericParam::Const { name, .. } => {
                        partial
                            .entry(name.clone())
                            .or_insert_with(|| HirTy::Path(vec![format!("#{name}")]));
                    }
                }
            }
            let mut ty = resolve_in_mono(ctx, def, &partial, None, t);
            erase_unbound_errors(&mut ty);
            let mut leftover = Vec::new();
            collect_unknown_paths(&ty, &mut leftover);
            let open = |t: &HirTy| {
                let mut l = Vec::new();
                collect_unknown_paths(t, &mut l);
                !l.is_empty()
            };
            match ty {
                _ if leftover.is_empty() => ty,
                // `fn(T) -> U` with `U` still open: the closure
                // still learns its parameter types; `U` binds from
                // the closure afterwards.
                HirTy::Fn(args, ret, b) => HirTy::Fn(
                    args.into_iter()
                        .map(|a| if open(&a) { HirTy::Unknown } else { a })
                        .collect(),
                    Box::new(if open(&ret) { HirTy::Unknown } else { *ret }),
                    b,
                ),
                _ => HirTy::Unknown,
            }
        });
    // `[T; N]` with `N` unbound and an array literal argument: the
    // literal's length is the array's (spec 2.11.6), else it would
    // default to a `List`.
    let hint = match (
        &hint,
        def.params.get(i).and_then(|p| p.ty.as_ref()),
        &e.kind,
    ) {
        (HirTy::Unknown, Some(t), ExprKind::List(items)) => match &t.kind {
            rokc_ast::TyKind::Array(elem, _) => {
                let mut et = resolve_in_mono(ctx, def, subst, None, elem);
                let mut open = Vec::new();
                collect_unknown_paths(&et, &mut open);
                if !open.is_empty() {
                    et = HirTy::Unknown;
                }
                u32::try_from(items.len()).map_or(hint, |n| HirTy::Array(Box::new(et), n))
            }
            _ => hint,
        },
        _ => hint,
    };
    hint
}

/// `f::<T, 3>(..)`: bind explicit generic arguments by position into
/// `ctx.explicit_generics` for the next generic call. `false` after
/// reporting too many.
fn bind_explicit_generics(
    ctx: &mut LowerCtx<'_>,
    def: &FnDef,
    explicit: &[rokc_ast::Ty],
    full: &str,
) -> bool {
    if explicit.len() > def.generics.params.len() {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "`{full}` takes {} generic argument(s) but {} were supplied",
                def.generics.params.len(),
                explicit.len()
            ),
        );
        return false;
    }
    // Seeded by a literal handler call (`lower_magic`); empty otherwise.
    let mut bound = std::mem::take(&mut ctx.explicit_generics);
    for (gp, t) in def.generics.params.iter().zip(explicit) {
        let (rokc_ast::GenericParam::Type { name, .. }
        | rokc_ast::GenericParam::Const { name, .. }) = gp;
        bound.insert(name.clone(), ctx.resolve_ast_ty(t));
    }
    ctx.explicit_generics = bound;
    true
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
    let self_segs = self_path_segs(ctx, p);
    let segs: Vec<&str> = self_segs.iter().map(String::as_str).collect();
    let display = segs.join("::");

    // A local of `fn(...)` / closure type shadows items.
    if let [name] = segs.as_slice() {
        if let Some(local) = ctx.lookup(name) {
            let callee_h = ctx.read_local(local, callee.span);
            return call_value(ctx, callee_h, args, span);
        }
    }

    // Free function / extern / re-export, module-aware.
    if let Some(full) = ctx.resolve_fn_name(&segs) {
        ctx.check_item_visible(&full, "function");
        let sig = ctx.env.fn_table[&full].clone();
        return call_sig(ctx, &sig, &full, None, args, span);
    }

    // Generic function — monomorphize on the argument types.
    if let Some(full) = ctx.resolve_generic_fn_name(&segs) {
        ctx.check_item_visible(&full, "function");
        let generic_def = ctx.env.generic_fns[&full];
        if let Some(op) = buf_intrinsic(generic_def) {
            if generic_def.is_unsafe {
                check_unsafe_call(ctx, &full);
            }
            let targs = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
            if let Some(raw) = lower_raw_intrinsic(ctx, op, targs, args, span) {
                return raw;
            }
            if let Some(atomic) = op.strip_prefix("atomic_") {
                return lower_atomic_intrinsic(ctx, atomic, args, span);
            }
            return lower_buf_intrinsic(ctx, op, args, span);
        }
        let explicit = p.segments.last().map_or(&[][..], |s| s.generics.as_slice());
        if !bind_explicit_generics(ctx, generic_def, explicit, &full) {
            return poison(span);
        }
        return call_generic(ctx, generic_def, None, None, args, &full, span);
    }

    // `Box::get(b)` / `Box::new(v)` — generic-impl method by path.
    if let Some((method, ty_segs)) = segs.split_last() {
        let env = ctx.env;
        let gm = ctx
            .canon_type(ty_segs)
            .filter(|_| !ty_segs.is_empty())
            .and_then(|full| env.generic_methods.get(&(full, (*method).to_owned())))
            .and_then(|v| {
                v.iter()
                    .find(|g| g.info.trait_name.is_none())
                    .or_else(|| v.first())
            });
        if let Some(gm) = gm {
            check_method_info_visible(ctx, &gm.info, method);
            // `Box::<i32>::new(v)`: the type's arguments fix `Self`;
            // `Box::m::<U>(..)`: the method's own.
            let n = p.segments.len();
            let self_hint = (!p.segments[n - 2].generics.is_empty()).then(|| {
                ctx.resolve_ast_ty(&Ty {
                    kind: AstTyKind::Path(rokc_ast::Path {
                        segments: p.segments[..n - 1].to_vec(),
                        span: p.span,
                    }),
                    span: p.span,
                })
            });
            // `let a: Atomic<i64> = Atomic::new(0)`: a constructor that
            // returns `Self` takes `Self` from the expected type.
            let returns_self = gm.def.ret_ty.as_ref().is_some_and(|t| {
                matches!(&t.kind, AstTyKind::Path(rp) if rp.segments.len() == 1
                    && (rp.segments[0].name == "Self" || rp.segments[0].name == *ty_segs[ty_segs.len() - 1]))
            });
            let self_hint = self_hint.or_else(|| {
                let full = ctx.canon_type(ty_segs)?;
                ctx.current_expected().cloned().filter(|t| {
                    returns_self
                        && matches!(t, HirTy::Struct(id)
                            if enum_base_name(&ctx.struct_def(*id).name) == full)
                })
            });
            match bind_explicit(
                ctx,
                &gm.def,
                Some(&gm.self_ty),
                &p.segments[n - 1].generics,
                method,
            ) {
                Ok(bound) => ctx.explicit_generics = bound,
                Err(msg) => {
                    discard_args(ctx, args);
                    return ctx.error_expr(span, msg);
                }
            }
            return call_generic_on(
                ctx,
                &gm.def,
                Some(&gm.self_ty),
                self_hint.as_ref(),
                None,
                args,
                &display,
                span,
            );
        }
    }

    // `Pair(3, 4)` of a generic tuple struct: a struct literal with the
    // positional field names, which infers the instantiation.
    let generic_tuple = ctx.canon_type(&segs).is_some_and(|full| {
        ctx.lookup_struct(&full).is_none()
            && ctx
                .env
                .generic_structs
                .get(&full)
                .is_some_and(|d| matches!(d.kind, rokc_ast::StructKind::Tuple(_)))
    });
    if generic_tuple && args.iter().all(|a| matches!(a, CallArg::Positional(_))) {
        let fields: Vec<(String, Expr)> = args
            .iter()
            .enumerate()
            .filter_map(|(i, a)| match a {
                CallArg::Positional(e) => Some((i.to_string(), e.clone())),
                _ => None,
            })
            .collect();
        return lower_struct_init(ctx, p, &fields, span);
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
        // Spec 5.6: constructing needs every field visible here.
        def.fields
            .iter()
            .for_each(|f| ctx.check_field_visible(sid, &f.name));
        let sig = FnSig {
            id: FunctionId(u32::MAX),
            ret_ty: HirTy::Struct(sid),
            param_defaults: vec![None; def.fields.len()],
            param_tys: def.fields.iter().map(|f| f.ty.clone()).collect(),
            param_names: def.fields.iter().map(|f| f.name.clone()).collect(),
            param_refs: Vec::new(),
            variadic: false,
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
    // picked from the argument types. `EnumName::f(..)` naming no
    // variant is an associated function (below).
    let not_variant = enum_lacks_variant(ctx, &segs);
    let hint = ctx.current_expected().cloned();
    let is_generic_enum_base = ctx.enum_path(&segs).is_some_and(|(full, _)| {
        ctx.lookup_enum(&full).is_none() && !ctx.enum_instantiations(&full).is_empty()
    });
    let pre_args: Option<Vec<HirExpr>> = if !not_variant
        && is_generic_enum_base
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
    let res = if not_variant {
        EnumRes::NotEnum
    } else {
        resolve_enum_variant(ctx, &segs, hint.as_ref(), arg_tys.as_deref())
    };
    match res {
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
                    param_refs: Vec::new(),
                    variadic: false,
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
    // `Tr::m(x)`, `T::f()`, `i32::add(a, b)`, `Self::f()` — through the
    // trait's impls (concrete or generic) for the type.
    if let Some((method, ty_segs)) = segs.split_last().filter(|(_, t)| !t.is_empty()) {
        if let Some(r) =
            path_call_via_impls(ctx, &p.segments, ty_segs, method, args, &display, span)
        {
            return r;
        }
    }

    if let Some((method, ty_segs)) = segs.split_last() {
        if !ty_segs.is_empty() {
            if let Some(full) = ctx.canon_type(ty_segs) {
                let method = (*method).to_owned();
                if let Some(r) = named_type_overload(ctx, &full, &method, args, &display, span) {
                    return r;
                }
                let hits = match path_method_hits(ctx, &full, &method) {
                    Ok(h) => h,
                    Err(msg) => {
                        discard_args(ctx, args);
                        return ctx.error_expr(span, msg);
                    }
                };
                match hits.as_slice() {
                    [fn_id] => {
                        check_method_visible(ctx, *fn_id, &method);
                        let sig = ctx.sig_by_id(*fn_id);
                        return call_sig(ctx, &sig, &display, None, args, span);
                    }
                    [] => {
                        if let Some(r) =
                            named_type_call(ctx, &p.segments, &full, &method, args, span)
                        {
                            return r;
                        }
                        // A generic trait impl's method: `Self` is the
                        // expected type (`let b: Box<i32> = Box::zero()`)
                        // or else `self`'s.
                        let of_base = |ctx: &LowerCtx<'_>, t: &HirTy| match t {
                            HirTy::Struct(id) => enum_base_name(&ctx.struct_def(*id).name) == full,
                            HirTy::Enum(id) => enum_base_name(&ctx.enum_def(*id).name) == full,
                            _ => false,
                        };
                        if let Some(t) = ctx.current_expected().cloned().filter(|t| of_base(ctx, t))
                        {
                            if let Some(r) =
                                call_impl_method(ctx, &t, &method, None, None, args, &display, span)
                            {
                                return r;
                            }
                        }
                        if let Some((a @ (CallArg::Positional(e) | CallArg::Ref(e)), rest)) =
                            args.split_first()
                        {
                            let recv = lower_expected(ctx, e, HirTy::Unknown);
                            let t = recv.ty.clone();
                            if of_base(ctx, &t) {
                                ctx.explicit_recv = Some(matches!(a, CallArg::Ref(_)));
                                let r = call_impl_method(
                                    ctx,
                                    &t,
                                    &method,
                                    None,
                                    Some(recv),
                                    rest,
                                    &display,
                                    span,
                                );
                                ctx.explicit_recv = None;
                                if let Some(r) = r {
                                    return r;
                                }
                            }
                            discard_args(ctx, rest);
                        }
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

/// `Box::<f64>::f()` — the named instantiation's (generic-impl) method
/// — or `Reflect`'s `T::type_name()` / `size()` / `align()` of a struct /
/// enum (`List::<i64>::type_name()`).
fn named_type_call(
    ctx: &mut LowerCtx<'_>,
    segs: &[rokc_ast::PathSegment],
    full: &str,
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> Option<HirExpr> {
    let ty_segs = &segs[..segs.len() - 1];
    let own = if ty_segs.last().is_some_and(|s| !s.generics.is_empty()) {
        ctx.resolve_ast_ty(&Ty {
            kind: AstTyKind::Path(AstPath {
                segments: ty_segs.to_vec(),
                span,
            }),
            span,
        })
    } else {
        ctx.lookup_struct(full)
            .map(HirTy::Struct)
            .or_else(|| ctx.lookup_enum(full).map(HirTy::Enum))?
    };
    if let Some(r) = call_impl_method(ctx, &own, method, None, None, args, method, span) {
        return Some(r);
    }
    super::reflect::static_call(ctx, &own, method, args, span)
}

/// A range value (stdlib 2.7.4, spec 6.5.1): `a..b` / `a..=b` / `a..` /
/// `..b` / `..` call the `#[literal]` handler of that shape (core's
/// build `Range` / `RangeInclusive` / `RangeFrom` / `RangeTo` /
/// `RangeToInclusive` / `RangeFull`).
fn lower_range_value(
    ctx: &mut LowerCtx<'_>,
    start: Option<&Expr>,
    end: Option<&Expr>,
    inclusive: bool,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    use rokc_parser::Shape;
    let (shape, what) = match (start, end, inclusive) {
        (Some(_), Some(_), false) => (Shape::Range, "`a..b`"),
        (Some(_), Some(_), true) => (Shape::RangeInclusive, "`a..=b`"),
        (Some(_), None, _) => (Shape::RangeFrom, "`a..`"),
        (None, Some(_), false) => (Shape::RangeTo, "`..b`"),
        (None, Some(_), true) => (Shape::RangeToInclusive, "`..=b`"),
        (None, None, _) => (Shape::RangeFull, "`..`"),
    };
    let args = [start, end]
        .into_iter()
        .flatten()
        .map(|e| rokc_ast::LitArg::One(e.clone()))
        .collect();
    lower_shape(ctx, shape, args, what, span)
}

/// `Type::method` on a named struct / enum (or each instantiation of a
/// generic base): the concrete methods `pick_method` chooses.
fn path_method_hits(
    ctx: &LowerCtx<'_>,
    full: &str,
    method: &str,
) -> Result<Vec<FunctionId>, String> {
    let mut tys: Vec<HirTy> = Vec::new();
    if let Some(sid) = ctx.lookup_struct(full) {
        tys.push(HirTy::Struct(sid));
    } else if let Some(eid) = ctx.lookup_enum(full) {
        tys.push(HirTy::Enum(eid));
    } else {
        tys.extend(
            LowerCtx::instantiations(&ctx.env.struct_table, full)
                .into_iter()
                .map(HirTy::Struct),
        );
        tys.extend(ctx.enum_instantiations(full).into_iter().map(HirTy::Enum));
    }
    let mut hits = Vec::new();
    for ty in tys {
        if let Some(MethodPick::Concrete(id)) = pick_method(ctx, &ty, method, None)? {
            hits.push(id);
        }
    }
    Ok(hits)
}

/// `<T as Tr>::m(args)` (spec 2.13.4): `Tr`'s `m` of `T`; the first
/// argument fills `self` like `Tr::m(x)`.
fn qpath_call(
    ctx: &mut LowerCtx<'_>,
    segs: &[rokc_ast::PathSegment],
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let ([_, item], [self_ty, tr]) = (segs, segs[0].generics.as_slice()) else {
        discard_args(ctx, args);
        return poison(span);
    };
    let method = item.name.as_str();
    let t = ctx.resolve_ast_ty(self_ty);
    let key = match &tr.kind {
        AstTyKind::Path(tp) => {
            let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
            Some(ctx.env.names.trait_key(&segs, &ctx.current_module))
                .filter(|k| ctx.env.names.traits.contains(k))
        }
        _ => None,
    };
    let display = format!(
        "<{} as {}>::{method}",
        ctx.ty_name(&t),
        key.as_deref().unwrap_or("?")
    );
    let Some(key) = key else {
        discard_args(ctx, args);
        return ctx.error_expr(span, format!("`{display}`: not a trait after `as`"));
    };
    if method == "drop" && key == ctx.lang_trait("drop_method") {
        if let Some(e) = direct_drop_error(ctx, span) {
            discard_args(ctx, args);
            return e;
        }
    }
    let (recv, rest) = match args.split_first() {
        Some((a @ (CallArg::Positional(e) | CallArg::Ref(e)), rest)) => {
            let r = lower_expected(ctx, e, t.clone());
            ctx.explicit_recv = Some(matches!(a, CallArg::Ref(_)));
            (Some(r), rest)
        }
        _ => (None, args),
    };
    let call = call_impl_method(ctx, &t, method, Some(&key), recv, rest, &display, span);
    ctx.explicit_recv = None;
    call.unwrap_or_else(|| {
        ctx.error_expr(
            span,
            format!(
                "`{}` has no `{key}` impl providing `{method}`",
                ctx.ty_name(&t)
            ),
        )
    })
}

/// `Tr::m(..)` (`Self` = the first argument's type, else the expected
/// type), or `T::f(..)` / `i32::f(..)` / `Self::f(..)` on a type that is
/// not a named struct / enum. `None`: not such a path.
#[allow(clippy::too_many_arguments)]
fn path_call_via_impls(
    ctx: &mut LowerCtx<'_>,
    all_segs: &[rokc_ast::PathSegment],
    ty_segs: &[&str],
    method: &str,
    args: &[CallArg],
    display: &str,
    span: rokc_diagnostic::Span,
) -> Option<HirExpr> {
    let trait_key = ctx
        .canon_type(ty_segs)
        .filter(|f| ctx.env.names.traits.contains(f));
    if let Some(key) = trait_key {
        // A static method (`TryFrom::try_from(8)`) takes `Self` from the
        // expected type; its first argument is not `self`.
        let static_self = ctx
            .env
            .trait_info
            .get(&key)
            .and_then(|i| i.decls.get(method))
            .is_some_and(|d| d.params.first().is_none_or(|p| p.name != "self"))
            .then(|| ctx.current_expected().cloned())
            .flatten()
            .filter(|t| *t != HirTy::Unknown);
        let (recv, rest) = match args.split_first() {
            _ if static_self.is_some() => (None, args),
            Some((a @ (CallArg::Positional(e) | CallArg::Ref(e)), rest)) => {
                let r = lower_expected(ctx, e, HirTy::Unknown);
                ctx.explicit_recv = Some(matches!(a, CallArg::Ref(_)));
                (Some(r), rest)
            }
            _ => (None, args),
        };
        let self_ty = static_self
            .or_else(|| recv.as_ref().map(|r| r.ty.clone()))
            .or_else(|| ctx.current_expected().cloned())
            .filter(|t| *t != HirTy::Unknown);
        let Some(t) = self_ty else {
            discard_args(ctx, rest);
            return Some(ctx.error_expr(
                span,
                format!(
                    "cannot tell which type's `{key}` impl `{display}` calls — annotate the \
                     expected type"
                ),
            ));
        };
        if key == super::reflect::REFLECT {
            ctx.explicit_recv = None;
            if let Some(r) = super::reflect::trait_call(ctx, &t, recv.clone(), method, rest, span) {
                return Some(r);
            }
        }
        match (&t, &recv) {
            (HirTy::Sum(_), Some(r)) if method == "fmt" && key == ctx.lang_trait("debug_trait") => {
                ctx.explicit_recv = None;
                return Some(sum_structural_call(
                    ctx,
                    r.clone(),
                    method,
                    rest,
                    None,
                    span,
                ));
            }
            // `Trait::m(v)` on an `any` value: that trait's `m`, dispatched.
            (HirTy::AnyTrait(bounds), Some(r)) => {
                ctx.explicit_recv = None;
                let (bounds, r) = (bounds.clone(), r.clone());
                return Some(any_method_call(
                    ctx,
                    r,
                    &bounds,
                    method,
                    Some(&key),
                    rest,
                    span,
                ));
            }
            _ => {}
        }
        let call = call_impl_method(ctx, &t, method, Some(&key), recv, rest, display, span);
        ctx.explicit_recv = None;
        return Some(call.unwrap_or_else(|| {
            ctx.error_expr(
                span,
                format!(
                    "`{}` has no `{key}` impl providing `{method}`",
                    ctx.ty_name(&t)
                ),
            )
        }));
    }
    // Only paths the struct / enum lookup below can't take: a type
    // parameter, a primitive, `Self`.
    let [name] = ty_segs else {
        return None;
    };
    let is_type_param = ctx.ty_subst.contains_key(*name);
    let ty_ast = rokc_ast::Ty {
        kind: rokc_ast::TyKind::Path(rokc_ast::Path {
            segments: all_segs[..1].to_vec(),
            span,
        }),
        span,
    };
    let prim = matches!(crate::ty::resolve_ty(&ty_ast), HirTy::Prim(_));
    if !(is_type_param || prim || *name == "Self") {
        return None;
    }
    let t = ctx.resolve_ast_ty(&ty_ast);
    // `T::default()` for a `T | none` sum is `none` (stdlib 2.13).
    if let (HirTy::Sum(vs), "default", []) = (&t, method, args) {
        if let Some(i) = vs.iter().position(is_none_ty) {
            return Some(HirExpr {
                kind: HirExprKind::SumWrap {
                    sum_ty: t.clone(),
                    variant_index: u32::try_from(i).expect("variant overflow"),
                    value: None,
                },
                ty: t.clone(),
                span,
            });
        }
    }
    // `T::from_str(s)` under `T: FromStr` is the bound's method, not an
    // inherent one of the same name (`int::from_str(s, radix)`).
    let bound_key = ctx
        .ty_bounds
        .get(*name)
        .filter(|_| is_type_param)
        .and_then(|bs| {
            bs.iter()
                .map(|b| b.split('<').next().unwrap_or(b))
                .find(|k| {
                    ctx.env
                        .trait_info
                        .get(*k)
                        .is_some_and(|i| i.decls.contains_key(method))
                })
                .map(str::to_owned)
        });
    let call = call_impl_method(
        ctx,
        &t,
        method,
        bound_key.as_deref(),
        None,
        args,
        display,
        span,
    )
    .or_else(|| super::reflect::static_call(ctx, &t, method, args, span));
    Some(call.unwrap_or_else(|| {
        discard_args(ctx, args);
        ctx.error_expr(
            span,
            format!("no associated function `{method}` on `{}`", ctx.ty_name(&t)),
        )
    }))
}

/// Call `t`'s method `method` — of trait `trait_key` when given —
/// from a concrete impl, else a generic one. `recv` fills `self`.
#[allow(clippy::too_many_arguments)]
fn call_impl_method(
    ctx: &mut LowerCtx<'_>,
    t: &HirTy,
    method: &str,
    trait_key: Option<&str>,
    recv: Option<HirExpr>,
    args: &[CallArg],
    display: &str,
    span: rokc_diagnostic::Span,
) -> Option<HirExpr> {
    if let Some(call) = call_overload(ctx, t, method, trait_key, recv.clone(), args, display, span)
    {
        return Some(call);
    }
    let gm = match pick_method(ctx, t, method, trait_key) {
        Ok(Some(MethodPick::Concrete(fid))) => {
            check_method_visible(ctx, fid, method);
            let sig = ctx.sig_by_id(fid);
            return Some(call_sig(ctx, &sig, display, recv, args, span));
        }
        Ok(Some(MethodPick::Generic(gm))) => gm,
        Ok(None) => return None,
        Err(msg) => {
            discard_args(ctx, args);
            return Some(ctx.error_expr(span, msg));
        }
    };
    check_method_info_visible(ctx, &gm.info, method);
    // `Self` = `t` binds the impl's parameters, so a static method
    // (`fn zero() -> Self`) instantiates too.
    Some(call_generic_on(
        ctx,
        &gm.def,
        Some(&gm.self_ty),
        Some(t),
        recv,
        args,
        display,
        span,
    ))
}

/// `call_overload` on the struct / enum named `full`.
fn named_type_overload(
    ctx: &mut LowerCtx<'_>,
    full: &str,
    method: &str,
    args: &[CallArg],
    display: &str,
    span: rokc_diagnostic::Span,
) -> Option<HirExpr> {
    let t = ctx
        .lookup_struct(full)
        .map(HirTy::Struct)
        .or_else(|| ctx.lookup_enum(full).map(HirTy::Enum))?;
    call_overload(ctx, &t, method, None, None, args, display, span)
}

/// `T::from(x)` where `T` implements one generic trait several times
/// over (`From<i32>`, `From<i8>`): the impl whose first parameter is
/// the first argument's type. `None` when `method` is not overloaded
/// that way.
// Picks on the first argument only, by exact type; enough
// for `From` / `TryFrom`. Method-call and operator overloads still
// report the ambiguity.
#[allow(clippy::too_many_arguments)]
fn call_overload(
    ctx: &mut LowerCtx<'_>,
    t: &HirTy,
    method: &str,
    trait_key: Option<&str>,
    recv: Option<HirExpr>,
    args: &[CallArg],
    display: &str,
    span: rokc_diagnostic::Span,
) -> Option<HirExpr> {
    let ids =
        method_target_for(t).and_then(|k| ctx.env.method_table.get(&(k, method.to_owned())))?;
    let traits: Vec<Option<&str>> = ids
        .iter()
        .map(|id| {
            ctx.env
                .method_info
                .get(id)
                .and_then(|i| i.trait_name.as_deref())
        })
        .collect();
    let tn = *traits
        .iter()
        .flatten()
        .find(|t| trait_key.is_none_or(|k| k == **t))?;
    let ids: Vec<FunctionId> = ids
        .iter()
        .zip(&traits)
        .filter(|(_, t)| **t == Some(tn))
        .map(|(id, _)| *id)
        .collect();
    if ids.len() < 2 || traits.contains(&None) {
        return None;
    }
    let (first, rest) = match (recv, args) {
        (Some(r), _) => (r, args),
        (None, [CallArg::Positional(e), rest @ ..]) => {
            // An unsuffixed literal takes the impl it fits (spec 3.1.3).
            let params: Vec<HirTy> = ids
                .iter()
                .filter_map(|id| ctx.sig_by_id(*id).param_tys.first().cloned())
                .collect();
            match pick_literal_impl(ctx, e, &params) {
                Ok(Some(i)) => (lower_expected(ctx, e, params[i].clone()), rest),
                Ok(None) => (lower_expected(ctx, e, HirTy::Unknown), rest),
                Err(fits) => {
                    discard_args(ctx, args);
                    return Some(ctx.error_expr(
                        span,
                        format!(
                            "`{display}`: the literal fits several `{}` impls of `{}` ({fits}); \
                             add a suffix or `as`",
                            leaf_name(tn),
                            ctx.ty_name(t)
                        ),
                    ));
                }
            }
        }
        _ => return None,
    };
    let hit = ids
        .iter()
        .map(|id| ctx.sig_by_id(*id))
        .find(|sig| sig.param_tys.first() == Some(&first.ty));
    let Some(sig) = hit else {
        discard_args(ctx, rest);
        if first.ty == HirTy::Unknown {
            return Some(first);
        }
        return Some(ctx.error_expr(
            span,
            format!(
                "`{display}`: no `{}<{}>` impl for `{}`",
                leaf_name(tn),
                ctx.ty_name(&first.ty),
                ctx.ty_name(t)
            ),
        ));
    };
    check_method_visible(ctx, sig.id, method);
    Some(call_sig(ctx, &sig, display, Some(first), rest, span))
}

/// An unsuffixed numeric literal's value, read off the AST.
// Plain and negated literals only: `1 + 1` keeps its default type.
#[derive(Clone, Copy)]
enum LitVal {
    Int(i128),
    Float(f64),
}

fn untyped_lit_value(e: &Expr) -> Option<LitVal> {
    let (lit, neg) = match &e.kind {
        ExprKind::Literal(l) => (l, false),
        ExprKind::OpPrefix { op, operand } if op == "-" => match &operand.kind {
            ExprKind::Literal(l) => (l, true),
            _ => return None,
        },
        _ => return None,
    };
    if !is_untyped_literal(e) {
        return None;
    }
    match lit {
        AstLit::Int(t) => parse_int_literal(t).map(|(v, _)| LitVal::Int(if neg { -v } else { v })),
        AstLit::Float(t) => {
            let cleaned: String = t.chars().filter(|c| *c != '_').collect();
            cleaned.parse::<f64>().ok().map(LitVal::Float)
        }
        _ => None,
    }
}

/// Whether a literal of value `v` can take type `ty`: an integer any
/// integer type it is in range of (or `int`), a float `f32` / `f64` it
/// stays finite in (or `float`).
fn literal_fits(ctx: &LowerCtx<'_>, v: LitVal, ty: &HirTy) -> bool {
    #[allow(clippy::cast_possible_truncation)]
    match (v, ty) {
        (LitVal::Int(v), HirTy::Prim(p)) => {
            p.is_int()
                && !matches!(p, PrimTy::Char | PrimTy::CChar)
                && super::pattern::int_fits(v, *p)
        }
        (LitVal::Float(f), HirTy::Prim(PrimTy::F32)) => (f as f32).is_finite(),
        (LitVal::Float(f), HirTy::Prim(PrimTy::F64)) => f.is_finite(),
        (LitVal::Int(_), _) => super::bignum::big_of(ctx, ty) == Some(super::bignum::Big::Int),
        (LitVal::Float(_), _) => super::bignum::big_of(ctx, ty) == Some(super::bignum::Big::Float),
    }
}

/// Impl selection (spec 3.1.3) for any trait impl chosen by an argument's
/// type (`a * 2`, `T::from(2)`, `T::try_from(-1)`, `2.into()`): when
/// `lit` is an unsuffixed literal and `params` are the candidate impls'
/// types for its slot, the index of the one it should take — its
/// default type (`i32` / `f64`) if some impl has it, else the unique
/// impl it fits. `Ok(None)`: not a literal, or nothing fits.
/// `Err`: several fit (their names, for the diagnostic).
fn pick_literal_impl(
    ctx: &LowerCtx<'_>,
    lit: &Expr,
    params: &[HirTy],
) -> Result<Option<usize>, String> {
    let Some(v) = untyped_lit_value(lit) else {
        return Ok(None);
    };
    let default = match v {
        LitVal::Int(_) => HirTy::Prim(PrimTy::I32),
        LitVal::Float(_) => HirTy::Prim(PrimTy::F64),
    };
    if let Some(i) = params.iter().position(|p| *p == default) {
        if literal_fits(ctx, v, &default) {
            return Ok(Some(i));
        }
    }
    let fits: Vec<usize> = (0..params.len())
        .filter(|i| literal_fits(ctx, v, &params[*i]))
        .collect();
    match fits[..] {
        [] => Ok(None),
        [i] => Ok(Some(i)),
        _ => Err(fits
            .iter()
            .map(|i| format!("`{}`", ctx.ty_name(&params[*i])))
            .collect::<Vec<_>>()
            .join(", ")),
    }
}

/// `lit.into()` / `lit.try_into()` in a slot of type `expected`: the
/// literal receiver takes the `From` / `TryFrom` impl of `expected` it
/// fits (`let e: Even = 4.try_into()` with `impl TryFrom<i64> for Even`).
fn literal_conv_receiver(ctx: &mut LowerCtx<'_>, receiver: &Expr, method: &str) -> Option<HirExpr> {
    let conv = match method {
        "into" => "from",
        "try_into" => "try_from",
        _ => return None,
    };
    untyped_lit_value(receiver)?;
    let expected = ctx.current_expected()?.clone();
    let ids = method_target_for(&expected)
        .and_then(|k| ctx.env.method_table.get(&(k, conv.to_owned())))?;
    let params: Vec<HirTy> = ids
        .iter()
        .filter_map(|id| ctx.sig_by_id(*id).param_tys.first().cloned())
        .collect();
    // Ambiguous or nothing fits: the ordinary lowering reports it.
    let i = pick_literal_impl(ctx, receiver, &params).ok()??;
    Some(lower_expected(ctx, receiver, params[i].clone()))
}

/// `[a, b]` is a `List` (spec 6.5.1); a fixed array only in a slot
/// typed `[T; N]`.
fn lower_list_lit(ctx: &mut LowerCtx<'_>, items: &[Expr], span: rokc_diagnostic::Span) -> HirExpr {
    let Some(HirTy::Array(e, _)) = ctx.current_expected().cloned() else {
        let args = vec![rokc_ast::LitArg::Many(items.to_vec())];
        return lower_shape(ctx, rokc_parser::Shape::List, args, "`List`", span);
    };
    let mut elem_ty = (*e).clone();
    let mut lowered: Vec<HirExpr> = Vec::with_capacity(items.len());
    for (i, e) in items.iter().enumerate() {
        let v = lower_expected(ctx, e, elem_ty.clone());
        // An open element type (`[T; N]` slot, `T` unbound) is the
        // first element's.
        if elem_ty == HirTy::Unknown {
            elem_ty = v.ty.clone();
        }
        lowered.push(coerce(ctx, &elem_ty, v, &|| format!("array element {i}")));
    }
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

/// `[v; N]`: `v` evaluated once, then copied into each element (one
/// node per element up to `REPEAT_UNROLL`, a fill loop beyond).
fn lower_array_repeat(
    ctx: &mut LowerCtx<'_>,
    value: &Expr,
    len: &rokc_ast::ConstExpr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let elem_hint = match ctx.current_expected() {
        Some(HirTy::Array(e, _)) => (**e).clone(),
        _ => HirTy::Unknown,
    };
    let v = lower_expected(ctx, value, elem_hint.clone());
    let v = if elem_hint == HirTy::Unknown {
        v
    } else {
        coerce(ctx, &elem_hint, v, &|| "array repeat value".to_owned())
    };
    let Some(n) = ctx.eval_const(len).and_then(|n| u32::try_from(n).ok()) else {
        return ctx.error_expr(
            span,
            "the length of `[v; N]` must be a non-negative compile-time integer (spec 2.11)"
                .to_owned(),
        );
    };
    let elem_ty = v.ty.clone();
    let tmp = ctx.declare(None, elem_ty.clone());
    let ty = HirTy::Array(Box::new(elem_ty.clone()), n);
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: vec![HirStmt::Let {
                local: tmp,
                init: v,
            }],
            trailing: Some(HirExpr {
                kind: if n > REPEAT_UNROLL {
                    HirExprKind::ArrayRepeat {
                        value: Box::new(hir_local(tmp, &elem_ty, span)),
                        elem_ty,
                        len: n,
                    }
                } else {
                    HirExprKind::ArrayInit {
                        elements: (0..n).map(|_| hir_local(tmp, &elem_ty, span)).collect(),
                        elem_ty,
                    }
                },
                ty: ty.clone(),
                span,
            }),
            label: None,
        })),
        ty,
        span,
    }
}

/// Longest `[v; N]` lowered element by element.
const REPEAT_UNROLL: u32 = 16;

/// `#[intrinsic("rok.buf.new" | "rok.buf.get" | "rok.buf.set")]` on a
/// core function: the `GcBuf<T>` primitives `List` / `Dict` are built
/// on.
fn buf_intrinsic(def: &FnDef) -> Option<&'static str> {
    if !def.name.starts_with("rok::") {
        return None;
    }
    let attr = def.attrs.iter().find(|a| a.name() == "intrinsic")?;
    let rokc_ast::AttrBody::Args(args) = &attr.body else {
        return None;
    };
    args.iter().find_map(|a| match a {
        rokc_ast::AttrArg::Lit(rokc_ast::Literal::Str(s)) => match s.as_str() {
            "rok.buf.new" => Some("new"),
            "rok.buf.get" => Some("get"),
            "rok.buf.set" => Some("set"),
            "rok.buf.same" => Some("same"),
            "rok.buf.erase" => Some("erase"),
            "rok.ptr.read" => Some("ptr_read"),
            "rok.ptr.write" => Some("ptr_write"),
            "rok.ptr.read_volatile" => Some("ptr_read_volatile"),
            "rok.ptr.write_volatile" => Some("ptr_write_volatile"),
            "rok.size_of" => Some("size_of"),
            "rok.align_of" => Some("align_of"),
            "rok.atomic.load" => Some("atomic_load"),
            "rok.atomic.xchg" => Some("atomic_xchg"),
            "rok.atomic.add" => Some("atomic_add"),
            "rok.atomic.sub" => Some("atomic_sub"),
            "rok.atomic.and" => Some("atomic_and"),
            "rok.atomic.or" => Some("atomic_or"),
            "rok.atomic.xor" => Some("atomic_xor"),
            "rok.atomic.cas" => Some("atomic_cas"),
            "rok.any_cast" => Some("any_cast"),
            "rok.method_table" => Some("method_table"),
            "rok.mlir.op" => Some("mlir_op"),
            "rok.mlir.attr" => Some("mlir_attr"),
            _ => None,
        },
        _ => None,
    })
}

use super::resolve::{str_lit_of, str_targ};

/// `__mlir_attr::<"text">` (also called, `()`, or a plain string): the
/// attribute's text.
fn mlir_attr_text(e: &Expr) -> Option<String> {
    if let Some(s) = str_lit_of(e) {
        return Some(s.to_owned());
    }
    let p = match &e.kind {
        ExprKind::Path(p) => p,
        ExprKind::Call { callee, args, .. } if args.is_empty() => match &callee.kind {
            ExprKind::Path(p) => p,
            _ => return None,
        },
        _ => return None,
    };
    let last = p.segments.last()?;
    match (last.name.as_str(), last.generics.as_slice()) {
        ("__mlir_attr", [t]) => str_targ(t).map(str::to_owned),
        _ => None,
    }
}

/// `attributes = { "name": __mlir_attr::<"text">, .. }`: its pairs.
fn mlir_attrs(e: &Expr) -> Option<Vec<(String, String)>> {
    let pair = |k: &Expr, v: &Expr| Some((str_lit_of(k)?.to_owned(), mlir_attr_text(v)?));
    match &e.kind {
        ExprKind::Dict(pairs) => pairs.iter().map(|(k, v)| pair(k, v)).collect(),
        // `{ k: v }` matched by the `Dict` literal handler: its one
        // repetition of `(k, v)` items.
        ExprKind::MagicLiteral(cands) => cands.iter().find_map(|c| match c.args.as_slice() {
            [rokc_ast::LitArg::Many(items)] => items
                .iter()
                .map(|it| match &it.kind {
                    ExprKind::Tuple(kv) if kv.len() == 2 => pair(&kv[0], &kv[1]),
                    _ => None,
                })
                .collect(),
            _ => None,
        }),
        ExprKind::Block(b) if b.stmts.is_empty() && b.trailing.is_none() => Some(Vec::new()),
        _ => None,
    }
}

/// `regions = [|a: A, ..| -> R { ..; __mlir_op::<"d.yield", ()>(..); v }, ..]`
/// (bare 1.9): each closure is one region, lowered inline in this
/// function — its parameters are the entry block's arguments, captures
/// are plain uses of the enclosing locals (MLIR regions see the values
/// above them). The body is straight-line ops; the terminator op it
/// ends with is the region's last op (a trailing value is not
/// evaluated).
fn lower_mlir_regions(ctx: &mut LowerCtx<'_>, e: &Expr) -> Vec<(Vec<LocalId>, HirExpr)> {
    let items: &[Expr] = match &e.kind {
        ExprKind::List(xs) => xs,
        ExprKind::MagicLiteral(cands) => cands
            .iter()
            .find_map(|c| match c.args.as_slice() {
                [rokc_ast::LitArg::Many(xs)] => Some(xs.as_slice()),
                _ => None,
            })
            .unwrap_or(&[]),
        _ => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "`regions` of `__mlir_op` is a list of closures `[|args| { .. }, ..]` (bare 1.9)"
                    .to_owned(),
            );
            return Vec::new();
        }
    };
    let mut out = Vec::new();
    for it in items {
        let ExprKind::Closure {
            params,
            ret_ty,
            body,
            is_async: false,
            is_generator: false,
            ..
        } = &it.kind
        else {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "a region of `__mlir_op` is a closure `|args| { .. }` (bare 1.9)".to_owned(),
            );
            continue;
        };
        ctx.push_scope();
        let locals = params
            .iter()
            .map(|p| {
                let ty = p.ty.as_ref().map_or_else(
                    || {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "region argument `{}` of `__mlir_op` needs a type (bare 1.9)",
                                p.name
                            ),
                        );
                        HirTy::Unknown
                    },
                    |t| ctx.resolve_ast_ty(t),
                );
                ctx.declare(Some(p.name.clone()), ty)
            })
            .collect();
        let ret = ret_ty
            .as_ref()
            .map_or(HirTy::Unknown, |t| ctx.resolve_ast_ty(t));
        let body = lower_expected(ctx, body, ret);
        ctx.pop_scope();
        if has_control_flow(&body) {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "a region of `__mlir_op` is straight-line ops (no `if` / `match` / loops / \
                 `return`; use `scf` ops) (bare 1.9)"
                    .to_owned(),
            );
        }
        out.push((locals, body));
    }
    out
}

/// Whether `e` has control flow (MIR blocks), which a region body
/// can't hold.
fn has_control_flow(e: &HirExpr) -> bool {
    let mut branchy = false;
    crate::each_expr(e, &mut |x| match &x.kind {
        HirExprKind::If { .. }
        | HirExprKind::While { .. }
        | HirExprKind::Loop { .. }
        | HirExprKind::Match { .. }
        | HirExprKind::Suspend { .. } => branchy = true,
        HirExprKind::Block(b) => {
            if b.stmts.iter().any(|s| {
                matches!(
                    s,
                    HirStmt::Return(_)
                        | HirStmt::Break { .. }
                        | HirStmt::Continue { .. }
                        | HirStmt::Panic(_)
                )
            }) {
                branchy = true;
            }
        }
        _ => {}
    });
    branchy
}

/// `__mlir_op::<"dialect.op", R>(operands.., attributes = {..}, regions = [..])`
/// (stdlib bare 1.9): one op in MLIR's generic form. `R` is a rok type
/// or `__mlir_type<"..">` (`_`: the expected type; `()`: no result).
fn lower_mlir_op(
    ctx: &mut LowerCtx<'_>,
    targs: &[Ty],
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let shape = "`__mlir_op` is called as `__mlir_op::<\"dialect.op\", R>(operands..)` (bare 1.9)";
    let (Some(op), Some(r)) = (targs.first().and_then(str_targ), targs.get(1)) else {
        discard_args(ctx, args);
        return ctx.error_expr(span, shape.to_owned());
    };
    let op = op.to_owned();
    if targs.len() != 2 || !op.contains('.') {
        discard_args(ctx, args);
        return ctx.error_expr(span, shape.to_owned());
    }
    let infer = matches!(&r.kind, rokc_ast::TyKind::Path(p)
        if p.segments.len() == 1 && p.segments[0].name == "_");
    let ty = if infer {
        ctx.current_expected().cloned().unwrap_or(HirTy::Unknown)
    } else {
        ctx.resolve_ast_ty(r)
    };
    let mut attrs = Vec::new();
    let mut regions = Vec::new();
    let mut lowered = Vec::new();
    for a in args {
        match a {
            CallArg::Positional(e) => lowered.push(lower_expected(ctx, e, HirTy::Unknown)),
            CallArg::Named { name, value } if name == "attributes" => match mlir_attrs(value) {
                Some(kv) => attrs = kv,
                None => ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    "`attributes` of `__mlir_op` is `{ \"name\": __mlir_attr::<\"text\">, .. }` \
                     (bare 1.9)"
                        .to_owned(),
                ),
            },
            CallArg::Named { name, value } if name == "regions" => {
                regions = lower_mlir_regions(ctx, value);
            }
            _ => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    "`__mlir_op` takes operands, `attributes = {..}` and `regions = [..]` \
                     (bare 1.9)"
                        .to_owned(),
                );
            }
        }
    }
    if ty == HirTy::Unknown {
        return ctx.error_expr(
            span,
            format!("type annotations needed: the result type of `__mlir_op::<\"{op}\", _>`"),
        );
    }
    HirExpr {
        kind: HirExprKind::MlirOp {
            op,
            attrs,
            args: lowered,
            regions,
        },
        ty,
        span,
    }
}

/// `rok::bare` raw-memory intrinsics. `size_of::<T>()` /
/// `align_of::<T>()` take `T` from the turbofish; `ptr_read(p)`,
/// `ptr_write(p, v)` (and `_volatile`) take a pointer struct (`Ptr<T>`,
/// `ConstPtr<T>`, `ManyPtr<T>`: field 0 is the `usize` address) and
/// use its `T`. `None` for other intrinsics.
fn lower_raw_intrinsic(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    targs: &[Ty],
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> Option<HirExpr> {
    if let Some(r) = super::reflect::intrinsic(ctx, op, targs, args, span) {
        return Some(r);
    }
    if op == "mlir_op" {
        return Some(lower_mlir_op(ctx, targs, args, span));
    }
    if op == "mlir_attr" {
        discard_args(ctx, args);
        return Some(
            ctx.error_expr(
                span,
                "`__mlir_attr::<\"..\">` is only an `attributes` value of `__mlir_op` (bare 1.9)"
                    .to_owned(),
            ),
        );
    }
    let usize_ty = HirTy::Prim(PrimTy::Usize);
    if matches!(op, "size_of" | "align_of") {
        let (Some(t), true) = (targs.first(), args.is_empty() && targs.len() == 1) else {
            discard_args(ctx, args);
            return Some(ctx.error_expr(span, format!("`{op}` is called as `{op}::<T>()`")));
        };
        return Some(HirExpr {
            kind: HirExprKind::SizeOf {
                ty: ctx.resolve_ast_ty(t),
                align: op == "align_of",
            },
            ty: usize_ty,
            span,
        });
    }
    let volatile = op.ends_with("_volatile");
    let write = op.starts_with("ptr_write");
    if !op.starts_with("ptr_read") && !write {
        return None;
    }
    let pos: Vec<&Expr> = args
        .iter()
        .filter_map(|a| match a {
            CallArg::Positional(e) => Some(e),
            _ => None,
        })
        .collect();
    let want = if write { 2 } else { 1 };
    if pos.len() != want || args.len() != want {
        discard_args(ctx, args);
        return Some(ctx.error_expr(span, format!("`{op}` takes {want} argument(s)")));
    }
    let p = lower_expected(ctx, pos[0], HirTy::Unknown);
    let HirTy::Struct(sid) = p.ty else {
        discard_args(ctx, &args[1..]);
        if p.ty == HirTy::Unknown {
            return Some(p);
        }
        return Some(ctx.error_expr(
            span,
            format!("`{op}` needs a `Ptr<T>`, found `{}`", ctx.ty_name(&p.ty)),
        ));
    };
    let def = ctx.struct_def(sid);
    let (Some(ty), Some(HirTy::Prim(PrimTy::Usize))) = (
        def.generic_args.first().cloned(),
        def.fields.first().map(|f| f.ty.clone()),
    ) else {
        return Some(ctx.error_expr(span, format!("`{op}` needs a `Ptr<T>`")));
    };
    let addr = Box::new(HirExpr {
        kind: HirExprKind::FieldRead {
            target: Box::new(p),
            struct_id: sid,
            field_index: 0,
            field_ty: usize_ty.clone(),
        },
        ty: usize_ty,
        span,
    });
    Some(if write {
        let v = lower_expected(ctx, pos[1], ty.clone());
        let v = coerce(ctx, &ty, v, &|| "the stored value".to_owned());
        HirExpr {
            kind: HirExprKind::RawWrite {
                addr,
                value: Box::new(v),
                ty,
                volatile,
            },
            ty: HirTy::Unit,
            span,
        }
    } else {
        HirExpr {
            kind: HirExprKind::RawRead {
                addr,
                ty: ty.clone(),
                volatile,
            },
            ty,
            span,
        }
    })
}

/// `atomic_OP(buf, i, operands..)` over a `GcBuf<T>` of an integer or
/// `bool` `T`; yields the element's previous value.
fn lower_atomic_intrinsic(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let op: &'static str = match op {
        "load" => "load",
        "xchg" => "xchg",
        "add" => "add",
        "sub" => "sub",
        "and" => "and",
        "or" => "or",
        "xor" => "xor",
        _ => "cas",
    };
    let pos: Vec<&Expr> = args
        .iter()
        .filter_map(|a| match a {
            CallArg::Positional(e) => Some(e),
            _ => None,
        })
        .collect();
    // Value operands, then the ordering(s) (`cas`: success, failure).
    let (values, orders) = match op {
        "load" => (0, 1),
        "cas" => (2, 2),
        _ => (1, 1),
    };
    let want = 2 + values + orders;
    if pos.len() != want || args.len() != want {
        discard_args(ctx, args);
        return ctx.error_expr(span, format!("`atomic_{op}` takes {want} argument(s)"));
    }
    // The orderings must be literal `AtomicOrdering` variants: LLVM fixes
    // them per instruction.
    let mut order = ["seq_cst"; 2];
    for (k, e) in pos[2 + values..].iter().enumerate() {
        let name = match &e.kind {
            ExprKind::Path(p) => p.segments.last().map(|s| s.name.as_str()),
            _ => None,
        };
        let llvm = match name {
            Some("Relaxed") => "monotonic",
            Some("Acquire") => "acquire",
            Some("Release") => "release",
            Some("AcqRel") => "acq_rel",
            Some("SeqCst") => "seq_cst",
            _ => {
                discard_args(ctx, args);
                return ctx.error_expr(
                    span,
                    format!(
                        "`atomic_{op}`: the memory ordering must be a constant `AtomicOrdering` \
                         variant (`Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst`)"
                    ),
                );
            }
        };
        // A load cannot release; a failed `cas` is a load.
        if (op == "load" || k == 1) && matches!(llvm, "release" | "acq_rel") {
            discard_args(ctx, args);
            let what = if op == "load" {
                "a load"
            } else {
                "a failed compare-exchange"
            };
            return ctx.error_expr(
                span,
                format!(
                    "`atomic_{op}`: `{}` is not a valid ordering for {what}",
                    name.unwrap_or("")
                ),
            );
        }
        order[k] = llvm;
    }
    let buf = lower_expected(ctx, pos[0], HirTy::Unknown);
    let elem = match &buf.ty {
        HirTy::GcBuf(e) if matches!(**e, HirTy::Prim(p) if p.is_int() || p == PrimTy::Bool) => {
            (**e).clone()
        }
        HirTy::Unknown => {
            discard_args(ctx, &args[1..]);
            return buf;
        }
        other => {
            let msg = format!(
                "`atomic_{op}` needs a `GcBuf` of an integer or `bool`, found `{}`",
                ctx.ty_name(other)
            );
            discard_args(ctx, &args[1..]);
            return ctx.error_expr(span, msg);
        }
    };
    if elem == HirTy::Prim(PrimTy::Bool) && matches!(op, "add" | "sub") {
        discard_args(ctx, &args[1..]);
        return ctx.error_expr(
            span,
            format!("`atomic_{op}` needs an integer, found `bool`"),
        );
    }
    let usize_ty = HirTy::Prim(PrimTy::Usize);
    let i = lower_expected(ctx, pos[1], usize_ty.clone());
    let i = coerce(ctx, &usize_ty, i, &|| "the buffer index".to_owned());
    let operands = pos[2..2 + values]
        .iter()
        .map(|e| {
            let v = lower_expected(ctx, e, elem.clone());
            coerce(ctx, &elem, v, &|| "the atomic operand".to_owned())
        })
        .collect();
    HirExpr {
        ty: elem.clone(),
        kind: HirExprKind::BufAtomic {
            op,
            buf: Box::new(buf),
            index: Box::new(i),
            args: operands,
            elem,
            order,
        },
        span,
    }
}

fn lower_buf_intrinsic(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let usize_ty = HirTy::Prim(PrimTy::Usize);
    let pos: Vec<&Expr> = args
        .iter()
        .filter_map(|a| match a {
            CallArg::Positional(e) => Some(e),
            _ => None,
        })
        .collect();
    let want = match op {
        "new" | "erase" => 1,
        "get" | "same" => 2,
        _ => 3,
    };
    if pos.len() != want || args.len() != want {
        discard_args(ctx, args);
        return ctx.error_expr(
            span,
            format!("`buf_{op}` takes {want} positional argument(s)"),
        );
    }
    let index = |ctx: &mut LowerCtx<'_>, e: &Expr| {
        let i = lower_expected(ctx, e, usize_ty.clone());
        coerce(ctx, &usize_ty, i, &|| "the buffer index".to_owned())
    };
    if op == "new" {
        let Some(HirTy::GcBuf(elem)) = ctx.current_expected().cloned() else {
            discard_args(ctx, args);
            return ctx.error_expr(
                span,
                "`buf_new` needs its `GcBuf<T>` type from the context — annotate the slot"
                    .to_owned(),
            );
        };
        let len = index(ctx, pos[0]);
        return HirExpr {
            ty: HirTy::GcBuf(elem.clone()),
            kind: HirExprKind::BufNew {
                elem: *elem,
                len: Box::new(len),
            },
            span,
        };
    }
    let buf = lower_expected(ctx, pos[0], HirTy::Unknown);
    let HirTy::GcBuf(elem) = buf.ty.clone() else {
        discard_args(ctx, &args[1..]);
        if buf.ty == HirTy::Unknown {
            return buf;
        }
        return ctx.error_expr(
            span,
            format!(
                "`buf_{op}` needs a `GcBuf<T>`, found `{}`",
                ctx.ty_name(&buf.ty)
            ),
        );
    };
    let u8_buf = HirTy::GcBuf(Box::new(HirTy::Prim(PrimTy::U8)));
    match op {
        "same" => buf_same(ctx, buf, pos[1], span),
        // The same reference as `GcBuf<u8>`, the type of a runtime
        // parameter that takes any GC object.
        "erase" => HirExpr {
            ty: u8_buf.clone(),
            kind: HirExprKind::Cast {
                from_ty: buf.ty.clone(),
                to_ty: u8_buf,
                operand: Box::new(buf),
            },
            span,
        },
        _ => buf_access(ctx, buf, *elem, pos[1], pos.get(2).copied(), span),
    }
}

/// `buf_same(a, b)`: whether two buffers are one object. The addresses
/// are compared where both are loaded, so no collection can move either
/// in between and nothing is pinned.
fn buf_same(ctx: &mut LowerCtx<'_>, a: HirExpr, b: &Expr, span: rokc_diagnostic::Span) -> HirExpr {
    let b = lower_expected(ctx, b, a.ty.clone());
    let b = coerce(ctx, &a.ty, b, &|| "the compared buffer".to_owned());
    let usize_ty = HirTy::Prim(PrimTy::Usize);
    let addr = |e: HirExpr| HirExpr {
        ty: usize_ty.clone(),
        kind: HirExprKind::Cast {
            from_ty: e.ty.clone(),
            to_ty: usize_ty.clone(),
            operand: Box::new(e),
        },
        span,
    };
    HirExpr {
        ty: HirTy::Prim(PrimTy::Bool),
        kind: HirExprKind::PrimBinOp {
            op: PrimOp::Eq,
            lhs: Box::new(addr(a)),
            rhs: Box::new(addr(b)),
        },
        span,
    }
}

/// `buf[i]` (`value: None`) or `buf[i] = value` on a lowered `GcBuf<T>`:
/// the `rok.buf.get` / `rok.buf.set` primitive, no call. Shared by the
/// `buf_get` / `buf_set` intrinsics and `Index` / `IndexSet` syntax.
fn buf_access(
    ctx: &mut LowerCtx<'_>,
    buf: HirExpr,
    elem: HirTy,
    idx: &Expr,
    value: Option<&Expr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // No bounds check: an index past the allocation reads / writes
    // arbitrary memory.
    if ctx.unsafe_depth == 0 {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            "indexing a `GcBuf` is unchecked and needs an `unsafe` block or `unsafe fn` \
             (spec 4.15)"
                .to_owned(),
        );
    }
    let usize_ty = HirTy::Prim(PrimTy::Usize);
    let i = lower_expected(ctx, idx, usize_ty.clone());
    let i = coerce(ctx, &usize_ty, i, &|| "the buffer index".to_owned());
    let Some(value) = value else {
        return HirExpr {
            ty: elem.clone(),
            kind: HirExprKind::BufGet {
                buf: Box::new(buf),
                index: Box::new(i),
                elem,
            },
            span,
        };
    };
    let v = lower_expected(ctx, value, elem.clone());
    let v = coerce(ctx, &elem, v, &|| "the stored element".to_owned());
    HirExpr {
        ty: HirTy::Unit,
        kind: HirExprKind::BufSet {
            buf: Box::new(buf),
            index: Box::new(i),
            value: Box::new(v),
            elem,
        },
        span,
    }
}

/// Lower call arguments only for their diagnostics (the call itself
/// failed to resolve).
pub(super) fn discard_args(ctx: &mut LowerCtx<'_>, args: &[CallArg]) {
    for a in args {
        let (CallArg::Positional(e)
        | CallArg::Named { value: e, .. }
        | CallArg::Spread(e)
        | CallArg::Ref(e)) = a;
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
    if matches!(lhs_h.ty, HirTy::AnyTrait(_)) || matches!(rhs_h.ty, HirTy::AnyTrait(_)) {
        return dyn_op(ctx, op, lhs_h, Some(rhs_h), span);
    }
    // Spec 6.7.2 `swap`: `a ∈ s` is `s.contains(a)`. Operands still
    // evaluate left to right: `a` goes to a temp first.
    if ctx
        .env
        .prec
        .lookup(op, Fixity::Infix)
        .is_some_and(|e| e.swap)
    {
        let ty = lhs_h.ty.clone();
        let tmp = ctx.declare(None, ty.clone());
        let call = dispatch_user_op(
            ctx,
            op,
            Fixity::Infix,
            rhs_h,
            Some(hir_local(tmp, &ty, span)),
            span,
        );
        let call_ty = call.ty.clone();
        return HirExpr {
            kind: HirExprKind::Block(Box::new(HirBlock {
                stmts: vec![HirStmt::Let {
                    local: tmp,
                    init: lhs_h,
                }],
                trailing: Some(call),
                label: None,
            })),
            ty: call_ty,
            span,
        };
    }
    // Spec 0.4 / 3.1: `a + b` on a user type desugars to the operator
    // trait's method (`impl Add for T`); so does `str` (core::str impls:
    // concatenation, content comparison), and a Unicode math operator
    // (spec 1.10.3) on any type, primitives included (`impl Sqrt for f64`).
    // Tuples / arrays: core's component-wise impls (`core::tuple`).
    if matches!(
        lhs_h.ty,
        HirTy::Struct(_)
            | HirTy::Enum(_)
            | HirTy::Prim(PrimTy::Str)
            | HirTy::Tuple(_)
            | HirTy::Array(..)
    ) || !op.is_ascii()
    {
        return dispatch_user_op_lit(ctx, op, Fixity::Infix, lhs_h, Some(rhs_h), Some(rhs), span);
    }
    // A primitive on the left of a user type (`impl Mul<Duration> for f64`),
    // or an operator with no primitive lowering (`%%` → core's `Modulo`).
    if let HirTy::Prim(lp) = lhs_h.ty {
        if matches!(rhs_h.ty, HirTy::Struct(_) | HirTy::Enum(_)) || infix_for_prim(op, lp).is_none()
        {
            return dispatch_user_op_lit(
                ctx,
                op,
                Fixity::Infix,
                lhs_h,
                Some(rhs_h),
                Some(rhs),
                span,
            );
        }
    }
    // Comparisons on a sum dispatch on the variant (`sum_structural_call`).
    if let HirTy::Sum(_) = lhs_h.ty {
        let method = match op {
            "==" => Some("eq"),
            "!=" => Some("ne"),
            "<" => Some("lt"),
            ">" => Some("gt"),
            "<=" => Some("le"),
            ">=" => Some("ge"),
            _ => None,
        };
        let key = match method {
            Some("eq" | "ne") => ctx.lang_trait("eq_trait"),
            _ => ctx.lang_trait("cmp_trait"),
        };
        if let Some(m) = method.filter(|_| ctx.implements_trait(&lhs_h.ty, key, 0)) {
            return sum_structural_call(ctx, lhs_h, m, &[], Some(rhs_h), span);
        }
    }
    if let (HirTy::Prim(lp), HirTy::Prim(rp)) = (&lhs_h.ty, &rhs_h.ty) {
        if lp == rp {
            if let Some((primop, result_ty)) = infix_for_prim(op, *lp) {
                let e = hir_binop(primop, lhs_h, rhs_h, result_ty, span);
                check_const_overflow(ctx, &e.kind, &e.ty, span);
                return e;
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

/// Spec 2.2.3 / 808: an operator with an `any` operand switches
/// on the tag over the primitive types that have the operator (both
/// operands the same type, as for static primitive operators); a
/// static operand fixes that type. Arithmetic results are boxed back
/// into `any`; when every candidate yields `bool` (comparisons) the
/// result is `bool`. A runtime type without the operator panics.
fn dyn_op(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    lhs: HirExpr,
    rhs: Option<HirExpr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    use PrimTy as P;
    const PRIMS: [PrimTy; 15] = [
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
        P::F32,
        P::F64,
        P::Bool,
        P::CChar,
        P::Char,
    ];
    let is_dyn = |t: &HirTy| matches!(t, HirTy::AnyTrait(_));
    let fixed = [Some(&lhs.ty), rhs.as_ref().map(|r| &r.ty)]
        .into_iter()
        .flatten()
        .find(|t| !is_dyn(t))
        .cloned();
    let lookup = |p: PrimTy| {
        if rhs.is_some() {
            infix_for_prim(op, p)
        } else {
            prefix_for_prim(op, p)
        }
    };
    let cands: Vec<(PrimTy, PrimOp, HirTy)> = PRIMS
        .into_iter()
        .filter(|p| fixed.as_ref().is_none_or(|f| *f == HirTy::Prim(*p)))
        .filter_map(|p| lookup(p).map(|(o, t)| (p, o, t)))
        .collect();
    if cands.is_empty() {
        let tys: Vec<String> = [Some(&lhs.ty), rhs.as_ref().map(|r| &r.ty)]
            .into_iter()
            .flatten()
            .map(|t| format!("`{}`", ctx.ty_name(t)))
            .collect();
        return ctx.error_expr(
            span,
            format!(
                "operator `{op}` cannot be applied to {} — on an `any` value it dispatches \
                 only over primitive types (narrow it with `is` first)",
                tys.join(" and ")
            ),
        );
    }
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let result_ty = if cands.iter().all(|c| c.2 == bool_ty) {
        bool_ty
    } else {
        HirTy::AnyTrait(Vec::new())
    };
    // Operands are evaluated once, left to right.
    let mut lets = Vec::new();
    let mut temp = |ctx: &mut LowerCtx<'_>, e: HirExpr| {
        let ty = e.ty.clone();
        let l = ctx.declare(None, ty.clone());
        lets.push(HirStmt::Let { local: l, init: e });
        hir_local(l, &ty, span)
    };
    let l = temp(ctx, lhs);
    let r = rhs.map(|r| temp(ctx, r));
    let panic_arm = |ctx: &LowerCtx<'_>| HirMatchArm {
        pat: HirPattern::Wildcard,
        guard: None,
        body: HirExpr {
            kind: HirExprKind::Block(Box::new(HirBlock {
                stmts: vec![HirStmt::Panic(super::throws::hook_call(
                    ctx,
                    "rok_panic_at",
                    &format!(
                        "operator `{op}` is not defined for the runtime type of an `any` value"
                    ),
                    span,
                ))],
                trailing: None,
                label: None,
            })),
            ty: result_ty.clone(),
            span,
        },
    };
    // `match v { x: P => body(x), _ => panic }`, or `v` itself if static.
    let narrow = |ctx: &mut LowerCtx<'_>,
                  v: &HirExpr,
                  p: PrimTy,
                  body: &dyn Fn(&mut LowerCtx<'_>, HirExpr) -> HirExpr| {
        let pty = HirTy::Prim(p);
        if !is_dyn(&v.ty) {
            return body(ctx, v.clone());
        }
        let x = ctx.declare(None, pty.clone());
        let arm = HirMatchArm {
            pat: HirPattern::SumVariant {
                sum_ty: v.ty.clone(),
                variant_index: ctx.any_tag(&pty),
                binder: Some(x),
                payload_ty: Some(pty.clone()),
            },
            guard: None,
            body: body(ctx, hir_local(x, &pty, span)),
        };
        HirExpr {
            kind: HirExprKind::Match {
                scrutinee: Box::new(v.clone()),
                arms: vec![arm, panic_arm(ctx)],
            },
            ty: result_ty.clone(),
            span,
        }
    };
    let mut arms = Vec::new();
    for (p, primop, ty) in cands {
        let finish = |ctx: &mut LowerCtx<'_>, e: HirExpr| {
            coerce(ctx, &result_ty, e, &|| format!("the result of `{op}`"))
        };
        let pty = HirTy::Prim(p);
        let x = ctx.declare(None, pty.clone());
        let xv = hir_local(x, &pty, span);
        let body = if let Some(r) = &r {
            narrow(ctx, r, p, &|ctx, y| {
                finish(ctx, hir_binop(primop, xv.clone(), y, ty.clone(), span))
            })
        } else {
            let e = HirExpr {
                kind: HirExprKind::PrimUnaryOp {
                    op: primop,
                    operand: Box::new(xv.clone()),
                },
                ty: ty.clone(),
                span,
            };
            finish(ctx, e)
        };
        if !is_dyn(&l.ty) {
            // Static lhs: exactly one candidate; bind it plainly.
            lets.push(HirStmt::Let { local: x, init: l });
            return with_lets(lets, body);
        }
        arms.push(HirMatchArm {
            pat: HirPattern::SumVariant {
                sum_ty: l.ty.clone(),
                variant_index: ctx.any_tag(&pty),
                binder: Some(x),
                payload_ty: Some(pty),
            },
            guard: None,
            body,
        });
    }
    arms.push(panic_arm(ctx));
    with_lets(
        lets,
        HirExpr {
            kind: HirExprKind::Match {
                scrutinee: Box::new(l),
                arms,
            },
            ty: result_ty,
            span,
        },
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
    // `x is T && rhs`: `x` is `T` in `rhs` (spec 2.2.6).
    let rhs_h = if op == "&&" {
        ctx.push_scope();
        let lets = bind_narrowed(ctx, lhs);
        let r = lower_cond(ctx, rhs);
        ctx.pop_scope();
        with_lets(lets, r)
    } else {
        lower_cond(ctx, rhs)
    };
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
            return super::bignum::literal(ctx, lit, true, span)
                .unwrap_or_else(|| lower_literal(ctx, lit, true, span));
        }
    }
    let operand_h = lower_expr(ctx, operand);
    if operand_h.ty == HirTy::Unknown {
        return operand_h;
    }
    if matches!(operand_h.ty, HirTy::Struct(_) | HirTy::Enum(_)) || !op.is_ascii() {
        return dispatch_user_op(ctx, op, Fixity::Prefix, operand_h, None, span);
    }
    if matches!(operand_h.ty, HirTy::AnyTrait(_)) {
        return dyn_op(ctx, op, operand_h, None, span);
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
    ctx: &mut LowerCtx<'_>,
    sym: &str,
    fixity: Fixity,
    lhs: HirExpr,
    rhs: Option<HirExpr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    dispatch_user_op_lit(ctx, sym, fixity, lhs, rhs, None, span)
}

/// `dispatch_user_op`; `lit_rhs`: the right operand's source when it may
/// be an unsuffixed literal, free to take the impl's `Rhs` type.
pub(super) fn dispatch_user_op_lit(
    ctx: &mut LowerCtx<'_>,
    sym: &str,
    fixity: Fixity,
    lhs: HirExpr,
    rhs: Option<HirExpr>,
    lit_rhs: Option<&Expr>,
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
    // The impl must be of the trait that registered the operator: a
    // library operator needs the `rok::` trait, not a user trait that
    // happens to share its name.
    // Matched by leaf name (+ `rok::` for library entries); two user
    // traits sharing a name would need the defining module in `OpEntry`.
    let from_lib = entry.from_lib;
    let is_op_trait = |t: &str| {
        (!from_lib || t.starts_with("rok::")) && t.rsplit("::").next() == Some(op_trait.as_str())
    };
    let impls: Vec<FunctionId> = method_target_for(&lhs.ty)
        .and_then(|t| ctx.env.method_table.get(&(t, method.clone())))
        .map(|ids| {
            ids.iter()
                .copied()
                .filter(|id| {
                    ctx.env
                        .method_info
                        .get(id)
                        .and_then(|i| i.trait_name.as_deref())
                        .is_some_and(is_op_trait)
                })
                .collect()
        })
        .unwrap_or_default();
    // Several impls of the trait (`impl Sub<Duration> for Instant` and
    // `impl Sub<Instant> for Instant`): the one whose `Rhs` is the right
    // operand's type, else the one an unsuffixed literal fits (`d * 2`
    // with `impl Mul<i64>`, `pick_literal_impl`), else the first.
    let rhs_param = |ctx: &LowerCtx<'_>, id: FunctionId| {
        ctx.sig_by_id(id)
            .param_tys
            .get(1)
            .cloned()
            .unwrap_or(HirTy::Unknown)
    };
    let exact = rhs
        .as_ref()
        .and_then(|r| impls.iter().copied().find(|id| rhs_param(ctx, *id) == r.ty));
    let mut rhs = rhs;
    let mut lit_pick = None;
    if let (None, Some(e)) = (exact, lit_rhs) {
        let params: Vec<HirTy> = impls.iter().map(|id| rhs_param(ctx, *id)).collect();
        match pick_literal_impl(ctx, e, &params) {
            Ok(Some(i)) => {
                rhs = Some(lower_expected(ctx, e, params[i].clone()));
                lit_pick = Some(impls[i]);
            }
            Ok(None) => {}
            Err(fits) => {
                return ctx.error_expr(
                    span,
                    format!(
                        "operator `{sym}` on `{ty_name}`: the literal fits several \
                         `{op_trait}` impls ({fits}); add a suffix or `as`"
                    ),
                );
            }
        }
    }
    let fn_id = exact.or(lit_pick).or_else(|| impls.first().copied());
    let Some(fn_id) = fn_id else {
        // `impl<T> Add for Pair<T>` (spec 2.9.4): monomorphize on the
        // operand types.
        if let Ok(Some(gm)) = generic_trait_method_for(ctx, &lhs.ty, &method) {
            if gm.info.trait_name.as_deref().is_some_and(is_op_trait) {
                let mut args = vec![lhs];
                args.extend(rhs);
                let Some((callee, ty)) = monomorphize(ctx, &gm.def, Some(&gm.self_ty), &args, span)
                else {
                    return poison(span);
                };
                return HirExpr {
                    kind: HirExprKind::Call { callee, args },
                    ty,
                    span,
                };
            }
        }
        return ctx.error_expr(
            span,
            format!(
                "operator `{sym}` cannot be applied to `{ty_name}`: it needs \
                 `impl {op_trait} for {ty_name}` (`{method}` from any other trait or an \
                 inherent `fn {method}` is not enough)"
            ),
        );
    };
    let sig = ctx.sig_by_id(fn_id);
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
        // `str` compares contents through its `PartialEq` impl.
        "==" if prim != PrimTy::Str => cmp(PrimOp::Eq),
        "!=" if prim != PrimTy::Str => cmp(PrimOp::Ne),
        "<" if num => cmp(PrimOp::Lt),
        "<=" if num => cmp(PrimOp::Le),
        ">" if num => cmp(PrimOp::Gt),
        ">=" if num => cmp(PrimOp::Ge),
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

/// Path segments with a leading `Self` (inside an impl of a named type)
/// replaced by that type's absolute path (`pkg::m::T`, `rok::..`).
pub(super) fn self_path_segs(ctx: &LowerCtx<'_>, p: &AstPath) -> Vec<String> {
    let segs: Vec<String> = p.segments.iter().map(|s| s.name.clone()).collect();
    let owner = match (segs.first().map(String::as_str), &ctx.self_ty) {
        (Some("Self"), Some(HirTy::Struct(id))) if segs.len() > 1 => ctx.struct_def(*id).name,
        (Some("Self"), Some(HirTy::Enum(id))) if segs.len() > 1 => ctx.enum_def(*id).name,
        _ => return segs,
    };
    let root = (!owner.starts_with("rok::")).then(|| "pkg".to_owned());
    root.into_iter()
        .chain(owner.split("::").map(str::to_owned))
        .chain(segs.into_iter().skip(1))
        .collect()
}

/// Associated const `name` of concrete type `ty` (from one of `traits`
/// when given): the one impl whose target and bounds `ty` meets; two
/// or more is an ambiguity error.
/// The impls (with their substitution for `ty`) that give `ty` an
/// associated const `name`, from one of `traits` when given.
pub(super) fn assoc_const_hits<'e>(
    ctx: &LowerCtx<'e>,
    ty: &HirTy,
    name: &str,
    traits: Option<&[String]>,
) -> Vec<(&'e ImplConsts, HashMap<String, HirTy>)> {
    ctx.env
        .impl_consts
        .iter()
        .filter(|set| {
            traits.is_none_or(|ks| ks.contains(&set.target.trait_key))
                && set.consts.iter().any(|(n, ..)| n == name)
        })
        .filter_map(|set| Some((set, ctx.generic_impl_subst(&set.target, ty, 0)?)))
        .collect()
}

fn lower_assoc_const(
    ctx: &mut LowerCtx<'_>,
    ty: &HirTy,
    name: &str,
    traits: Option<&[String]>,
) -> Option<HirExpr> {
    let env = ctx.env;
    let hits = assoc_const_hits(ctx, ty, name, traits);
    if hits.len() > 1 {
        let from: Vec<String> = hits
            .iter()
            .map(|(s, _)| {
                if s.target.trait_key.is_empty() {
                    "an inherent impl".to_owned()
                } else {
                    format!("`{}`", leaf_name(&s.target.trait_key))
                }
            })
            .collect();
        return Some(ctx.error_expr(
            rokc_diagnostic::current_span(),
            format!(
                "associated const `{name}` of `{}` is ambiguous: {} define it — name the \
                 trait (`<T as Tr>::{name}`) (spec 2.8.3a)",
                ctx.ty_name(ty),
                from.join(" and ")
            ),
        ));
    }
    let (set, subst) = hits.into_iter().next()?;
    let (_, cty, value) = set.consts.iter().find(|(n, ..)| n == name)?;
    let sc = Scope {
        names: &env.names,
        module: &set.target.module,
    };
    let mut cty =
        super::mono::resolve_ast_with_subst(cty, &env.struct_table, &env.enum_table, &subst, sc);
    substitute_aliases(&mut cty, &env.type_aliases);
    // The value is the impl's: its names resolve in the impl's module,
    // with the impl's type parameters and `Self` bound for `ty`.
    let key = (std::ptr::from_ref(set) as usize, ty_mangle(ty));
    let subst: &'static HashMap<String, HirTy> = env
        .sink
        .const_substs
        .borrow_mut()
        .entry(key)
        .or_insert_with(|| Box::leak(Box::new(subst)));
    let saved_subst = std::mem::replace(&mut ctx.ty_subst, subst);
    let saved_module = std::mem::replace(&mut ctx.current_module, set.target.module.clone());
    let saved_self = std::mem::replace(&mut ctx.self_ty, Some(ty.clone()));
    let saved_uses = std::mem::replace(&mut ctx.local_uses, vec![Vec::new()]);
    let saved_scopes = std::mem::replace(&mut ctx.scopes, vec![HashMap::new()]);
    let key = format!("{}::{name}", ctx.ty_name(ty));
    let span = rokc_diagnostic::current_span();
    let v = super::const_eval::guard(ctx, &key, span, |ctx| {
        let v = lower_expected(ctx, value, cty.clone());
        coerce(ctx, &cty, v, &|| format!("associated const `{name}`"))
    });
    ctx.ty_subst = saved_subst;
    ctx.current_module = saved_module;
    ctx.self_ty = saved_self;
    ctx.local_uses = saved_uses;
    ctx.scopes = saved_scopes;
    Some(v.map_or_else(
        || poison(span),
        |v| super::const_eval::const_item(ctx, &key, v),
    ))
}

/// The name a type's associated consts are keyed under (`impl_consts`).
fn const_owner(ctx: &LowerCtx<'_>, ty: &HirTy) -> Option<String> {
    match ty {
        HirTy::Struct(id) => Some(enum_base_name(&ctx.struct_def(*id).name).to_owned()),
        HirTy::Enum(id) => Some(enum_base_name(&ctx.enum_def(*id).name).to_owned()),
        HirTy::Prim(p) => Some(p.name().to_owned()),
        _ => None,
    }
}

/// `<T as Tr>::N`, `Type::N` / `Box::<i32>::N`, `T::N` / `Self::N`:
/// an associated const from the impl covering that type (spec 2.8.3a).
fn assoc_const_path(ctx: &mut LowerCtx<'_>, path: &AstPath) -> Option<HirExpr> {
    // `<T as Tr>::N` (spec 2.13.4 qualified path).
    if let [q, name] = path.segments.as_slice() {
        if let (rokc_ast::QPATH_MARK, [self_ty, tr]) = (q.name.as_str(), q.generics.as_slice()) {
            let t = ctx.resolve_ast_ty(self_ty);
            let key = match &tr.kind {
                AstTyKind::Path(tp) => {
                    let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
                    ctx.env.names.trait_key(&segs, &ctx.current_module)
                }
                _ => String::new(),
            };
            if let Some(v) = lower_assoc_const(ctx, &t, &name.name, Some(&[key])) {
                return Some(v);
            }
        }
    }
    // `Type::N` / `Box::<i32>::N`: the impl covering that type.
    if let [prefix @ .., name] = path.segments.as_slice() {
        let segs: Vec<&str> = prefix.iter().map(|s| s.name.as_str()).collect();
        let owner = rokc_ast::Ty {
            kind: AstTyKind::Path(AstPath {
                segments: prefix.to_vec(),
                span: path.span,
            }),
            span: path.span,
        };
        if !prefix.is_empty()
            && segs != ["Self"]
            && (ctx
                .canon_type(&segs)
                .is_some_and(|f| !ctx.env.names.traits.contains(&f))
                || matches!(crate::ty::resolve_ty(&owner), HirTy::Prim(_)))
        {
            let ty = ctx.resolve_ast_ty(&owner);
            if let Some(v) = lower_assoc_const(ctx, &ty, &name.name, None) {
                return Some(v);
            }
        }
    }
    // `T::N` / `Self::N` on a concrete type: the impl that covers it.
    if let [owner, name] = path.segments.as_slice() {
        let ty = match owner.name.as_str() {
            "Self" => ctx.self_ty.clone(),
            n => ctx
                .ty_subst
                .get(n)
                .or_else(|| ctx.explicit_generics.get(n))
                .cloned(),
        };
        // A type parameter reads the const of a trait it is bounded by.
        let bounds = ctx.ty_bounds.get(&owner.name).cloned();
        if let Some(v) = ty
            .filter(|_| owner.generics.is_empty())
            .and_then(|t| lower_assoc_const(ctx, &t, &name.name, bounds.as_deref()))
        {
            return Some(v);
        }
    }
    None
}

pub(super) fn lower_path(
    ctx: &mut LowerCtx<'_>,
    path: &AstPath,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let self_segs = self_path_segs(ctx, path);
    let segs: Vec<&str> = self_segs.iter().map(String::as_str).collect();
    if let [name] = segs.as_slice() {
        if let Some(h) = ctx.splices.get(*name) {
            return h.clone();
        }
        if let Some(local) = ctx.lookup(name) {
            return ctx.read_local(local, span);
        }
    }
    // Spec 2.11.10: a const generic parameter is a value.
    if let [name] = segs.as_slice() {
        if let Some((v, Some(p))) = ctx.ty_subst.get(*name).and_then(crate::ty::as_const) {
            let value = if p == PrimTy::Bool {
                ConstVal::Bool(v != 0)
            } else {
                ConstVal::Int { value: v, ty: p }
            };
            return HirExpr {
                kind: HirExprKind::Const(value),
                ty: HirTy::Prim(p),
                span,
            };
        }
    }
    // Module-level `const NAME: T = expr;` — inline the value at the
    // use site, typed by the const's declaration. `T::N` / `Self::N`
    // on a type parameter or `Self` reads the concrete type's const
    // (spec 2.8.3a).
    if let Some(v) = assoc_const_path(ctx, path) {
        return v;
    }
    let assoc = match path.segments.as_slice() {
        [owner, name] if owner.generics.is_empty() => {
            let ty = if owner.name == "Self" {
                ctx.self_ty.clone()
            } else {
                ctx.ty_subst
                    .get(&owner.name)
                    .or_else(|| ctx.explicit_generics.get(&owner.name))
                    .cloned()
            };
            ty.and_then(|t| const_owner(ctx, &t))
                .map(|o| format!("{o}::{}", name.name))
                .filter(|k| ctx.env.consts.contains_key(k))
        }
        _ => None,
    };
    if let Some(full) = assoc.or_else(|| ctx.resolve_in(&segs, &ctx.env.consts)) {
        ctx.check_item_visible(&full, "const");
        let (ty, value) = ctx.env.consts[&full].clone();
        // An impl const `m::T::N` resolves its type and value in `m`.
        let owner = module_of(&full);
        let owner_segs: Vec<&str> = owner.split("::").collect();
        let module = if ctx.canon_type(&owner_segs).as_deref() == Some(owner.as_str()) {
            module_of(&owner)
        } else {
            owner
        };
        let sc = Scope {
            names: &ctx.env.names,
            module: &module,
        };
        let mut ty = resolve_ty_with_structs(&ty, &ctx.env.struct_table, &ctx.env.enum_table, sc);
        substitute_aliases(&mut ty, &ctx.env.type_aliases);
        // The value's names (and field privacy) are the defining module's.
        let saved_module = std::mem::replace(&mut ctx.current_module, module);
        let saved_uses = std::mem::replace(&mut ctx.local_uses, vec![Vec::new()]);
        let saved_scopes = std::mem::replace(&mut ctx.scopes, vec![HashMap::new()]);
        let Some(v) = super::const_eval::guard(ctx, &full, span, |ctx| {
            lower_expected(ctx, &value, ty.clone())
        }) else {
            ctx.current_module = saved_module;
            ctx.local_uses = saved_uses;
            ctx.scopes = saved_scopes;
            return poison(span);
        };
        ctx.current_module = saved_module;
        ctx.local_uses = saved_uses;
        ctx.scopes = saved_scopes;
        let v = coerce(ctx, &ty, v, &|| format!("const `{full}`"));
        return super::const_eval::const_item(ctx, &full, v);
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
        if sig.param_refs.iter().any(|r| *r) {
            return ctx.error_expr(
                span,
                format!(
                    "`{full}` has `ref` parameters and cannot be used as a `fn` value (a `fn` \
                     type has no `ref` parameters, spec 4.7.6)"
                ),
            );
        }
        return HirExpr {
            kind: HirExprKind::FnRef(sig.id),
            // A named function captures nothing: Send + Sync.
            ty: HirTy::Fn(sig.param_tys, Box::new(sig.ret_ty), {
                // An `unsafe fn` / C function value keeps its unsafety.
                let mut b = ctx.env.names.all_auto();
                if ctx.env.unsafe_fns.contains(&sig.id) {
                    b.insert(0, rokc_ast::UNSAFE_FN_MARK.to_owned());
                }
                b
            }),
            span,
        };
    }
    if let Some(full) = ctx.resolve_generic_fn_name(&segs) {
        ctx.check_item_visible(&full, "function");
        let def = ctx.env.generic_fns[&full];
        // `id::<i32>`: every type argument given — that instance's value.
        let targs = path
            .segments
            .last()
            .map_or(&[][..], |s| s.generics.as_slice());
        if !targs.is_empty() {
            let bound = match bind_explicit(ctx, def, None, targs, &full) {
                Ok(b) => b,
                Err(msg) => return ctx.error_expr(span, msg),
            };
            if bound.len() < def.generics.params.len() {
                return ctx.error_expr(
                    span,
                    format!(
                        "`{}` as a value needs all {} generic argument(s)",
                        leaf_name(&full),
                        def.generics.params.len()
                    ),
                );
            }
            ctx.explicit_generics = bound;
            let mono = monomorphize(ctx, def, None, &[], span);
            ctx.explicit_generics.clear();
            let Some((id, ret)) = mono else {
                return poison(span);
            };
            let params = ctx
                .env
                .sink
                .mono_sigs
                .borrow()
                .get(&id)
                .map(|s| s.param_tys.clone())
                .unwrap_or_default();
            return HirExpr {
                kind: HirExprKind::FnRef(id),
                ty: HirTy::Fn(params, Box::new(ret), ctx.env.names.all_auto()),
                span,
            };
        }
        if let Some(v) = rethrows_value(ctx, def, span) {
            return v;
        }
        return ctx.error_expr(
            span,
            format!(
                "generic function `{}` can only be called, not used as a value",
                segs.join("::")
            ),
        );
    }
    // `S::new` / `i32::add` / `Tr::m` without a call (spec 3.5.3).
    if let Some(v) = super::method_value::method_path_value(ctx, path, span) {
        return v;
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
    // A unit struct `Unit` is its own value.
    if let Some(sid) = ctx
        .canon_type(&segs)
        .and_then(|full| ctx.lookup_struct(&full))
    {
        if ctx.struct_def(sid).fields.is_empty() {
            return HirExpr {
                kind: HirExprKind::StructInit {
                    struct_id: sid,
                    fields: Vec::new(),
                },
                ty: HirTy::Struct(sid),
                span,
            };
        }
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
                return ctx.error_expr(
                    span,
                    format!("integer literal `{text}` is too large (an `int` holds any size)"),
                );
            };
            let value = if negate { -value } else { value };
            // An unsuffixed integer in a float slot is that float
            // (`a * 2` with `a: f64`, `let x: f64 = 1`), if exact.
            // An integer member of an expected sum wins (`i32 | f64`).
            if let Some(fty) = (!has_int_suffix(text)
                && expected_prim(ctx, PrimTy::is_int).is_none())
            .then(|| expected_prim(ctx, PrimTy::is_float))
            .flatten()
            {
                #[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
                let (bits, exact) = if fty == PrimTy::F32 {
                    let f = value as f32;
                    (u64::from(f.to_bits()), f as i128 == value)
                } else {
                    let f = value as f64;
                    (f.to_bits(), f as i128 == value)
                };
                if !exact {
                    return ctx.error_expr(
                        span,
                        format!(
                            "integer literal `{text}` is not exactly representable as `{}`",
                            fty.name()
                        ),
                    );
                }
                return konst(ConstVal::Float { bits, ty: fty }, HirTy::Prim(fty));
            }
            let ty = if has_int_suffix(text) {
                suffix_ty
            } else {
                expected_prim(ctx, |p| {
                    p.is_int() && !matches!(p, PrimTy::CChar | PrimTy::Char)
                })
                .unwrap_or(PrimTy::I32)
            };
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
            if v.is_infinite() || (ty == PrimTy::F32 && (v as f32).is_infinite()) {
                return ctx.error_expr(
                    span,
                    format!("float literal out of range for `{}`", ty.name()),
                );
            }
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

/// Parse an integer literal; an unsuffixed one defaults to `i32`.
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

/// A built-in literal shape (`[..]`, `{k: v}`, `{a, b}`, ranges) is a
/// call of the `#[literal]` handlers registered with its pattern (spec
/// 6.5.1, 6.5.4). A user package's handler applies to its own code.
fn lower_shape(
    ctx: &mut LowerCtx<'_>,
    shape: rokc_parser::Shape,
    args: Vec<rokc_ast::LitArg>,
    what: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let in_lib = ctx.current_module == "rok" || ctx.current_module.starts_with("rok::");
    let cands: Vec<rokc_ast::LitCand> = ctx
        .env
        .literal_shapes
        .iter()
        .filter(|h| h.shape == shape && (!in_lib || h.name.starts_with("rok::")))
        .map(|h| rokc_ast::LitCand {
            handler: AstPath {
                segments: h
                    .name
                    .split("::")
                    .map(|n| rokc_ast::PathSegment {
                        name: n.to_owned(),
                        generics: Vec::new(),
                    })
                    .collect(),
                span,
            },
            args: args.clone(),
            priority: h.priority,
            reg: h.span,
        })
        .collect();
    if cands.is_empty() {
        return ctx.error_expr(
            span,
            format!("no `#[literal]` handler is registered for {what} literals (spec 6.5)"),
        );
    }
    let empty = args
        .iter()
        .any(|a| matches!(a, rokc_ast::LitArg::Many(v) if v.is_empty()));
    if empty && !ctx.infer_vars && ctx.current_expected().is_none_or(|t| *t == HirTy::Unknown) {
        ctx.emit_uninferred(format!(
            "cannot infer the type of an empty {what} literal — annotate the slot"
        ));
        return poison(span);
    }
    lower_magic(ctx, &cands, span)
}

/// The full name of a literal handler's path (`pkg::` is the root).
fn handler_name(c: &rokc_ast::LitCand) -> String {
    let segs: Vec<&str> = c.handler.segments.iter().map(|s| s.name.as_str()).collect();
    match segs.split_first() {
        Some((&"pkg", rest)) => rest.join("::"),
        _ => segs.join("::"),
    }
}

/// The leaf name of the type a handler declares it returns.
fn handler_ret_leaf(ctx: &LowerCtx<'_>, name: &str) -> Option<String> {
    if let Some(def) = ctx.env.generic_fns.get(name) {
        let rokc_ast::TyKind::Path(p) = &def.ret_ty.as_ref()?.kind else {
            return None;
        };
        return p.segments.last().map(|s| s.name.clone());
    }
    match &ctx.env.fn_table.get(name)?.ret_ty {
        HirTy::Struct(id) => Some(leaf_name(enum_base_name(&ctx.struct_def(*id).name)).to_owned()),
        HirTy::Enum(id) => Some(leaf_name(enum_base_name(&ctx.enum_def(*id).name)).to_owned()),
        _ => None,
    }
}

/// Spec 6.5.4 / 6.5.5: pick the handler — the one whose return type is
/// the slot's, then the highest `priority`; still several is an error —
/// and lower the call with the captures as arguments.
fn lower_magic(
    ctx: &mut LowerCtx<'_>,
    cands: &[rokc_ast::LitCand],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let expected = ctx.current_expected().cloned().unwrap_or(HirTy::Unknown);
    let slot_leaf = match &expected {
        HirTy::Struct(id) => Some(leaf_name(enum_base_name(&ctx.struct_def(*id).name)).to_owned()),
        HirTy::Enum(id) => Some(leaf_name(enum_base_name(&ctx.enum_def(*id).name)).to_owned()),
        _ => None,
    };
    let mut live: Vec<&rokc_ast::LitCand> = cands.iter().collect();
    let typed: Vec<&rokc_ast::LitCand> = live
        .iter()
        .copied()
        .filter(|c| slot_leaf.is_some() && handler_ret_leaf(ctx, &handler_name(c)) == slot_leaf)
        .collect();
    if !typed.is_empty() {
        live = typed;
    }
    let top = live.iter().map(|c| c.priority).max().unwrap_or(0);
    live.retain(|c| c.priority == top);
    if live.len() > 1 {
        let names: Vec<String> = live
            .iter()
            .map(|c| format!("`{}`", handler_name(c)))
            .collect();
        let mut d = rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "ambiguous literal: handlers {} all match (spec 6.5.5) — give the slot a type \
                 or a handler `priority = N`",
                names.join(", ")
            ),
        )
        .with_span(span, "");
        for c in &live {
            d = d.with_secondary(c.reg, "registered here");
        }
        ctx.env.sink.diagnostics.borrow_mut().push(d);
        return poison(span);
    }
    let Some(c) = live.first() else {
        return poison(span);
    };
    let name = handler_name(c);
    let def = ctx.env.generic_fns.get(&name).copied();
    // The handler's last parameter is a variadic `...T`.
    let variadic_at = match def {
        Some(d) => d
            .params
            .last()
            .filter(|p| p.variadic)
            .map(|_| d.params.len() - 1),
        None => ctx
            .env
            .fn_table
            .get(&name)
            .filter(|s| s.variadic)
            .map(|s| s.param_tys.len() - 1),
    };
    let mut args: Vec<CallArg> = Vec::new();
    for (i, a) in c.args.iter().enumerate() {
        match a {
            rokc_ast::LitArg::One(e) => args.push(CallArg::Positional(e.clone())),
            rokc_ast::LitArg::Many(items) if variadic_at == Some(i) => {
                args.extend(items.iter().cloned().map(CallArg::Positional));
            }
            rokc_ast::LitArg::Many(items) => args.push(CallArg::Positional(Expr {
                kind: ExprKind::List(items.clone()),
                span,
            })),
        }
    }
    let call = Expr {
        kind: ExprKind::Call {
            callee: Box::new(Expr {
                kind: ExprKind::Path(c.handler.clone()),
                span,
            }),
            args,
            trailing_closure: None,
        },
        span,
    };
    // The slot's type fixes the handler's type parameters, as if
    // written `handler::<..>(..)`: `[1, 2]` in a `List<i64>` slot has
    // `i64` items.
    if let (Some(def), Some(ret), true) = (
        def,
        def.and_then(|d| d.ret_ty.as_ref()),
        slot_leaf.is_some() && handler_ret_leaf(ctx, &name) == slot_leaf,
    ) {
        let names: std::collections::HashSet<String> = def
            .generics
            .params
            .iter()
            .map(|gp| match gp {
                rokc_ast::GenericParam::Type { name, .. }
                | rokc_ast::GenericParam::Const { name, .. } => name.clone(),
            })
            .collect();
        let mut subst = HashMap::new();
        super::mono::unify_param_ty_with(ret, &expected, &names, &mut subst, ctx);
        ctx.explicit_generics = subst;
    }
    let mut h = lower_expected(ctx, &call, expected);
    super::const_eval::fold_literal(ctx, &mut h, span);
    h
}

/// An AST stand-in (a `#sN` path) for the already lowered `h`, so a
/// desugar can place it without lowering its source twice. Use it once:
/// each use evaluates `h` again.
fn splice(ctx: &mut LowerCtx<'_>, h: HirExpr) -> Expr {
    let span = h.span;
    let name = format!("#s{}", ctx.splices.len());
    ctx.splices.insert(name.clone(), h);
    Expr {
        kind: ExprKind::Path(rokc_ast::Path {
            segments: vec![rokc_ast::PathSegment {
                name,
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    }
}

const fn is_signed(ty: &HirTy) -> bool {
    matches!(ty, HirTy::Prim(p) if p.is_signed_int())
}

/// An index / slice bound in a `usize` position slot: a negative
/// untyped literal (`xs[-1]`) is an `isize`.
fn lower_position(ctx: &mut LowerCtx<'_>, idx: &Expr) -> HirExpr {
    let neg = matches!(&idx.kind, ExprKind::OpPrefix { op, .. } if op == "-");
    let want = if neg && is_untyped_literal(idx) {
        PrimTy::Isize
    } else {
        PrimTy::Usize
    };
    lower_expected(ctx, idx, HirTy::Prim(want))
}

/// `rok::core::index::<name>(args..)`.
fn index_fn(name: &str, args: Vec<Expr>, span: rokc_diagnostic::Span) -> Expr {
    let names = ["rok", "core", "index", name];
    let path = rokc_ast::Path {
        segments: names
            .iter()
            .map(|n| rokc_ast::PathSegment {
                name: (*n).to_owned(),
                generics: Vec::new(),
            })
            .collect(),
        span,
    };
    Expr {
        kind: ExprKind::Call {
            callee: Box::new(Expr {
                kind: ExprKind::Path(path),
                span,
            }),
            args: args.into_iter().map(CallArg::Positional).collect(),
            trailing_closure: None,
        },
        span,
    }
}

fn isize_ty(span: rokc_diagnostic::Span) -> Ty {
    Ty {
        kind: AstTyKind::Path(rokc_ast::Path {
            segments: vec![rokc_ast::PathSegment {
                name: "isize".to_owned(),
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    }
}

/// `e as isize`.
fn as_isize(e: Expr, span: rokc_diagnostic::Span) -> Expr {
    Expr {
        kind: ExprKind::Cast(Box::new(e), isize_ty(span)),
        span,
    }
}

/// Spec 3.6: `rok::core::index::index_from_end(i as isize, len)` — a
/// signed position `i` < 0 is `len + i`.
fn from_end(i: Expr, len: Expr, span: rokc_diagnostic::Span) -> Expr {
    index_fn("index_from_end", vec![as_isize(i, span), len], span)
}

fn len_of(recv: &Expr, span: rokc_diagnostic::Span) -> Expr {
    Expr {
        kind: ExprKind::MethodCall {
            receiver: Box::new(recv.clone()),
            method: "len".to_owned(),
            type_args: Vec::new(),
            args: Vec::new(),
            trailing_closure: None,
        },
        span,
    }
}

/// Index `idx` of a fixed array of length `n`; a signed one counts
/// from the end (spec 3.6).
fn array_position(ctx: &mut LowerCtx<'_>, idx: &Expr, n: u32) -> HirExpr {
    let i = lower_position(ctx, idx);
    check_index_ty(ctx, &i);
    if !is_signed(&i.ty) {
        return i;
    }
    let span = i.span;
    let len = Expr {
        kind: ExprKind::Literal(AstLit::Int(format!("{n}usize"))),
        span,
    };
    let i = splice(ctx, i);
    lower_expr(ctx, &from_end(i, len, span))
}

/// Does `ty`'s `method` (`index` / `index_set` / `slice`) take a
/// position (`usize`, or `Range<usize>` for `slice`) — a `List` / `Slice`
/// / `str`, not a `Dict<i64, V>`?
fn takes_position(ctx: &LowerCtx<'_>, ty: &HirTy, method: &str) -> bool {
    fn text(t: &Ty) -> String {
        let AstTyKind::Path(p) = &t.kind else {
            return String::new();
        };
        let Some(seg) = p.segments.last() else {
            return String::new();
        };
        if seg.generics.is_empty() {
            return seg.name.clone();
        }
        let args: Vec<String> = seg.generics.iter().map(text).collect();
        format!("{}<{}>", seg.name, args.join(", "))
    }
    let param = match pick_method(ctx, ty, method, None) {
        Ok(Some(MethodPick::Concrete(id))) => {
            ctx.sig_by_id(id).param_tys.get(1).map(|t| ctx.ty_name(t))
        }
        Ok(Some(MethodPick::Generic(gm))) => {
            gm.def.params.get(1).and_then(|p| p.ty.as_ref()).map(text)
        }
        _ => None,
    };
    let want = if method == "slice" {
        "Range<usize>"
    } else {
        "usize"
    };
    param.is_some_and(|p| p == want || p.ends_with(&format!("::{want}")))
}

/// `recv.index(idx)` / `recv.index_set(idx, rest..)` (spec 3.6). On a
/// position-indexed receiver (`takes_position`) a signed `idx` counts
/// from the end: `{ let #t = recv; #t.index(index_from_end(idx, #t.len())) }`.
/// An unsigned one lowers exactly as a plain call.
fn index_call(
    ctx: &mut LowerCtx<'_>,
    recv_h: HirExpr,
    method: &str,
    idx: &Expr,
    rest: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let mut args = rest.to_vec();
    if !takes_position(ctx, &recv_h.ty, method) {
        args.insert(0, CallArg::Positional(idx.clone()));
        return method_call_on(ctx, recv_h, method, &args, span);
    }
    let i = lower_position(ctx, idx);
    if !is_signed(&i.ty) {
        args.insert(0, CallArg::Positional(splice(ctx, i)));
        return method_call_on(ctx, recv_h, method, &args, span);
    }
    let t = tmp_path("t", span);
    let i = splice(ctx, i);
    args.insert(0, CallArg::Positional(from_end(i, len_of(&t, span), span)));
    let recv = splice(ctx, recv_h);
    let call = Expr {
        kind: ExprKind::MethodCall {
            receiver: Box::new(t.clone()),
            method: method.to_owned(),
            type_args: Vec::new(),
            args,
            trailing_closure: None,
        },
        span,
    };
    lower_expr(ctx, &block_of(vec![let_stmt(&t, recv)], call, span))
}

fn block_of(stmts: Vec<Stmt>, tail: Expr, span: rokc_diagnostic::Span) -> Expr {
    Expr {
        kind: ExprKind::Block(Block {
            stmts,
            trailing: Some(Box::new(tail)),
            span,
            label: None,
        }),
        span,
    }
}

/// `t[a:b:k]` (`slice_desugar`), with Python's semantics on a
/// position-sliced target (`takes_position`; the `Sliceable` impls clamp
/// the range to the length):
/// - no step, unsigned bounds: `t.slice(a..b)` as is;
/// - no step, a signed bound counts from the end, clamped at 0:
///   `{ let #t = t; #t.slice(slice_bound(a, #t.len())..b) }`;
/// - a step: `{ let #t = t; let #k: isize = k;
///   #t.slice(slice_range(a, b, #k, #t.len())).step(#k) }`, a missing
///   bound passed as `none` (its default depends on the step's sign).
fn lower_slice(
    ctx: &mut LowerCtx<'_>,
    target: &Expr,
    start: Option<&Expr>,
    end: Option<&Expr>,
    step: Option<&Expr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let t_h = lower_expected(ctx, target, HirTy::Unknown);
    if !takes_position(ctx, &t_h.ty, "slice") {
        let t = splice(ctx, t_h);
        return lower_expr(ctx, &slice_desugar(&t, start, end, step, span));
    }
    let a = start.map(|e| lower_position(ctx, e));
    let b = end.map(|e| lower_position(ctx, e));
    let signed = |h: &Option<HirExpr>| h.as_ref().is_some_and(|h| is_signed(&h.ty));
    if step.is_none() && !signed(&a) && !signed(&b) {
        let t = splice(ctx, t_h);
        let a = a.map(|h| splice(ctx, h));
        let b = b.map(|h| splice(ctx, h));
        return lower_expr(ctx, &slice_desugar(&t, a.as_ref(), b.as_ref(), None, span));
    }
    let t = tmp_path("t", span);
    let recv = splice(ctx, t_h);
    let mut bound = |h: Option<HirExpr>| h.map(|h| (is_signed(&h.ty), splice(ctx, h)));
    let (a, b) = (bound(a), bound(b));
    let Some(k) = step else {
        let pos = |x: Option<(bool, Expr)>| {
            x.map(|(neg, e)| {
                if neg {
                    index_fn(
                        "slice_bound",
                        vec![as_isize(e, span), len_of(&t, span)],
                        span,
                    )
                } else {
                    e
                }
            })
        };
        let (a, b) = (pos(a), pos(b));
        let body = slice_desugar(&t, a.as_ref(), b.as_ref(), None, span);
        return lower_expr(ctx, &block_of(vec![let_stmt(&t, recv)], body, span));
    };
    let kt = tmp_path("k", span);
    let opt = |x: Option<(bool, Expr)>| {
        x.map_or(
            Expr {
                kind: ExprKind::Literal(AstLit::None),
                span,
            },
            |(_, e)| as_isize(e, span),
        )
    };
    let range = index_fn(
        "slice_range",
        vec![opt(a), opt(b), kt.clone(), len_of(&t, span)],
        span,
    );
    let call = |recv: Expr, method: &str, arg: Expr| Expr {
        kind: ExprKind::MethodCall {
            receiver: Box::new(recv),
            method: method.to_owned(),
            type_args: Vec::new(),
            args: vec![CallArg::Positional(arg)],
            trailing_closure: None,
        },
        span,
    };
    let body = call(call(t.clone(), "slice", range), "step", kt.clone());
    // Any signed integer step widens to `isize`.
    let k_h = lower_expected(ctx, k, HirTy::Prim(PrimTy::Isize));
    let k_signed = is_signed(&k_h.ty);
    let k_e = splice(ctx, k_h);
    let let_k = Stmt {
        span,
        kind: StmtKind::Let {
            name: path_name(&kt),
            ty: Some(isize_ty(span)),
            init: if k_signed { as_isize(k_e, span) } else { k_e },
        },
    };
    lower_expr(ctx, &block_of(vec![let_stmt(&t, recv), let_k], body, span))
}

/// Spec 3.6.2 / stdlib 2.3.4: `t[a:b]` is `t.slice(a..b)` (`Sliceable`)
/// and `t[a:b:k]` is `t.slice(a..b).step(k)`. A missing `a` is `0`; a
/// missing `b` is `t.len()`, with `t` evaluated once into a temporary.
fn slice_desugar(
    target: &Expr,
    start: Option<&Expr>,
    end: Option<&Expr>,
    step: Option<&Expr>,
    span: rokc_diagnostic::Span,
) -> Expr {
    const TEMP: &str = "__rok_slice_target";
    let call = |recv: Expr, method: &str, args: Vec<Expr>| Expr {
        kind: ExprKind::MethodCall {
            receiver: Box::new(recv),
            method: method.to_owned(),
            type_args: Vec::new(),
            args: args.into_iter().map(CallArg::Positional).collect(),
            trailing_closure: None,
        },
        span,
    };
    let temp = end.is_none();
    let recv = if temp {
        Expr {
            kind: ExprKind::Path(rokc_ast::Path {
                segments: vec![rokc_ast::PathSegment {
                    name: TEMP.to_owned(),
                    generics: Vec::new(),
                }],
                span,
            }),
            span,
        }
    } else {
        target.clone()
    };
    let start = start.cloned().unwrap_or_else(|| Expr {
        kind: ExprKind::Literal(AstLit::Int("0usize".to_owned())),
        span,
    });
    let end = end
        .cloned()
        .unwrap_or_else(|| call(recv.clone(), "len", Vec::new()));
    let range = Expr {
        kind: ExprKind::Range {
            start: Some(Box::new(start)),
            end: Some(Box::new(end)),
            inclusive: false,
        },
        span,
    };
    let mut e = call(recv, "slice", vec![range]);
    if let Some(k) = step {
        e = call(e, "step", vec![k.clone()]);
    }
    if !temp {
        return e;
    }
    Expr {
        kind: ExprKind::Block(rokc_ast::Block {
            stmts: vec![rokc_ast::Stmt {
                kind: rokc_ast::StmtKind::Let {
                    name: TEMP.to_owned(),
                    ty: None,
                    init: target.clone(),
                },
                span,
            }],
            trailing: Some(Box::new(e)),
            span,
            label: None,
        }),
        span,
    }
}

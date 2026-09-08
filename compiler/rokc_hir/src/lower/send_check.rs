//! `task::spawn` moves a future to another worker (stdlib 2.18.1), so
//! the coroutine frame must be `Send`. The future types are shared
//! library wrappers (`AsyncFuture<T>` is `Send` when `T` is), so this
//! pass looks at the coroutine itself: at each `task::spawn(f)` whose `f`
//! is an `async` block, an `async fn` call, or a local bound to one, the
//! coroutine's captures and every local it holds across an `await` must
//! be `Send`.
//!
//! "Held across an `await`" is read off the HIR in evaluation order: a
//! non-`Send` local declared before a suspend point and used after it
//! (loop bodies are walked twice for the back edge).
// ponytail: a future reaching `spawn` through a struct field, a function
// parameter or another call is not traced (its wrapper's `Send` bound
// still applies).

use std::collections::{HashMap, HashSet};

use rokc_ir_common::{FunctionId, LocalId};

use super::{Env, LowerCtx};
use crate::{HirBlock, HirExpr, HirExprKind, HirFunction, HirPattern, HirStmt, HirTy};

const SPAWN: &str = "rok::core::task::spawn";

pub(super) fn check(env: &Env<'_>, functions: &[HirFunction]) {
    let extras = env.sink.extras.borrow();
    let all: HashMap<FunctionId, &HirFunction> = functions
        .iter()
        .chain(extras.iter())
        .map(|f| (f.id, f))
        .collect();
    let spawns: HashSet<FunctionId> = all
        .values()
        .filter(|f| f.name == SPAWN || f.name.starts_with(&format!("{SPAWN}__")))
        .map(|f| f.id)
        .collect();
    if spawns.is_empty() {
        return;
    }
    let Some(send) = env
        .names
        .all_auto()
        .into_iter()
        .find(|k| k.ends_with("::Send"))
    else {
        return;
    };
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None);
    let mut seen = HashSet::new();
    for f in all.values() {
        let Some(body) = &f.body else { continue };
        let mut lets = HashMap::new();
        let mut calls = Vec::new();
        visit_block(
            body,
            &mut |e| match &e.kind {
                HirExprKind::Call { callee, args } if spawns.contains(callee) => {
                    if let Some(a) = args.first() {
                        calls.push((a.clone(), e.span));
                    }
                }
                _ => {}
            },
            &mut |s| {
                if let HirStmt::Let { local, init } = s {
                    lets.insert(*local, init.clone());
                }
            },
        );
        for (arg, span) in calls {
            let Some(coro) = coroutine_of(&arg, &lets, &all) else {
                continue;
            };
            if !seen.insert((coro, (span.file, span.start))) {
                continue;
            }
            let Some(body_fn) = all.get(&coro) else {
                continue;
            };
            if let Some(why) = witness(&ctx, &send, body_fn) {
                let old = rokc_diagnostic::set_current_span(span);
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "`task::spawn` needs a `Send` future: {why}, and the task may resume \
                         on another worker (spec 2.18.1); use `task::spawn_local`"
                    ),
                );
                rokc_diagnostic::set_current_span(old);
            }
        }
    }
}

/// The coroutine body behind a spawned future expression.
fn coroutine_of(
    e: &HirExpr,
    lets: &HashMap<LocalId, HirExpr>,
    all: &HashMap<FunctionId, &HirFunction>,
) -> Option<FunctionId> {
    match &e.kind {
        HirExprKind::Block(b) if b.stmts.is_empty() => {
            coroutine_of(b.trailing.as_ref()?, lets, all)
        }
        HirExprKind::StructInit { fields, .. } => match &fields.first()?.kind {
            HirExprKind::CoroNew { body_fn, .. } => Some(*body_fn),
            _ => None,
        },
        HirExprKind::Local(l) => coroutine_of(lets.get(l)?, &HashMap::new(), all),
        // An `async fn` call: the function returns its coroutine.
        HirExprKind::Call { callee, .. } => {
            let f = all.get(callee)?;
            let mut found = None;
            visit_block(
                f.body.as_ref()?,
                &mut |e| {
                    if let (None, HirExprKind::CoroNew { body_fn, .. }) = (found, &e.kind) {
                        found = Some(*body_fn);
                    }
                },
                &mut |_| {},
            );
            found
        }
        _ => None,
    }
}

/// Why the coroutine `f`'s frame is not `Send` (`None`: it is).
fn witness(ctx: &LowerCtx<'_>, send: &str, f: &HirFunction) -> Option<String> {
    let name = |l: LocalId| {
        f.locals
            .iter()
            .find(|x| x.id == l)
            .and_then(|x| x.name.clone())
            .unwrap_or_else(|| "a temporary".to_owned())
    };
    let ty_of = |l: LocalId| f.locals.iter().find(|x| x.id == l).map(|x| x.ty.clone());
    let non_send = |t: &HirTy| *t != HirTy::Unknown && !ctx.implements_trait(t, send, 0);
    let env_params: HashSet<LocalId> = f
        .params
        .iter()
        .filter(|p| !p.name.starts_with('#'))
        .map(|p| p.local)
        .collect();
    let mut w = Walk {
        non_send: &|l| ty_of(l).filter(non_send),
        env_params: &env_params,
        declared: Vec::new(),
        crossed: HashSet::new(),
        found: None,
    };
    w.block(f.body.as_ref()?);
    let (l, captured) = w.found?;
    let ty = ty_of(l).map(|t| ctx.ty_name(&t)).unwrap_or_default();
    Some(if captured {
        format!("it captures `{}: {ty}`, which is not `Send`", name(l))
    } else {
        format!(
            "it holds `{}: {ty}`, which is not `Send`, across an `await`",
            name(l)
        )
    })
}

struct Walk<'a> {
    non_send: &'a dyn Fn(LocalId) -> Option<HirTy>,
    env_params: &'a HashSet<LocalId>,
    /// Non-`Send` locals declared so far.
    declared: Vec<LocalId>,
    /// Those live at a suspend point seen so far.
    crossed: HashSet<LocalId>,
    /// The first offender; `true` for a capture.
    found: Option<(LocalId, bool)>,
}

impl Walk<'_> {
    fn declare(&mut self, l: LocalId, init: Option<&HirExpr>) {
        if (self.non_send)(l).is_none() {
            return;
        }
        // A capture: unpacked from the env parameter in the prelude.
        let from_env = init.is_some_and(|e| {
            matches!(&e.kind, HirExprKind::TupleField { target, .. }
                if matches!(&target.kind, HirExprKind::Local(p) if self.env_params.contains(p)))
        });
        if from_env && self.found.is_none() {
            self.found = Some((l, true));
        }
        self.declared.push(l);
    }

    fn use_local(&mut self, l: LocalId) {
        if self.found.is_none() && self.crossed.contains(&l) {
            self.found = Some((l, false));
        }
    }

    fn block(&mut self, b: &HirBlock) {
        for s in &b.stmts {
            self.stmt(s);
        }
        if let Some(t) = &b.trailing {
            self.expr(t);
        }
    }

    fn stmt(&mut self, s: &HirStmt) {
        match s {
            HirStmt::Let { local, init } => {
                self.expr(init);
                self.declare(*local, Some(init));
            }
            HirStmt::Assign { value, .. } | HirStmt::StaticAssign { value, .. } => self.expr(value),
            HirStmt::ArrayAssign {
                array_local,
                index,
                value,
                ..
            } => {
                self.expr(index);
                self.expr(value);
                self.use_local(*array_local);
            }
            HirStmt::Expr(e)
            | HirStmt::Panic(e)
            | HirStmt::Return(Some(e))
            | HirStmt::Break { value: Some(e), .. } => self.expr(e),
            _ => {}
        }
    }

    fn pattern(&mut self, p: &HirPattern) {
        match p {
            HirPattern::Binding { local, .. }
            | HirPattern::SumVariant {
                binder: Some(local),
                ..
            } => self.declare(*local, None),
            HirPattern::At { local, sub, .. } => {
                self.declare(*local, None);
                self.pattern(sub);
            }
            HirPattern::Or(ps) | HirPattern::Tuple(ps) => ps.iter().for_each(|p| self.pattern(p)),
            HirPattern::Struct { fields, .. } => fields.iter().for_each(|(_, p)| self.pattern(p)),
            HirPattern::EnumVariant { args, .. } => args.iter().for_each(|p| self.pattern(p)),
            _ => {}
        }
    }

    fn expr(&mut self, e: &HirExpr) {
        match &e.kind {
            HirExprKind::Local(l) => self.use_local(*l),
            HirExprKind::Suspend { value, is_final } => {
                self.expr(value);
                if !is_final {
                    self.crossed.extend(self.declared.iter().copied());
                }
            }
            HirExprKind::While { cond, body, .. } => {
                for _ in 0..2 {
                    self.expr(cond);
                    self.block(body);
                }
            }
            HirExprKind::Loop { body, .. } => {
                self.block(body);
                self.block(body);
            }
            HirExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                for a in arms {
                    self.pattern(&a.pat);
                    if let Some(g) = &a.guard {
                        self.expr(g);
                    }
                    self.expr(&a.body);
                }
            }
            _ => {
                let mut kids = Vec::new();
                each_child(e, &mut |c| kids.push(c));
                for c in kids {
                    match c {
                        Child::E(x) => self.expr(x),
                        Child::B(b) => self.block(b),
                    }
                }
            }
        }
    }
}

/// Visit every expression (pre-order) and statement under `b`.
fn visit_block(b: &HirBlock, on_expr: &mut dyn FnMut(&HirExpr), on_stmt: &mut dyn FnMut(&HirStmt)) {
    for s in &b.stmts {
        on_stmt(s);
        match s {
            HirStmt::Let { init: e, .. }
            | HirStmt::Assign { value: e, .. }
            | HirStmt::StaticAssign { value: e, .. }
            | HirStmt::Expr(e)
            | HirStmt::Panic(e)
            | HirStmt::Return(Some(e))
            | HirStmt::Break { value: Some(e), .. } => visit_expr(e, on_expr, on_stmt),
            HirStmt::ArrayAssign { index, value, .. } => {
                visit_expr(index, on_expr, on_stmt);
                visit_expr(value, on_expr, on_stmt);
            }
            _ => {}
        }
    }
    if let Some(t) = &b.trailing {
        visit_expr(t, on_expr, on_stmt);
    }
}

fn visit_expr(e: &HirExpr, on_expr: &mut dyn FnMut(&HirExpr), on_stmt: &mut dyn FnMut(&HirStmt)) {
    on_expr(e);
    if let HirExprKind::Match { scrutinee, arms } = &e.kind {
        visit_expr(scrutinee, on_expr, on_stmt);
        for a in arms {
            if let Some(g) = &a.guard {
                visit_expr(g, on_expr, on_stmt);
            }
            visit_expr(&a.body, on_expr, on_stmt);
        }
        return;
    }
    let mut kids = Vec::new();
    each_child(e, &mut |c| kids.push(c));
    for c in kids {
        match c {
            Child::E(x) => visit_expr(x, on_expr, on_stmt),
            Child::B(b) => visit_block(b, on_expr, on_stmt),
        }
    }
}

enum Child<'e> {
    E(&'e HirExpr),
    B(&'e HirBlock),
}

/// The direct sub-expressions and sub-blocks of `e` in evaluation order
/// (not `Match`: callers handle its patterns).
fn each_child<'e>(e: &'e HirExpr, out: &mut dyn FnMut(Child<'e>)) {
    use HirExprKind as K;
    match &e.kind {
        K::Block(b) => out(Child::B(b)),
        K::PrimBinOp { lhs, rhs, .. } => {
            out(Child::E(lhs));
            out(Child::E(rhs));
        }
        K::PrimUnaryOp { operand: x, .. }
        | K::Cast { operand: x, .. }
        | K::FieldRead { target: x, .. }
        | K::TupleField { target: x, .. }
        | K::ArrayRepeat { value: x, .. }
        | K::BufNew { len: x, .. }
        | K::RawRead { addr: x, .. }
        | K::UnionWrite { value: x, .. }
        | K::UnionRead { target: x, .. }
        | K::Suspend { value: x, .. }
        | K::ClosureValue { env: x, .. }
        | K::SumWrap { value: Some(x), .. } => out(Child::E(x)),
        K::Call { args, .. }
        | K::CoroNew { args, .. }
        | K::StructInit { fields: args, .. }
        | K::EnumVariantInit { args, .. }
        | K::Tuple { fields: args }
        | K::ArrayInit { elements: args, .. } => args.iter().for_each(|a| out(Child::E(a))),
        K::CallIndirect { callee, args, .. } => {
            out(Child::E(callee));
            args.iter().for_each(|a| out(Child::E(a)));
        }
        K::CallClosure { closure, args, .. } => {
            out(Child::E(closure));
            args.iter().for_each(|a| out(Child::E(a)));
        }
        K::If {
            cond,
            then_block,
            else_branch,
        } => {
            out(Child::E(cond));
            out(Child::B(then_block));
            if let Some(x) = else_branch {
                out(Child::E(x));
            }
        }
        K::While { cond, body, .. } => {
            out(Child::E(cond));
            out(Child::B(body));
        }
        K::Loop { body, .. } => out(Child::B(body)),
        K::WithField { target, value, .. } => {
            out(Child::E(target));
            out(Child::E(value));
        }
        K::RawWrite { addr, value, .. } => {
            out(Child::E(addr));
            out(Child::E(value));
        }
        K::BufGet { buf, index, .. } => {
            out(Child::E(buf));
            out(Child::E(index));
        }
        K::BufSet {
            buf, index, value, ..
        } => {
            out(Child::E(buf));
            out(Child::E(index));
            out(Child::E(value));
        }
        K::BufAtomic {
            buf, index, args, ..
        } => {
            out(Child::E(buf));
            out(Child::E(index));
            args.iter().for_each(|a| out(Child::E(a)));
        }
        K::ArrayIndex { array, index, .. } => {
            out(Child::E(array));
            out(Child::E(index));
        }
        K::Match { .. }
        | K::Const(_)
        | K::Local(_)
        | K::StaticRef(_)
        | K::UnresolvedPath(_)
        | K::FnRef(_)
        | K::SizeOf { .. }
        | K::SumWrap { value: None, .. } => {}
    }
}

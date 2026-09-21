//! `use_after_handoff` (stdlib 2.13.9): rok has no move semantics, so
//! handing a value to another owner (`Mutex::new(xs)`, `tx.send(xs)`,
//! `Handoff::new(xs)`) leaves `xs` pointing at the object the new owner
//! shares with other threads, and a handle taken out of a guard
//! (`g.get()`, or given to it by `g.set(v)`) is unprotected once the
//! guard's `using` block ends. Using either afterwards races.
//!
//! A forward flow over each body's structured HIR: a local is "gone"
//! on some path from the hand-off (or the guard's `drop`) on, a use of
//! a gone local is a finding, and assigning the local again re-arms
//! it. Joins are unions (a use on any path counts); loops run to a
//! fixpoint. Values whose type is `Sync` (numbers, `str`, `Mutex`,
//! `Sender`, ...) are exempt: sharing them is safe.
// Only the local itself is tracked: a second handle copied out of it
// before the hand-off (`let ys = xs;`) is not. Captures of a spawned
// `+ Send` closure / future need no rule: they must already be `Sync`.

use std::collections::{BTreeMap, HashMap, HashSet};

use rokc_diagnostic::Span;
use rokc_ir_common::{FunctionId, LocalId};

use super::send_check::{Child, each_binding, each_child};
use super::{Env, LowerCtx};
use crate::{HirBlock, HirExpr, HirExprKind, HirFunction, HirStmt, HirTy, LintHit};

const LINT: &str = "use_after_handoff";

/// Calls that hand argument `.1` to another owner, shown as `.2`.
const HANDOFFS: &[(&str, usize, &str)] = &[
    ("rok::core::sync::Mutex__new", 0, "Mutex::new"),
    ("rok::core::sync::RwLock__new", 0, "RwLock::new"),
    ("rok::core::channel::Sender__send", 1, "Sender::send"),
    (
        "rok::core::channel::Sender__try_send",
        1,
        "Sender::try_send",
    ),
    (
        "rok::core::channel::Sender__send_async",
        1,
        "Sender::send_async",
    ),
    ("rok::core::marker::Handoff__new", 0, "Handoff::new"),
];

/// Lock guards: `get` returns, and `set` stores, a handle the lock
/// protects until `drop`.
const GUARDS: &[&str] = &[
    "rok::core::sync::MutexGuard",
    "rok::core::sync::RwLockReadGuard",
    "rok::core::sync::RwLockWriteGuard",
];

/// `name` is `path` or an instance of it (`path__mono__..`).
fn is_fn(name: &str, path: &str) -> bool {
    name.strip_prefix(path)
        .is_some_and(|rest| rest.is_empty() || rest.starts_with("__"))
}

#[derive(Clone, Copy, PartialEq)]
enum Op {
    Handoff(usize, &'static str),
    Get,
    Set,
    Drop,
}

/// The op of function `name`; `guard`: a method of a `GUARDS` type.
/// Method names end the path (`MutexGuard__get`, a `Drop` impl's
/// `__impl<hash>_drop`), before a generic instance's `__mono__..`.
fn op_of(name: &str, guard: bool) -> Option<Op> {
    if let Some(&(_, i, what)) = HANDOFFS.iter().find(|(p, ..)| is_fn(name, p)) {
        return Some(Op::Handoff(i, what));
    }
    if !guard {
        return None;
    }
    let path = name.split(rokc_ir_common::MONO_MARK).next()?;
    match path.rsplit('_').next()? {
        "get" => Some(Op::Get),
        "set" => Some(Op::Set),
        "drop" => Some(Op::Drop),
        _ => None,
    }
}

/// Why a local is gone.
#[derive(Clone, Copy, PartialEq)]
enum Gone {
    /// Handed over at this call.
    To(Span, &'static str),
    /// Tied to this guard at this span; the guard was dropped.
    Guard(Span, LocalId),
}

#[derive(Clone, Default, PartialEq)]
struct St {
    gone: BTreeMap<LocalId, Gone>,
    /// Guard local -> the locals holding what it protects.
    tied: BTreeMap<LocalId, BTreeMap<LocalId, Span>>,
}

/// `None`: unreachable.
fn join(a: Option<St>, b: Option<St>) -> Option<St> {
    match (a, b) {
        (Some(mut a), Some(b)) => {
            for (l, g) in b.gone {
                a.gone.entry(l).or_insert(g);
            }
            for (g, ls) in b.tied {
                let t = a.tied.entry(g).or_default();
                for (l, s) in ls {
                    t.entry(l).or_insert(s);
                }
            }
            Some(a)
        }
        (a, b) => a.or(b),
    }
}

struct Frame<'h> {
    label: Option<&'h str>,
    is_loop: bool,
    brk: Option<St>,
    cont: Option<St>,
}

struct Walk<'a, 'h> {
    ops: &'a HashMap<FunctionId, Op>,
    f: &'h HirFunction,
    /// Locals whose type is not `Sync` (the only ones tracked).
    tracked: HashSet<LocalId>,
    cur: Option<St>,
    frames: Vec<Frame<'h>>,
    hits: &'a mut Vec<LintHit>,
    reported: HashSet<(LocalId, u32, u32)>,
}

pub(super) fn check(env: &Env<'_>, functions: &[HirFunction]) -> Vec<LintHit> {
    let extras = env.sink.extras.borrow();
    let all: Vec<&HirFunction> = functions.iter().chain(extras.iter()).collect();
    let structs = env.defs.structs.borrow();
    let guard = |f: &HirFunction| {
        let Some(HirTy::Struct(id)) = f.params.first().filter(|p| p.name == "self").map(|p| &p.ty)
        else {
            return false;
        };
        structs.get(id.0 as usize).is_some_and(|s| {
            let base = s.name.split("__").next().unwrap_or_default();
            GUARDS.contains(&base.split('<').next().unwrap_or_default())
        })
    };
    let ops: HashMap<FunctionId, Op> = all
        .iter()
        .filter_map(|f| Some((f.id, op_of(&f.name, guard(f))?)))
        .collect();
    drop(structs);
    let mut hits = Vec::new();
    let sync = env.names.lang_item("sync_trait");
    if ops.is_empty() || sync.is_empty() {
        return hits;
    }
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None, Span::DUMMY);
    let mut cache: HashMap<String, bool> = HashMap::new();
    for f in all {
        let Some(body) = &f.body else { continue };
        let mut calls = false;
        crate::each_block(body, &mut |e| {
            calls |=
                matches!(&e.kind, HirExprKind::Call { callee, .. } if ops.contains_key(callee));
        });
        if !calls || ops.contains_key(&f.id) {
            continue;
        }
        let tracked = f
            .locals
            .iter()
            .filter(|l| {
                *cache.entry(l.ty.stable_key()).or_insert_with(|| {
                    l.ty != HirTy::Unknown
                        && !super::bounds::has_param(&ctx, &l.ty)
                        && !ctx.has_trait(&l.ty, sync)
                })
            })
            .map(|l| l.id)
            .collect();
        let mut w = Walk {
            ops: &ops,
            f,
            tracked,
            cur: Some(St::default()),
            frames: Vec::new(),
            hits: &mut hits,
            reported: HashSet::new(),
        };
        w.block(body);
    }
    hits
}

impl<'h> Walk<'_, 'h> {
    fn name(&self, l: LocalId) -> String {
        self.f
            .locals
            .iter()
            .find(|x| x.id == l)
            .and_then(|x| x.name.clone())
            .filter(|n| !n.starts_with('#'))
            .unwrap_or_else(|| "the value".to_owned())
    }

    fn use_local(&mut self, l: LocalId, at: Span) {
        let Some(g) = self.cur.as_ref().and_then(|s| s.gone.get(&l)).copied() else {
            return;
        };
        let origin = match g {
            Gone::To(s, _) | Gone::Guard(s, _) => s,
        };
        if !self.reported.insert((l, origin.file, origin.start)) {
            return;
        }
        let x = self.name(l);
        let hit = match g {
            Gone::To(s, what) => LintHit {
                lint: LINT,
                span: at,
                msg: format!("`{x}` is used after it was handed over to `{what}`"),
                secondary: Some((s, "handed over here".to_owned())),
                note: format!(
                    "rok has no move semantics: `{x}` still shares the object `{what}` now owns, \
                     so this use can race with another thread (stdlib 2.13.9); hand over a \
                     `clone()` or assign `{x}` a new value first"
                ),
            },
            Gone::Guard(s, guard) => LintHit {
                lint: LINT,
                span: at,
                msg: format!(
                    "`{x}` is used after guard `{}` released its lock",
                    self.name(guard)
                ),
                secondary: Some((s, "the guard protects it from here".to_owned())),
                note: "the lock no longer protects it, so this use can race with another thread \
                       (stdlib 2.13.9); use it inside the `using` block, or `clone()` it there"
                    .to_owned(),
            },
        };
        self.hits.push(hit);
    }

    /// `l` gets a new value.
    fn assign(&mut self, l: LocalId) {
        if let Some(s) = &mut self.cur {
            s.gone.remove(&l);
            for t in s.tied.values_mut() {
                t.remove(&l);
            }
        }
    }

    fn tie(&mut self, guard: LocalId, l: LocalId, at: Span) {
        if !self.tracked.contains(&l) {
            return;
        }
        if let Some(s) = &mut self.cur {
            s.tied.entry(guard).or_default().insert(l, at);
        }
    }

    /// The guard a `g.get()` (or a field of it) reads from.
    fn got_from(&self, e: &HirExpr) -> Option<LocalId> {
        match &e.kind {
            HirExprKind::Call { callee, args } if self.ops.get(callee) == Some(&Op::Get) => {
                local(args.first()?)
            }
            HirExprKind::FieldRead { target: x, .. }
            | HirExprKind::TupleField { target: x, .. }
            | HirExprKind::SumWrap { value: Some(x), .. } => self.got_from(x),
            HirExprKind::Block(b) if b.stmts.is_empty() => self.got_from(b.trailing.as_ref()?),
            _ => None,
        }
    }

    fn block(&mut self, b: &'h HirBlock) {
        if b.label.is_some() {
            self.frames.push(Frame {
                label: b.label.as_deref(),
                is_loop: false,
                brk: None,
                cont: None,
            });
        }
        for s in &b.stmts {
            self.stmt(s);
        }
        if let Some(t) = &b.trailing {
            self.expr(t);
        }
        if b.label.is_some() {
            let f = self.frames.pop().expect("block frame");
            self.cur = join(self.cur.take(), f.brk);
        }
    }

    fn target(&mut self, label: Option<&str>, cont: bool) -> Option<&mut Frame<'h>> {
        self.frames.iter_mut().rev().find(|f| match label {
            Some(l) => f.label == Some(l),
            None => f.is_loop,
        } && (!cont || f.is_loop))
    }

    fn stmt(&mut self, s: &'h HirStmt) {
        match s {
            HirStmt::Let { local: l, init: e } | HirStmt::Assign { local: l, value: e } => {
                self.expr(e);
                self.assign(*l);
                if let Some(g) = self.got_from(e) {
                    self.tie(g, *l, e.span);
                }
            }
            HirStmt::ArrayAssign {
                array_local,
                index,
                value,
                ..
            } => {
                self.expr(index);
                self.expr(value);
                self.use_local(*array_local, index.span);
            }
            HirStmt::StaticAssign { value: e, .. } | HirStmt::Expr(e) => self.expr(e),
            HirStmt::Return(e) => {
                if let Some(e) = e {
                    self.expr(e);
                }
                self.cur = None;
            }
            HirStmt::Panic(e) => {
                self.expr(e);
                self.cur = None;
            }
            HirStmt::Break { label, value } => {
                if let Some(e) = value {
                    self.expr(e);
                }
                let st = self.cur.take();
                if let Some(f) = self.target(label.as_deref(), false) {
                    f.brk = join(f.brk.take(), st);
                }
            }
            HirStmt::Continue { label } => {
                let st = self.cur.take();
                if let Some(f) = self.target(label.as_deref(), true) {
                    f.cont = join(f.cont.take(), st);
                }
            }
        }
    }

    /// `while` (with `cond`) or `loop`: the body runs until the state at
    /// its head stops growing.
    fn looped(&mut self, label: Option<&'h str>, cond: Option<&'h HirExpr>, body: &'h HirBlock) {
        let mut head = self.cur.take();
        loop {
            self.frames.push(Frame {
                label,
                is_loop: true,
                brk: None,
                cont: None,
            });
            self.cur.clone_from(&head);
            let mut exit = None;
            if let Some(c) = cond {
                self.expr(c);
                exit.clone_from(&self.cur);
            }
            self.block(body);
            let f = self.frames.pop().expect("loop frame");
            let next = join(head.clone(), join(self.cur.take(), f.cont));
            if next == head {
                self.cur = join(f.brk, exit);
                return;
            }
            head = next;
        }
    }

    fn expr(&mut self, e: &'h HirExpr) {
        if self.cur.is_none() {
            return;
        }
        match &e.kind {
            HirExprKind::Local(l) => self.use_local(*l, e.span),
            HirExprKind::Block(b) => self.block(b),
            HirExprKind::If {
                cond,
                then_block,
                else_branch,
            } => {
                self.expr(cond);
                let base = self.cur.clone();
                self.block(then_block);
                let then = std::mem::replace(&mut self.cur, base);
                if let Some(x) = else_branch {
                    self.expr(x);
                }
                self.cur = join(then, self.cur.take());
            }
            HirExprKind::While { label, cond, body } => {
                self.looped(label.as_deref(), Some(cond), body);
            }
            HirExprKind::Loop { label, body, .. } => self.looped(label.as_deref(), None, body),
            HirExprKind::Match { scrutinee, arms } => {
                self.expr(scrutinee);
                let base = self.cur.take();
                let mut out = None;
                for a in arms {
                    self.cur = base.clone();
                    each_binding(&a.pat, &mut |l| {
                        if let Some(s) = &mut self.cur {
                            s.gone.remove(&l);
                        }
                    });
                    if let Some(g) = &a.guard {
                        self.expr(g);
                    }
                    self.expr(&a.body);
                    out = join(out, self.cur.take());
                }
                self.cur = if arms.is_empty() { base } else { out };
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
                if let HirExprKind::Call { callee, args } = &e.kind {
                    self.call(self.ops.get(callee).copied(), args, e.span);
                }
            }
        }
    }

    fn call(&mut self, op: Option<Op>, args: &[HirExpr], at: Span) {
        let arg = |i: usize| args.get(i).and_then(local);
        match op {
            Some(Op::Handoff(i, what)) => {
                let l = arg(i).filter(|l| self.tracked.contains(l));
                if let (Some(l), Some(s)) = (l, &mut self.cur) {
                    s.gone.insert(l, Gone::To(at, what));
                }
            }
            // The lock now guards the new value, not what `get` returned.
            Some(Op::Set) => {
                let Some(g) = arg(0) else { return };
                if let Some(s) = &mut self.cur {
                    s.tied.remove(&g);
                }
                if let Some(l) = arg(1) {
                    self.tie(g, l, at);
                }
            }
            Some(Op::Drop) => {
                let (Some(g), Some(s)) = (arg(0), &mut self.cur) else {
                    return;
                };
                for (l, span) in s.tied.remove(&g).unwrap_or_default() {
                    s.gone.insert(l, Gone::Guard(span, g));
                }
            }
            Some(Op::Get) | None => {}
        }
    }
}

/// The local `e` passes as is (`x`, or `x` wrapped into a sum slot).
fn local(e: &HirExpr) -> Option<LocalId> {
    match &e.kind {
        HirExprKind::Local(l) => Some(*l),
        HirExprKind::SumWrap { value: Some(x), .. } | HirExprKind::Cast { operand: x, .. } => {
            local(x)
        }
        _ => None,
    }
}

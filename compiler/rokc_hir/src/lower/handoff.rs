//! `use_after_handoff` (stdlib 2.13.9): rok has no move semantics, so
//! handing a value to another owner (`Mutex::new(xs)`, `tx.send(xs)`,
//! `Handoff::new(xs)`) leaves `xs` pointing at the object the new owner
//! shares with other threads, and a handle taken out of a guard
//! (`g.get()`, given to it by `g.set(v)`, or reached by the closure of
//! `g.update(f)`) is unprotected once the guard's `using` block ends.
//! Using either afterwards races.
//!
//! A forward flow over each body's structured HIR. What is tracked is a
//! place: a local and a field path into it (`s`, `s.items`, `t.0`). A
//! place is "gone" on some path from the hand-off (or the guard's
//! `drop`) on, and a use of a gone place, of a place inside it, or of
//! one containing it is a finding. Aliases are edges between places:
//! a copy (`let ys = xs;`, `s.items = xs`, a struct or tuple literal
//! field) makes two places the same object, and containment (a closure
//! capturing `xs`, a list literal of it, a `match` binding of its
//! scrutinee) puts one object inside another. A place going away takes
//! every place aliased to it along. Assigning a place re-arms it and
//! drops its edges. Joins are unions (a use on any path counts); loops
//! run to a fixpoint. Uses of a `Sync` type (numbers, `str`, `Mutex`,
//! `Sender`, ...) are exempt: sharing them is safe.
// Values flowing through calls (`let ys = id(xs)`) are not followed. A
// copy `t = s` whose field `t.f` is assigned later still ties all of
// `t` to `s`. Captures of a spawned `+ Send` closure / future need no
// rule: they must already be `Sync`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use rokc_diagnostic::Span;
use rokc_ir_common::{FunctionId, LocalId};

use super::send_check::{Child, each_child};
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

/// Lock guards: `get` returns, `set` stores, and `update`'s closure
/// does both with a handle the lock protects until `drop`.
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
    Update,
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
        "update" => Some(Op::Update),
        "drop" => Some(Op::Drop),
        _ => None,
    }
}

/// Marks a tuple index in a place path (struct fields are bare).
const TUPLE: u32 = 1 << 31;
/// Longest field path followed (alias chains cannot grow past it).
const MAX_DEPTH: usize = 16;

/// A local and a field path into it.
type Place = (LocalId, Vec<u32>);

/// `a` is `b` or a place inside it.
fn within(a: &Place, b: &Place) -> bool {
    a.0 == b.0 && a.1.starts_with(&b.1)
}

/// One of `a`, `b` is inside the other: they share memory.
fn overlap(a: &Place, b: &Place) -> bool {
    within(a, b) || within(b, a)
}

fn extend(p: &Place, rest: &[u32]) -> Place {
    (p.0, [&p.1[..], rest].concat())
}

/// Why a place is gone.
#[derive(Clone, Copy, PartialEq)]
enum Gone {
    /// Handed over at this call.
    To(Span, &'static str),
    /// Tied to this guard at this span; the guard was dropped.
    Guard(Span, LocalId),
}

/// An alias: `Same` places are one object; `In(outer, inner)` holds
/// `inner` somewhere inside `outer`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Edge {
    Same(Place, Place),
    In(Place, Place),
}

impl Edge {
    fn touches(&self, p: &Place) -> bool {
        let (Self::Same(a, b) | Self::In(a, b)) = self;
        within(a, p) || within(b, p)
    }
}

#[derive(Clone, Default, PartialEq)]
struct St {
    gone: BTreeMap<Place, Gone>,
    /// Guard local -> the places holding what it protects.
    tied: BTreeMap<LocalId, BTreeMap<Place, Span>>,
    edges: BTreeSet<Edge>,
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
            a.edges.extend(b.edges);
            Some(a)
        }
        (a, b) => a.or(b),
    }
}

/// Where a value flows when stored at a place `P`: `(Some(sub), q)`
/// makes `P ++ sub` the same object as `q`, `(None, q)` puts `q`
/// inside `P`.
type Flow = (Option<Vec<u32>>, Place);

/// The place `e` reads as is (`x`, `x.f.0`, `x` wrapped into a sum
/// slot or cast).
fn place(e: &HirExpr) -> Option<Place> {
    match &e.kind {
        HirExprKind::Local(l) => Some((*l, Vec::new())),
        HirExprKind::FieldRead {
            target,
            field_index,
            ..
        } => place(target).map(|p| extend(&p, &[*field_index])),
        HirExprKind::TupleField { target, index, .. } => {
            place(target).map(|p| extend(&p, &[index | TUPLE]))
        }
        HirExprKind::SumWrap { value: Some(x), .. } | HirExprKind::Cast { operand: x, .. } => {
            place(x)
        }
        HirExprKind::Block(b) if b.stmts.is_empty() => place(b.trailing.as_ref()?),
        _ => None,
    }
}

/// The places whose objects `e`'s value carries.
fn flows(e: &HirExpr, out: &mut Vec<Flow>) {
    if let Some(p) = place(e) {
        out.push((Some(Vec::new()), p));
        return;
    }
    let field = |i: u32, x: &HirExpr, out: &mut Vec<Flow>| {
        let mut v = Vec::new();
        flows(x, &mut v);
        out.extend(
            v.into_iter()
                .map(|(sub, q)| (sub.map(|s| [&[i][..], &s].concat()), q)),
        );
    };
    let inside = |x: &HirExpr, out: &mut Vec<Flow>| {
        let mut v = Vec::new();
        flows(x, &mut v);
        out.extend(v.into_iter().map(|(_, q)| (None, q)));
    };
    match &e.kind {
        HirExprKind::StructInit { fields, .. } => {
            for (i, x) in fields.iter().enumerate() {
                field(i as u32, x, out);
            }
        }
        HirExprKind::Tuple { fields } => {
            for (i, x) in fields.iter().enumerate() {
                field(i as u32 | TUPLE, x, out);
            }
        }
        HirExprKind::WithField {
            target,
            field_index,
            value,
            ..
        } => {
            flows(target, out);
            field(*field_index, value, out);
        }
        HirExprKind::ClosureValue { env: x, .. } | HirExprKind::SumWrap { value: Some(x), .. } => {
            inside(x, out);
        }
        HirExprKind::ArrayInit { elements: xs, .. }
        | HirExprKind::EnumVariantInit { args: xs, .. } => xs.iter().for_each(|x| inside(x, out)),
        HirExprKind::Block(b) => {
            if let Some(t) = &b.trailing {
                flows(t, out);
            }
        }
        _ => {}
    }
}

struct Frame<'h> {
    label: Option<&'h str>,
    is_loop: bool,
    brk: Option<St>,
    cont: Option<St>,
}

struct Walk<'a, 'h> {
    env: &'a Env<'a>,
    ops: &'a HashMap<FunctionId, Op>,
    f: &'h HirFunction,
    /// A value of this type is not `Sync` (the only ones reported).
    tracked: &'a dyn Fn(&HirTy) -> bool,
    cur: Option<St>,
    frames: Vec<Frame<'h>>,
    hits: &'a mut Vec<LintHit>,
    reported: HashSet<(Place, u32, u32)>,
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
    let cache: RefCell<HashMap<String, bool>> = RefCell::default();
    let tracked = |t: &HirTy| {
        let key = t.stable_key();
        if let Some(&v) = cache.borrow().get(&key) {
            return v;
        }
        let v =
            *t != HirTy::Unknown && !super::bounds::has_param(&ctx, t) && !ctx.has_trait(t, sync);
        cache.borrow_mut().insert(key, v);
        v
    };
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
        let mut w = Walk {
            env,
            ops: &ops,
            f,
            tracked: &tracked,
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

    /// `e` (a place) as written: `s.items`, `t.0`.
    fn show(&self, e: &HirExpr) -> String {
        match &e.kind {
            HirExprKind::Local(l) => self.name(*l),
            HirExprKind::FieldRead {
                target,
                struct_id,
                field_index,
                ..
            } => {
                let structs = self.env.defs.structs.borrow();
                let f = structs
                    .get(struct_id.0 as usize)
                    .and_then(|s| s.fields.get(*field_index as usize))
                    .map_or_else(|| field_index.to_string(), |f| f.name.clone());
                drop(structs);
                format!("{}.{f}", self.show(target))
            }
            HirExprKind::TupleField { target, index, .. } => {
                format!("{}.{index}", self.show(target))
            }
            HirExprKind::SumWrap { value: Some(x), .. } | HirExprKind::Cast { operand: x, .. } => {
                self.show(x)
            }
            HirExprKind::Block(b) => b
                .trailing
                .as_ref()
                .map_or_else(String::new, |t| self.show(t)),
            _ => "the value".to_owned(),
        }
    }

    /// A use of place `p`, written `e` (`None`: the whole local `p.0`).
    fn use_place(&mut self, p: &Place, ty: &HirTy, written: Option<&HirExpr>, at: Span) {
        let Some((gp, g)) = self.cur.as_ref().and_then(|st| {
            st.gone
                .iter()
                .find(|(q, _)| overlap(p, q))
                .map(|(q, why)| (q.clone(), *why))
        }) else {
            return;
        };
        if !(self.tracked)(ty) {
            return;
        }
        let origin = match g {
            Gone::To(s, _) | Gone::Guard(s, _) => s,
        };
        if !self.reported.insert((gp, origin.file, origin.start)) {
            return;
        }
        let x = written.map_or_else(|| self.name(p.0), |e| self.show(e));
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

    /// `p` and every place aliased to it go away.
    fn mark_gone(&mut self, p: Place, why: Gone) {
        let Some(s) = &mut self.cur else { return };
        let mut work = vec![p];
        while let Some(q) = work.pop() {
            if q.1.len() > MAX_DEPTH || s.gone.keys().any(|g| within(&q, g)) {
                continue;
            }
            for e in &s.edges {
                match e {
                    Edge::Same(a, b) => {
                        for (x, y) in [(a, b), (b, a)] {
                            if within(&q, y) {
                                work.push(extend(x, &q.1[y.1.len()..]));
                            } else if within(y, &q) {
                                work.push(x.clone());
                            }
                        }
                    }
                    Edge::In(outer, inner) => {
                        if overlap(&q, inner) {
                            work.push(outer.clone());
                        }
                        if overlap(&q, outer) {
                            work.push(inner.clone());
                        }
                    }
                }
            }
            s.gone.retain(|g, _| !within(g, &q));
            s.gone.insert(q, why);
        }
    }

    /// `p` gets a new value: it is ours again and aliases nothing.
    fn assign(&mut self, p: &Place) {
        if let Some(s) = &mut self.cur {
            s.gone.retain(|g, _| !within(g, p));
            for t in s.tied.values_mut() {
                t.retain(|q, _| !within(q, p));
            }
            s.edges.retain(|e| !e.touches(p));
        }
    }

    /// `p` now holds `e`'s value (`part`: a part of it).
    fn store(&mut self, p: &Place, e: &HirExpr, part: bool) {
        self.assign(p);
        let mut fl = Vec::new();
        flows(e, &mut fl);
        if let Some(s) = &mut self.cur {
            for (sub, q) in fl {
                let edge = match sub {
                    _ if part => Edge::In(q, p.clone()),
                    Some(sub) => Edge::Same(extend(p, &sub), q),
                    None => Edge::In(p.clone(), q),
                };
                if !matches!(&edge, Edge::Same(a, b) if a == b) {
                    s.edges.insert(edge);
                }
            }
        }
        if let Some(g) = self.got_from(e) {
            self.tie(g, p.clone(), e.span);
        }
    }

    /// Place `p` becomes `e`. A field update of `p` itself
    /// (`p.f = v`, lowered to `p = p with f: v`) stores into `p.f`.
    fn assign_into(&mut self, p: Place, e: &'h HirExpr) {
        if let HirExprKind::WithField {
            target,
            field_index,
            value,
            ..
        } = &e.kind
        {
            if place(target).as_ref() == Some(&p) {
                return self.assign_into(extend(&p, &[*field_index]), value);
            }
        }
        self.expr(e);
        self.store(&p, e, false);
    }

    fn tie(&mut self, guard: LocalId, p: Place, at: Span) {
        if let Some(s) = &mut self.cur {
            s.tied.entry(guard).or_default().insert(p, at);
        }
    }

    /// The guard a `g.get()` (or a field of it) reads from.
    fn got_from(&self, e: &HirExpr) -> Option<LocalId> {
        match &e.kind {
            HirExprKind::Call { callee, args } if self.ops.get(callee) == Some(&Op::Get) => {
                Some(place(args.first()?)?.0)
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
                self.assign_into((*l, Vec::new()), e);
            }
            HirStmt::ArrayAssign {
                array_local,
                path,
                index,
                value,
                ..
            } => {
                self.expr(index);
                self.expr(value);
                let ty = self
                    .f
                    .locals
                    .iter()
                    .find(|x| x.id == *array_local)
                    .map(|x| &x.ty);
                if let Some(ty) = ty {
                    self.use_place(&(*array_local, path.clone()), ty, None, index.span);
                }
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
        if let Some(p) = place(e).filter(|_| {
            matches!(
                e.kind,
                HirExprKind::Local(_)
                    | HirExprKind::FieldRead { .. }
                    | HirExprKind::TupleField { .. }
            )
        }) {
            return self.use_place(&p, &e.ty, Some(e), e.span);
        }
        match &e.kind {
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
                    a.pat.each_binding(&mut |l| {
                        self.store(&(l, Vec::new()), scrutinee, true);
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
        let carried = |i: usize| {
            let mut fl = Vec::new();
            if let Some(a) = args.get(i) {
                flows(a, &mut fl);
            }
            fl.into_iter().map(|(_, q)| q).collect::<Vec<_>>()
        };
        let guard = args.first().and_then(place).map(|p| p.0);
        match op {
            Some(Op::Handoff(i, what)) => {
                for q in carried(i) {
                    self.mark_gone(q, Gone::To(at, what));
                }
            }
            // The lock now guards the new value, not what `get` returned.
            Some(Op::Set) => {
                let Some(g) = guard else { return };
                if let Some(s) = &mut self.cur {
                    s.tied.remove(&g);
                }
                for q in carried(1) {
                    self.tie(g, q, at);
                }
            }
            // The closure's captures may receive the guarded value or
            // hand theirs to the lock.
            Some(Op::Update) => {
                let Some(g) = guard else { return };
                for q in carried(1) {
                    self.tie(g, q, at);
                }
            }
            Some(Op::Drop) => {
                let Some(g) = guard else { return };
                let tied = self.cur.as_mut().and_then(|s| s.tied.remove(&g));
                for (q, span) in tied.unwrap_or_default() {
                    self.mark_gone(q, Gone::Guard(span, g));
                }
            }
            Some(Op::Get) | None => {}
        }
    }
}

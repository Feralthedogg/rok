//! Use after hand-off (stdlib 2.13.9), an error: rok has no move
//! semantics, so handing a value to another owner (`Mutex::new(xs)`,
//! `tx.send(xs)`, `Handoff::new(xs)`) leaves `xs` pointing at the object
//! the new owner shares with other threads, and a handle taken out of a
//! guard (`g.get()`, given to it by `g.set(v)`, or reached by the
//! closure of `g.update(f)`) is unprotected once the guard's `using`
//! block ends. Using either afterwards races.
//!
//! A forward flow over each body's structured HIR. What is tracked is a
//! place: a local and a field path into it (`s`, `s.items`, `t.0`). A
//! place is "gone" on some path from the hand-off (or the guard's
//! `drop`) on, and a use of a gone place, of a place inside it, or of
//! one containing it is an error. Aliases are edges between places:
//! `Same` (a copy: `let ys = xs`, `s.items = xs`, a struct or tuple
//! literal field) makes two places one object, `In` (a closure
//! capture, an array or enum literal, a `match` binding) holds one in
//! the other both ways, and `Into` (an element stored into a buffer, a
//! coroutine's arguments) holds one in the other: the buffer going away
//! takes the element along, not the reverse. A place going away takes
//! every place aliased to it along, and a value copied out of a gone
//! one is gone too. Assigning a place re-arms it: its edges are joined
//! past it and dropped, and a copy or gone place it is a field of is
//! split into its other fields. Paths are kept apart by what they know
//! of tags: a `bool`, a sum or enum variant, a carrier's error or its
//! value's tag, set by a constant, a copy or a call (below), so a test
//! of one (`if`, `while`, `match`, `catch`, `try?`, `??`) passes only
//! the paths it may let through. Paths with the same places gone are
//! one; past `MAX_PATHS`, or `MAX_SPLIT_PASSES` loop passes, all are
//! one. Joins are unions (a use on any path counts); loops run to a
//! fixpoint. Exempt: uses of a `Sync` type
//! (numbers, `str`, `Mutex`, `Sender`, ...), uses inside `unsafe` (spec
//! 4.15.2), a `match` on a variable (it reads the tag; its bindings are
//! the uses), and compiler-made locals (what they are copied into is).
//!
//! Calls are followed through summaries: what a function does with each
//! parameter (hands it over, returns it or a part of it, stores it into
//! another parameter's object, captures it into the returned closure,
//! ties it to a guard parameter), its exit state projected onto its
//! parameters as they were on entry and its return value, and what it
//! hands over by the tag of the value it returns (an error, `none`,
//! `false`): the caller's paths split by that tag at the call. An
//! `async` body's future has the tag its body ends with, and polling it
//! gives an error only if that is one, so a `catch` of `try await
//! f(xs)` sees only what `f` hands over before throwing. Summaries are
//! a fixpoint over the call graph (recursion), and a prebuilt library
//! keeps those of its bodies in its ROKHIR. A call through a function
//! value may reach any function used as a value with its parameter
//! types (closed world, as for `any` dispatch); generic functions and
//! trait methods are their instances' and `any` dispatchers' bodies;
//! `extern` functions and intrinsics keep nothing. A `Handoff::new`
//! stays inside its function: the `unsafe` code that made the protocol
//! ends it before returning.
// An element read out of a buffer is a value of its own (`pop`,
// `remove` and iteration hand out items the buffer no longer shares, or
// never touches again): reading an item back out of a buffer after
// handing it, or the buffer, over is not caught.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};
use rokc_ir_common::{ConstVal, FunctionId, LocalId, PrimOp, PrimTy};

use super::send_check::{Child, each_child};
use super::{Env, LowerCtx};
use crate::{
    HirBlock, HirExpr, HirExprKind, HirFunction, HirMatchArm, HirPattern, HirStmt, HirTy, StructId,
};

/// Who takes a value over.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum What {
    Mutex,
    RwLock,
    Channel,
    Handoff,
}

impl What {
    const fn noun(self) -> &'static str {
        match self {
            Self::Mutex => "a `Mutex`",
            Self::RwLock => "an `RwLock`",
            Self::Channel => "a channel",
            Self::Handoff => "a `Handoff`",
        }
    }

    const fn tag(self) -> &'static str {
        match self {
            Self::Mutex => "mutex",
            Self::RwLock => "rwlock",
            Self::Channel => "channel",
            Self::Handoff => "handoff",
        }
    }

    fn from_tag(s: &str) -> Option<Self> {
        [Self::Mutex, Self::RwLock, Self::Channel, Self::Handoff]
            .into_iter()
            .find(|w| w.tag() == s)
    }
}

/// Calls that hand argument `.1` to another owner `.2`.
const HANDOFFS: &[(&str, usize, What)] = &[
    ("rok::core::sync::Mutex__new", 0, What::Mutex),
    ("rok::core::sync::RwLock__new", 0, What::RwLock),
    ("rok::core::channel::Sender__send", 1, What::Channel),
    ("rok::core::channel::Sender__try_send", 1, What::Channel),
    ("rok::core::channel::Sender__send_async", 1, What::Channel),
    ("rok::core::marker::Handoff__new", 0, What::Handoff),
];

/// Lock guards: `get` returns, `set` stores, and `update`'s closure
/// does both with a handle the lock protects until `drop`.
const GUARDS: &[(&str, What)] = &[
    ("rok::core::sync::MutexGuard", What::Mutex),
    ("rok::core::sync::RwLockReadGuard", What::RwLock),
    ("rok::core::sync::RwLockWriteGuard", What::RwLock),
];

/// A future of an `async` body that may throw, and its poll: an error
/// comes out of `poll` only if the body ends with one.
const FUTURE: &str = "rok::core::future::TryAsyncFuture";
const POLL: &str = "rok::core::future::TryAsyncFuture__poll";

/// `name` is `path` or an instance of it (`path__mono__..`).
fn is_fn(name: &str, path: &str) -> bool {
    name.strip_prefix(path)
        .is_some_and(|rest| rest.is_empty() || rest.starts_with("__"))
}

#[derive(Clone, Copy, PartialEq)]
enum Op {
    Handoff(usize, What),
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
const MAX_DEPTH: usize = 12;
/// Locals the walk adds: each parameter as it was on entry, the return
/// value, and a call's arguments and result.
const SHADOW: u32 = 0x4000_0000;
const TEMP: u32 = 0x5000_0000;
/// The places holding a tested or stored value's tag (`Walk::key`).
const TAG_KEY: u32 = 0x6000_0000;
const RET: LocalId = LocalId(0x7fff_ffff);
/// The return value as a summary root.
const RET_ROOT: u32 = u32::MAX;

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

/// Where a hand-off inside a callee happened, as its callers report it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Why {
    what: What,
    /// The function that made the hand-off, as written (`Bag::store`).
    func: String,
    file: String,
    line: u32,
}

/// Why a place is gone.
#[derive(Clone, Copy, PartialEq)]
enum Gone {
    /// Handed over at this call.
    To(Span, What),
    /// Handed over by this call (a `Why` id).
    Via(Span, u32),
    /// Tied to this guard at this span; the guard was dropped.
    Guard(Span, LocalId, Tie),
}

/// How a place is tied to a guard.
#[derive(Clone, Copy, PartialEq)]
enum Tie {
    /// It holds what the guard gave out (`g.get()`).
    Taken,
    /// The guard holds it (`g.set(v)`).
    Given,
    /// It shares one of those (a copy, a part, what was stored in it).
    Shared,
}

impl Gone {
    const fn origin(self) -> Span {
        match self {
            Self::To(s, _) | Self::Via(s, _) | Self::Guard(s, ..) => s,
        }
    }
}

/// An alias: `Same` places are one object; `In(a, b)` holds one inside
/// the other (both go away together); `Into(a, b)`: `b` goes away with
/// `a`, not the reverse.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Edge {
    Same(Place, Place),
    In(Place, Place),
    Into(Place, Place),
}

impl Edge {
    const fn ends(&self) -> (&Place, &Place) {
        let (Self::Same(a, b) | Self::In(a, b) | Self::Into(a, b)) = self;
        (a, b)
    }

    fn touches(&self, p: &Place) -> bool {
        let (a, b) = self.ends();
        within(a, p) || within(b, p)
    }
}

/// The edges, under the local of each end.
#[derive(Clone, Default, PartialEq)]
struct Edges(BTreeMap<LocalId, BTreeSet<Edge>>);

impl Edges {
    fn of(&self, l: LocalId) -> impl Iterator<Item = &Edge> {
        self.0.get(&l).into_iter().flatten()
    }

    fn insert(&mut self, e: Edge) {
        let (a, b) = (e.ends().0.0, e.ends().1.0);
        if a != b {
            self.0.entry(b).or_default().insert(e.clone());
        }
        self.0.entry(a).or_default().insert(e);
    }

    fn extend(&mut self, o: Self) {
        for (l, es) in o.0 {
            self.0.entry(l).or_default().extend(es);
        }
    }

    /// Remove and return every edge with an end on `l`.
    fn take_of(&mut self, l: LocalId) -> Vec<Edge> {
        let mine: Vec<Edge> = self.0.remove(&l).into_iter().flatten().collect();
        for e in &mine {
            let (a, b) = (e.ends().0.0, e.ends().1.0);
            let other = if a == l { b } else { a };
            if let Some(es) = self.0.get_mut(&other) {
                es.remove(e);
                if es.is_empty() {
                    self.0.remove(&other);
                }
            }
        }
        mine
    }
}

#[derive(Clone, Default, PartialEq)]
struct St {
    gone: BTreeMap<Place, Gone>,
    /// Guard local -> the places holding what it protects.
    tied: BTreeMap<LocalId, BTreeMap<Place, (Span, Tie)>>,
    edges: Edges,
}

/// An edge worth keeping: between two places, of followed depth.
fn kept(e: &Edge) -> bool {
    let (a, b) = e.ends();
    a != b && a.1.len() <= MAX_DEPTH && b.1.len() <= MAX_DEPTH
}

fn join_st(mut a: St, b: St) -> St {
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
    a
}

/// What a path knows of the value at a place: a `bool`, a sum or enum
/// variant, a carrier's (`ERR`, `OK`, `OK_TAG` + its value's), or a
/// `TryAsyncFuture`'s (that of the carrier its body ends with).
type Tags = BTreeMap<Place, u32>;

/// An exit whose tag is not known (`Summary::exits`).
const ANY: u32 = u32::MAX;
/// Paths kept apart at one point; past it they are one.
const MAX_PATHS: usize = 8;
/// Loop passes with paths kept apart; then they are one.
const MAX_SPLIT_PASSES: usize = 8;

/// The paths reaching a point, apart by the tags they know (empty:
/// unreachable). Paths with the same tags are one, and so are paths
/// with the same places gone and tied (their aliases joined): only
/// those tell paths apart later.
#[derive(Clone, Default, PartialEq)]
struct Cur(Vec<(Tags, St)>);

impl Cur {
    fn start() -> Self {
        Self(vec![(Tags::new(), St::default())])
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn states(&mut self) -> impl Iterator<Item = &mut St> {
        self.0.iter_mut().map(|(_, s)| s)
    }

    fn norm(&mut self) {
        loop {
            let mut out: Vec<(Tags, St)> = Vec::with_capacity(self.0.len());
            let mut merged = false;
            for (t, s) in std::mem::take(&mut self.0) {
                match out
                    .iter_mut()
                    .find(|(u, v)| *u == t || v.gone.keys().eq(s.gone.keys()) && v.tied == s.tied)
                {
                    Some(o) => {
                        if o.0 != t {
                            o.0.retain(|k, v| t.get(k) == Some(v));
                        }
                        if o.1 != s {
                            o.1 = join_st(std::mem::take(&mut o.1), s);
                        }
                        merged = true;
                    }
                    None => out.push((t, s)),
                }
            }
            self.0 = out;
            if !merged {
                break;
            }
        }
        if self.0.len() > MAX_PATHS {
            self.flatten();
        }
        self.0.sort_by(|a, b| a.0.cmp(&b.0));
    }

    /// One path: the tags all know, the states joined.
    fn flatten(&mut self) {
        let mut it = std::mem::take(&mut self.0).into_iter();
        if let Some((mut t, mut s)) = it.next() {
            for (u, v) in it {
                t.retain(|k, x| u.get(k) == Some(x));
                s = join_st(s, v);
            }
            self.0.push((t, s));
        }
    }

    fn untag(&mut self, k: &Place) {
        let mut hit = false;
        for (t, _) in &mut self.0 {
            let n = t.len();
            t.retain(|q, _| !overlap(q, k));
            hit |= t.len() != n;
        }
        if hit {
            self.norm();
        }
    }
}

fn join(a: Cur, b: Cur) -> Cur {
    if a.is_empty() {
        return b;
    }
    if b.is_empty() {
        return a;
    }
    let mut c = a;
    c.0.extend(b.0);
    c.norm();
    c
}

/// The place `e` names exactly (`x`, `x.f.0`).
fn tag_place(e: &HirExpr) -> Option<Place> {
    match &e.kind {
        HirExprKind::Local(l) => Some((*l, Vec::new())),
        HirExprKind::FieldRead {
            target,
            field_index,
            ..
        } => tag_place(target).map(|p| extend(&p, &[*field_index])),
        HirExprKind::TupleField { target, index, .. } => {
            tag_place(target).map(|p| extend(&p, &[index | TUPLE]))
        }
        _ => None,
    }
}

/// A carrier's tag: an error, a value of unknown tag, or `OK_TAG` plus
/// the value's tag.
const OK: u32 = 0;
const ERR: u32 = 1;
const OK_TAG: u32 = 2;

/// `ty` is a carrier with a value slot (`throws -> T`, `T` not `()`).
const fn ok_slot(ty: &HirTy) -> bool {
    matches!(ty, HirTy::Throws { ok, .. } if !matches!(**ok, HirTy::Unit | HirTy::Never))
}

/// The tag of `e`'s value on a path that knows `t`.
fn tag_of(e: &HirExpr, t: &Tags) -> Option<u32> {
    match &e.kind {
        HirExprKind::Const(ConstVal::Bool(b)) => Some(u32::from(*b)),
        HirExprKind::SumWrap {
            sum_ty,
            variant_index,
            ..
        } if is_sum(sum_ty) && *sum_ty == e.ty => Some(*variant_index),
        HirExprKind::EnumVariantInit { variant_index, .. } => Some(*variant_index),
        HirExprKind::Tuple { fields } if matches!(e.ty, HirTy::Throws { .. }) => {
            match (tag_of(fields.first()?, t)?, ok_slot(&e.ty)) {
                (1, _) => Some(ERR),
                (_, true) => Some(tag_of(&fields[1], t).map_or(OK, |v| v.saturating_add(OK_TAG))),
                (_, false) => Some(OK),
            }
        }
        HirExprKind::PrimUnaryOp {
            op: PrimOp::LogicalNot,
            operand,
        } => tag_of(operand, t).map(|b| b ^ 1),
        // A carrier's `is_err`, and its value.
        HirExprKind::TupleField {
            target, index: 0, ..
        } if matches!(target.ty, HirTy::Throws { .. }) => {
            t.get(&tag_place(target)?).map(|&v| u32::from(v == ERR))
        }
        HirExprKind::TupleField {
            target, index: 1, ..
        } if ok_slot(&target.ty) => t
            .get(&tag_place(target)?)
            .and_then(|&v| v.checked_sub(OK_TAG)),
        HirExprKind::Block(b) if b.stmts.is_empty() => tag_of(b.trailing.as_ref()?, t),
        _ => t.get(&tag_place(e)?).copied(),
    }
}

const fn is_sum(ty: &HirTy) -> bool {
    matches!(ty, HirTy::Sum(_))
}

/// Pattern `p` may match a value of type `ty` with tag `v`.
fn may_match(p: &HirPattern, v: u32, ty: &HirTy) -> bool {
    match p {
        HirPattern::Literal {
            value: ConstVal::Bool(b),
            ..
        } if *ty == HirTy::Prim(PrimTy::Bool) => u32::from(*b) == v,
        HirPattern::SumVariant {
            sum_ty,
            variant_index,
            ..
        }
        | HirPattern::SumMember {
            sum_ty,
            variant_index,
            ..
        } if is_sum(ty) && sum_ty == ty => *variant_index == v,
        HirPattern::EnumVariant {
            enum_id,
            variant_index,
            ..
        } if *ty == HirTy::Enum(*enum_id) => *variant_index == v,
        HirPattern::At { sub, .. } => may_match(sub, v, ty),
        HirPattern::Or(alts) => alts.iter().any(|a| may_match(a, v, ty)),
        _ => true,
    }
}

/// Pattern `p` matches every value of type `ty` with tag `v`.
fn catches(p: &HirPattern, v: u32, ty: &HirTy) -> bool {
    match p {
        HirPattern::Wildcard | HirPattern::Binding { .. } => true,
        HirPattern::Literal {
            value: ConstVal::Bool(b),
            ..
        } => *ty == HirTy::Prim(PrimTy::Bool) && u32::from(*b) == v,
        HirPattern::SumVariant {
            sum_ty,
            variant_index,
            ..
        } => is_sum(ty) && sum_ty == ty && *variant_index == v,
        HirPattern::SumMember {
            sum_ty,
            variant_index,
            sub,
            ..
        } => is_sum(ty) && sum_ty == ty && *variant_index == v && sub.is_irrefutable(),
        HirPattern::EnumVariant {
            enum_id,
            variant_index,
            args,
        } => {
            *ty == HirTy::Enum(*enum_id)
                && *variant_index == v
                && args.iter().all(HirPattern::is_irrefutable)
        }
        HirPattern::At { sub, .. } => catches(sub, v, ty),
        HirPattern::Or(alts) => alts.iter().any(|a| catches(a, v, ty)),
        _ => false,
    }
}

/// `q` and every place aliased to it go away in `s`.
fn mark_gone(s: &mut St, p: Place, why: Gone) {
    let first = p.clone();
    let mut work = vec![p];
    while let Some(q) = work.pop() {
        // What a guard gave out: its aliases share it.
        let why = match why {
            Gone::Guard(at, g, Tie::Taken) if q != first => Gone::Guard(at, g, Tie::Shared),
            w => w,
        };
        if q.1.len() > MAX_DEPTH || s.gone.keys().any(|g| within(&q, g)) {
            continue;
        }
        for e in s.edges.of(q.0) {
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
                Edge::In(a, b) => {
                    if overlap(&q, b) {
                        work.push(a.clone());
                    }
                    if overlap(&q, a) {
                        work.push(b.clone());
                    }
                }
                Edge::Into(a, b) => {
                    if overlap(&q, a) {
                        work.push(b.clone());
                    }
                }
            }
        }
        s.gone.retain(|g, _| !within(g, &q));
        s.gone.insert(q, why);
    }
}

/// The places that are `start ++ sub` itself, through `Same` edges.
fn same_reach(s: &St, start: &Place) -> Vec<(Vec<u32>, Place)> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    let mut work = vec![(Vec::new(), start.clone())];
    while let Some((sub, c)) = work.pop() {
        if c.1.len() > MAX_DEPTH || sub.len() > MAX_DEPTH || !seen.insert(c.clone()) {
            continue;
        }
        for e in s.edges.of(c.0) {
            let Edge::Same(a, b) = e else { continue };
            for (x, y) in [(a, b), (b, a)] {
                if within(y, &c) {
                    work.push(([&sub[..], &y.1[c.1.len()..]].concat(), x.clone()));
                } else if within(&c, y) {
                    work.push((sub.clone(), extend(x, &c.1[y.1.len()..])));
                }
            }
        }
        out.push((sub, c));
    }
    out
}

/// A parameter (`RET_ROOT`: the return value) and a path into it.
type Root = (u32, Vec<u32>);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SEdge {
    Same(Root, Root),
    /// The first going away takes the second along.
    Into(Root, Root),
}

/// What a function does with its parameters, as its callers see it.
#[derive(Clone, Debug, Default)]
struct Summary {
    /// The parts of parameters the call hands over.
    gives: BTreeMap<Root, Why>,
    edges: BTreeSet<SEdge>,
    /// `(guard parameter, root)`: tied to that guard.
    ties: BTreeSet<(u32, Root)>,
    /// Exit tag (of the return value; `ANY`: not known) -> the parts of
    /// `gives` handed over on those exits. Empty: every exit hands over
    /// all of them.
    exits: BTreeMap<u32, BTreeSet<Root>>,
}

impl Summary {
    fn is_empty(&self) -> bool {
        self.gives.is_empty() && self.edges.is_empty() && self.ties.is_empty()
    }

    /// The same facts (which hand-off is named does not matter).
    fn same_facts(&self, o: &Self) -> bool {
        self.gives.keys().eq(o.gives.keys())
            && self.edges == o.edges
            && self.ties == o.ties
            && self.exits == o.exits
    }

    /// `exits`, with every exit kind spelled out.
    fn exit_kinds(&self) -> BTreeMap<u32, BTreeSet<Root>> {
        if self.exits.is_empty() {
            BTreeMap::from([(ANY, self.gives.keys().cloned().collect())])
        } else {
            self.exits.clone()
        }
    }

    /// Drop `exits` when no exit of a known tag hands over less.
    fn trim(&mut self) {
        let any = self.exits.get(&ANY).cloned().unwrap_or_default();
        let less = self
            .exits
            .iter()
            .any(|(t, r)| *t != ANY && r.union(&any).count() < self.gives.len());
        if !less {
            self.exits.clear();
        }
    }

    fn roots(&self) -> impl Iterator<Item = &Root> {
        self.gives
            .keys()
            .chain(self.edges.iter().flat_map(|e| {
                let (SEdge::Same(a, b) | SEdge::Into(a, b)) = e;
                [a, b]
            }))
            .chain(self.ties.iter().map(|(_, r)| r))
    }

    /// Parameter `i` of `self` as parameter `map(i)` (`None`: dropped).
    fn remap(&self, map: &dyn Fn(u32) -> Option<u32>) -> Self {
        let root = |r: &Root| {
            if r.0 == RET_ROOT {
                Some(r.clone())
            } else {
                map(r.0).map(|i| (i, r.1.clone()))
            }
        };
        Self {
            gives: self
                .gives
                .iter()
                .filter_map(|(r, w)| Some((root(r)?, w.clone())))
                .collect(),
            edges: self
                .edges
                .iter()
                .filter_map(|e| match e {
                    SEdge::Same(a, b) => Some(SEdge::Same(root(a)?, root(b)?)),
                    SEdge::Into(a, b) => Some(SEdge::Into(root(a)?, root(b)?)),
                })
                .collect(),
            ties: self
                .ties
                .iter()
                .filter_map(|(g, r)| Some((map(*g)?, root(r)?)))
                .collect(),
            exits: self
                .exits
                .iter()
                .map(|(t, rs)| (*t, rs.iter().filter_map(root).collect()))
                .collect(),
        }
    }

    fn merge(&mut self, o: &Self) {
        let mut exits = self.exit_kinds();
        for (t, rs) in o.exit_kinds() {
            exits.entry(t).or_default().extend(rs);
        }
        for (r, w) in &o.gives {
            self.gives.entry(r.clone()).or_insert_with(|| w.clone());
        }
        self.edges.extend(o.edges.iter().cloned());
        self.ties.extend(o.ties.iter().cloned());
        self.exits = exits;
        self.trim();
    }

    /// One line per fact, fields split by tabs (ROKHIR).
    fn encode(&self) -> String {
        let root = |r: &Root| {
            let head = if r.0 == RET_ROOT {
                "r".to_owned()
            } else {
                r.0.to_string()
            };
            std::iter::once(head)
                .chain(r.1.iter().map(u32::to_string))
                .collect::<Vec<_>>()
                .join(".")
        };
        let mut out = String::new();
        for (r, w) in &self.gives {
            out.push_str(&format!(
                "g\t{}\t{}\t{}\t{}\t{}\n",
                root(r),
                w.what.tag(),
                w.line,
                w.func,
                w.file
            ));
        }
        for e in &self.edges {
            let (k, a, b) = match e {
                SEdge::Same(a, b) => ("s", a, b),
                SEdge::Into(a, b) => ("i", a, b),
            };
            out.push_str(&format!("{k}\t{}\t{}\n", root(a), root(b)));
        }
        for (g, r) in &self.ties {
            out.push_str(&format!("t\t{g}\t{}\n", root(r)));
        }
        for (t, rs) in &self.exits {
            let t = if *t == ANY {
                "*".to_owned()
            } else {
                t.to_string()
            };
            if rs.is_empty() {
                out.push_str(&format!("x\t{t}\n"));
            }
            for r in rs {
                out.push_str(&format!("x\t{t}\t{}\n", root(r)));
            }
        }
        out
    }

    fn decode(text: &str) -> Option<Self> {
        let root = |s: &str| -> Option<Root> {
            let mut it = s.split('.');
            let head = it.next()?;
            let i = if head == "r" {
                RET_ROOT
            } else {
                head.parse().ok()?
            };
            Some((i, it.map(str::parse).collect::<Result<_, _>>().ok()?))
        };
        let mut s = Self::default();
        for line in text.lines() {
            let f: Vec<&str> = line.split('\t').collect();
            match f[..] {
                ["g", r, what, l, func, file] => {
                    s.gives.insert(
                        root(r)?,
                        Why {
                            what: What::from_tag(what)?,
                            func: func.to_owned(),
                            file: file.to_owned(),
                            line: l.parse().ok()?,
                        },
                    );
                }
                ["s", a, b] => {
                    s.edges.insert(SEdge::Same(root(a)?, root(b)?));
                }
                ["i", a, b] => {
                    s.edges.insert(SEdge::Into(root(a)?, root(b)?));
                }
                ["t", g, r] => {
                    s.ties.insert((g.parse().ok()?, root(r)?));
                }
                ["x", t, ref rest @ ..] if rest.len() <= 1 => {
                    let t = if t == "*" { ANY } else { t.parse().ok()? };
                    let rs = s.exits.entry(t).or_default();
                    if let [r] = rest {
                        rs.insert(root(r)?);
                    }
                }
                _ => return None,
            }
        }
        Some(s)
    }
}

/// The name prefix of a ROKHIR entry for the functions used as values
/// with these parameter types (`e`: a closure, its environment first).
const FN_VALUE: &str = "#fn";

/// A function used as a value: a call through a function value of its
/// parameter types may reach it.
struct Cand {
    /// A closure: parameter 0 is its environment.
    env: bool,
    keys: Vec<String>,
    from: CandFrom,
}

enum CandFrom {
    Fn(FunctionId),
    Stored(Rc<Summary>),
}

/// How a value flows when stored at a place `P`.
#[derive(Clone)]
enum Fk {
    /// `P ++ sub` is this object.
    Is(Vec<u32>),
    /// Held inside `P`, both going away together.
    Both,
    /// Held inside `P`: it goes away with `P`.
    Holds,
}

type Flow = (Fk, Place);

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

struct Frame<'h> {
    label: Option<&'h str>,
    is_loop: bool,
    brk: Cur,
    cont: Cur,
    /// Where the tag of a `break`'s value goes.
    dest: Option<Place>,
}

/// What every walk shares.
struct Checker<'a> {
    env: &'a Env<'a>,
    ctx: &'a LowerCtx<'a>,
    sync: &'a str,
    fns: HashMap<FunctionId, &'a HirFunction>,
    ops: HashMap<FunctionId, Op>,
    /// `TryAsyncFuture::poll` and its instances.
    polls: HashSet<FunctionId>,
    /// `TryAsyncFuture` and its instances.
    futures: HashSet<StructId>,
    sums: RefCell<HashMap<FunctionId, Rc<Summary>>>,
    /// A closure's or coroutine body's function -> the function it is in.
    parent: HashMap<FunctionId, FunctionId>,
    /// A call that handed something over (its span start) -> the callee.
    callees: RefCell<HashMap<(u32, u32), String>>,
    cands: HashMap<usize, Vec<Cand>>,
    tracked_memo: RefCell<HashMap<HirTy, bool>>,
    whys: RefCell<(Vec<Why>, HashMap<Why, u32>)>,
    /// A `Mutex::new` / `RwLock::new` / `Handoff::new` call (its span
    /// start) -> the variable that holds what it made, and its block.
    owners: RefCell<HashMap<(u32, u32), (String, usize)>>,
    /// A hand-off call (its span start) of a variable or field -> it as
    /// written, and its type.
    direct: RefCell<HashMap<(u32, u32), (String, String)>>,
    unsafe_regions: RefCell<HashMap<u32, Vec<(u32, u32)>>>,
}

impl Checker<'_> {
    /// A value of this type is not `Sync` (the only ones followed).
    fn tracked(&self, t: &HirTy) -> bool {
        if matches!(
            t,
            HirTy::Unknown | HirTy::Prim(_) | HirTy::Unit | HirTy::Never | HirTy::None
        ) {
            return false;
        }
        if let Some(&v) = self.tracked_memo.borrow().get(t) {
            return v;
        }
        let v = !super::bounds::has_param(self.ctx, t) && !self.ctx.has_trait(t, self.sync);
        self.tracked_memo.borrow_mut().insert(t.clone(), v);
        v
    }

    fn why_id(&self, w: Why) -> u32 {
        let mut t = self.whys.borrow_mut();
        if let Some(&i) = t.1.get(&w) {
            return i;
        }
        let i = u32::try_from(t.0.len()).unwrap_or(u32::MAX);
        t.0.push(w.clone());
        t.1.insert(w, i);
        i
    }

    fn summary(&self, id: FunctionId) -> Option<Rc<Summary>> {
        self.sums.borrow().get(&id).cloned()
    }

    fn src(&self, s: Span) -> Option<&str> {
        let (_, text) = self.env.sources.file(s.file)?;
        text.get(s.start as usize..s.end as usize)
    }

    fn file_name(&self, file: u32) -> String {
        self.env.sources.path(file).unwrap_or_default().to_owned()
    }

    /// `s` lies inside an `unsafe { .. }` block or an `unsafe fn` body.
    fn in_unsafe(&self, s: Span) -> bool {
        let mut memo = self.unsafe_regions.borrow_mut();
        let regions = memo.entry(s.file).or_insert_with(|| {
            self.env
                .sources
                .file(s.file)
                .map(|(_, text)| unsafe_regions(text))
                .unwrap_or_default()
        });
        regions.iter().any(|&(a, b)| a <= s.start && s.end <= b)
    }
}

/// The byte ranges of `unsafe { .. }` blocks and `unsafe fn` bodies.
fn unsafe_regions(text: &str) -> Vec<(u32, u32)> {
    use rokc_lexer::TokenKind as K;
    let (tokens, _) = rokc_lexer::Lexer::new(text, String::new()).lex_all();
    let close = |open: usize| {
        let mut depth = 0i32;
        tokens[open..].iter().find_map(|t| {
            match t.kind {
                K::LBrace => depth += 1,
                K::RBrace => depth -= 1,
                _ => {}
            }
            (depth == 0).then_some(t.span.end)
        })
    };
    let mut out = Vec::new();
    for (i, t) in tokens.iter().enumerate() {
        if t.kind != K::Unsafe {
            continue;
        }
        let open = match tokens.get(i + 1).map(|t| &t.kind) {
            Some(K::LBrace) => Some(i + 1),
            // The body: the first `{` outside the parameter list.
            Some(K::Fn) => {
                let mut depth = 0i32;
                tokens[i + 2..]
                    .iter()
                    .position(|t| {
                        match t.kind {
                            K::LParen | K::LBracket => depth += 1,
                            K::RParen | K::RBracket => depth -= 1,
                            _ => {}
                        }
                        depth == 0 && matches!(t.kind, K::LBrace | K::Semi)
                    })
                    .map(|k| i + 2 + k)
                    .filter(|&k| tokens[k].kind == K::LBrace)
            }
            _ => None,
        };
        if let Some(o) = open {
            if let Some(end) = close(o) {
                out.push((tokens[o].span.start, end));
            }
        }
    }
    out
}

/// The function as written: `store`, `Bag::store` (a closure or an
/// `async` body: the function it is in).
fn shown_fn(c: &Checker<'_>, f: &HirFunction) -> String {
    let mut f = f;
    while let Some(p) = c.parent.get(&f.id).and_then(|p| c.fns.get(p)) {
        f = p;
    }
    let path = f.facts.path(&f.name);
    let path = path.split("__by_").next().unwrap_or(path);
    let leaf = path.rsplit("::").next().unwrap_or(path);
    // A method of a struct of this build: `Struct<id>__name`.
    if let Some((id, m)) = leaf
        .strip_prefix("Struct")
        .and_then(|r| r.split_once("__"))
        .filter(|(id, _)| !id.is_empty() && id.bytes().all(|b| b.is_ascii_digit()))
    {
        let structs = c.env.defs.structs.borrow();
        if let Some(s) = id.parse::<usize>().ok().and_then(|i| structs.get(i)) {
            let ty = s.name.split(['<', '_']).next().unwrap_or(&s.name);
            let ty = ty.rsplit("::").next().unwrap_or(ty);
            return format!("{ty}::{m}");
        }
    }
    leaf.replace('.', "::").replace("__", "::")
}

/// Check every body; report each use after hand-off. `stored`: the
/// summaries of prebuilt libraries (ROKHIR); returned: those of this
/// build's bodies, for its ROKHIR when `export`.
pub(super) fn check(
    env: &Env<'_>,
    functions: &[HirFunction],
    stored: &[(String, String)],
    export: bool,
) -> Vec<(String, String)> {
    let sync = env.names.lang_item("sync_trait");
    if sync.is_empty() {
        return Vec::new();
    }
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
            let base = base.split('<').next().unwrap_or_default();
            GUARDS.iter().any(|(g, _)| *g == base)
        })
    };
    let mut ops = HashMap::new();
    let mut polls = HashSet::new();
    for f in &all {
        if let Some(op) = op_of(&f.name, guard(f)) {
            ops.insert(f.id, op);
        }
        if is_fn(&f.name, POLL) {
            polls.insert(f.id);
        }
    }
    #[allow(clippy::cast_possible_truncation)]
    let futures = structs
        .iter()
        .enumerate()
        .filter(|(_, s)| {
            let base = s.name.split("__").next().unwrap_or_default();
            base.split('<').next() == Some(FUTURE)
        })
        .map(|(i, _)| StructId(i as u32))
        .collect();
    drop(structs);
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None, Span::DUMMY);
    let by_name: HashMap<&str, &str> = stored
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect();
    let mut sums = HashMap::new();
    for f in all.iter().filter(|f| f.body.is_none()) {
        if let Some(s) = by_name
            .get(f.name.as_str())
            .and_then(|t| Summary::decode(t))
        {
            sums.insert(f.id, Rc::new(s));
        }
    }
    let c = Checker {
        env,
        ctx: &ctx,
        sync,
        fns: all.iter().map(|f| (f.id, *f)).collect(),
        ops,
        polls,
        futures,
        sums: RefCell::new(sums),
        parent: parents(&all),
        callees: RefCell::default(),
        cands: HashMap::new(),
        tracked_memo: RefCell::default(),
        whys: RefCell::default(),
        owners: RefCell::default(),
        direct: RefCell::default(),
        unsafe_regions: RefCell::default(),
    };
    let mut c = c;
    c.cands = candidates(&c, &all, stored);
    let c = c;

    // The bodies worth a walk: one holding a value that is not `Sync`.
    let walked: Vec<&HirFunction> = all
        .iter()
        .copied()
        .filter(|f| {
            f.body.is_some()
                && !c.ops.contains_key(&f.id)
                && (c.tracked(&f.ret_ty) || f.locals.iter().any(|l| c.tracked(&l.ty)))
        })
        .collect();

    // Summaries to a fixpoint, callees first.
    let order = postorder(&walked);
    let mut readers: HashMap<FunctionId, HashSet<FunctionId>> = HashMap::new();
    let mut queue: std::collections::VecDeque<FunctionId> = order.iter().copied().collect();
    let mut queued: HashSet<FunctionId> = queue.iter().copied().collect();
    let mut budget = 40 * order.len() + 1000;
    // A function's last walk saw its callees' final summaries (a change
    // walks its readers again): its errors are those of that walk.
    let mut found: HashMap<FunctionId, Vec<RokDiagnostic>> = HashMap::new();
    while let Some(id) = queue.pop_front() {
        queued.remove(&id);
        let f = c.fns[&id];
        let ((s, deps), errs) = walk(&c, f);
        found.insert(id, errs);
        if budget == 0 {
            continue;
        }
        budget -= 1;
        for d in deps {
            readers.entry(d).or_default().insert(id);
        }
        let changed = c
            .summary(id)
            .is_none_or(|old| !(old.same_facts(&s) || old.is_empty() && s.is_empty()));
        if changed {
            c.sums.borrow_mut().insert(id, Rc::new(s));
            for r in readers.get(&id).into_iter().flatten() {
                if queued.insert(*r) {
                    queue.push_back(*r);
                }
            }
        }
    }
    let mut diags: Vec<RokDiagnostic> = walked
        .iter()
        .filter_map(|f| found.remove(&f.id))
        .flatten()
        .collect();
    let mut seen = HashSet::new();
    diags.retain(|d: &RokDiagnostic| {
        let at = d.primary.as_ref().map(|l| (l.span.file, l.span.start));
        seen.insert((at, d.message.clone()))
    });
    env.sink.diagnostics.borrow_mut().extend(diags);

    if !export {
        return Vec::new();
    }
    let sums = c.sums.borrow();
    let mut out: Vec<(String, String)> = walked
        .iter()
        .filter(|f| !f.name.contains(rokc_ir_common::MONO_MARK))
        .filter_map(|f| {
            let s = sums.get(&f.id).filter(|s| !s.is_empty())?;
            Some((f.name.clone(), s.encode()))
        })
        .collect();
    // The functions used as values, by parameter types.
    let mut by_sig: BTreeMap<String, Summary> = BTreeMap::new();
    for cs in c.cands.values() {
        for k in cs {
            let CandFrom::Fn(id) = &k.from else { continue };
            let Some(s) = sums.get(id).filter(|s| !s.is_empty()) else {
                continue;
            };
            let name = std::iter::once(format!("{FN_VALUE}{}", if k.env { "e" } else { "" }))
                .chain(k.keys.iter().cloned())
                .collect::<Vec<_>>()
                .join("\u{1f}");
            by_sig.entry(name).or_default().merge(s);
        }
    }
    out.extend(by_sig.into_iter().map(|(n, s)| (n, s.encode())));
    out
}

/// The functions used as values (and the stored ones of prebuilt
/// libraries), by their parameter count without the environment.
fn candidates(
    c: &Checker<'_>,
    all: &[&HirFunction],
    stored: &[(String, String)],
) -> HashMap<usize, Vec<Cand>> {
    let mut used: BTreeMap<FunctionId, bool> = BTreeMap::new();
    for f in all {
        let Some(body) = &f.body else { continue };
        crate::each_block(body, &mut |e| match &e.kind {
            HirExprKind::FnRef(id) => {
                used.entry(*id).or_insert(false);
            }
            HirExprKind::ClosureValue { fn_id, .. } => {
                used.insert(*fn_id, true);
            }
            _ => {}
        });
    }
    let mut out: HashMap<usize, Vec<Cand>> = HashMap::new();
    for (id, env) in used {
        let Some(f) = c.fns.get(&id) else { continue };
        if c.ops.contains_key(&id) {
            continue;
        }
        let keys: Vec<String> = f
            .params
            .iter()
            .skip(usize::from(env))
            .map(|p| p.ty.stable_key())
            .collect();
        out.entry(keys.len()).or_default().push(Cand {
            env,
            keys,
            from: CandFrom::Fn(id),
        });
    }
    for (name, text) in stored {
        let mut parts = name.split('\u{1f}');
        let Some(head) = parts.next().and_then(|h| h.strip_prefix(FN_VALUE)) else {
            continue;
        };
        let Some(s) = Summary::decode(text) else {
            continue;
        };
        let keys: Vec<String> = parts.map(str::to_owned).collect();
        out.entry(keys.len()).or_default().push(Cand {
            env: head == "e",
            keys,
            from: CandFrom::Stored(Rc::new(s)),
        });
    }
    out
}

/// Each closure's and coroutine body's function -> the one making it.
fn parents(all: &[&HirFunction]) -> HashMap<FunctionId, FunctionId> {
    let mut out = HashMap::new();
    for f in all {
        let Some(body) = &f.body else { continue };
        crate::each_block(body, &mut |e| {
            if let HirExprKind::ClosureValue { fn_id: id, .. }
            | HirExprKind::CoroNew { body_fn: id, .. } = &e.kind
            {
                if *id != f.id {
                    out.entry(*id).or_insert(f.id);
                }
            }
        });
    }
    out
}

/// `fns` callees before callers (by direct calls).
fn postorder(fns: &[&HirFunction]) -> Vec<FunctionId> {
    let ids: HashSet<FunctionId> = fns.iter().map(|f| f.id).collect();
    let callees: HashMap<FunctionId, Vec<FunctionId>> = fns
        .iter()
        .map(|f| {
            let mut v = Vec::new();
            if let Some(b) = &f.body {
                crate::each_block(b, &mut |e| {
                    if let HirExprKind::Call { callee: id, .. }
                    | HirExprKind::CoroNew { body_fn: id, .. }
                    | HirExprKind::ClosureValue { fn_id: id, .. } = &e.kind
                    {
                        if ids.contains(id) {
                            v.push(*id);
                        }
                    }
                });
            }
            (f.id, v)
        })
        .collect();
    let mut done = HashSet::new();
    let mut out = Vec::new();
    for f in fns {
        let mut stack = vec![(f.id, 0usize)];
        while let Some((id, i)) = stack.pop() {
            if i == 0 && !done.insert(id) {
                continue;
            }
            let next = callees[&id].get(i).copied();
            match next {
                Some(n) => {
                    stack.push((id, i + 1));
                    if !done.contains(&n) {
                        stack.push((n, 0));
                    }
                }
                None => out.push(id),
            }
        }
    }
    out
}

type WalkOut = ((Summary, HashSet<FunctionId>), Vec<RokDiagnostic>);

fn walk(c: &Checker<'_>, f: &HirFunction) -> WalkOut {
    let mut w = Walk {
        c,
        f,
        cur: Cur::start(),
        frames: Vec::new(),
        exits: BTreeMap::new(),
        mixed: false,
        keys: HashMap::new(),
        dests: Vec::new(),
        pinned: HashSet::new(),
        reported: HashSet::new(),
        temps: HashMap::new(),
        temp_tys: HashMap::new(),
        results: HashMap::new(),
        calls: Vec::new(),
        scopes: Vec::new(),
        returning: false,
        deps: HashSet::new(),
        diags: Vec::new(),
    };
    // Each parameter as it came in: what the caller passed.
    for (i, p) in f.params.iter().enumerate() {
        if c.tracked(&p.ty) {
            let s = shadow(i);
            for st in w.cur.states() {
                st.edges
                    .insert(Edge::Same((s, Vec::new()), (p.local, Vec::new())));
            }
        }
    }
    let body = f.body.as_ref().expect("walked bodies have one");
    crate::each_block(body, &mut |e| {
        if let HirExprKind::AddrOf { place } = &e.kind {
            let mut x = &**place;
            while let HirExprKind::FieldRead { target: t, .. }
            | HirExprKind::TupleField { target: t, .. }
            | HirExprKind::ArrayIndex { array: t, .. } = &x.kind
            {
                x = t;
            }
            if let HirExprKind::Local(l) = x.kind {
                w.pinned.insert(l);
            }
        }
    });
    w.block_to(body, Some(&RET_TAG));
    if let (Some(t), false) = (&body.trailing, w.cur.is_empty()) {
        w.store(&(RET, Vec::new()), t, false);
    }
    w.exit_with(Some(&RET_TAG));
    let s = w.summarize();
    ((s, w.deps), w.diags)
}

#[allow(clippy::cast_possible_truncation)]
const fn shadow(i: usize) -> LocalId {
    LocalId(SHADOW + i as u32)
}

/// Where a returned (or a coroutine's step) value's tag goes.
const RET_TAG: Place = (LocalId(0x7fff_fffe), Vec::new());

struct Walk<'c, 'h> {
    c: &'c Checker<'c>,
    f: &'h HirFunction,
    cur: Cur,
    frames: Vec<Frame<'h>>,
    /// The states at the returns, by the returned value's tag.
    exits: BTreeMap<u32, St>,
    /// A coroutine step before the last one may be an error.
    mixed: bool,
    /// The places holding the tags of values being tested or stored (by
    /// the expression's address).
    keys: HashMap<usize, LocalId>,
    /// Calls (by address) whose value's tag goes to a place, innermost
    /// last.
    dests: Vec<(usize, Place)>,
    /// Locals whose address is taken: no tag is kept for them.
    pinned: HashSet<LocalId>,
    reported: HashSet<(Place, u32, u32)>,
    /// A call's (by address) argument / result slot -> its local.
    temps: HashMap<(usize, u32), LocalId>,
    temp_tys: HashMap<LocalId, HirTy>,
    /// What a call's value carries (by address).
    results: HashMap<usize, Vec<Flow>>,
    /// The calls being walked, innermost last (for the hints).
    calls: Vec<&'h HirExpr>,
    /// The blocks being walked (by address), innermost last.
    scopes: Vec<usize>,
    /// Walking a `return`'s value.
    returning: bool,
    /// The summaries this walk read.
    deps: HashSet<FunctionId>,
    diags: Vec<RokDiagnostic>,
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
                let structs = self.c.env.defs.structs.borrow();
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

    fn local_ty(&self, l: LocalId) -> Option<HirTy> {
        if l == RET {
            return Some(self.f.ret_ty.clone());
        }
        if (SHADOW..TEMP).contains(&l.0) {
            return self
                .f
                .params
                .get((l.0 - SHADOW) as usize)
                .map(|p| p.ty.clone());
        }
        if let Some(t) = self.temp_tys.get(&l) {
            return Some(t.clone());
        }
        self.f
            .locals
            .iter()
            .find(|x| x.id == l)
            .map(|x| x.ty.clone())
    }

    /// The fields of a value of type `t` worth following, by path step.
    fn fields(&self, t: &HirTy) -> Option<Vec<(u32, HirTy)>> {
        let all: Vec<(u32, HirTy)> = match t {
            HirTy::Struct(id) => {
                let structs = self.c.env.defs.structs.borrow();
                let s = structs.get(id.0 as usize)?;
                #[allow(clippy::cast_possible_truncation)]
                s.fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (i as u32, f.ty.clone()))
                    .collect()
            }
            #[allow(clippy::cast_possible_truncation)]
            HirTy::Tuple(ts) => ts
                .iter()
                .enumerate()
                .map(|(i, t)| (i as u32 | TUPLE, t.clone()))
                .collect(),
            _ => return None,
        };
        Some(all.into_iter().filter(|(_, t)| self.c.tracked(t)).collect())
    }

    fn place_ty(&self, p: &Place) -> Option<HirTy> {
        let mut t = self.local_ty(p.0)?;
        for step in &p.1 {
            t = self.fields(&t)?.into_iter().find(|(k, _)| k == step)?.1;
        }
        Some(t)
    }

    /// The paths below `base` (relative to it) that cover it except
    /// `base ++ rel` (`None`: its type is not known).
    fn split(&self, base: &Place, rel: &[u32]) -> Option<Vec<Vec<u32>>> {
        let Some((&k0, rest)) = rel.split_first() else {
            return Some(Vec::new());
        };
        let t = self.place_ty(base)?;
        let mut out = Vec::new();
        for (k, _) in self.fields(&t)? {
            if k == k0 {
                let below = self.split(&extend(base, &[k]), rest)?;
                out.extend(below.into_iter().map(|s| [&[k][..], &s].concat()));
            } else {
                out.push(vec![k]);
            }
        }
        Some(out)
    }

    /// A use of place `p`, written `e` (`None`: the whole local `p.0`).
    fn use_place(&mut self, p: &Place, ty: &HirTy, written: Option<&HirExpr>, at: Span) {
        let Some((gp, g)) = self.cur.0.iter().find_map(|(_, st)| {
            st.gone
                .iter()
                .find(|(q, _)| overlap(p, q))
                .map(|(q, why)| (q.clone(), *why))
        }) else {
            return;
        };
        // A compiler-made local (`#..`) is not reported: what it is copied
        // into is.
        if !self.c.tracked(ty)
            || self.c.in_unsafe(at)
            || self.copy_out(written, at)
            || self.hidden(p.0)
        {
            return;
        }
        let origin = g.origin();
        if !self.reported.insert((gp, origin.file, origin.start)) {
            return;
        }
        let x = written.map_or_else(|| self.name(p.0), |e| self.show(e));
        let d = self.diagnostic(&x, g, written, at);
        self.diags.push(d);
    }

    fn hidden(&self, l: LocalId) -> bool {
        self.f
            .locals
            .iter()
            .find(|x| x.id == l)
            .is_some_and(|x| x.name.as_ref().is_none_or(|n| n.starts_with('#')))
    }

    /// `e` is the value of a `ref` parameter going back to the caller
    /// (not written in the source): the caller sees what is gone of it.
    fn copy_out(&self, e: Option<&HirExpr>, at: Span) -> bool {
        let Some(HirExprKind::Local(l)) = e.map(|e| &e.kind) else {
            return false;
        };
        self.f.params.iter().any(|p| p.local == *l && p.by_ref)
            && self.c.src(at).is_some_and(|t| t != self.name(*l))
    }

    /// `at`: where the line of `s` is, said from the use at `from`.
    fn line(&self, s: Span, from: Span) -> String {
        if s.file == from.file {
            format!("line {}", s.line)
        } else {
            let path = self.c.file_name(s.file);
            let name = path.rsplit(['/', '\\']).next().unwrap_or(&path);
            format!("{name}:{}", s.line)
        }
    }

    /// The call `e` is an argument (or receiver) of, rewritten with
    /// `with` in place of `e`: `xs.push(i)` -> `g.get().push(i)`.
    fn in_call(&self, e: Option<&HirExpr>, with: &str) -> String {
        let fallback = with.to_owned();
        let Some(e) = e else { return fallback };
        let Some(call) = self.calls.last().filter(|c| {
            let (HirExprKind::Call { args, .. }
            | HirExprKind::CallIndirect { args, .. }
            | HirExprKind::CallClosure { args, .. }) = &c.kind
            else {
                return false;
            };
            args.iter().any(|a| a.span == e.span)
        }) else {
            return fallback;
        };
        let (Some(text), true) = (
            self.c.src(call.span),
            call.span.file == e.span.file
                && call.span.start <= e.span.start
                && e.span.end <= call.span.end,
        ) else {
            return fallback;
        };
        let (a, b) = (
            (e.span.start - call.span.start) as usize,
            (e.span.end - call.span.start) as usize,
        );
        if text.len() > 60 || text.contains('\n') || !text.is_char_boundary(a) {
            return fallback;
        }
        format!("{}{with}{}", &text[..a], &text[b..])
    }

    fn diagnostic(
        &self,
        who: &str,
        gone: Gone,
        written: Option<&HirExpr>,
        at: Span,
    ) -> RokDiagnostic {
        let chk = self.c;
        let err = |msg: String| RokDiagnostic::error(ErrorKind::Handoff, at, msg);
        let keep = format!("pass `{who}.clone()` to keep a separate copy");
        match gone {
            Gone::To(site, what) => {
                let owner = chk
                    .owners
                    .borrow()
                    .get(&(site.file, site.start))
                    .filter(|(_, b)| self.scopes.contains(b))
                    .map(|(n, _)| n.clone());
                let (arg, arg_ty) = chk
                    .direct
                    .borrow()
                    .get(&(site.file, site.start))
                    .cloned()
                    .unzip();
                let line = self.line(site, at);
                let (moved, here) = match what {
                    What::Mutex => ("moved into the `Mutex`", "moved into the `Mutex` here"),
                    What::RwLock => ("moved into the `RwLock`", "moved into the `RwLock` here"),
                    What::Channel => ("sent through a channel", "sent here"),
                    What::Handoff => ("handed to a `Handoff`", "handed over here"),
                };
                // The hand-off itself again, on the loop's next pass.
                if self.calls.last().is_some_and(|k| k.span == site) {
                    return err(format!(
                        "`{who}` was already {moved} by this call, on an earlier pass of the loop"
                    ))
                    .with_note(format!(
                        "help: hand over `{who}.clone()` so each pass hands over its own copy, or \
                         make `{who}` inside the loop (stdlib 2.13.9)"
                    ));
                }
                // Another handle to what was handed over.
                let (head, given) = match arg.as_deref().filter(|arg| *arg != who) {
                    Some(arg) => (
                        format!("`{who}` shares `{arg}`, which was {moved}"),
                        arg.to_owned(),
                    ),
                    None => (format!("`{who}` was {moved}"), who.to_owned()),
                };
                let keep = format!("hand over `{given}.clone()` to keep a separate copy");
                let diag = err(format!("{head} at {line}"))
                    .with_secondary(site, format!("`{given}` {here}"));
                match what {
                    What::Mutex | What::RwLock => {
                        let (ty, lock) = if what == What::Mutex {
                            ("Mutex", "lock")
                        } else {
                            ("RwLock", "write")
                        };
                        let through = match owner {
                            Some(lock_var) => {
                                let same = written
                                    .is_some_and(|e| arg_ty.as_ref() == Some(&e.ty.stable_key()));
                                let body = if same {
                                    self.in_call(written, "g.get()")
                                } else {
                                    ".. g.get() ..".to_owned()
                                };
                                format!(
                                    "use it through the lock: `using g = {lock_var}.{lock}() {{ {body} }}`"
                                )
                            }
                            None => format!(
                                "use it through the `{ty}`'s lock (`g.get()` inside its `using` \
                                 block)"
                            ),
                        };
                        diag.with_note(format!(
                            "help: it belongs to the `{ty}` now; {through}, or {keep} (stdlib \
                             2.13.9)"
                        ))
                    }
                    What::Channel => diag.with_note(format!(
                        "help: the receiver owns it now; {keep}, or give `{who}` a new value before \
                         using it again (stdlib 2.13.9)"
                    )),
                    What::Handoff => {
                        let getter = owner.map_or_else(
                            || "the `Handoff`'s `get()`".to_owned(),
                            |own| format!("`{own}.get()`"),
                        );
                        diag.with_note(format!(
                            "help: the `Handoff` owns it now; read it through {getter}, or {keep} \
                             (stdlib 2.13.9)"
                        ))
                    }
                }
            }
            Gone::Via(site, id) => {
                let why = chk.whys.borrow().0[id as usize].clone();
                let callee = chk.callees.borrow().get(&(site.file, site.start)).cloned();
                let text = chk.src(site).filter(|t| t.len() <= 60 && !t.contains('\n'));
                let named = text.is_some_and(|t| t.contains(who));
                let call = text
                    .map(|t| format!("`{t}`"))
                    .or_else(|| callee.map(|n| format!("this call of `{n}`")))
                    .unwrap_or_else(|| "this call".to_owned());
                let verb = match why.what {
                    What::Mutex | What::RwLock => format!("moved into {}", why.what.noun()),
                    What::Channel => "sent through a channel".to_owned(),
                    What::Handoff => "handed to a `Handoff`".to_owned(),
                };
                let file = why.file.rsplit(['/', '\\']).next().unwrap_or(&why.file);
                let inner = if chk.file_name(site.file) == why.file {
                    format!("line {}", why.line)
                } else {
                    format!("{file}:{}", why.line)
                };
                let head = if named {
                    format!("`{who}` was {verb} by {call}")
                } else {
                    format!("`{who}` shares what {call} {verb}")
                };
                err(format!(
                    "{head} at {} (inside `{}`, {inner})",
                    self.line(site, at),
                    why.func
                ))
                .with_secondary(site, format!("{verb} here"))
                .with_note(format!(
                    "help: {} now; pass a `.clone()` to keep a separate copy, or give `{who}` a new \
                     value before using it again (stdlib 2.13.9)",
                    match why.what {
                        What::Channel => "the receiver owns it".to_owned(),
                        What::Handoff => "the `Handoff` owns it".to_owned(),
                        What::Mutex | What::RwLock => format!("it belongs to {}", why.what.noun()),
                    }
                ))
            }
            Gone::Guard(site, guard, tie_kind) => {
                let gname = self.name(guard);
                let what = self.guard_what(guard);
                let ty = if what == What::RwLock {
                    "RwLock"
                } else {
                    "Mutex"
                };
                let line = self.line(site, at);
                let tie = chk
                    .src(site)
                    .filter(|t| t.len() <= 24 && !t.contains('\n'))
                    .map(str::to_owned);
                if tie_kind == Tie::Given {
                    err(format!("`{who}` was given to the `{ty}` at {line}"))
                        .with_secondary(site, format!("`{who}` given to the lock here"))
                        .with_note(format!(
                            "help: `{who}` belongs to the `{ty}` now; use it through the lock \
                             (`{gname}.get()` inside a `using` block), or {keep} (stdlib 2.13.9)"
                        ))
                } else if self.returning {
                    let copy = tie.map_or_else(
                        || "a `.clone()` of it".to_owned(),
                        |t| format!("`{t}.clone()`"),
                    );
                    err(format!(
                        "this returns a value out of the `{ty}` after `{gname}`'s `using` \
                         block released the lock"
                    ))
                    .with_secondary(site, "taken out of the lock here")
                    .with_note(format!(
                        "help: the lock no longer protects it; return {copy}, or do the work \
                         inside the `using` block (stdlib 2.13.9)"
                    ))
                } else if tie_kind == Tie::Shared {
                    let from = tie.map_or_else(String::new, |t| format!(" (`{t}`)"));
                    err(format!(
                        "`{who}` shares the value the `{ty}` protects{from} at {line}, and \
                         `{gname}`'s `using` block released the lock"
                    ))
                    .with_secondary(site, "the lock's value, taken out here")
                    .with_note(format!(
                        "help: the lock no longer protects `{who}`; use it inside the `using` \
                         block, or {keep} (stdlib 2.13.9)"
                    ))
                } else {
                    let copy = format!("keep a separate copy there with `{gname}.get().clone()`");
                    err(format!(
                        "`{who}` came out of the `{ty}` at {line}, and `{gname}`'s `using` block \
                         released the lock"
                    ))
                    .with_secondary(site, format!("`{who}` taken out of the lock here"))
                    .with_note(format!(
                        "help: the lock no longer protects `{who}`; use it inside the `using` \
                         block, or {copy} (stdlib 2.13.9)"
                    ))
                }
            }
        }
    }

    /// The lock a guard local belongs to.
    fn guard_what(&self, g: LocalId) -> What {
        let structs = self.c.env.defs.structs.borrow();
        let ty = self.local_ty(g);
        let name = match &ty {
            Some(HirTy::Struct(id)) => structs.get(id.0 as usize).map(|s| s.name.clone()),
            _ => None,
        };
        drop(structs);
        name.and_then(|n| {
            GUARDS
                .iter()
                .find(|(p, _)| n.starts_with(p))
                .map(|(_, w)| *w)
        })
        .unwrap_or(What::Mutex)
    }

    fn mark_gone(&mut self, p: Place, why: Gone) {
        for s in self.cur.states() {
            mark_gone(s, p.clone(), why);
        }
    }

    /// `p` is not gone any more; a gone place it is a field of: its other
    /// fields stay gone.
    fn regain(&self, s: &mut St, p: &Place) {
        let wider: Vec<(Place, Gone)> = s
            .gone
            .iter()
            .filter(|(g, _)| within(p, g) && g.1.len() < p.1.len())
            .map(|(g, w)| (g.clone(), *w))
            .collect();
        s.gone.retain(|g, _| !within(g, p) && !within(p, g));
        for (g, why) in wider {
            match self.split(&g, &p.1[g.1.len()..]) {
                Some(rest) => {
                    for r in rest {
                        s.gone.insert(extend(&g, &r), why);
                    }
                }
                None => {
                    s.gone.insert(g, why);
                }
            }
        }
    }

    /// `p` gets a new value: it is ours again and aliases nothing. Edges
    /// through it are joined past it first: what aliased its old value
    /// still aliases each other.
    fn assign(&mut self, p: &Place) {
        let mut cur = std::mem::take(&mut self.cur);
        for (_, s) in &mut cur.0 {
            *s = self.assign_st(std::mem::take(s), p);
        }
        cur.untag(p);
        self.cur = cur;
    }

    fn assign_st(&self, mut s: St, p: &Place) -> St {
        self.regain(&mut s, p);
        for t in s.tied.values_mut() {
            t.retain(|q, _| !within(q, p));
        }
        let (touch, keep): (Vec<Edge>, Vec<Edge>) =
            s.edges.take_of(p.0).into_iter().partition(|e| e.touches(p));
        let mut edges: BTreeSet<Edge> = BTreeSet::new();
        // A copy that `p` is a field of: its other fields stay copies.
        for e in keep {
            let Edge::Same(a, b) = &e else {
                edges.insert(e);
                continue;
            };
            let (base, other) = if within(p, a) {
                (a, b)
            } else if within(p, b) {
                (b, a)
            } else {
                edges.insert(e);
                continue;
            };
            match self.split(base, &p.1[base.1.len()..]) {
                Some(rest) => {
                    for r in rest {
                        edges.insert(Edge::Same(extend(base, &r), extend(other, &r)));
                    }
                }
                None => {
                    edges.insert(e);
                }
            }
        }
        // A copy of all of `p`'s old value stands in for it in the rest.
        let rep = touch.iter().find_map(|e| match e {
            Edge::Same(a, b) if a == p && !within(b, p) => Some(b.clone()),
            Edge::Same(a, b) if b == p && !within(a, p) => Some(a.clone()),
            _ => None,
        });
        if let Some(r) = rep {
            let swap = |u: &Place| {
                if within(u, p) {
                    extend(&r, &u.1[p.1.len()..])
                } else {
                    u.clone()
                }
            };
            for e in &touch {
                let e = match e {
                    Edge::Same(a, b) => Edge::Same(swap(a), swap(b)),
                    Edge::In(a, b) => Edge::In(swap(a), swap(b)),
                    Edge::Into(a, b) => Edge::Into(swap(a), swap(b)),
                };
                edges.insert(e);
            }
            for e in edges.into_iter().filter(kept) {
                s.edges.insert(e);
            }
            return s;
        }
        // Each end in `p`: (end, other end, other ⇒ end, end ⇒ other, same).
        let mut ends: Vec<(Place, Place, bool, bool, bool)> = Vec::new();
        for e in &touch {
            let (a, b) = e.ends();
            for (u, x, fwd) in [(a, b, true), (b, a, false)] {
                if !within(u, p) || within(x, p) {
                    continue;
                }
                let (to_u, from_u, same) = match e {
                    Edge::Same(..) => (true, true, true),
                    Edge::In(..) => (true, true, false),
                    // `Into(a, b)`: a ⇒ b.
                    Edge::Into(..) => (!fwd, fwd, false),
                };
                ends.push((u.clone(), x.clone(), to_u, from_u, same));
            }
        }
        for (i, (u1, x1, to1, from1, same1)) in ends.iter().enumerate() {
            for (u2, x2, to2, from2, same2) in &ends[i + 1..] {
                if !overlap(u1, u2) || x1 == x2 {
                    continue;
                }
                if *same1 && *same2 {
                    let e = if within(u2, u1) {
                        Edge::Same(extend(x1, &u2.1[u1.1.len()..]), x2.clone())
                    } else {
                        Edge::Same(x1.clone(), extend(x2, &u1.1[u2.1.len()..]))
                    };
                    edges.insert(e);
                    continue;
                }
                let fwd = *to1 && *from2;
                let back = *to2 && *from1;
                match (fwd, back) {
                    (true, true) => edges.insert(Edge::In(x1.clone(), x2.clone())),
                    (true, false) => edges.insert(Edge::Into(x1.clone(), x2.clone())),
                    (false, true) => edges.insert(Edge::Into(x2.clone(), x1.clone())),
                    (false, false) => false,
                };
            }
        }
        for e in edges.into_iter().filter(kept) {
            s.edges.insert(e);
        }
        s
    }

    /// What `e`'s value carries, of the places this walk knows.
    fn flows(&self, e: &HirExpr, out: &mut Vec<Flow>) {
        if !self.c.tracked(&e.ty) {
            return;
        }
        if let Some(p) = place(e) {
            out.push((Fk::Is(Vec::new()), p));
            return;
        }
        let sub = |s: &Self, i: u32, x: &HirExpr, out: &mut Vec<Flow>| {
            let mut v = Vec::new();
            s.flows(x, &mut v);
            out.extend(v.into_iter().map(|(k, q)| match k {
                Fk::Is(s) => (Fk::Is([&[i][..], &s].concat()), q),
                k => (k, q),
            }));
        };
        let as_kind = |s: &Self, x: &HirExpr, k: &Fk, out: &mut Vec<Flow>| {
            let mut v = Vec::new();
            s.flows(x, &mut v);
            out.extend(v.into_iter().map(|(_, q)| (k.clone(), q)));
        };
        match &e.kind {
            HirExprKind::StructInit { fields, .. } => {
                for (i, x) in fields.iter().enumerate() {
                    #[allow(clippy::cast_possible_truncation)]
                    sub(self, i as u32, x, out);
                }
            }
            HirExprKind::Tuple { fields } => {
                for (i, x) in fields.iter().enumerate() {
                    #[allow(clippy::cast_possible_truncation)]
                    sub(self, i as u32 | TUPLE, x, out);
                }
            }
            HirExprKind::WithField {
                target,
                field_index,
                value,
                ..
            } => {
                self.flows(target, out);
                sub(self, *field_index, value, out);
            }
            HirExprKind::FieldRead {
                target,
                field_index: i,
                ..
            }
            | HirExprKind::TupleField {
                target, index: i, ..
            } => {
                let i = if matches!(e.kind, HirExprKind::TupleField { .. }) {
                    i | TUPLE
                } else {
                    *i
                };
                let mut v = Vec::new();
                self.flows(target, &mut v);
                for (k, q) in v {
                    match k {
                        Fk::Is(s) if s.is_empty() => out.push((Fk::Is(s), extend(&q, &[i]))),
                        Fk::Is(s) if s[0] == i => out.push((Fk::Is(s[1..].to_vec()), q)),
                        Fk::Is(_) => {}
                        k => out.push((k, q)),
                    }
                }
            }
            HirExprKind::SumWrap { value: Some(x), .. } | HirExprKind::Cast { operand: x, .. } => {
                self.flows(x, out);
            }
            HirExprKind::ClosureValue { env: x, .. } => as_kind(self, x, &Fk::Both, out),
            HirExprKind::ArrayInit { elements: xs, .. }
            | HirExprKind::EnumVariantInit { args: xs, .. } => {
                xs.iter().for_each(|x| as_kind(self, x, &Fk::Both, out));
            }
            HirExprKind::Block(b) => self.block_flows(b, out),
            HirExprKind::If {
                then_block,
                else_branch,
                ..
            } => {
                self.block_flows(then_block, out);
                if let Some(x) = else_branch {
                    self.flows(x, out);
                }
            }
            HirExprKind::Match { arms, .. } => arms.iter().for_each(|a| self.flows(&a.body, out)),
            HirExprKind::Call { .. }
            | HirExprKind::CallIndirect { .. }
            | HirExprKind::CallClosure { .. }
            | HirExprKind::CoroNew { .. } => {
                if let Some(v) = self.results.get(&addr(e)) {
                    out.extend(v.iter().cloned());
                }
            }
            _ => {}
        }
    }

    fn block_flows(&self, b: &HirBlock, out: &mut Vec<Flow>) {
        if let Some(t) = &b.trailing {
            self.flows(t, out);
        }
    }

    /// `p` now holds `e`'s value (`part`: a part of it).
    fn store(&mut self, p: &Place, e: &HirExpr, part: bool) {
        self.assign(p);
        let mut fl = Vec::new();
        self.flows(e, &mut fl);
        for s in self.cur.states() {
            // What is gone of the value stays gone in `p` (a call's result
            // that its callee handed over).
            let mut inherit = Vec::new();
            for (k, q) in &fl {
                for (g, why) in s.gone.iter().filter(|(g, _)| overlap(g, q)) {
                    match k {
                        Fk::Is(sub) if !part => {
                            let rest = g.1.get(q.1.len()..).unwrap_or_default();
                            inherit.push((extend(p, &[&sub[..], rest].concat()), *why));
                        }
                        Fk::Is(_) | Fk::Both => inherit.push((p.clone(), *why)),
                        Fk::Holds => {}
                    }
                }
            }
            for (k, q) in &fl {
                let edge = match k {
                    Fk::Is(sub) if !part => Edge::Same(extend(p, sub), q.clone()),
                    Fk::Is(_) | Fk::Both => Edge::In(p.clone(), q.clone()),
                    Fk::Holds => Edge::Into(p.clone(), q.clone()),
                };
                if kept(&edge) {
                    s.edges.insert(edge);
                }
            }
            for (q, why) in inherit {
                mark_gone(s, q, why);
            }
        }
        if let Some(g) = self.got_from(e) {
            self.tie(g, p.clone(), e.span, Tie::Taken);
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
        let k = self.key(e);
        self.expr_to(e, &k);
        self.store(&p, e, false);
        self.retag(&k, &p);
        // The variable that holds a new lock / `Handoff`: named in hints.
        let mut init = e;
        while let HirExprKind::Block(blk) = &init.kind {
            match (&blk.trailing, blk.stmts.is_empty()) {
                (Some(t), true) => init = t,
                _ => break,
            }
        }
        if let HirExprKind::Call { callee, .. } = &init.kind {
            if matches!(self.c.ops.get(callee), Some(Op::Handoff(_, w)) if *w != What::Channel)
                && p.1.is_empty()
            {
                let owner = (
                    self.name(p.0),
                    self.scopes.last().copied().unwrap_or_default(),
                );
                self.c
                    .owners
                    .borrow_mut()
                    .insert((init.span.file, init.span.start), owner);
            }
        }
    }

    fn tie(&mut self, guard: LocalId, p: Place, at: Span, given: Tie) {
        for s in self.cur.states() {
            s.tied
                .entry(guard)
                .or_default()
                .entry(p.clone())
                .or_insert((at, given));
        }
    }

    /// The guard a `g.get()` (or a field of it) reads from.
    fn got_from(&self, e: &HirExpr) -> Option<LocalId> {
        match &e.kind {
            HirExprKind::Call { callee, args } if self.c.ops.get(callee) == Some(&Op::Get) => {
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
        self.block_to(b, None);
    }

    /// Block `b`; the tag of its value goes to `k`.
    fn block_to(&mut self, b: &'h HirBlock, k: Option<&Place>) {
        self.scopes.push(std::ptr::from_ref(b) as usize);
        if b.label.is_some() {
            self.frames.push(Frame {
                label: b.label.as_deref(),
                is_loop: false,
                brk: Cur::default(),
                cont: Cur::default(),
                dest: k.cloned(),
            });
        }
        for s in &b.stmts {
            self.stmt(s);
        }
        if let Some(t) = &b.trailing {
            self.value(t, k);
        }
        if b.label.is_some() {
            let f = self.frames.pop().expect("block frame");
            self.cur = join(std::mem::take(&mut self.cur), f.brk);
        }
        self.scopes.pop();
    }

    fn value(&mut self, e: &'h HirExpr, k: Option<&Place>) {
        match k {
            Some(k) => self.expr_to(e, k),
            None => self.expr(e),
        }
    }

    /// The place holding the tag of `e`'s value while it is tested or
    /// stored.
    fn key(&mut self, e: &HirExpr) -> Place {
        let n = self.keys.len();
        #[allow(clippy::cast_possible_truncation)]
        let l = *self
            .keys
            .entry(addr(e))
            .or_insert(LocalId(TAG_KEY + n as u32));
        (l, Vec::new())
    }

    /// The tags at `from` move to `to`.
    fn retag(&mut self, from: &Place, to: &Place) {
        let pinned = self.pinned.contains(&to.0);
        for (t, _) in &mut self.cur.0 {
            let moved: Vec<(Place, u32)> = t
                .iter()
                .filter(|(q, _)| within(q, from))
                .map(|(q, v)| (extend(to, &q.1[from.1.len()..]), *v))
                .collect();
            t.retain(|q, _| !within(q, from));
            if !pinned {
                t.extend(moved);
            }
        }
    }

    /// `e`; the tag of its value goes to `k` on the paths that know it.
    fn expr_to(&mut self, e: &'h HirExpr, k: &Place) {
        if self.cur.is_empty() {
            return;
        }
        for (t, _) in &mut self.cur.0 {
            t.retain(|q, _| !within(q, k));
        }
        match &e.kind {
            HirExprKind::Block(b) => {
                let returning = std::mem::take(&mut self.returning);
                self.returning = returning && b.stmts.is_empty();
                self.block_to(b, Some(k));
            }
            HirExprKind::If {
                cond,
                then_block,
                else_branch,
            } => {
                self.returning = false;
                self.branch(cond, then_block, else_branch.as_deref(), Some(k));
            }
            HirExprKind::Match { scrutinee, arms } => {
                self.returning = false;
                self.matched(scrutinee, arms, Some(k));
            }
            HirExprKind::Loop { label, body, .. } => {
                self.returning = false;
                self.looped(label.as_deref(), None, body, Some(k));
            }
            HirExprKind::Call { .. }
            | HirExprKind::CallIndirect { .. }
            | HirExprKind::CallClosure { .. }
            | HirExprKind::CoroNew { .. } => self.expr_into(e, e, k),
            HirExprKind::PrimUnaryOp {
                op: PrimOp::LogicalNot,
                operand,
            } => {
                self.expr_to(operand, k);
                for (t, _) in &mut self.cur.0 {
                    if let Some(v) = t.get_mut(k) {
                        *v ^= 1;
                    }
                }
            }
            // A future's tag is its body's.
            HirExprKind::StructInit { struct_id, fields }
                if self.c.futures.contains(struct_id)
                    && matches!(&fields[..], [x] if matches!(x.kind, HirExprKind::CoroNew { .. })) =>
            {
                self.expr_into(e, &fields[0], k);
            }
            _ => {
                self.expr(e);
                let copied = tag_place(e).filter(|_| {
                    !matches!(&e.kind, HirExprKind::TupleField { target, .. }
                        if matches!(target.ty, HirTy::Throws { .. }))
                });
                for (t, _) in &mut self.cur.0 {
                    if let Some(q) = &copied {
                        let got: Vec<(Place, u32)> = t
                            .iter()
                            .filter(|(p, _)| within(p, q))
                            .map(|(p, v)| (extend(k, &p.1[q.1.len()..]), *v))
                            .collect();
                        t.extend(got);
                    } else if let Some(v) = tag_of(e, t) {
                        t.insert(k.clone(), v);
                    }
                }
            }
        }
    }

    /// `e`, whose call `call` gives the tag of its value to `k`.
    fn expr_into(&mut self, e: &'h HirExpr, call: &HirExpr, k: &Place) {
        self.dests.push((addr(call), k.clone()));
        self.expr(e);
        self.dests.pop();
    }

    /// Walk `cond`: the paths on which it may be true, and false.
    fn test(&mut self, cond: &'h HirExpr) -> (Cur, Cur) {
        let k = self.key(cond);
        self.expr_to(cond, &k);
        let (mut yes, mut no) = (Cur::default(), Cur::default());
        for (mut t, s) in std::mem::take(&mut self.cur.0) {
            match t.remove(&k) {
                Some(1) => yes.0.push((t, s)),
                Some(0) => no.0.push((t, s)),
                _ => {
                    no.0.push((t.clone(), s.clone()));
                    yes.0.push((t, s));
                }
            }
        }
        yes.norm();
        no.norm();
        (yes, no)
    }

    fn branch(
        &mut self,
        cond: &'h HirExpr,
        then_block: &'h HirBlock,
        else_branch: Option<&'h HirExpr>,
        k: Option<&Place>,
    ) {
        let (yes, no) = self.test(cond);
        self.cur = yes;
        self.block_to(then_block, k);
        let then = std::mem::replace(&mut self.cur, no);
        if let Some(x) = else_branch {
            self.value(x, k);
        }
        self.cur = join(then, std::mem::take(&mut self.cur));
    }

    /// Matching a variable reads its tag (in the value itself) and binds
    /// its parts: the uses are the bindings'. An arm sees the paths whose
    /// tag it may match and no arm before it takes.
    fn matched(&mut self, scrutinee: &'h HirExpr, arms: &'h [HirMatchArm], k: Option<&Place>) {
        let key = if place(scrutinee).is_none() {
            let ks = self.key(scrutinee);
            self.expr_to(scrutinee, &ks);
            Some((ks, true))
        } else {
            tag_place(scrutinee).map(|p| (p, false))
        };
        let mut base = std::mem::take(&mut self.cur);
        let ty = &scrutinee.ty;
        let mut out = Cur::default();
        for (i, a) in arms.iter().enumerate() {
            let mut cur = Cur::default();
            for (t, s) in &base.0 {
                if let Some(&v) = key.as_ref().and_then(|(p, _)| t.get(p)) {
                    let taken = arms[..i]
                        .iter()
                        .any(|b| b.guard.is_none() && catches(&b.pat, v, ty));
                    if taken || !may_match(&a.pat, v, ty) {
                        continue;
                    }
                }
                cur.0.push((t.clone(), s.clone()));
            }
            if let Some((ks, true)) = &key {
                cur.untag(ks);
            }
            self.cur = cur;
            a.pat.each_binding(&mut |l| {
                self.store(&(l, Vec::new()), scrutinee, true);
            });
            if let Some(g) = &a.guard {
                self.expr(g);
            }
            self.value(&a.body, k);
            out = join(out, std::mem::take(&mut self.cur));
        }
        if let Some((ks, true)) = &key {
            base.untag(ks);
        }
        self.cur = if arms.is_empty() { base } else { out };
    }

    /// The paths reach an exit; `k` holds the returned value's tag.
    fn exit_with(&mut self, k: Option<&Place>) {
        for (t, s) in std::mem::take(&mut self.cur.0) {
            let tag = k.and_then(|k| t.get(k)).copied().unwrap_or(ANY);
            let s = match self.exits.remove(&tag) {
                Some(e) => join_st(e, s),
                None => s,
            };
            self.exits.insert(tag, s);
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
                let arr = (*array_local, path.clone());
                if let Some(ty) = self.local_ty(*array_local) {
                    self.use_place(&arr, &ty, None, index.span);
                }
                self.hold(&arr, value);
            }
            HirStmt::StaticAssign { value: e, .. } | HirStmt::Expr(e) => self.expr(e),
            HirStmt::Return(e) => {
                if let Some(e) = e {
                    self.returning = place(e).is_some();
                    self.expr_to(e, &RET_TAG);
                    self.returning = false;
                    self.store(&(RET, Vec::new()), e, false);
                }
                self.exit_with(Some(&RET_TAG));
            }
            HirStmt::Panic(e) => {
                self.expr(e);
                self.cur = Cur::default();
            }
            HirStmt::Break { label, value } => {
                if let Some(e) = value {
                    let k = self
                        .target(label.as_deref(), false)
                        .and_then(|f| f.dest.clone());
                    self.value(e, k.as_ref());
                }
                let st = std::mem::take(&mut self.cur);
                if let Some(f) = self.target(label.as_deref(), false) {
                    f.brk = join(std::mem::take(&mut f.brk), st);
                }
            }
            HirStmt::Continue { label } => {
                let st = std::mem::take(&mut self.cur);
                if let Some(f) = self.target(label.as_deref(), true) {
                    f.cont = join(std::mem::take(&mut f.cont), st);
                }
            }
        }
    }

    /// The places whose objects hold the buffer `e` (`self.h[0].buf`
    /// is held by `self.h`).
    fn holders(&self, e: &HirExpr, out: &mut Vec<Place>) {
        if let Some(p) = place(e) {
            out.push(p);
            return;
        }
        match &e.kind {
            HirExprKind::BufGet { buf: x, .. }
            | HirExprKind::ArrayIndex { array: x, .. }
            | HirExprKind::FieldRead { target: x, .. }
            | HirExprKind::TupleField { target: x, .. }
            | HirExprKind::Cast { operand: x, .. } => self.holders(x, out),
            _ => {
                let mut fl = Vec::new();
                self.flows(e, &mut fl);
                out.extend(fl.into_iter().map(|(_, q)| q));
            }
        }
    }

    /// The buffer at `c` now holds `v`: `v` goes away with it.
    fn hold(&mut self, c: &Place, v: &HirExpr) {
        let mut fl = Vec::new();
        self.flows(v, &mut fl);
        for s in self.cur.states() {
            for (_, q) in &fl {
                if q != c {
                    s.edges.insert(Edge::Into(c.clone(), q.clone()));
                }
            }
        }
    }

    /// `while` (with `cond`) or `loop`: the body runs until the state at
    /// its head stops growing.
    fn looped(
        &mut self,
        label: Option<&'h str>,
        cond: Option<&'h HirExpr>,
        body: &'h HirBlock,
        k: Option<&Place>,
    ) {
        let mut head = std::mem::take(&mut self.cur);
        for pass in 0.. {
            self.frames.push(Frame {
                label,
                is_loop: true,
                brk: Cur::default(),
                cont: Cur::default(),
                dest: k.cloned(),
            });
            self.cur.clone_from(&head);
            let mut exit = Cur::default();
            if let Some(c) = cond {
                let (yes, no) = self.test(c);
                self.cur = yes;
                exit = no;
            }
            self.block(body);
            let f = self.frames.pop().expect("loop frame");
            let cur = std::mem::take(&mut self.cur);
            let mut next = join(head.clone(), join(cur, f.cont));
            if pass >= MAX_SPLIT_PASSES {
                next.flatten();
            }
            if next == head {
                self.cur = join(f.brk, exit);
                return;
            }
            head = next;
        }
    }

    fn expr(&mut self, e: &'h HirExpr) {
        if self.cur.is_empty() {
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
        let returning = std::mem::take(&mut self.returning);
        match &e.kind {
            HirExprKind::Block(b) => {
                self.returning = returning && b.stmts.is_empty();
                self.block(b);
            }
            HirExprKind::If {
                cond,
                then_block,
                else_branch,
            } => self.branch(cond, then_block, else_branch.as_deref(), None),
            HirExprKind::While { label, cond, body } => {
                self.looped(label.as_deref(), Some(cond), body, None);
            }
            HirExprKind::Loop { label, body, .. } => {
                self.looped(label.as_deref(), None, body, None);
            }
            HirExprKind::Match { scrutinee, arms } => self.matched(scrutinee, arms, None),
            // A step handed to the resumer; the last one ends the body.
            HirExprKind::Suspend { value, is_final } => {
                self.expr_to(value, &RET_TAG);
                if *is_final {
                    self.exit_with(Some(&RET_TAG));
                } else {
                    let mut mixed = false;
                    for (t, _) in &mut self.cur.0 {
                        mixed |= t.remove(&RET_TAG).is_none_or(|v| v == ERR);
                    }
                    self.mixed |= mixed;
                    self.cur.norm();
                }
            }
            _ => {
                let is_call = matches!(
                    e.kind,
                    HirExprKind::Call { .. }
                        | HirExprKind::CallIndirect { .. }
                        | HirExprKind::CallClosure { .. }
                );
                if is_call {
                    self.calls.push(e);
                }
                let mut kids = Vec::new();
                each_child(e, &mut |c| kids.push(c));
                for c in kids {
                    match c {
                        Child::E(x) => self.expr(x),
                        Child::B(b) => self.block(b),
                    }
                }
                if is_call {
                    self.calls.pop();
                }
                self.after(e);
            }
        }
    }

    /// The effect of `e` once its operands ran.
    fn after(&mut self, e: &'h HirExpr) {
        match &e.kind {
            HirExprKind::Call { callee, args } => {
                if let Some(op) = self.c.ops.get(callee).copied() {
                    return self.op(op, args, e.span);
                }
                let args: Vec<&HirExpr> = args.iter().collect();
                if let Some(s) = self.callee(*callee) {
                    if !s.gives.is_empty() {
                        if let Some(f) = self.c.fns.get(callee) {
                            let n = shown_fn(self.c, f);
                            self.c
                                .callees
                                .borrow_mut()
                                .insert((e.span.file, e.span.start), n);
                        }
                    }
                    self.apply(&s, &args, e, true);
                }
                if self.c.polls.contains(callee) {
                    self.polled(e, args.first().copied());
                }
            }
            HirExprKind::CallIndirect { callee, args, .. } => {
                let mut all = vec![&**callee];
                all.extend(args.iter());
                let s = match &callee.kind {
                    HirExprKind::FnRef(id) => {
                        self.callee(*id).map(|s| Rc::new(s.remap(&|i| Some(i + 1))))
                    }
                    _ => self.indirect(args),
                };
                if let Some(s) = s {
                    self.apply(&s, &all, e, true);
                }
            }
            HirExprKind::CallClosure { closure, args, .. } => {
                let mut all = vec![&**closure];
                all.extend(args.iter());
                let s = match &closure.kind {
                    HirExprKind::ClosureValue { fn_id, .. } => self.callee(*fn_id),
                    _ => self.indirect(args),
                };
                if let Some(s) = s {
                    self.apply(&s, &all, e, true);
                }
            }
            HirExprKind::CoroNew { body_fn, args } => {
                let args: Vec<&HirExpr> = args.iter().collect();
                if let Some(s) = self.callee(*body_fn) {
                    self.apply(&s, &args, e, false);
                }
                // The frame holds the arguments until it runs.
                let mut v = Vec::new();
                for a in &args {
                    let mut fl = Vec::new();
                    self.flows(a, &mut fl);
                    v.extend(fl.into_iter().map(|(_, q)| (Fk::Holds, q)));
                }
                self.results.insert(addr(e), v);
            }
            HirExprKind::BufSet { buf, value, .. } => {
                let mut cs = Vec::new();
                self.holders(buf, &mut cs);
                for c in cs {
                    self.hold(&c, value);
                }
            }
            _ => {}
        }
    }

    fn callee(&mut self, id: FunctionId) -> Option<Rc<Summary>> {
        self.deps.insert(id);
        self.c.summary(id).filter(|s| !s.is_empty())
    }

    /// A call through a function value with these arguments: every
    /// function used as a value with their types (argument 0 is the
    /// function value).
    fn indirect(&mut self, args: &[HirExpr]) -> Option<Rc<Summary>> {
        let c = self.c;
        let cands = c.cands.get(&args.len())?;
        let mut out = Summary::default();
        for k in cands {
            let fits = k.keys.iter().zip(args).all(|(key, a)| {
                matches!(a.ty, HirTy::Unknown | HirTy::Any) || *key == a.ty.stable_key()
            });
            if !fits {
                continue;
            }
            let s = match &k.from {
                CandFrom::Fn(id) => {
                    self.deps.insert(*id);
                    match c.summary(*id) {
                        Some(s) => s,
                        None => continue,
                    }
                }
                CandFrom::Stored(s) => s.clone(),
            };
            let env = k.env;
            out.merge(&s.remap(&|i| Some(if env { i } else { i + 1 })));
        }
        (!out.is_empty()).then(|| Rc::new(out))
    }

    /// Run summary `s` at call `e` with these arguments (`ret`: its
    /// value is the function's return value).
    fn apply(&mut self, s: &Summary, args: &[&HirExpr], e: &HirExpr, ret: bool) {
        let key = addr(e);
        let used: BTreeSet<u32> = s.roots().map(|r| r.0).collect();
        // Each parameter's object: a local holding the argument.
        let mut slot: HashMap<u32, Place> = HashMap::new();
        for (i, a) in args.iter().enumerate() {
            #[allow(clippy::cast_possible_truncation)]
            let i = i as u32;
            if !used.contains(&i) || !self.c.tracked(&a.ty) {
                continue;
            }
            let t = (self.temp(key, i, &a.ty), Vec::new());
            self.store(&t, a, false);
            slot.insert(i, t);
        }
        if ret && used.contains(&RET_ROOT) && self.c.tracked(&e.ty) {
            let t = (self.temp(key, RET_ROOT, &e.ty), Vec::new());
            self.assign(&t);
            self.results
                .insert(key, vec![(Fk::Is(Vec::new()), t.clone())]);
            slot.insert(RET_ROOT, t);
        }
        let map = |r: &Root| slot.get(&r.0).map(|p| extend(p, &r.1));
        for edge in &s.edges {
            let e = match edge {
                SEdge::Same(a, b) => map(a).zip(map(b)).map(|(a, b)| Edge::Same(a, b)),
                SEdge::Into(a, b) => map(a).zip(map(b)).map(|(a, b)| Edge::Into(a, b)),
            };
            if let Some(e) = e.filter(|e| e.ends().0 != e.ends().1) {
                for st in self.cur.states() {
                    st.edges.insert(e.clone());
                }
            }
        }
        for (g, r) in &s.ties {
            let guard = args
                .get(*g as usize)
                .and_then(|a| place(a))
                .filter(|p| p.1.is_empty());
            if let (Some(guard), Some(p)) = (guard, map(r)) {
                self.tie(guard.0, p, e.span, Tie::Taken);
            }
        }
        let given: Vec<(&Root, Place, Gone)> = s
            .gives
            .iter()
            .filter_map(|(r, why)| {
                let id = self.c.why_id(why.clone());
                Some((r, map(r)?, Gone::Via(e.span, id)))
            })
            .collect();
        // Apart by how the call ends, when its value's tag is followed.
        let dest = self.dest_of(e);
        let (Some(dest), false) = (dest, s.exits.is_empty()) else {
            for (_, p, why) in given {
                self.mark_gone(p, why);
            }
            return;
        };
        let none = BTreeSet::new();
        let any = s.exits.get(&ANY).unwrap_or(&none);
        let mut out = Cur::default();
        for (t, st) in std::mem::take(&mut self.cur.0) {
            for (tag, roots) in &s.exits {
                let (mut t, mut st) = (t.clone(), st.clone());
                if *tag != ANY {
                    t.insert(dest.clone(), *tag);
                }
                for (r, p, why) in &given {
                    if roots.contains(*r) || *tag != ANY && any.contains(*r) {
                        mark_gone(&mut st, p.clone(), *why);
                    }
                }
                out.0.push((t, st));
            }
        }
        out.norm();
        self.cur = out;
    }

    /// Where the tag of call `e`'s value goes.
    fn dest_of(&self, e: &HirExpr) -> Option<Place> {
        let a = addr(e);
        self.dests
            .iter()
            .rev()
            .find(|(x, _)| *x == a)
            .map(|(_, p)| p.clone())
    }

    /// `e` polled future `fut` (`poll(ref self, ref ctx)`): its value
    /// is `(step, fut, ctx)`, and the step is no error if `fut`'s body
    /// ends with none.
    fn polled(&mut self, e: &HirExpr, fut: Option<&HirExpr>) {
        let (Some(dest), Some(f)) = (self.dest_of(e), fut.and_then(tag_place)) else {
            return;
        };
        for (t, _) in &mut self.cur.0 {
            if let Some(&v) = t.get(&f) {
                t.insert(extend(&dest, &[1 | TUPLE]), v);
                if v != ERR {
                    t.insert(extend(&dest, &[TUPLE]), OK);
                }
            }
        }
    }

    fn temp(&mut self, key: usize, slot: u32, ty: &HirTy) -> LocalId {
        let n = self.temps.len();
        let l = *self.temps.entry((key, slot)).or_insert_with(|| {
            #[allow(clippy::cast_possible_truncation)]
            LocalId(TEMP + n as u32)
        });
        self.temp_tys.insert(l, ty.clone());
        l
    }

    /// A lock op or a hand-off.
    fn op(&mut self, op: Op, args: &[HirExpr], at: Span) {
        let carried = |w: &Self, i: usize| {
            let mut fl = Vec::new();
            if let Some(a) = args.get(i) {
                w.flows(a, &mut fl);
            }
            fl.into_iter().map(|(_, q)| q).collect::<Vec<_>>()
        };
        let guard = args.first().and_then(place).map(|p| p.0);
        match op {
            Op::Handoff(i, what) => {
                if let Some(a) = args.get(i).filter(|a| place(a).is_some()) {
                    let shown = self.show(a);
                    self.c
                        .direct
                        .borrow_mut()
                        .insert((at.file, at.start), (shown, a.ty.stable_key()));
                }
                for q in carried(self, i) {
                    self.mark_gone(q, Gone::To(at, what));
                }
            }
            // The lock now guards the new value, not what `get` returned.
            Op::Set => {
                let Some(g) = guard else { return };
                for s in self.cur.states() {
                    s.tied.remove(&g);
                }
                for q in carried(self, 1) {
                    self.tie(g, q, at, Tie::Given);
                }
            }
            // The closure's captures may receive the guarded value or
            // hand theirs to the lock.
            Op::Update => {
                let Some(g) = guard else { return };
                for q in carried(self, 1) {
                    self.tie(g, q, at, Tie::Shared);
                }
            }
            Op::Drop => {
                let Some(g) = guard else { return };
                for s in self.cur.states() {
                    for (q, (span, tie)) in s.tied.remove(&g).unwrap_or_default() {
                        mark_gone(s, q, Gone::Guard(span, g, tie));
                    }
                }
            }
            Op::Get => {}
        }
    }

    /// What `exit` has handed over of the parameters.
    fn gives(&self, exit: &St) -> BTreeMap<Root, Why> {
        let mut out = BTreeMap::new();
        let root_of = |l: LocalId| -> Option<u32> {
            if l == RET {
                Some(RET_ROOT)
            } else if (SHADOW..TEMP).contains(&l.0) {
                Some(l.0 - SHADOW)
            } else {
                None
            }
        };
        let me = shown_fn(self.c, self.f);
        for (q, g) in &exit.gone {
            let Some(r) = root_of(q.0).filter(|&r| r != RET_ROOT) else {
                continue;
            };
            // A `Handoff` protocol is the `unsafe` code's: it ends before
            // the function that made it returns.
            if matches!(g, Gone::To(_, What::Handoff)) {
                continue;
            }
            let why = match *g {
                Gone::To(at, what) => Why {
                    what,
                    func: me.clone(),
                    file: self.c.file_name(at.file),
                    line: at.line,
                },
                Gone::Via(_, id) => self.c.whys.borrow().0[id as usize].clone(),
                Gone::Guard(at, guard, _) => Why {
                    what: self.guard_what(guard),
                    func: me.clone(),
                    file: self.c.file_name(at.file),
                    line: at.line,
                },
            };
            out.insert((r, q.1.clone()), why);
        }
        out
    }

    /// The walk's exit state as its callers see it.
    fn summarize(&self) -> Summary {
        let mut s = Summary::default();
        let Some(exit) = self.exits.values().cloned().reduce(join_st) else {
            return s;
        };
        let exit = &exit;
        s.gives = self.gives(exit);
        if !self.mixed && self.exits.keys().any(|&t| t != ANY) {
            s.exits = self
                .exits
                .iter()
                .map(|(t, st)| (*t, self.gives(st).into_keys().collect()))
                .collect();
            s.trim();
        }
        let root_of = |l: LocalId| -> Option<u32> {
            if l == RET {
                Some(RET_ROOT)
            } else if (SHADOW..TEMP).contains(&l.0) {
                Some(l.0 - SHADOW)
            } else {
                None
            }
        };
        let mut roots: Vec<(u32, Place)> = self
            .f
            .params
            .iter()
            .enumerate()
            .filter(|(_, p)| self.c.tracked(&p.ty))
            .map(|(i, _)| {
                #[allow(clippy::cast_possible_truncation)]
                (i as u32, (shadow(i), Vec::new()))
            })
            .collect();
        if self.c.tracked(&self.f.ret_ty) {
            roots.push((RET_ROOT, (RET, Vec::new())));
        }
        for (r, start) in &roots {
            let same = same_reach(exit, start);
            for (sub, q) in &same {
                if let Some(r2) = root_of(q.0) {
                    if (r2, &q.1) != (*r, sub) {
                        let (a, b) = ((*r, sub.clone()), (r2, q.1.clone()));
                        s.edges
                            .insert(SEdge::Same(a.clone().min(b.clone()), a.max(b)));
                    }
                }
            }
            let mut probe = St {
                gone: BTreeMap::new(),
                tied: BTreeMap::new(),
                edges: exit.edges.clone(),
            };
            mark_gone(
                &mut probe,
                start.clone(),
                Gone::To(Span::DUMMY, What::Mutex),
            );
            for q in probe.gone.keys() {
                let Some(r2) = root_of(q.0).filter(|r2| r2 != r) else {
                    continue;
                };
                let implied = same.iter().any(|(_, p)| within(q, p));
                if !implied {
                    s.edges
                        .insert(SEdge::Into((*r, Vec::new()), (r2, q.1.clone())));
                }
            }
        }
        for (g, tied) in &exit.tied {
            let Some(i) = self.f.params.iter().position(|p| p.local == *g) else {
                continue;
            };
            let mut probe = St {
                gone: BTreeMap::new(),
                tied: BTreeMap::new(),
                edges: exit.edges.clone(),
            };
            for q in tied.keys() {
                mark_gone(&mut probe, q.clone(), Gone::To(Span::DUMMY, What::Mutex));
            }
            for q in probe.gone.keys() {
                if let Some(r) = root_of(q.0) {
                    #[allow(clippy::cast_possible_truncation)]
                    s.ties.insert((i as u32, (r, q.1.clone())));
                }
            }
        }
        s
    }
}

fn addr(e: &HirExpr) -> usize {
    std::ptr::from_ref(e) as usize
}

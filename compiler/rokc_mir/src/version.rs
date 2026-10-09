//! Bounds versioning of counted loops. An innermost rotated loop
//! `for j in a..n` whose body indexes lists with `j`, or with a value
//! the loop does not change, and changes no list's length gets a copy
//! with unchecked accesses, entered when a test in front of the loop
//! finds `n <= xs.len()` / `i < xs.len()` for every such list; the
//! original loop runs otherwise, so an access out of bounds panics as
//! before. Without it LLVM keeps one bounds check per list and
//! iteration: each exits to its own panic, so no load after the first
//! check is known to run, and none leaves the loop.
//!
//! An index may also be the counter plus a constant (`xs[j + 1]`), and
//! a two-pointer loop (`while lo < hi`, `lo` stepped up and `hi` down by
//! one) indexes within `lo0..=hi0`: its test is `hi0 < xs.len()`.
//!
//! The accessors are the core library's `List` `Index` / `IndexSet`
//! impls (`if idx >= self.len() { panic }`, then the element access);
//! an unchecked copy is the access alone. The loop may call only them
//! and functions that store nowhere and call nothing indirectly:
//! nothing else could shrink a list between the test and an access.

use std::collections::{HashMap, HashSet};

use rokc_ir_common::{BlockId, ConstVal, FunctionId, Linkage, LocalId, MONO_MARK, PrimOp, PrimTy};

use crate::rotate::{back_edges, loop_body, retarget, succs};
use crate::{BasicBlock, LocalDecl, MirFunction, MirTy, Operand, RValue, Statement, Terminator};

/// A loop body copied for its unchecked version has at most this many
/// statements.
const MAX_BODY: usize = 256;

/// The largest `k` of an index `ctr + k` made unchecked (in total).
const MAX_OFFSET: i128 = 64;

/// A checked accessor (`xs[i]`, `xs[i] = v`): its length function and
/// the block after the check.
#[derive(Clone, Copy)]
struct Accessor {
    len: FunctionId,
    tail: usize,
}

const fn usize_ty() -> MirTy {
    MirTy::Prim(PrimTy::Usize)
}

fn stmts(block: &BasicBlock) -> impl Iterator<Item = &Statement> {
    block
        .stmts
        .iter()
        .filter(|s| !matches!(s, Statement::Loc(..) | Statement::StorageDead(_)))
}

/// Loads only: `xs.0`, `buf[k]`, fields, copies.
const fn load(rv: &RValue) -> bool {
    matches!(
        rv,
        RValue::Use(_) | RValue::FieldRead { .. } | RValue::BufLoad { .. } | RValue::Cast { .. }
    )
}

/// An rvalue that writes no memory but its own result and runs no
/// other code (a static's load may run its lazy initializer).
const fn pure(rv: &RValue) -> bool {
    matches!(
        rv,
        RValue::Use(_)
            | RValue::BinOp { .. }
            | RValue::UnaryOp { .. }
            | RValue::StructInit { .. }
            | RValue::FieldRead { .. }
            | RValue::Cast { .. }
            | RValue::Bitcast { .. }
            | RValue::WithField { .. }
            | RValue::ArrayInit { .. }
            | RValue::ArrayIndex { .. }
            | RValue::FnAddr { .. }
            | RValue::HeapBox { .. }
            | RValue::BufAlloc { .. }
            | RValue::RawLoad { .. }
            | RValue::SizeOf { .. }
            | RValue::BufLoad { .. }
            | RValue::HeapLoad { .. }
            | RValue::HeapAlloc { .. }
            | RValue::HeapField { .. }
    )
}

/// The core library's `List` module: its accessors and `len` are the
/// only ones whose checks the pass may drop.
const LIST: &str = "rok::core::collections::list::";

fn is_len(func: &MirFunction) -> bool {
    func.path() == format!("{LIST}List__len")
        && func.params.len() == 1
        && func.ret_ty == usize_ty()
        && matches!(func.blocks.as_slice(), [only]
            if matches!(only.terminator, Terminator::Return(Some(_)))
                && stmts(only).all(|s| matches!(s, Statement::Assign { rvalue, .. } if load(rvalue))))
}

/// Block `block` of `func` reads only the parameters and its own
/// definitions.
fn reads_own(func: &MirFunction, block: &BasicBlock) -> bool {
    let mut known: HashSet<LocalId> = func.params.iter().copied().collect();
    for s in &block.stmts {
        let (uses, def) = crate::liveness::stmt_uses(s);
        if !uses.iter().all(|u| known.contains(u)) {
            return false;
        }
        known.extend(def);
    }
    crate::liveness::term_uses(&block.terminator)
        .iter()
        .all(|u| known.contains(u))
}

fn accessor(func: &MirFunction, fns: &HashMap<FunctionId, &MirFunction>) -> Option<Accessor> {
    let path = func.path().strip_prefix(LIST)?;
    if !path.starts_with("__impl") || !(path.ends_with("_index") || path.ends_with("_index_set")) {
        return None;
    }
    let ([xs, idx, ..], Some(entry)) = (func.params.as_slice(), func.blocks.first()) else {
        return None;
    };
    let [
        Statement::Assign {
            target: len_l,
            rvalue: RValue::Call { callee, args, .. },
        },
        Statement::Assign {
            target: test_l,
            rvalue:
                RValue::BinOp {
                    op: PrimOp::Ge,
                    op_ty,
                    lhs: Operand::Copy(lhs),
                    rhs: Operand::Copy(rhs),
                },
        },
    ] = stmts(entry).collect::<Vec<_>>().as_slice()
    else {
        return None;
    };
    let Terminator::If {
        cond: Operand::Copy(cond),
        then_bb,
        then_args,
        else_bb,
        else_args,
    } = &entry.terminator
    else {
        return None;
    };
    let index_of = |id: BlockId| func.blocks.iter().position(|b| b.id == id);
    let (fail, tail) = (index_of(*then_bb)?, index_of(*else_bb)?);
    let rest = &func.blocks[tail];
    let ok = cond == test_l
        && rhs == len_l
        && lhs == idx
        && *op_ty == usize_ty()
        && matches!(args.as_slice(), [Operand::Copy(a)] if a == xs)
        && fns.get(callee).is_some_and(|l| is_len(l))
        && then_args.is_empty()
        && else_args.is_empty()
        && matches!(func.blocks[fail].terminator, Terminator::Unreachable)
        && rest.params.is_empty()
        && matches!(rest.terminator, Terminator::Return(_))
        && reads_own(func, rest)
        && stmts(rest).all(|s| match s {
            Statement::Assign { rvalue, .. } => load(rvalue),
            Statement::BufStore { .. } => true,
            _ => false,
        });
    ok.then_some(Accessor { len: *callee, tail })
}

/// Functions that store nowhere, allocate or not: calls a loop may make
/// without changing any list.
fn storeless(fns: &[MirFunction]) -> HashSet<FunctionId> {
    let mut out: HashSet<FunctionId> = HashSet::new();
    loop {
        let before = out.len();
        for func in fns {
            if out.contains(&func.id)
                || func.blocks.is_empty()
                || func.facts.linkage == Linkage::Extern
            {
                continue;
            }
            let ok = func.blocks.iter().all(|b| {
                !matches!(b.terminator, Terminator::Suspend { .. })
                    && b.stmts.iter().all(|s| match s {
                        Statement::Assign {
                            rvalue: RValue::Call { callee, .. },
                            ..
                        } => out.contains(callee),
                        Statement::Assign { rvalue, .. } => pure(rvalue),
                        Statement::Loc(..) | Statement::StorageDead(_) => true,
                        _ => false,
                    })
            });
            if ok {
                out.insert(func.id);
            }
        }
        if out.len() == before {
            return out;
        }
    }
}

pub fn same(a: &Operand, b: &Operand) -> bool {
    match (a, b) {
        (Operand::Copy(x), Operand::Copy(y)) => x == y,
        (Operand::Const(x), Operand::Const(y)) => x == y,
        _ => false,
    }
}

/// A loop's exit test `ctr < bound` of integer type `ty`. `hi`: a
/// two-pointer loop (`while lo < hi { ..; lo += 1; hi -= 1 }`), whose
/// bound is the local `hi`, stepped down as `ctr` steps up.
#[derive(Clone)]
pub struct Test {
    pub ctr: LocalId,
    pub bound: Operand,
    pub ty: PrimTy,
    pub hi: Option<LocalId>,
}

/// The test block `block` ends in, taken to `header` when it holds.
pub fn test_into(block: &BasicBlock, header: u32) -> Option<Test> {
    let Terminator::If {
        cond: Operand::Copy(cond),
        then_bb,
        then_args,
        ..
    } = &block.terminator
    else {
        return None;
    };
    if then_bb.0 != header || !then_args.is_empty() {
        return None;
    }
    let at = block
        .stmts
        .iter()
        .rposition(|s| matches!(s, Statement::Assign { target, .. } if target == cond))?;
    let Statement::Assign {
        rvalue:
            RValue::BinOp {
                op: PrimOp::Lt,
                op_ty: MirTy::Prim(ty),
                lhs: Operand::Copy(ctr),
                rhs: bound,
            },
        ..
    } = &block.stmts[at]
    else {
        return None;
    };
    let set_later = |l: &LocalId| {
        block.stmts[at + 1..]
            .iter()
            .any(|s| crate::liveness::stmt_uses(s).1 == Some(*l))
    };
    let moves = set_later(ctr) || matches!(bound, Operand::Copy(l) if set_later(l));
    ((ty.is_signed_int() || ty.is_unsigned_int()) && !moves).then(|| Test {
        ctr: *ctr,
        bound: bound.clone(),
        ty: *ty,
        hi: None,
    })
}

/// The test `lo < hi` header `hb` of loop `body` ends in, entering the
/// loop when it holds: a two-pointer loop's, not rotated.
fn two_test(hb: &BasicBlock, body: &HashSet<u32>) -> Option<Test> {
    let Terminator::If {
        then_bb, else_bb, ..
    } = &hb.terminator
    else {
        return None;
    };
    if !body.contains(&then_bb.0) || body.contains(&else_bb.0) {
        return None;
    }
    let t = test_into(hb, then_bb.0)?;
    match t.bound {
        Operand::Copy(hi) if hi != t.ctr => Some(Test { hi: Some(hi), ..t }),
        _ => None,
    }
}

/// A list access in the loop to make unchecked: block, statement.
type Site = (u32, usize);

/// What the test in front of the loop checks: `bound + k <= len(xs)` for
/// a list indexed by the counter plus `k`, `i < len(xs)` for one indexed
/// by `i` (`i < bound` when `xs` is indexed by the counter too: one test
/// for every such list), and `0 <= ctr` for a signed counter. A
/// two-pointer loop indexes within `lo..=hi`, so in front `hi < len(xs)`.
enum Need {
    Bound(LocalId, FunctionId, i128),
    Index(LocalId, FunctionId, Operand),
    BelowBound(Operand),
    NonNeg,
}

impl Need {
    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bound(xs, len, k), Self::Bound(ys, len2, l)) => {
                xs == ys && len == len2 && k == l
            }
            (Self::Index(xs, len, i), Self::Index(ys, len2, j)) => {
                xs == ys && len == len2 && same(i, j)
            }
            (Self::BelowBound(i), Self::BelowBound(j)) => same(i, j),
            (Self::NonNeg, Self::NonNeg) => true,
            _ => false,
        }
    }
}

struct Plan {
    header: u32,
    body: HashSet<u32>,
    test: Test,
    /// The counter type's width.
    bits: u32,
    needs: Vec<Need>,
    sites: HashMap<Site, FunctionId>,
}

/// What a loop's accesses are checked against.
struct Scope<'a> {
    accessors: &'a HashMap<FunctionId, Accessor>,
    storeless: &'a HashSet<FunctionId>,
    /// Locals the loop sets, or that a pointer may.
    set: HashSet<LocalId>,
    test: Test,
}

impl Scope<'_> {
    fn fixed(&self, op: &Operand) -> bool {
        match op {
            Operand::Const(_) => true,
            Operand::Copy(l) => !self.set.contains(l),
        }
    }

    /// The accesses of body block `block` to make unchecked, with what
    /// the test must check for them; `None` if the block may change a
    /// list.
    fn scan(&self, block: &BasicBlock) -> Option<Vec<(usize, FunctionId, Need)>> {
        let Test { ctr, ty, hi, .. } = self.test;
        // Locals holding a counter's value plus a constant here (`hi`'s
        // when the flag is set), and those as a `usize`.
        let mut at: HashMap<LocalId, (bool, i128)> = HashMap::from([(ctr, (false, 0))]);
        at.extend(hi.map(|h| (h, (true, 0))));
        let mut as_index: HashMap<LocalId, (bool, i128)> = HashMap::new();
        if ty == PrimTy::Usize {
            as_index.clone_from(&at);
        }
        let mut out = Vec::new();
        for (k, s) in block.stmts.iter().enumerate() {
            let Statement::Assign { target, rvalue } = s else {
                if matches!(
                    s,
                    Statement::Loc(..) | Statement::StorageDead(_) | Statement::ArrayWrite { .. }
                ) {
                    continue;
                }
                return None;
            };
            match rvalue {
                RValue::Call { callee, args, .. } => {
                    if let Some(a) = self.accessors.get(callee) {
                        let need = match args.as_slice() {
                            [Operand::Copy(xs), idx, ..] if !self.set.contains(xs) => match idx {
                                Operand::Copy(i) if as_index.contains_key(i) => {
                                    match (hi, as_index[i]) {
                                        (None, (_, off)) => Some(Need::Bound(*xs, a.len, off)),
                                        (Some(h), (_, 0)) => {
                                            Some(Need::Index(*xs, a.len, Operand::Copy(h)))
                                        }
                                        _ => None,
                                    }
                                }
                                i if self.fixed(i) => Some(Need::Index(*xs, a.len, i.clone())),
                                _ => None,
                            },
                            _ => None,
                        };
                        out.extend(need.map(|n| (k, *callee, n)));
                    } else if !self.storeless.contains(callee) {
                        return None;
                    }
                }
                rv if !pure(rv) => return None,
                _ => {}
            }
            // (counter value, as a `usize`) of the result.
            let from = match rvalue {
                RValue::Use(Operand::Copy(l)) => (at.get(l).copied(), as_index.get(l).copied()),
                RValue::Cast {
                    source: Operand::Copy(l),
                    from_ty: MirTy::Prim(from),
                    to_ty,
                } if *from == ty && *to_ty == usize_ty() => (None, at.get(l).copied()),
                RValue::BinOp {
                    op: PrimOp::Add | PrimOp::WrappingAdd,
                    op_ty: MirTy::Prim(t),
                    lhs: Operand::Copy(l),
                    rhs: Operand::Const(ConstVal::Int { value, .. }),
                } if *t == ty && (1..=MAX_OFFSET).contains(value) => {
                    // The total offset stays at most `MAX_OFFSET`, below every
                    // signed type's top, so the wrap test's constant fits.
                    let v = at
                        .get(l)
                        .map(|&(h, off)| (h, off + value))
                        .filter(|&(_, off)| off <= MAX_OFFSET);
                    (v, v.filter(|_| ty == PrimTy::Usize))
                }
                _ => (None, None),
            };
            at.remove(target);
            as_index.remove(target);
            if *target == ctr || Some(*target) == hi {
                let moved = Some(*target) == hi;
                at.retain(|_, (h, _)| *h != moved);
                as_index.retain(|_, (h, _)| *h != moved);
            } else {
                at.extend(from.0.map(|v| (*target, v)));
                as_index.extend(from.1.map(|v| (*target, v)));
            }
        }
        Some(out)
    }
}

/// Every way into `header` tests `ctr < bound`, the same ones.
fn entry_test(func: &MirFunction, header: u32) -> Option<Test> {
    let mut test: Option<Test> = None;
    for b in func.blocks.iter().filter(|b| succs(b).contains(&header)) {
        let t = test_into(b, header)?;
        if let Some(seen) = &test {
            if seen.ctr != t.ctr || !same(&seen.bound, &t.bound) || seen.ty != t.ty {
                return None;
            }
        }
        test = Some(t);
    }
    test
}

fn plan(
    func: &MirFunction,
    header: u32,
    latches: &[u32],
    scope: (&HashMap<FunctionId, Accessor>, &HashSet<FunctionId>),
    pointer_width: u32,
) -> Option<Plan> {
    let blocks: HashMap<u32, &BasicBlock> = func.blocks.iter().map(|b| (b.id.0, b)).collect();
    let body = loop_body(func, header, latches);
    let size: usize = body.iter().map(|b| blocks[b].stmts.len()).sum();
    if !blocks.get(&header)?.params.is_empty() || size > MAX_BODY {
        return None;
    }
    // A latch's other way leaves the loop: past the latches the counter
    // is the one `header` was entered with.
    if latches.iter().any(|l| {
        succs(blocks[l])
            .iter()
            .any(|s| *s != header && body.contains(s))
    }) {
        return None;
    }
    let test = entry_test(func, header).or_else(|| two_test(blocks[&header], &body))?;
    let (ctr, ty) = (test.ctr, test.ty);
    // Another counter type indexes through a cast to `usize`, which keeps
    // its value: no wider than `usize`, and a signed one counts up by one
    // from at least 0 (tested in front).
    let signed = ty.is_signed_int();
    let mut set = crate::addressed(func);
    if set.contains(&ctr)
        || test.hi.is_some_and(|h| set.contains(&h))
        || ty.bit_width(pointer_width) > pointer_width
    {
        return None;
    }
    let step = |s: &Statement, l: LocalId, op: PrimOp| {
        matches!(s, Statement::Assign {
            target,
            rvalue: RValue::BinOp {
                op: o,
                op_ty: MirTy::Prim(t),
                lhs: Operand::Copy(x),
                rhs: Operand::Const(ConstVal::Int { value: 1, .. }),
            },
        } if *target == l && *x == l && *o == op && *t == ty)
    };
    for id in &body {
        let b = blocks[id];
        if matches!(b.terminator, Terminator::Suspend { .. })
            || b.params.iter().any(|p| *p == ctr || Some(*p) == test.hi)
        {
            return None;
        }
        set.extend(b.params.iter().copied());
        if let Some(hi) = test.hi {
            // Two pointers: each stepped by one at most once an iteration,
            // in a block whose only way on is back to `header`, so at
            // every access `lo0 <= lo < hi <= hi0`.
            let latch = matches!(&b.terminator,
                Terminator::Goto { target, args } if target.0 == header && args.is_empty());
            let defs = |l: LocalId| {
                b.stmts
                    .iter()
                    .filter(|s| crate::liveness::stmt_uses(s).1 == Some(l))
                    .collect::<Vec<_>>()
            };
            let (lo_defs, hi_defs) = (defs(ctr), defs(hi));
            let ok = |ds: &[&Statement], l, op| {
                ds.is_empty() || (latch && ds.len() == 1 && step(ds[0], l, op))
            };
            if !ok(&lo_defs, ctr, PrimOp::Add) || !ok(&hi_defs, hi, PrimOp::Sub) {
                return None;
            }
        }
        for s in &b.stmts {
            if let Some(d) = crate::liveness::stmt_uses(s).1 {
                // A counted loop's counter is set only in the latches,
                // whose way on is the test into `header`.
                if test.hi.is_none()
                    && d == ctr
                    && (!latches.contains(id) || (signed && !step(s, ctr, PrimOp::Add)))
                {
                    return None;
                }
                set.insert(d);
            }
        }
    }
    let scope = Scope {
        accessors: scope.0,
        storeless: scope.1,
        set,
        test,
    };
    if scope.test.hi.is_none() && !scope.fixed(&scope.test.bound) {
        return None;
    }
    let mut needs: Vec<Need> = Vec::new();
    let mut sites: HashMap<Site, FunctionId> = HashMap::new();
    for id in &body {
        let found = scope.scan(blocks[id])?;
        // A two-pointer header runs its statements before its test.
        if scope.test.hi.is_some() && *id == header {
            continue;
        }
        for (k, callee, need) in found {
            if !needs.iter().any(|n| n.same(&need)) {
                needs.push(need);
            }
            sites.insert((*id, k), callee);
        }
    }
    // `i < bound <= len(xs)`: the bound test of `xs` covers `i`.
    let bounded: HashSet<(LocalId, FunctionId)> = needs
        .iter()
        .filter_map(|n| match n {
            Need::Bound(xs, len, _) => Some((*xs, *len)),
            _ => None,
        })
        .collect();
    let mut merged: Vec<Need> = Vec::new();
    for need in needs {
        let need = match need {
            Need::Index(xs, len, i) if bounded.contains(&(xs, len)) => Need::BelowBound(i),
            n => n,
        };
        if !merged.iter().any(|n| n.same(&need)) {
            merged.push(need);
        }
    }
    let mut needs = merged;
    let by_ctr = |n: &Need| match n {
        Need::Bound(..) => true,
        Need::Index(_, _, i) => scope.test.hi.is_some() && same(i, &scope.test.bound),
        _ => false,
    };
    if signed && needs.iter().any(by_ctr) {
        needs.push(Need::NonNeg);
    }
    (!sites.is_empty()).then_some(Plan {
        header,
        body,
        bits: ty.bit_width(pointer_width),
        test: scope.test,
        needs,
        sites,
    })
}

fn fresh(func: &mut MirFunction, ty: MirTy) -> LocalId {
    let id = LocalId(u32::try_from(func.locals.len()).expect("local count"));
    func.locals.push(LocalDecl { id, name: None, ty });
    id
}

const fn int(value: i128, ty: PrimTy) -> Operand {
    Operand::Const(ConstVal::Int { value, ty })
}

const fn assign(target: LocalId, rvalue: RValue) -> Statement {
    Statement::Assign { target, rvalue }
}

/// The test of plan `p` in `func`: its statements, then its conditions.
fn conditions(func: &mut MirFunction, p: &Plan) -> (Vec<Statement>, Vec<LocalId>) {
    let Test {
        ctr, ref bound, ty, ..
    } = p.test;
    let mut stmts = Vec::new();
    let mut conds = Vec::new();
    let mut cmp = |func: &mut MirFunction, stmts: &mut Vec<Statement>, op, op_ty, lhs, rhs| {
        let c = fresh(func, MirTy::Prim(PrimTy::Bool));
        stmts.push(assign(
            c,
            RValue::BinOp {
                op,
                op_ty,
                lhs,
                rhs,
            },
        ));
        conds.push(c);
    };
    // The bound as a `usize` (a negative one fails the test).
    let ubound = if ty == PrimTy::Usize {
        bound.clone()
    } else {
        let l = fresh(func, usize_ty());
        stmts.push(assign(
            l,
            RValue::Cast {
                source: bound.clone(),
                from_ty: MirTy::Prim(ty),
                to_ty: usize_ty(),
            },
        ));
        Operand::Copy(l)
    };
    let mut lens: HashMap<(LocalId, FunctionId), LocalId> = HashMap::new();
    for need in &p.needs {
        let (xs, len) = match need {
            Need::NonNeg => {
                let zero = Operand::Const(ConstVal::Int { value: 0, ty });
                cmp(
                    func,
                    &mut stmts,
                    PrimOp::Le,
                    MirTy::Prim(ty),
                    zero,
                    Operand::Copy(ctr),
                );
                continue;
            }
            Need::BelowBound(i) => {
                cmp(
                    func,
                    &mut stmts,
                    PrimOp::Lt,
                    usize_ty(),
                    i.clone(),
                    ubound.clone(),
                );
                continue;
            }
            Need::Bound(xs, len, _) | Need::Index(xs, len, _) => (*xs, *len),
        };
        let l = Operand::Copy(*lens.entry((xs, len)).or_insert_with(|| {
            let l = fresh(func, usize_ty());
            stmts.push(assign(
                l,
                RValue::Call {
                    callee: len,
                    args: vec![Operand::Copy(xs)],
                    ret_ty: usize_ty(),
                },
            ));
            l
        }));
        match need {
            // A two-pointer loop's `hi`, as a `usize`.
            Need::Index(_, _, i) if p.test.hi.is_some() && same(i, bound) => {
                cmp(func, &mut stmts, PrimOp::Lt, usize_ty(), ubound.clone(), l);
            }
            Need::Index(_, _, i) => cmp(func, &mut stmts, PrimOp::Lt, usize_ty(), i.clone(), l),
            &Need::Bound(_, _, 0) => {
                cmp(func, &mut stmts, PrimOp::Le, usize_ty(), ubound.clone(), l);
            }
            &Need::Bound(_, _, k) => {
                // A signed `ctr + k` wraps negative past the type's top at
                // -O2, and as a `usize` it is huge: `bound <= MAX - k + 1`.
                if ty.is_signed_int() {
                    let top = (1i128 << (p.bits - 1)) - 1;
                    cmp(
                        func,
                        &mut stmts,
                        PrimOp::Le,
                        MirTy::Prim(ty),
                        bound.clone(),
                        int(top - k + 1, ty),
                    );
                }
                // `k <= len`, then `bound <= len - k`.
                let k = Operand::Const(ConstVal::Int {
                    value: k,
                    ty: PrimTy::Usize,
                });
                cmp(
                    func,
                    &mut stmts,
                    PrimOp::Le,
                    usize_ty(),
                    k.clone(),
                    l.clone(),
                );
                let room = fresh(func, usize_ty());
                stmts.push(assign(
                    room,
                    RValue::BinOp {
                        op: PrimOp::WrappingSub,
                        op_ty: usize_ty(),
                        lhs: l,
                        rhs: k,
                    },
                ));
                cmp(
                    func,
                    &mut stmts,
                    PrimOp::Le,
                    usize_ty(),
                    ubound.clone(),
                    Operand::Copy(room),
                );
            }
            _ => unreachable!(),
        }
    }
    (stmts, conds)
}

/// Insert the test and the unchecked copy of the loop `p` into `func`.
fn apply(func: &mut MirFunction, p: &Plan, unchecked: &mut dyn FnMut(FunctionId) -> FunctionId) {
    let mut next = func.blocks.iter().map(|b| b.id.0 + 1).max().unwrap_or(0);
    let mut ids: Vec<u32> = p.body.iter().copied().collect();
    ids.sort_unstable();
    let map: HashMap<u32, u32> = ids
        .into_iter()
        .map(|b| {
            next += 1;
            (b, next - 1)
        })
        .collect();
    let (mut stmts, conds) = conditions(func, p);
    let fast = map[&p.header];
    // One branch on all the conditions (each computed anyway): the ones
    // an enclosing loop does not change then leave it.
    let all = conds
        .into_iter()
        .reduce(|a, b| {
            let c = fresh(func, MirTy::Prim(PrimTy::Bool));
            stmts.push(assign(
                c,
                RValue::BinOp {
                    op: PrimOp::BitAnd,
                    op_ty: MirTy::Prim(PrimTy::Bool),
                    lhs: Operand::Copy(a),
                    rhs: Operand::Copy(b),
                },
            ));
            c
        })
        .expect("a plan tests something");
    let tests = [BasicBlock {
        id: BlockId(next),
        params: vec![],
        stmts,
        terminator: Terminator::If {
            cond: Operand::Copy(all),
            then_bb: BlockId(fast),
            then_args: vec![],
            else_bb: BlockId(p.header),
            else_args: vec![],
        },
    }];
    for b in &mut func.blocks {
        if !p.body.contains(&b.id.0) {
            retarget(&mut b.terminator, p.header, next);
        }
    }
    let mut copies: Vec<BasicBlock> = Vec::new();
    for b in func.blocks.iter().filter(|b| map.contains_key(&b.id.0)) {
        let mut c = b.clone();
        c.id = BlockId(map[&b.id.0]);
        for (&from, &to) in &map {
            retarget(&mut c.terminator, from, to);
        }
        for (k, s) in c.stmts.iter_mut().enumerate() {
            if let (
                Some(&callee),
                Statement::Assign {
                    rvalue: RValue::Call { callee: to, .. },
                    ..
                },
            ) = (p.sites.get(&(b.id.0, k)), s)
            {
                *to = unchecked(callee);
            }
        }
        copies.push(c);
    }
    func.blocks.extend(copies);
    func.blocks.extend(tests);
}

/// Accessor `func` without its check: the tail block alone.
fn strip(func: &MirFunction, a: Accessor, id: FunctionId) -> MirFunction {
    let mut out = func.clone();
    out.id = id;
    // `#` is in no rok identifier, so no user item has this name.
    out.name = match &func.facts.mono_args {
        Some(args) => format!("{}#unchecked{MONO_MARK}{args}", func.path()),
        None => format!("{}#unchecked", func.name),
    };
    out.def_id = None;
    out.facts.linkage = Linkage::Defined;
    out.facts.export_name = None;
    let mut tail = func.blocks[a.tail].clone();
    tail.id = BlockId(0);
    out.blocks = vec![tail];
    out
}

pub fn version(fns: &mut Vec<MirFunction>, pointer_width: u32) {
    let accessors: HashMap<FunctionId, Accessor> = {
        let by: HashMap<FunctionId, &MirFunction> = fns.iter().map(|f| (f.id, f)).collect();
        fns.iter()
            .filter(|f| f.facts.linkage != Linkage::Extern)
            .filter_map(|f| accessor(f, &by).map(|a| (f.id, a)))
            .collect()
    };
    if accessors.is_empty() {
        return;
    }
    let storeless = storeless(fns);
    let mut next = fns.iter().map(|f| f.id.0 + 1).max().unwrap_or(0);
    let mut made: HashMap<FunctionId, FunctionId> = HashMap::new();
    for func in fns.iter_mut() {
        if func.facts.linkage != Linkage::Defined || func.blocks.is_empty() {
            continue;
        }
        let mut latches: HashMap<u32, Vec<u32>> = HashMap::new();
        for (latch, hs) in back_edges(func) {
            for header in hs {
                latches.entry(header).or_default().push(latch);
            }
        }
        let mut headers: Vec<(u32, Vec<u32>)> = latches.into_iter().collect();
        headers.sort_unstable_by_key(|(header, _)| *header);
        let plans: Vec<Plan> = headers
            .iter()
            .filter_map(|(header, ls)| {
                let p = plan(func, *header, ls, (&accessors, &storeless), pointer_width)?;
                // Innermost loops only: one copy each.
                let inner = p
                    .body
                    .iter()
                    .any(|b| b != header && headers.iter().any(|(h, _)| h == b));
                (!inner).then_some(p)
            })
            .collect();
        for p in &plans {
            apply(func, p, &mut |callee| {
                *made.entry(callee).or_insert_with(|| {
                    next += 1;
                    FunctionId(next - 1)
                })
            });
        }
    }
    let mut copies: Vec<MirFunction> = made
        .iter()
        .map(|(orig, id)| {
            let func = fns.iter().find(|f| f.id == *orig).expect("accessor");
            strip(func, accessors[orig], *id)
        })
        .collect();
    copies.sort_unstable_by_key(|f| f.id);
    fns.extend(copies);
}

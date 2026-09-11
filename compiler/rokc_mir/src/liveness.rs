//! Where locals die: backward liveness over the MIR CFG, so codegen can
//! clear a GC root slot right after its last use (704 §7.4.1: a slot
//! whose variable is dead may be nulled) instead of at function end.
//!
//! A block param is defined on block entry. An array write is a partial
//! definition (the old elements stay), so it only uses the array.

use std::collections::HashMap;

use rokc_ir_common::LocalId;

use crate::{MirFunction, Operand, Statement, Terminator};

/// Deaths of the tracked locals, indexed like `MirFunction::blocks`.
#[derive(Debug, Default)]
pub struct Deaths {
    /// Locals some predecessor still held at its terminator (live out or
    /// a terminator operand) that are dead on entry to this block.
    pub on_entry: Vec<Vec<LocalId>>,
    /// Per statement: the locals it mentions that are dead after it.
    pub after_stmt: Vec<Vec<Vec<LocalId>>>,
}

/// Fixed-size bit set over the tracked locals' dense indices.
#[derive(Clone, PartialEq)]
struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Self {
        Self(vec![0; n.div_ceil(64)])
    }
    fn has(&self, i: usize) -> bool {
        (self.0[i / 64] >> (i % 64)) & 1 == 1
    }
    fn set(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }
    fn unset(&mut self, i: usize) {
        self.0[i / 64] &= !(1 << (i % 64));
    }
    fn union(&mut self, o: &Self) {
        for (a, b) in self.0.iter_mut().zip(&o.0) {
            *a |= b;
        }
    }
}

/// Locals a statement reads, and the one it (fully) defines.
fn stmt_uses(s: &Statement) -> (Vec<LocalId>, Option<LocalId>) {
    let mut ops = Vec::new();
    let mut def = None;
    match s {
        Statement::Assign { target, rvalue } => {
            crate::coro::rvalue_operands(rvalue, &mut ops);
            def = Some(*target);
        }
        Statement::ArrayWrite {
            array,
            index,
            value,
            ..
        } => ops.extend([Operand::Copy(*array), index.clone(), value.clone()]),
        // Region parameters are MLIR values, never GC references.
        Statement::StorageDead(_)
        | Statement::Loc(..)
        | Statement::MlirRegion { .. }
        | Statement::MlirRegionEnd => {}
        Statement::BufStore {
            buf, index, value, ..
        } => ops.extend([buf.clone(), index.clone(), value.clone()]),
        Statement::RawStore { addr, value, .. } => ops.extend([addr.clone(), value.clone()]),
        Statement::HeapStore { ptr, value, .. } => ops.extend([ptr.clone(), value.clone()]),
        Statement::StaticStore { value, .. } => ops.push(value.clone()),
    }
    (copies(&ops), def)
}

fn copies(ops: &[Operand]) -> Vec<LocalId> {
    ops.iter()
        .filter_map(|o| match o {
            Operand::Copy(l) => Some(*l),
            Operand::Const(_) => None,
        })
        .collect()
}

fn term_uses(t: &Terminator) -> Vec<LocalId> {
    match t {
        Terminator::Goto { args, .. } => copies(args),
        Terminator::If {
            cond,
            then_args,
            else_args,
            ..
        } => {
            let mut ops = vec![cond.clone()];
            ops.extend(then_args.iter().cloned());
            ops.extend(else_args.iter().cloned());
            copies(&ops)
        }
        Terminator::Return(v) | Terminator::Suspend { value: v, .. } => copies(v.as_slice()),
        Terminator::Unreachable => Vec::new(),
    }
}

fn successors(t: &Terminator) -> Vec<rokc_ir_common::BlockId> {
    match t {
        Terminator::Goto { target, .. } => vec![*target],
        Terminator::If {
            then_bb, else_bb, ..
        } => vec![*then_bb, *else_bb],
        Terminator::Suspend { resume, .. } => vec![*resume],
        Terminator::Return(_) | Terminator::Unreachable => Vec::new(),
    }
}

/// The tracked locals' dense indices: liveness of one local does not
/// depend on the others, so the rest are ignored.
struct Dense {
    ids: Vec<LocalId>,
    index: HashMap<LocalId, usize>,
}

impl Dense {
    fn get(&self, l: LocalId) -> Option<usize> {
        self.index.get(&l).copied()
    }

    fn bits<'a>(&self, ls: impl IntoIterator<Item = &'a LocalId>) -> Bits {
        let mut bits = Bits::new(self.ids.len());
        for &l in ls {
            if let Some(i) = self.get(l) {
                bits.set(i);
            }
        }
        bits
    }
}

/// `(gen, kill)` of a block: tracked locals used before any definition
/// in it, and those it defines (block params included).
fn gen_kill(
    dense: &Dense,
    b: &crate::BasicBlock,
    stmts: &[(Vec<LocalId>, Option<LocalId>)],
) -> (Bits, Bits) {
    let mut kill = dense.bits(&b.params);
    let mut gen_ = Bits::new(dense.ids.len());
    let mut uses_of = |ls: &[LocalId], kill: &Bits| {
        for &l in ls {
            if let Some(i) = dense.get(l).filter(|&i| !kill.has(i)) {
                gen_.set(i);
            }
        }
    };
    for (uses, def) in stmts {
        uses_of(uses, &kill);
        if let Some(i) = def.and_then(|d| dense.get(d)) {
            kill.set(i);
        }
    }
    uses_of(&term_uses(&b.terminator), &kill);
    (gen_, kill)
}

/// Live-in sets: the backward dataflow fixpoint.
fn solve(succs: &[Vec<usize>], gen_kill: &[(Bits, Bits)], n: usize) -> Vec<Bits> {
    let mut live_in = vec![Bits::new(n); succs.len()];
    let mut changed = true;
    while changed {
        changed = false;
        for i in (0..succs.len()).rev() {
            let mut inn = Bits::new(n);
            for &s in &succs[i] {
                inn.union(&live_in[s]);
            }
            let (gen_, kill) = &gen_kill[i];
            for (w, (g, k)) in inn.0.iter_mut().zip(gen_.0.iter().zip(&kill.0)) {
                *w = (*w & !k) | g;
            }
            if inn != live_in[i] {
                live_in[i] = inn;
                changed = true;
            }
        }
    }
    live_in
}

/// Where each local `tracked` accepts dies in `f`.
pub fn deaths(f: &MirFunction, tracked: impl Fn(LocalId) -> bool) -> Deaths {
    let ids: Vec<LocalId> = f
        .locals
        .iter()
        .map(|l| l.id)
        .filter(|&l| tracked(l))
        .collect();
    let dense = Dense {
        index: ids.iter().enumerate().map(|(i, &l)| (l, i)).collect(),
        ids,
    };
    let mut out = Deaths {
        on_entry: vec![Vec::new(); f.blocks.len()],
        after_stmt: f
            .blocks
            .iter()
            .map(|b| vec![Vec::new(); b.stmts.len()])
            .collect(),
    };
    if dense.ids.is_empty() {
        return out;
    }
    let pos: HashMap<_, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect();
    let succs: Vec<Vec<usize>> = f
        .blocks
        .iter()
        .map(|b| {
            successors(&b.terminator)
                .iter()
                .filter_map(|s| pos.get(s).copied())
                .collect()
        })
        .collect();
    let stmts: Vec<Vec<(Vec<LocalId>, Option<LocalId>)>> = f
        .blocks
        .iter()
        .map(|b| b.stmts.iter().map(stmt_uses).collect())
        .collect();
    let gk: Vec<(Bits, Bits)> = f
        .blocks
        .iter()
        .zip(&stmts)
        .map(|(b, st)| gen_kill(&dense, b, st))
        .collect();
    let live_in = solve(&succs, &gk, dense.ids.len());
    for (bi, b) in f.blocks.iter().enumerate() {
        // What this block still holds at its terminator.
        let mut live = dense.bits(&term_uses(&b.terminator));
        for &s in &succs[bi] {
            live.union(&live_in[s]);
        }
        for &s in &succs[bi] {
            for (i, &l) in dense.ids.iter().enumerate() {
                let dies = live.has(i) && !live_in[s].has(i);
                if dies && !f.blocks[s].params.contains(&l) && !out.on_entry[s].contains(&l) {
                    out.on_entry[s].push(l);
                }
            }
        }
        for (si, (uses, def)) in stmts[bi].iter().enumerate().rev() {
            let dead = &mut out.after_stmt[bi][si];
            for &l in uses.iter().chain(def) {
                if dense.get(l).is_some_and(|i| !live.has(i)) && !dead.contains(&l) {
                    dead.push(l);
                }
            }
            if let Some(i) = def.and_then(|d| dense.get(d)) {
                live.unset(i);
            }
            live.union(&dense.bits(uses));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BasicBlock, LocalDecl, MirTy, RValue};
    use rokc_diagnostic::Span;
    use rokc_ir_common::{BlockId, FunctionId};

    const fn local(i: u32) -> LocalDecl {
        LocalDecl {
            id: LocalId(i),
            name: None,
            ty: MirTy::GcRef,
        }
    }

    const fn assign(t: u32, from: u32) -> Statement {
        Statement::Assign {
            target: LocalId(t),
            rvalue: RValue::Use(Operand::Copy(LocalId(from))),
        }
    }

    /// bb0: x0 = x1; x2 = x0; if x3 -> bb1 / bb2
    /// bb1: x4 = x2; return
    /// bb2: return
    #[test]
    fn last_use_and_edge_deaths() {
        let f = MirFunction {
            id: FunctionId(0),
            def_id: None,
            name: "f".into(),
            facts: rokc_ir_common::FnFacts::default(),
            params: vec![LocalId(1), LocalId(3)],
            locals: (0..5).map(local).collect(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    params: vec![],
                    stmts: vec![assign(0, 1), assign(2, 0)],
                    terminator: Terminator::If {
                        cond: Operand::Copy(LocalId(3)),
                        then_bb: BlockId(1),
                        then_args: vec![],
                        else_bb: BlockId(2),
                        else_args: vec![],
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    params: vec![],
                    stmts: vec![assign(4, 2)],
                    terminator: Terminator::Return(None),
                },
                BasicBlock {
                    id: BlockId(2),
                    params: vec![],
                    stmts: vec![],
                    terminator: Terminator::Return(None),
                },
            ],
            param_tys: vec![],
            ret_ty: MirTy::Unit,
            span: Span::default(),
        };
        let d = deaths(&f, |_| true);
        // x1 dies at its only use, x0 at its last use.
        assert_eq!(d.after_stmt[0][0], vec![LocalId(1)]);
        assert_eq!(d.after_stmt[0][1], vec![LocalId(0)]);
        // x2 dies at its use in bb1 and on the edge into bb2; the
        // condition dies at the terminator (cleared on both entries).
        assert_eq!(d.after_stmt[1][0], vec![LocalId(2), LocalId(4)]);
        assert_eq!(d.on_entry[2], vec![LocalId(2), LocalId(3)]);
        assert_eq!(d.on_entry[1], vec![LocalId(3)]);
    }
}

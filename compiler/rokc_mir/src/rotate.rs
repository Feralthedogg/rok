//! Loops and loop rotation. A counted loop whose header tests its exit
//! (a range `for`, `while i < n` with `n` fixed) is rotated: its back
//! edges go to a copy of the header, so the body is the loop header and
//! runs at least once per entry, and the test is at the bottom. LLVM's own rotation leaves a
//! loop alone when its latch already exits (the back-edge poll's yield
//! path), and a load hoisted out of an unrotated body is speculated,
//! which drops its TBAA tag: rotated, a length load leaves the loop with
//! its tag, so it stays valid across the poll's yield (`REF_ONLY_CALLS`)
//! and leaves the enclosing loop too.

use std::collections::{BTreeMap, HashMap, HashSet};

use rokc_ir_common::{BlockId, LocalId, PrimOp};

use crate::{BasicBlock, MirFunction, Operand, RValue, Statement, Terminator};

/// A header copied for the back edges has at most this many statements.
const MAX_HEADER: usize = 16;

fn succs(b: &BasicBlock) -> Vec<u32> {
    match &b.terminator {
        Terminator::Goto { target, .. } => vec![target.0],
        Terminator::If {
            then_bb, else_bb, ..
        } => vec![then_bb.0, else_bb.0],
        Terminator::Suspend { resume, .. } => vec![resume.0],
        Terminator::Return(_) | Terminator::Unreachable => Vec::new(),
    }
}

/// Each block with an edge to a block on the current DFS path (a loop
/// back edge), with the loop headers its back edges go to; an iterative
/// DFS from the entry block.
#[must_use]
pub fn back_edges(f: &MirFunction) -> HashMap<u32, HashSet<u32>> {
    let index: HashMap<u32, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id.0, i))
        .collect();
    let mut out: HashMap<u32, HashSet<u32>> = HashMap::new();
    // 0 = unvisited, 1 = on the DFS path, 2 = done.
    let mut state = vec![0u8; f.blocks.len()];
    let mut stack: Vec<(usize, Vec<u32>)> = Vec::new();
    if let Some(b) = f.blocks.first() {
        state[0] = 1;
        stack.push((0, succs(b)));
    }
    while let Some((i, rest)) = stack.last_mut() {
        let i = *i;
        let Some(t) = rest.pop() else {
            state[i] = 2;
            stack.pop();
            continue;
        };
        let Some(&j) = index.get(&t) else { continue };
        if state[j] == 0 {
            state[j] = 1;
            stack.push((j, succs(&f.blocks[j])));
        } else if state[j] == 1 {
            out.entry(f.blocks[i].id.0).or_default().insert(t);
        }
    }
    out
}

/// A header cheap to copy: no parameters, a few statements that call
/// nothing and allocate nothing, an `if` at the end.
fn copyable(b: &BasicBlock) -> bool {
    b.params.is_empty()
        && matches!(b.terminator, Terminator::If { .. })
        && b.stmts.len() <= MAX_HEADER
        && b.stmts.iter().all(|s| match s {
            Statement::Assign { rvalue, .. } => matches!(
                rvalue,
                RValue::Use(_)
                    | RValue::BinOp { .. }
                    | RValue::UnaryOp { .. }
                    | RValue::Cast { .. }
                    | RValue::FieldRead { .. }
            ),
            Statement::Loc(..) | Statement::StorageDead(_) => true,
            _ => false,
        })
}

fn retarget(t: &mut Terminator, from: u32, to: u32) {
    let fix = |b: &mut BlockId| {
        if b.0 == from {
            *b = BlockId(to);
        }
    };
    match t {
        Terminator::Goto { target, .. } => fix(target),
        Terminator::If {
            then_bb, else_bb, ..
        } => {
            fix(then_bb);
            fix(else_bb);
        }
        Terminator::Suspend { resume, .. } => fix(resume),
        Terminator::Return(_) | Terminator::Unreachable => {}
    }
}

/// Rotate the loops of `f` whose header tests the exit (see the module
/// doc): the back edges of header `H` go to a copy of `H`.
pub fn rotate(f: &mut MirFunction) {
    let mut latches: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for (l, hs) in back_edges(f) {
        for h in hs {
            latches.entry(h).or_default().push(l);
        }
    }
    let mut next = f.blocks.iter().map(|b| b.id.0 + 1).max().unwrap_or(0);
    for (h, ls) in latches {
        let Some(hb) = f.blocks.iter().find(|b| b.id.0 == h) else {
            continue;
        };
        if !copyable(hb) {
            continue;
        }
        let body = loop_body(f, h, &ls);
        if !succs(hb).iter().any(|s| !body.contains(s)) || !counted(f, hb, &body) {
            continue;
        }
        let mut copy = hb.clone();
        copy.id = BlockId(next);
        retarget(&mut copy.terminator, h, next);
        for b in &mut f.blocks {
            if ls.contains(&b.id.0) {
                retarget(&mut b.terminator, h, next);
            }
        }
        f.blocks.push(copy);
        next += 1;
    }
}

/// The blocks of the loop of header `h` (back edges from `latches`): the
/// ones reaching a latch without passing `h`.
fn loop_body(f: &MirFunction, h: u32, latches: &[u32]) -> HashSet<u32> {
    let mut preds: HashMap<u32, Vec<u32>> = HashMap::new();
    for b in &f.blocks {
        for s in succs(b) {
            preds.entry(s).or_default().push(b.id.0);
        }
    }
    let mut body: HashSet<u32> = HashSet::from([h]);
    let mut work: Vec<u32> = latches.to_vec();
    while let Some(b) = work.pop() {
        if body.insert(b) {
            work.extend(preds.get(&b).into_iter().flatten().copied());
        }
    }
    body
}

/// Whether header `hb` tests an ordering of a local the loop changes
/// against a value it does not (a counter against its bound): such a
/// loop is worth rotating; a test of two moving values (`lo < hi`) gets
/// worse induction variables rotated.
fn counted(f: &MirFunction, hb: &BasicBlock, body: &HashSet<u32>) -> bool {
    let Terminator::If {
        cond: Operand::Copy(c),
        ..
    } = &hb.terminator
    else {
        return false;
    };
    let Some((lhs, rhs)) = hb.stmts.iter().rev().find_map(|s| match s {
        Statement::Assign {
            target,
            rvalue:
                RValue::BinOp {
                    op: PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge,
                    lhs,
                    rhs,
                    ..
                },
        } if target == c => Some((lhs, rhs)),
        _ => None,
    }) else {
        return false;
    };
    let mut moved: HashSet<LocalId> = HashSet::new();
    for b in f.blocks.iter().filter(|b| body.contains(&b.id.0)) {
        moved.extend(b.params.iter().copied());
        for s in &b.stmts {
            if let Statement::Assign { target, .. } = s {
                moved.insert(*target);
            }
        }
    }
    let fixed = |o: &Operand| {
        matches!(o, Operand::Const(_)) || matches!(o, Operand::Copy(l) if !moved.contains(l))
    };
    fixed(lhs) != fixed(rhs)
}

#[cfg(test)]
mod tests {
    use rokc_diagnostic::Span;
    use rokc_ir_common::{ConstVal, FunctionId, PrimTy};

    use super::*;
    use crate::{LocalDecl, MirTy};

    const fn block(id: u32, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            params: vec![],
            stmts,
            terminator,
        }
    }

    const fn op(t: u32, op: PrimOp, lhs: u32, rhs: Operand) -> Statement {
        Statement::Assign {
            target: LocalId(t),
            rvalue: RValue::BinOp {
                op,
                op_ty: MirTy::Prim(PrimTy::Usize),
                lhs: Operand::Copy(LocalId(lhs)),
                rhs,
            },
        }
    }

    /// bb0: goto bb1; bb1: x2 = x0 < x1; if x2 -> bb2 / bb3;
    /// bb2: x0 += 1 (and x1 -= 1 when `both`); goto bb1; bb3: return.
    fn counting(both: bool) -> MirFunction {
        let one = || {
            Operand::Const(ConstVal::UInt {
                value: 1,
                ty: PrimTy::Usize,
            })
        };
        let mut step = vec![op(0, PrimOp::Add, 0, one())];
        if both {
            step.push(op(1, PrimOp::Sub, 1, one()));
        }
        MirFunction {
            id: FunctionId(0),
            def_id: None,
            name: "f".into(),
            facts: rokc_ir_common::FnFacts::default(),
            params: vec![LocalId(0), LocalId(1)],
            locals: (0..3)
                .map(|i| LocalDecl {
                    id: LocalId(i),
                    name: None,
                    ty: MirTy::Prim(PrimTy::Usize),
                })
                .collect(),
            blocks: vec![
                block(
                    0,
                    vec![],
                    Terminator::Goto {
                        target: BlockId(1),
                        args: vec![],
                    },
                ),
                block(
                    1,
                    vec![op(2, PrimOp::Lt, 0, Operand::Copy(LocalId(1)))],
                    Terminator::If {
                        cond: Operand::Copy(LocalId(2)),
                        then_bb: BlockId(2),
                        then_args: vec![],
                        else_bb: BlockId(3),
                        else_args: vec![],
                    },
                ),
                block(
                    2,
                    step,
                    Terminator::Goto {
                        target: BlockId(1),
                        args: vec![],
                    },
                ),
                block(3, vec![], Terminator::Return(None)),
            ],
            param_tys: vec![MirTy::Prim(PrimTy::Usize); 2],
            ret_ty: MirTy::Unit,
            span: Span::default(),
        }
    }

    #[test]
    fn a_counted_loop_tests_at_the_bottom() {
        let mut f = counting(false);
        rotate(&mut f);
        // bb2 goes to bb4, a copy of the test: bb2 is the header now.
        assert_eq!(succs(&f.blocks[2]), vec![4]);
        assert_eq!(succs(&f.blocks[4]), vec![2, 3]);
        let edges = back_edges(&f);
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[&4], HashSet::from([2]));
    }

    #[test]
    fn two_moving_bounds_stay() {
        let mut f = counting(true);
        rotate(&mut f);
        assert_eq!(f.blocks.len(), 4);
    }
}

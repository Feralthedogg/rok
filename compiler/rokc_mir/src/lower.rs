//! HIR → MIR lowering.
//!
//! Builds basic blocks with SSA-style locals. The current slice handles
//! straight-line bodies (no branching); control-flow constructs (if /
//! match / loop) extend this incrementally.

use std::collections::HashMap;

use rokc_hir::{
    HirBlock, HirExpr, HirExprKind, HirFunction, HirMatchArm, HirModule, HirPattern, HirStmt, HirTy,
};
use rokc_ir_common::PrimTy as IrPrimTy;
use rokc_ir_common::{BlockId, ConstVal, FunctionId, LocalId, PrimOp, PrimTy};

use crate::ty::{code_ty, enum_payload_ty, fat_fn, has_gc_ref, lower_ty, lower_ty_in};
use crate::{
    BasicBlock, LocalDecl, MirFunction, MirModule, MirStaticDef, MirTy, Operand, RValue, Statement,
    Terminator,
};

#[must_use]
pub fn lower(module: &HirModule) -> MirModule {
    let mut ret_tys: HashMap<FunctionId, MirTy> = HashMap::new();
    for f in &module.functions {
        ret_tys.insert(f.id, lower_ty_in(&f.ret_ty, module));
    }
    let statics: Vec<MirStaticDef> = module
        .statics
        .iter()
        .map(|s| MirStaticDef {
            name: s.name.clone(),
            ty: lower_ty_in(&s.ty, module),
            init: s.init.clone(),
            is_mut: s.is_mut,
            is_extern: s.is_extern,
            init_fn: s.init_fn,
        })
        .collect();
    let fnv = FnValues {
        wrappers: std::cell::RefCell::new(std::collections::BTreeMap::new()),
        closures: std::cell::RefCell::new(std::collections::BTreeMap::new()),
        coro_ctors: std::cell::RefCell::new(std::collections::BTreeMap::new()),
        next_id: std::cell::Cell::new(
            module
                .functions
                .iter()
                .map(|f| f.id.0 + 1)
                .max()
                .unwrap_or(0),
        ),
        externs: module
            .functions
            .iter()
            .filter(|f| f.body.is_none() && !rokc_ir_common::takes_rok_fn_values(&f.name))
            .map(|f| f.id)
            .collect(),
    };
    let mut functions: Vec<MirFunction> = module
        .functions
        .iter()
        .map(|f| lower_fn(f, module, &ret_tys, &fnv))
        .collect();
    // Coroutine bodies → resume functions + constructors (spec 708).
    for (i, hf) in module.functions.iter().enumerate() {
        if !(hf.is_async || hf.is_generator) || hf.body.is_none() {
            continue;
        }
        let ctor = *fnv
            .coro_ctors
            .borrow_mut()
            .entry(hf.id)
            .or_insert_with(|| fnv.fresh_id());
        // An `async` body takes the poll's `Context` on every resume.
        let ctor_fn = crate::coro::transform(&mut functions[i], usize::from(hf.is_async), ctor);
        functions.push(ctor_fn);
    }
    finish_fn_values(&mut functions, &fnv);
    // Lazy static initializers are called from codegen's access checks.
    let roots: Vec<FunctionId> = module
        .exports
        .iter()
        .map(|(id, _)| *id)
        .chain(statics.iter().filter_map(|s| s.init_fn))
        .collect();
    prune_unreachable(&mut functions, &roots);
    MirModule {
        functions,
        statics,
        exports: module.exports.clone(),
        pkg_hashes: Vec::new(),
    }
}

/// What lowering function values (spec 4.4: `{code, env}`) leaves to do
/// once every body is lowered.
struct FnValues {
    /// Named fn → its `(env, args..)` wrapper (the code of `f` as a value).
    wrappers: std::cell::RefCell<std::collections::BTreeMap<FunctionId, FunctionId>>,
    /// Lifted closure body → its env's MIR type: the body gets the env as
    /// a `GcRef` and loads it on entry.
    closures: std::cell::RefCell<std::collections::BTreeMap<FunctionId, MirTy>>,
    next_id: std::cell::Cell<u32>,
    /// Coroutine body → its constructor (`coro::transform`).
    coro_ctors: std::cell::RefCell<std::collections::BTreeMap<FunctionId, FunctionId>>,
    /// `extern` functions (but `rok_thread_spawn`): their `fn` parameters stay thin C pointers.
    externs: std::collections::HashSet<FunctionId>,
}

impl FnValues {
    fn fresh_id(&self) -> FunctionId {
        let id = FunctionId(self.next_id.get());
        self.next_id.set(id.0 + 1);
        id
    }
}

fn finish_fn_values(functions: &mut Vec<MirFunction>, fnv: &FnValues) {
    // Closure bodies: param 0 becomes the boxed env, unpacked on entry.
    for (id, env_ty) in fnv.closures.borrow().iter() {
        let Some(f) = functions.iter_mut().find(|f| f.id == *id) else {
            continue;
        };
        let (Some(&env_local), false) = (f.params.first(), f.blocks.is_empty()) else {
            continue;
        };
        let boxed = LocalId(u32::try_from(f.locals.len()).expect("too many locals"));
        f.locals.push(LocalDecl {
            id: boxed,
            name: Some("#env".to_owned()),
            ty: MirTy::GcRef,
        });
        f.params[0] = boxed;
        f.param_tys[0] = MirTy::GcRef;
        f.blocks[0].stmts.insert(
            0,
            Statement::Assign {
                target: env_local,
                rvalue: RValue::HeapLoad {
                    ptr: Operand::Copy(boxed),
                    ty: env_ty.clone(),
                },
            },
        );
    }
    // Named fns used as values: `fn #w(env, args..) { return f(args..); }`.
    for (target, wrapper) in fnv.wrappers.borrow().iter() {
        let Some(f) = functions.iter().find(|f| f.id == *target) else {
            continue;
        };
        let mut locals = vec![LocalDecl {
            id: LocalId(0),
            name: Some("#env".to_owned()),
            ty: MirTy::GcRef,
        }];
        let mut params = vec![LocalId(0)];
        for t in &f.param_tys {
            let id = LocalId(u32::try_from(locals.len()).expect("too many locals"));
            locals.push(LocalDecl {
                id,
                name: None,
                ty: t.clone(),
            });
            params.push(id);
        }
        let ret = LocalId(u32::try_from(locals.len()).expect("too many locals"));
        locals.push(LocalDecl {
            id: ret,
            name: None,
            ty: f.ret_ty.clone(),
        });
        let unit = matches!(f.ret_ty, MirTy::Unit);
        let call = Statement::Assign {
            target: ret,
            rvalue: RValue::Call {
                callee: f.id,
                args: params[1..].iter().map(|l| Operand::Copy(*l)).collect(),
                ret_ty: f.ret_ty.clone(),
            },
        };
        let mut param_tys = vec![MirTy::GcRef];
        param_tys.extend(f.param_tys.iter().cloned());
        let w = MirFunction {
            id: *wrapper,
            def_id: None,
            name: format!("{}__fnval", f.name),
            params,
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                params: Vec::new(),
                stmts: vec![call],
                terminator: Terminator::Return((!unit).then_some(Operand::Copy(ret))),
            }],
            param_tys,
            ret_ty: f.ret_ty.clone(),
            span: f.span,
        };
        functions.push(w);
    }
}

/// Drop functions `main` can't reach (direct calls and `fn` values).
/// No `main` (a library) keeps everything. Every defined function gets
/// a mangled symbol, so nothing else is called from outside by name.
// ponytail: `#[export_name]` items would be roots too; the attribute
// isn't carried into MIR yet.
fn prune_unreachable(functions: &mut Vec<MirFunction>, exports: &[FunctionId]) {
    // Roots: `main` and `#[export_name]` items (spec 902 9.2.8).
    let Some(main) = functions.iter().find(|f| f.name == "main").map(|f| f.id) else {
        return;
    };
    let index: HashMap<FunctionId, usize> = functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, i))
        .collect();
    let mut live: std::collections::HashSet<FunctionId> = std::collections::HashSet::new();
    let mut work = vec![main];
    work.extend_from_slice(exports);
    while let Some(id) = work.pop() {
        if !live.insert(id) {
            continue;
        }
        let Some(&i) = index.get(&id) else { continue };
        for b in &functions[i].blocks {
            for s in &b.stmts {
                if let Statement::Assign {
                    rvalue: RValue::Call { callee, .. } | RValue::FnAddr { callee, .. },
                    ..
                } = s
                {
                    work.push(*callee);
                }
            }
        }
    }
    functions.retain(|f| live.contains(&f.id));
}

fn lower_fn(
    f: &HirFunction,
    module: &HirModule,
    ret_tys: &HashMap<FunctionId, MirTy>,
    fnv: &FnValues,
) -> MirFunction {
    let mut builder = FnBuilder::new(module, ret_tys, fnv);

    // Mirror HIR locals so HIR LocalId == MIR LocalId.
    for l in &f.locals {
        builder.locals.push(LocalDecl {
            id: l.id,
            name: l.name.clone(),
            ty: lower_ty_in(&l.ty, module),
        });
    }

    // An extern's `fn` parameter is a C function pointer (thin); the
    // runtime's `rok_thread_spawn` takes the fat `{code, env}` value.
    let param_tys: Vec<MirTy> = f
        .params
        .iter()
        .map(|p| {
            match (
                &p.ty,
                f.body.is_none() && !rokc_ir_common::takes_rok_fn_values(&f.name),
            ) {
                (HirTy::Fn(args, ret, _), true) => MirTy::Fn(
                    args.iter().map(|a| lower_ty_in(a, module)).collect(),
                    Box::new(lower_ty_in(ret, module)),
                ),
                (t, _) => lower_ty_in(t, module),
            }
        })
        .collect();
    let params: Vec<LocalId> = f.params.iter().map(|p| p.local).collect();

    if f.body.is_some() {
        let entry = builder.new_block();
        builder.current = entry;
        let returned = builder.lower_block(f.body.as_ref().unwrap(), true);
        if !returned {
            let term = if matches!(lower_ty_in(&f.ret_ty, module), MirTy::Unit) {
                Terminator::Return(None)
            } else {
                Terminator::Unreachable
            };
            builder.terminate(term);
        }
    }
    // No body → no blocks → emit declaration form in codegen.

    MirFunction {
        id: f.id,
        def_id: f.def_id,
        name: f.name.clone(),
        params,
        locals: builder.locals,
        blocks: reachable_blocks(builder.blocks),
        param_tys,
        ret_ty: lower_ty_in(&f.ret_ty, module),
        span: f.span,
    }
}

/// Drop blocks no path from the entry reaches (e.g. `match` arms after
/// a catch-all): MLIR's dialect conversion leaves their ops unconverted.
fn reachable_blocks(blocks: Vec<BasicBlock>) -> Vec<BasicBlock> {
    let mut seen = vec![false; blocks.len()];
    let mut work = if blocks.is_empty() { vec![] } else { vec![0] };
    while let Some(i) = work.pop() {
        if std::mem::replace(&mut seen[i], true) {
            continue;
        }
        match &blocks[i].terminator {
            Terminator::Goto { target, .. } => work.push(target.0 as usize),
            Terminator::If {
                then_bb, else_bb, ..
            } => work.extend([then_bb.0 as usize, else_bb.0 as usize]),
            Terminator::Suspend { resume, .. } => work.push(resume.0 as usize),
            Terminator::Return(_) | Terminator::Unreachable => {}
        }
    }
    blocks
        .into_iter()
        .filter(|b| seen[b.id.0 as usize])
        .collect()
}

struct LoopFrame {
    /// Where `continue` jumps to. For `while`, the header (cond check);
    /// for `loop`, the start of the body.
    continue_bb: BlockId,
    /// Where `break` jumps to.
    break_bb: BlockId,
    /// Block param of `break_bb` carrying the loop's value, if any.
    break_param: Option<LocalId>,
    label: Option<String>,
    /// `false` for a labelled block: only `break 'label` targets it, an
    /// unlabelled `break` / `continue` goes to the enclosing loop.
    is_loop: bool,
}

struct FnBuilder<'a> {
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    current: BlockId,
    module: &'a HirModule,
    fn_ret_tys: &'a HashMap<FunctionId, MirTy>,
    fnv: &'a FnValues,
    loop_stack: Vec<LoopFrame>,
    /// Set of block ids that have been explicitly terminated. Once a
    /// block is terminated further `push_stmt` / `terminate` calls are
    /// dropped — the rest of the source path is dead code.
    terminated: std::collections::HashSet<u32>,
}

impl<'a> FnBuilder<'a> {
    fn new(
        module: &'a HirModule,
        fn_ret_tys: &'a HashMap<FunctionId, MirTy>,
        fnv: &'a FnValues,
    ) -> Self {
        Self {
            locals: Vec::new(),
            blocks: Vec::new(),
            current: BlockId(0),
            module,
            fn_ret_tys,
            fnv,
            loop_stack: Vec::new(),
            terminated: std::collections::HashSet::new(),
        }
    }

    fn new_block(&mut self) -> BlockId {
        let id = BlockId(u32::try_from(self.blocks.len()).expect("too many blocks"));
        self.blocks.push(BasicBlock {
            id,
            params: Vec::new(),
            stmts: Vec::new(),
            terminator: Terminator::Unreachable,
        });
        id
    }

    fn add_block_param(&mut self, block: BlockId, ty: MirTy) -> LocalId {
        let local = self.fresh_local(ty);
        self.blocks[block.0 as usize].params.push(local);
        local
    }

    fn current_block(&mut self) -> &mut BasicBlock {
        &mut self.blocks[self.current.0 as usize]
    }

    fn block_is_live(&self) -> bool {
        !self.terminated.contains(&self.current.0)
    }

    fn push_stmt(&mut self, s: Statement) {
        if !self.block_is_live() {
            return;
        }
        self.current_block().stmts.push(s);
    }

    fn terminate(&mut self, t: Terminator) {
        if !self.block_is_live() {
            return;
        }
        self.current_block().terminator = t;
        self.terminated.insert(self.current.0);
    }

    fn fresh_local(&mut self, ty: MirTy) -> LocalId {
        let id = LocalId(u32::try_from(self.locals.len()).expect("LocalId overflow"));
        self.locals.push(LocalDecl { id, name: None, ty });
        id
    }

    /// Lower a block at function-body level. The trailing expression
    /// becomes the implicit return value. Returns `true` if the block
    /// ended in a terminating statement.
    fn lower_block(&mut self, b: &HirBlock, _is_fn_body: bool) -> bool {
        for s in &b.stmts {
            if self.lower_stmt(s) {
                return true;
            }
        }
        if let Some(t) = &b.trailing {
            let op = self.lower_expr_to_operand(t);
            // Unit-typed trailing — emit a no-args return so void-fn
            // signatures stay well-typed.
            let term = if matches!(lower_ty_in(&t.ty, self.module), MirTy::Unit) {
                Terminator::Return(None)
            } else {
                Terminator::Return(Some(op))
            };
            self.terminate(term);
            return true;
        }
        false
    }

    /// Lower a block whose value is needed. Returns `(operand, diverged)`
    /// where `diverged` is true when the block already terminated the
    /// current basic block (e.g. via `return`, `break`, `continue`). The
    /// caller must not append another terminator in that case.
    fn lower_block_value(&mut self, b: &HirBlock) -> (Operand, bool) {
        let first_temp = self.locals.len();
        for s in &b.stmts {
            if self.lower_stmt(s) {
                return (Operand::Const(ConstVal::Unit), true);
            }
        }
        let mut value = match &b.trailing {
            Some(t) => self.lower_expr_to_operand(t),
            None => Operand::Const(ConstVal::Unit),
        };
        // The block's `let`s and the temporaries made while lowering it go
        // out of scope (only the block value escapes, copied below): tell
        // codegen so their shadow-stack roots stop keeping objects alive.
        let lets = b.stmts.iter().filter_map(|s| match s {
            HirStmt::Let { local, .. } => Some(*local),
            _ => None,
        });
        let temps = (first_temp..self.locals.len()).map(|i| self.locals[i].id);
        let mut dead: Vec<LocalId> = lets
            .chain(temps)
            .filter(|l| has_gc_ref(&self.locals[l.0 as usize].ty))
            .collect();
        dead.dedup();
        let escaping = match &value {
            Operand::Copy(l) => dead.contains(l).then_some(*l),
            Operand::Const(_) => None,
        };
        if let Some(l) = escaping {
            let tmp = self.fresh_local(self.locals[l.0 as usize].ty.clone());
            self.push_stmt(Statement::Assign {
                target: tmp,
                rvalue: RValue::Use(value),
            });
            value = Operand::Copy(tmp);
        }
        for l in dead {
            self.push_stmt(Statement::StorageDead(l));
        }
        (value, false)
    }

    fn lower_stmt(&mut self, s: &HirStmt) -> bool {
        match s {
            HirStmt::Let { local, init } => {
                // Array literals write directly into the target slot —
                // routing them through a temporary would copy a memref
                // by value, which is ill-typed.
                if let HirExprKind::ArrayInit { elem_ty, elements } = &init.kind {
                    let mir_elem_ty = lower_ty_in(elem_ty, self.module);
                    let elem_ops: Vec<Operand> = elements
                        .iter()
                        .map(|e| self.lower_expr_to_operand(e))
                        .collect();
                    self.push_stmt(Statement::Assign {
                        target: *local,
                        rvalue: RValue::ArrayInit {
                            elem_ty: mir_elem_ty,
                            elements: elem_ops,
                        },
                    });
                    return false;
                }
                let rvalue = self.lower_expr_to_rvalue(init);
                self.push_stmt(Statement::Assign {
                    target: *local,
                    rvalue,
                });
                false
            }
            HirStmt::Assign { local, value } => {
                let rvalue = self.lower_expr_to_rvalue(value);
                self.push_stmt(Statement::Assign {
                    target: *local,
                    rvalue,
                });
                false
            }
            HirStmt::ArrayAssign {
                array_local,
                index,
                value,
                elem_ty,
            } => {
                let idx = self.lower_expr_to_operand(index);
                let val = self.lower_expr_to_operand(value);
                let mir_elem_ty = lower_ty_in(elem_ty, self.module);
                let len = match &self.locals[array_local.0 as usize].ty {
                    MirTy::Array(_, n) => *n,
                    _ => 0,
                };
                self.push_stmt(Statement::ArrayWrite {
                    array: *array_local,
                    index: idx,
                    value: val,
                    elem_ty: mir_elem_ty,
                    len,
                });
                false
            }
            HirStmt::Expr(e) => {
                let _ = self.lower_expr_to_operand(e);
                false
            }
            HirStmt::Return(value) => {
                let op = value.as_ref().map(|e| self.lower_expr_to_operand(e));
                self.terminate(Terminator::Return(op));
                true
            }
            HirStmt::Break { label, value } => {
                let value_op = value.as_ref().map(|e| self.lower_expr_to_operand(e));
                let Some(frame) = self.find_loop_frame(label.as_deref()) else {
                    // No enclosing loop; fall back to unreachable so the
                    // caller's pipeline doesn't read uninitialised state.
                    self.terminate(Terminator::Unreachable);
                    return true;
                };
                let break_bb = frame.break_bb;
                let args = match (frame.break_param, value_op) {
                    (Some(_), Some(v)) => vec![v],
                    (Some(_), None) => vec![Operand::Const(ConstVal::Unit)],
                    _ => Vec::new(),
                };
                self.terminate(Terminator::Goto {
                    target: break_bb,
                    args,
                });
                true
            }
            HirStmt::Continue { label } => {
                let Some(frame) = self.find_loop_frame(label.as_deref()) else {
                    self.terminate(Terminator::Unreachable);
                    return true;
                };
                let target = frame.continue_bb;
                self.terminate(Terminator::Goto {
                    target,
                    args: Vec::new(),
                });
                true
            }
            HirStmt::Panic(call) => {
                // The payload calls a never-returning runtime hook.
                // Emit the call, then an `unreachable` terminator so the
                // surrounding block won't fall through into a merge.
                let _ = self.lower_expr_to_operand(call);
                self.terminate(Terminator::Unreachable);
                true
            }
            HirStmt::StaticAssign { name, value } => {
                let mir_ty = lower_ty_in(&value.ty, self.module);
                let value_op = self.lower_expr_to_operand(value);
                self.push_stmt(Statement::StaticStore {
                    name: name.clone(),
                    value: value_op,
                    ty: mir_ty,
                });
                false
            }
        }
    }

    fn find_loop_frame(&self, label: Option<&str>) -> Option<&LoopFrame> {
        match label {
            None => self.loop_stack.iter().rev().find(|f| f.is_loop),
            Some(name) => self
                .loop_stack
                .iter()
                .rev()
                .find(|f| f.label.as_deref() == Some(name)),
        }
    }

    fn lower_expr_to_rvalue(&mut self, e: &HirExpr) -> RValue {
        match &e.kind {
            HirExprKind::PrimBinOp { op, lhs, rhs } => {
                let op_ty = lower_ty(&lhs.ty);
                let lhs_op = self.lower_expr_to_operand(lhs);
                let rhs_op = self.lower_expr_to_operand(rhs);
                RValue::BinOp {
                    op: *op,
                    op_ty,
                    lhs: lhs_op,
                    rhs: rhs_op,
                }
            }
            HirExprKind::PrimUnaryOp { op, operand } => {
                let op_ty = lower_ty(&operand.ty);
                let v = self.lower_expr_to_operand(operand);
                RValue::UnaryOp {
                    op: *op,
                    op_ty,
                    operand: v,
                }
            }
            HirExprKind::Call { callee, args } => {
                let c_callback = self.fnv.externs.contains(callee);
                let mut arg_ops = Vec::with_capacity(args.len());
                for a in args {
                    // A named fn passed to C: its own (thin) address.
                    if let (true, HirExprKind::FnRef(id), HirTy::Fn(ps, r, _)) =
                        (c_callback, &a.kind, &a.ty)
                    {
                        let fn_ty = MirTy::Fn(
                            ps.iter().map(|t| lower_ty_in(t, self.module)).collect(),
                            Box::new(lower_ty_in(r, self.module)),
                        );
                        let l = self.fresh_local(fn_ty.clone());
                        self.push_stmt(Statement::Assign {
                            target: l,
                            rvalue: RValue::FnAddr { callee: *id, fn_ty },
                        });
                        arg_ops.push(Operand::Copy(l));
                        continue;
                    }
                    arg_ops.push(self.lower_expr_to_operand(a));
                }
                let ret_ty = self.fn_ret_tys.get(callee).cloned().unwrap_or(MirTy::Unit);
                RValue::Call {
                    callee: *callee,
                    args: arg_ops,
                    ret_ty,
                }
            }
            // A named fn as a value: `{wrapper, null}`.
            HirExprKind::FnRef(id) => {
                let MirTy::Tuple(parts) = lower_ty_in(&e.ty, self.module) else {
                    return RValue::Use(Operand::Const(ConstVal::Unit));
                };
                let wrapper = *self
                    .fnv
                    .wrappers
                    .borrow_mut()
                    .entry(*id)
                    .or_insert_with(|| {
                        let w = FunctionId(self.fnv.next_id.get());
                        self.fnv.next_id.set(w.0 + 1);
                        w
                    });
                let code = self.fresh_local(parts[0].clone());
                self.push_stmt(Statement::Assign {
                    target: code,
                    rvalue: RValue::FnAddr {
                        callee: wrapper,
                        fn_ty: parts[0].clone(),
                    },
                });
                RValue::StructInit {
                    ty: MirTy::Tuple(parts),
                    fields: vec![
                        Operand::Copy(code),
                        Operand::Const(ConstVal::Int {
                            value: 0,
                            ty: IrPrimTy::Usize,
                        }),
                    ],
                }
            }
            HirExprKind::CallIndirect {
                callee,
                args,
                ret_ty,
            } => {
                let callee_op = self.lower_expr_to_operand(callee);
                self.call_fn_value(callee_op, args, ret_ty)
            }
            HirExprKind::Cast {
                operand,
                from_ty,
                to_ty,
            } => {
                let source = self.lower_expr_to_operand(operand);
                RValue::Cast {
                    source,
                    from_ty: lower_ty_in(from_ty, self.module),
                    to_ty: lower_ty_in(to_ty, self.module),
                }
            }
            // A closure value: `{body, boxed captures}`; the body takes
            // the box (see `finish_fn_values`).
            HirExprKind::ClosureValue {
                fn_id,
                env,
                env_ty,
                arg_tys,
                ret_ty,
            } => {
                let env_mir = lower_ty_in(env_ty, self.module);
                self.fnv
                    .closures
                    .borrow_mut()
                    .insert(*fn_id, env_mir.clone());
                let args: Vec<MirTy> = arg_tys
                    .iter()
                    .map(|t| lower_ty_in(t, self.module))
                    .collect();
                let ret = lower_ty_in(ret_ty, self.module);
                let code_t = code_ty(args.clone(), ret.clone());
                let env_op = self.lower_expr_to_operand(env);
                let boxed = self.fresh_local(MirTy::GcRef);
                self.push_stmt(Statement::Assign {
                    target: boxed,
                    rvalue: RValue::HeapBox {
                        value: env_op,
                        ty: env_mir,
                    },
                });
                let code = self.fresh_local(code_t.clone());
                self.push_stmt(Statement::Assign {
                    target: code,
                    rvalue: RValue::FnAddr {
                        callee: *fn_id,
                        fn_ty: code_t,
                    },
                });
                RValue::StructInit {
                    ty: fat_fn(args, ret),
                    fields: vec![Operand::Copy(code), Operand::Copy(boxed)],
                }
            }
            HirExprKind::CallClosure {
                closure,
                args,
                ret_ty,
                ..
            } => {
                let closure_op = self.lower_expr_to_operand(closure);
                self.call_fn_value(closure_op, args, ret_ty)
            }
            // `{resume, frame}` from the coroutine's constructor.
            HirExprKind::CoroNew { body_fn, args } => {
                let ctor = *self
                    .fnv
                    .coro_ctors
                    .borrow_mut()
                    .entry(*body_fn)
                    .or_insert_with(|| self.fnv.fresh_id());
                let args = args.iter().map(|a| self.lower_expr_to_operand(a)).collect();
                RValue::Call {
                    callee: ctor,
                    args,
                    ret_ty: lower_ty_in(&e.ty, self.module),
                }
            }
            _ => RValue::Use(self.lower_expr_to_operand(e)),
        }
    }

    fn lower_expr_to_operand(&mut self, e: &HirExpr) -> Operand {
        match &e.kind {
            HirExprKind::Const(c) => Operand::Const(c.clone()),
            HirExprKind::Local(id) => Operand::Copy(*id),
            HirExprKind::StaticRef(name) => {
                let mir_ty = lower_ty_in(&e.ty, self.module);
                let dst = self.fresh_local(mir_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::StaticLoad {
                        name: name.clone(),
                        ty: mir_ty,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::Block(b) => {
                // Plain block: just execute. Labeled block: push a
                // frame so `break 'label value` exits with a value via
                // a join block.
                if let Some(label) = b.label.clone() {
                    let exit_bb = self.new_block();
                    let result_ty = lower_ty_in(&e.ty, self.module);
                    let break_param = if matches!(result_ty, MirTy::Unit) {
                        None
                    } else {
                        Some(self.add_block_param(exit_bb, result_ty))
                    };
                    self.loop_stack.push(LoopFrame {
                        // `continue` inside a labeled block isn't
                        // meaningful — point it at exit so misuse
                        // becomes a no-op rather than a crash.
                        continue_bb: exit_bb,
                        break_bb: exit_bb,
                        break_param,
                        label: Some(label),
                        is_loop: false,
                    });
                    let (value, diverged) = self.lower_block_value(b);
                    self.loop_stack.pop();
                    if !diverged {
                        let args = match break_param {
                            Some(_) => vec![value],
                            None => Vec::new(),
                        };
                        self.terminate(Terminator::Goto {
                            target: exit_bb,
                            args,
                        });
                    }
                    self.current = exit_bb;
                    match break_param {
                        Some(p) => Operand::Copy(p),
                        None => Operand::Const(ConstVal::Unit),
                    }
                } else {
                    for s in &b.stmts {
                        self.lower_stmt(s);
                    }
                    if let Some(t) = &b.trailing {
                        self.lower_expr_to_operand(t)
                    } else {
                        Operand::Const(ConstVal::Unit)
                    }
                }
            }
            // HIR reports every unresolved name; reaching MIR is a bug.
            HirExprKind::UnresolvedPath(p) => {
                panic!(
                    "internal compiler error: unresolved path `{}` reached MIR",
                    p.join("::")
                )
            }
            HirExprKind::Call { callee, .. } => {
                let result_ty = self.fn_ret_tys.get(callee).cloned().unwrap_or(MirTy::Unit);
                let dst = self.fresh_local(result_ty);
                let rvalue = self.lower_expr_to_rvalue(e);
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue,
                });
                Operand::Copy(dst)
            }
            HirExprKind::CallIndirect { ret_ty, .. } => {
                let result_ty = lower_ty_in(ret_ty, self.module);
                let dst = self.fresh_local(result_ty);
                let rvalue = self.lower_expr_to_rvalue(e);
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue,
                });
                Operand::Copy(dst)
            }
            HirExprKind::Cast { to_ty, .. } => {
                let result_ty = lower_ty_in(to_ty, self.module);
                let dst = self.fresh_local(result_ty);
                let rvalue = self.lower_expr_to_rvalue(e);
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue,
                });
                Operand::Copy(dst)
            }
            HirExprKind::PrimBinOp { .. }
            | HirExprKind::PrimUnaryOp { .. }
            | HirExprKind::FnRef(_)
            | HirExprKind::ClosureValue { .. }
            | HirExprKind::CoroNew { .. }
            | HirExprKind::CallClosure { .. } => {
                let result_ty = lower_ty_in(&e.ty, self.module);
                let dst = self.fresh_local(result_ty);
                let rvalue = self.lower_expr_to_rvalue(e);
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue,
                });
                Operand::Copy(dst)
            }
            HirExprKind::Suspend { value, is_final } => {
                let v = self.lower_expr_to_operand(value);
                let unit = matches!(lower_ty_in(&value.ty, self.module), MirTy::Unit);
                let resume = self.new_block();
                self.terminate(Terminator::Suspend {
                    value: (!unit).then_some(v),
                    resume,
                    is_final: *is_final,
                });
                self.current = resume;
                Operand::Const(ConstVal::Unit)
            }
            HirExprKind::If {
                cond,
                then_block,
                else_branch,
            } => self.lower_if(cond, then_block, else_branch.as_deref(), &e.ty),
            HirExprKind::While { label, cond, body } => self.lower_while(label.clone(), cond, body),
            HirExprKind::Loop {
                label,
                body,
                result_ty,
            } => self.lower_loop(label.clone(), body, result_ty),
            HirExprKind::Match { scrutinee, arms } => self.lower_match(scrutinee, arms, &e.ty),
            HirExprKind::StructInit { struct_id, fields } => {
                let result_ty = lower_ty_in(&e.ty, self.module);
                let field_ops: Vec<Operand> = fields
                    .iter()
                    .map(|f| self.lower_expr_to_operand(f))
                    .collect();
                let dst = self.fresh_local(result_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::StructInit {
                        ty: result_ty,
                        fields: field_ops,
                    },
                });
                let _ = struct_id;
                Operand::Copy(dst)
            }
            HirExprKind::SumWrap {
                sum_ty,
                variant_index,
                value,
            } => {
                let mir_ty = lower_ty_in(sum_ty, self.module);
                let tag_op = Operand::Const(ConstVal::Int {
                    value: i128::from(*variant_index),
                    ty: IrPrimTy::I32,
                });
                // `any Tr` (D4): the payload is a heap copy of the value.
                // ponytail: always boxed; inline values that fit a word
                // once `ANY_SLOT` tracing (802 §8.2.7) exists.
                if let (HirTy::AnyTrait(_), Some(v)) = (sum_ty, value) {
                    let raw = self.lower_expr_to_operand(v);
                    let ptr = self.fresh_local(MirTy::GcRef);
                    self.push_stmt(Statement::Assign {
                        target: ptr,
                        rvalue: RValue::HeapBox {
                            value: raw,
                            ty: lower_ty_in(&v.ty, self.module),
                        },
                    });
                    let dst = self.fresh_local(mir_ty.clone());
                    self.push_stmt(Statement::Assign {
                        target: dst,
                        rvalue: RValue::StructInit {
                            ty: mir_ty,
                            fields: vec![tag_op, Operand::Copy(ptr)],
                        },
                    });
                    return Operand::Copy(dst);
                }
                // Payload-less sum (all-none, exotic) — return tag only.
                let MirTy::Tuple(parts) = &mir_ty else {
                    return tag_op;
                };
                let payload_ty = parts[1].clone();
                // Spec 변경점 1019: heterogeneous sums (`i32 | f64`) reserve
                // payload storage for the widest variant. The wrap site
                // casts the value's MIR type to that unified payload so
                // every variant fits into the same struct slot.
                let payload_op = match value {
                    Some(v) => {
                        let raw = self.lower_expr_to_operand(v);
                        let value_ty = lower_ty_in(&v.ty, self.module);
                        self.payload_cast(raw, &value_ty, &payload_ty)
                    }
                    None => Operand::Const(zero_const(&payload_ty)),
                };
                let dst = self.fresh_local(mir_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::StructInit {
                        ty: mir_ty,
                        fields: vec![tag_op, payload_op],
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::EnumVariantInit {
                enum_id,
                variant_index,
                args,
            } => {
                let tag_op = Operand::Const(ConstVal::Int {
                    value: i128::from(*variant_index),
                    ty: IrPrimTy::I32,
                });
                let Some(payload_ty) = enum_payload_ty(*enum_id, self.module) else {
                    for a in args {
                        self.lower_expr_to_operand(a);
                    }
                    return tag_op;
                };
                let unit_arg = matches!(args.as_slice(), [a] if lower_ty_in(&a.ty, self.module) == MirTy::Unit);
                let payload_op = if args.is_empty() || unit_arg {
                    Operand::Const(zero_const(&payload_ty))
                } else if args.len() == 1 {
                    let arg = &args[0];
                    let raw = self.lower_expr_to_operand(arg);
                    self.payload_cast(raw, &lower_ty_in(&arg.ty, self.module), &payload_ty)
                } else {
                    // Multi-arg variant: pack the args into the variant's
                    // own tuple, then move it into the shared slot.
                    let variant_ty = self.variant_payload_ty(*enum_id, *variant_index);
                    let MirTy::Tuple(field_tys) = variant_ty.clone() else {
                        return tag_op;
                    };
                    let field_ops: Vec<Operand> = args
                        .iter()
                        .zip(field_tys.iter())
                        .map(|(a, ft)| {
                            let raw = self.lower_expr_to_operand(a);
                            self.cast_to(raw, &lower_ty_in(&a.ty, self.module), ft)
                        })
                        .collect();
                    let tup = self.fresh_local(variant_ty.clone());
                    self.push_stmt(Statement::Assign {
                        target: tup,
                        rvalue: RValue::StructInit {
                            ty: variant_ty.clone(),
                            fields: field_ops,
                        },
                    });
                    self.payload_cast(Operand::Copy(tup), &variant_ty, &payload_ty)
                };
                let enum_ty = MirTy::Tuple(vec![MirTy::Prim(IrPrimTy::I32), payload_ty]);
                let dst = self.fresh_local(enum_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::StructInit {
                        ty: enum_ty,
                        fields: vec![tag_op, payload_op],
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::ArrayInit { elem_ty, elements } => {
                let mir_elem_ty = lower_ty_in(elem_ty, self.module);
                let n = u32::try_from(elements.len()).unwrap_or(0);
                let array_ty = MirTy::Array(Box::new(mir_elem_ty.clone()), n);
                let elem_ops: Vec<Operand> = elements
                    .iter()
                    .map(|e| self.lower_expr_to_operand(e))
                    .collect();
                let dst = self.fresh_local(array_ty);
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::ArrayInit {
                        elem_ty: mir_elem_ty,
                        elements: elem_ops,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::ArrayRepeat {
                elem_ty,
                value,
                len,
            } => {
                let elem = lower_ty_in(elem_ty, self.module);
                let v = self.lower_expr_to_operand(value);
                let dst = self.fresh_local(MirTy::Array(Box::new(elem.clone()), *len));
                if has_gc_ref(&elem) {
                    // ponytail: no element is left unset while a GC
                    // could scan the slot; unrolled like `ArrayInit`.
                    self.push_stmt(Statement::Assign {
                        target: dst,
                        rvalue: RValue::ArrayInit {
                            elem_ty: elem,
                            elements: vec![v; *len as usize],
                        },
                    });
                } else {
                    self.fill_array(dst, &elem, v, *len);
                }
                Operand::Copy(dst)
            }
            HirExprKind::BufNew { elem, len } => {
                let len = self.lower_expr_to_operand(len);
                let dst = self.fresh_local(MirTy::GcRef);
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::BufAlloc {
                        elem_ty: lower_ty_in(elem, self.module),
                        len,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::RawRead { addr, ty, volatile } => {
                let addr = self.lower_expr_to_operand(addr);
                let ty = lower_ty_in(ty, self.module);
                let dst = self.fresh_local(ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::RawLoad {
                        addr,
                        ty,
                        volatile: *volatile,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::RawWrite {
                addr,
                value,
                ty,
                volatile,
            } => {
                let addr = self.lower_expr_to_operand(addr);
                let value = self.lower_expr_to_operand(value);
                self.push_stmt(Statement::RawStore {
                    addr,
                    value,
                    ty: lower_ty_in(ty, self.module),
                    volatile: *volatile,
                });
                Operand::Const(ConstVal::Unit)
            }
            HirExprKind::SizeOf { ty, align } => {
                let dst = self.fresh_local(MirTy::Prim(PrimTy::Usize));
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::SizeOf {
                        ty: lower_ty_in(ty, self.module),
                        align: *align,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::BufGet { buf, index, elem } => {
                let buf = self.lower_expr_to_operand(buf);
                let index = self.lower_expr_to_operand(index);
                let elem_ty = lower_ty_in(elem, self.module);
                // A buffer of `()` stores nothing.
                if elem_ty == MirTy::Unit {
                    return Operand::Const(ConstVal::Unit);
                }
                let dst = self.fresh_local(elem_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::BufLoad {
                        buf,
                        index,
                        elem_ty,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::BufAtomic {
                op,
                buf,
                index,
                args,
                elem,
                order,
            } => {
                let buf = self.lower_expr_to_operand(buf);
                let index = self.lower_expr_to_operand(index);
                let args = args.iter().map(|a| self.lower_expr_to_operand(a)).collect();
                let elem_ty = lower_ty_in(elem, self.module);
                let dst = self.fresh_local(elem_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::BufAtomic {
                        op,
                        buf,
                        index,
                        args,
                        elem_ty,
                        order: *order,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::BufSet {
                buf,
                index,
                value,
                elem,
            } => {
                let buf = self.lower_expr_to_operand(buf);
                let index = self.lower_expr_to_operand(index);
                let value = self.lower_expr_to_operand(value);
                let elem_ty = lower_ty_in(elem, self.module);
                if elem_ty != MirTy::Unit {
                    self.push_stmt(Statement::BufStore {
                        buf,
                        index,
                        value,
                        elem_ty,
                    });
                }
                Operand::Const(ConstVal::Unit)
            }
            HirExprKind::ArrayIndex {
                array,
                index,
                elem_ty,
            } => {
                let arr_op = self.lower_expr_to_operand(array);
                let idx_op = self.lower_expr_to_operand(index);
                let Operand::Copy(arr_local) = arr_op else {
                    return Operand::Const(ConstVal::Unit);
                };
                let mir_elem_ty = lower_ty_in(elem_ty, self.module);
                let len = match &self.locals[arr_local.0 as usize].ty {
                    MirTy::Array(_, n) => *n,
                    _ => 0,
                };
                let dst = self.fresh_local(mir_elem_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::ArrayIndex {
                        array: arr_local,
                        index: idx_op,
                        elem_ty: mir_elem_ty,
                        len,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::Tuple { fields } => {
                let result_ty = lower_ty_in(&e.ty, self.module);
                let field_ops: Vec<Operand> = fields
                    .iter()
                    .map(|f| self.lower_expr_to_operand(f))
                    .collect();
                let dst = self.fresh_local(result_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::StructInit {
                        ty: result_ty,
                        fields: field_ops,
                    },
                });
                Operand::Copy(dst)
            }
            // Spec 2.x / i-want 322: `union { ... }` write/read. Both
            // boil down to a typed cast against the synthetic `__data`
            // slot — `cast_to` handles `WidestPrim` (int/float cast)
            // and same-size `ByteArray` (`bitcast`). Different-size
            // `ByteArray` cases (struct-in-union, oversize fields) are
            // gated up front by `union_storage_strategy` diagnostics.
            HirExprKind::UnionWrite {
                from_ty,
                storage_ty,
                value,
                ..
            } => {
                let raw = self.lower_expr_to_operand(value);
                let src_ty = lower_ty_in(from_ty, self.module);
                let dst_ty = lower_ty_in(storage_ty, self.module);
                self.union_bits(raw, &src_ty, &dst_ty)
            }
            HirExprKind::UnionRead {
                target,
                storage_ty,
                field_ty,
                ..
            } => {
                let target_op = self.lower_expr_to_operand(target);
                let Operand::Copy(target_local) = target_op else {
                    return Operand::Const(ConstVal::Unit);
                };
                let storage_mir_ty = lower_ty_in(storage_ty, self.module);
                let storage_local = self.fresh_local(storage_mir_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: storage_local,
                    rvalue: RValue::FieldRead {
                        target: Operand::Copy(target_local),
                        index: 0,
                        field_ty: storage_mir_ty.clone(),
                    },
                });
                let dst_ty = lower_ty_in(field_ty, self.module);
                self.union_bits(Operand::Copy(storage_local), &storage_mir_ty, &dst_ty)
            }
            HirExprKind::TupleField {
                target,
                index,
                field_ty,
            } => {
                let target_op = self.lower_expr_to_operand(target);
                let mir_field_ty = lower_ty_in(field_ty, self.module);
                let dst = self.fresh_local(mir_field_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::FieldRead {
                        target: target_op,
                        index: *index,
                        field_ty: mir_field_ty,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::WithField {
                target,
                field_index,
                value,
                ..
            } => {
                let struct_ty = lower_ty_in(&target.ty, self.module);
                let source = self.lower_expr_to_operand(target);
                let new_value = self.lower_expr_to_operand(value);
                let dst = self.fresh_local(struct_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::WithField {
                        source,
                        struct_ty,
                        index: *field_index,
                        value: new_value,
                    },
                });
                Operand::Copy(dst)
            }
            HirExprKind::FieldRead {
                target,
                field_index,
                field_ty,
                ..
            } => {
                let target_op = self.lower_expr_to_operand(target);
                let mir_field_ty = lower_ty_in(field_ty, self.module);
                let dst = self.fresh_local(mir_field_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::FieldRead {
                        target: target_op,
                        index: *field_index,
                        field_ty: mir_field_ty,
                    },
                });
                Operand::Copy(dst)
            }
        }
    }

    fn lower_match(
        &mut self,
        scrutinee: &HirExpr,
        arms: &[HirMatchArm],
        result_hir_ty: &HirTy,
    ) -> Operand {
        // Materialize the scrutinee into a stack-slotted local so each
        // arm can compare against it without recomputing.
        let scrut_op = self.lower_expr_to_operand(scrutinee);
        let scrut_ty = lower_ty_in(&scrutinee.ty, self.module);
        let scrut_local = match scrut_op {
            Operand::Copy(id) => id,
            other @ Operand::Const(_) => {
                let id = self.fresh_local(scrut_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: id,
                    rvalue: RValue::Use(other),
                });
                id
            }
        };

        let merge_bb = self.new_block();
        let mir_result_ty = lower_ty_in(result_hir_ty, self.module);
        let value_producing = !matches!(mir_result_ty, MirTy::Unit);
        let merge_param = if value_producing {
            Some(self.add_block_param(merge_bb, mir_result_ty))
        } else {
            None
        };

        let mut any_arm_to_merge = false;
        for arm in arms {
            let arm_body_bb = self.new_block();
            let next_bb = self.new_block();

            self.lower_pattern_test(&arm.pat, scrut_local, &scrut_ty, arm_body_bb, next_bb);

            // Body block: bind any pattern locals, then evaluate the
            // guard (if any), then run the body.
            self.current = arm_body_bb;
            self.bind_pattern(&arm.pat, scrut_local);
            if let Some(guard) = &arm.guard {
                let cond = self.lower_expr_to_operand(guard);
                let pass_bb = self.new_block();
                self.terminate(Terminator::If {
                    cond,
                    then_bb: pass_bb,
                    then_args: Vec::new(),
                    else_bb: next_bb,
                    else_args: Vec::new(),
                });
                self.current = pass_bb;
            }
            let body_val = self.lower_expr_to_operand(&arm.body);
            // Skip the goto-merge if the body fully diverged (e.g. all
            // its sub-branches `return`-ed out).
            if !self.terminated.contains(&self.current.0) {
                let args = if value_producing {
                    vec![body_val]
                } else {
                    Vec::new()
                };
                self.terminate(Terminator::Goto {
                    target: merge_bb,
                    args,
                });
                any_arm_to_merge = true;
            }

            self.current = next_bb;
        }
        // No arm can reach the merge — the merge is unreachable, so
        // mark it terminated to prevent dead-code emission landing
        // there from downstream lowering.
        if !any_arm_to_merge {
            self.terminated.insert(merge_bb.0);
        }

        // No arm matched: spec leaves this as a runtime error / undefined
        // behaviour for now. Mark as unreachable so optimisation can
        // collapse it. Exhaustiveness checking in the type checker will
        // turn this into a compile-time error later.
        self.terminate(Terminator::Unreachable);

        self.current = merge_bb;
        match merge_param {
            Some(p) => Operand::Copy(p),
            None => Operand::Const(ConstVal::Unit),
        }
    }

    /// Emit the comparison(s) that decide whether an arm matches. On a
    /// match the fall-through reaches `arm_body_bb`; otherwise it
    /// reaches `next_bb`. The current block is fully terminated.
    fn lower_pattern_test(
        &mut self,
        pat: &HirPattern,
        scrut_local: LocalId,
        scrut_ty: &MirTy,
        arm_body_bb: BlockId,
        next_bb: BlockId,
    ) {
        match pat {
            HirPattern::Wildcard | HirPattern::Binding { .. } => {
                self.terminate(Terminator::Goto {
                    target: arm_body_bb,
                    args: Vec::new(),
                });
            }
            HirPattern::At { sub, .. } => {
                self.lower_pattern_test(sub, scrut_local, scrut_ty, arm_body_bb, next_bb);
            }
            HirPattern::Literal { value, prim } => {
                let cond = self.build_eq(scrut_local, value, *prim);
                self.terminate(Terminator::If {
                    cond,
                    then_bb: arm_body_bb,
                    then_args: Vec::new(),
                    else_bb: next_bb,
                    else_args: Vec::new(),
                });
            }
            HirPattern::Range {
                start,
                end,
                inclusive,
                prim,
            } => {
                // Check `lo <= x` and (`x < hi` | `x <= hi`); each open
                // bound is omitted. Empty range matches everything.
                if start.is_none() && end.is_none() {
                    self.terminate(Terminator::Goto {
                        target: arm_body_bb,
                        args: Vec::new(),
                    });
                    return;
                }
                let bounds: Vec<(PrimOp, &ConstVal)> = {
                    let mut v: Vec<(PrimOp, &ConstVal)> = Vec::new();
                    if let Some(s) = start {
                        v.push((PrimOp::Le, s));
                    }
                    if let Some(e) = end {
                        v.push((if *inclusive { PrimOp::Ge } else { PrimOp::Gt }, e));
                    }
                    v
                };
                for (i, (op, value)) in bounds.iter().enumerate() {
                    let success_bb = if i + 1 < bounds.len() {
                        self.new_block()
                    } else {
                        arm_body_bb
                    };
                    // For start: `lo <= x`  ↔  `x >= lo` is the same; we
                    // mirror by computing `value <op> x` for the bound.
                    // Concretely: bound `(Le, lo)`  ↔  `lo <= x`,
                    //            bound `(Gt, hi)`  ↔  `hi >  x`,
                    //            bound `(Ge, hi)`  ↔  `hi >= x`.
                    let cond = self.build_cmp_const_op(*op, value, scrut_local, *prim);
                    self.terminate(Terminator::If {
                        cond,
                        then_bb: success_bb,
                        then_args: Vec::new(),
                        else_bb: next_bb,
                        else_args: Vec::new(),
                    });
                    if i + 1 < bounds.len() {
                        self.current = success_bb;
                    }
                }
            }
            HirPattern::Or(alts) => {
                // Chain: first alt that matches lands in a per-alt success
                // block, runs its own `bind_pattern`, then jumps to the arm
                // body. Spec 3.11.4 — each alt's bindings reach the arm body
                // through the same shared locals (allocated in HIR lowering).
                for (i, alt) in alts.iter().enumerate() {
                    let local_next = if i + 1 < alts.len() {
                        self.new_block()
                    } else {
                        next_bb
                    };
                    let alt_success_bb = self.new_block();
                    self.lower_pattern_test(alt, scrut_local, scrut_ty, alt_success_bb, local_next);
                    self.current = alt_success_bb;
                    self.bind_pattern(alt, scrut_local);
                    self.terminate(Terminator::Goto {
                        target: arm_body_bb,
                        args: Vec::new(),
                    });
                    if i + 1 < alts.len() {
                        self.current = local_next;
                    }
                }
            }
            HirPattern::Struct { fields, .. } => {
                let MirTy::Struct(_, elem_tys) = scrut_ty.clone() else {
                    self.terminate(Terminator::Goto {
                        target: arm_body_bb,
                        args: Vec::new(),
                    });
                    return;
                };
                if fields.is_empty() {
                    self.terminate(Terminator::Goto {
                        target: arm_body_bb,
                        args: Vec::new(),
                    });
                    return;
                }
                // Pull each named field once, then chain its sub-test.
                let mut field_locals: Vec<(LocalId, MirTy)> = Vec::with_capacity(fields.len());
                for (idx, _) in fields {
                    let Some(field_ty) = elem_tys.get(*idx as usize).cloned() else {
                        self.terminate(Terminator::Goto {
                            target: next_bb,
                            args: Vec::new(),
                        });
                        return;
                    };
                    let local = self.fresh_local(field_ty.clone());
                    self.push_stmt(Statement::Assign {
                        target: local,
                        rvalue: RValue::FieldRead {
                            target: Operand::Copy(scrut_local),
                            index: *idx,
                            field_ty: field_ty.clone(),
                        },
                    });
                    field_locals.push((local, field_ty));
                }
                for (i, (_, sub_pat)) in fields.iter().enumerate() {
                    let success_bb = if i + 1 < fields.len() {
                        self.new_block()
                    } else {
                        arm_body_bb
                    };
                    let (local, ty) = field_locals[i].clone();
                    self.lower_pattern_test(sub_pat, local, &ty, success_bb, next_bb);
                    if i + 1 < fields.len() {
                        self.current = success_bb;
                    }
                }
            }
            HirPattern::Tuple(sub_pats) => {
                let MirTy::Tuple(elem_tys) = scrut_ty.clone() else {
                    self.terminate(Terminator::Goto {
                        target: arm_body_bb,
                        args: Vec::new(),
                    });
                    return;
                };
                if sub_pats.len() != elem_tys.len() {
                    self.terminate(Terminator::Goto {
                        target: next_bb,
                        args: Vec::new(),
                    });
                    return;
                }
                // Extract each tuple element into a fresh local up front so
                // sub-tests can run against scalar scrutinees.
                let mut elem_locals: Vec<LocalId> = Vec::with_capacity(elem_tys.len());
                for (i, elem_ty) in elem_tys.iter().enumerate() {
                    let local = self.fresh_local(elem_ty.clone());
                    self.push_stmt(Statement::Assign {
                        target: local,
                        rvalue: RValue::FieldRead {
                            target: Operand::Copy(scrut_local),
                            index: u32::try_from(i).expect("tuple index overflow"),
                            field_ty: elem_ty.clone(),
                        },
                    });
                    elem_locals.push(local);
                }
                // Chain sub-tests: any failure jumps to next_bb; the final
                // success falls through to arm_body_bb.
                for (i, sub_pat) in sub_pats.iter().enumerate() {
                    let success_bb = if i + 1 < sub_pats.len() {
                        self.new_block()
                    } else {
                        arm_body_bb
                    };
                    self.lower_pattern_test(
                        sub_pat,
                        elem_locals[i],
                        &elem_tys[i],
                        success_bb,
                        next_bb,
                    );
                    if i + 1 < sub_pats.len() {
                        self.current = success_bb;
                    }
                }
            }
            HirPattern::EnumVariant { variant_index, .. }
            | HirPattern::SumVariant { variant_index, .. } => {
                // Tag check; payload binding (if any) happens in
                // `bind_pattern` after the arm body block is selected.
                let value = ConstVal::Int {
                    value: i128::from(*variant_index),
                    ty: IrPrimTy::I32,
                };
                let tag = self.extract_tag(scrut_local, scrut_ty);
                let cond = self.build_eq_op(tag, &value, IrPrimTy::I32);
                // Refutable payload sub-patterns (`E::A(1)`) are tested
                // after the tag.
                let nested = match pat {
                    HirPattern::EnumVariant {
                        enum_id,
                        variant_index,
                        args,
                    } if args.iter().any(|a| !a.is_irrefutable()) => {
                        Some((*enum_id, *variant_index, args))
                    }
                    _ => None,
                };
                let tag_ok_bb = if nested.is_some() {
                    self.new_block()
                } else {
                    arm_body_bb
                };
                self.terminate(Terminator::If {
                    cond,
                    then_bb: tag_ok_bb,
                    then_args: Vec::new(),
                    else_bb: next_bb,
                    else_args: Vec::new(),
                });
                let Some((enum_id, variant_index, args)) = nested else {
                    return;
                };
                self.current = tag_ok_bb;
                let Some(arg_locals) =
                    self.variant_arg_locals(enum_id, variant_index, scrut_local, args.len())
                else {
                    self.terminate(Terminator::Goto {
                        target: arm_body_bb,
                        args: Vec::new(),
                    });
                    return;
                };
                for (i, (sub_pat, (local, ty))) in args.iter().zip(&arg_locals).enumerate() {
                    let success_bb = if i + 1 < args.len() {
                        self.new_block()
                    } else {
                        arm_body_bb
                    };
                    self.lower_pattern_test(sub_pat, *local, ty, success_bb, next_bb);
                    if i + 1 < args.len() {
                        self.current = success_bb;
                    }
                }
            }
        }
    }

    // Read the tag from an enum scrutinee. Payload-less enums are i32
    // outright; payload-bearing enums are `(i32, payload)` tuples.
    fn extract_tag(&mut self, scrut: LocalId, scrut_ty: &MirTy) -> Operand {
        match scrut_ty {
            MirTy::Tuple(parts) if parts.len() == 2 => {
                let dst = self.fresh_local(parts[0].clone());
                self.push_stmt(Statement::Assign {
                    target: dst,
                    rvalue: RValue::FieldRead {
                        target: Operand::Copy(scrut),
                        index: 0,
                        field_ty: parts[0].clone(),
                    },
                });
                Operand::Copy(dst)
            }
            _ => Operand::Copy(scrut),
        }
    }

    // No-op when the types match; otherwise insert a `Cast` rvalue
    // (zext / sext / trunc selected by codegen from from_ty/to_ty).
    fn cast_to(&mut self, source: Operand, from_ty: &MirTy, to_ty: &MirTy) -> Operand {
        if from_ty == to_ty {
            return source;
        }
        let dst = self.fresh_local(to_ty.clone());
        self.push_stmt(Statement::Assign {
            target: dst,
            rvalue: RValue::Cast {
                source,
                from_ty: from_ty.clone(),
                to_ty: to_ty.clone(),
            },
        });
        Operand::Copy(dst)
    }

    /// Call a function value `{code, env}`: `code(env, args..)`.
    fn call_fn_value(&mut self, callee: Operand, args: &[HirExpr], ret_ty: &HirTy) -> RValue {
        let arg_tys: Vec<MirTy> = args
            .iter()
            .map(|a| lower_ty_in(&a.ty, self.module))
            .collect();
        let ret = lower_ty_in(ret_ty, self.module);
        let code_t = code_ty(arg_tys.clone(), ret.clone());
        let code = self.fresh_local(code_t);
        self.push_stmt(Statement::Assign {
            target: code,
            rvalue: RValue::FieldRead {
                target: callee.clone(),
                index: 0,
                field_ty: code_ty(arg_tys.clone(), ret.clone()),
            },
        });
        let env = self.fresh_local(MirTy::GcRef);
        self.push_stmt(Statement::Assign {
            target: env,
            rvalue: RValue::FieldRead {
                target: callee,
                index: 1,
                field_ty: MirTy::GcRef,
            },
        });
        let mut call_args = vec![Operand::Copy(env)];
        call_args.extend(args.iter().map(|a| self.lower_expr_to_operand(a)));
        let mut all_tys = vec![MirTy::GcRef];
        all_tys.extend(arg_tys);
        RValue::CallIndirect {
            callee: Operand::Copy(code),
            args: call_args,
            arg_tys: all_tys,
            ret_ty: ret,
        }
    }

    /// The MIR type of one enum variant's own payload (before it is
    /// moved into the enum's shared slot).
    /// Each payload argument of enum variant `scrut` in its own local
    /// (`None` when the variant carries no matching payload).
    fn variant_arg_locals(
        &mut self,
        enum_id: rokc_hir::EnumId,
        variant_index: u32,
        scrut: LocalId,
        n_args: usize,
    ) -> Option<Vec<(LocalId, MirTy)>> {
        if n_args == 0 {
            return None;
        }
        let MirTy::Tuple(parts) = self.locals[scrut.0 as usize].ty.clone() else {
            return None;
        };
        if parts.len() != 2 {
            return None;
        }
        let unified_ty = parts[1].clone();
        let payload = self.fresh_local(unified_ty.clone());
        self.push_stmt(Statement::Assign {
            target: payload,
            rvalue: RValue::FieldRead {
                target: Operand::Copy(scrut),
                index: 1,
                field_ty: unified_ty.clone(),
            },
        });
        let variant_ty = self.variant_payload_ty(enum_id, variant_index);
        let v = self.payload_cast(Operand::Copy(payload), &unified_ty, &variant_ty);
        let local = match v {
            Operand::Copy(l) => l,
            c @ Operand::Const(_) => {
                let l = self.fresh_local(variant_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: l,
                    rvalue: RValue::Use(c),
                });
                l
            }
        };
        // A named-field variant's payload is the tuple of its fields,
        // even with one field.
        let named = !self.module.enums[enum_id.0 as usize].variants[variant_index as usize]
            .named_fields
            .is_empty();
        if n_args == 1 && !named {
            return Some(vec![(local, variant_ty)]);
        }
        let MirTy::Tuple(field_tys) = variant_ty else {
            return None;
        };
        if field_tys.len() != n_args {
            return None;
        }
        Some(
            field_tys
                .into_iter()
                .enumerate()
                .map(|(i, field_ty)| {
                    let elem = self.fresh_local(field_ty.clone());
                    self.push_stmt(Statement::Assign {
                        target: elem,
                        rvalue: RValue::FieldRead {
                            target: Operand::Copy(local),
                            index: u32::try_from(i).expect("field index overflow"),
                            field_ty: field_ty.clone(),
                        },
                    });
                    (elem, field_ty)
                })
                .collect(),
        )
    }

    fn variant_payload_ty(&self, enum_id: rokc_hir::EnumId, variant_index: u32) -> MirTy {
        self.module.enums[enum_id.0 as usize].variants[variant_index as usize]
            .payload_ty
            .as_ref()
            .map_or(MirTy::Unit, |t| lower_ty_in(t, self.module))
    }

    /// Spec 2.5.2: a union field write / read reinterprets bits (an
    /// `f32` written and read as `i32` is its IEEE bits, not `1`).
    fn union_bits(&mut self, source: Operand, from_ty: &MirTy, to_ty: &MirTy) -> Operand {
        if matches!((from_ty, to_ty), (MirTy::Prim(_), MirTy::Prim(_))) {
            self.payload_cast(source, from_ty, to_ty)
        } else {
            self.cast_to(source, from_ty, to_ty)
        }
    }

    /// Move a value into / out of a shared payload slot, keeping bits.
    fn payload_cast(&mut self, source: Operand, from_ty: &MirTy, to_ty: &MirTy) -> Operand {
        if from_ty == to_ty {
            return source;
        }
        let dst = self.fresh_local(to_ty.clone());
        self.push_stmt(Statement::Assign {
            target: dst,
            rvalue: RValue::Bitcast {
                source,
                from_ty: from_ty.clone(),
                to_ty: to_ty.clone(),
            },
        });
        Operand::Copy(dst)
    }

    fn build_eq_op(&mut self, lhs: Operand, value: &ConstVal, prim: IrPrimTy) -> Operand {
        let result = self.fresh_local(MirTy::Prim(IrPrimTy::Bool));
        self.push_stmt(Statement::Assign {
            target: result,
            rvalue: RValue::BinOp {
                op: PrimOp::Eq,
                op_ty: MirTy::Prim(prim),
                lhs,
                rhs: Operand::Const(value.clone()),
            },
        });
        Operand::Copy(result)
    }

    /// Emit `value <op> scrut` as a primitive compare returning bool.
    /// Used by range tests where the bound is the constant.
    fn build_cmp_const_op(
        &mut self,
        op: PrimOp,
        value: &ConstVal,
        scrut: LocalId,
        prim: PrimTy,
    ) -> Operand {
        let result = self.fresh_local(MirTy::Prim(PrimTy::Bool));
        self.push_stmt(Statement::Assign {
            target: result,
            rvalue: RValue::BinOp {
                op,
                op_ty: MirTy::Prim(prim),
                lhs: Operand::Const(value.clone()),
                rhs: Operand::Copy(scrut),
            },
        });
        Operand::Copy(result)
    }

    fn build_eq(&mut self, scrut: LocalId, value: &ConstVal, prim: PrimTy) -> Operand {
        let result = self.fresh_local(MirTy::Prim(PrimTy::Bool));
        self.push_stmt(Statement::Assign {
            target: result,
            rvalue: RValue::BinOp {
                op: PrimOp::Eq,
                op_ty: MirTy::Prim(prim),
                lhs: Operand::Copy(scrut),
                rhs: Operand::Const(value.clone()),
            },
        });
        Operand::Copy(result)
    }

    /// Walk a pattern that successfully matched and store the scrutinee
    /// into any binding locals.
    fn bind_pattern(&mut self, pat: &HirPattern, scrut: LocalId) {
        match pat {
            HirPattern::Binding { local, .. } => {
                self.push_stmt(Statement::Assign {
                    target: *local,
                    rvalue: RValue::Use(Operand::Copy(scrut)),
                });
            }
            HirPattern::At { local, sub, .. } => {
                self.push_stmt(Statement::Assign {
                    target: *local,
                    rvalue: RValue::Use(Operand::Copy(scrut)),
                });
                self.bind_pattern(sub, scrut);
            }
            HirPattern::Or(alts) => {
                // Bindings inside or-patterns require consistency across
                // alternatives — not yet supported.
                let _ = alts;
            }
            HirPattern::EnumVariant {
                enum_id,
                variant_index,
                args,
            } => {
                let Some(arg_locals) =
                    self.variant_arg_locals(*enum_id, *variant_index, scrut, args.len())
                else {
                    return;
                };
                for (sub_pat, (local, _)) in args.iter().zip(arg_locals) {
                    self.bind_pattern(sub_pat, local);
                }
            }
            HirPattern::SumVariant { binder, sum_ty, .. } => {
                let Some(local) = binder else { return };
                let scrut_ty = self.locals[scrut.0 as usize].ty.clone();
                let MirTy::Tuple(parts) = &scrut_ty else {
                    return;
                };
                if parts.len() != 2 {
                    return;
                }
                let payload_ty = parts[1].clone();
                let payload = self.fresh_local(payload_ty.clone());
                self.push_stmt(Statement::Assign {
                    target: payload,
                    rvalue: RValue::FieldRead {
                        target: Operand::Copy(scrut),
                        index: 1,
                        field_ty: payload_ty.clone(),
                    },
                });
                // Spec 변경점 1019: heterogeneous sums store every variant
                // through the widest payload slot. When the binder's
                // declared type is narrower (e.g. `v: i32` against an
                // `i32 | f64` sum), narrow the extracted payload back.
                let bind_ty = self.locals[local.0 as usize].ty.clone();
                if matches!(sum_ty, HirTy::AnyTrait(_)) {
                    self.push_stmt(Statement::Assign {
                        target: *local,
                        rvalue: RValue::HeapLoad {
                            ptr: Operand::Copy(payload),
                            ty: bind_ty,
                        },
                    });
                    return;
                }
                let v = self.payload_cast(Operand::Copy(payload), &payload_ty, &bind_ty);
                self.push_stmt(Statement::Assign {
                    target: *local,
                    rvalue: RValue::Use(v),
                });
            }
            HirPattern::Tuple(sub_pats) => {
                let scrut_ty = self.locals[scrut.0 as usize].ty.clone();
                let MirTy::Tuple(elem_tys) = scrut_ty else {
                    return;
                };
                if sub_pats.len() != elem_tys.len() {
                    return;
                }
                for (i, sub_pat) in sub_pats.iter().enumerate() {
                    if matches!(
                        sub_pat,
                        HirPattern::Wildcard
                            | HirPattern::Literal { .. }
                            | HirPattern::Range { .. }
                    ) {
                        continue;
                    }
                    let elem_local = self.fresh_local(elem_tys[i].clone());
                    self.push_stmt(Statement::Assign {
                        target: elem_local,
                        rvalue: RValue::FieldRead {
                            target: Operand::Copy(scrut),
                            index: u32::try_from(i).expect("tuple index overflow"),
                            field_ty: elem_tys[i].clone(),
                        },
                    });
                    self.bind_pattern(sub_pat, elem_local);
                }
            }
            HirPattern::Struct { fields, .. } => {
                let scrut_ty = self.locals[scrut.0 as usize].ty.clone();
                let MirTy::Struct(_, elem_tys) = scrut_ty else {
                    return;
                };
                for (idx, sub_pat) in fields {
                    if matches!(
                        sub_pat,
                        HirPattern::Wildcard
                            | HirPattern::Literal { .. }
                            | HirPattern::Range { .. }
                    ) {
                        continue;
                    }
                    let Some(field_ty) = elem_tys.get(*idx as usize).cloned() else {
                        continue;
                    };
                    let elem_local = self.fresh_local(field_ty.clone());
                    self.push_stmt(Statement::Assign {
                        target: elem_local,
                        rvalue: RValue::FieldRead {
                            target: Operand::Copy(scrut),
                            index: *idx,
                            field_ty,
                        },
                    });
                    self.bind_pattern(sub_pat, elem_local);
                }
            }
            HirPattern::Wildcard | HirPattern::Literal { .. } | HirPattern::Range { .. } => {}
        }
    }

    /// `for i in 0..len { array[i] = value }`.
    fn fill_array(&mut self, array: LocalId, elem_ty: &MirTy, value: Operand, len: u32) {
        let usize_ty = MirTy::Prim(PrimTy::Usize);
        let i = self.fresh_local(usize_ty.clone());
        let int = |v: i128| {
            Operand::Const(ConstVal::Int {
                value: v,
                ty: PrimTy::Usize,
            })
        };
        self.push_stmt(Statement::Assign {
            target: i,
            rvalue: RValue::Use(int(0)),
        });
        let header_bb = self.new_block();
        let body_bb = self.new_block();
        let exit_bb = self.new_block();
        self.terminate(Terminator::Goto {
            target: header_bb,
            args: Vec::new(),
        });
        self.current = header_bb;
        let more = self.fresh_local(MirTy::Prim(PrimTy::Bool));
        self.push_stmt(Statement::Assign {
            target: more,
            rvalue: RValue::BinOp {
                op: PrimOp::Lt,
                op_ty: usize_ty.clone(),
                lhs: Operand::Copy(i),
                rhs: int(i128::from(len)),
            },
        });
        self.terminate(Terminator::If {
            cond: Operand::Copy(more),
            then_bb: body_bb,
            then_args: Vec::new(),
            else_bb: exit_bb,
            else_args: Vec::new(),
        });
        self.current = body_bb;
        self.push_stmt(Statement::ArrayWrite {
            array,
            index: Operand::Copy(i),
            value,
            elem_ty: elem_ty.clone(),
            len,
        });
        self.push_stmt(Statement::Assign {
            target: i,
            rvalue: RValue::BinOp {
                op: PrimOp::Add,
                op_ty: usize_ty,
                lhs: Operand::Copy(i),
                rhs: int(1),
            },
        });
        self.terminate(Terminator::Goto {
            target: header_bb,
            args: Vec::new(),
        });
        self.current = exit_bb;
    }

    fn lower_while(&mut self, label: Option<String>, cond: &HirExpr, body: &HirBlock) -> Operand {
        let header_bb = self.new_block();
        let body_bb = self.new_block();
        let exit_bb = self.new_block();

        // Jump from the current block into the header.
        self.terminate(Terminator::Goto {
            target: header_bb,
            args: Vec::new(),
        });

        // Header: evaluate the condition, branch to body or exit.
        self.current = header_bb;
        let cond_op = self.lower_expr_to_operand(cond);
        self.terminate(Terminator::If {
            cond: cond_op,
            then_bb: body_bb,
            then_args: Vec::new(),
            else_bb: exit_bb,
            else_args: Vec::new(),
        });

        // Body — `lower_block_value` so a trailing expression doesn't
        // get rewritten into a synthetic `func.return`.
        self.current = body_bb;
        self.loop_stack.push(LoopFrame {
            continue_bb: header_bb,
            break_bb: exit_bb,
            break_param: None,
            label,
            is_loop: true,
        });
        let (_value, diverged) = self.lower_block_value(body);
        self.loop_stack.pop();
        if !diverged {
            self.terminate(Terminator::Goto {
                target: header_bb,
                args: Vec::new(),
            });
        }

        self.current = exit_bb;
        Operand::Const(ConstVal::Unit)
    }

    fn lower_loop(&mut self, label: Option<String>, body: &HirBlock, result_ty: &HirTy) -> Operand {
        let body_bb = self.new_block();
        let exit_bb = self.new_block();

        let mir_ty = lower_ty_in(result_ty, self.module);
        let break_param = if matches!(mir_ty, MirTy::Unit) {
            None
        } else {
            Some(self.add_block_param(exit_bb, mir_ty))
        };

        self.terminate(Terminator::Goto {
            target: body_bb,
            args: Vec::new(),
        });

        self.current = body_bb;
        self.loop_stack.push(LoopFrame {
            continue_bb: body_bb,
            break_bb: exit_bb,
            break_param,
            label,
            is_loop: true,
        });
        let (_value, diverged) = self.lower_block_value(body);
        self.loop_stack.pop();
        if !diverged {
            self.terminate(Terminator::Goto {
                target: body_bb,
                args: Vec::new(),
            });
        }

        self.current = exit_bb;
        match break_param {
            Some(p) => Operand::Copy(p),
            None => Operand::Const(ConstVal::Unit),
        }
    }

    fn lower_if(
        &mut self,
        cond: &HirExpr,
        then_block: &HirBlock,
        else_branch: Option<&HirExpr>,
        result_hir_ty: &HirTy,
    ) -> Operand {
        let result_ty = lower_ty_in(result_hir_ty, self.module);
        let has_else = else_branch.is_some();
        let value_producing = has_else && !matches!(result_ty, MirTy::Unit);

        let then_bb = self.new_block();
        let merge_bb = self.new_block();
        let else_bb = if has_else { self.new_block() } else { merge_bb };

        // Merge block param holds the unified result when both branches
        // produce a value.
        let merge_param = if value_producing {
            Some(self.add_block_param(merge_bb, result_ty))
        } else {
            None
        };

        // Condition lives in the current block.
        let cond_op = self.lower_expr_to_operand(cond);
        self.terminate(Terminator::If {
            cond: cond_op,
            then_bb,
            then_args: Vec::new(),
            else_bb,
            else_args: Vec::new(),
        });

        // Then arm.
        self.current = then_bb;
        let (then_value, then_diverged) = self.lower_block_value(then_block);
        if !then_diverged {
            let then_args = if value_producing {
                vec![then_value]
            } else {
                Vec::new()
            };
            self.terminate(Terminator::Goto {
                target: merge_bb,
                args: then_args,
            });
        }
        let then_to_merge = !then_diverged;

        // Else arm.
        let mut else_to_merge = !has_else;
        if let Some(else_e) = else_branch {
            self.current = else_bb;
            let else_value = self.lower_expr_to_operand(else_e);
            // The else expression itself may have diverged via a return
            // or break inside; check whether the current block is still
            // live before adding a goto-merge edge.
            if !self.terminated.contains(&self.current.0) {
                let else_args = if value_producing {
                    vec![else_value]
                } else {
                    Vec::new()
                };
                self.terminate(Terminator::Goto {
                    target: merge_bb,
                    args: else_args,
                });
                else_to_merge = true;
            }
        }

        // If neither arm reaches the merge, the merge is unreachable —
        // mark it terminated so a downstream `terminate` won't write a
        // dead edge into it.
        if !then_to_merge && !else_to_merge {
            self.terminated.insert(merge_bb.0);
        }

        self.current = merge_bb;
        match merge_param {
            Some(p) => Operand::Copy(p),
            None => Operand::Const(ConstVal::Unit),
        }
    }
}

// Helper trait used in print.rs to keep the surface noise out of lib.rs.
#[allow(dead_code)]
trait HirTyExt {
    fn is_unit(&self) -> bool;
}

impl HirTyExt for HirTy {
    fn is_unit(&self) -> bool {
        matches!(self, Self::Unit)
    }
}

// A zero ConstVal of the given primitive shape; used as a dummy
// payload for unit variants of payload-bearing enums.
const fn zero_const(ty: &MirTy) -> ConstVal {
    match ty {
        MirTy::Prim(p) if p.is_int() => ConstVal::Int { value: 0, ty: *p },
        MirTy::Prim(IrPrimTy::Bool) => ConstVal::Bool(false),
        MirTy::Prim(p) if p.is_float() => ConstVal::Float { bits: 0, ty: *p },
        _ => ConstVal::Unit,
    }
}

//! Codegen on hand-built MIR: the MLIR each construct becomes.

use rokc_diagnostic::Span;
use rokc_ir_common::{BlockId, FnFacts, FunctionId, LocalId, PrimOp, PrimTy};
use rokc_mir::{
    BasicBlock, LocalDecl, MirFunction, MirModule, MirTy, Operand, RValue, Statement, Terminator,
};

use crate::{CodegenOptions, codegen};

const I32: MirTy = MirTy::Prim(PrimTy::I32);

const fn local(i: u32, ty: MirTy) -> LocalDecl {
    LocalDecl {
        id: LocalId(i),
        name: None,
        ty,
    }
}

const fn block(id: u32, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock {
        id: BlockId(id),
        params: vec![],
        stmts,
        terminator,
    }
}

const fn copy(i: u32) -> Operand {
    Operand::Copy(LocalId(i))
}

/// `fn <name>(_0: ty, _1: ty) -> ret`, locals from `_2` typed `more`.
fn function(
    id: u32,
    name: &str,
    (ty, ret): (&MirTy, &MirTy),
    more: Vec<MirTy>,
    blocks: Vec<BasicBlock>,
) -> MirFunction {
    let mut locals = vec![local(0, ty.clone()), local(1, ty.clone())];
    locals.extend(more.into_iter().zip(2..).map(|(t, i)| local(i, t)));
    MirFunction {
        id: FunctionId(id),
        def_id: None,
        name: name.into(),
        facts: FnFacts::default(),
        params: vec![LocalId(0), LocalId(1)],
        locals,
        blocks,
        param_tys: vec![ty.clone(), ty.clone()],
        ret_ty: ret.clone(),
        span: Span::default(),
    }
}

/// `fn f(_0: ty, _1: ty) -> ty { _2 = _0 <op> _1; return _2 }`
fn binary(op: PrimOp, ty: &MirTy) -> MirFunction {
    let stmts = vec![Statement::Assign {
        target: LocalId(2),
        rvalue: RValue::BinOp {
            op,
            op_ty: ty.clone(),
            lhs: copy(0),
            rhs: copy(1),
        },
    }];
    let ret = Terminator::Return(Some(copy(2)));
    function(
        0,
        "f",
        (ty, ty),
        vec![ty.clone()],
        vec![block(0, stmts, ret)],
    )
}

fn mlir(functions: Vec<MirFunction>, overflow_checks: bool) -> String {
    let module = MirModule {
        functions,
        ..MirModule::default()
    };
    let opts = CodegenOptions {
        overflow_checks,
        ..CodegenOptions::default()
    };
    codegen(&module, &opts).expect("codegen").text
}

/// The body of function `name` (symbol `_Y<hash>__<name>_`).
fn body<'a>(text: &'a str, name: &str) -> &'a str {
    let head = text
        .find(&format!("__{name}_("))
        .and_then(|at| text[..at].rfind("func.func"))
        .unwrap_or_else(|| panic!("no function {name} in\n{text}"));
    let rest = &text[head..];
    &rest[..rest.find("\n  }").unwrap_or(rest.len())]
}

/// The symbol of function `name`.
fn symbol<'a>(text: &'a str, name: &str) -> &'a str {
    let end = text.find(&format!("__{name}_(")).expect("the function") + name.len() + 3;
    let start = text[..end].rfind('@').expect("a symbol") + 1;
    &text[start..end]
}

#[test]
fn checked_add_panics_on_overflow() {
    let checked = mlir(vec![binary(PrimOp::Add, &I32)], true);
    let f = body(&checked, "f");
    assert!(f.contains("arith.addi"), "{f}");
    assert!(
        f.contains("cf.cond_br") && f.contains("@rok_panic_at"),
        "{f}"
    );
    let plain = mlir(vec![binary(PrimOp::Add, &I32)], false);
    let f = body(&plain, "f");
    assert!(f.contains("arith.addi"), "{f}");
    assert!(!f.contains("rok_panic_at"), "{f}");
}

/// Division checks its divisor, and `MIN / -1` when signed, with or
/// without overflow checks.
#[test]
fn division_checks_follow_signedness() {
    let text = mlir(vec![binary(PrimOp::Div, &I32)], false);
    let f = body(&text, "f");
    assert!(f.contains("arith.divsi"), "{f}");
    assert_eq!(f.matches("@rok_panic_at").count(), 2, "{f}");
    assert!(text.contains("\"attempt to divide by zero\\00\""));
    assert!(text.contains("\"attempt to divide with overflow\\00\""));
    let text = mlir(vec![binary(PrimOp::Div, &MirTy::Prim(PrimTy::U32))], false);
    let f = body(&text, "f");
    assert!(f.contains("arith.divui"), "{f}");
    assert_eq!(f.matches("@rok_panic_at").count(), 1, "{f}");
}

#[test]
fn branches_and_calls() {
    // g(_0, _1) = if _0 < _1 { f(_0, _1) } else { _1 }
    let cmp = vec![Statement::Assign {
        target: LocalId(2),
        rvalue: RValue::BinOp {
            op: PrimOp::Lt,
            op_ty: I32,
            lhs: copy(0),
            rhs: copy(1),
        },
    }];
    let call = vec![Statement::Assign {
        target: LocalId(3),
        rvalue: RValue::Call {
            callee: FunctionId(0),
            args: vec![copy(0), copy(1)],
            ret_ty: I32,
        },
    }];
    let branch = Terminator::If {
        cond: copy(2),
        then_bb: BlockId(1),
        then_args: vec![],
        else_bb: BlockId(2),
        else_args: vec![],
    };
    let g = function(
        1,
        "g",
        (&I32, &I32),
        vec![MirTy::Prim(PrimTy::Bool), I32],
        vec![
            block(0, cmp, branch),
            block(1, call, Terminator::Return(Some(copy(3)))),
            block(2, vec![], Terminator::Return(Some(copy(1)))),
        ],
    );
    let text = mlir(vec![binary(PrimOp::Add, &I32), g], false);
    let g = body(&text, "g");
    assert!(g.contains("arith.cmpi slt"), "{g}");
    assert!(g.contains("cf.cond_br"), "{g}");
    let f = symbol(&text, "f");
    assert!(g.contains(&format!("call @{f}(")), "{g}");
}

/// A function's symbol depends on its package hash, not on its id.
#[test]
fn symbols_are_stable_across_ids() {
    let a = mlir(vec![binary(PrimOp::Sub, &I32)], false);
    let mut moved = binary(PrimOp::Sub, &I32);
    moved.id = FunctionId(7);
    let b = mlir(vec![moved], false);
    assert_eq!(symbol(&a, "f"), symbol(&b, "f"));
    assert!(symbol(&a, "f").starts_with("_Y"));
}

/// `-g`: a subprogram named by the rok path at the function's line, in
/// a unit that says whether the build is optimized.
#[test]
fn debug_info_describes_the_function() {
    let file = rokc_diagnostic::register_file("dbg.rok".into(), "\nfn f() {}\n".into());
    let mut f = binary(PrimOp::Add, &I32);
    f.span = Span {
        file,
        line: 2,
        col: 1,
        ..Span::default()
    };
    let module = MirModule {
        functions: vec![f],
        ..MirModule::default()
    };
    let text = |optimized| {
        let opts = CodegenOptions {
            debug: true,
            optimized,
            ..CodegenOptions::default()
        };
        codegen(&module, &opts).expect("codegen").text
    };
    let plain = text(false);
    assert!(plain.contains("isOptimized = false"), "{plain}");
    assert!(plain.contains("name = \"f\""), "{plain}");
    assert!(plain.contains("line = 2, scopeLine = 2"), "{plain}");
    assert!(text(true).contains("isOptimized = true"));
}

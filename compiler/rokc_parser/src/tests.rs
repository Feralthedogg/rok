//! Parser unit tests focused on the surface grammar.

use rokc_ast::{AttrArg, AttrBody, ExprKind, Item, Literal, StmtKind};
use rokc_lexer::Lexer;
use rokc_scanner::{ScannerTables, scan_source};

use crate::{Assoc, Fixity, OpEntry, PrecTable, collect_prec_table, parse_program};

fn parse(src: &str) -> rokc_ast::Program {
    parse_with(src, &PrecTable::new())
}

fn parse_with(src: &str, prec: &PrecTable) -> rokc_ast::Program {
    let tables = ScannerTables::new();
    let lexer = Lexer::new(src, &tables, "test");
    let (tokens, lex_diags) = lexer.lex_all();
    assert!(lex_diags.is_empty(), "lex diagnostics: {lex_diags:?}");
    let (program, diags) = parse_program(&tokens, prec, "test");
    assert!(diags.is_empty(), "parse diagnostics: {diags:?}");
    program
}

/// Build a precedence table with the standard arithmetic / comparison
/// operators for tests.
fn arith_prec_table() -> PrecTable {
    let mut t = PrecTable::new();
    for (sym, prec, m) in [
        ("+", 7u32, "add"),
        ("-", 7, "sub"),
        ("*", 8, "mul"),
        ("/", 8, "div"),
        ("%", 8, "rem"),
    ] {
        t.insert(OpEntry {
            symbol: sym.into(),
            fixity: Fixity::Infix,
            prec,
            assoc: Assoc::Left,
            method_name: m.into(),
        });
    }
    for (sym, m) in [
        ("==", "eq"), ("!=", "ne"), ("<", "lt"), (">", "gt"), ("<=", "le"), (">=", "ge"),
    ] {
        t.insert(OpEntry {
            symbol: sym.into(),
            fixity: Fixity::Infix,
            prec: 6,
            assoc: Assoc::None,
            method_name: m.into(),
        });
    }
    t.insert(OpEntry {
        symbol: "&&".into(),
        fixity: Fixity::Infix,
        prec: 5,
        assoc: Assoc::Left,
        method_name: "logical_and".into(),
    });
    t.insert(OpEntry {
        symbol: "||".into(),
        fixity: Fixity::Infix,
        prec: 4,
        assoc: Assoc::Left,
        method_name: "logical_or".into(),
    });
    t.insert(OpEntry {
        symbol: "-".into(),
        fixity: Fixity::Prefix,
        prec: 11,
        assoc: Assoc::Right,
        method_name: "neg".into(),
    });
    t.insert(OpEntry {
        symbol: "!".into(),
        fixity: Fixity::Prefix,
        prec: 11,
        assoc: Assoc::Right,
        method_name: "not".into(),
    });
    t
}

#[test]
fn attr_flag_only() {
    let p = parse("#[inline] fn f() { }");
    let Item::Fn(f) = &p.items[0] else { panic!() };
    assert_eq!(f.attrs.len(), 1);
    assert_eq!(f.attrs[0].name(), "inline");
    assert!(matches!(f.attrs[0].body, AttrBody::Empty));
}

#[test]
fn attr_args_mixed() {
    let p = parse(r#"#[infix("+", prec = 9, left)] fn f() { }"#);
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let attr = &f.attrs[0];
    assert_eq!(attr.name(), "infix");
    let AttrBody::Args(args) = &attr.body else { panic!() };
    assert_eq!(args.len(), 3);
    assert!(matches!(&args[0], AttrArg::Lit(Literal::Str(s)) if s == "+"));
    assert!(matches!(&args[1], AttrArg::KeyValue(k, Literal::Int(v)) if k == "prec" && v == "9"));
    assert!(matches!(&args[2], AttrArg::Word(w) if w == "left"));
}

#[test]
fn attr_value_form() {
    let p = parse(r#"#[doc = "hi"] fn f() { }"#);
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let attr = &f.attrs[0];
    assert_eq!(attr.name(), "doc");
    assert!(matches!(&attr.body, AttrBody::Value(Literal::Str(s)) if s == "hi"));
}

#[test]
fn attr_nested() {
    let p = parse(r#"#[cfg(target_os = "linux")] fn f() { }"#);
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let attr = &f.attrs[0];
    assert_eq!(attr.name(), "cfg");
    let AttrBody::Args(args) = &attr.body else { panic!() };
    assert!(matches!(
        &args[0],
        AttrArg::KeyValue(k, Literal::Str(v)) if k == "target_os" && v == "linux"
    ));
}

#[test]
fn attr_nested_call() {
    let p = parse(r#"#[cfg_attr(unix, link(name = "m"))] fn f() { }"#);
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let AttrBody::Args(args) = &f.attrs[0].body else { panic!() };
    assert_eq!(args.len(), 2);
    let AttrArg::Nested { path, body } = &args[1] else { panic!() };
    assert_eq!(path, &vec!["link".to_owned()]);
    let AttrBody::Args(inner) = body.as_ref() else { panic!() };
    assert!(matches!(
        &inner[0],
        AttrArg::KeyValue(k, Literal::Str(v)) if k == "name" && v == "m"
    ));
}

/// Strip the wrapping `fn t() { return EXPR; }` and return the EXPR AST.
fn return_expr(p: &rokc_ast::Program) -> &rokc_ast::Expr {
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let body = f.body.as_ref().unwrap();
    let StmtKind::Return(Some(e)) = &body.stmts[0].kind else { panic!() };
    e
}

#[test]
fn pratt_left_assoc() {
    // `a - b - c` parses as `(a - b) - c`.
    let p = parse_with(
        "fn t() { return a - b - c; }",
        &arith_prec_table(),
    );
    let e = return_expr(&p);
    let ExprKind::OpInfix { op, lhs, rhs: _ } = &e.kind else { panic!() };
    assert_eq!(op, "-");
    let ExprKind::OpInfix { op: inner_op, .. } = &lhs.kind else {
        panic!("expected nested infix on lhs")
    };
    assert_eq!(inner_op, "-");
}

#[test]
fn pratt_precedence_mul_over_add() {
    // `a + b * c` parses as `a + (b * c)`.
    let p = parse_with("fn t() { return a + b * c; }", &arith_prec_table());
    let e = return_expr(&p);
    let ExprKind::OpInfix { op, rhs, .. } = &e.kind else { panic!() };
    assert_eq!(op, "+");
    let ExprKind::OpInfix { op: rop, .. } = &rhs.kind else {
        panic!("expected `*` on rhs")
    };
    assert_eq!(rop, "*");
}

#[test]
fn pratt_prefix_neg() {
    // `-a + b` parses as `(-a) + b`, not `-(a + b)`.
    let p = parse_with("fn t() { return -a + b; }", &arith_prec_table());
    let e = return_expr(&p);
    let ExprKind::OpInfix { op, lhs, .. } = &e.kind else { panic!() };
    assert_eq!(op, "+");
    let ExprKind::OpPrefix { op: pop, .. } = &lhs.kind else {
        panic!("expected unary `-` on lhs")
    };
    assert_eq!(pop, "-");
}

#[test]
fn pratt_unknown_op_stops() {
    // With an empty PrecTable, `1 + 2` cannot be parsed beyond the literal
    // primary. The trailing `+ 2;` should produce parse diagnostics.
    let tables = ScannerTables::new();
    let src = "fn t() { return 1 + 2; }";
    let lexer = Lexer::new(src, &tables, "test");
    let (tokens, _) = lexer.lex_all();
    let prec = PrecTable::new();
    let (_p, diags) = parse_program(&tokens, &prec, "test");
    assert!(!diags.is_empty(), "expected parse error on `+` without PrecTable entry");
}

#[test]
fn trait_with_self_method() {
    let p = parse(
        r#"trait Add<Rhs> {
            type Output;
            #[infix("+", prec = 7, left)]
            fn add(self, rhs: Rhs) -> Output;
        }"#,
    );
    let Item::Trait(t) = &p.items[0] else { panic!("expected trait, got {:?}", p.items) };
    assert_eq!(t.name, "Add");
    assert_eq!(t.items.len(), 2, "trait items: {:?}", t.items);
}

#[test]
fn two_traits_back_to_back() {
    // Use the real scanner pass — the driver does the same. Empty
    // `ScannerTables` masks bugs that depend on TypeIdent promotion.
    let src = r#"trait Add<Rhs> {
    type Output;
    #[infix("+", prec = 7, left)]
    fn add(self, rhs: Rhs) -> Output;
}

trait Sub<Rhs> {
    type Output;
    #[infix("-", prec = 7, left)]
    fn sub(self, rhs: Rhs) -> Output;
}
"#;
    let tables = scan_source(src);
    let lexer = Lexer::new(src, &tables, "test");
    let (tokens, _) = lexer.lex_all();
    let prec = PrecTable::new();
    let (program, diags) = parse_program(&tokens, &prec, "test");
    assert!(diags.is_empty(), "parse diagnostics: {diags:#?}");
    assert_eq!(program.items.len(), 2);
}

#[test]
fn collect_prec_from_trait_attrs() {
    let src = r#"trait Add<Rhs> {
    type Output;
    #[infix("+", prec = 7, left)]
    fn add(self, rhs: Rhs) -> Output;
}

trait Cmp<Rhs> {
    #[infix("<=", prec = 4, none)]
    #[infix("≤", prec = 4, none)]
    fn le(self, rhs: Rhs) -> bool;
}

trait Neg {
    type Output;
    #[prefix("-", prec = 11)]
    fn neg(self) -> Output;
}
"#;
    let tables = scan_source(src);
    let lexer = Lexer::new(src, &tables, "test");
    let (tokens, _) = lexer.lex_all();
    let empty = PrecTable::new();
    let (program, diags) = parse_program(&tokens, &empty, "test");
    assert!(diags.is_empty(), "{diags:#?}");
    let (table, errs) = collect_prec_table(&program);
    assert!(errs.is_empty(), "{errs:#?}");

    let plus = table.lookup("+", Fixity::Infix).expect("`+` registered");
    assert_eq!(plus.prec, 7);
    assert!(matches!(plus.assoc, Assoc::Left));

    // `<=` and `≤` share the same method, both registered.
    assert!(table.lookup("<=", Fixity::Infix).is_some());
    assert!(table.lookup("≤", Fixity::Infix).is_some());

    let neg = table.lookup("-", Fixity::Prefix).expect("prefix `-`");
    assert_eq!(neg.prec, 11);
}

#[test]
fn visibility_qualifiers_are_contextual() {
    use rokc_core::Visibility;
    // `sub` is reserved only inside `pub(...)`; a method named `sub` and
    // a `pub(sub)` qualifier coexist on the same item.
    let p = parse(
        r#"trait Sub<Rhs> {
            #[infix("-", prec = 7, left)]
            pub(sub) fn sub(self, rhs: Rhs) -> Self;
        }"#,
    );
    let Item::Trait(t) = &p.items[0] else { panic!() };
    let rokc_ast::TraitItem::Method(m) = &t.items[0] else { panic!() };
    assert_eq!(m.name, "sub");
    assert_eq!(m.vis, Visibility::Sub);
}

#[test]
fn attr_derive_words() {
    let p = parse("#[derive(Display, Clone, Eq)] fn f() { }");
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let AttrBody::Args(args) = &f.attrs[0].body else { panic!() };
    assert_eq!(args.len(), 3);
    for (a, expected) in args.iter().zip(["Display", "Clone", "Eq"]) {
        assert!(matches!(a, AttrArg::Word(w) if w == expected));
    }
}

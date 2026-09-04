//! Parser unit tests focused on the surface grammar.

use rokc_ast::{AttrArg, AttrBody, ExprKind, Item, Literal, StmtKind};
use rokc_lexer::Lexer;

use crate::{Assoc, Fixity, OpEntry, PrecTable, collect_prec_table, parse_program};

fn parse(src: &str) -> rokc_ast::Program {
    parse_with(src, &PrecTable::new())
}

fn parse_with(src: &str, prec: &PrecTable) -> rokc_ast::Program {
    let lexer = Lexer::new(src, "test");
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
        ("|", 3u32, "bitor"),
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
            trait_name: String::new(),
        });
    }
    for (sym, m) in [
        ("==", "eq"),
        ("!=", "ne"),
        ("<", "lt"),
        (">", "gt"),
        ("<=", "le"),
        (">=", "ge"),
    ] {
        t.insert(OpEntry {
            symbol: sym.into(),
            fixity: Fixity::Infix,
            prec: 6,
            assoc: Assoc::None,
            method_name: m.into(),
            trait_name: String::new(),
        });
    }
    t.insert(OpEntry {
        symbol: "&&".into(),
        fixity: Fixity::Infix,
        prec: 5,
        assoc: Assoc::Left,
        method_name: "logical_and".into(),
        trait_name: String::new(),
    });
    t.insert(OpEntry {
        symbol: "||".into(),
        fixity: Fixity::Infix,
        prec: 4,
        assoc: Assoc::Left,
        method_name: "logical_or".into(),
        trait_name: String::new(),
    });
    t.insert(OpEntry {
        symbol: "-".into(),
        fixity: Fixity::Prefix,
        prec: 11,
        assoc: Assoc::Right,
        method_name: "neg".into(),
        trait_name: String::new(),
    });
    t.insert(OpEntry {
        symbol: "!".into(),
        fixity: Fixity::Prefix,
        prec: 11,
        assoc: Assoc::Right,
        method_name: "not".into(),
        trait_name: String::new(),
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
    let AttrBody::Args(args) = &attr.body else {
        panic!()
    };
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
    let AttrBody::Args(args) = &attr.body else {
        panic!()
    };
    assert!(matches!(
        &args[0],
        AttrArg::KeyValue(k, Literal::Str(v)) if k == "target_os" && v == "linux"
    ));
}

#[test]
fn attr_nested_call() {
    let p = parse(r#"#[cfg_attr(unix, link(name = "m"))] fn f() { }"#);
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let AttrBody::Args(args) = &f.attrs[0].body else {
        panic!()
    };
    assert_eq!(args.len(), 2);
    let AttrArg::Nested { path, body } = &args[1] else {
        panic!()
    };
    assert_eq!(path, &vec!["link".to_owned()]);
    let AttrBody::Args(inner) = body.as_ref() else {
        panic!()
    };
    assert!(matches!(
        &inner[0],
        AttrArg::KeyValue(k, Literal::Str(v)) if k == "name" && v == "m"
    ));
}

/// Strip the wrapping `fn t() { return EXPR; }` and return the EXPR AST.
fn return_expr(p: &rokc_ast::Program) -> &rokc_ast::Expr {
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let body = f.body.as_ref().unwrap();
    let StmtKind::Return(Some(e)) = &body.stmts[0].kind else {
        panic!()
    };
    e
}

#[test]
fn pratt_left_assoc() {
    // `a - b - c` parses as `(a - b) - c`.
    let p = parse_with("fn t() { return a - b - c; }", &arith_prec_table());
    let e = return_expr(&p);
    let ExprKind::OpInfix { op, lhs, rhs: _ } = &e.kind else {
        panic!()
    };
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
    let ExprKind::OpInfix { op, rhs, .. } = &e.kind else {
        panic!()
    };
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
    let ExprKind::OpInfix { op, lhs, .. } = &e.kind else {
        panic!()
    };
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
    let src = "fn t() { return 1 + 2; }";
    let lexer = Lexer::new(src, "test");
    let (tokens, _) = lexer.lex_all();
    let prec = PrecTable::new();
    let (_p, diags) = parse_program(&tokens, &prec, "test");
    assert!(
        !diags.is_empty(),
        "expected parse error on `+` without PrecTable entry"
    );
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
    let Item::Trait(t) = &p.items[0] else {
        panic!("expected trait, got {:?}", p.items)
    };
    assert_eq!(t.name, "Add");
    assert_eq!(t.items.len(), 2, "trait items: {:?}", t.items);
}

#[test]
fn two_traits_back_to_back() {
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
    let lexer = Lexer::new(src, "test");
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
    let lexer = Lexer::new(src, "test");
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
    let Item::Trait(t) = &p.items[0] else {
        panic!()
    };
    let rokc_ast::TraitItem::Method(m) = &t.items[0] else {
        panic!()
    };
    assert_eq!(m.name, "sub");
    assert_eq!(m.vis, Visibility::Sub);
}

#[test]
fn attr_derive_words() {
    let p = parse("#[derive(Display, Clone, Eq)] fn f() { }");
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let AttrBody::Args(args) = &f.attrs[0].body else {
        panic!()
    };
    assert_eq!(args.len(), 3);
    for (a, expected) in args.iter().zip(["Display", "Clone", "Eq"]) {
        assert!(matches!(a, AttrArg::Word(w) if w == expected));
    }
}

#[test]
fn struct_literal_decided_by_syntax_not_prescan() {
    // Regression: the old scanner registered `size` (from the comment)
    // as a type name, so `Foo { size: 1 }` became a trailing closure.
    let p = parse(
        "// compute the struct size\nstruct Foo { size: i32; }\n\
         fn f() { let v = Foo { size: 1 }; }",
    );
    let Item::Fn(f) = &p.items[1] else { panic!() };
    let StmtKind::Let { init, .. } = &f.body.as_ref().unwrap().stmts[0].kind else {
        panic!()
    };
    assert!(
        matches!(init.kind, ExprKind::StructInit { .. }),
        "{:?}",
        init.kind
    );
}

#[test]
fn struct_patterns_without_capitalisation() {
    // Non-ASCII / lower-case / imported type names work in patterns.
    let p = parse(
        "fn f(p: 점) { let 점 { x, y } = p; let m::pt { a, .. } = q; \
         match p { 점 { x, .. } => x, _ => 0 } }",
    );
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let stmts = &f.body.as_ref().unwrap().stmts;
    assert!(
        matches!(&stmts[0].kind, StmtKind::LetStruct { path, .. } if path.segments[0].name == "점")
    );
    assert!(matches!(&stmts[1].kind, StmtKind::LetStruct { path, .. } if path.segments.len() == 2));
    let m = f.body.as_ref().unwrap().trailing.as_ref().unwrap();
    let ExprKind::Match { arms, .. } = &m.kind else {
        panic!()
    };
    assert!(matches!(
        arms[0].pat.kind,
        rokc_ast::PatternKind::Struct { .. }
    ));
}

#[test]
fn catch_binding_followed_by_block() {
    let p = parse("fn f() { try { g(); } catch e { h(e); } }");
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let e = f.body.as_ref().unwrap().trailing.as_ref().unwrap();
    let ExprKind::Try { catches, .. } = &e.kind else {
        panic!("{e:?}")
    };
    assert!(matches!(
        catches[0].pat.kind,
        rokc_ast::PatternKind::Binding { .. }
    ));
}

/// All lexer + parser diagnostics for `src` (arith precedence table).
fn diags_of(src: &str) -> Vec<String> {
    let (tokens, mut diags) = Lexer::new(src, "test").lex_all();
    let (_p, parse_diags) = parse_program(&tokens, &arith_prec_table(), "test");
    diags.extend(parse_diags);
    diags.into_iter().map(|d| d.message).collect()
}

fn assert_rejected(src: &str, needle: &str) {
    let d = diags_of(src);
    assert!(
        d.iter().any(|m| m.contains(needle)),
        "{src:?}: expected `{needle}` in {d:#?}"
    );
}

fn fn_param_ty(p: &rokc_ast::Program) -> &rokc_ast::Ty {
    let Item::Fn(f) = &p.items[0] else { panic!() };
    f.params[0].ty.as_ref().unwrap()
}

#[test]
fn cast_target_does_not_swallow_lt_or_pipe() {
    let p = parse_with("fn t() { return a as i64 < b; }", &arith_prec_table());
    let ExprKind::OpInfix { op, lhs, .. } = &return_expr(&p).kind else {
        panic!()
    };
    assert_eq!(op, "<");
    assert!(matches!(lhs.kind, ExprKind::Cast(..)));

    let p = parse_with("fn t() { return a as i32 | b; }", &arith_prec_table());
    let ExprKind::OpInfix { op, lhs, .. } = &return_expr(&p).kind else {
        panic!()
    };
    assert_eq!(op, "|");
    assert!(matches!(lhs.kind, ExprKind::Cast(..)));

    // Real generic args and parenthesised sums still work.
    let p = parse_with("fn t() { return a as Foo<Bar<i32>>; }", &arith_prec_table());
    let ExprKind::Cast(_, ty) = &return_expr(&p).kind else {
        panic!()
    };
    let rokc_ast::TyKind::Path(path) = &ty.kind else {
        panic!()
    };
    assert_eq!(path.segments[0].generics.len(), 1);
    let p = parse_with("fn t() { return a as (i32 | none); }", &arith_prec_table());
    let ExprKind::Cast(_, ty) = &return_expr(&p).kind else {
        panic!()
    };
    assert!(matches!(ty.kind, rokc_ast::TyKind::Sum(_)));
}

#[test]
fn unclosed_generic_args_rejected() {
    assert_rejected("fn f(x: Vec<i32) { }", "expected `>`");
    assert_rejected("struct S<T { x: T; }", "expected `>`");
}

#[test]
fn split_closing_angles() {
    let p = parse("fn f(x: Vec<Vec<i32>>, y: A<B<C<D>>>) { let z: Vec<i32>= x; }");
    let Item::Fn(f) = &p.items[0] else { panic!() };
    assert_eq!(f.params.len(), 2);
}

#[test]
fn impl_trait_alias_generics_and_where_are_kept() {
    let p = parse(
        "impl<T: Add<T>> Pair<T> where T: Copy, T::Out: Show { } \
         trait Ord<R>: Eq + Cmp<R> where R: Copy { } \
         type Map<K, V = Vec<K>> = Tree<K, V>; \
         fn g<T>(x: T) -> T where T: Clone + Copy { x }",
    );
    let Item::Impl(imp) = &p.items[0] else {
        panic!()
    };
    assert_eq!(imp.generics.params.len(), 1);
    assert_eq!(imp.where_clause.len(), 2);
    let Item::Trait(tr) = &p.items[1] else {
        panic!()
    };
    assert_eq!(tr.generics.params.len(), 1);
    assert_eq!(tr.supertraits.len(), 2);
    assert_eq!(tr.where_clause.len(), 1);
    let Item::TypeAlias(alias) = &p.items[2] else {
        panic!()
    };
    assert_eq!(alias.generics.params.len(), 2);
    let Item::Fn(func) = &p.items[3] else {
        panic!()
    };
    assert_eq!(func.where_clause[0].bounds.len(), 2);
}

#[test]
fn paren_type_grouping_vs_tuple() {
    use rokc_ast::TyKind;
    assert!(matches!(
        fn_param_ty(&parse("fn f(x: (i32)) { }")).kind,
        TyKind::Path(_)
    ));
    assert!(
        matches!(&fn_param_ty(&parse("fn f(x: (i32,)) { }")).kind, TyKind::Tuple(v) if v.len() == 1)
    );
    assert!(
        matches!(&fn_param_ty(&parse("fn f(x: ()) { }")).kind, TyKind::Tuple(v) if v.is_empty())
    );
    // `fn() -> A | B` is `(fn() -> A) | B` (spec 2.1.10).
    let p = parse("fn f(x: fn(i32) -> i32 | none) { }");
    let ty = fn_param_ty(&p);
    let TyKind::Sum(v) = &ty.kind else {
        panic!("{ty:?}")
    };
    assert!(matches!(v[0].kind, TyKind::Fn(..)));
}

#[test]
fn tuple_field_indices() {
    let p = parse("fn t() { return x.0.1; }");
    let ExprKind::TupleField(inner, 1) = &return_expr(&p).kind else {
        panic!()
    };
    assert!(matches!(inner.kind, ExprKind::TupleField(_, 0)));
    for bad in ["x.1u8", "x.0x1", "x.1_0", "x.01", "x.1e1", "x?.1u8"] {
        assert_rejected(
            &format!("fn t() {{ return {bad}; }}"),
            "invalid tuple field index",
        );
    }
}

#[test]
fn deep_nesting_is_a_diagnostic_not_a_crash() {
    // The depth cap must trip before the parser thread's stack does.
    let n = 5000;
    for src in [
        format!("fn f() {{ return {}1{}; }}", "(".repeat(n), ")".repeat(n)),
        format!("fn f() {}{}", "{".repeat(n), "}".repeat(n)),
        format!("fn f(x: {}i32{}) {{ }}", "(".repeat(n), ",)".repeat(n)),
        format!(
            "fn f() {{ match x {{ {}_{} => 1 }} }}",
            "(".repeat(n),
            ")".repeat(n)
        ),
        format!("fn f() {{ return {}1; }}", "-".repeat(n)),
    ] {
        assert_rejected(&src, "nesting too deep");
    }
}

#[test]
fn open_ranges() {
    let range = |src: &str| {
        let p = parse_with(&format!("fn t() {{ return {src}; }}"), &arith_prec_table());
        let ExprKind::Range {
            start,
            end,
            inclusive,
        } = return_expr(&p).kind.clone()
        else {
            panic!("{src}")
        };
        (start.is_some(), end.is_some(), inclusive)
    };
    assert_eq!(range("a..b"), (true, true, false));
    assert_eq!(range("..b"), (false, true, false));
    assert_eq!(range("a.."), (true, false, false));
    assert_eq!(range(".."), (false, false, false));
    assert_eq!(range("..=b + 1"), (false, true, true));
    let p = parse("fn t() { for i in 0.. { } f(xs[1..], ..ys); }");
    assert!(matches!(p.items[0], Item::Fn(_)));
    assert_rejected("fn t() { return a..b..c; }", "cannot be chained");
}

#[test]
fn unsafe_raw_strings_and_unsupported_forms() {
    let p = parse(
        r##"unsafe fn f() { let s = r#"a"b"#; unsafe { g(); } } extern "C" { unsafe fn h(); }"##,
    );
    assert_eq!(p.items.len(), 2);
    let Item::Fn(f) = &p.items[0] else { panic!() };
    let StmtKind::Let { init, .. } = &f.body.as_ref().unwrap().stmts[0].kind else {
        panic!()
    };
    assert!(matches!(&init.kind, ExprKind::Literal(Literal::RawStr(s)) if s == "a\"b"));
    assert_rejected("async unsafe fn f() { }", "expected `fn`");
    assert_rejected(
        r#"fn f() { let s = f"x = {x}"; }"#,
        "f-string literals (spec 1.7.3) are not yet supported",
    );
    assert_rejected(
        "fn f() { using x = g() { x } }",
        "`using` expressions (spec 3.17) are not yet supported",
    );
}

#[test]
fn recovery_reports_each_mistake_once() {
    let src = "fn a() { let q = (1 + ; let r = 2; if r > 1 { f( } else { 3 }; return r; }\n\
               fn b( -> i32 { return 1; }\n\
               enum E { A { 1: i32 } }\n\
               fn c() { if (x + ) { } }\n\
               fn d() { let p = P { x: 1 }; return ~p; }";
    let d = diags_of(src);
    assert_eq!(d.len(), 6, "{d:#?}");
    assert!(d.iter().any(|m| m.contains("field name expected")));
    // `~` has no `#[prefix]` entry in the test table.
    assert!(
        d.iter()
            .any(|m| m.contains("prefix operator `~` is not defined"))
    );
    // No flag leaked out of the failed `if` head in `c`: the struct
    // literal in `d` still parses (no extra diagnostic for it).
}

#[test]
fn unsupported_impl_const_and_extern_static() {
    let d = diags_of(
        "impl S { const N: i32 = 1; fn f() { } } extern \"C\" { static mut X: i32; fn g(); }",
    );
    assert_eq!(d.len(), 2, "{d:#?}");
    assert!(d[0].contains("not yet supported") && d[1].contains("not yet supported"));
}

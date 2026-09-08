use crate::{Document, Value, parse};

fn get<'a>(t: &'a crate::Table, path: &str) -> &'a Value {
    let mut v: Option<&Value> = None;
    let mut t = t;
    for k in path.split('.') {
        let item = t.get(k).unwrap_or_else(|| panic!("no `{k}` in {path}"));
        v = Some(&item.value);
        if let Value::Table(sub) = &item.value {
            t = sub;
        }
    }
    v.unwrap()
}

fn err(src: &str) -> String {
    parse(src).expect_err(src).message
}

#[test]
fn scalars() {
    let t = parse(
        r#"
int1 = +99
int2 = -17
int3 = 1_000
hex = 0xDEAD_beef
oct = 0o755
bin = 0b1101
f1 = 3.25
f2 = -0.01
f3 = 5e+22
f4 = 6.626e-34
f5 = 224_617.445_991_228
inf1 = -inf
b = true
s = "tab\there \u00e9 \U0001F600 \"q\""
l = 'C:\Users\x'
odt = 1979-05-27T07:32:00-07:00
odt2 = 1979-05-27 07:32:00.999Z
ldt = 1979-05-27T00:32:00
ld = 1979-05-27
lt = 07:32:00.5
"#,
    )
    .unwrap();
    assert_eq!(get(&t, "int1"), &Value::Integer(99));
    assert_eq!(get(&t, "int2"), &Value::Integer(-17));
    assert_eq!(get(&t, "int3"), &Value::Integer(1000));
    assert_eq!(get(&t, "hex"), &Value::Integer(0xDEAD_BEEF));
    assert_eq!(get(&t, "oct"), &Value::Integer(0o755));
    assert_eq!(get(&t, "bin"), &Value::Integer(13));
    assert_eq!(get(&t, "f1"), &Value::Float(3.25));
    assert_eq!(get(&t, "f3"), &Value::Float(5e22));
    assert_eq!(get(&t, "f5"), &Value::Float(224_617.445_991_228));
    assert_eq!(get(&t, "inf1"), &Value::Float(f64::NEG_INFINITY));
    assert_eq!(get(&t, "b"), &Value::Boolean(true));
    assert_eq!(
        get(&t, "s").as_str(),
        Some("tab\there \u{e9} \u{1F600} \"q\"")
    );
    assert_eq!(get(&t, "l").as_str(), Some(r"C:\Users\x"));
    assert_eq!(
        get(&t, "odt2"),
        &Value::Datetime("1979-05-27 07:32:00.999Z".into())
    );
    assert!(matches!(get(&t, "ld"), Value::Datetime(_)));
    assert!(matches!(get(&t, "lt"), Value::Datetime(_)));
}

#[test]
fn multiline_strings() {
    let t = parse(
        "a = \"\"\"\nRoses\r\nViolets\"\"\"\nb = \"\"\"\\\n   The quick \\\n\n  fox\"\"\"\nc = \"\"\"\"\"quotes\"\"\"\"\"\nd = '''\nraw \\n ''text'''''\n",
    )
    .unwrap();
    assert_eq!(get(&t, "a").as_str(), Some("Roses\nViolets"));
    assert_eq!(get(&t, "b").as_str(), Some("The quick fox"));
    assert_eq!(get(&t, "c").as_str(), Some("\"\"quotes\"\""));
    assert_eq!(get(&t, "d").as_str(), Some("raw \\n ''text''"));
}

#[test]
fn tables_and_keys() {
    let t = parse(
        r#"
"quoted key" = 1
'lit.key' = 2
a.b.c = 3
a . "d" = 4
[x.y.z]   # implicit x and x.y
w = 1
[x]       # defining an implicit table later is fine
v = 2
[fruit]
apple.color = "red"
[fruit.apple.texture]   # a sub-table of a dotted table
smooth = true
[[products]]
name = "Hammer"
[[products]]
[products.dims]
h = 1
[[products]]
name = "Nail"
inline = { a = 1, b.c = [1, "two", { x = [] }], }
"#
        .replace(", }", " }")
        .as_str(),
    )
    .unwrap();
    assert_eq!(get(&t, "quoted key"), &Value::Integer(1));
    assert_eq!(t.get("lit.key").unwrap().value, Value::Integer(2));
    assert_eq!(get(&t, "a.b.c"), &Value::Integer(3));
    assert_eq!(get(&t, "a.d"), &Value::Integer(4));
    assert_eq!(get(&t, "x.y.z.w"), &Value::Integer(1));
    assert_eq!(get(&t, "x.v"), &Value::Integer(2));
    assert_eq!(get(&t, "fruit.apple.texture.smooth"), &Value::Boolean(true));
    let products = get(&t, "products").as_array().unwrap();
    assert_eq!(products.len(), 3);
    let second = products[1].value.as_table().unwrap();
    assert!(second.get("name").is_none());
    assert!(second.get("dims").is_some());
    let third = products[2].value.as_table().unwrap();
    let inline = third.get("inline").unwrap().value.as_table().unwrap();
    let c = inline.get("b").unwrap().value.as_table().unwrap().get("c");
    assert_eq!(c.unwrap().value.as_array().unwrap().len(), 3);
}

#[test]
fn invalid_documents() {
    for (src, want) in [
        ("a = 1\na = 2", "duplicate key `a`"),
        ("[a]\n[a]", "already defined"),
        ("a.b = 1\n[a]", "already defined"),
        ("[fruit]\napple.color = 1\n[fruit.apple]", "already defined"),
        ("[a.b.c]\nz = 9\n[a]\nb.c.t = 1", "dotted keys cannot add"),
        (
            "[product]\ntype.name = 1\ntype = { x = 1 }",
            "duplicate key",
        ),
        ("a = { b = 1 }\n[a.c]", "inline table"),
        ("a = { b = 1 }\na.c = 2", "dotted keys cannot add"),
        ("a = [1]\n[[a]]", "static array"),
        ("[a]\n[[a]]", "already defined as a table"),
        ("[[a]]\n[a]", "array of tables"),
        ("a = 1\n[a.b]", "already a integer"),
        ("a = { b = 1, }", "trailing comma"),
        ("a = { b = 1,\n c = 2 }", "on one line"),
        ("a = 01", "invalid number"),
        ("a = 1__0", "invalid number"),
        ("a = _1", "expected a value"),
        ("a = 1.", "invalid number"),
        ("a = .5", "invalid number"),
        ("a = +0x10", "invalid number"),
        ("a = 1979-02-29", "invalid date"),
        ("a = 25:00:00", "invalid date"),
        ("a = \"\\x\"", "unknown escape"),
        ("a = \"\\uD800\"", "not a Unicode scalar"),
        ("a = \"open", "unterminated"),
        ("a = \"x\ny\"", "newline in a single-line string"),
        ("a = '''x''''''", "too many quotes"),
        ("a = 1 b = 2", "end of the line"),
        ("a = bare", "strings need quotes"),
        ("= 1", "expected a key"),
        ("a = [1 2]", "expected `,` or `]`"),
        ("[a\nb = 1", "close the table header"),
        ("\"\"\"k\"\"\" = 1", "multi-line"),
        ("a = 1 # \u{1}", "control character"),
    ] {
        let msg = err(src);
        assert!(msg.contains(want), "{src:?}: {msg:?} lacks {want:?}");
    }
}

#[test]
fn error_spans_render() {
    let src = "[package]\nname = \"x\"\nname = \"y\"\n";
    let e = parse(src).unwrap_err();
    assert_eq!(&src[e.span.start..e.span.end], "name");
    let r = e.render(src, "Rok.toml");
    assert!(
        r.starts_with("Rok.toml:3:1: error: duplicate key `name`"),
        "{r}"
    );
    assert!(r.ends_with("| ^^^^"), "{r}");
}

#[test]
fn editing_keeps_formatting() {
    let src = "# my package\n[package]\nname = \"app\"   # the name\n\n[deps]\n# local\nfoo = { path = \"../foo\" }  # keep me\n\n[dev-deps]\n";
    let mut d = Document::parse(src).unwrap();
    // Add after the last entry of the section, before the blank line.
    d.set(&["deps"], "bar", "{ git = \"u\" }").unwrap();
    assert_eq!(
        d.text(),
        src.replace("# keep me\n", "# keep me\nbar = { git = \"u\" }\n")
    );
    // Replace a value in place: the comment after it stays.
    d.set(&["deps"], "foo", "{ path = \"../foo2\" }").unwrap();
    assert!(
        d.text()
            .contains("foo = { path = \"../foo2\" }  # keep me\n")
    );
    // A section with no entries yet.
    d.set(&["dev-deps"], "t", "{ path = \"t\" }").unwrap();
    assert!(
        d.text().ends_with("[dev-deps]\nt = { path = \"t\" }\n"),
        "{}",
        d.text()
    );
    // A missing section is appended.
    d.set(&["x", "y z"], "k", "1").unwrap();
    assert!(d.text().ends_with("\n[x.\"y z\"]\nk = 1\n"), "{}", d.text());
    // Removal drops just that line.
    assert!(d.remove(&["deps"], "foo").unwrap());
    assert!(!d.remove(&["deps"], "foo").unwrap());
    assert!(d.text().contains("[deps]\n# local\nbar = "), "{}", d.text());
    assert!(
        d.table()
            .get("deps")
            .unwrap()
            .value
            .as_table()
            .unwrap()
            .get("foo")
            .is_none()
    );
    // Dotted at the root counts as `[package] version`.
    let mut d = Document::parse("package.name = \"a\"").unwrap();
    d.set(&["package"], "name", "\"b\"").unwrap();
    assert_eq!(d.text(), "package.name = \"b\"");
    d.set(&[], "top", "true").unwrap();
    assert_eq!(d.text(), "package.name = \"b\"\ntop = true\n");
    // An edit that would make invalid TOML fails and changes nothing.
    let mut d = Document::parse("deps = { a = 1 }\n").unwrap();
    assert!(d.set(&["deps"], "b", "2").is_err());
    assert_eq!(d.text(), "deps = { a = 1 }\n");
}

#[test]
fn format_roundtrip() {
    let src = "a = { s = \"q\\\"\\n\", n = [1, 2.5, true], e = {} }\n";
    let t = parse(src).unwrap();
    let text = format!("a = {}\n", crate::format_value(&t.get("a").unwrap().value));
    assert_eq!(parse(&text).unwrap(), t);
    assert_eq!(text, src);
}

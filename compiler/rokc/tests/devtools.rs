//! `rokc lint`, `rokc doc`, `rokc bench` (spec 901) on scratch packages.
//! Lint and doc need no LLVM; bench builds native code and skips without
//! the toolchain (see `common::setup`).

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use common::{ROKC, scratch, setup, text, workspace};

/// A fresh scratch package directory holding `files`.
fn package(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let dir = scratch(name);
    for (path, text) in files {
        let p = dir.join(path);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(p, text).unwrap();
    }
    dir
}

fn rokc(cwd: &Path, args: &[&str]) -> Output {
    Command::new(ROKC)
        .current_dir(cwd)
        .env("ROK_HOME", workspace())
        .args(args)
        .output()
        .unwrap()
}

#[track_caller]
fn exit(out: &Output, code: i32) -> (String, String) {
    let (o, e) = (text(&out.stdout), text(&out.stderr));
    assert_eq!(out.status.code(), Some(code), "stdout: {o}\nstderr: {e}");
    (o, e)
}

const LINTED: &str = "\
use rok::core::str::StrBuf;

fn helper() -> i32 { 1 }
fn unusedFn() -> i32 { let y = 2; 3 }
#[must_use]
fn important() -> i32 { 3 }
#[deprecated = \"use helper\"]
fn old() -> i32 { 4 }
struct bad_name { v: i32; }
const lower: i32 = 1;
fn thrower() throws -> i32 { 1 }

#[allow(unused_variables)]
fn quiet() { let a = 1; }

fn main() {
    let v: i32 | none = none;
    if v == none { println(\"n\"); }
    let f = 1.5;
    let z = f as f64;
    let q = 3i32;
    let w = q.clone();
    println(f\"{w} {f:.2} {z}\");
    for i in 0..3 { let i = 5; println(f\"{i}\"); }
    let t = true;
    if t == true { println(\"t\"); }
    let k = 1;
    k = k;
    important();
    println(f\"{old()} {helper()}\");
    try? thrower();
    while true { break; }
    quiet();
    return;
    println(\"x\");
}
";

/// The GC never closes a descriptor (stdlib 2.13): a `File` only read
/// through its own methods and never closed leaks; `using`, `close()`,
/// or handing it on (returned, passed, stored) does not.
#[test]
fn lint_unclosed_resource() {
    let src = "\
use rok::std::fs::File;

fn leaks(p: str) -> str {
    let f = try! File::open(p);
    try! f.read_to_str()
}

fn closes(p: str) -> str {
    let g = try! File::open(p);
    let s = try! g.read_to_str();
    try! g.close();
    s
}

fn scoped(p: str) -> str {
    using h = try! File::open(p) { try! h.read_to_str() }
}

fn handed(p: str) -> File {
    let k = try! File::open(p);
    k
}

fn main() {
    println(leaks(\"a\"));
    println(closes(\"a\"));
    println(scoped(\"a\"));
    try! handed(\"a\").close();
}
";
    let dir = package("lint_unclosed", &[("main.rok", src)]);
    let (_, err) = exit(&rokc(&dir, &["lint"]), 0);
    assert!(
        err.contains("`f` holds a `File` that is never closed"),
        "{err}"
    );
    for name in ["`g`", "`h`", "`k`"] {
        assert!(!err.contains(&format!("{name} holds")), "{err}");
    }
}

#[test]
fn lint_finds_each_kind_and_honors_levels() {
    let dir = package("lint", &[("main.rok", LINTED)]);
    let (_, err) = exit(&rokc(&dir, &["lint"]), 0);
    for want in [
        "unused import `rok::core::str::StrBuf`",
        "function `unusedFn` is never used",
        "function `unusedFn` should have a snake case name",
        "unused variable `y`",
        "type `bad_name` should have an upper camel case name",
        "constant `lower` should have an upper case name",
        "comparing with `none` using `==`",
        "casting to the same type `f64`",
        "redundant `.clone()`",
        "`i` shadows the loop variable `i`",
        "comparison with `true`",
        "`k` is assigned to itself",
        "unused result of `important`",
        "use of deprecated function `old`",
        "`try?` result discarded",
        "`while true` is `loop`",
        "unreachable statement",
        "`#[warn(unused_variables)]` on by default",
    ] {
        assert!(err.contains(want), "missing {want:?}:\n{err}");
    }
    // `#[allow]` on `quiet`; the f-string's own `as f64` is not ours.
    assert!(!err.contains("unused variable `a`"), "{err}");
    assert_eq!(err.matches("casting to the same type").count(), 1, "{err}");

    // `-D` makes it an error (exit 1); `-A` on a group silences it.
    let (_, err) = exit(&rokc(&dir, &["lint", "-D", "unused_variables"]), 1);
    assert!(
        err.contains("error[E503]") && err.contains("`-D unused_variables` on the command line")
    );
    let (_, err) = exit(&rokc(&dir, &["lint", "-A", "all", "-W", "deprecated"]), 0);
    assert!(
        err.contains("deprecated function") && !err.contains("unused"),
        "{err}"
    );
    let (_, err) = exit(&rokc(&dir, &["lint", "-A", "nope"]), 0);
    assert!(err.contains("unknown lint `nope`"), "{err}");

    // Attributes beat the command line, innermost first.
    fs::write(
        dir.join("main.rok"),
        "#![deny(unused)]\nmod m;\n#[warn(unused_variables)]\nfn f() { let a = 1; }\n\
         fn main() { f(); let b = 1; }\n",
    )
    .unwrap();
    fs::write(dir.join("m.rok"), "#![allow(dead_code)]\nfn hidden() {}\n").unwrap();
    let (_, err) = exit(&rokc(&dir, &["lint", "-A", "unused_variables"]), 1);
    assert!(
        err.contains("warning[E503]: unused variable `a`\n  --> main.rok:4:10"),
        "{err}"
    );
    assert!(
        err.contains("error[E503]: unused variable `b`\n  --> main.rok:5:18"),
        "{err}"
    );
    assert!(
        err.contains("`#[deny(unused_variables)]` set here"),
        "{err}"
    );
    assert!(!err.contains("hidden"), "{err}");

    // JSON lines on stdout.
    let (out, _) = exit(&rokc(&dir, &["-q", "--message-format=json", "lint"]), 1);
    let line = out.lines().find(|l| l.contains("`b`")).expect(&out);
    assert!(
        line.starts_with("{\"type\":\"error\",\"code\":\"E503\",\"kind\":\"lint\""),
        "{line}"
    );

    let (out, _) = exit(&rokc(&dir, &["lint", "--list"]), 0);
    assert!(out.contains("unused_variables") && out.contains("nonstandard_style"));

    // No false hits: a method reached only through `?.`, an import used
    // only as the head of a later `use`.
    fs::write(
        dir.join("main.rok"),
        "mod a { pub mod inner { pub fn f() -> i32 { 1 } } }\n\
         use a::inner;\nuse inner::f;\n\
         struct V { x: i32; }\nimpl V { fn get(self) -> i32 { self.x } }\n\
         fn mk() -> V | none { V { x: f() } }\n\
         fn main() { println(f\"{mk()?.get() ?? 0}\"); }\n",
    )
    .unwrap();
    let (_, err) = exit(&rokc(&dir, &["lint"]), 0);
    assert!(!err.contains("[E503]"), "{err}");
}

#[test]
fn doc_writes_html_with_links_and_search_index() {
    let dep = package(
        "doc-dep",
        &[(
            "lib.rok",
            "//! Utilities.\n\n/// Says hi.\npub fn hello() -> i32 { 1 }\n",
        )],
    );
    let dir = package(
        "doc",
        &[
            (
                "lib.rok",
                "//! Shapes and **things**.\n//!\n//! - one\n//! - two\n\n\
                 pub mod geo;\nmod hidden;\n\n\
                 /// A point. See `Shape` and [rok](https://example.com).\n\
                 #[derive(Clone)]\npub struct Point {\n    /// Across.\n    pub x: f64;\n    \
                 secret: f64;\n}\n\n\
                 impl Point {\n    /// The origin.\n    pub fn origin() -> Point { Point { x: 0.0, secret: 0.0 } }\n}\n\n\
                 /// Kinds.\npub enum Shape {\n    /// Round.\n    Circle(f64),\n    Square,\n}\n\n\
                 /// Adds.\n///\n/// ```\n/// add(1, 2) < 4\n/// ```\npub fn add(a: i32, b: i32) -> i32 { a + b }\n\n\
                 fn private_fn() {}\n",
            ),
            (
                "geo.rok",
                "//! Geometry.\n\n/// Area.\npub fn area(p: pkg::Point) -> f64 { p.x }\n",
            ),
            ("hidden.rok", "pub fn invisible() {}\n"),
        ],
    );
    let ext = format!("util={}", dep.display());
    let (_, err) = exit(&rokc(&dir, &["doc", "--extern", &ext]), 0);
    assert!(err.contains("target/doc/index.html"), "{err}");
    let read = |p: &str| fs::read_to_string(dir.join("target/doc").join(p)).unwrap();

    let index = read("index.html");
    let at = |s: &str| {
        index
            .find(s)
            .unwrap_or_else(|| panic!("{s} not in {index}"))
    };
    assert!(
        at("rokc-test") < at("util/index.html"),
        "user package first"
    );

    let root = read(&format!(
        "{}/index.html",
        dir.file_name().unwrap().to_str().unwrap()
    ));
    for want in [
        "<strong>things</strong>",
        "<li>one</li>",
        "id=\"struct.Point\"",
        "<pre class=\"sig fn\"><code>pub fn add(a: i32, b: i32) -&gt; i32</code></pre>",
        "add(1, 2) &lt; 4",
        "<a href=\"https://example.com\">rok</a>",
        "#enum.Shape\"><code>Shape</code></a>",
        "x: f64</code><div class=\"doc\"><p>Across.</p>",
        "impl Clone for Point",
        "The origin.",
        "Circle(f64)",
        "href=\"../style.css\"",
        "geo/index.html\">geo</a>",
    ] {
        assert!(root.contains(want), "missing {want:?}:\n{root}");
    }
    for absent in ["secret", "private_fn", "hidden", "invisible"] {
        assert!(!root.contains(absent), "{absent} leaked:\n{root}");
    }
    let geo = read(&format!(
        "{}/geo/index.html",
        dir.file_name().unwrap().to_str().unwrap()
    ));
    assert!(
        geo.contains("Geometry.") && geo.contains("href=\"../../style.css\""),
        "{geo}"
    );
    assert!(geo.contains("index.html#struct.Point\">Point</a>"), "{geo}");
    assert!(read("util/index.html").contains("Says hi."));

    let search = read("search-index.js");
    assert!(
        search.contains("\"p\":\"util::hello\",\"k\":\"fn\""),
        "{search}"
    );
    assert!(search.contains("geo::area"), "{search}");
    assert!(!search.contains("invisible"), "{search}");
    assert!(read("search.js").contains("SEARCH_INDEX"));
}

/// `rokc doc --std` (no package): the standard library tiers alone, into
/// `./target/doc/`, one directory per tier.
#[test]
fn doc_std_documents_the_library() {
    let dir = scratch("doc-std");
    let (_, err) = exit(&rokc(&dir, &["doc", "--std"]), 0);
    assert!(err.contains("target/doc/index.html"), "{err}");
    let read = |p: &str| fs::read_to_string(dir.join("target/doc").join(p)).unwrap();
    let index = read("index.html");
    for want in [
        "rok-core/index.html\">rok::core",
        "rok-std/index.html\">rok::std",
    ] {
        assert!(index.contains(want), "missing {want:?}:\n{index}");
    }
    let list = read("rok-core/collections/list/index.html");
    assert!(list.contains("id=\"struct.List\""), "{list}");
    assert!(list.contains("href=\"../../../style.css\""), "{list}");
    assert!(read("search-index.js").contains("rok::core::collections::list::List"));
}

#[test]
fn bench_times_each_bench() {
    let Some(env) = setup() else { return };
    let dir = package(
        "bench",
        &[(
            "lib.rok",
            "pub fn fib(n: i64) -> i64 { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }\n\
             #[bench]\nfn fib_10() { fib(10i64); }\n\
             #[bench]\nfn other() { fib(2i64); }\n\
             #[bench]\nfn boom() { panic(\"bad bench\"); }\n",
        )],
    );
    let rokr = env.rokr.display().to_string();
    let run = |extra: &[&str]| {
        let mut args = vec!["bench", "--rokr", &rokr, "--iters", "3", "--samples", "2"];
        args.extend_from_slice(extra);
        rokc(&dir, &args)
    };
    let (out, _) = exit(&run(&["fib"]), 0);
    assert!(out.contains("running 1 bench\n"), "{out}");
    assert!(out.contains("bench fib_10 ... bench:"), "{out}");
    assert!(out.contains(" ns/iter (+/- "), "{out}");
    assert!(
        out.contains("bench result: ok. 1 measured; 0 failed; 2 filtered out"),
        "{out}"
    );

    let (out, _) = exit(&run(&[]), 1);
    assert!(out.contains("bench boom   ... FAILED"), "{out}");
    assert!(out.contains("bad bench"), "{out}");
    assert!(out.contains("2 measured; 1 failed"), "{out}");

    // `#[bench]` functions are not part of a normal build.
    let (_, err) = exit(&rokc(&dir, &["check"]), 0);
    assert!(!err.contains("fib_10"), "{err}");
}

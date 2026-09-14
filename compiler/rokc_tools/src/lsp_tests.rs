//! The language server driven by a scripted JSON-RPC session (front end
//! only: no LLVM toolchain needed).

use std::io::Cursor;
use std::path::Path;

use crate::lsp::serve;
use rokc_diagnostic::Json;

/// One server at a time: the diagnostic file table is process-global.
static ONE_SERVER: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn frame(msg: &Json) -> String {
    let body = msg.to_string();
    format!("Content-Length: {}\r\n\r\n{body}", body.len())
}

fn request(id: u32, method: &str, params: Json) -> Json {
    Json::obj([
        ("jsonrpc", Json::str("2.0")),
        ("id", Json::num(id)),
        ("method", Json::str(method)),
        ("params", params),
    ])
}

fn notify(method: &str, params: Json) -> Json {
    Json::obj([
        ("jsonrpc", Json::str("2.0")),
        ("method", Json::str(method)),
        ("params", params),
    ])
}

fn doc(uri: &str) -> Json {
    Json::obj([("uri", Json::str(uri))])
}

fn at(uri: &str, line: u32, character: u32) -> Json {
    Json::obj([
        ("textDocument", doc(uri)),
        (
            "position",
            Json::obj([
                ("line", Json::num(line)),
                ("character", Json::num(character)),
            ]),
        ),
    ])
}

fn change(uri: &str, text: &str) -> Json {
    notify(
        "textDocument/didChange",
        Json::obj([
            ("textDocument", doc(uri)),
            (
                "contentChanges",
                Json::Arr(vec![Json::obj([("text", Json::str(text))])]),
            ),
        ]),
    )
}

/// Every framed message of the server's output.
fn messages(out: &[u8]) -> Vec<Json> {
    let mut rest = std::str::from_utf8(out).unwrap();
    let mut msgs = Vec::new();
    while let Some(i) = rest.find("\r\n\r\n") {
        let len: usize = rest[..i]
            .trim_start_matches("Content-Length: ")
            .parse()
            .unwrap();
        msgs.push(Json::parse(&rest[i + 4..i + 4 + len]).unwrap());
        rest = &rest[i + 4 + len..];
    }
    msgs
}

const SRC: &str = "\
#[derive(Debug)]
struct P { x: i32; y: i32; }
impl P {
    fn sum(self) -> i32 { self.x + self.y } }
/// Doubles `n`.
fn twice(n: i32) -> i32 { n * 2 }
let p = P { x: 1, y: 2 };
let s = p.sum();
println(f\"{twice(s)}\");
";

#[test]
fn scripted_session() {
    let _one = ONE_SERVER
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let bootstrap = workspace.join("library/core/lib.rok");
    let dir = std::env::temp_dir().join(format!("rokc-lsp-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // A lone file: the anonymous package.
    let file = dir.join("demo.rok");
    let uri = format!("file://{}", file.display());
    let uri = uri.as_str();

    let completing = format!("{SRC}let t = p.\n");
    let paths = format!("{SRC}rok::core::\n");
    let broken = SRC.replace("n * 2", "n * true");
    let unformatted = "fn f() {\nlet a = 1;\n}\n";
    let script = [
        request(
            1,
            "initialize",
            Json::obj([("capabilities", Json::obj([]))]),
        ),
        notify("initialized", Json::obj([])),
        notify(
            "textDocument/didOpen",
            Json::obj([(
                "textDocument",
                Json::obj([
                    ("uri", Json::str(uri)),
                    ("languageId", Json::str("rok")),
                    ("version", Json::num(1)),
                    ("text", Json::str(SRC)),
                ]),
            )]),
        ),
        // `p` in `p.sum()`, `twice` in the call, `s` in `twice(s)`.
        request(2, "textDocument/hover", at(uri, 7, 8)),
        request(3, "textDocument/hover", at(uri, 8, 12)),
        request(4, "textDocument/definition", at(uri, 8, 12)),
        request(5, "textDocument/definition", at(uri, 8, 18)),
        request(
            6,
            "textDocument/documentSymbol",
            Json::obj([("textDocument", doc(uri))]),
        ),
        change(uri, &broken),
        request(10, "textDocument/hover", at(uri, 7, 8)),
        change(uri, &completing),
        request(7, "textDocument/completion", at(uri, 9, 10)),
        change(uri, &paths),
        request(8, "textDocument/completion", at(uri, 9, 11)),
        change(uri, unformatted),
        request(
            9,
            "textDocument/formatting",
            Json::obj([("textDocument", doc(uri))]),
        ),
        request(11, "workspace/bogus", Json::obj([])),
        request(12, "shutdown", Json::Null),
        notify("exit", Json::Null),
    ];
    let input: String = script.iter().map(frame).collect();
    let mut out = Vec::new();
    let code = serve(
        Cursor::new(input.into_bytes()),
        &mut out,
        vec![bootstrap],
        Vec::new(),
        vec![(crate::lint::Level::Allow, "dead_code".to_owned())],
    );
    assert_eq!(code, 0);
    let msgs = messages(&out);
    let result = |id: u32| {
        msgs.iter()
            .find(|m| m.get("id") == &Json::num(id))
            .unwrap_or_else(|| panic!("no reply {id}"))
            .get("result")
            .clone()
    };
    let hover = |id| {
        result(id)
            .get("contents")
            .get("value")
            .as_str()
            .unwrap_or("")
            .to_owned()
    };

    let caps = result(1);
    assert_eq!(
        caps.get("capabilities").get("hoverProvider"),
        &Json::Bool(true)
    );
    assert!(hover(2).contains("p: P"), "{}", hover(2));
    assert!(hover(3).contains("fn twice(n: i32) -> i32"), "{}", hover(3));
    assert!(hover(3).ends_with("```\n\nDoubles `n`."), "{}", hover(3));
    let line = |r: &Json| r.get("range").get("start").get("line").clone();
    assert_eq!(line(&result(4)), Json::num(5));
    assert_eq!(result(4).get("uri").as_str(), Some(uri));
    assert_eq!(line(&result(5)), Json::num(7));

    let Json::Arr(symbols) = result(6) else {
        panic!("symbols: {}", result(6))
    };
    let names: Vec<&str> = symbols
        .iter()
        .filter_map(|s| s.get("name").as_str())
        .collect();
    assert_eq!(names, ["P", "impl P", "twice"]);
    let Json::Arr(methods) = symbols[1].get("children").clone() else {
        panic!()
    };
    assert_eq!(methods[0].get("name").as_str(), Some("sum"));

    let labels = |id| match result(id) {
        Json::Arr(items) => items
            .iter()
            .filter_map(|i| i.get("label").as_str().map(str::to_owned))
            .collect::<Vec<_>>(),
        r => panic!("completion {id}: {r}"),
    };
    let members = labels(7);
    for m in ["x", "y", "sum"] {
        assert!(members.iter().any(|l| l == m), "{members:?}");
    }
    assert!(labels(8).iter().any(|l| l == "fmt"), "{:?}", labels(8));

    let Json::Arr(edits) = result(9) else {
        panic!("formatting: {}", result(9))
    };
    assert_eq!(
        edits[0].get("newText").as_str(),
        Some("fn f() {\n    let a = 1;\n}\n")
    );

    // Hover still answers from the last good compile of a broken buffer.
    assert!(hover(10).contains("p: P"), "{}", hover(10));
    let bogus = msgs.iter().find(|m| m.get("id") == &Json::num(11)).unwrap();
    assert_eq!(bogus.get("error").get("code"), &Json::num(-32601));

    // Diagnostics: clean at first, then the type error of `broken`.
    let published: Vec<&Json> = msgs
        .iter()
        .filter(|m| m.get("method").as_str() == Some("textDocument/publishDiagnostics"))
        .map(|m| m.get("params"))
        .collect();
    assert_eq!(published[0].get("diagnostics"), &Json::Arr(Vec::new()));
    let Json::Arr(second) = published[1].get("diagnostics").clone() else {
        panic!()
    };
    let err = second
        .iter()
        .find(|d| d.get("severity") == &Json::num(1))
        .unwrap_or_else(|| panic!("no error in {second:?}"));
    assert_eq!(line(err), Json::num(5));
    // The last buffer type-checks; its lints follow the given levels.
    let Json::Arr(last) = published.last().unwrap().get("diagnostics").clone() else {
        panic!()
    };
    assert_eq!(last.len(), 1, "{last:?}");
    let msg = last[0].get("message").as_str().unwrap_or("");
    assert!(msg.starts_with("unused variable `a`"), "{msg}");
    let _ = std::fs::remove_dir_all(&dir);
}

const MEMBERS: &str = "\
struct P {
    /// The x coordinate.
    x: i32;
    y: i32;
}
impl P {
    /// Sum of the coordinates.
    fn sum(self) -> i32 { self.x + self.y }
}
let p = P { x: 1, y: 2 };
let total = p.sum() + p.x;
let u = total * 2;
println(f\"{u}\");
";

/// Hover and definition of fields and methods, name ranges,
/// references and rename.
#[test]
fn members_references_rename() {
    let _one = ONE_SERVER
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let bootstrap = workspace.join("library/core/lib.rok");
    let dir = std::env::temp_dir().join(format!("rokc-lsp-members-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("members.rok");
    let uri = format!("file://{}", file.display());
    let uri = uri.as_str();
    let rename = |id, line, col, name: &str| {
        let mut p = at(uri, line, col);
        if let Json::Obj(fields) = &mut p {
            fields.push(("newName".to_owned(), Json::str(name)));
        }
        request(id, "textDocument/rename", p)
    };
    let script = [
        request(
            1,
            "initialize",
            Json::obj([("capabilities", Json::obj([]))]),
        ),
        notify(
            "textDocument/didOpen",
            Json::obj([(
                "textDocument",
                Json::obj([
                    ("uri", Json::str(uri)),
                    ("languageId", Json::str("rok")),
                    ("version", Json::num(1)),
                    ("text", Json::str(MEMBERS)),
                ]),
            )]),
        ),
        // `sum` and `x` in `p.sum() + p.x`, `total` in `total * 2`.
        request(2, "textDocument/hover", at(uri, 10, 15)),
        request(3, "textDocument/hover", at(uri, 10, 24)),
        request(4, "textDocument/definition", at(uri, 10, 15)),
        request(5, "textDocument/definition", at(uri, 10, 24)),
        request(6, "textDocument/definition", at(uri, 11, 9)),
        request(7, "textDocument/references", at(uri, 11, 9)),
        request(8, "textDocument/references", at(uri, 10, 24)),
        rename(9, 11, 9, "sum2"),
        rename(10, 11, 9, "fn"),
        rename(11, 12, 1, "say"),
        request(12, "shutdown", Json::Null),
        notify("exit", Json::Null),
    ];
    let input: String = script.iter().map(frame).collect();
    let mut out = Vec::new();
    let code = serve(
        Cursor::new(input.into_bytes()),
        &mut out,
        vec![bootstrap],
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(code, 0);
    let msgs = messages(&out);
    let reply = |id: u32| {
        msgs.iter()
            .find(|m| m.get("id") == &Json::num(id))
            .unwrap_or_else(|| panic!("no reply {id}"))
            .clone()
    };
    let result = |id: u32| reply(id).get("result").clone();
    let hover = |id| {
        result(id)
            .get("contents")
            .get("value")
            .as_str()
            .unwrap_or("")
            .to_owned()
    };
    let start = |r: &Json| {
        let s = r.get("range").get("start");
        (s.get("line").clone(), s.get("character").clone())
    };
    let pos = |l: u32, c: u32| (Json::num(l), Json::num(c));

    assert!(hover(2).contains("fn sum(self: P) -> i32"), "{}", hover(2));
    assert!(
        hover(2).ends_with("Sum of the coordinates."),
        "{}",
        hover(2)
    );
    assert!(hover(3).contains("P.x: i32"), "{}", hover(3));
    assert!(hover(3).ends_with("The x coordinate."), "{}", hover(3));
    // Name ranges, not whole items.
    assert_eq!(start(&result(4)), pos(7, 7));
    assert_eq!(start(&result(5)), pos(2, 4));
    assert_eq!(start(&result(6)), pos(10, 4));

    let starts = |id| match result(id) {
        Json::Arr(locs) => locs.iter().map(start).collect::<Vec<_>>(),
        r => panic!("references {id}: {r}"),
    };
    assert_eq!(starts(7), [pos(10, 4), pos(11, 8)]);
    // `.x` reads, the declaration and the literal's `x:`.
    assert_eq!(starts(8), [pos(2, 4), pos(7, 31), pos(9, 12), pos(10, 24)]);

    let Json::Arr(edits) = result(9).get("changes").get(uri).clone() else {
        panic!("rename: {}", reply(9))
    };
    assert_eq!(edits.len(), 2);
    assert_eq!(edits[0].get("newText").as_str(), Some("sum2"));
    assert!(
        matches!(reply(10).get("error"), Json::Obj(_)),
        "{}",
        reply(10)
    );
    // `println` is declared in the library.
    assert!(
        matches!(reply(11).get("error"), Json::Obj(_)),
        "{}",
        reply(11)
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A `.rokon` buffer (`rok.rokon`, the package manifest) is one RokON
/// value: only its syntax is checked, not compiled as a module.
#[test]
fn manifest_buffer() {
    let _one = ONE_SERVER
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let uri = "file:///nowhere/rok.rokon";
    let open = notify(
        "textDocument/didOpen",
        Json::obj([(
            "textDocument",
            Json::obj([
                ("uri", Json::str(uri)),
                ("languageId", Json::str("rok")),
                ("version", Json::num(1)),
                (
                    "text",
                    Json::str("Package {\n    deps: { \"a\": Dep::path(\"x\") },\n}\n"),
                ),
            ]),
        )]),
    );
    let script = [
        open,
        request(1, "textDocument/hover", at(uri, 0, 1)),
        change(uri, "Package {\n    name: \"a\"\n    version: \"1\",\n}\n"),
        request(2, "textDocument/hover", at(uri, 0, 1)),
        // Valid rok, but not RokON data.
        change(uri, "Package {\n    name: bare,\n}\n"),
        request(4, "textDocument/hover", at(uri, 0, 1)),
        request(3, "shutdown", Json::Null),
        notify("exit", Json::Null),
    ];
    let input: String = script.iter().map(frame).collect();
    let mut out = Vec::new();
    let code = serve(
        Cursor::new(input.into_bytes()),
        &mut out,
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(code, 0);
    let published: Vec<Json> = messages(&out)
        .into_iter()
        .filter(|m| m.get("method").as_str() == Some("textDocument/publishDiagnostics"))
        .map(|m| m.get("params").get("diagnostics").clone())
        .collect();
    assert_eq!(published[0], Json::Arr(Vec::new()));
    let Json::Arr(errs) = &published[1] else {
        panic!("{published:?}")
    };
    assert!(!errs.is_empty(), "{published:?}");
    assert_eq!(errs[0].get("range").get("start").get("line"), &Json::num(2));
    let Json::Arr(errs) = &published[2] else {
        panic!("{published:?}")
    };
    assert_eq!(errs[0].get("range").get("start").get("line"), &Json::num(1));
    assert!(
        errs[0]
            .get("message")
            .as_str()
            .is_some_and(|m| m.starts_with("bare identifier `bare`")),
        "{published:?}"
    );
}

/// An open submodule buffer stands for its file: its unsaved text is
/// what the package compiles with.
#[test]
fn unsaved_submodule_buffer() {
    let _one = ONE_SERVER
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let bootstrap = workspace.join("library/core/lib.rok");
    let dir = std::env::temp_dir().join(format!("rokc-lsp-sub-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("main.rok"), "mod m;\n\nlet x: i32 = m::v();\n").unwrap();
    std::fs::write(dir.join("m.rok"), "pub fn v() -> i32 {\n    1\n}\n").unwrap();
    let uri = format!("file://{}", dir.join("m.rok").display());
    let uri = uri.as_str();
    let open = notify(
        "textDocument/didOpen",
        Json::obj([(
            "textDocument",
            Json::obj([
                ("uri", Json::str(uri)),
                ("languageId", Json::str("rok")),
                ("version", Json::num(1)),
                ("text", Json::str("pub fn v() -> i32 {\n    true\n}\n")),
            ]),
        )]),
    );
    let script = [
        open,
        request(1, "textDocument/hover", at(uri, 0, 8)),
        change(uri, "pub fn v() -> i32 {\n    2\n}\n"),
        request(2, "textDocument/hover", at(uri, 0, 8)),
        request(3, "shutdown", Json::Null),
        notify("exit", Json::Null),
    ];
    let input: String = script.iter().map(frame).collect();
    let mut out = Vec::new();
    let code = serve(
        Cursor::new(input.into_bytes()),
        &mut out,
        vec![bootstrap],
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(code, 0);
    let published: Vec<Json> = messages(&out)
        .into_iter()
        .filter(|m| m.get("method").as_str() == Some("textDocument/publishDiagnostics"))
        .map(|m| m.get("params").get("diagnostics").clone())
        .collect();
    let Json::Arr(errs) = &published[0] else {
        panic!("{published:?}")
    };
    assert_eq!(errs.len(), 1, "{published:?}");
    assert!(
        errs[0]
            .get("message")
            .as_str()
            .is_some_and(|m| m.contains("bool")),
        "{published:?}"
    );
    assert_eq!(published[1], Json::Arr(Vec::new()), "{published:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

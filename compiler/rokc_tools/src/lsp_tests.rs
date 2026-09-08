//! The language server driven by a scripted JSON-RPC session (front end
//! only: no LLVM toolchain needed).

use std::io::Cursor;
use std::path::Path;

use crate::json::Json;
use crate::lsp::serve;

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
    fn sum(self) -> i32 { self.x + self.y }
}
fn twice(n: i32) -> i32 { n * 2 }
let p = P { x: 1, y: 2 };
let s = p.sum();
println(f\"{twice(s)}\");
";

#[test]
fn scripted_session() {
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
    // The formatted-away buffer compiles clean again.
    assert_eq!(
        published.last().unwrap().get("diagnostics"),
        &Json::Arr(Vec::new())
    );
    let _ = std::fs::remove_dir_all(&dir);
}

//! Interactive tools through the binaries: `rokc repl` fed by a pipe,
//! `rokls` / `rokc lsp` framing, `rokc check -`. (The language server's
//! queries are tested in `rokc_tools`.)

mod common;

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use common::{ROKC, setup};

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// `exe args` with `input` on stdin.
fn piped(exe: &str, args: &[&str], input: &str) -> Output {
    let mut child = Command::new(exe)
        .args(args)
        .env("ROK_HOME", workspace())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

#[test]
fn repl_keeps_state_across_cells() {
    let Some(env) = setup() else { return };
    let rokr = env.rokr.display().to_string();
    let input = "\
1 + 2
let x =
    40i32;
#[derive(Debug)]
struct P { x: i32; y: i32; }
fn add(p: P) -> i32 { p.x + p.y }
let p = P { x: x, y: 2 };
println(f\"sum {add(p)}\");
p
:type add(p)
let x = \"rebound\";
x
nope
fn add(p: P) -> i32 { p.x * p.y }
add(p)
panic(\"boom\");
[1, 2, 3]
:reset
:type x
:quit
1 + 1
";
    let out = piped(ROKC, &["repl", "--rokr", &rokr], input);
    let stdout = text(&out.stdout);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stdout}\n{stderr}");
    assert_eq!(
        stdout,
        "\
i32: 3
i32: 40
P: P { x: 40, y: 2 }
sum 42
P: P { x: 40, y: 2 }
i32
str: \"rebound\"
str: \"rebound\"
i32: 80
List<i32>: [1, 2, 3]
",
        "stderr: {stderr}"
    );
    // A bad cell reports and is dropped; so is one that fails at run time.
    assert!(stderr.contains("cannot find value `nope`"), "{stderr}");
    assert!(stderr.contains("boom"), "{stderr}");
    // After `:reset` nothing is bound.
    assert!(stderr.contains("cannot find value `x`"), "{stderr}");
}

fn frame(body: &str) -> String {
    format!("Content-Length: {}\r\n\r\n{body}", body.len())
}

#[test]
fn rokc_lsp_answers_over_stdio() {
    let input = [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#,
        r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]
    .map(frame)
    .concat();
    // (`rokls` is `rok lsp`: the `rok` crate tests it.)
    {
        let out = piped(ROKC, &["lsp"], &input);
        assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
        let stdout = text(&out.stdout);
        assert!(stdout.starts_with("Content-Length: "), "{stdout}");
        assert!(stdout.contains(r#""hoverProvider":true"#), "{stdout}");
        assert!(stdout.contains(r#""id":2,"result":null"#), "{stdout}");
    }
    // `exit` without `shutdown` is exit code 1 (LSP spec).
    let out = piped(
        ROKC,
        &["lsp"],
        &frame(r#"{"jsonrpc":"2.0","method":"exit"}"#),
    );
    assert_eq!(out.status.code(), Some(1));
}

#[test]
fn check_reads_stdin() {
    let out = piped(
        ROKC,
        &["-q", "check", "-"],
        "let x: i32 = 1;\nprintln(f\"{x}\");\n",
    );
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let out = piped(ROKC, &["-q", "check", "-"], "let x: i32 = true;\n");
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out.stderr).contains("<stdin>:1:"),
        "{}",
        text(&out.stderr)
    );
}

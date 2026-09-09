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
    // The default (one library per cell) and `--replay` modes agree.
    let runs: Vec<_> = [&[][..], &["--replay"][..]]
        .map(|mode| {
            let rokr = rokr.clone();
            std::thread::spawn(move || {
                let args = [&["repl", "--rokr", &rokr][..], mode].concat();
                piped(ROKC, &args, input)
            })
        })
        .into_iter()
        .collect();
    for run in runs {
        let out = run.join().unwrap();
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
}

/// The default mode runs a cell once, in one process: its side effects
/// do not repeat, its bindings / items stay, and a cell that dies
/// leaves the session as it was.
#[test]
fn repl_runs_each_cell_once() {
    let Some(env) = setup() else { return };
    let rokr = env.rokr.display().to_string();
    let log = std::env::temp_dir().join(format!("rok_repl_once_{}", std::process::id()));
    let log_s = log.display().to_string();
    let _ = std::fs::remove_file(&log);
    // Cell 1 appends to `log`: a rerun would append again.
    let input = format!(
        "\
println(\"once\"); let old = try fs::read_to_str(\"{log_s}\") catch _ {{ \"\" }}; try fs::write(\"{log_s}\", old + \"x\") catch _ {{ }};
let n = 1i32;
#[derive(Debug)]
struct P {{ x: i32; }}
fn twice(p: P) -> i32 {{ p.x * 2 }}
let p = P {{ x: 21 }};
n += 1;
n += 100; panic(\"boom\");
n
twice(p)
p
"
    );
    let out = piped(
        ROKC,
        &["repl", "--rokr", &rokr],
        &format!("use rok::std::fs;\n{input}"),
    );
    let stdout = text(&out.stdout);
    let stderr = text(&out.stderr);
    assert_eq!(
        stdout, "once\ni32: 1\nP: P { x: 21 }\ni32: 2\ni32: 42\nP: P { x: 21 }\n",
        "stderr: {stderr}"
    );
    assert!(stderr.contains("boom"), "{stderr}");
    assert_eq!(std::fs::read_to_string(&log).ok().as_deref(), Some("x"));
    let _ = std::fs::remove_file(&log);
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

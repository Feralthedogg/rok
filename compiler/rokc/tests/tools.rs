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
    piped_env(exe, args, input, &[])
}

/// `piped` with environment variables `env`.
fn piped_env(exe: &str, args: &[&str], input: &str, env: &[(&str, &str)]) -> Output {
    let mut child = Command::new(exe)
        .args(args)
        .env("ROK_HOME", workspace())
        .envs(env.iter().copied())
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

/// `repl --package <lib>` (901.2): the library is loaded and its items
/// are in scope from the first cell, also after `:reset`.
#[test]
fn repl_package_loads_and_uses_a_library() {
    let Some(env) = setup() else { return };
    let rokr = env.rokr.display().to_string();
    let dir = std::env::temp_dir().join(format!("rok_repl_pkg_{}", std::process::id()));
    let lib = dir.join("geom");
    std::fs::create_dir_all(&lib).unwrap();
    std::fs::write(
        lib.join("lib.rok"),
        "pub fn twice(x: i32) -> i32 { x * 2 }\n",
    )
    .unwrap();
    let pkg = lib.display().to_string();
    let out = piped(
        ROKC,
        &["repl", "--rokr", &rokr, "--package", &pkg],
        "twice(21)\n:reset\ntwice(2)\n",
    );
    let stdout = text(&out.stdout);
    assert_eq!(stdout, "i32: 42\ni32: 4\n", "{}", text(&out.stderr));
    // A main package is refused.
    std::fs::write(dir.join("main.rok"), "").unwrap();
    let main = dir.display().to_string();
    let out = piped(ROKC, &["repl", "--rokr", &rokr, "--package", &main], "");
    assert_eq!(out.status.code(), Some(1));
    assert!(text(&out.stderr).contains("not a library package"));
    let _ = std::fs::remove_dir_all(&dir);
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

/// A binding a later cell could not use is refused in the cell that
/// makes it (`--replay` keeps it); one a later cell can name is kept,
/// `any` values too (their methods and type tests work in later cells).
#[test]
fn repl_refuses_bindings_later_cells_cannot_use() {
    let Some(env) = setup() else { return };
    let rokr = env.rokr.display().to_string();
    let input = "\
mod geo { struct Hid { x: i32; } pub fn mk() -> Hid { Hid { x: 1 } } pub struct Pt { pub x: i32; } }
let h = geo::mk();
let d: any Debug = 5i32;
let pt = geo::Pt { x: 3 };
pt.x
#[derive(Debug)]
struct Q { v: i32; }
let q: any Debug = Q { v: 9 };
d
q
match q { x: Q => x.v, _ => 0 }
";
    let out = piped(ROKC, &["repl", "--rokr", &rokr], input);
    let stdout = text(&out.stdout);
    let stderr = text(&out.stderr);
    let any = "any rok::core::fmt::Debug";
    assert_eq!(
        stdout,
        format!(
            "{any}: 5\nPt\ni32: 3\n{any}: Q {{ v: 9 }}\n{any}: 5\n{any}: Q {{ v: 9 }}\ni32: 9\n"
        ),
        "stderr: {stderr}"
    );
    assert!(
        stderr.contains("`h: Hid` cannot be kept for later cells (`geo::Hid` is private"),
        "{stderr}"
    );
    assert!(stderr.contains("--replay` keeps it"), "{stderr}");
}

/// `static` items keep their state across cells (a redefinition starts
/// it over). On macOS arm64 the host loads each cell's object itself;
/// `ROK_REPL_DYLIB=1` loads shared libraries instead.
#[test]
fn repl_statics_persist() {
    let Some(env) = setup() else { return };
    let rokr = env.rokr.display().to_string();
    let input = "\
static N: Atomic<i32> = Atomic::new(0);
fn bump() -> i32 { return N.fetch_add(1) + 1; }
bump()
bump()
N.load()
";
    let redefined = "\
static N: Atomic<i32> = Atomic::new(100);
bump()
bump()
";
    let args = ["repl", "--rokr", &rokr];
    let out = piped_env(
        ROKC,
        &args,
        &format!("{input}{redefined}"),
        &[("ROK_REPL_TIME", "1")],
    );
    let stderr = text(&out.stderr);
    assert_eq!(
        text(&out.stdout),
        "i32: 1\ni32: 2\ni32: 2\ni32: 101\ni32: 102\n",
        "stderr: {stderr}"
    );
    if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        assert!(stderr.contains("[repl] load + run"), "{stderr}");
        assert!(!stderr.contains("dlopen"), "{stderr}");
    }
    let out = piped_env(ROKC, &args, input, &[("ROK_REPL_DYLIB", "1")]);
    assert_eq!(
        text(&out.stdout),
        "i32: 1\ni32: 2\ni32: 2\n",
        "stderr: {}",
        text(&out.stderr)
    );
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

/// `rokc jupyter` driven by a hand-written ZMTP client (no Jupyter
/// needed): heartbeat, `kernel_info`, cells that bind, show, print and
/// panic, completion, and `shutdown`. Every message must be signed.
#[test]
fn jupyter_kernel_speaks_the_wire_protocol() {
    use rokc_tools::json::Json;
    use rokc_tools::jupyter::{encode, handshake, parse_msg, read_msg, write_msg};
    use std::net::{TcpListener, TcpStream};
    use std::time::Duration;

    let Some(env) = setup() else { return };
    let key = b"secret-key";
    let listeners: Vec<_> = (0..5)
        .map(|_| TcpListener::bind("127.0.0.1:0").unwrap())
        .collect();
    let ports: Vec<u16> = listeners
        .iter()
        .map(|l| l.local_addr().unwrap().port())
        .collect();
    drop(listeners);
    let dir = std::env::temp_dir().join(format!("rok_jupyter_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("kernel.json");
    std::fs::write(
        &file,
        format!(
            r#"{{"transport":"tcp","ip":"127.0.0.1","shell_port":{},"iopub_port":{},
"stdin_port":{},"control_port":{},"hb_port":{},"key":"secret-key",
"signature_scheme":"hmac-sha256","kernel_name":"rok"}}"#,
            ports[0], ports[1], ports[2], ports[3], ports[4]
        ),
    )
    .unwrap();
    let kernel = Command::new(ROKC)
        .args(["jupyter", "--connection-file"])
        .arg(&file)
        .args(["--rokr", &env.rokr.display().to_string()])
        .env("ROK_HOME", workspace())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let connect = |port: u16, kind: &str| {
        let mut s = (0..200)
            .find_map(|_| {
                TcpStream::connect(("127.0.0.1", port)).ok().or_else(|| {
                    std::thread::sleep(Duration::from_millis(50));
                    None
                })
            })
            .expect("the kernel does not listen");
        s.set_read_timeout(Some(Duration::from_secs(120))).unwrap();
        handshake(&mut s, kind).unwrap();
        s
    };
    let mut iopub = connect(ports[1], "SUB");
    write_msg(&mut iopub, &[b"\x01".to_vec()]).unwrap();
    let mut shell = connect(ports[0], "DEALER");
    let mut control = connect(ports[3], "DEALER");
    let mut hb = connect(ports[4], "REQ");
    write_msg(&mut hb, &[Vec::new(), b"ping".to_vec()]).unwrap();
    assert_eq!(read_msg(&mut hb).unwrap(), [Vec::new(), b"ping".to_vec()]);

    // Send a request: its reply (type, content) and the iopub messages
    // it caused, up to its `idle`.
    let mut request = |s: &mut TcpStream, kind: &str, content: Json| {
        let frames = encode(key, "test", &[], kind, &Json::obj([]), &content);
        let mine = parse_msg(key, frames.clone()).unwrap().header;
        let id = mine.get("msg_id").clone();
        write_msg(s, &frames).unwrap();
        let reply = parse_msg(key, read_msg(s).unwrap()).expect("a signed reply");
        assert!(reply.ids.is_empty());
        assert_eq!(reply.parent.get("msg_id"), &id);
        let mut published = Vec::new();
        loop {
            let m = parse_msg(key, read_msg(&mut iopub).unwrap()).expect("signed iopub");
            if m.parent.get("msg_id") != &id {
                continue;
            }
            if m.content.get("execution_state").as_str() == Some("idle") {
                break;
            }
            published.push((m.kind().to_owned(), m.content));
        }
        (reply.kind().to_owned(), reply.content, published)
    };
    let exec = |code: &str| Json::obj([("code", Json::str(code)), ("silent", Json::Bool(false))]);
    let shows = |published: &[(String, Json)], text: &str| {
        published.iter().any(|(k, c)| {
            k == "execute_result" && c.get("data").get("text/plain").as_str() == Some(text)
        })
    };

    let (kind, info, _) = request(&mut shell, "kernel_info_request", Json::obj([]));
    assert_eq!(kind, "kernel_info_reply");
    assert_eq!(info.get("language_info").get("name").as_str(), Some("rok"));

    let (_, reply, _) = request(&mut shell, "execute_request", exec("let x = 40i32;"));
    assert_eq!(reply.get("status").as_str(), Some("ok"), "{reply}");
    let (_, reply, published) = request(&mut shell, "execute_request", exec("x + 2"));
    assert_eq!(reply.get("execution_count"), &Json::num(2));
    assert!(shows(&published, "i32: 42"), "{published:?}");
    assert!(
        published
            .iter()
            .any(|(k, c)| k == "execute_input" && c.get("code").as_str() == Some("x + 2"))
    );

    let (_, _, published) = request(&mut shell, "execute_request", exec("println(f\"hi {x}\");"));
    assert!(
        published.iter().any(|(k, c)| k == "stream"
            && c.get("name").as_str() == Some("stdout")
            && c.get("text").as_str() == Some("hi 40\n")),
        "{published:?}"
    );

    let (_, reply, published) = request(&mut shell, "execute_request", exec("panic(\"boom\");"));
    assert_eq!(reply.get("status").as_str(), Some("error"), "{reply}");
    let error = published.iter().find(|(k, _)| k == "error").expect("error");
    assert!(error.1.to_string().contains("boom"), "{}", error.1);
    // The session goes on, as it was before the failed cell.
    let (_, _, published) = request(&mut shell, "execute_request", exec("x"));
    assert!(shows(&published, "i32: 40"), "{published:?}");

    let (_, reply, _) = request(
        &mut shell,
        "is_complete_request",
        Json::obj([("code", Json::str("fn f() {"))]),
    );
    assert_eq!(reply.get("status").as_str(), Some("incomplete"));
    let (_, reply, _) = request(
        &mut shell,
        "complete_request",
        Json::obj([("code", Json::str("1 + x")), ("cursor_pos", Json::num(5))]),
    );
    assert_eq!(
        reply.get("matches"),
        &Json::Arr(vec![Json::str("x")]),
        "{reply}"
    );
    assert_eq!(reply.get("cursor_start"), &Json::num(4));

    let (kind, _, _) = request(
        &mut control,
        "shutdown_request",
        Json::obj([("restart", Json::Bool(false))]),
    );
    assert_eq!(kind, "shutdown_reply");
    let out = kernel.wait_with_output().unwrap();
    assert!(out.status.success(), "{}", text(&out.stderr));
    let _ = std::fs::remove_dir_all(&dir);
}

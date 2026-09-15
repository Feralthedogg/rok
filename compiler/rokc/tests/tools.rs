//! Interactive tools through the binaries: `rokc repl` fed by a pipe,
//! `rokls` / `rokc lsp` framing, `rokc check -`. (The language server's
//! queries are tested in `rokc_tools`.)

mod common;

use std::io::{BufRead, BufReader, Read, Write};
use std::process::{Command, Output, Stdio};

use common::{ROKC, scratch, setup, setup_runtime, text, workspace};

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

#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_keeps_state_across_cells() {
    let env = setup_runtime();
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
sum 42
P: P { x: 40, y: 2 }
i32
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

/// `repl <lib>` (901.2): the library is loaded and its items
/// are in scope from the first cell, also after `:reset`.
#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_loads_and_uses_a_library() {
    // The library is archived by LLVM.
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
        &["repl", "--rokr", &rokr, &pkg],
        "twice(21)\n:reset\ntwice(2)\n",
    );
    let stdout = text(&out.stdout);
    assert_eq!(stdout, "i32: 42\ni32: 4\n", "{}", text(&out.stderr));
    let _ = std::fs::remove_dir_all(&dir);
}

/// A cell runs once, in one process: its side effects
/// do not repeat, its bindings / items stay, and a cell that dies
/// leaves the session as it was.
#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_runs_each_cell_once() {
    let env = setup_runtime();
    let rokr = env.rokr.display().to_string();
    let log = std::env::temp_dir().join(format!("rok_repl_once_{}", std::process::id()));
    let log_s = log.display().to_string().replace('\\', "/");
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
        stdout, "once\ni32: 2\ni32: 42\nP: P { x: 21 }\n",
        "stderr: {stderr}"
    );
    assert!(stderr.contains("boom"), "{stderr}");
    assert_eq!(std::fs::read_to_string(&log).ok().as_deref(), Some("x"));
    let _ = std::fs::remove_file(&log);
}

/// A binding a later cell could not use is refused in the cell that
/// makes it; one a later cell can name is kept,
/// `any` values too (their methods and type tests work in later cells).
#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_refuses_bindings_later_cells_cannot_use() {
    let env = setup_runtime();
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
        format!("i32: 3\n{any}: 5\n{any}: Q {{ v: 9 }}\ni32: 9\n"),
        "stderr: {stderr}"
    );
    assert!(
        stderr.contains("`h: Hid` cannot be kept for later cells (`geo::Hid` is private"),
        "{stderr}"
    );
}

/// `static` items keep their state across cells (a redefinition starts
/// it over); cells are JIT-compiled.
#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_statics_persist() {
    let env = setup_runtime();
    let rokr = env.rokr.display().to_string();
    let input = "\
static N: Atomic<i32> = Atomic::new(0);
fn bump() -> i32 { return N.fetch_add(1) + 1; }
bump()
bump()
N.load()
static N: Atomic<i32> = Atomic::new(100);
bump()
bump()
";
    let out = piped_env(
        ROKC,
        &["repl", "--rokr", &rokr],
        input,
        &[("ROK_REPL_TIME", "1")],
    );
    let stderr = text(&out.stderr);
    assert_eq!(
        text(&out.stdout),
        "i32: 1\ni32: 2\ni32: 2\ni32: 101\ni32: 102\n",
        "stderr: {stderr}"
    );
    assert!(stderr.contains("[repl] jit + run"), "{stderr}");
}

/// Library code (and unchanged items) is compiled once per session: a
/// later cell declares what an earlier one compiled. A redefinition
/// still takes effect from the next cell, also in code compiled before
/// it that a later cell reaches again (`g`, compiled with the old `f`).
#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_compiles_library_code_once() {
    let env = setup_runtime();
    let rokr = env.rokr.display().to_string();
    let input = "\
let l = [1, 2, 3];
l.len()
fn f() -> i32 { 1 }
fn g() -> i32 { f() + 10 }
g()
fn f() -> i32 { 2 }
f()
g()
";
    let out = piped_env(
        ROKC,
        &["repl", "--rokr", &rokr],
        input,
        &[("ROK_REPL_TIME", "1")],
    );
    let stderr = text(&out.stderr);
    assert_eq!(
        text(&out.stdout),
        "usize: 3\ni32: 11\ni32: 2\ni32: 12\n",
        "stderr: {stderr}"
    );
    let counts: Vec<(usize, usize)> = stderr
        .lines()
        .filter_map(|l| l.strip_prefix("[repl] functions: "))
        .filter_map(|l| {
            let (new, old) = l.split_once(" compiled, ")?;
            Some((new.parse().ok()?, old.split(' ').next()?.parse().ok()?))
        })
        .collect();
    assert_eq!(counts.len(), 5, "{stderr}");
    // `l.len()`: `List`'s methods come from the first cell.
    assert!(
        counts[0].0 > 10 && counts[1].0 <= 3 && counts[1].1 > 10,
        "{stderr}"
    );
}

/// `repl <path>`: the program runs in the session, which goes on with its
/// bindings and items. A failure keeps the bindings made before the
/// cell (the stretch ending at a top-level `let`) that failed; panic
/// locations and diagnostics point into the file.
#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_path_keeps_the_programs_bindings() {
    let env = setup_runtime();
    let rokr = env.rokr.display().to_string();
    let dir = scratch("run_i");
    let prog = dir.join("prog.rok");
    std::fs::write(
        &prog,
        "\
mod geo { struct Hid { x: i32; } pub fn mk() -> Hid { Hid { x: 1 } } pub fn get(h: Hid) -> i32 { h.x } }
#[derive(Debug)]
struct P { x: i32; }
let n = 1i32;
let h = geo::mk();
let m = geo::get(h) + n;
fn twice(p: P) -> i32 { p.x * 2 }
let p = P { x: m };
let xs = [1, 2, 3];
println(f\"ran {twice(p)}\");
n += 100;
let bad = xs[m + 5];
let never = 0;
",
    )
    .unwrap();
    let path = prog.display().to_string();
    let input = "n\n:type p\ntwice(p) + m\nxs\nnever\n";
    let out = piped(ROKC, &["repl", "--rokr", &rokr, &path], input);
    let stdout = text(&out.stdout);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stdout}\n{stderr}");
    // `n += 100` ran in the cell that failed: `n` is as before it.
    assert_eq!(
        stdout, "ran 4\ni32: 1\nP\ni32: 6\nList<i32>: [1, 2, 3]\n",
        "stderr: {stderr}"
    );
    assert!(stderr.contains(&format!("{path}:12:11")), "{stderr}");
    assert!(
        stderr.contains("the rest of the program did not run"),
        "{stderr}"
    );
    assert!(stderr.contains("cannot find value `never`"), "{stderr}");
    // `h`'s type is private to `geo`: not kept, and nothing after names it.
    assert!(stderr.contains("`h: Hid` cannot be kept"), "{stderr}");

    // `fn main`: it runs; the items stay, its locals do not.
    std::fs::write(
        &prog,
        "fn helper(x: i32) -> i32 { x * 2 }\nfn main() {\n    let local = helper(21);\n    println(f\"main {local}\");\n}\n",
    )
    .unwrap();
    let out = piped(
        ROKC,
        &["repl", "--rokr", &rokr, &path],
        "helper(5)\nlocal\n",
    );
    let stderr = text(&out.stderr);
    assert_eq!(text(&out.stdout), "main 42\ni32: 10\n", "stderr: {stderr}");
    assert!(stderr.contains("cannot find value `local`"), "{stderr}");

    // A program that does not compile runs nothing; its errors point
    // into it, and the session starts empty.
    std::fs::write(&prog, "println(\"no\");\nlet y = nope + 1;\n").unwrap();
    let out = piped(ROKC, &["repl", "--rokr", &rokr, &path], "1 + 1\n");
    let stderr = text(&out.stderr);
    assert_eq!(text(&out.stdout), "i32: 2\n", "stderr: {stderr}");
    assert!(stderr.contains(&format!("{path}:2:9")), "{stderr}");

    // A package: its `mod` files resolve.
    let pkg = dir.join("pkg");
    std::fs::create_dir_all(&pkg).unwrap();
    std::fs::write(pkg.join("main.rok"), "mod util;\nlet k = util::three();\n").unwrap();
    std::fs::write(pkg.join("util.rok"), "pub fn three() -> i32 { 3 }\n").unwrap();
    let pkg_s = pkg.display().to_string();
    let out = piped(
        ROKC,
        &["repl", "--rokr", &rokr, &pkg_s],
        "k + util::three()\n",
    );
    assert_eq!(text(&out.stdout), "i32: 6\n", "{}", text(&out.stderr));
    let _ = std::fs::remove_dir_all(&dir);
}

/// A cell that faults, panics deep in calls or exits fails alone: the
/// session goes on as it was before it. A definition the failed cell
/// made is gone (a later cell that names `f` with its old text links the
/// old `f`, not the failed cell's), so are its changes to an earlier
/// binding's object and to a static, and the thread it started.
#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_survives_failed_cells() {
    let Some(env) = setup() else { return };
    let rokr = env.rokr.display().to_string();
    let input = "\
use rok::bare::ptr::Ptr;
let kept = 7;
fn peek() -> i64 { let p: Ptr<i64> = Ptr::dangling(); unsafe { p.read() } }
peek()
kept + 1
fn down(n: i32) -> i32 { if n == 0 { panic(\"deep\") } else { down(n - 1) + 1 } }
down(50)
kept + 2
rok::std::env::exit(3);
fn f() -> i32 { 1 }
f()
fn f() -> i32 { panic(\"v2\") }
f()
fn f() -> i32 { 1 }
f()
kept + 3
use rok::std::thread;
static C: Atomic<i64> = Atomic::new(0);
let xs = [1, 2, 3];
C.store(1);
xs.push(4); C.store(5); thread::spawn(|| { while true { C.fetch_add(1); } }); thread::sleep(Duration::ms(50)); panic(\"after\");
xs
C.load()
thread::sleep(Duration::ms(200));
C.load()
";
    let out = piped(ROKC, &["repl", "--rokr", &rokr], input);
    let stderr = text(&out.stderr);
    assert_eq!(
        text(&out.stdout),
        "i32: 8\ni32: 9\ni32: 1\ni32: 1\ni32: 10\nList<i32>: [1, 2, 3]\ni64: 1\ni64: 1\n",
        "stderr: {stderr}"
    );
    assert_eq!(
        stderr.matches("error: the cell failed").count(),
        5,
        "{stderr}"
    );
    assert!(stderr.contains("deep") && stderr.contains("v2"), "{stderr}");
}

/// Threads from earlier cells and a failed cell: the task executor's
/// threads (started by earlier cells, some of them running the failed
/// cell's tasks) serve later cells, and a thread that was running while
/// the cell failed is gone (its join says so).
#[test]
#[cfg_attr(
    not(any(
        all(
            any(target_os = "macos", target_os = "linux"),
            any(target_arch = "aarch64", target_arch = "x86_64")
        ),
        windows
    )),
    ignore = "the REPL host runs on macOS, Linux and Windows (arm64, x86_64)"
)]
fn repl_threads_after_a_failed_cell() {
    let Some(env) = setup() else { return };
    let rokr = env.rokr.display().to_string();
    let input = "\
use rok::core::task;
use rok::std::thread;
task::block_on(async { let t = task::spawn(async { 20 + 1 }); await t })
task::block_on(async { await task::spawn_blocking(|| 7) })
task::block_on(async { let t = task::spawn(async { 5 }); await t }); panic(\"in the middle\");
task::block_on(async { let t = task::spawn(async { 40 + 2 }); await t })
task::block_on(async { await task::spawn_blocking(|| 8) })
let h = thread::spawn(|| { let n: i64 = 0; while n >= 0 { n += 1; } n });
thread::sleep(Duration::ms(100)); panic(\"busy\");
let j = try h.join() catch e { println(f\"{e}\"); -1i64 };
j
task::block_on(async { let ts = [task::spawn(async { 1 }), task::spawn(async { 2 })]; let s = 0; for t in ts { s += await t; } s })
";
    let out = piped(ROKC, &["repl", "--rokr", &rokr], input);
    let stdout = text(&out.stdout);
    let stderr = text(&out.stderr);
    assert_eq!(
        stdout,
        "i32: 21\ni32: 7\ni32: 42\ni32: 8\nthread join failed: the thread ended with a failed REPL cell\ni64: -1\ni32: 3\n",
        "stderr: {stderr}"
    );
    assert_eq!(
        stderr.matches("error: the cell failed").count(),
        2,
        "{stderr}"
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

/// The server builds its dependencies first and answers from their RHIR:
/// hover shows a dependency function's doc comment, definition goes to
/// its source.
#[test]
fn lsp_sees_prebuilt_dependencies() {
    let Some(env) = setup() else { return };
    let dir = scratch("lsp-deps");
    let (util, app) = (dir.join("util"), dir.join("app"));
    std::fs::create_dir_all(&util).unwrap();
    std::fs::create_dir_all(&app).unwrap();
    std::fs::write(
        util.join("lib.rok"),
        "/// Says hi.\npub fn hello() -> i32 {\n    return 1;\n}\n",
    )
    .unwrap();
    let main = app.join("main.rok");
    let src = "use util::hello;\nlet x = hello();\nprintln(f\"{x}\");\n";
    std::fs::write(&main, src).unwrap();
    let uri = format!("file://{}", main.display());
    let doc = format!(r#"{{"uri":"{uri}","languageId":"rok","version":1,"text":{src:?}}}"#);
    let at =
        format!(r#"{{"textDocument":{{"uri":"{uri}"}},"position":{{"line":1,"character":10}}}}"#);
    let input = [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#.to_owned(),
        format!(r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{doc}}}}}"#),
        format!(r#"{{"jsonrpc":"2.0","id":2,"method":"textDocument/hover","params":{at}}}"#),
        format!(r#"{{"jsonrpc":"2.0","id":3,"method":"textDocument/definition","params":{at}}}"#),
        r#"{"jsonrpc":"2.0","id":4,"method":"shutdown"}"#.to_owned(),
        r#"{"jsonrpc":"2.0","method":"exit"}"#.to_owned(),
    ]
    .map(|m| frame(&m))
    .concat();
    let ext = format!("util={}", util.display());
    let mut child = Command::new(ROKC)
        .current_dir(&app)
        .env("ROK_HOME", workspace())
        .args(["lsp", "--extern", &ext, "--rokr"])
        .arg(&env.rokr)
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
    let out = child.wait_with_output().unwrap();
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    assert!(app.join("target/debug/deps/util.rhir").is_file());
    let stdout = text(&out.stdout);
    let reply = |id: u32| {
        let at = stdout
            .find(&format!(r#""id":{id},"#))
            .unwrap_or_else(|| panic!("{stdout}"));
        stdout[at..]
            .split("Content-Length")
            .next()
            .unwrap()
            .to_owned()
    };
    assert!(reply(2).contains("Says hi."), "{stdout}");
    let def = reply(3);
    let want = format!("file://{}", util.join("lib.rok").display());
    assert!(def.contains(&want), "{def}");
    assert!(def.contains(r#""start":{"line":1,"#), "{def}");
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
#[cfg_attr(
    not(all(
        any(target_os = "macos", target_os = "linux"),
        any(target_arch = "aarch64", target_arch = "x86_64")
    )),
    ignore = "the REPL host runs on macOS and Linux, arm64 and x86_64"
)]
fn jupyter_kernel_speaks_the_wire_protocol() {
    use rokc_interface::Json;
    use rokc_tools::jupyter::{encode, handshake, parse_msg, read_msg, write_msg};
    use std::net::{TcpListener, TcpStream};
    use std::time::Duration;

    let env = setup_runtime();
    let key = b"secret-key";
    let dir = std::env::temp_dir().join(format!("rok_jupyter_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("kernel.json");
    // The kernel says `ready` on stderr once every socket accepts. A
    // probed port can be taken again before the kernel binds it (it then
    // exits instead): start over on fresh ports.
    let mut attempts = 0;
    let (kernel, ports, mut stderr) = loop {
        let listeners: Vec<_> = (0..5)
            .map(|_| TcpListener::bind("127.0.0.1:0").unwrap())
            .collect();
        let ports: Vec<u16> = listeners
            .iter()
            .map(|l| l.local_addr().unwrap().port())
            .collect();
        drop(listeners);
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
        let mut kernel = Command::new(ROKC)
            .args(["jupyter", "--connection-file"])
            .arg(&file)
            .args(["--rokr", &env.rokr.display().to_string()])
            .env("ROK_HOME", workspace())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stderr = BufReader::new(kernel.stderr.take().unwrap());
        let mut said = String::new();
        stderr.read_line(&mut said).unwrap();
        if said == "rokc jupyter: ready\n" {
            break (kernel, ports, stderr);
        }
        kernel.wait().unwrap();
        attempts += 1;
        assert!(attempts < 5, "the kernel exits: {said}");
    };
    let connect = |port: u16, kind: &str| {
        let mut s = TcpStream::connect(("127.0.0.1", port)).unwrap();
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

    // The kernel adds a subscriber on its own thread after the handshake
    // and publishes nothing to it before (ZeroMQ's slow joiner): send
    // `kernel_info_request` until iopub has something. (`request` skips
    // what these probes publish.)
    iopub
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();
    let deadline = std::time::Instant::now() + Duration::from_secs(60);
    loop {
        let probe = encode(
            key,
            "test",
            &[],
            "kernel_info_request",
            &Json::obj([]),
            &Json::obj([]),
        );
        write_msg(&mut shell, &probe).unwrap();
        read_msg(&mut shell).unwrap();
        if iopub.peek(&mut [0u8]).is_ok_and(|n| n > 0) {
            break;
        }
        assert!(
            std::time::Instant::now() < deadline,
            "nothing on iopub after 60s"
        );
    }
    iopub
        .set_read_timeout(Some(Duration::from_secs(120)))
        .unwrap();

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

    completion_inspect_history(&mut shell, &mut request);

    let (kind, _, _) = request(
        &mut control,
        "shutdown_request",
        Json::obj([("restart", Json::Bool(false))]),
    );
    assert_eq!(kind, "shutdown_reply");
    let out = kernel.wait_with_output().unwrap();
    let mut rest = String::new();
    stderr.read_to_string(&mut rest).unwrap();
    assert!(out.status.success(), "{rest}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A REPL message: (reply kind, reply content, iopub messages).
type Reply = (
    String,
    rokc_interface::Json,
    Vec<(String, rokc_interface::Json)>,
);

/// `complete` / `is_complete` / `inspect` / `history` against the
/// session of `jupyter_kernel_speaks_the_wire_protocol` (`x: i32`, five
/// cells run).
fn completion_inspect_history(
    shell: &mut std::net::TcpStream,
    request: &mut impl FnMut(&mut std::net::TcpStream, &str, rokc_interface::Json) -> Reply,
) {
    use rokc_interface::Json;
    let (_, reply, _) = request(
        shell,
        "is_complete_request",
        Json::obj([("code", Json::str("fn f() {"))]),
    );
    assert_eq!(reply.get("status").as_str(), Some("incomplete"));
    let (_, reply, _) = request(
        shell,
        "complete_request",
        Json::obj([("code", Json::str("1 + x")), ("cursor_pos", Json::num(5))]),
    );
    assert_eq!(
        reply.get("matches"),
        &Json::Arr(vec![Json::str("x")]),
        "{reply}"
    );
    assert_eq!(reply.get("cursor_start"), &Json::num(4));
    let (_, reply, _) = request(
        shell,
        "complete_request",
        Json::obj([("code", Json::str("whi")), ("cursor_pos", Json::num(3))]),
    );
    assert_eq!(
        reply.get("matches"),
        &Json::Arr(vec![Json::str("while")]),
        "{reply}"
    );
    let inspect = |pos: u32| {
        Json::obj([
            ("code", Json::str("1 + x + nope")),
            ("cursor_pos", Json::num(pos)),
            ("detail_level", Json::num(0)),
        ])
    };
    let (kind, reply, _) = request(shell, "inspect_request", inspect(4));
    assert_eq!(kind, "inspect_reply");
    assert_eq!(reply.get("found"), &Json::Bool(true), "{reply}");
    assert_eq!(reply.get("data").get("text/plain").as_str(), Some("x: i32"));
    let (_, reply, _) = request(shell, "inspect_request", inspect(10));
    assert_eq!(reply.get("found"), &Json::Bool(false), "{reply}");
    let (_, reply, _) = request(
        shell,
        "history_request",
        Json::obj([
            ("hist_access_type", Json::str("tail")),
            ("n", Json::num(2)),
            ("output", Json::Bool(false)),
            ("raw", Json::Bool(true)),
        ]),
    );
    assert_eq!(
        reply.get("history"),
        &Json::Arr(vec![
            Json::Arr(vec![
                Json::num(0),
                Json::num(4),
                Json::str("panic(\"boom\");")
            ]),
            Json::Arr(vec![Json::num(0), Json::num(5), Json::str("x")]),
        ]),
        "{reply}"
    );

    // Members, paths and doc comments (9.8.5 / 9.8.6).
    let code = "struct P { x: i32; y: i32; }\n\
                impl P {\n    /// Sum of the coordinates.\n    fn sum(self) -> i32 { self.x + self.y }\n}";
    let exec = Json::obj([("code", Json::str(code)), ("silent", Json::Bool(false))]);
    let (_, reply, _) = request(shell, "execute_request", exec);
    assert_eq!(reply.get("status").as_str(), Some("ok"), "{reply}");
    let complete = |code: &str| {
        Json::obj([
            ("code", Json::str(code)),
            ("cursor_pos", Json::num(code.chars().count() as u32)),
        ])
    };
    let (_, reply, _) = request(
        shell,
        "complete_request",
        complete("let p = P { x: 1, y: 2 };\np.s"),
    );
    assert_eq!(
        reply.get("matches"),
        &Json::Arr(vec![Json::str("sum")]),
        "{reply}"
    );
    assert_eq!(reply.get("cursor_start"), &Json::num(28));
    let (_, reply, _) = request(
        shell,
        "complete_request",
        complete("let p = P { x: 1, y: 2 };\np."),
    );
    for m in ["x", "y", "sum"] {
        assert!(reply.get("matches").to_string().contains(m), "{reply}");
    }
    let (_, reply, _) = request(shell, "complete_request", complete("P::"));
    assert!(
        reply.get("matches").to_string().contains("\"sum\""),
        "{reply}"
    );
    let code = "let p = P { x: 1, y: 2 };\np.sum()";
    let (_, reply, _) = request(
        shell,
        "inspect_request",
        Json::obj([
            ("code", Json::str(code)),
            ("cursor_pos", Json::num(28)),
            ("detail_level", Json::num(0)),
        ]),
    );
    assert_eq!(
        reply.get("data").get("text/plain").as_str(),
        Some("fn sum(self: P) -> i32\n\nSum of the coordinates."),
        "{reply}"
    );
}

//! Shared plumbing of the `rokc` integration tests, and the directives of
//! the `.rok` cases (`integration.rs`), read from `//` comment lines:
//!   - `// expect-exit: N`      — runtime exit code
//!   - `// expect-stdout: text` — single-line stdout, or an empty value
//!     followed by `// line` comments for a multi-line block (none:
//!     empty stdout); required of every case that runs
//!   - `// expect-error: text`  — build must fail and stderr must contain `text`
//!   - `// forbid-error: text`  — (repeatable) that failed build's stderr must
//!     not contain `text`
//!   - `// expect-warning: text` — (repeatable) build stderr must contain `text`
//!   - `// forbid-warning: text` — (repeatable) build stderr must not contain `text`
//!   - `// expect-stderr: text` — (repeatable) the run's stderr, one
//!     directive per line, leading and trailing blanks aside (`\` read
//!     as `/`, library paths relative to the workspace); none: empty stderr
//!   - `// debug-only`          — skipped under `ROK_TEST_OPT` (e.g.
//!     overflow panics, which only `-O0` checks)
//!   - `// gc-stress: N`        — run twice more, with
//!     `ROK_GC_STRESS=N ROK_GC_EVAC=always` and with
//!     `ROK_GC_STRESS=N ROK_GC_EVAC=always ROK_GC_CONCURRENT=always`,
//!     same expectations
//!   - `// rokc-arg: args`      — extra `rokc` arguments (`--cfg feat`)
//!   - `// only-os: macos linux` — skipped unless the target's `target_os`
//!     is listed (POSIX commands, paths, signals)
//!   - `// only-pointer-width: 64` — skipped on targets of another width
//!     (sizes, `usize::BITS`, layouts in the expected output)
//!   - `// needs: threads net process fs posix-fs` — skipped on a
//!     target without one of them: threads only on `wasm32-wasi-threads`
//!     among the wasm32 targets, sockets only on `wasm32-wasi`, no
//!     processes or signals on wasm32 (stdlib 0.1.4, 3.x availability;
//!     `process` also covers POSIX C calls), a browser no file system
//!     (`fs`), WASI no `dup` / `flock` / `mmap` (`posix-fs`)
//!   - `// only-target: wasm32-wasi ..` — run only on the listed
//!     `ROK_TEST_TARGET`s (what one target reports that the others do
//!     not, e.g. its `Unsupported` APIs)
//!   - `// wasm-invoke: f(1, "a") => 2` — (repeatable) after the run, the
//!     component's export `f` called through `wasmtime run --invoke`
//!     (WAVE syntax) prints the value after `=>`
//!   - `// wasm-reactor` — a component without `wasi:cli/run`: not run,
//!     only its `wasm-invoke`s
//!   - `// wasm-plug: dir/main.rok` — that program is built too and
//!     `wac plug` (`ROK_TEST_WAC`; the case is skipped without it)
//!     satisfies the case's imports with its exports; the composition
//!     runs
//!   - `// spec: <section>`     — the spec section a case checks (a tag)
//!
//! Environment:
//!   - `ROK_REQUIRE_LLVM=1` — a rokc built without LLVM is a failure
//!     instead of a skip (CI sets this).
//!   - `ROK_TEST_OPT=-O2` (or `--release`, `-O3`, ...) — build every case
//!     at that optimization level instead of the default `-O0`.
//!   - `ROK_TEST_FILTER=text` — only the integration cases whose name
//!     contains `text`.
//!   - `ROK_TEST_TARGET=<triple>` — build for that target (with a runtime
//!     built for it), e.g. `x86_64-apple-darwin` run under Rosetta.
//!     `wasm32-wasi` and `wasm32-wasi-threads` run each module with
//!     `ROK_TEST_WASM_RUNNER` (a `wasmtime` that still has wasi-threads:
//!     46.0.3, the last);
//!     `wasm32-unknown-unknown` with `node` and the toolchain's `rok.mjs`
//!     host (all need `targets/build.sh <triple>` for the C library).
#![allow(dead_code)]

use std::env;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

use rokc_target::{Linker, ObjectFormat, TargetSpec};

pub const ROKC: &str = env!("CARGO_BIN_EXE_rokc");

/// The repository root (`compiler/rokc/../..`).
pub fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// A fresh, empty scratch directory for this test binary.
pub fn scratch(name: &str) -> PathBuf {
    static PRUNE: std::sync::Once = std::sync::Once::new();
    PRUNE.call_once(prune_scratch);
    let dir = env::temp_dir().join(format!("rokc-test-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Scratch directories of runs that ended (killed, failed, or never
/// cleaned) are removed once they are three hours old.
fn prune_scratch() {
    let Ok(entries) = std::fs::read_dir(env::temp_dir()) else {
        return;
    };
    let stale = std::time::Duration::from_secs(3 * 3600);
    for e in entries.flatten() {
        let old = e
            .metadata()
            .and_then(|m| m.modified())
            .is_ok_and(|t| t.elapsed().is_ok_and(|a| a > stale));
        if old && e.file_name().to_string_lossy().starts_with("rokc-test-") {
            let _ = std::fs::remove_dir_all(e.path());
        }
    }
}

pub fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

#[track_caller]
pub fn assert_exit(out: &Output, code: i32) {
    assert_eq!(
        out.status.code(),
        Some(code),
        "stdout: {}\nstderr: {}",
        text(&out.stdout),
        text(&out.stderr)
    );
}

pub struct Env {
    pub workspace: PathBuf,
    pub bootstrap: PathBuf,
    pub rokr: PathBuf,
}

/// Locate the workspace, rebuild `librokr.a`, and check the LLVM toolchain.
/// Returns `None` when the suite should be skipped.
pub fn setup() -> Option<Env> {
    if !llvm_present() {
        let msg = "rokc is built without LLVM (ROK_LLVM_PREFIX, llvm/build.sh)";
        assert!(
            env::var("ROK_REQUIRE_LLVM").as_deref() != Ok("1"),
            "ROK_REQUIRE_LLVM=1 but {msg}"
        );
        // Write straight to the stderr handle: `eprintln!` is swallowed by
        // libtest's capture for passing tests.
        let _ = writeln!(
            std::io::stderr(),
            "\n!!!!!!!! SKIPPED: {msg} — .rok end-to-end cases NOT run !!!!!!!!\n"
        );
        return None;
    }
    Some(setup_runtime())
}

/// `setup` for what runs without LLVM (`-O0` through the native
/// backend: REPL cells).
pub fn setup_runtime() -> Env {
    let workspace = std::fs::canonicalize(workspace()).unwrap();
    let bootstrap = workspace.join("library/core/lib.rok");
    assert!(bootstrap.exists(), "missing {bootstrap:?}");

    // `cargo test` doesn't rebuild the staticlib on its own (rokc must not
    // depend on rokr), so build it here to never link a stale runtime.
    // Once per test binary: parallel tests rebuilding it at the same time
    // race on the archive file.
    #[allow(clippy::items_after_statements)]
    static BUILT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let ok = *BUILT.get_or_init(|| {
        let cargo = env::var("CARGO").unwrap_or_else(|_| "cargo".into());
        Command::new(cargo)
            .args(["build", "-p", "rokr"])
            .args(rust_target().map(|t| format!("--target={t}")))
            .current_dir(&workspace)
            .status()
            .expect("spawn cargo build -p rokr")
            .success()
    });
    assert!(ok, "cargo build -p rokr failed");
    let target =
        env::var_os("CARGO_TARGET_DIR").map_or_else(|| workspace.join("target"), PathBuf::from);
    let rokr = target
        .join(rust_target().unwrap_or_default())
        .join("debug")
        .join(spec().runtime_lib());
    assert!(rokr.exists(), "missing {rokr:?} after cargo build -p rokr");

    Env {
        workspace,
        bootstrap,
        rokr,
    }
}

/// `rokc version -v` names the LLVM it links (`llvm: none`: built
/// without one).
fn llvm_present() -> bool {
    Command::new(ROKC)
        .args(["version", "-v"])
        .output()
        .is_ok_and(|o| !String::from_utf8_lossy(&o.stdout).contains("llvm: none"))
}

/// Scratch-directory suffix, so runs at different `ROK_TEST_OPT` levels
/// don't share build outputs.
pub fn opt_suffix() -> String {
    env::var("ROK_TEST_OPT").unwrap_or_default()
}

/// Built above `-O0` (`ROK_TEST_OPT`).
pub fn optimized() -> bool {
    !matches!(opt_suffix().as_str(), "" | "-O0")
}

/// `rokc build <src> -o <exe>` with the harness bootstrap + runtime.
pub fn rokc_build(env: &Env, src: &Path, exe: &Path) -> std::io::Result<Output> {
    let source = std::fs::read_to_string(src).unwrap_or_default();
    Command::new(ROKC)
        .args(directives(&source, "rokc-arg:").flat_map(str::split_whitespace))
        .arg("build")
        .arg(src)
        .arg("--bootstrap")
        .arg(&env.bootstrap)
        .arg("--bootstrap")
        .arg(env.workspace.join("library/std/lib.rok"))
        .arg("--bootstrap")
        .arg(env.workspace.join("library/bare/lib.rok"))
        .arg("--rokr")
        .arg(&env.rokr)
        .args(env::var("ROK_TEST_OPT").ok().filter(|o| !o.is_empty()))
        .args(test_target().map(|t| format!("--target={t}")))
        // Prebuilt `--extern`s go beside the case's output.
        .arg("--target-dir")
        .arg(exe.with_file_name("target"))
        .arg("-o")
        .arg(exe)
        .output()
}

/// `ROK_TEST_TARGET`: the target to build the cases for.
pub fn test_target() -> Option<String> {
    env::var("ROK_TEST_TARGET").ok().filter(|t| !t.is_empty())
}

/// The cases' target (`ROK_TEST_TARGET`, else the host).
pub fn spec() -> TargetSpec {
    TargetSpec::resolve(test_target().as_deref()).unwrap()
}

/// The Rust target the runtime is built for (WASI preview 2 for
/// `wasm32-wasi`, ...); `None` for the host.
pub fn rust_target() -> Option<String> {
    test_target().map(|_| spec().rust_target)
}

/// The cases are built for wasm32.
pub fn wasm() -> bool {
    spec().object_format == ObjectFormat::Wasm
}

/// The OS the cases are built for, as `target_os` names it.
pub fn target_os() -> String {
    spec().os
}

/// The pointer width of the cases' target, in bits.
pub fn target_pointer_width() -> u32 {
    spec().pointer_width
}

/// A case's `// only-os: <os> ..` excludes the target's OS, its
/// `// only-pointer-width: <bits>` the target's width, its `// needs:`
/// something the target lacks.
pub fn skipped_on_target(source: &str) -> bool {
    directive(source, "only-os:").is_some_and(|oses| {
        let os = target_os();
        !oses.split_whitespace().any(|o| o == os)
    }) || directive(source, "only-pointer-width:")
        .is_some_and(|w| w.trim() != target_pointer_width().to_string())
        || directive(source, "needs:").is_some_and(|needs| needs.split_whitespace().any(lacks))
        || directive(source, "only-target:").is_some_and(|ts| {
            let t = test_target().unwrap_or_default();
            !ts.split_whitespace().any(|x| x == t)
        })
}

/// The cases' target lacks `// needs:` capability `need`.
fn lacks(need: &str) -> bool {
    let t = spec();
    match need {
        "threads" => !t.threads,
        "process" | "posix-fs" => wasm(),
        // Sockets: WASI preview 2 (a component).
        "net" => wasm() && t.linker != Linker::WasmComponentLd,
        "fs" => t.reactor(),
        _ => panic!("unknown `// needs: {need}`"),
    }
}

/// A run's exit code `got` is the expected one. A `wasm32-wasi`
/// component exits through `wasi:cli/exit`, which carries only success
/// or failure (1); wasmtime fails (1) a preview 1 module's exit with a
/// code of 126 or more (a trap, such as `abort`'s, still gives 134).
pub fn exit_matches(got: i32, expected: i32) -> bool {
    let t = spec();
    if t.linker == Linker::WasmComponentLd {
        got == i32::from(expected != 0)
    } else if wasm() && !t.reactor() {
        got == expected || (expected >= 126 && got == 1)
    } else {
        got == expected
    }
}

/// File name of executable `name` for the cases' target.
pub fn exe_name(name: &str) -> String {
    format!("{name}{}", spec().exe_suffix)
}

/// A command running the built program `exe`: itself, or a wasm module
/// under `wasmtime` (`ROK_TEST_WASM_RUNNER`; the host's environment and
/// file system, the engine stack as deep as a native main thread's) or
/// `node` with the toolchain's `rok.mjs`.
pub fn run_command(exe: &Path) -> Command {
    let t = spec();
    match t.object_format {
        ObjectFormat::Wasm if t.linker == Linker::WasmComponentLd => {
            let runner = env::var_os("ROK_TEST_WASM_RUNNER")
                .expect("ROK_TEST_TARGET=wasm32-wasi needs ROK_TEST_WASM_RUNNER (wasmtime)");
            let mut c = Command::new(runner);
            c.args([
                "run",
                "-S",
                "inherit-env",
                "-S",
                "inherit-network",
                "-S",
                "allow-ip-name-lookup",
                "-W",
                "max-wasm-stack=8388608",
                "-W",
                COMPONENT_FEATURES,
                "--dir",
                "/::/",
            ])
            .arg(exe);
            c
        }
        ObjectFormat::Wasm if !t.reactor() => {
            let runner = env::var_os("ROK_TEST_WASM_RUNNER").expect(
                "ROK_TEST_TARGET=wasm32-wasi-threads needs ROK_TEST_WASM_RUNNER (wasmtime)",
            );
            let mut c = Command::new(runner);
            c.args([
                "run",
                "-W",
                "threads=y,shared-memory=y",
                "-S",
                "threads=y",
                "-S",
                "inherit-env",
                "-W",
                "max-wasm-stack=8388608",
                "--dir",
                "/::/",
            ])
            .arg(exe);
            c
        }
        ObjectFormat::Wasm => {
            let host = workspace().join("targets/rok.mjs");
            let mut c = Command::new("node");
            c.arg("--stack-size=8000").arg(host).arg(exe);
            c
        }
        _ => Command::new(exe),
    }
}

/// `wasmtime run --invoke <call> <exe>`: export `call` of the component
/// `exe` (`ROK_TEST_WASM_RUNNER`), without running `main`.
pub fn invoke_command(exe: &Path, call: &str) -> Command {
    let runner = env::var_os("ROK_TEST_WASM_RUNNER")
        .expect("`// wasm-invoke:` needs ROK_TEST_WASM_RUNNER (wasmtime)");
    let mut c = Command::new(runner);
    c.args(["run", "-W", COMPONENT_FEATURES, "--invoke", call])
        .arg(exe);
    c
}

/// The component model features `wasm32-wasi` components may use beyond
/// what wasmtime enables by default (async is on).
const COMPONENT_FEATURES: &str =
    "component-model-fixed-length-lists=y,component-model-error-context=y";

/// Run `f` over `items` on all cores; results keep input order.
pub fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let workers = thread::available_parallelism().map_or(4, std::num::NonZero::get);
    let next = AtomicUsize::new(0);
    let mut out: Vec<(usize, R)> = thread::scope(|s| {
        // Collect first so every worker is spawned before any join.
        #[allow(clippy::needless_collect)]
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                s.spawn(|| {
                    let mut local = Vec::new();
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        let Some(item) = items.get(i) else { break };
                        local.push((i, f(item)));
                    }
                    local
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect()
    });
    out.sort_by_key(|(i, _)| *i);
    out.into_iter().map(|(_, r)| r).collect()
}

/// Values after `// <key>` on every matching line.
pub fn directives<'a>(source: &'a str, key: &'a str) -> impl Iterator<Item = &'a str> {
    source
        .lines()
        .filter_map(move |l| l.trim_start().strip_prefix("// ")?.strip_prefix(key))
        .map(str::trim)
}

/// Value after `// <key>` on the first matching line.
pub fn directive<'a>(source: &'a str, key: &str) -> Option<&'a str> {
    source
        .lines()
        .find_map(|l| l.trim_start().strip_prefix("// ")?.strip_prefix(key))
        .map(str::trim)
}

pub fn parse_expect_exit(source: &str) -> Option<i32> {
    directive(source, "expect-exit:")?.parse().ok()
}

pub fn parse_expect_error(source: &str) -> Option<&str> {
    directive(source, "expect-error:")
}

/// `None` = no stdout check. Multi-line form: `// expect-stdout:` followed by
/// `// <line>` / `//` comment lines.
pub fn parse_expect_stdout(source: &str) -> Option<String> {
    let mut lines = source.lines();
    while let Some(line) = lines.next() {
        let Some(rest) = line.trim_start().strip_prefix("// expect-stdout:") else {
            continue;
        };
        let rest = rest.trim();
        if !rest.is_empty() {
            return Some(rest.to_owned());
        }
        let mut out = String::new();
        for l in lines {
            let t = l.trim_start();
            if let Some(content) = t.strip_prefix("// ") {
                out.push_str(content);
            } else if t != "//" {
                break;
            }
            out.push('\n');
        }
        return Some(out);
    }
    None
}

/// `stderr` plus one `path:line:col: message` line per rendered
/// diagnostic (`error[E..]: message` over `--> path:line:col`), so an
/// expectation can pin a message to its location.
pub fn flatten_diagnostics(stderr: &str) -> String {
    let mut out = stderr.to_owned();
    let lines: Vec<&str> = stderr.lines().collect();
    for w in lines.windows(2) {
        let msg = w[0].split_once("]: ").map(|(_, m)| m);
        let loc = w[1].trim_start().strip_prefix("--> ");
        if let (Some(msg), Some(loc)) = (msg, loc) {
            out.push_str(&format!("\n{loc}: {msg}"));
        }
    }
    out
}

/// Check a failed build's stderr against every `// expect-error:` and
/// `// forbid-error:`.
pub fn check_expect_error(source: &str, stderr: &str) -> Result<(), String> {
    let stderr = &flatten_diagnostics(stderr);
    if let Some(unwanted) = directives(source, "forbid-error:").find(|w| stderr.contains(w)) {
        return Err(format!("build stderr has error {unwanted:?}"));
    }
    match directives(source, "expect-error:").find(|want| !stderr.contains(want)) {
        Some(want) => Err(format!(
            "build failed but stderr lacks expect-error {want:?}\n    stderr: {:?}",
            stderr
                .lines()
                .find(|l| l.starts_with("error"))
                .unwrap_or_else(|| stderr.trim())
        )),
        None => Ok(()),
    }
}

/// Deterministic PRNG (splitmix64) for the fuzz and differential tests.
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n` (`n > 0`).
    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    /// True with probability `pct`%.
    pub fn chance(&mut self, pct: u64) -> bool {
        self.next() % 100 < pct
    }

    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }

    /// Uniform in `lo..=hi`.
    pub fn range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = hi.wrapping_sub(lo) as u64;
        let r = if span == u64::MAX {
            self.next()
        } else {
            self.next() % (span + 1)
        };
        lo.wrapping_add(r as i64)
    }
}

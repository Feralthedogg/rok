//! Shared plumbing of the `rokc` integration tests, and the directives of
//! the `.rok` cases (`integration.rs`), read from `//` comment lines:
//!   - `// expect-exit: N`      — runtime exit code
//!   - `// expect-stdout: text` — single-line stdout, or an empty value
//!     followed by `// line` comments for a multi-line block
//!   - `// expect-error: text`  — build must fail and stderr must contain `text`
//!   - `// expect-warning: text` — (repeatable) build stderr must contain `text`
//!   - `// forbid-warning: text` — (repeatable) build stderr must not contain `text`
//!   - `// expect-stderr: text` — (repeatable) the run's stderr must contain `text`
//!   - `// debug-only`          — skipped under `ROK_TEST_OPT` (e.g.
//!     overflow panics, which only `-O0` checks)
//!   - `// gc-stress: N`        — run twice more, with
//!     `ROK_GC_STRESS=N ROK_GC_EVAC=always` and with
//!     `ROK_GC_STRESS=N ROK_GC_EVAC=always ROK_GC_CONCURRENT=always`,
//!     same expectations
//!   - `// rokc-arg: args`      — extra `rokc` arguments (`--cfg feat`)
//!   - `// spec: <section>`     — the spec section a case checks (a tag)
//!
//! Environment:
//!   - `ROK_REQUIRE_LLVM=1` — a rokc built without LLVM is a failure
//!     instead of a skip (CI sets this).
//!   - `ROK_TEST_OPT=-O2` (or `--release`, `-O3`, ...) — build every case
//!     at that optimization level instead of the default `-O0`.
//!   - `ROK_TEST_TARGET=<triple>` — build for that target (with a runtime
//!     built for it), e.g. `x86_64-apple-darwin` run under Rosetta.
#![allow(dead_code)]

use std::env;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

pub const ROKC: &str = env!("CARGO_BIN_EXE_rokc");

/// The repository root (`compiler/rokc/../..`).
pub fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// A fresh, empty scratch directory for this test binary.
pub fn scratch(name: &str) -> PathBuf {
    let dir = env::temp_dir().join(format!("rokc-test-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
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
    let workspace = std::fs::canonicalize(workspace()).unwrap();
    let bootstrap = workspace.join("library/core/lib.rok");
    assert!(bootstrap.exists(), "missing {bootstrap:?}");

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
            .args(test_target().map(|t| format!("--target={t}")))
            .current_dir(&workspace)
            .status()
            .expect("spawn cargo build -p rokr")
            .success()
    });
    assert!(ok, "cargo build -p rokr failed");
    let target =
        env::var_os("CARGO_TARGET_DIR").map_or_else(|| workspace.join("target"), PathBuf::from);
    let rokr = target
        .join(test_target().unwrap_or_default())
        .join("debug/librokr.a");
    assert!(rokr.exists(), "missing {rokr:?} after cargo build -p rokr");

    Some(Env {
        workspace,
        bootstrap,
        rokr,
    })
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
        .arg("-o")
        .arg(exe)
        .output()
}

/// `ROK_TEST_TARGET`: the target to build the cases for.
pub fn test_target() -> Option<String> {
    env::var("ROK_TEST_TARGET").ok().filter(|t| !t.is_empty())
}

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

/// Check a failed build's stderr against every `// expect-error:`.
pub fn check_expect_error(source: &str, stderr: &str) -> Result<(), String> {
    let stderr = &flatten_diagnostics(stderr);
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

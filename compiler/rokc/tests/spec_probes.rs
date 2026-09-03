//! Spec audit harness: each probe asserts what spec says should happen.
//!
//! `audit/probes/*.rok` carries metadata in leading `//` comments:
//!   - `// spec: <id>`            — spec section (informational)
//!   - `// probe: <kind>`         — expected outcome class
//!   - `// expect-exit: N`        — runtime exit code (positive probes)
//!   - `// expect-stdout:`        — multi-line stdout block (positive probes)
//!
//! Probe kinds:
//!   - `positive`                 — must build + run + match expect-*
//!   - `positive-parse-only`      — must build (no run check)
//!   - `negative-must-fail`       — must fail at any compile stage
//!   - `negative-must-fail-parse` — must fail specifically at parse stage
//!   - `measure`                  — informational, never fails the suite
//!
//! `measure` probes record current behaviour without asserting it; they
//! exist to flag silent drift — when their outcome shifts, someone should
//! decide whether spec or impl needs updating.
//!
//! Known-gap probes carry an extra `// xfail: <reason>` directive. The
//! harness inverts the assertion: the suite passes if the probe still
//! fails, and fails (with a "remove xfail" message) the moment someone's
//! fix makes the probe start passing. This keeps the corpus green for
//! known stage-1 gaps while still signalling progress.
//!
//! Skips silently if the LLVM toolchain isn't on PATH (same as
//! integration.rs). The probe corpus is meant to grow alongside the spec.
//! When a probe's outcome shifts, either spec or impl must be updated to
//! restore alignment.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const ROKC: &str = env!("CARGO_BIN_EXE_rokc");
const MANIFEST_DIR: &str = env!("CARGO_MANIFEST_DIR");

#[test]
fn spec_probes() {
    let manifest = PathBuf::from(MANIFEST_DIR);
    let workspace = manifest.parent().and_then(Path::parent).unwrap();
    let bootstrap = workspace.join("library/core/lib.rok");
    let rokr = workspace.join("target/debug/librokr.a");
    let probes_dir = workspace.join("audit/probes");

    if !probes_dir.exists() {
        eprintln!("skip: audit/probes/ not found");
        return;
    }
    assert!(bootstrap.exists(), "missing {bootstrap:?}");
    assert!(rokr.exists(), "{rokr:?} not built");

    if locate("mlir-opt").is_none()
        || locate("mlir-translate").is_none()
        || locate("clang").is_none()
    {
        eprintln!("skip: mlir-opt / mlir-translate / clang not on PATH");
        return;
    }

    let scratch = workspace.join("target/probe_tmp");
    let _ = fs::create_dir_all(&scratch);

    let mut failures = Vec::new();
    let mut measurements = Vec::new();
    let mut entries: Vec<_> = fs::read_dir(&probes_dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("rok"))
        .collect();
    entries.sort_by_key(|e| e.path());

    for entry in entries {
        let path = entry.path();
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let source = fs::read_to_string(&path).unwrap();
        let kind = parse_probe_kind(&source).unwrap_or(ProbeKind::Positive);
        let xfail = parse_xfail(&source);

        let outcome = run_probe(&name, &path, &source, kind, &bootstrap, &rokr, &scratch);
        match (xfail.as_deref(), outcome) {
            (Some(_), ProbeOutcome::Fail(reason)) => {
                println!("xfail {name}: {reason}");
            }
            (Some(reason), ProbeOutcome::Pass) => failures.push(format!(
                "{name}: probe now PASSES — remove `// xfail: {reason}` and \
                 update probe_results.md"
            )),
            (Some(_), ProbeOutcome::Measure(detail)) => {
                println!("meas  {name}: {detail}");
                measurements.push(format!("{name} (xfail): {detail}"));
            }
            (None, ProbeOutcome::Pass) => println!("ok    {name}"),
            (None, ProbeOutcome::Measure(detail)) => {
                println!("meas  {name}: {detail}");
                measurements.push(format!("{name}: {detail}"));
            }
            (None, ProbeOutcome::Fail(reason)) => {
                failures.push(format!("{name}: {reason}"));
            }
        }
    }

    if !measurements.is_empty() {
        eprintln!("\n--- measure probes (informational) ---");
        for m in &measurements {
            eprintln!("  {m}");
        }
    }
    if !failures.is_empty() {
        panic!(
            "{} spec probe failures:\n  {}",
            failures.len(),
            failures.join("\n  ")
        );
    }
}

#[derive(Clone, Copy, Debug)]
enum ProbeKind {
    Positive,
    PositiveParseOnly,
    NegativeMustFail,
    NegativeMustFailParse,
    Measure,
}

enum ProbeOutcome {
    Pass,
    Measure(String),
    Fail(String),
}

fn run_probe(
    name: &str,
    path: &Path,
    source: &str,
    kind: ProbeKind,
    bootstrap: &Path,
    rokr: &Path,
    scratch: &Path,
) -> ProbeOutcome {
    let exe = scratch.join(name);
    let _ = fs::remove_file(&exe);

    let build = Command::new(ROKC)
        .arg("build")
        .arg(path)
        .arg("--bootstrap")
        .arg(bootstrap)
        .arg("--rokr")
        .arg(rokr)
        .arg("-o")
        .arg(&exe)
        .output();
    let Ok(build) = build else {
        return ProbeOutcome::Fail("rokc invocation failed".into());
    };

    let stderr = String::from_utf8_lossy(&build.stderr).into_owned();
    if !build.status.success() {
        // Build failed. Classify into parse vs later, then judge against kind.
        let stage = if stderr.contains("[parse]") {
            BuildFail::Parse
        } else {
            BuildFail::Codegen
        };
        return classify_build_fail(kind, stage, &stderr);
    }

    // Build succeeded — judge against kind.
    match kind {
        ProbeKind::NegativeMustFail | ProbeKind::NegativeMustFailParse => {
            ProbeOutcome::Fail("spec violation: build succeeded but probe expected failure".into())
        }
        ProbeKind::PositiveParseOnly => ProbeOutcome::Pass,
        ProbeKind::Measure => {
            // For `measure`, building successfully *is* the measurement.
            // Run it if expect-* is present, but never fail the suite.
            let run = Command::new(&exe).output();
            let detail = match run {
                Ok(out) => format!(
                    "exit={} stdout={:?}",
                    out.status.code().unwrap_or(-1),
                    String::from_utf8_lossy(&out.stdout).trim_end()
                ),
                Err(e) => format!("exec failed: {e}"),
            };
            ProbeOutcome::Measure(detail)
        }
        ProbeKind::Positive => {
            let Ok(run) = Command::new(&exe).output() else {
                return ProbeOutcome::Fail("exec failed".into());
            };
            let actual_exit = run.status.code().unwrap_or(-1);
            let actual_stdout = String::from_utf8_lossy(&run.stdout).into_owned();
            if let Some(want_exit) = parse_expect_exit(source) {
                if actual_exit != want_exit {
                    return ProbeOutcome::Fail(format!(
                        "exit={actual_exit} (want {want_exit})"
                    ));
                }
            }
            if let Some(want) = parse_expect_stdout(source) {
                if actual_stdout.trim_end() != want.trim_end() {
                    return ProbeOutcome::Fail(format!(
                        "stdout mismatch\n    want: {:?}\n    got:  {:?}",
                        want.trim_end(),
                        actual_stdout.trim_end()
                    ));
                }
            }
            ProbeOutcome::Pass
        }
    }
}

#[derive(Clone, Copy)]
enum BuildFail {
    Parse,
    Codegen,
}

fn classify_build_fail(kind: ProbeKind, stage: BuildFail, stderr: &str) -> ProbeOutcome {
    let first_err = stderr
        .lines()
        .find(|l| l.starts_with("error:"))
        .unwrap_or("(no error: line)")
        .chars()
        .take(120)
        .collect::<String>();
    match kind {
        ProbeKind::Positive | ProbeKind::PositiveParseOnly => ProbeOutcome::Fail(format!(
            "build failed at {} stage: {first_err}",
            match stage {
                BuildFail::Parse => "parse",
                BuildFail::Codegen => "codegen+",
            }
        )),
        ProbeKind::NegativeMustFail => ProbeOutcome::Pass,
        ProbeKind::NegativeMustFailParse => match stage {
            BuildFail::Parse => ProbeOutcome::Pass,
            BuildFail::Codegen => ProbeOutcome::Fail(format!(
                "rejected but not at parse stage: {first_err}"
            )),
        },
        ProbeKind::Measure => ProbeOutcome::Measure(format!(
            "build failed at {} stage",
            match stage {
                BuildFail::Parse => "parse",
                BuildFail::Codegen => "codegen+",
            }
        )),
    }
}

fn parse_xfail(source: &str) -> Option<String> {
    for line in source.lines() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("// xfail:") {
            return Some(rest.trim().to_owned());
        }
    }
    None
}

fn parse_probe_kind(source: &str) -> Option<ProbeKind> {
    for line in source.lines() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("// probe:") {
            return Some(match rest.trim() {
                "positive" => ProbeKind::Positive,
                "positive-parse-only" => ProbeKind::PositiveParseOnly,
                "negative-must-fail" => ProbeKind::NegativeMustFail,
                "negative-must-fail-parse" => ProbeKind::NegativeMustFailParse,
                "measure" => ProbeKind::Measure,
                other => panic!("unknown probe kind: {other}"),
            });
        }
    }
    None
}

fn parse_expect_exit(source: &str) -> Option<i32> {
    for line in source.lines() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("// expect-exit:") {
            return rest.trim().parse::<i32>().ok();
        }
    }
    None
}

fn parse_expect_stdout(source: &str) -> Option<String> {
    let mut lines = source.lines().peekable();
    while let Some(line) = lines.next() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("// expect-stdout:") {
            let rest = rest.trim();
            if !rest.is_empty() {
                return Some(rest.to_owned());
            }
            let mut out = String::new();
            while let Some(&peek) = lines.peek() {
                let pt = peek.trim_start();
                if let Some(content) = pt.strip_prefix("// ") {
                    out.push_str(content);
                    out.push('\n');
                    lines.next();
                } else if pt == "//" {
                    out.push('\n');
                    lines.next();
                } else {
                    break;
                }
            }
            return Some(out);
        }
    }
    None
}

fn locate(name: &str) -> Option<PathBuf> {
    let path = env::var_os("PATH")?;
    for dir in env::split_paths(&path) {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

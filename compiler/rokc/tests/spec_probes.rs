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
//! Negative probes may carry `// expect-error: <substring>`; the build's
//! stderr must then contain it, so a probe can't pass by failing for an
//! unrelated reason. Shared directives / LLVM gating: `common/mod.rs`.

mod common;

use std::fs;
use std::path::Path;
use std::process::Command;

use common::*;

#[test]
fn spec_probes() {
    let Some(env) = setup() else { return };
    let probes_dir = env.workspace.join("audit/probes");
    let scratch = env.workspace.join("target/probe_tmp");
    let _ = fs::create_dir_all(&scratch);

    let mut paths: Vec<_> = fs::read_dir(&probes_dir)
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "rok"))
        .collect();
    paths.sort();

    let results = par_map(&paths, |path| {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let source = fs::read_to_string(path).unwrap();
        let kind = parse_probe_kind(&source).unwrap_or(ProbeKind::Positive);
        let outcome = run_probe(&env, &name, path, &source, kind, &scratch);
        (name, parse_xfail(&source), outcome)
    });

    let mut failures = Vec::new();
    let mut measurements = Vec::new();
    for (name, xfail, outcome) in results {
        match (xfail.as_deref(), outcome) {
            (Some(_), ProbeOutcome::Fail(reason)) => {
                println!("xfail {name}: {reason}");
            }
            (Some(reason), ProbeOutcome::Pass) => failures.push(format!(
                "{name}: probe now PASSES — remove `// xfail: {reason}`"
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
    assert!(
        failures.is_empty(),
        "{} of {} spec probes failed:\n  {}",
        failures.len(),
        paths.len(),
        failures.join("\n  ")
    );
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
    env: &Env,
    name: &str,
    path: &Path,
    source: &str,
    kind: ProbeKind,
    scratch: &Path,
) -> ProbeOutcome {
    let exe = scratch.join(name);
    let _ = fs::remove_file(&exe);

    let Ok(build) = rokc_build(env, path, &exe) else {
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
        return match classify_build_fail(kind, stage, &stderr) {
            ProbeOutcome::Pass => match check_expect_error(source, &stderr) {
                Ok(()) => ProbeOutcome::Pass,
                Err(e) => ProbeOutcome::Fail(e),
            },
            other => other,
        };
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
                    return ProbeOutcome::Fail(format!("exit={actual_exit} (want {want_exit})"));
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
            BuildFail::Codegen => {
                ProbeOutcome::Fail(format!("rejected but not at parse stage: {first_err}"))
            }
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
    directive(source, "xfail:").map(str::to_owned)
}

fn parse_probe_kind(source: &str) -> Option<ProbeKind> {
    Some(match directive(source, "probe:")? {
        "positive" => ProbeKind::Positive,
        "positive-parse-only" => ProbeKind::PositiveParseOnly,
        "negative-must-fail" => ProbeKind::NegativeMustFail,
        "negative-must-fail-parse" => ProbeKind::NegativeMustFailParse,
        "measure" => ProbeKind::Measure,
        other => panic!("unknown probe kind: {other}"),
    })
}

//! End to end: `rokc build` each `tests/cases/*.rok` (or
//! `tests/cases/<dir>/main.rok`), then run it. A case has
//! `// expect-exit: N` (optionally `// expect-stdout:`), or
//! `// expect-error: text` when it must fail to build. Directives:
//! `common/mod.rs`.

mod common;

use std::fs;
use std::path::PathBuf;

use common::*;

#[test]
fn end_to_end_cases() {
    let Some(env) = setup() else { return };
    let cases_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases");
    let scratch = env
        .workspace
        .join(format!("target/integration_tmp{}", opt_suffix()));

    let mut cases: Vec<(String, PathBuf)> = fs::read_dir(&cases_dir)
        .unwrap()
        .filter_map(|e| {
            let p = e.ok()?.path();
            if p.is_dir() {
                let main = p.join("main.rok");
                let name = p.file_name()?.to_string_lossy().into_owned();
                main.exists().then_some((name, main))
            } else if p.extension().is_some_and(|x| x == "rok") {
                Some((p.file_stem()?.to_string_lossy().into_owned(), p))
            } else {
                None
            }
        })
        .collect();
    cases.sort();

    let results = par_map(&cases, |(name, path)| {
        let r = run_case(&env, name, path, &scratch);
        if r.is_ok() {
            println!("ok    {name}");
        }
        r.map_err(|e| format!("{name}: {e}"))
    });
    let failures: Vec<String> = results.into_iter().filter_map(Result::err).collect();
    assert!(
        failures.is_empty(),
        "{} of {} integration cases failed:\n  {}",
        failures.len(),
        cases.len(),
        failures.join("\n  ")
    );
}

fn run_case(
    env: &Env,
    name: &str,
    path: &PathBuf,
    scratch: &std::path::Path,
) -> Result<(), String> {
    let source = fs::read_to_string(path).unwrap();
    if optimized() && directives(&source, "debug-only").next().is_some() {
        return Ok(());
    }
    let case_dir = scratch.join(name);
    let _ = fs::create_dir_all(&case_dir);
    let exe = case_dir.join("out");

    let build = rokc_build(env, path, &exe).map_err(|e| format!("rokc: {e}"))?;
    let stderr = String::from_utf8_lossy(&build.stderr);
    if parse_expect_error(&source).is_some() {
        if build.status.success() {
            return Err("build succeeded but `// expect-error:` expects failure".into());
        }
        return check_expect_error(&source, &stderr);
    }
    let Some(expected) = parse_expect_exit(&source) else {
        return Err("missing `// expect-exit: N` (or `// expect-error:`) directive".into());
    };
    if !build.status.success() {
        let first = stderr
            .lines()
            .find(|l| l.starts_with("error"))
            .unwrap_or("");
        return Err(format!("rokc build failed: {first}"));
    }
    for want in directives(&source, "expect-warning:") {
        if !stderr.contains(want) {
            return Err(format!(
                "build stderr lacks warning {want:?}\n    stderr: {stderr:?}"
            ));
        }
    }

    for unwanted in directives(&source, "forbid-warning:") {
        if stderr.contains(unwanted) {
            return Err(format!(
                "build stderr has warning {unwanted:?}\n    stderr: {stderr:?}"
            ));
        }
    }

    check_run(&source, &exe, expected, &[])?;
    // `// gc-stress: N`: again with a collection every N allocations and
    // every full one evacuating all it may (objects move all the time).
    if let Some(n) = directive(&source, "gc-stress:") {
        let env = [("ROK_GC_STRESS", n.trim()), ("ROK_GC_EVAC", "always")];
        check_run(&source, &exe, expected, &env).map_err(|e| format!("gc-stress: {e}"))?;
    }
    Ok(())
}

/// Run `exe` (with `env`) and check its exit code, stderr and stdout
/// against the case's directives.
fn check_run(
    source: &str,
    exe: &std::path::Path,
    expected: i32,
    env: &[(&str, &str)],
) -> Result<(), String> {
    let run = std::process::Command::new(exe)
        .envs(env.iter().copied())
        .output()
        .map_err(|e| format!("exec: {e}"))?;
    let exit = run.status.code().ok_or("no exit code")?;
    if exit != expected {
        return Err(format!("exit={exit} (expected {expected})"));
    }
    if let Some(want) = directive(source, "expect-stderr:") {
        let got = String::from_utf8_lossy(&run.stderr);
        if !got.contains(want) {
            return Err(format!("stderr lacks {want:?}\n    stderr: {got:?}"));
        }
    }
    if let Some(want) = parse_expect_stdout(source) {
        let got = String::from_utf8_lossy(&run.stdout);
        if got.trim_end() != want.trim_end() {
            return Err(format!(
                "stdout mismatch\n  want: {want:?}\n  got:  {got:?}"
            ));
        }
    }
    Ok(())
}

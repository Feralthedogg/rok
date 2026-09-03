//! End-to-end driver: `rokc build` (which fans out to mlir-opt + mlir-translate + clang) → exec.
//! Each `tests/cases/*.rok` (or `tests/cases/<dir>/main.rok`) needs either
//! `// expect-exit: N` (optionally `// expect-stdout:`) or `// expect-error: text`
//! for a case that must fail to build. Directive details: `common/mod.rs`.

mod common;

use std::fs;
use std::path::PathBuf;

use common::*;

#[test]
fn end_to_end_cases() {
    let Some(env) = setup() else { return };
    let cases_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/cases");
    let scratch = env.workspace.join("target/integration_tmp");

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

    let run = std::process::Command::new(&exe)
        .output()
        .map_err(|e| format!("exec: {e}"))?;
    let exit = run.status.code().ok_or("no exit code")?;
    if exit != expected {
        return Err(format!("exit={exit} (expected {expected})"));
    }
    if let Some(want) = parse_expect_stdout(&source) {
        let got = String::from_utf8_lossy(&run.stdout);
        if got.trim_end() != want.trim_end() {
            return Err(format!(
                "stdout mismatch\n  want: {want:?}\n  got:  {got:?}"
            ));
        }
    }
    Ok(())
}

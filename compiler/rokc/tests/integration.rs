//! End-to-end driver: `rokc build` (which fans out to mlir-opt + mlir-translate + clang) → exec.
//! Reads `// expect-exit: N` from each `tests/cases/*.rok`.
//! Skips silently if the LLVM toolchain isn't on PATH.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const ROKC: &str = env!("CARGO_BIN_EXE_rokc");
const MANIFEST_DIR: &str = env!("CARGO_MANIFEST_DIR");

#[test]
fn end_to_end_cases() {
    let manifest = PathBuf::from(MANIFEST_DIR);
    // compiler/rokc → workspace root.
    let workspace = manifest.parent().and_then(Path::parent).unwrap();
    let bootstrap = workspace.join("library/core/lib.rok");
    let rokr = workspace.join("target/debug/librokr.a");
    let cases = manifest.join("tests/cases");

    assert!(bootstrap.exists(), "missing {bootstrap:?}");
    assert!(
        rokr.exists(),
        "{rokr:?} not built — run `cargo build` for the workspace first"
    );

    // `rokc build` shells out to mlir-opt / mlir-translate / clang. If
    // any are missing, skip the suite the same way the old driver did.
    if locate("mlir-opt").is_none()
        || locate("mlir-translate").is_none()
        || locate("clang").is_none()
    {
        eprintln!("skip: mlir-opt / mlir-translate / clang not on PATH");
        return;
    }

    let scratch = workspace.join("target/integration_tmp");
    let _ = fs::create_dir_all(&scratch);

    let mut failures = Vec::new();
    for entry in fs::read_dir(&cases).unwrap() {
        let entry_path = entry.unwrap().path();
        let (path, name) = if entry_path.is_dir() {
            let main = entry_path.join("main.rok");
            if !main.exists() {
                continue;
            }
            let n = entry_path
                .file_name()
                .unwrap()
                .to_string_lossy()
                .into_owned();
            (main, n)
        } else if entry_path.extension().and_then(|s| s.to_str()) == Some("rok") {
            let n = entry_path
                .file_stem()
                .unwrap()
                .to_string_lossy()
                .into_owned();
            (entry_path.clone(), n)
        } else {
            continue;
        };
        let source = fs::read_to_string(&path).unwrap();
        let Some(expected) = parse_expect_exit(&source) else {
            failures.push(format!("{name}: missing `// expect-exit: N` directive"));
            continue;
        };
        let expected_stdout = parse_expect_stdout(&source);
        let outcome = run_case(&name, &path, &bootstrap, &rokr, &scratch);
        match outcome {
            Ok((actual_exit, actual_stdout)) => {
                if actual_exit != expected {
                    failures.push(format!(
                        "{name}: exit={actual_exit} (expected {expected})"
                    ));
                    continue;
                }
                if let Some(want) = expected_stdout {
                    if actual_stdout.trim_end() != want.trim_end() {
                        failures.push(format!(
                            "{name}: stdout mismatch\n  want: {want:?}\n  got:  {:?}",
                            actual_stdout
                        ));
                        continue;
                    }
                }
                println!("ok    {name}: exit={actual_exit}");
            }
            Err(e) => failures.push(format!("{name}: {e}")),
        }
    }

    if !failures.is_empty() {
        panic!("{} integration failures:\n  {}", failures.len(), failures.join("\n  "));
    }
}

fn run_case(
    name: &str,
    source: &Path,
    bootstrap: &Path,
    rokr: &Path,
    scratch: &Path,
) -> Result<(i32, String), String> {
    let case_dir = scratch.join(name);
    let _ = fs::create_dir_all(&case_dir);
    let exe = case_dir.join("out");

    let status = Command::new(ROKC)
        .arg("build")
        .arg(source)
        .arg("--bootstrap")
        .arg(bootstrap)
        .arg("--rokr")
        .arg(rokr)
        .arg("-o")
        .arg(&exe)
        .status()
        .map_err(|e| format!("rokc: {e}"))?;
    if !status.success() {
        return Err("rokc build failed".into());
    }

    let run_out = Command::new(&exe)
        .output()
        .map_err(|e| format!("exec: {e}"))?;
    let exit = run_out.status.code().ok_or_else(|| "no exit code".to_owned())?;
    let stdout = String::from_utf8_lossy(&run_out.stdout).into_owned();
    Ok((exit, stdout))
}

fn parse_expect_stdout(source: &str) -> Option<String> {
    // Multi-line stdout block:  // expect-stdout:\n// <line>\n// <line>\n
    let mut lines = source.lines().peekable();
    while let Some(line) = lines.next() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("// expect-stdout:") {
            let rest = rest.trim();
            if !rest.is_empty() {
                return Some(rest.to_owned());
            }
            // Following `// ...` lines form the expected output.
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

fn parse_expect_exit(source: &str) -> Option<i32> {
    for line in source.lines() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("// expect-exit:") {
            return rest.trim().parse::<i32>().ok();
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

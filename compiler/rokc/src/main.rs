//! `rokc` — the rok compiler binary.
//!
//! Subcommands:
//! - `rokc emit <file> --stage hir|mir|mlir [-o output]` — debug textual emit
//! - `rokc build <file> [-o output]` — full pipeline → executable
//! - `rokc run <file> [-- args...]` — build + run
//!
//! `build` / `run` invoke `mlir-opt`, `mlir-translate`, and `clang` from
//! `PATH`. The pipeline is the same one the integration tests drive.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{self, Command, Stdio};

use clap::Parser as ClapParser;
use rokc_diagnostic::report;
use rokc_interface::{LibGlob, Session};

#[derive(ClapParser)]
#[command(name = "rokc", about = "rok programming language compiler")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(clap::Subcommand)]
enum Cmd {
    /// Emit a debug textual artifact (HIR, MIR, or MLIR).
    Emit(EmitArgs),
    /// Compile to an executable via mlir-opt + mlir-translate + clang.
    Build(BuildArgs),
    /// Build and run the produced executable.
    Run(RunArgs),
}

#[derive(clap::Args)]
struct CommonArgs {
    /// Input `.rok` file.
    input: PathBuf,
    /// Library search paths. Append `::*` or `::**` for auto-import.
    #[arg(short = 'L', long = "lib")]
    libs: Vec<String>,
    /// Files containing operator declarations to pre-load.
    #[arg(long = "bootstrap")]
    bootstrap: Vec<PathBuf>,
    /// LLVM target triple. Used by codegen for `isize` / `usize` width.
    #[arg(long)]
    target: Option<String>,
    /// `#[cfg(...)]` flags. Either bare flag (`--cfg test`) or
    /// `key=value` (`--cfg feature=gpu`).
    #[arg(long = "cfg")]
    cfg: Vec<String>,
}

#[derive(clap::Args)]
struct EmitArgs {
    #[command(flatten)]
    common: CommonArgs,
    /// Output stage: `hir`, `mir`, or `mlir`.
    #[arg(long, default_value = "mlir")]
    stage: String,
    /// Output file path.
    #[arg(short = 'o', long)]
    output: Option<PathBuf>,
}

#[derive(clap::Args)]
struct BuildArgs {
    #[command(flatten)]
    common: CommonArgs,
    /// Output executable path. Defaults to the input stem in cwd.
    /// `--out` is the spec-named long form (901.2); `-o` / `--output`
    /// stay for ergonomics and back-compat.
    #[arg(short = 'o', long = "output", visible_alias = "out")]
    output: Option<PathBuf>,
    /// Library to link the runtime from. Resolved with `-l<name>` if a
    /// bare name, or used as-is if a path.
    #[arg(long = "rokr", default_value = "rokr")]
    rokr: String,
}

#[derive(clap::Args)]
struct RunArgs {
    #[command(flatten)]
    build: BuildArgs,
    /// Arguments forwarded to the produced executable.
    #[arg(last = true)]
    args: Vec<String>,
}

fn main() {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Emit(args) => cmd_emit(args),
        Cmd::Build(args) => {
            cmd_build(args);
        }
        Cmd::Run(args) => cmd_run(args),
    }
}

fn make_session(common: &CommonArgs) -> Session {
    let mut session = Session::new();
    for lib in &common.libs {
        let (path, glob) = parse_lib_arg(lib);
        let g = match glob {
            Some("**") => LibGlob::GlobRecursive,
            Some("*") => LibGlob::Glob,
            _ => LibGlob::None,
        };
        session.add_lib(PathBuf::from(path), g);
    }
    for path in &common.bootstrap {
        session.add_bootstrap_file(path.clone());
    }
    for flag in &common.cfg {
        session.add_cfg(flag.clone());
    }
    session
}

fn parse_lib_arg(arg: &str) -> (&str, Option<&str>) {
    if let Some(path) = arg.strip_suffix("::**") {
        (path, Some("**"))
    } else if let Some(path) = arg.strip_suffix("::*") {
        (path, Some("*"))
    } else {
        (arg, None)
    }
}

fn default_emit_output(input: &Path, stage: &str) -> PathBuf {
    let stem = input.file_stem().and_then(|s| s.to_str()).unwrap_or("out");
    let ext = match stage {
        "hir" => "hir.rok",
        "mir" => "mir.rok",
        "mlir" => "mlir",
        _ => "out",
    };
    PathBuf::from(format!("{stem}.{ext}"))
}

fn cmd_emit(args: EmitArgs) {
    let session = make_session(&args.common);
    let result = session.compile_file(&args.common.input);
    if result.has_errors() {
        result.report_errors();
        process::exit(1);
    }
    for module in &result.modules {
        let out_path = args
            .output
            .clone()
            .unwrap_or_else(|| default_emit_output(&args.common.input, &args.stage));
        let content = match args.stage.as_str() {
            "hir" => rokc_hir::print_hir(&module.hir),
            "mir" => rokc_mir::print_mir(&module.mir),
            "mlir" => match rokc_codegen_mlir::codegen_with_target(
                &module.mir,
                args.common.target.as_deref(),
            ) {
                Ok(m) => m.text,
                Err(e) => {
                    report(&e);
                    process::exit(1);
                }
            },
            other => {
                eprintln!("rokc: unknown emit stage '{other}' (valid: hir, mir, mlir)");
                process::exit(1);
            }
        };
        if let Err(e) = std::fs::write(&out_path, content) {
            eprintln!("rokc: cannot write {}: {e}", out_path.display());
            process::exit(1);
        }
        eprintln!("rokc: wrote {}", out_path.display());
    }
}

/// Compile to executable. Returns the path to the produced binary on
/// success. Exits the process on failure.
fn cmd_build(args: BuildArgs) -> PathBuf {
    let session = make_session(&args.common);
    let result = session.compile_file(&args.common.input);
    if result.has_errors() {
        result.report_errors();
        process::exit(1);
    }

    let mlir_opt = locate_tool("mlir-opt");
    let mlir_translate = locate_tool("mlir-translate");
    let clang = locate_tool("clang");

    let stem = args
        .common
        .input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("out");
    let work_dir = std::env::temp_dir().join(format!("rokc-build-{stem}"));
    let _ = std::fs::create_dir_all(&work_dir);
    let mlir_path = work_dir.join(format!("{stem}.mlir"));
    let ll_path = work_dir.join(format!("{stem}.ll"));
    let exe_out = args
        .output
        .clone()
        .unwrap_or_else(|| PathBuf::from(stem));
    // Make the path absolute so `Command::new(exe)` doesn't fall back
    // to PATH lookup when callers pass a bare stem.
    let exe_out = if exe_out.is_absolute() {
        exe_out
    } else {
        std::env::current_dir().unwrap_or_default().join(exe_out)
    };

    // 1. rokc → MLIR text.
    let module = result
        .modules
        .first()
        .unwrap_or_else(|| {
            eprintln!("rokc: no module produced");
            process::exit(1)
        });
    let mlir = match rokc_codegen_mlir::codegen_with_target(
        &module.mir,
        args.common.target.as_deref(),
    ) {
        Ok(m) => m,
        Err(e) => {
            report(&e);
            process::exit(1);
        }
    };
    if let Err(e) = std::fs::write(&mlir_path, &mlir.text) {
        eprintln!("rokc: cannot write {}: {e}", mlir_path.display());
        process::exit(1);
    }

    // 2. mlir-opt — lower to LLVM dialect.
    let opt_out = match Command::new(&mlir_opt)
        .args([
            "--convert-func-to-llvm",
            "--convert-arith-to-llvm",
            "--convert-cf-to-llvm",
            "--finalize-memref-to-llvm",
            "--reconcile-unrealized-casts",
        ])
        .arg(&mlir_path)
        .output()
    {
        Ok(o) => o,
        Err(e) => {
            eprintln!("rokc: mlir-opt invocation failed: {e}");
            process::exit(1);
        }
    };
    if !opt_out.status.success() {
        eprintln!("rokc: mlir-opt failed:\n{}", String::from_utf8_lossy(&opt_out.stderr));
        process::exit(1);
    }

    // 3. mlir-translate → LLVM IR (read on stdin).
    let mut translate = match Command::new(&mlir_translate)
        .arg("--mlir-to-llvmir")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            eprintln!("rokc: mlir-translate spawn failed: {e}");
            process::exit(1);
        }
    };
    if let Some(stdin) = translate.stdin.as_mut() {
        let _ = stdin.write_all(&opt_out.stdout);
    }
    let translate_out = translate.wait_with_output().unwrap_or_else(|e| {
        eprintln!("rokc: mlir-translate wait failed: {e}");
        process::exit(1);
    });
    if !translate_out.status.success() {
        eprintln!(
            "rokc: mlir-translate failed:\n{}",
            String::from_utf8_lossy(&translate_out.stderr)
        );
        process::exit(1);
    }
    if let Err(e) = std::fs::write(&ll_path, &translate_out.stdout) {
        eprintln!("rokc: cannot write {}: {e}", ll_path.display());
        process::exit(1);
    }

    // 4. clang → executable. The `--rokr` value is treated as a path
    // when it carries a file extension (`.a` / `.so` / `.dylib`),
    // otherwise as a -l flag. When a path is supplied we skip the
    // auto-emitted `-lrokr` so the linker doesn't go looking for the
    // library on its own search path.
    let mut clang_cmd = Command::new(&clang);
    clang_cmd.arg("-Wno-override-module").arg(&ll_path);
    let rokr_is_path = Path::new(&args.rokr).extension().is_some();
    if rokr_is_path {
        clang_cmd.arg(&args.rokr);
    } else {
        clang_cmd.arg(format!("-l{}", args.rokr));
    }
    for lib in &result.link_libraries {
        clang_cmd.arg(format!("-l{lib}"));
    }
    for lib in &mlir.runtime_libraries {
        if rokr_is_path && lib == "rokr" {
            continue;
        }
        clang_cmd.arg(format!("-l{lib}"));
    }
    clang_cmd.arg("-o").arg(&exe_out);
    let clang_out = clang_cmd.output().unwrap_or_else(|e| {
        eprintln!("rokc: clang invocation failed: {e}");
        process::exit(1);
    });
    if !clang_out.status.success() {
        eprintln!("rokc: clang failed:\n{}", String::from_utf8_lossy(&clang_out.stderr));
        process::exit(1);
    }

    eprintln!("rokc: built {}", exe_out.display());
    exe_out
}

fn cmd_run(args: RunArgs) {
    let exe = cmd_build(args.build);
    let status = Command::new(&exe)
        .args(&args.args)
        .status()
        .unwrap_or_else(|e| {
            eprintln!("rokc: exec failed: {e}");
            process::exit(1);
        });
    process::exit(status.code().unwrap_or(1));
}

fn locate_tool(name: &str) -> PathBuf {
    let path = std::env::var_os("PATH").unwrap_or_default();
    for dir in std::env::split_paths(&path) {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return candidate;
        }
    }
    eprintln!("rokc: cannot find `{name}` in PATH (required for `build`/`run`)");
    process::exit(1);
}

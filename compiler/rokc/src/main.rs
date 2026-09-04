//! `rokc` — the rok compiler binary (spec 901). Arguments are parsed by
//! hand: the workspace takes no external crates (targets.md).
//!
//! Exit codes: 0 ok, 1 compile / build error, 2 usage error. `run`
//! exits with the program's own code.

use std::path::{Path, PathBuf};
use std::process::{self, Command};

use rokc_interface::{BuildOptions, CompileResult, EmitKind, Session, TempDir, report};

const USAGE: &str = "\
usage: rokc <command> [options] [path] [-- args...]

commands:
  build [path]        compile to an executable (default: <dir>/target/<stem>)
  run [path]          build to a temp dir and run; args after `--` are forwarded
  check [path]        diagnose only, no native build
  emit [path]         write an intermediate artifact (see --emit)
  version             print the version
  help                print this help

path is a `.rok` file or a package directory containing `main.rok`
(default: current directory).

options:
  -o, --out, --output <path>   output file
  --emit=<kind>                hir | mir | mlir | llvmir | asm | obj
                               (written to target/ unless -o is given)
  --target=<triple>            LLVM target triple
  --release                    optimized build (same as -O2)
  -O0 | -O1 | -O2 | -O3 | -Os  optimization level (default -O0)
  --cfg <flag | key=value>     #[cfg] flag (repeatable)
  --bootstrap <file>           operator / lang declarations to preload (repeatable;
                               default: $ROK_HOME/library/core/lib.rok)
  --rokr <lib>                 runtime library: path, or name for -l<name>
                               (default: librokr.a next to rokc, else -lrokr)
  --keep                       keep the temporary build directory
";

#[derive(Default)]
struct Args {
    cmd: String,
    input: Option<PathBuf>,
    output: Option<PathBuf>,
    emit: Option<EmitKind>,
    bootstrap: Vec<PathBuf>,
    cfg: Vec<String>,
    opts: BuildOptions,
    run_args: Vec<String>,
}

fn usage_error(msg: &str) -> ! {
    eprintln!("rokc: {msg}\nrun `rokc help` for usage");
    process::exit(2);
}

fn parse_args(raw: Vec<String>) -> Args {
    let mut it = raw.into_iter();
    let mut a = Args {
        cmd: it.next().unwrap_or_else(|| usage_error("missing command")),
        ..Args::default()
    };
    // Value of `--name=value` or the next argument for `--name value`.
    let value = |name: &str, inline: Option<String>, it: &mut std::vec::IntoIter<String>| {
        inline
            .or_else(|| it.next())
            .unwrap_or_else(|| usage_error(&format!("`{name}` needs a value")))
    };
    while let Some(arg) = it.next() {
        let (name, inline) = match arg.split_once('=') {
            Some((n, v)) if n.starts_with("--") => (n.to_owned(), Some(v.to_owned())),
            _ => (arg.clone(), None),
        };
        match name.as_str() {
            "--" => {
                a.run_args = it.by_ref().collect();
            }
            "-o" | "--out" | "--output" => a.output = Some(value(&name, inline, &mut it).into()),
            "--bootstrap" => a.bootstrap.push(value(&name, inline, &mut it).into()),
            "--cfg" => a.cfg.push(value(&name, inline, &mut it)),
            "--target" => a.opts.target = Some(value(&name, inline, &mut it)),
            "--rokr" => a.opts.rokr = value(&name, inline, &mut it),
            // `--stage` is the pre-901 spelling of `--emit`.
            "--emit" | "--stage" => {
                let k = value(&name, inline, &mut it);
                a.emit = Some(
                    EmitKind::parse(&k)
                        .unwrap_or_else(|| usage_error(&format!("unknown emit kind `{k}`"))),
                );
            }
            "--release" => "2".clone_into(&mut a.opts.opt_level),
            "-O0" | "-O1" | "-O2" | "-O3" | "-Os" => name[2..].clone_into(&mut a.opts.opt_level),
            "--keep" => a.opts.keep_temps = true,
            "-h" | "--help" => {
                print!("{USAGE}");
                process::exit(0);
            }
            s if s.starts_with('-') => usage_error(&format!("unknown option `{s}`")),
            _ if a.input.is_none() => a.input = Some(arg.into()),
            _ => usage_error(&format!("unexpected argument `{arg}`")),
        }
    }
    a
}

fn main() {
    let a = with_defaults(parse_args(std::env::args().skip(1).collect()));
    match a.cmd.as_str() {
        "build" => {
            if let Some(kind) = a.emit {
                cmd_emit(&a, kind);
            } else {
                let (result, input) = compile(&a);
                let out = a
                    .output
                    .clone()
                    .unwrap_or_else(|| target_dir(&input).join(stem(&input)));
                fail_on(result.link(&a.opts, &out));
                eprintln!("rokc: built {}", out.display());
            }
        }
        "emit" => cmd_emit(&a, a.emit.unwrap_or(EmitKind::Mlir)),
        "check" => {
            let (result, _) = compile(&a);
            // Codegen too: it rejects constructs the backend cannot lower.
            fail_on(result.emit(EmitKind::Mlir, &a.opts));
        }
        "run" => cmd_run(&a),
        "version" | "--version" | "-V" => println!("rokc {}", env!("CARGO_PKG_VERSION")),
        "help" | "--help" | "-h" => print!("{USAGE}"),
        other => usage_error(&format!("unknown command `{other}`")),
    }
}

/// The implicit `use rok::core::**;` (spec 0.0.5) needs `library/core`,
/// and linking needs `librokr.a`; find both without flags.
fn with_defaults(mut a: Args) -> Args {
    let exe_dir = std::env::current_exe()
        .ok()
        .and_then(|e| e.parent().map(Path::to_path_buf));
    if a.bootstrap.is_empty() {
        match rok_home(exe_dir.as_deref()) {
            Some(home) => a.bootstrap.push(home.join(CORE_LIB)),
            None => eprintln!(
                "rokc: warning: `{CORE_LIB}` not found (set ROK_HOME); \
                 operators and lang items are unavailable"
            ),
        }
    }
    if a.opts.rokr == "rokr" {
        let local = exe_dir.map(|d| d.join("librokr.a"));
        if let Some(lib) = local.filter(|l| l.is_file()) {
            a.opts.rokr = lib.display().to_string();
        }
    }
    a
}

const CORE_LIB: &str = "library/core/lib.rok";

/// `$ROK_HOME`, else the nearest ancestor of the `rokc` binary holding
/// `library/core` (the dev layout `impl/target/debug/rokc` → `impl/`).
fn rok_home(exe_dir: Option<&Path>) -> Option<PathBuf> {
    if let Some(h) = std::env::var_os("ROK_HOME") {
        return Some(h.into());
    }
    exe_dir?
        .ancestors()
        .find(|d| d.join(CORE_LIB).is_file())
        .map(Path::to_path_buf)
}

/// Resolve the input: a `.rok` file, or a package dir holding `main.rok`.
fn input_path(a: &Args) -> PathBuf {
    let p = a.input.clone().unwrap_or_else(|| PathBuf::from("."));
    if p.is_dir() { p.join("main.rok") } else { p }
}

fn stem(input: &Path) -> String {
    input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("out")
        .to_owned()
}

/// Spec 902 `target/` next to the package (overridable with
/// `ROKC_TARGET_DIR`, spec 901.7).
fn target_dir(input: &Path) -> PathBuf {
    let dir = std::env::var_os("ROKC_TARGET_DIR").map_or_else(
        || {
            input
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .join("target")
        },
        PathBuf::from,
    );
    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("rokc: cannot create {}: {e}", dir.display());
        process::exit(1);
    }
    dir
}

fn compile(a: &Args) -> (CompileResult, PathBuf) {
    let input = input_path(a);
    let mut session = Session::new();
    for b in &a.bootstrap {
        session.add_bootstrap_file(b.clone());
    }
    for c in &a.cfg {
        session.add_cfg(c.clone());
    }
    let result = session.compile_file(&input);
    if result.has_errors() {
        result.report_errors();
        process::exit(1);
    }
    (result, input)
}

fn fail_on<T>(r: Result<T, rokc_interface::RokDiagnostic>) -> T {
    r.unwrap_or_else(|d| {
        report(&d);
        process::exit(1)
    })
}

fn cmd_emit(a: &Args, kind: EmitKind) {
    let (result, input) = compile(a);
    let bytes = fail_on(result.emit(kind, &a.opts));
    let out = a.output.clone().unwrap_or_else(|| {
        target_dir(&input).join(format!("{}.{}", stem(&input), kind.extension()))
    });
    if let Err(e) = std::fs::write(&out, bytes) {
        eprintln!("rokc: cannot write {}: {e}", out.display());
        process::exit(1);
    }
    eprintln!("rokc: wrote {}", out.display());
}

fn cmd_run(a: &Args) {
    let (result, input) = compile(a);
    let tmp = fail_on(TempDir::new(a.opts.keep_temps));
    let exe = tmp.path().join(stem(&input));
    fail_on(result.link(&a.opts, &exe));
    let status = Command::new(&exe)
        .args(&a.run_args)
        .status()
        .unwrap_or_else(|e| {
            eprintln!("rokc: cannot run {}: {e}", exe.display());
            process::exit(1);
        });
    drop(tmp);
    #[cfg(unix)]
    if let Some(sig) = std::os::unix::process::ExitStatusExt::signal(&status) {
        process::exit(128 + sig);
    }
    process::exit(status.code().unwrap_or(1));
}

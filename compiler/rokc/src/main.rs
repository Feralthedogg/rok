//! `rokc` — the rok compiler binary (spec 901). Arguments are parsed by
//! hand: the workspace takes no external crates (targets.md).
//!
//! Exit codes (901.6): 0 ok, 1 user error (compile error / failed test),
//! 2 usage error, 101 rokc internal error. `run` exits with the
//! program's own code.

mod package;
mod test_runner;

use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::time::Instant;

use package::Package;
use rokc_interface::{BuildOptions, CompileResult, EmitKind, Session, TempDir, report};

const USAGE: &str = "\
usage: rokc [global options] <command> [options] [args]

commands:
  build [path]           build the package (executable target/<name>, or
                         target/lib<name>.a for a `lib.rok` package)
  run [path] [-- args]   build, then run; args after `--` are forwarded
  test [path] [filter]   build and run the `#[test]` functions (filter: regex
                         with ^ $ . * + ?, or a substring)
  check [path]           diagnose only, no native build
  fmt [path]             format .rok files in place (file or directory)
  new [--lib|--bin] <name>  create a package directory
  clean [path]           remove the package's target/
  demangle <symbol>...   decode `_Y` symbols
  emit [path]            write an intermediate artifact (see --emit)
  version                print the version
  help                   print this help

path is a package directory (default: the current one), a file inside a
package (the package is found by looking upward for `main.rok` / `lib.rok`),
or a lone `.rok` file, which is built as an anonymous executable package.

global options:
  -v, --verbose, -vv           more output (stage timings)
  -q, --quiet                  no progress output
  --color=auto|always|never    color diagnostics (--no-color = never)
  --cwd=<path>                 change directory first
  --message-format=human|json  diagnostics as JSON lines on stdout

build options:
  -o, --out, --output <path>   output file
  --emit=<kind>[,<kind>...]    hir | mir | mlir | llvmir | asm | obj
                               (written to target/<name>.<ext> unless -o)
  --target=<triple>            LLVM target triple
  --release                    optimized build (same as -O2)
  -O0 | -O1 | -O2 | -O3 | -Os  optimization level (default -O0)
  --cfg <flag | key=value>     #[cfg] flag (repeatable)
  --bootstrap <file>           library root to preload (repeatable; default:
                               $ROK_HOME/lib/rok/{core,std,bare}/lib.rok)
  --rokr <lib>                 runtime library: path, or name for -l<name>
                               (default: $ROK_HOME/lib/librokr.a, else -lrokr)
  --keep                       keep the temporary build directory

test options:   --threads=N, --show-output
fmt options:    --check (exit 1 if a file would change), --diff

environment:
  ROK_HOME          install root (default: the parent of rokc's directory);
                    falls back to the repo dev layout
  ROKC_TARGET_DIR   target/ location (default: inside the package)
  ROKC_VERBOSE      same as --verbose
  ROKC_NUM_JOBS     default for --threads
";

// One flag per CLI switch; an enum per group would only add plumbing.
#[allow(clippy::struct_excessive_bools)]
#[derive(Default)]
struct Args {
    cmd: String,
    positional: Vec<String>,
    output: Option<PathBuf>,
    emit: Vec<EmitKind>,
    bootstrap: Vec<PathBuf>,
    cfg: Vec<String>,
    opts: BuildOptions,
    run_args: Vec<String>,
    verbose: u8,
    quiet: bool,
    json: bool,
    color: Option<bool>,
    lib: bool,
    check: bool,
    diff: bool,
    threads: Option<usize>,
    show_output: bool,
}

fn usage_error(msg: &str) -> ! {
    eprintln!("rokc: {msg}\nrun `rokc help` for usage");
    process::exit(2);
}

fn fail(msg: &str) -> ! {
    eprintln!("rokc: error: {msg}");
    process::exit(1);
}

fn parse_args(raw: Vec<String>) -> Args {
    let mut it = raw.into_iter();
    let mut a = Args::default();
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
            // Global options (901.5), accepted before or after the command.
            "-v" | "--verbose" => a.verbose += 1,
            "-vv" => a.verbose += 2,
            "-q" | "--quiet" => a.quiet = true,
            "--no-color" => a.color = Some(false),
            "--color" => {
                a.color = match value(&name, inline, &mut it).as_str() {
                    "auto" => None,
                    "always" => Some(true),
                    "never" => Some(false),
                    v => usage_error(&format!("`--color` takes auto|always|never, not `{v}`")),
                };
            }
            "--cwd" => {
                let dir = value(&name, inline, &mut it);
                if let Err(e) = std::env::set_current_dir(&dir) {
                    usage_error(&format!("--cwd {dir}: {e}"));
                }
            }
            "--message-format" => {
                a.json = match value(&name, inline, &mut it).as_str() {
                    "json" => true,
                    "human" | "short" => false,
                    v => usage_error(&format!("unknown message format `{v}`")),
                };
            }
            "-o" | "--out" | "--output" => a.output = Some(value(&name, inline, &mut it).into()),
            "--bootstrap" => a.bootstrap.push(value(&name, inline, &mut it).into()),
            "--cfg" => a.cfg.push(value(&name, inline, &mut it)),
            "--target" => a.opts.target = Some(value(&name, inline, &mut it)),
            "--rokr" => a.opts.rokr = value(&name, inline, &mut it),
            // `--stage` is the pre-901 spelling of `--emit`.
            "--emit" | "--stage" => {
                for k in value(&name, inline, &mut it).split(',') {
                    a.emit.push(
                        EmitKind::parse(k)
                            .unwrap_or_else(|| usage_error(&format!("unknown emit kind `{k}`"))),
                    );
                }
            }
            "--release" => "2".clone_into(&mut a.opts.opt_level),
            "-O0" | "-O1" | "-O2" | "-O3" | "-Os" => name[2..].clone_into(&mut a.opts.opt_level),
            "--keep" => a.opts.keep_temps = true,
            "--lib" => a.lib = true,
            "--bin" => a.lib = false,
            "--check" => a.check = true,
            "--diff" => a.diff = true,
            "--show-output" => a.show_output = true,
            "--threads" => {
                let n = value(&name, inline, &mut it);
                a.threads = Some(
                    n.parse()
                        .unwrap_or_else(|_| usage_error(&format!("bad --threads `{n}`"))),
                );
            }
            "-h" | "--help" if a.cmd.is_empty() => "help".clone_into(&mut a.cmd),
            "-h" | "--help" => {
                print!("{USAGE}");
                process::exit(0);
            }
            "--version" | "-V" if a.cmd.is_empty() => "version".clone_into(&mut a.cmd),
            // `-` alone is a positional (stdin, 901.9).
            s if s.starts_with('-') && s.len() > 1 => {
                usage_error(&format!("unknown option `{s}`"));
            }
            _ if a.cmd.is_empty() => a.cmd = arg,
            _ => a.positional.push(arg),
        }
    }
    if a.cmd.is_empty() {
        usage_error("missing command");
    }
    if std::env::var_os("ROKC_VERBOSE").is_some_and(|v| !v.is_empty() && v != "0") {
        a.verbose = a.verbose.max(1);
    }
    a
}

fn main() {
    // Spec 901.6: an internal error (rokc panic) exits 101.
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        default_hook(info);
        eprintln!("rokc: internal compiler error");
        process::exit(101);
    }));
    let a = parse_args(std::env::args().skip(1).collect());
    let color = a.color.unwrap_or_else(|| {
        std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none()
    });
    rokc_interface::set_report_style(a.json, color);
    match a.cmd.as_str() {
        "build" => cmd_build(&with_defaults(a)),
        "emit" => {
            let mut a = with_defaults(a);
            if a.emit.is_empty() {
                a.emit.push(EmitKind::Mlir);
            }
            cmd_build(&a);
        }
        "check" => {
            let a = with_defaults(a);
            let (result, _) = compile(&a, &discover_arg(&a), false);
            // Codegen too: it rejects constructs the backend cannot lower.
            fail_on(result.emit(EmitKind::Mlir, &a.opts));
        }
        "run" => cmd_run(&with_defaults(a)),
        "test" => cmd_test(&with_defaults(a)),
        "fmt" => cmd_fmt(&a),
        "new" => {
            let [name] = a.positional.as_slice() else {
                usage_error("usage: rokc new [--lib | --bin] <name>");
            };
            let root = package::new_package(Path::new(name), a.lib).unwrap_or_else(|e| fail(&e));
            if !a.quiet {
                eprintln!(
                    "     Created {} package `{name}` ({})",
                    if a.lib { "library" } else { "executable" },
                    root.display()
                );
            }
        }
        "clean" => {
            let pkg = discover_arg(&a);
            let target = pkg.target_dir();
            match std::fs::remove_dir_all(&target) {
                Ok(()) if !a.quiet => eprintln!("     Removed {}", target.display()),
                Ok(()) => {}
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                Err(e) => fail(&format!("cannot remove {}: {e}", target.display())),
            }
        }
        "demangle" => cmd_demangle(&a),
        "version" => println!("rokc {}", env!("CARGO_PKG_VERSION")),
        "help" => print!("{USAGE}"),
        other => usage_error(&format!("unknown command `{other}`")),
    }
}

/// The implicit `use rok::core::**;` (spec 0.0.5) needs `rok/core`,
/// and linking needs `librokr.a`; find both without flags.
fn with_defaults(mut a: Args) -> Args {
    let exe_dir = std::env::current_exe()
        .ok()
        .and_then(|e| e.parent().map(Path::to_path_buf));
    let (libs, rokr) = locate(exe_dir.as_deref());
    if a.bootstrap.is_empty() {
        match libs {
            Some(libs) => {
                a.bootstrap.push(libs.join("core/lib.rok"));
                // `rok::std` / `rok::bare` ride along when present (no
                // implicit glob: user code names them).
                for tier in ["std", "bare"] {
                    let lib = libs.join(tier).join("lib.rok");
                    if lib.is_file() {
                        a.bootstrap.push(lib);
                    }
                }
            }
            None => eprintln!(
                "rokc: warning: `$ROK_HOME/{INSTALLED_LIBS}/core/lib.rok` not found \
                 (set ROK_HOME); operators and lang items are unavailable"
            ),
        }
    }
    if a.opts.rokr == "rokr" {
        if let Some(lib) = rokr {
            a.opts.rokr = lib.display().to_string();
        }
    }
    a
}

/// Installed layout (E6): `$ROK_HOME/bin/rokc`, `$ROK_HOME/lib/librokr.a`,
/// `$ROK_HOME/lib/rok/{core,std,bare}/`.
const INSTALLED_LIBS: &str = "lib/rok";
const INSTALLED_RT: &str = "lib/librokr.a";
/// Dev layout: the repository's `library/` above `target/<profile>/rokc`,
/// with `librokr.a` next to `rokc`.
const DEV_LIBS: &str = "library";

/// `(library root holding core/ std/ bare/, librokr.a)`. `ROK_HOME`
/// defaults to the parent of the directory holding `rokc` (`bin/..`);
/// when that is not an install, fall back to the dev layout.
fn locate(exe_dir: Option<&Path>) -> (Option<PathBuf>, Option<PathBuf>) {
    let file = |p: PathBuf| p.is_file().then_some(p);
    let libs_in = |d: &Path, rel: &str| {
        let libs = d.join(rel);
        libs.join("core/lib.rok").is_file().then_some(libs)
    };
    let env_home = std::env::var_os("ROK_HOME").map(PathBuf::from);
    let home = env_home
        .clone()
        .or_else(|| exe_dir.and_then(Path::parent).map(Path::to_path_buf));
    if let Some(h) = home {
        if let Some(libs) = libs_in(&h, INSTALLED_LIBS) {
            return (Some(libs), file(h.join(INSTALLED_RT)));
        }
    }
    let dev = env_home
        .and_then(|h| libs_in(&h, DEV_LIBS))
        .or_else(|| exe_dir?.ancestors().find_map(|d| libs_in(d, DEV_LIBS)));
    (dev, exe_dir.and_then(|d| file(d.join("librokr.a"))))
}

/// The package named by the first positional (default: `.`).
fn discover_arg(a: &Args) -> Package {
    let path = a.positional.first().map_or(".", String::as_str);
    package::discover(Path::new(path)).unwrap_or_else(|e| fail(&e))
}

fn create_dir(dir: &Path) {
    if let Err(e) = std::fs::create_dir_all(dir) {
        fail(&format!("cannot create {}: {e}", dir.display()));
    }
}

/// Front end for `pkg`; exits 1 on errors. Prints the 901.8 progress
/// line unless `-q`.
fn compile(a: &Args, pkg: &Package, test: bool) -> (CompileResult, Instant) {
    let started = Instant::now();
    if !a.quiet {
        eprintln!("   Compiling {} ({})", pkg.name, pkg.dir.display());
    }
    let mut session = Session::new();
    for b in &a.bootstrap {
        session.add_bootstrap_file(b.clone());
    }
    for c in &a.cfg {
        session.add_cfg(c.clone());
    }
    session.set_anonymous(pkg.anonymous);
    session.set_test(test);
    let result = session.compile_file(&pkg.root);
    result.warnings.iter().for_each(report);
    if result.has_errors() {
        result.report_errors();
        process::exit(1);
    }
    stage(a, "front end", started);
    (result, started)
}

/// `-v`: per-stage timing (909.5).
fn stage(a: &Args, what: &str, since: Instant) {
    if a.verbose > 0 && !a.quiet {
        eprintln!("   Stage: {what} ({}ms)", since.elapsed().as_millis());
    }
}

fn finished(a: &Args, started: Instant) {
    if !a.quiet {
        eprintln!("    Finished in {:.2}s", started.elapsed().as_secs_f64());
    }
}

fn fail_on<T>(r: Result<T, rokc_interface::RokDiagnostic>) -> T {
    r.unwrap_or_else(|d| {
        report(&d);
        process::exit(1)
    })
}

/// Spec 902.15 layout: `target/<name>` (executable), `target/lib<name>.a`
/// + `target/<name>.o` (library), `target/<name>.<ext>` (`--emit`).
fn cmd_build(a: &Args) {
    let pkg = discover_arg(a);
    let (result, started) = compile(a, &pkg, false);
    let target = pkg.target_dir();
    if !a.emit.is_empty() {
        if a.output.is_some() && a.emit.len() > 1 {
            usage_error("`-o` with several `--emit` kinds");
        }
        for &kind in &a.emit {
            let t = Instant::now();
            let bytes = fail_on(result.emit(kind, &a.opts));
            let out = a.output.clone().unwrap_or_else(|| {
                create_dir(&target);
                target.join(format!("{}.{}", pkg.name, kind.extension()))
            });
            if let Err(e) = std::fs::write(&out, bytes) {
                fail(&format!("cannot write {}: {e}", out.display()));
            }
            stage(a, &format!("emit {}", kind.extension()), t);
            if !a.quiet {
                eprintln!("       Wrote {}", out.display());
            }
        }
        finished(a, started);
        return;
    }
    let out = a.output.clone().unwrap_or_else(|| {
        create_dir(&target);
        target.join(if pkg.lib {
            format!("lib{}.a", pkg.name)
        } else {
            pkg.name.clone()
        })
    });
    let t = Instant::now();
    if !a.quiet {
        eprintln!("    Building {}", out.display());
    }
    if pkg.lib {
        fail_on(result.archive(&a.opts, &out));
    } else {
        fail_on(result.link(&a.opts, &out));
    }
    stage(a, "codegen + link", t);
    finished(a, started);
}

fn cmd_run(a: &Args) {
    let pkg = discover_arg(a);
    if pkg.lib {
        fail(&format!(
            "`{}` is a library package (`lib.rok`); there is nothing to run",
            pkg.dir.display()
        ));
    }
    let (result, started) = compile(a, &pkg, false);
    // An anonymous file builds in a scratch directory (no `target/` next
    // to a loose script); a package builds into its `target/`.
    let tmp = fail_on(TempDir::new(a.opts.keep_temps));
    let exe = match &a.output {
        Some(o) => o.clone(),
        None if pkg.anonymous => tmp.path().join(&pkg.name),
        None => {
            let target = pkg.target_dir();
            create_dir(&target);
            target.join(&pkg.name)
        }
    };
    let t = Instant::now();
    fail_on(result.link(&a.opts, &exe));
    stage(a, "codegen + link", t);
    finished(a, started);
    if !a.quiet {
        eprintln!("     Running `{}`", exe.display());
    }
    let status = Command::new(&exe)
        .args(&a.run_args)
        .status()
        .unwrap_or_else(|e| fail(&format!("cannot run {}: {e}", exe.display())));
    drop(tmp);
    #[cfg(unix)]
    if let Some(sig) = std::os::unix::process::ExitStatusExt::signal(&status) {
        process::exit(128 + sig);
    }
    process::exit(status.code().unwrap_or(1));
}

/// `rokc test [path] [filter]`. A lone argument that is not an existing
/// path is the filter.
fn cmd_test(a: &Args) {
    let (path, filter) = match a.positional.as_slice() {
        [] => (".", None),
        [p] if Path::new(p).exists() => (p.as_str(), None),
        [f] => (".", Some(f.as_str())),
        [p, f] => (p.as_str(), Some(f.as_str())),
        _ => usage_error("usage: rokc test [path] [filter]"),
    };
    let pkg = package::discover(Path::new(path)).unwrap_or_else(|e| fail(&e));
    let (result, started) = compile(a, &pkg, true);
    let tmp = fail_on(TempDir::new(a.opts.keep_temps));
    let exe = tmp.path().join(format!("{}-test", pkg.name));
    let t = Instant::now();
    fail_on(result.link(&a.opts, &exe));
    stage(a, "codegen + link", t);
    finished(a, started);
    let threads = a
        .threads
        .or_else(|| std::env::var("ROKC_NUM_JOBS").ok()?.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, usize::from));
    let ok = test_runner::run(
        &exe,
        &result.tests,
        &test_runner::Options {
            filter,
            threads,
            show_output: a.show_output,
        },
    );
    drop(tmp);
    process::exit(i32::from(!ok));
}

/// `rokc fmt [path]`: a file, or every `.rok` under a directory (skipping
/// `target/` and dot-directories).
fn cmd_fmt(a: &Args) {
    let roots: Vec<PathBuf> = if a.positional.is_empty() {
        vec![PathBuf::from(".")]
    } else {
        a.positional.iter().map(PathBuf::from).collect()
    };
    let mut files = Vec::new();
    for r in &roots {
        if r.is_dir() {
            rok_files(r, &mut files);
        } else if r.is_file() {
            files.push(r.clone());
        } else {
            fail(&format!("`{}` does not exist", r.display()));
        }
    }
    let (mut changed, mut errors) = (0, 0);
    for f in &files {
        let src = match std::fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => fail(&format!("{}: {e}", f.display())),
        };
        let formatted = match rokc_fmt::format_source(&src) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("rokc: cannot format {}: {e}", f.display());
                errors += 1;
                continue;
            }
        };
        if formatted == src {
            continue;
        }
        changed += 1;
        if a.diff || a.check {
            println!("Diff in {}:", f.display());
            if a.diff || !a.quiet {
                print!("{}", rokc_fmt::line_diff(&src, &formatted));
            }
        }
        if !a.check && !a.diff {
            if let Err(e) = std::fs::write(f, formatted) {
                fail(&format!("cannot write {}: {e}", f.display()));
            }
            if a.verbose > 0 {
                eprintln!("   Formatted {}", f.display());
            }
        }
    }
    if errors > 0 || (a.check && changed > 0) {
        process::exit(1);
    }
}

fn rok_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<PathBuf> = rd.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if p.is_dir() {
            if name != "target" && !name.starts_with('.') {
                rok_files(&p, out);
            }
        } else if p.extension().is_some_and(|x| x == "rok") {
            out.push(p);
        }
    }
}

/// Spec 905.4 output, one block per symbol.
fn cmd_demangle(a: &Args) {
    if a.positional.is_empty() {
        usage_error("usage: rokc demangle <symbol>...");
    }
    let mut bad = false;
    for (i, sym) in a.positional.iter().enumerate() {
        if i > 0 {
            println!();
        }
        let Some(d) = rokc_interface::demangle(sym) else {
            eprintln!("rokc: `{sym}` is not a rok symbol");
            bad = true;
            continue;
        };
        let path = d.qualified_path();
        println!("package:  {}", d.pkg);
        println!(
            "path:     {}",
            if path.is_empty() { "(root)" } else { &path }
        );
        println!("name:     {}", d.name);
        match &d.typehash {
            Some(h) => println!("generics: {h} (type tuple hash)"),
            None => println!("generics: (none)"),
        }
    }
    if bad {
        process::exit(1);
    }
}

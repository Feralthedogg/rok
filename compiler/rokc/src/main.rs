//! `rokc` — the rok compiler binary (spec 901). Arguments are parsed by
//! hand: the workspace takes no external crates (targets.md).
//!
//! Exit codes (901.6): 0 ok, 1 user error (compile error / failed test),
//! 2 usage error, 101 rokc internal error. `run` exits with the
//! program's own code.

mod bench_runner;
mod fresh;
mod package;
mod test_runner;

use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::time::Instant;

use package::Package;
use rokc_interface::{BuildOptions, CompileResult, EmitKind, Session, TempDir, report};
use rokc_tools::lint::Level;

const USAGE: &str = "\
usage: rokc [global options] <command> [options] [args]

commands:
  build [path]           build the package (executable target/<profile>/<name>,
                         or target/<profile>/lib<name>.a + <name>.rhir for a
                         `lib.rok` package; <profile> is debug, or release at
                         -O2+ / -Os; a --target build goes under target/<triple>/)
  run [path] [-- args]   build, then run; args after `--` are forwarded
  test [path] [filter]   build and run the `#[test]` functions (filter: regex
                         with ^ $ . * + ?, or a substring)
  bench [path] [filter]  build (-O2 unless -O given) and time the `#[bench]`
                         functions; prints ns/iter (+/- deviation)
  check [path | -]       diagnose only, no native build (`-`: source on stdin)
  repl [--replay] [--package <path>]
                         interactive session (:type <expr>, :reset, :quit);
                         --replay reruns every cell for each new one;
                         --package loads a library package and `use`s it
  lsp                    language server on stdio (`rok lsp` / `rokls` run it)
  jupyter --connection-file <file>
                         Jupyter kernel (Jupyter starts it; the REPL engine)
  jupyter --install-kernel [--user]
                         write the `rok` kernelspec (kernel.json) into
                         $JUPYTER_DATA_DIR, else ~/Library/Jupyter (macOS) /
                         ~/.local/share/jupyter; `rok jupyter install` makes
                         one that starts the kernel through `rok`
  fmt [path]             format .rok files in place (file or directory)
  lint [path]            compile diagnostics plus lint checks (no native
                         build); exit 1 if a `deny` lint fires
  doc [path]             HTML API docs of the package (and its --extern
                         dependencies) in target/doc/
  new [--lib|--bin] <name>  create a package directory
  init [--lib|--bin] [dir]  make an existing directory a package
  clean [path]           remove the package's target/
  demangle <symbol>...   decode `_Y` symbols
  rhir-text <file>       dump a prebuilt library's RHIR (<name>.rhir or
                         the lib<name>.a beside it)
  inspect <file>         a prebuilt library's package, exports, generic
                         items and archive members
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
  --emit=<kind>[,<kind>...]    ast | hir | mir | mlir | llvmir | asm | obj | expanded
                               (ast: the package's whole AST after meta
                               expansion and desugaring, as rok source;
                               expanded: each meta expansion's output)
                               (written to target/<profile>/build/<name>.<ext>
                               unless -o)
  --target=<triple>            LLVM target triple
  --release                    optimized build (same as -O2)
  -O0 | -O1 | -O2 | -O3 | -Os  optimization level (default -O0)
  -C overflow-checks[=yes|no]  integer overflow panics (default: on at -O0)
  --cfg <flag | key=value>     #[cfg] flag (repeatable)
  --load-mlir-plugin <path|name>
                               MLIR dialect plugin for mlir-opt
                               (--load-dialect-plugin; a name is searched
                               in $ROK_MLIR_PLUGIN_PATH; repeatable)
  --load-mlir-pass-plugin <path|name>
                               MLIR pass plugin (--load-pass-plugin)
  --mlir-pass <pass>           extra mlir-opt pass, before the LLVM
                               lowering (repeatable)
  --bootstrap <file>           library root to preload (repeatable; default:
                               $ROK_HOME/lib/rok/{core,std,bare}/lib.rok)
  --rokr <lib>                 runtime library: path, or name for -l<name>
                               (default: $ROK_HOME/lib/librokr.a, else -lrokr)
  --extern <name>=<path>       dependency package (its directory or
                               `lib.rok`, or a prebuilt <name>.rhir /
                               lib<name>.a), importable as `use name::..`
                               (repeatable; `rok` passes these)
  --name <name>                a library's package name (default: its
                               directory's); it is in the library's symbols
  --target-dir <dir>           instead of the package's target/
  -g, --debug                  DWARF debug info (macOS: a .dSYM next to the
                               executable)
  --keep                       keep the temporary build directory

test options:   --threads=N, --show-output
bench options:  --iters=N (calls per sample; default: calibrated to ~10ms),
                --samples=N (timed samples, default 10)
lint options:   -A|-W|-D <lint|group> (allow / warn / deny; repeatable, later
                wins; `#[allow(..)]` etc. in the source override), --list
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
    externs: Vec<(String, PathBuf)>,
    /// `--name`: a library build's package name.
    name: Option<String>,
    target_dir: Option<PathBuf>,
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
    lint_levels: Vec<(Level, String)>,
    list: bool,
    /// `repl --replay`.
    replay: bool,
    /// `repl --package`: a library package to load and `use`.
    package: Option<PathBuf>,
    /// `jupyter --connection-file`.
    connection_file: Option<PathBuf>,
    /// `jupyter --install-kernel` (`--user` is the default, accepted).
    install_kernel: bool,
    /// `jupyter --install-kernel --env <name>` (from `rok --env`).
    env: Option<String>,
    iters: Option<u64>,
    samples: Option<u64>,
    /// An `-O` level or `--release` was given.
    opt_set: bool,
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
            "--extern" => a.externs.push(parse_extern(&value(&name, inline, &mut it))),
            "--name" => a.name = Some(value(&name, inline, &mut it)),
            "--target-dir" => a.target_dir = Some(value(&name, inline, &mut it).into()),
            "--target" => a.opts.target = Some(value(&name, inline, &mut it)),
            "--rokr" => a.opts.rokr = value(&name, inline, &mut it),
            "--load-mlir-plugin" | "--load-mlir-pass-plugin" => {
                let v = value(&name, inline, &mut it);
                let p = rokc_interface::find_mlir_plugin(&v).unwrap_or_else(|e| fail(&e));
                if name == "--load-mlir-plugin" {
                    a.opts.mlir_dialect_plugins.push(p);
                } else {
                    a.opts.mlir_pass_plugins.push(p);
                }
            }
            "--mlir-pass" => a.opts.mlir_passes.push(value(&name, inline, &mut it)),
            // `--stage` is the pre-901 spelling of `--emit`.
            "--emit" | "--stage" => {
                for k in value(&name, inline, &mut it).split(',') {
                    a.emit.push(
                        EmitKind::parse(k)
                            .unwrap_or_else(|| usage_error(&format!("unknown emit kind `{k}`"))),
                    );
                }
            }
            "--release" => {
                "2".clone_into(&mut a.opts.opt_level);
                a.opt_set = true;
            }
            "-O0" | "-O1" | "-O2" | "-O3" | "-Os" => {
                name[2..].clone_into(&mut a.opts.opt_level);
                a.opt_set = true;
            }
            "-C" | "--codegen" => {
                let v = value(&name, inline, &mut it);
                a.opts.overflow_checks = Some(match v.as_str() {
                    "overflow-checks" | "overflow-checks=yes" | "overflow-checks=on" => true,
                    "overflow-checks=no" | "overflow-checks=off" => false,
                    _ => usage_error(&format!("unknown codegen option `{v}`")),
                });
            }
            "--keep" => a.opts.keep_temps = true,
            "-g" | "--debug" => a.opts.debug = true,
            "--lib" => a.lib = true,
            "--bin" => a.lib = false,
            "--check" => a.check = true,
            "--diff" => a.diff = true,
            "--show-output" => a.show_output = true,
            "--list" => a.list = true,
            "--replay" => a.replay = true,
            "--package" => a.package = Some(value(&name, inline, &mut it).into()),
            "--connection-file" => {
                a.connection_file = Some(value(&name, inline, &mut it).into());
            }
            "--install-kernel" => a.install_kernel = true,
            "--user" => {}
            "--env" => a.env = Some(value(&name, inline, &mut it)),
            "-A" | "-W" | "-D" | "--allow" | "--warn" | "--deny" => {
                let lvl = match name.as_str() {
                    "-A" | "--allow" => Level::Allow,
                    "-W" | "--warn" => Level::Warn,
                    _ => Level::Deny,
                };
                a.lint_levels.push((lvl, value(&name, inline, &mut it)));
            }
            "--iters" | "--samples" => {
                let n = value(&name, inline, &mut it);
                let n = n
                    .parse()
                    .ok()
                    .filter(|n| *n > 0)
                    .unwrap_or_else(|| usage_error(&format!("bad {name} `{n}`")));
                if name == "--iters" {
                    a.iters = Some(n);
                } else {
                    a.samples = Some(n);
                }
            }
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

/// `--extern name=path` (spec 902.3). The path is the dependency's
/// package directory or its `lib.rok` (compiled from source with the
/// package), or a prebuilt `<name>.rhir` / `lib<name>.a` (spec 904).
fn parse_extern(v: &str) -> (String, PathBuf) {
    let Some((name, path)) = v.split_once('=') else {
        usage_error(&format!("`--extern {v}`: expected <name>=<path>"));
    };
    let ident = |s: &str| {
        s.chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_')
            && s.chars().all(|c| c.is_alphanumeric() || c == '_')
    };
    if !ident(name) {
        usage_error(&format!("`--extern`: `{name}` is not a package name"));
    }
    let path = PathBuf::from(path);
    let prebuilt = path.extension().is_some_and(|e| e == "a" || e == "rhir");
    let root = if prebuilt {
        rokc_interface::rhir::companions(&path).0
    } else if path.is_dir() {
        path.join("lib.rok")
    } else {
        path
    };
    if !root.is_file() {
        fail(&format!("`--extern {name}`: no `{}`", root.display()));
    }
    (name.to_owned(), root)
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
            // `check -`: the source is stdin (901.9), an anonymous package.
            let pkg = if a.positional.first().is_some_and(|p| p == "-") {
                Package::stdin()
            } else {
                discover_arg(&a)
            };
            let (result, _) = compile(&a, &pkg, Mode::Build);
            // Codegen too: it rejects constructs the backend cannot lower.
            fail_on(result.emit(EmitKind::Mlir, &a.opts));
        }
        "lsp" => {
            let a = with_defaults(a);
            let io = (
                std::io::BufReader::new(std::io::stdin()),
                std::io::stdout().lock(),
            );
            process::exit(rokc_tools::lsp::serve(io.0, io.1, a.bootstrap, a.externs));
        }
        "repl" => {
            let mut a = with_defaults(a);
            // `--package` (901.2): the library is a dependency of the
            // session, and its first cell is `use <name>::*;`.
            let prelude = a.package.clone().map(|p| {
                let pkg = package::discover(&p).unwrap_or_else(|e| fail(&e));
                if !pkg.lib {
                    fail(&format!(
                        "`--package {}`: not a library package (no `lib.rok`)",
                        p.display()
                    ));
                }
                let name = lib_name(&a, &pkg);
                a.externs.push((name.clone(), pkg.root));
                format!("use {name}::*;")
            });
            let tty = std::io::stdin().is_terminal();
            process::exit(rokc_tools::repl::main(
                a.bootstrap,
                a.externs,
                a.opts,
                tty,
                a.replay,
                prelude.as_deref(),
            ));
        }
        "jupyter" => cmd_jupyter(with_defaults(a)),
        "run" => cmd_run(&with_defaults(a)),
        "test" => cmd_test(&with_defaults(a)),
        "bench" => cmd_bench(with_defaults(a)),
        "lint" => cmd_lint(&with_defaults(a)),
        "doc" => cmd_doc(&with_defaults(a)),
        "fmt" => cmd_fmt(&a),
        "new" => {
            let [name] = a.positional.as_slice() else {
                usage_error("usage: rokc new [--lib | --bin] <name>");
            };
            let root =
                package::new_package(Path::new(name), a.lib, false).unwrap_or_else(|e| fail(&e));
            if !a.quiet {
                eprintln!(
                    "     Created {} package `{name}` ({})",
                    if a.lib { "library" } else { "executable" },
                    root.display()
                );
            }
        }
        "init" => {
            let dir = match a.positional.as_slice() {
                [] => ".",
                [d] => d.as_str(),
                _ => usage_error("usage: rokc init [--lib | --bin] [dir]"),
            };
            let root =
                package::new_package(Path::new(dir), a.lib, true).unwrap_or_else(|e| fail(&e));
            if !a.quiet {
                eprintln!("     Created package ({})", root.display());
            }
        }
        "clean" => {
            let pkg = discover_arg(&a);
            let target = a.target_dir.clone().unwrap_or_else(|| pkg.target_dir());
            match std::fs::remove_dir_all(&target) {
                Ok(()) if !a.quiet => eprintln!("     Removed {}", target.display()),
                Ok(()) => {}
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                Err(e) => fail(&format!("cannot remove {}: {e}", target.display())),
            }
        }
        "demangle" => cmd_demangle(&a),
        "rhir-text" | "inspect" => {
            let [file] = a.positional.as_slice() else {
                usage_error(&format!("usage: rokc {} <file.rhir | lib<name>.a>", a.cmd));
            };
            let path = Path::new(file);
            let out = if a.cmd == "inspect" {
                rokc_interface::rhir::inspect(path)
            } else {
                let rhir = rokc_interface::rhir::companions(path).0;
                std::fs::read(&rhir)
                    .map_err(|e| format!("{}: {e}", rhir.display()))
                    .and_then(|b| rokc_interface::rhir::Rhir::decode(&b))
                    .map(|r| r.text())
            };
            print!("{}", out.unwrap_or_else(|e| fail(&e)));
        }
        "version" => println!("rokc {}", env!("CARGO_PKG_VERSION")),
        "help" => print!("{USAGE}"),
        other => usage_error(&format!("unknown command `{other}`")),
    }
}

/// `jupyter`: run the kernel, or install its kernelspec. Started by
/// `rok` (`$ROK` set), the kernel goes through `rok` so it gets the
/// dependencies of the notebook's project or of `--env`.
fn cmd_jupyter(a: Args) {
    if !a.install_kernel {
        let Some(file) = &a.connection_file else {
            usage_error("usage: rokc jupyter --connection-file <file> | --install-kernel");
        };
        process::exit(rokc_tools::jupyter::serve(
            file,
            a.bootstrap,
            a.externs,
            a.opts,
        ));
    }
    let exe = |p: Option<std::ffi::OsString>| {
        p.map(PathBuf::from)
            .or_else(|| std::env::current_exe().ok())
            .map_or_else(
                || fail("cannot find the kernel executable"),
                |p| p.display().to_string(),
            )
    };
    let mut argv = vec![exe(std::env::var_os("ROK").filter(|r| !r.is_empty()))];
    if let Some(e) = &a.env {
        argv.extend(["--env".to_owned(), e.clone()]);
    }
    argv.extend(["jupyter", "--connection-file", "{connection_file}"].map(str::to_owned));
    let (name, display) = match &a.env {
        Some(e) => (format!("rok-{e}"), format!("rok ({e})")),
        None => ("rok".to_owned(), "rok".to_owned()),
    };
    match rokc_tools::jupyter::install(&name, &display, &argv) {
        Ok(file) if !a.quiet => eprintln!("   Installed kernel `{name}` ({})", file.display()),
        Ok(_) => {}
        Err(e) => fail(&e),
    }
}

/// The implicit `use rok::core::**;` (spec 0.0.5) needs `rok/core`,
/// and linking needs `librokr.a`; find both without flags.
fn with_defaults(mut a: Args) -> Args {
    let (roots, rokr) = rokc_interface::toolchain();
    if a.bootstrap.is_empty() {
        match roots {
            Some(roots) => a.bootstrap = roots,
            None => eprintln!(
                "rokc: warning: `$ROK_HOME/{}/core/lib.rok` not found \
                 (set ROK_HOME); operators and lang items are unavailable",
                rokc_interface::INSTALLED_LIBS
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

/// What `compile` builds for.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Build,
    Test,
    Bench,
    /// Front end only, ASTs kept; warnings left to the caller.
    Lint,
    /// Front end only, ASTs kept.
    Doc,
}

/// Front end for `pkg`; exits 1 on errors. Prints the 901.8 progress
/// line unless `-q`.
fn compile(a: &Args, pkg: &Package, mode: Mode) -> (CompileResult, Instant) {
    let started = Instant::now();
    if !a.quiet {
        let verb = match mode {
            Mode::Lint => "     Linting",
            Mode::Doc => " Documenting",
            _ => "   Compiling",
        };
        eprintln!("{verb} {} ({})", pkg.name, pkg.dir.display());
    }
    let mut session = Session::new();
    for b in &a.bootstrap {
        session.add_bootstrap_file(b.clone());
    }
    for c in &a.cfg {
        session.add_cfg(c.clone());
    }
    for (n, p) in &a.externs {
        session.add_extern(n.clone(), p.clone());
    }
    session.set_anonymous(pkg.anonymous);
    // A library's `build` is a prebuilt library: `lib<name>.a` + RHIR.
    if pkg.lib && matches!(a.cmd.as_str(), "build" | "emit") {
        session.set_lib_name(Some(lib_name(a, pkg)));
    }
    session.set_test(mode == Mode::Test);
    session.set_bench(mode == Mode::Bench);
    session.set_keep_ast(
        matches!(mode, Mode::Lint | Mode::Doc)
            || a.emit.contains(&EmitKind::Expanded)
            || a.emit.contains(&EmitKind::Ast),
    );
    let result = if pkg.root == Path::new(package::STDIN) {
        let mut src = String::new();
        if let Err(e) = std::io::Read::read_to_string(&mut std::io::stdin(), &mut src) {
            fail(&format!("cannot read stdin: {e}"));
        }
        session.compile_source(&src, &pkg.root)
    } else {
        session.compile_file(&pkg.root)
    };
    if mode != Mode::Lint || result.has_errors() {
        result.warnings.iter().for_each(report);
    }
    if result.has_errors() {
        result.report_errors();
        process::exit(1);
    }
    stage(a, "front end", started);
    (result, started)
}

/// A library's package name: `--name`, else its directory's (made an
/// identifier).
fn lib_name(a: &Args, pkg: &Package) -> String {
    a.name.clone().unwrap_or_else(|| {
        let n: String = pkg
            .name
            .chars()
            .map(|c| if c.is_alphanumeric() { c } else { '_' })
            .collect();
        if n.starts_with(|c: char| c.is_ascii_digit()) {
            format!("_{n}")
        } else {
            n
        }
    })
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

/// Cargo-like output directory: `target/[<triple>/]<profile>/`, the
/// profile `release` at `-O2` and above or `-Os`, else `debug`.
fn out_dir(a: &Args, pkg: &Package) -> PathBuf {
    let mut dir = a.target_dir.clone().unwrap_or_else(|| pkg.target_dir());
    if let Some(t) = &a.opts.target {
        dir.push(t);
    }
    let release = matches!(a.opts.opt_level.as_str(), "2" | "3" | "s");
    dir.join(if release { "release" } else { "debug" })
}

/// Layout: `target/<profile>/<name>` (executable),
/// `target/<profile>/lib<name>.a` + `<name>.o` (library),
/// `target/<profile>/build/<name>.<ext>` (`--emit`).
fn cmd_build(a: &Args) {
    let pkg = discover_arg(a);
    let target = out_dir(a, &pkg);
    if !a.emit.is_empty() {
        let (result, started) = compile(a, &pkg, Mode::Build);
        if a.output.is_some() && a.emit.len() > 1 {
            usage_error("`-o` with several `--emit` kinds");
        }
        for &kind in &a.emit {
            let t = Instant::now();
            let bytes = fail_on(result.emit(kind, &a.opts));
            let out = a.output.clone().unwrap_or_else(|| {
                let build = target.join("build");
                create_dir(&build);
                build.join(format!("{}.{}", pkg.name, kind.extension()))
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
            format!("lib{}.a", lib_name(a, &pkg))
        } else {
            pkg.name.clone()
        })
    });
    let fp = fingerprint(a, &pkg, &out);
    if skip_fresh(a, &pkg, &fp) {
        return;
    }
    let (result, started) = compile(a, &pkg, Mode::Build);
    let t = Instant::now();
    if !a.quiet {
        eprintln!("    Building {}", out.display());
    }
    if pkg.lib {
        fail_on(result.archive(&a.opts, &out));
    } else {
        fail_on(result.link(&a.opts, &out));
    }
    if result.warnings.is_empty() {
        fp.save();
    }
    stage(a, "codegen + link", t);
    finished(a, started);
}

/// The incremental-build key of `pkg` built into `out` (see `fresh`).
fn fingerprint(a: &Args, pkg: &Package, out: &Path) -> fresh::Fingerprint {
    let mut words = vec![
        format!("{:?}", a.opts),
        out.display().to_string(),
        pkg.root.display().to_string(),
        std::env::var("PATH").unwrap_or_default(),
        std::env::var("ROK_EAGER_LIBRARY").unwrap_or_default(),
    ];
    words.extend(a.cfg.iter().cloned());
    words.extend(pkg.lib.then(|| lib_name(a, pkg)));
    let mut inputs = vec![if pkg.anonymous {
        pkg.root.clone()
    } else {
        pkg.dir.clone()
    }];
    let mut stamped: Vec<PathBuf> = std::env::current_exe().into_iter().collect();
    stamped.push(PathBuf::from(&a.opts.rokr));
    stamped.extend(a.opts.mlir_dialect_plugins.iter().cloned());
    stamped.extend(a.opts.mlir_pass_plugins.iter().cloned());
    for b in &a.bootstrap {
        words.push(b.display().to_string());
        inputs.push(b.parent().map_or_else(|| b.clone(), Path::to_path_buf));
    }
    for (n, p) in &a.externs {
        words.push(format!("{n}={}", p.display()));
        if p.extension().is_some_and(|e| e == "rhir") {
            let (rhir, archive) = rokc_interface::rhir::companions(p);
            inputs.push(rhir);
            stamped.push(archive);
        } else {
            inputs.push(p.parent().map_or_else(|| p.clone(), Path::to_path_buf));
        }
    }
    let also = if pkg.lib {
        vec![rokc_interface::rhir::companions(out).0]
    } else {
        Vec::new()
    };
    fresh::Fingerprint::new(out, also, &words, &inputs, &stamped)
}

/// `true` (after saying so) when `fp`'s output is up to date; else
/// forget the old record, so a failed build leaves none.
fn skip_fresh(a: &Args, pkg: &Package, fp: &fresh::Fingerprint) -> bool {
    if fp.fresh() {
        if !a.quiet {
            eprintln!("       Fresh {} ({})", pkg.name, pkg.dir.display());
        }
        return true;
    }
    fp.clear();
    false
}

fn cmd_run(a: &Args) {
    let pkg = discover_arg(a);
    if pkg.lib {
        fail(&format!(
            "`{}` is a library package (`lib.rok`); there is nothing to run",
            pkg.dir.display()
        ));
    }
    // An anonymous file builds in a scratch directory (no `target/` next
    // to a loose script); a package builds into its `target/`.
    let tmp = fail_on(TempDir::new(a.opts.keep_temps));
    let exe = match &a.output {
        Some(o) => o.clone(),
        None if pkg.anonymous => tmp.path().join(&pkg.name),
        None => {
            let target = out_dir(a, &pkg);
            create_dir(&target);
            target.join(&pkg.name)
        }
    };
    let fp = (a.output.is_some() || !pkg.anonymous).then(|| fingerprint(a, &pkg, &exe));
    if !fp.as_ref().is_some_and(|fp| skip_fresh(a, &pkg, fp)) {
        let (result, started) = compile(a, &pkg, Mode::Build);
        let t = Instant::now();
        fail_on(result.link(&a.opts, &exe));
        if result.warnings.is_empty() {
            fp.iter().for_each(fresh::Fingerprint::save);
        }
        stage(a, "codegen + link", t);
        finished(a, started);
    }
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

/// `[path] [filter]` of `test` / `bench`: a lone argument that is not an
/// existing path is the filter.
fn path_and_filter(a: &Args) -> (&str, Option<&str>) {
    match a.positional.as_slice() {
        [] => (".", None),
        [p] if Path::new(p).exists() => (p.as_str(), None),
        [f] => (".", Some(f.as_str())),
        [p, f] => (p.as_str(), Some(f.as_str())),
        _ => usage_error(&format!("usage: rokc {} [path] [filter]", a.cmd)),
    }
}

/// `rokc test [path] [filter]`.
fn cmd_test(a: &Args) {
    let (path, filter) = path_and_filter(a);
    let pkg = package::discover(Path::new(path)).unwrap_or_else(|e| fail(&e));
    let (result, started) = compile(a, &pkg, Mode::Test);
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

/// `rokc bench [path] [filter]`: an optimized build (`-O2` unless an
/// `-O` level was given) of the `#[bench]` harness, then
/// `bench_runner`.
fn cmd_bench(mut a: Args) {
    if !a.opt_set {
        "2".clone_into(&mut a.opts.opt_level);
    }
    let (path, filter) = path_and_filter(&a);
    let pkg = package::discover(Path::new(path)).unwrap_or_else(|e| fail(&e));
    let (result, started) = compile(&a, &pkg, Mode::Bench);
    let tmp = fail_on(TempDir::new(a.opts.keep_temps));
    let exe = tmp.path().join(format!("{}-bench", pkg.name));
    let t = Instant::now();
    fail_on(result.link(&a.opts, &exe));
    stage(&a, "codegen + link", t);
    finished(&a, started);
    let ok = bench_runner::run(
        &exe,
        &result.tests,
        &bench_runner::Options {
            filter,
            iters: a.iters,
            samples: a.samples.unwrap_or(10),
        },
    );
    drop(tmp);
    process::exit(i32::from(!ok));
}

/// `rokc lint [path]`: the front end (with ASTs), then the lints; exit 1
/// when one at `deny` fired.
fn cmd_lint(a: &Args) {
    if a.list {
        print!("{}", rokc_tools::lint::list());
        return;
    }
    let pkg = discover_arg(a);
    let (result, started) = compile(a, &pkg, Mode::Lint);
    let diags = rokc_tools::lint::run(&result, &a.lint_levels);
    diags.iter().for_each(report);
    let errors = diags.iter().filter(|d| d.is_error()).count();
    let warnings = diags.len() - errors;
    if !a.quiet && !a.json {
        eprintln!(
            "     Checked {}: {errors} error{}, {warnings} warning{}",
            pkg.name,
            if errors == 1 { "" } else { "s" },
            if warnings == 1 { "" } else { "s" },
        );
    }
    finished(a, started);
    process::exit(i32::from(errors > 0));
}

/// `rokc doc [path]`: HTML into `target/doc/` (see `rokc_tools::doc`).
fn cmd_doc(a: &Args) {
    let pkg = discover_arg(a);
    let (result, started) = compile(a, &pkg, Mode::Doc);
    let out = a
        .target_dir
        .clone()
        .unwrap_or_else(|| pkg.target_dir())
        .join("doc");
    let index = rokc_tools::doc::generate(&result, &pkg.name, &out)
        .unwrap_or_else(|e| fail(&format!("cannot write {}: {e}", out.display())));
    finished(a, started);
    if !a.quiet {
        eprintln!("   Generated {}", index.display());
    }
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

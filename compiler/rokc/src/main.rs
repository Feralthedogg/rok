//! `rokc`: the rok compiler (spec 901). Arguments are parsed by hand: the
//! workspace takes no external crates (targets.md).
//!
//! Exit codes (901.6): 0 ok, 1 user error (compile error / failed test),
//! 2 usage error, 101 internal error. `run` exits with the program's own
//! code.

mod bench_runner;
mod test_runner;

use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::time::Instant;

use rokc_interface::{
    BuildOptions, CompileResult, DepBuild, EmitKind, Fingerprint, Package, Session, TempDir,
    print_rendered, render, report,
};
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
  check [path | -]       front end, lints and codegen, no native build
                         (`-`: source on stdin)
  lint [path]            front end and lints; exit 1 if a `deny` lint fires
  repl [path]            interactive session, each cell compiled and run
                         (macOS arm64; :type <expr>, :reset, :quit); a program
                         path runs in the session first, its bindings and
                         items staying in scope; a library is loaded and
                         `use`d
  lsp                    language server on stdio (`rok lsp` / `rokls` run it)
  jupyter --connection-file <file>
                         Jupyter kernel (Jupyter starts it; `rok jupyter
                         install` writes its kernelspec)
  fmt [path]             format .rok / .rokon files in place (file or directory)
  doc [path]             HTML API docs of the package (and its --extern
                         dependencies) in target/doc/
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
  -v, --verbose                stage timings
  -vv                          also the files read and the generic
                               instances made
  -q, --quiet                  no progress output
  --color=auto|always|never    color diagnostics (--no-color = never)
  --cwd=<path>                 change directory first
  --message-format=human|json  diagnostics as JSON lines on stdout
  -A|-W|-D <lint|group>        allow / warn / deny a lint (repeatable, later
                               wins; `#[allow(..)]` etc. in the source
                               override); check, lint and lsp

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
  -C backend=native|llvm       code generator (default: native at -O0, else LLVM)
  -C subsystem=console|windows Windows executable subsystem (default: console;
                               windows: a GUI program entered through WinMain)
  --cfg <flag | key=value>     #[cfg] flag (repeatable)
  --print cfg                  print the active cfg (target keys, --cfg,
                               debug_assertions below -O1) and exit
  --load-mlir-plugin <path|name>
                               MLIR dialect plugin (a name is searched
                               in $ROK_MLIR_PLUGIN_PATH; repeatable)
  --load-mlir-pass-plugin <path|name>
                               MLIR pass plugin
  --mlir-pass <pass>           extra MLIR pass, before the LLVM
                               lowering (repeatable)
  --bootstrap <file>           library root to preload (repeatable; default:
                               <sysroot>/lib/rok/{core,std,bare}/lib.rok)
  --rokr <lib>                 runtime library: path, or name for -l<name>
                               (default: <sysroot>/lib/librokr.a)
  -L <dir>                     native library search directory, before
                               LIBRARY_PATH (repeatable)
  --extern <name>=<path>       dependency package: its directory or `lib.rok`
                               (prebuilt into target/<profile>/deps/ first,
                               each after the ones before it), or a prebuilt
                               <name>.rhir / lib<name>.a; importable as
                               `use name::..` (repeatable; `rok` passes these)
  --name <name>                the package name (default: its directory's;
                               `rok` passes rok.rokon's `name`); a
                               library's is in its symbols
  --target-dir <dir>           instead of the package's target/ (without a
                               package: the system temp directory's
                               rokc-target/)
  -g, --debug                  DWARF debug info (macOS: a .dSYM next to the
                               executable)
  --keep                       keep the temporary build directory

check options:  --check-library (check every library body, reached or not)
test options:   --threads=N, --show-output
bench options:  --iters=N (calls per sample; default: calibrated to ~10ms),
                --samples=N (timed samples, default 10)
doc options:    --std (document the standard library too; without a path,
                only it, into ./target/doc/)
lint options:   --list
fmt options:    --check (exit 1 if a file would change), --diff

The sysroot is the directory above rokc's own bin/ (a toolchain:
$ROK_HOME/toolchains/<version>-<triple>/); a build in the repository uses
its library/ and the librokr.a beside rokc.

environment:
  ROK_CC            C compiler driver for the final link (default: rokc's
                    own lld)
  ROK_BACKEND       native | llvm: code generator, as -C backend
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
    /// `--print <what>`: print it and exit (`cfg`).
    print: Option<String>,
    /// `--target`: an LLVM triple; `None` is the host.
    target: Option<String>,
    opts: BuildOptions,
    run_args: Vec<String>,
    verbose: u8,
    quiet: bool,
    json: bool,
    color: Option<bool>,
    check: bool,
    check_library: bool,
    /// `doc --std`: document the standard library tiers too.
    std: bool,
    diff: bool,
    threads: Option<usize>,
    show_output: bool,
    lint_levels: Vec<(Level, String)>,
    list: bool,
    /// `jupyter --connection-file`.
    connection_file: Option<PathBuf>,
    iters: Option<u64>,
    samples: Option<u64>,
    /// An `-O` level or `--release` was given.
    opt_set: bool,
    /// The prebuilt standard library this build links (`prebuild`).
    std_prebuilt: Option<PathBuf>,
}

/// The version, and the commit and its date when built from git.
const VERSION: &str = concat!(env!("CARGO_PKG_VERSION"), env!("ROK_COMMIT_INFO"));

/// `rokc <cmd> --help`: the command's entry in `USAGE` and its options.
fn command_help(cmd: &str) -> String {
    let Some(entry) = rokc_core::command_help(USAGE, cmd) else {
        usage_error(&format!("unknown command `{cmd}`"));
    };
    let mut out = format!("usage: rokc [global options] {cmd} [options] [args]\n\n{entry}");
    let sections: &[&str] = match cmd {
        "build" | "run" | "emit" => &["build options"],
        "test" => &["build options", "test options"],
        "bench" => &["build options", "bench options"],
        "check" => &["check options"],
        "lint" => &["lint options"],
        "fmt" => &["fmt options"],
        _ => &[],
    };
    for s in sections {
        let mut lines = USAGE
            .lines()
            .skip_while(|l| !l.starts_with(&format!("{s}:")));
        out.push('\n');
        if let Some(head) = lines.next() {
            out.push_str(head);
            out.push('\n');
        }
        for l in lines.take_while(|l| l.starts_with(' ') && !l.trim().is_empty()) {
            out.push_str(l);
            out.push('\n');
        }
    }
    out.push_str("\nglobal options and the environment: `rokc help`\n");
    out
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
                    "human" => false,
                    v => usage_error(&format!("unknown message format `{v}`")),
                };
            }
            "-o" | "--out" | "--output" => a.output = Some(value(&name, inline, &mut it).into()),
            "--bootstrap" => a.bootstrap.push(value(&name, inline, &mut it).into()),
            "--cfg" => a.cfg.push(value(&name, inline, &mut it)),
            "--print" => a.print = Some(value(&name, inline, &mut it)),
            "--extern" => a.externs.push(parse_extern(&value(&name, inline, &mut it))),
            "--name" => a.name = Some(value(&name, inline, &mut it)),
            "--target-dir" => a.target_dir = Some(value(&name, inline, &mut it).into()),
            "--target" => a.target = Some(value(&name, inline, &mut it)),
            "--rokr" => a.opts.rokr = value(&name, inline, &mut it),
            "-L" => a.opts.lib_dirs.push(value(&name, inline, &mut it).into()),
            s if s.starts_with("-L") => a.opts.lib_dirs.push(s[2..].into()),
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
            "--emit" => {
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
                match v.as_str() {
                    "overflow-checks" | "overflow-checks=yes" | "overflow-checks=on" => {
                        a.opts.overflow_checks = Some(true);
                    }
                    "overflow-checks=no" | "overflow-checks=off" => {
                        a.opts.overflow_checks = Some(false);
                    }
                    "backend=native" | "backend=llvm" => a.opts.backend = Some(v[8..].to_owned()),
                    _ => match v
                        .strip_prefix("subsystem=")
                        .and_then(rokc_interface::Subsystem::parse)
                    {
                        Some(s) => a.opts.subsystem = s,
                        None => usage_error(&format!("unknown codegen option `{v}`")),
                    },
                }
            }
            "--keep" => a.opts.keep_temps = true,
            "-g" | "--debug" => a.opts.debug = true,
            "--check" => a.check = true,
            "--check-library" => a.check_library = true,
            "--std" => a.std = true,
            "--diff" => a.diff = true,
            "--show-output" => a.show_output = true,
            "--list" => a.list = true,
            "--connection-file" => {
                a.connection_file = Some(value(&name, inline, &mut it).into());
            }
            "-A" | "-W" | "-D" | "--allow" | "--warn" | "--deny" => {
                let lvl = Level::from_flag(&name).expect("a lint level flag");
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
                print!("{}", command_help(&a.cmd));
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
    if a.cmd.is_empty() && a.print.is_none() {
        usage_error("missing command");
    }
    if std::env::var_os("ROKC_VERBOSE").is_some_and(|v| !v.is_empty() && v != "0") {
        a.verbose = a.verbose.max(1);
    }
    a
}

/// `--extern name=path` (spec 902.3). The path is the dependency's
/// package directory or its `lib.rok`, or a prebuilt `<name>.rhir` /
/// `lib<name>.a` (spec 904).
fn parse_extern(v: &str) -> (String, PathBuf) {
    let Some((name, path)) = v.split_once('=') else {
        usage_error(&format!("`--extern {v}`: expected <name>=<path>"));
    };
    // A package name (`my-lib`) stands for its code name (`my_lib`).
    let name = &name.replace('-', "_");
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

/// Every pass recurses over the tree (the parser caps its depth): run
/// the whole command on a thread whose stack is sized for that cap in a
/// debug build (address space only until used).
const COMPILER_STACK: usize = 1 << 30;

fn main() {
    // Spec 901.6: an internal error (rokc panic) exits 101.
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        default_hook(info);
        eprintln!("rokc: internal compiler error");
        process::exit(101);
    }));
    std::thread::Builder::new()
        .name("main".into())
        .stack_size(COMPILER_STACK)
        .spawn(real_main)
        .expect("spawn compiler thread")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e));
}

fn real_main() {
    let a = parse_args(std::env::args().skip(1).collect());
    let color = a.color.unwrap_or_else(|| {
        std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none()
    });
    rokc_interface::set_report_style(a.json, color);
    if let Some(what) = &a.print {
        if what != "cfg" {
            usage_error(&format!("`--print` takes `cfg`, not `{what}`"));
        }
        let mut session = Session::new();
        for c in &a.cfg {
            session.add_cfg(c.clone());
        }
        if a.opts.opt_level == "0" {
            session.add_cfg("debug_assertions".to_owned());
        }
        session.set_target(a.target.as_deref());
        for line in session.cfg_lines() {
            println!("{line}");
        }
        return;
    }
    // Commands of one `[path]` (`test` / `bench`: and a filter).
    let most = match a.cmd.as_str() {
        "build" | "emit" | "run" | "check" | "lint" | "doc" | "clean" | "repl" => 1,
        "test" | "bench" => 2,
        _ => usize::MAX,
    };
    if let Some(extra) = a.positional.get(most) {
        usage_error(&format!(
            "unexpected argument `{extra}` (rokc {} --help)",
            a.cmd
        ));
    }
    match a.cmd.as_str() {
        "build" => cmd_build(with_defaults(a)),
        "emit" => {
            let mut a = with_defaults(a);
            if a.emit.is_empty() {
                a.emit.push(EmitKind::Mlir);
            }
            cmd_build(a);
        }
        "check" => cmd_check(with_defaults(a), true),
        "lint" if a.list => print!("{}", rokc_tools::lint::list()),
        "lint" => cmd_check(with_defaults(a), false),
        "lsp" => {
            let mut a = with_defaults(a);
            let pkg = rokc_interface::discover(Path::new(".")).ok();
            // The server starts without the dependencies it cannot build.
            if let Err(e) = prebuild(&mut a, pkg.as_ref()) {
                eprintln!("rokc: warning: {e}");
                a.externs.clear();
            }
            let io = (
                std::io::BufReader::new(std::io::stdin()),
                std::io::stdout().lock(),
            );
            process::exit(rokc_tools::lsp::serve(
                io.0,
                io.1,
                a.bootstrap,
                a.externs,
                a.lint_levels,
            ));
        }
        "repl" => cmd_repl(with_defaults(a)),
        "jupyter" => {
            let mut a = with_defaults(a);
            let Some(file) = a.connection_file.take() else {
                usage_error("usage: rokc jupyter --connection-file <file>");
            };
            let pkg = rokc_interface::discover(Path::new(".")).ok();
            let deps = prebuild(&mut a, pkg.as_ref()).unwrap_or_else(|e| fail(&e));
            process::exit(rokc_tools::jupyter::serve(
                &file,
                a.bootstrap,
                a.externs,
                deps,
                a.opts,
            ));
        }
        "run" => cmd_run(with_defaults(a)),
        "test" => cmd_test(with_defaults(a)),
        "bench" => cmd_bench(with_defaults(a)),
        "doc" => cmd_doc(with_defaults(a)),
        "fmt" => cmd_fmt(&a),
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
        "version" => {
            println!("rokc {}", VERSION);
            if a.verbose > 0 {
                println!("host: {}", env!("ROK_HOST"));
                println!("llvm: {}", rokc_interface::LLVM_VERSION.unwrap_or("none"));
            }
        }
        "help" => match a.positional.first() {
            Some(c) => print!("{}", command_help(c)),
            None => print!("{USAGE}"),
        },
        other => usage_error(&format!("unknown command `{other}`")),
    }
}

/// The implicit `use rok::core::**;` (spec 0.0.5) needs `rok/core`,
/// and linking needs `librokr.a`; find both without flags.
fn with_defaults(mut a: Args) -> Args {
    let sys = rokc_interface::sysroot();
    if a.bootstrap.is_empty() {
        match sys.libs {
            Ok(roots) => a.bootstrap = roots,
            // The language server still starts.
            Err(e) if a.cmd == "lsp" => eprintln!("rokc: warning: {e}"),
            Err(e) => fail(&e),
        }
    }
    a.bootstrap = rokc_interface::bootstrap_tiers(&a.bootstrap);
    let links = matches!(
        a.cmd.as_str(),
        "run" | "test" | "bench" | "repl" | "jupyter"
    ) || (a.cmd == "build" && a.emit.is_empty());
    let host = env!("ROK_HOST");
    let triple = a.target.clone().unwrap_or_else(|| host.to_owned());
    let dir = sys.targets.join(&triple);
    let missing = || {
        format!(
            "no runtime for {triple}: {} is missing (this toolchain does not ship the \
             target; in the repository, run targets/build.sh {triple})",
            dir.display()
        )
    };
    if a.opts.rokr == "rokr" {
        let rokr = if triple == host {
            sys.rokr
        } else {
            Some(dir.join(rokc_core::runtime_lib(triple.contains("-windows"))))
                .filter(|p| p.is_file())
                .ok_or_else(missing)
        };
        match rokr {
            Ok(lib) => a.opts.rokr = lib.display().to_string(),
            Err(e) if links => fail(&e),
            Err(_) => {}
        }
    }
    if triple.contains("-linux") {
        if dir.is_dir() {
            a.opts.libc = Some(dir.clone());
        } else if links {
            fail(&missing());
        }
    }
    a
}

/// The package named by the first positional (default: `.`).
fn discover_arg(a: &Args) -> Package {
    discover_at(a, a.positional.first().map_or(".", String::as_str))
}

/// The package at `path`, named `--name` when given.
fn discover_at(a: &Args, path: &str) -> Package {
    let mut pkg = rokc_interface::discover(Path::new(path)).unwrap_or_else(|e| fail(&e));
    if let Some(n) = a.name.as_ref().filter(|_| !pkg.anonymous) {
        pkg.name.clone_from(n);
    }
    pkg
}

fn create_dir(dir: &Path) {
    if let Err(e) = std::fs::create_dir_all(dir) {
        fail(&format!("cannot create {}: {e}", dir.display()));
    }
}

/// Prebuild the source `--extern`s into `<out dir>/deps` and use their
/// RHIRs; the deps directory.
fn prebuild(a: &mut Args, pkg: Option<&Package>) -> Result<PathBuf, String> {
    let dir = out_dir(a, pkg).join("deps");
    // A native build links the standard library prebuilt.
    if matches!(a.cmd.as_str(), "build" | "run" | "test" | "bench") && a.emit.is_empty() {
        a.std_prebuilt = rokc_interface::prebuilt_std(&rokc_interface::StdKey {
            bootstrap: &a.bootstrap,
            cfg: &a.cfg,
            opts: &a.opts,
            target: a.target.as_deref(),
            test: matches!(a.cmd.as_str(), "test" | "bench"),
        });
    }
    let build = DepBuild {
        bootstrap: &a.bootstrap,
        cfg: &a.cfg,
        opts: &a.opts,
        target: a.target.as_deref(),
        dir: &dir,
        quiet: a.quiet,
        std: a.std_prebuilt.as_deref(),
    };
    a.externs = build.prebuild(&a.externs)?;
    Ok(dir)
}

/// What `compile` builds for.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Build,
    Test,
    Bench,
    /// Front end only, ASTs kept.
    Doc,
}

/// A session for `pkg` with the command line's libraries and flags.
fn session(a: &Args, pkg: &Package) -> Session {
    let mut session = Session::new();
    for b in &a.bootstrap {
        session.add_bootstrap_file(b.clone());
    }
    for c in &a.cfg {
        session.add_cfg(c.clone());
    }
    if a.opts.opt_level == "0" {
        session.add_cfg("debug_assertions".to_owned());
    } else {
        session.set_inline_prebuilt(true);
    }
    for (n, p) in &a.externs {
        session.add_extern(n.clone(), p.clone());
    }
    session.set_anonymous(pkg.anonymous);
    session.set_target(a.target.as_deref());
    session.set_std_prebuilt(a.std_prebuilt.clone());
    session
}

fn progress(a: &Args, verb: &str, pkg: &Package) {
    if !a.quiet {
        eprintln!("{verb:>12} {} ({})", pkg.name, pkg.dir.display());
    }
}

/// Front end for `pkg` (its dependencies prebuilt); reports the warnings
/// (also returned, rendered) and exits 1 on errors. Prints the 901.8
/// progress line unless `-q`.
fn compile(a: &Args, pkg: &Package, mode: Mode) -> (CompileResult, String, Instant) {
    let started = Instant::now();
    progress(
        a,
        if mode == Mode::Doc {
            "Documenting"
        } else {
            "Compiling"
        },
        pkg,
    );
    let mut session = session(a, pkg);
    // A library's `build` is a prebuilt library: `lib<name>.a` + RHIR.
    if pkg.lib && matches!(a.cmd.as_str(), "build" | "emit") {
        session.set_lib_name(Some(lib_name(a, pkg)));
    }
    session.set_test(mode == Mode::Test);
    session.set_bench(mode == Mode::Bench);
    session.set_keep_ast(
        mode == Mode::Doc
            || a.emit.contains(&EmitKind::Expanded)
            || a.emit.contains(&EmitKind::Ast),
    );
    rokc_interface::clear_files();
    let result = session.compile_file(&pkg.root);
    let warnings: String = result.warnings.iter().map(render).collect();
    print_rendered(&warnings);
    if result.has_errors() {
        result.report_errors();
        process::exit(1);
    }
    stage(a, "front end", started);
    if a.verbose > 1 && !a.quiet {
        eprint!("{}", result.trace());
    }
    (result, warnings, started)
}

/// A library's package name: `--name`, else its directory's (made an
/// identifier).
fn lib_name(a: &Args, pkg: &Package) -> String {
    // `my-app` is `my_app` in code and symbols.
    let n: String = a
        .name
        .as_ref()
        .unwrap_or(&pkg.name)
        .chars()
        .map(|c| if c.is_alphanumeric() { c } else { '_' })
        .collect();
    if n.starts_with(|c: char| c.is_ascii_digit()) {
        format!("_{n}")
    } else {
        n
    }
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

/// Cargo-like output directory: `<target>/[<triple>/]<profile>/`, the
/// profile `release` at `-O2` and above or `-Os`, else `debug`. Without a
/// package, `<target>` is the system temp directory's `rokc-target/`.
fn out_dir(a: &Args, pkg: Option<&Package>) -> PathBuf {
    let mut dir = a
        .target_dir
        .clone()
        .or_else(|| pkg.map(Package::target_dir))
        .or_else(|| std::env::var_os("ROKC_TARGET_DIR").map(PathBuf::from))
        .unwrap_or_else(|| std::env::temp_dir().join("rokc-target"));
    if let Some(t) = &a.target {
        dir.push(t);
    }
    let release = matches!(a.opts.opt_level.as_str(), "2" | "3" | "s");
    dir.join(if release { "release" } else { "debug" })
}

/// The file name of executable `name` for the build's target: `.exe` on
/// Windows.
fn exe_file(a: &Args, name: &str) -> String {
    let windows = a
        .target
        .as_deref()
        .map_or(cfg!(windows), |t| t.contains("-windows"));
    if windows {
        format!("{name}.exe")
    } else {
        name.to_owned()
    }
}

/// Layout: `target/<profile>/<name>` (executable, `<name>.exe` for Windows),
/// `target/<profile>/lib<name>.a` + `<name>.rhir` (library),
/// `target/<profile>/build/<name>.<ext>` (`--emit`).
fn cmd_build(mut a: Args) {
    let pkg = discover_arg(&a);
    prebuild(&mut a, Some(&pkg)).unwrap_or_else(|e| fail(&e));
    let target = out_dir(&a, Some(&pkg));
    if !a.emit.is_empty() {
        let (result, _, started) = compile(&a, &pkg, Mode::Build);
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
            stage(&a, &format!("emit {}", kind.extension()), t);
            if !a.quiet {
                eprintln!("       Wrote {}", out.display());
            }
        }
        finished(&a, started);
        return;
    }
    let out = a.output.clone().unwrap_or_else(|| {
        create_dir(&target);
        target.join(if pkg.lib {
            format!("lib{}.a", lib_name(&a, &pkg))
        } else {
            exe_file(&a, &pkg.name)
        })
    });
    build_fresh(&a, &pkg, &out, |a, result| {
        if !a.quiet {
            eprintln!("    Building {}", out.display());
        }
        if pkg.lib {
            fail_on(result.archive(&a.opts, &out));
        } else {
            fail_on(result.link(&a.opts, &out));
        }
    });
}

/// Build `pkg` into `out` with `link` unless the record says it is up to
/// date (then its warnings are printed again).
fn build_fresh(a: &Args, pkg: &Package, out: &Path, link: impl FnOnce(&Args, &CompileResult)) {
    let fp = fingerprint(a, pkg, out);
    if let Some(warnings) = fp.fresh() {
        print_rendered(&warnings);
        if !a.quiet {
            eprintln!("       Fresh {} ({})", pkg.name, pkg.dir.display());
        }
        return;
    }
    fp.clear();
    let (result, warnings, started) = compile(a, pkg, Mode::Build);
    let t = Instant::now();
    link(a, &result);
    fp.save(&result.files, &warnings);
    stage(a, "codegen + link", t);
    finished(a, started);
}

/// The incremental-build key of `pkg` built into `out` (see `Fingerprint`).
fn fingerprint(a: &Args, pkg: &Package, out: &Path) -> Fingerprint {
    let mut words = vec![
        format!("{:?}", a.opts),
        out.display().to_string(),
        pkg.root.display().to_string(),
        std::env::var("PATH").unwrap_or_default(),
        std::env::var("ROK_CC").unwrap_or_default(),
    ];
    words.extend(a.cfg.iter().cloned());
    words.extend(pkg.lib.then(|| lib_name(a, pkg)));
    let mut inputs = vec![if pkg.anonymous {
        pkg.root.clone()
    } else {
        pkg.dir.clone()
    }];
    let mut stamped = vec![PathBuf::from(&a.opts.rokr)];
    stamped.extend(a.opts.mlir_dialect_plugins.iter().cloned());
    stamped.extend(a.opts.mlir_pass_plugins.iter().cloned());
    for b in &a.bootstrap {
        words.push(b.display().to_string());
        inputs.push(b.parent().map_or_else(|| b.clone(), Path::to_path_buf));
    }
    for (n, p) in &a.externs {
        words.push(format!("{n}={}", p.display()));
        let (rhir, archive) = rokc_interface::rhir::companions(p);
        inputs.push(rhir);
        stamped.push(archive);
    }
    let also = if pkg.lib {
        vec![rokc_interface::rhir::companions(out).0]
    } else {
        Vec::new()
    };
    Fingerprint::new(out, also, &words, &inputs, &stamped)
}

/// `rokc check` (with codegen) and `rokc lint` (without): the check
/// pipeline over the package; exit 1 on an error or a `deny` lint.
fn cmd_check(mut a: Args, codegen: bool) {
    // `check -`: the source is stdin (901.9), an anonymous package.
    let stdin = a.positional.first().is_some_and(|p| p == "-");
    let pkg = if stdin {
        Package::stdin()
    } else {
        discover_arg(&a)
    };
    prebuild(&mut a, Some(&pkg)).unwrap_or_else(|e| fail(&e));
    let started = Instant::now();
    progress(&a, "Checking", &pkg);
    let source = stdin.then(|| {
        let mut src = String::new();
        if let Err(e) = std::io::Read::read_to_string(&mut std::io::stdin(), &mut src) {
            fail(&format!("cannot read stdin: {e}"));
        }
        src
    });
    let mut session = session(&a, &pkg);
    session.set_check_library(a.check_library);
    rokc_interface::clear_files();
    let (_, diags) = rokc_tools::analysis::check(
        &mut session,
        source.as_deref(),
        &pkg.root,
        &a.lint_levels,
        codegen.then_some(&a.opts),
    );
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
    finished(&a, started);
    process::exit(i32::from(errors > 0));
}

fn cmd_repl(mut a: Args) {
    // Standard input is the cell input (901.2).
    if a.positional.first().is_some_and(|p| p == "-") {
        usage_error("`rokc repl -`: standard input is the cell input; give a path or none");
    }
    // `repl <path>`: a library is a dependency of the session, and its
    // first cell is `use <name>::*;` (901.2); a program is loaded into it.
    let pkg = a.positional.first().map(|p| discover_at(&a, p));
    let prelude = pkg.as_ref().filter(|p| p.lib).map(|p| {
        let name = lib_name(&a, p);
        a.externs.push((name.clone(), p.root.clone()));
        format!("use {name}::*;")
    });
    let here = rokc_interface::discover(Path::new(".")).ok();
    let deps = prebuild(&mut a, pkg.as_ref().or(here.as_ref())).unwrap_or_else(|e| fail(&e));
    let program = pkg
        .as_ref()
        .filter(|p| !p.lib)
        .map(|p| (p.root.as_path(), p.anonymous));
    process::exit(rokc_tools::repl::main(
        a.bootstrap,
        a.externs,
        deps,
        a.opts,
        std::io::stdin().is_terminal(),
        prelude.as_deref(),
        program,
    ));
}

fn cmd_run(mut a: Args) {
    let pkg = discover_arg(&a);
    if pkg.lib {
        fail(&format!(
            "`{}` is a library package (`lib.rok`); there is nothing to run",
            pkg.dir.display()
        ));
    }
    prebuild(&mut a, Some(&pkg)).unwrap_or_else(|e| fail(&e));
    // An anonymous file builds in a scratch directory (no `target/` next
    // to a loose script); a package builds into its `target/`.
    let tmp = fail_on(TempDir::new(a.opts.keep_temps));
    let exe = match &a.output {
        Some(o) => o.clone(),
        None if pkg.anonymous => tmp.path().join(exe_file(&a, &pkg.name)),
        None => {
            let target = out_dir(&a, Some(&pkg));
            create_dir(&target);
            target.join(exe_file(&a, &pkg.name))
        }
    };
    let link = |a: &Args, result: &CompileResult| fail_on(result.link(&a.opts, &exe));
    if a.output.is_some() || !pkg.anonymous {
        build_fresh(&a, &pkg, &exe, link);
    } else {
        let (result, _, started) = compile(&a, &pkg, Mode::Build);
        let t = Instant::now();
        link(&a, &result);
        stage(&a, "codegen + link", t);
        finished(&a, started);
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
fn cmd_test(mut a: Args) {
    let (path, filter) = path_and_filter(&a);
    let filter = filter.map(str::to_owned);
    let pkg = discover_at(&a, path);
    prebuild(&mut a, Some(&pkg)).unwrap_or_else(|e| fail(&e));
    let (result, _, started) = compile(&a, &pkg, Mode::Test);
    let tmp = fail_on(TempDir::new(a.opts.keep_temps));
    let exe = tmp.path().join(exe_file(&a, &format!("{}-test", pkg.name)));
    let t = Instant::now();
    fail_on(result.link(&a.opts, &exe));
    stage(&a, "codegen + link", t);
    finished(&a, started);
    let threads = a
        .threads
        .or_else(|| std::env::var("ROKC_NUM_JOBS").ok()?.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, usize::from));
    let ok = test_runner::run(
        &exe,
        &result.tests,
        &test_runner::Options {
            filter: filter.as_deref(),
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
    let filter = filter.map(str::to_owned);
    let pkg = discover_at(&a, path);
    prebuild(&mut a, Some(&pkg)).unwrap_or_else(|e| fail(&e));
    let (result, _, started) = compile(&a, &pkg, Mode::Bench);
    let tmp = fail_on(TempDir::new(a.opts.keep_temps));
    let exe = tmp
        .path()
        .join(exe_file(&a, &format!("{}-bench", pkg.name)));
    let t = Instant::now();
    fail_on(result.link(&a.opts, &exe));
    stage(&a, "codegen + link", t);
    finished(&a, started);
    let ok = bench_runner::run(
        &exe,
        &result.tests,
        &bench_runner::Options {
            filter: filter.as_deref(),
            iters: a.iters,
            samples: a.samples.unwrap_or(10),
        },
    );
    drop(tmp);
    process::exit(i32::from(!ok));
}

/// `rokc doc [path]`: HTML into `target/doc/` (see `rokc_tools::doc`).
fn cmd_doc(mut a: Args) {
    // `--std` alone: an empty package that only mounts the library.
    let std_only = a.std && a.positional.is_empty();
    let tmp = std_only.then(|| fail_on(TempDir::new(a.opts.keep_temps)));
    if let Some(t) = &tmp {
        let main = t.path().join("main.rok");
        std::fs::write(&main, "")
            .unwrap_or_else(|e| fail(&format!("cannot write {}: {e}", main.display())));
        a.positional.push(main.display().to_string());
        a.name.get_or_insert_with(|| "rok".to_owned());
    }
    let pkg = discover_arg(&a);
    prebuild(&mut a, Some(&pkg)).unwrap_or_else(|e| fail(&e));
    let (result, _, started) = compile(&a, &pkg, Mode::Doc);
    let out = a
        .target_dir
        .clone()
        .unwrap_or_else(|| {
            if std_only {
                PathBuf::from("target")
            } else {
                pkg.target_dir()
            }
        })
        .join("doc");
    let docs = rokc_tools::doc::Scope {
        user: !std_only,
        std: a.std,
    };
    let index = rokc_tools::doc::generate(&result, &pkg.name, &out, docs)
        .unwrap_or_else(|e| fail(&format!("cannot write {}: {e}", out.display())));
    drop(tmp);
    finished(&a, started);
    if !a.quiet {
        eprintln!("   Generated {}", index.display());
    }
}

/// `rokc fmt [path]`: a file, or every source file under a directory.
fn cmd_fmt(a: &Args) {
    let roots: Vec<PathBuf> = if a.positional.is_empty() {
        vec![PathBuf::from(".")]
    } else {
        a.positional.iter().map(PathBuf::from).collect()
    };
    let mut files = Vec::new();
    for r in &roots {
        if r.is_dir() {
            files.extend(rokc_interface::source_files(r));
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
        let formatted = match rokc_fmt::format_file(f, &src) {
            Ok(s) => s,
            Err(e) if e.starts_with("error[") => {
                eprintln!("{e}");
                errors += 1;
                continue;
            }
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

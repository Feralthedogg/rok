//! `rok`: the toolchain front (spec 901). It owns `rok.rokon` /
//! `rok.lock`, dependency resolution, stones (registry packages) and the
//! git cache, environments,
//! toolchains, package scaffolding and the Jupyter kernelspec, and runs
//! the compiler `rokc` (next to itself, or a pinned toolchain's) with the
//! resolved dependencies as `--extern name=lib.rok`; rokc prebuilds them.
//!
//! ```text
//! $ROK_HOME/bin/{rok,rokc,rokls}     proxies to the active toolchain (`toolchain`)
//! $ROK_HOME/toolchains/<version>-<triple>/
//!                                    a toolchain: bin/{rok,rokc,rokls}, lib/
//! $ROK_HOME/cache/git/               shared git cache (see `git`)
//! $ROK_HOME/cache/registry/          stone index clones (see `registry`)
//! $ROK_HOME/cache/native/            native packages, by SHA-256 (see `native`)
//! $ROK_HOME/config.rokon             `Config { registry: "<index url>", toolchain: "<default>" }`
//! $ROK_HOME/cache/scripts/<hash>/    a script's lock and prebuilt dependencies
//! $ROK_HOME/envs/<name>/             a named environment (rok.rokon, rok.lock, target/)
//! $ROK_HOME/envs/CURRENT             `rok env use`'s choice
//! ```

mod env;
mod git;
mod lock;
mod manifest;
mod native;
mod registry;
mod resolve;
mod semver;
mod toolchain;

pub use toolchain::proxy;

use std::path::{Path, PathBuf};
use std::process::Command;

use manifest::{Dep, GitRef, MANIFEST, Manifest, NativeSource, Source};
use resolve::{Context, Options, Resolved};
use rokc_diagnostic::Json;
use rokc_rokon::{Kind, Value};

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
/// `VERSION`, and the commit and its date when built from git.
pub const VERSION_LINE: &str = concat!(env!("CARGO_PKG_VERSION"), env!("ROK_COMMIT_INFO"));

const USAGE: &str = "\
usage: rok [options] <command> [args]
       rok [options]                same as `rok repl`

packages:
  new [--lib|--bin] <name>     create a package (with rok.rokon)
  init [--lib|--bin] [dir]     make a directory a package
  add <name>[@<req>] [--registry <url>]
                               add a stone (default: ^ the newest version)
  add <name> --path <dir>      add a dependency (--dev: to dev_deps)
  add <name> --git <url> [--rev <r> | --tag <t> | --branch <b>]
  add --native <name>[@<req>] [--registry <url>]
                               add a native package (prebuilt C library)
  remove [--native] <name>     remove a dependency
  update [name...]             re-resolve git dependencies and stones,
                               rewrite rok.lock
  search [--native] <query>    stones (native packages) whose name contains
                               <query>
  deps                         print the resolved dependencies (name=lib.rok),
                               each after its own; native packages as
                               `# native <name> <vers>` and their rokc
                               arguments, one per line
  clean [path]                 remove target/

stones (the index is a git repository; sources are not uploaded):
  login [<token>]              keep a registry token (from <api>/me, e.g.
                               https://rokstones.io/me; read from stdin if
                               not given) in $ROK_HOME/credentials.rokon,
                               after checking its account may publish
  logout                       remove it
  publish [--index <dir>] [--commit]
                               the index entry for this package (its git
                               remote `origin`, HEAD commit and tree); a dry
                               run, checked against the index checkout <dir>
                               if given. --commit: commit it to <dir>, or
                               without --index, send it to the registry API
                               (needs `rok login`)
  publish --native <file> [--index <dir>] [--commit]
                               the index entry of the native package
                               `Native { .. }` in <file>, each build fetched
                               and checked
  yank [--native] --vers <v> [--undo] [--index <dir>] [name]
                               mark a version yanked: committed to <dir>, or
                               through the registry API (needs `rok login`);
                               --native: a native package's (named)

compiler commands (rokc, with the dependencies; see `rokc help`):
  build | check | run | test | bench | lint | doc | emit [path] ...
  repl [path]                  interactive session (`:add <dep>` adds to the
                               active environment); a program path runs in
                               it first, a library is loaded and `use`d
  lsp                          language server (also `rokls`)
  jupyter --connection-file <f>  the kernel (Jupyter starts it)
  fmt [path]                   format .rok and .rokon files

  The path, if any, comes first after the command; it picks the project
  (or script) whose dependencies and `lints` apply. A .rok file inside a
  project (the nearest directory above it with main.rok, lib.rok or
  rok.rokon) uses that project's.

jupyter:
  jupyter install              install the `rok` Jupyter kernel (with --env:
                               `rok-<env>`, running in that environment)

environments:
  env create|remove|use <name>      a named environment
  env list                          (`*`: the active one)
  env export <name> <dir>           write its rok.rokon / rok.lock to <dir>
  env import <name> <dir|rok.rokon> create it from a project or export
  env shell [name]                  a $SHELL with ROK_ENV=<name>

toolchains ($ROK_HOME/toolchains/<version>-<triple>/):
  toolchain list               installed toolchains
  toolchain install <version> --from <dir | .tar[.gz] | .zip | url>
                               install one (the first becomes the default)
  toolchain default [<version>]
                               the toolchain the $ROK_HOME/bin proxies run
  toolchain remove <version>   remove one
  +<version>                   (first) use that toolchain for this command;
                               else $ROK_TOOLCHAIN, else rok.rokon's
                               `toolchain`, else the default

options (anywhere before `--`):
  --env <name>    use that environment instead of the project's
  --offline       never fetch (git dependencies must be cached)
  --locked        fail instead of changing rok.lock
  --cwd <dir>     change directory first
  -q, --quiet     less output
  version, help

A directory with rok.rokon is a project (its own environment). Outside one,
the environment is $ROK_ENV, else the one `rok env use` chose, else
`default`. A lone script may start with a //! ```rokon block holding
`Package { deps: {..} }`.

Shared lint levels: `lints_from: \"<dir>\"` in rok.rokon starts from the
`lints` of <dir>/rok.rokon (and its own `lints_from`, recursively); this
manifest's `lints` then override per lint.

`rok <command> --help` (or `rok help <command>`) shows one command.

environment: ROK_HOME (default: ~/.rok), ROK_ENV, ROK_TOOLCHAIN,
  ROK_REGISTRY (the stone index; else `registry` in $ROK_HOME/config.rokon,
  else https://github.com/rok-lang/rokstones.io-index),
  ROK_REGISTRY_TOKEN (instead of `rok login`'s token)
";

#[derive(Default)]
struct Global {
    env: Option<String>,
    offline: bool,
    locked: bool,
    quiet: bool,
    /// `+<version>`.
    toolchain: Option<String>,
}

/// The user's rok directory (`rokc_core::rok_home`).
pub fn home() -> PathBuf {
    rokc_core::rok_home().unwrap_or_else(|| PathBuf::from(".rok"))
}

/// Fields of `$ROK_HOME/config.rokon` (`Config { .. }`).
const CONFIG_FIELDS: [&str; 2] = ["registry", "toolchain"];

/// String field `field` of `$ROK_HOME/config.rokon`.
fn config(home: &Path, field: &str) -> Result<Option<String>, String> {
    let path = home.join("config.rokon");
    let Ok(text) = std::fs::read_to_string(&path) else {
        return Ok(None);
    };
    let file = path.display().to_string();
    let doc = rokc_rokon::Doc::parse(&text, &file)?;
    let c = doc.root().record("Config")?;
    c.only(&CONFIG_FIELDS)?;
    c.opt(field).map(|r| r.string()).transpose()
}

/// Set string field `field` of `$ROK_HOME/config.rokon`, keeping the rest.
fn set_config(home: &Path, field: &str, value: &str) -> Result<(), String> {
    let path = home.join("config.rokon");
    let file = path.display().to_string();
    std::fs::create_dir_all(home).map_err(|e| format!("{}: {e}", home.display()))?;
    let old = std::fs::read_to_string(&path).unwrap_or_else(|_| "Config {}\n".to_owned());
    config(home, field)?;
    let step = [rokc_rokon::edit::Step::Field(field)];
    let text = rokc_rokon::edit::set(&old, &step, &rokc_rokon::quote(value))
        .map_err(|e| e.render(&old, &file))?;
    std::fs::write(&path, canonical_edit(&old, &text))
        .map_err(|e| format!("cannot write {file}: {e}"))
}

/// `new`, an edit of ROKON text `old`: in canonical form (spec 3.9.4)
/// when `old` was, else as edited (comments and layout kept).
fn canonical_edit(old: &str, new: &str) -> String {
    let canon = |t: &str| rokc_rokon::parse(t).ok().map(|v| rokc_rokon::to_string(&v));
    match (canon(old), canon(new)) {
        (Some(o), Some(n)) if o.trim() == old.trim() => n + "\n",
        _ => new.to_owned(),
    }
}

/// Run `rok` with `args` (without the program name); the exit code.
pub fn main_with(args: Vec<String>) -> i32 {
    let mut g = Global::default();
    let mut rest = Vec::new();
    let mut it = args.into_iter();
    // rok's own options, anywhere before `--`; the rest goes to rokc.
    while let Some(a) = it.next() {
        let (name, inline) = match a.split_once('=') {
            Some((n, v)) if n.starts_with("--") => (n.to_owned(), Some(v.to_owned())),
            _ => (a.clone(), None),
        };
        let value = |it: &mut std::vec::IntoIter<String>| inline.clone().or_else(|| it.next());
        match name.as_str() {
            "--" => {
                rest.push(a);
                rest.extend(it.by_ref());
            }
            "--env" => match value(&mut it) {
                Some(v) => g.env = Some(v),
                None => return usage("`--env` needs a name"),
            },
            "--offline" => g.offline = true,
            "--locked" => g.locked = true,
            "--cwd" => {
                let Some(dir) = value(&mut it) else {
                    return usage("`--cwd` needs a directory");
                };
                if let Err(e) = std::env::set_current_dir(&dir) {
                    return usage(&format!("--cwd {dir}: {e}"));
                }
            }
            "-q" | "--quiet" => {
                g.quiet = true;
                rest.push(a);
            }
            // `rok +<version> ..` (spec 9.10.6), before the command.
            t if t.len() > 1 && t.starts_with('+') && rest.iter().all(|r| r.starts_with('-')) => {
                g.toolchain = Some(t[1..].to_owned());
            }
            _ => rest.push(a),
        }
    }
    // The command: the first word that is not an option. rokc options
    // with a separate value go after it.
    let Some(i) = rest.iter().position(|a| !a.starts_with('-') || a == "--") else {
        if rest.iter().any(|a| a == "-V" || a == "--version") {
            println!("rok {VERSION_LINE}");
            return 0;
        }
        if rest.iter().any(|a| a == "-h" || a == "--help") {
            print!("{USAGE}");
            return 0;
        }
        // Bare `rok` (options only) is `rok repl`, like `python` / `julia`.
        return run(&g, "repl", &rest, &[]);
    };
    if rest[i] == "--" {
        return run(&g, "repl", &rest[..i], &rest[i..]);
    }
    let (cmd, post) = (&rest[i], &rest[i + 1..]);
    let before_dashes = post.iter().take_while(|a| *a != "--");
    if before_dashes
        .into_iter()
        .any(|a| a == "-h" || a == "--help")
    {
        return help(&g, cmd);
    }
    run(&g, cmd, &rest[..i], post)
}

/// The commands `rok` passes to `rokc`.
const DELEGATED: [&str; 15] = [
    "build", "check", "run", "test", "repl", "lsp", "fmt", "clean", "demangle", "emit", "bench",
    "doc", "lint", "jupyter", "profdata",
];

/// `rok <cmd> --help` / `rok help <cmd>`: rok's own entry, or rokc's
/// help for a command it runs.
fn help(g: &Global, cmd: &str) -> i32 {
    if cmd == "toolchain" {
        println!("{}", toolchain::USAGE);
        return 0;
    }
    if DELEGATED.contains(&cmd) && cmd != "jupyter" {
        return match toolchain::rokc_for(g.toolchain.as_deref(), None) {
            Ok(rokc) => {
                let mut c = Command::new(&rokc);
                c.args([cmd, "--help"]);
                exec(c, &rokc)
            }
            Err(e) => {
                eprintln!("rok: error: {e}");
                1
            }
        };
    }
    match rokc_core::command_help(USAGE, cmd) {
        Some(entry) => {
            print!("usage: rok [options] {cmd} ..\n\n{entry}");
            0
        }
        None => usage(&format!("unknown command `{cmd}`")),
    }
}

/// Errors that are about the command line (exit code 2, spec 9.1.6).
fn is_usage(e: &str) -> bool {
    [
        "usage:",
        "unknown option",
        "unexpected argument",
        "give at most one of",
    ]
    .iter()
    .any(|p| e.starts_with(p))
        || e.starts_with('`') && e.contains("` needs a value")
}

fn run(g: &Global, cmd: &str, pre: &[String], post: &[String]) -> i32 {
    let r = match cmd {
        "version" => {
            println!("rok {VERSION_LINE}");
            Ok(0)
        }
        "help" if !post.is_empty() => return help(g, &post[0]),
        "help" => {
            print!("{USAGE}");
            Ok(0)
        }
        "new" | "init" => cmd_new(g, cmd, post),
        "add" => cmd_add(g, post),
        "remove" => cmd_remove(g, post),
        "update" => cmd_update(g, post),
        "deps" => cmd_deps(g, post),
        "search" => cmd_search(g, post),
        "publish" => cmd_publish(g, post),
        "yank" => cmd_yank(g, post),
        "login" => cmd_login(g, post),
        "logout" => cmd_logout(g, post),
        "env" => env::cmd(g, post),
        "toolchain" => toolchain::cmd(post, g.quiet),
        "jupyter" if post.first().is_some_and(|p| p == "install") => install_kernel(g, &post[1..]),
        c if DELEGATED.contains(&c) => delegate(g, cmd, pre, post),
        other => return usage(&format!("unknown command `{other}`")),
    };
    r.unwrap_or_else(|e| {
        if is_usage(&e) {
            return usage(&e);
        }
        // A rendered diagnostic (`error[E..]: ..`) as it is.
        if e.starts_with("error[") {
            eprintln!("{e}");
        } else {
            eprintln!("rok: error: {e}");
        }
        1
    })
}

fn usage(msg: &str) -> i32 {
    eprintln!("rok: {msg}\nrun `rok help` for usage");
    2
}

/// The package directory `start` belongs to: the nearest directory at
/// or above it holding `main.rok`, `lib.rok` or `rok.rokon`.
fn package_dir(start: &Path) -> Option<PathBuf> {
    let abs = std::path::absolute(start).ok()?;
    let from = if abs.is_file() { abs.parent()? } else { &abs };
    from.ancestors()
        .find(|d| {
            d.join("main.rok").is_file()
                || d.join("lib.rok").is_file()
                || manifest::find(d).is_some()
        })
        .map(Path::to_path_buf)
}

/// What a command works on, and where its dependencies are prebuilt when
/// it is not a package (an environment's or a script's `target/`).
struct Target {
    ctx: Context,
    env: Option<String>,
    target_dir: Option<PathBuf>,
}

fn env_dir(name: &str) -> PathBuf {
    home().join("envs").join(name)
}

/// The environment used outside a project: `$ROK_ENV`, `rok env use`'s
/// choice, or `default`.
fn ambient_env() -> String {
    std::env::var("ROK_ENV")
        .ok()
        .filter(|e| !e.is_empty())
        .or_else(|| {
            let s = std::fs::read_to_string(home().join("envs/CURRENT")).ok()?;
            Some(s.trim().to_owned()).filter(|s| !s.is_empty())
        })
        .unwrap_or_else(|| "default".to_owned())
}

fn load_dir(dir: &Path) -> Result<Context, String> {
    let manifest = match manifest::find(dir) {
        Some(p) => {
            let mut m = manifest::load(&p)?;
            m.lints = manifest::inherit_lints(&m, &p)?;
            m
        }
        None => Manifest::default(),
    };
    Ok(Context {
        manifest,
        base: dir.to_path_buf(),
        lock_path: dir.is_dir().then(|| dir.join(manifest::LOCK)),
    })
}

fn env_target(name: &str) -> Result<Target, String> {
    Ok(Target {
        ctx: load_dir(&env_dir(name))?,
        env: Some(name.to_owned()),
        target_dir: Some(env_dir(name).join("target")),
    })
}

/// The context for `path` (default: the working directory).
fn target_for(g: &Global, path: Option<&str>) -> Result<Target, String> {
    if let Some(name) = &g.env {
        if !env_dir(name).is_dir() && name != "default" {
            return Err(format!(
                "no environment `{name}` (create it: rok env create {name})"
            ));
        }
        return env_target(name);
    }
    let start = Path::new(path.unwrap_or("."));
    if let Some(dir) = package_dir(start) {
        if manifest::find(&dir).is_some() {
            return Ok(Target {
                ctx: load_dir(&dir)?,
                env: None,
                target_dir: None,
            });
        }
    } else if start.is_file() {
        // A lone script: its own `//! ```rokon` block, if any.
        let src = std::fs::read_to_string(start).unwrap_or_default();
        let file = format!("{} (//! rokon block)", start.display());
        if let Some(block) = manifest::script_block(&src) {
            let manifest = manifest::parse(&block, &file)?;
            if manifest.dev_deps.len() + manifest.lints.len() > 0
                || manifest.lints_from.is_some()
                || manifest.toolchain.is_some()
                || manifest.name.is_some()
                || manifest.version.is_some()
            {
                return Err(format!("{file}: a script block holds only `deps`"));
            }
            let abs = rokc_core::real_path(start).map_err(|e| e.to_string())?;
            let key = format!("{}\0{block}", abs.display());
            let cache = home()
                .join("cache/scripts")
                .join(format!("{:016x}", rokc_core::hash::fnv(key.as_bytes())));
            std::fs::create_dir_all(&cache).map_err(|e| format!("{}: {e}", cache.display()))?;
            return Ok(Target {
                ctx: Context {
                    manifest,
                    base: abs.parent().unwrap_or_else(|| Path::new("/")).to_path_buf(),
                    lock_path: Some(cache.join(manifest::LOCK)),
                },
                env: None,
                target_dir: Some(cache.join("target")),
            });
        }
    }
    env_target(&ambient_env())
}

const fn options(g: &Global) -> Options {
    Options {
        offline: g.offline,
        locked: g.locked,
        update: None,
        quiet: g.quiet,
    }
}

/// Run `rokc <pre> <cmd> [--extern..] [lint levels] [--target-dir] <post>`.
fn delegate(g: &Global, cmd: &str, pre: &[String], post: &[String]) -> Result<i32, String> {
    // The path, when given, is the first argument after the command.
    let path = post
        .first()
        .map(String::as_str)
        .filter(|p| !p.starts_with('-') && Path::new(p).exists());
    // Commands on a package say so here, before resolving anything.
    let start = Path::new(path.unwrap_or("."));
    let stdin = post.first().is_some_and(|p| p == "-");
    let package = package_dir(start);
    if matches!(
        cmd,
        "build" | "check" | "run" | "test" | "bench" | "doc" | "lint" | "emit" | "clean"
    ) && package.is_none()
        && !start.is_file()
        && !stdin
    {
        return Err(format!(
            "not inside a package: no main.rok or lib.rok in {} or above (make one with `rok new \
             <name>` or `rok init`, or name a .rok file)",
            std::path::absolute(start)
                .unwrap_or_else(|_| start.to_path_buf())
                .display()
        ));
    }
    let t = target_for(g, path)?;
    let mut extra: Vec<String> = Vec::new();
    // The manifest's `name` is the package's (spec 9.10.3).
    let named = package.as_deref().filter(|_| t.env.is_none() && !stdin);
    if let (Some(name), Some(_)) = (&t.ctx.manifest.name, named) {
        if !matches!(
            cmd,
            "fmt" | "clean" | "demangle" | "profdata" | "lsp" | "jupyter"
        ) {
            extra.push(format!("--name={name}"));
        }
    }
    if !matches!(cmd, "fmt" | "clean" | "demangle" | "profdata") {
        let graph = match resolve::resolve(&home(), &t.ctx, &options(g)) {
            Ok(r) => r,
            // The language server still starts (without dependencies).
            Err(e) if cmd == "lsp" => {
                eprintln!("rok: warning: {e}");
                resolve::Graph {
                    packages: Vec::new(),
                    natives: Vec::new(),
                }
            }
            Err(e) => return Err(e),
        };
        let dev_too = matches!(cmd, "test" | "bench");
        for p in graph.packages.iter().filter(|p| dev_too || !p.dev) {
            extra.push("--extern".to_owned());
            extra.push(format!(
                "{}={}",
                manifest::code_name(&p.name),
                p.root.display()
            ));
        }
        // Native packages: what a link (or the REPL's session) needs, for
        // the build's target. Checks link nothing.
        if matches!(cmd, "build" | "run" | "test" | "bench" | "repl" | "jupyter") {
            let natives: Vec<&native::Resolved> =
                graph.natives.iter().filter(|n| dev_too || !n.dev).collect();
            if !natives.is_empty() {
                let target = rokc_target::TargetSpec::resolve(target_arg(post))?;
                extra.extend(native::rokc_args(
                    &home(),
                    &natives,
                    &target,
                    g.offline,
                    g.quiet,
                )?);
            }
        }
        // `lints` go first: the command line's own `-A/-W/-D` win.
        for (name, level) in &t.ctx.manifest.lints {
            extra.push(level.flag().to_owned());
            extra.push(name.clone());
        }
        let in_package = package_dir(Path::new(path.unwrap_or("."))).is_some();
        if let Some(dir) = t.target_dir.as_ref().filter(|_| !in_package) {
            extra.push(format!("--target-dir={}", dir.display()));
        }
    }
    let rokc = toolchain::rokc_for(g.toolchain.as_deref(), t.ctx.manifest.toolchain.as_deref())?;
    let mut c = Command::new(&rokc);
    c.args(pre).arg(cmd).args(&extra).args(post);
    if let Ok(me) = std::env::current_exe() {
        c.env("ROK", me);
    }
    if let Some(e) = &t.env {
        c.env("ROK_ENV", e);
    }
    Ok(exec(c, &rokc))
}

/// `--target <t>` / `--target=<t>` among rokc's arguments.
fn target_arg(post: &[String]) -> Option<&str> {
    let mut it = post.iter().take_while(|a| *a != "--");
    while let Some(a) = it.next() {
        if a == "--target" {
            return it.next().map(String::as_str);
        }
        if let Some(t) = a.strip_prefix("--target=") {
            return Some(t);
        }
    }
    None
}

/// Replace this process with `c` (unix), else wait for it.
pub(crate) fn exec(mut c: Command, what: &Path) -> i32 {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        let e = c.exec();
        eprintln!("rok: error: cannot run {}: {e}", what.display());
        1
    }
    #[cfg(windows)]
    {
        // Ctrl-C / Ctrl-Break reach every process on the console: the
        // child decides, this one waits for it. (A handler, unlike the
        // `NULL` one, is not inherited.)
        unsafe extern "system" {
            fn SetConsoleCtrlHandler(
                handler: Option<extern "system" fn(u32) -> i32>,
                add: i32,
            ) -> i32;
        }
        const extern "system" fn ignore(_: u32) -> i32 {
            1
        }
        // SAFETY: registers a handler that only returns.
        unsafe { SetConsoleCtrlHandler(Some(ignore), 1) };
    }
    #[cfg(not(unix))]
    match c.status() {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => {
            eprintln!("rok: error: cannot run {}: {e}", what.display());
            1
        }
    }
}

const MAIN_TEMPLATE: &str = "println(\"Hello, world!\");\n";

const LIB_TEMPLATE: &str = "\
pub fn add(a: i32, b: i32) -> i32 {
    return a + b;
}

#[test]
fn adds() {
    if add(2, 2) != 4 {
        panic(\"add(2, 2) != 4\");
    }
}
";

/// `rok new [--lib|--bin] <name>`: a new directory with `main.rok` (or
/// `lib.rok`) and `rok.rokon`. `init [--lib|--bin] [dir]`: the directory
/// may exist, but not its root file.
fn cmd_new(g: &Global, cmd: &str, args: &[String]) -> Result<i32, String> {
    let mut lib = false;
    let mut pos = Vec::new();
    for a in args {
        match a.as_str() {
            "--lib" => lib = true,
            "--bin" => lib = false,
            f if f.starts_with('-') => return Err(format!("unknown option `{f}`")),
            p => pos.push(p),
        }
    }
    let init = cmd == "init";
    let dir = match (init, pos.as_slice()) {
        (false, [name]) => PathBuf::from(name),
        (true, []) => PathBuf::from("."),
        (true, [d]) => PathBuf::from(d),
        _ => return Err(format!("usage: rok {cmd} [--lib | --bin] <name>")),
    };
    if init {
        for f in ["main.rok", "lib.rok"] {
            if dir.join(f).exists() {
                return Err(format!("`{}` already exists", dir.join(f).display()));
            }
        }
    } else if dir.exists() {
        return Err(format!("`{}` already exists", dir.display()));
    }
    // The package name (rok.rokon's `name`) is the directory's (spec
    // 9.10.3: `[a-z][a-z0-9_-]*`; code says `my_app` for `my-app`).
    let abs = std::path::absolute(&dir).map_err(|e| e.to_string())?;
    let dir_name = abs.file_name().and_then(|n| n.to_str()).unwrap_or("app");
    let name = if init {
        let mut n: String = dir_name
            .to_ascii_lowercase()
            .chars()
            .map(|c| {
                if c.is_ascii_alphanumeric() || c == '_' {
                    c
                } else {
                    '-'
                }
            })
            .collect();
        if !n.starts_with(|c: char| c.is_ascii_lowercase()) {
            n.insert_str(0, "pkg-");
        }
        if n != dir_name && !g.quiet {
            eprintln!("note: the package name is `{n}` (`{dir_name}` is not a package name)");
        }
        n
    } else {
        manifest::check_name(dir_name)?;
        dir_name.to_owned()
    };
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let (file, text) = if lib {
        ("lib.rok", LIB_TEMPLATE)
    } else {
        ("main.rok", MAIN_TEMPLATE)
    };
    let root = dir.join(file);
    std::fs::write(&root, text).map_err(|e| format!("{}: {e}", root.display()))?;
    if manifest::find(&dir).is_none() {
        let value = Value::record(
            Some("Package"),
            vec![
                ("name", Value::str(&name)),
                ("version", Value::str("0.1.0")),
                ("deps", Value::new(Kind::Dict(Vec::new()))),
            ],
        );
        let path = dir.join(MANIFEST);
        std::fs::write(&path, rokc_rokon::to_string(&value) + "\n")
            .map_err(|e| format!("{}: {e}", path.display()))?;
    }
    let ignore = dir.join(".gitignore");
    if !ignore.exists() {
        std::fs::write(&ignore, "target/\n").map_err(|e| format!("{}: {e}", ignore.display()))?;
    }
    // A git repository of its own, unless it is inside one (or git is
    // not installed).
    let in_repo = Command::new("git")
        .args(["rev-parse", "--is-inside-work-tree"])
        .current_dir(&dir)
        .output();
    if in_repo.is_ok_and(|o| !o.status.success()) {
        let _ = Command::new("git")
            .args(["init", "-q"])
            .current_dir(&dir)
            .status();
    }
    if !g.quiet {
        let what = if lib { "library" } else { "executable" };
        eprintln!("     Created {what} package ({})", dir.display());
    }
    Ok(0)
}

/// `rok jupyter install`: the kernelspec `kernels/<name>/kernel.json` in
/// the Jupyter data directory (`$JUPYTER_DATA_DIR`, else the platform's
/// per-user one), starting the kernel through this `rok`.
fn install_kernel(g: &Global, args: &[String]) -> Result<i32, String> {
    if let Some(a) = args.first() {
        return Err(format!("`rok jupyter install` takes no `{a}`"));
    }
    // The proxy, when installed: the kernel follows the default toolchain.
    let proxy = home()
        .join("bin")
        .join(format!("rok{}", std::env::consts::EXE_SUFFIX));
    let exe = if proxy.is_file() {
        proxy
    } else {
        std::env::current_exe().map_err(|e| e.to_string())?
    };
    let mut argv = vec![exe.display().to_string()];
    if let Some(e) = &g.env {
        argv.extend(["--env".to_owned(), e.clone()]);
    }
    argv.extend(["jupyter", "--connection-file", "{connection_file}"].map(str::to_owned));
    let (name, display) = match &g.env {
        Some(e) => (format!("rok-{e}"), format!("rok ({e})")),
        None => ("rok".to_owned(), "rok".to_owned()),
    };
    let user_home = rokc_core::user_home;
    let data = std::env::var_os("JUPYTER_DATA_DIR")
        .filter(|d| !d.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            if cfg!(target_vendor = "apple") {
                Some(user_home()?.join("Library/Jupyter"))
            } else if cfg!(windows) {
                std::env::var_os("APPDATA")
                    .filter(|d| !d.is_empty())
                    .map(|d| PathBuf::from(d).join("jupyter"))
            } else {
                std::env::var_os("XDG_DATA_HOME")
                    .filter(|d| !d.is_empty())
                    .map(|d| PathBuf::from(d).join("jupyter"))
                    .or_else(|| Some(user_home()?.join(".local/share/jupyter")))
            }
        })
        .ok_or("cannot find the Jupyter data directory (set JUPYTER_DATA_DIR)")?;
    let dir = data.join("kernels").join(&name);
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let mut spec = vec![
        (
            "argv".to_owned(),
            Json::Arr(argv.into_iter().map(Json::Str).collect()),
        ),
        ("display_name".to_owned(), Json::Str(display)),
        ("language".to_owned(), Json::str("rok")),
        ("interrupt_mode".to_owned(), Json::str("message")),
    ];
    // Jupyter started from a GUI (the Dock, VS Code) gets a bare PATH:
    // the kernel keeps this shell's, where the LLVM tools are.
    let mut env = vec![(
        "ROK_HOME".to_owned(),
        Json::Str(home().display().to_string()),
    )];
    if let Ok(path) = std::env::var("PATH") {
        env.push(("PATH".to_owned(), Json::Str(path)));
    }
    spec.push(("env".to_owned(), Json::Obj(env)));
    let file = dir.join("kernel.json");
    std::fs::write(&file, format!("{}\n", Json::Obj(spec)))
        .map_err(|e| format!("{}: {e}", file.display()))?;
    if !g.quiet {
        eprintln!("   Installed kernel `{name}` ({})", file.display());
    }
    Ok(0)
}

/// `rok add` arguments (see `USAGE`), and `--dev`.
///
/// A stone without `@req` has an empty `req` (the caller picks one).
pub fn parse_dep_args(args: &[String]) -> Result<(Dep, bool), String> {
    let mut name = None;
    let (mut path, mut git, mut reference, mut dev) = (None, None, GitRef::Default, false);
    let mut registry = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let (flag, inline) = match a.split_once('=') {
            Some((f, v)) if f.starts_with("--") => (f, Some(v.to_owned())),
            _ => (a.as_str(), None),
        };
        let mut value = || {
            inline
                .clone()
                .or_else(|| it.next().cloned())
                .ok_or_else(|| format!("`{flag}` needs a value"))
        };
        match flag {
            "--path" => path = Some(value()?),
            "--git" => git = Some(value()?),
            "--rev" | "--tag" | "--branch" if reference != GitRef::Default => {
                return Err("give at most one of --rev, --tag, --branch".into());
            }
            "--rev" => reference = GitRef::Rev(value()?),
            "--tag" => reference = GitRef::Tag(value()?),
            "--branch" => reference = GitRef::Branch(value()?),
            "--dev" => dev = true,
            "--registry" => registry = Some(value()?),
            f if f.starts_with('-') => return Err(format!("unknown option `{f}`")),
            n if name.is_none() => name = Some(n.to_owned()),
            n => return Err(format!("unexpected argument `{n}`")),
        }
    }
    let usage = "usage: rok add <name>[@<req>] [--registry <url>] | <name> --path <dir> | \
                 <name> --git <url> [--rev|--tag|--branch <r>]  [--dev]";
    let name = name.ok_or(usage)?;
    let (name, req) = match name.split_once('@') {
        Some((n, r)) => (n.to_owned(), Some(r.to_owned())),
        None => (name, None),
    };
    manifest::check_name(&name)?;
    let source = match (path, git) {
        (None, None) if reference == GitRef::Default => {
            let req = req.unwrap_or_default();
            if !req.is_empty() {
                semver::Req::parse(&req)?;
            }
            Source::Registry { req, registry }
        }
        _ if req.is_some() || registry.is_some() => {
            return Err("`@<req>` / --registry go with a stone, not --path / --git".into());
        }
        (Some(p), None) if reference == GitRef::Default => Source::Path(p),
        (None, Some(url)) => Source::Git { url, reference },
        (_, None) => return Err("--rev / --tag / --branch go with --git".into()),
        _ => return Err(usage.into()),
    };
    Ok((Dep { name, source }, dev))
}

/// The manifest `rok add` / `remove` edit: the environment's, or the
/// current package's (made when missing).
fn manifest_to_edit(g: &Global) -> Result<(PathBuf, bool), String> {
    if let Some(name) = &g.env {
        let dir = env_dir(name);
        if !dir.is_dir() {
            if name != "default" {
                return Err(format!(
                    "no environment `{name}` (create it: rok env create {name})"
                ));
            }
            env::create(name)?;
        }
        return Ok((dir.join(MANIFEST), true));
    }
    let dir = package_dir(Path::new(".")).ok_or(
        "not inside a package (no main.rok, lib.rok or rok.rokon here or above); run `rok init`, \
         or pass `--env <name>`",
    )?;
    Ok((
        manifest::find(&dir).unwrap_or_else(|| dir.join(MANIFEST)),
        false,
    ))
}

/// `a` relative to directory `from` (both absolute), with `..` steps.
fn relative(from: &Path, a: &Path) -> PathBuf {
    let f: Vec<_> = from.components().collect();
    let t: Vec<_> = a.components().collect();
    let common = f.iter().zip(&t).take_while(|(x, y)| x == y).count();
    let mut out = PathBuf::new();
    for _ in common..f.len() {
        out.push("..");
    }
    for c in &t[common..] {
        out.push(c);
    }
    if out.as_os_str().is_empty() {
        out.push(".");
    }
    out
}

/// Write `text` to `path`, resolve, and put the old text back when
/// resolution fails.
fn write_and_resolve(g: &Global, path: &Path, old: Option<&str>, text: &str) -> Result<(), String> {
    let text = canonical_edit(old.unwrap_or(manifest::EMPTY), text);
    std::fs::write(path, text).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
    let dir = path.parent().unwrap_or_else(|| Path::new("."));
    let r = load_dir(dir).and_then(|ctx| resolve::resolve(&home(), &ctx, &options(g)));
    if let Err(e) = r {
        match old {
            Some(o) => std::fs::write(path, o),
            None => std::fs::remove_file(path),
        }
        .map_err(|e2| format!("{e}\n(and cannot restore {}: {e2})", path.display()))?;
        return Err(e);
    }
    Ok(())
}

/// `rok add --native <name>[@<req>] [--registry <url>]`.
fn cmd_add_native(g: &Global, args: &[String]) -> Result<i32, String> {
    let (vals, _, pos) = flags(args, &["--registry"], &["--native"])?;
    let [spec] = pos.as_slice() else {
        return Err("usage: rok add --native <name>[@<req>] [--registry <url>]".into());
    };
    let (name, req) = spec.split_once('@').unwrap_or((spec, ""));
    manifest::check_name(name)?;
    let registry = val(&vals, "--registry").map(str::to_owned);
    let req = if req.is_empty() {
        let url = match &registry {
            Some(r) => r.clone(),
            None => registry::default_url(&home())?,
        };
        let index = registry::open(&home(), &url, g.offline, g.quiet)?;
        let all = native::entries(&index, &url, name)?;
        let e = native::best(&all, &semver::Req::parse("*")?)
            .ok_or_else(|| native::no_match(&all, name, "*", &url))?;
        format!("^{}", e.vers)
    } else {
        semver::Req::parse(req)?;
        req.to_owned()
    };
    let (path, _) = manifest_to_edit(g)?;
    let old = std::fs::read_to_string(&path).ok();
    let source = NativeSource::Registry { req, registry };
    let text = manifest::set_dep(
        old.as_deref().unwrap_or(manifest::EMPTY),
        &path.display().to_string(),
        "native",
        name,
        &rokc_rokon::to_line(&source.to_value()),
    )?;
    write_and_resolve(g, &path, old.as_deref(), &text)?;
    if !g.quiet {
        eprintln!("       Added {name} to native of {}", path.display());
    }
    Ok(0)
}

fn cmd_add(g: &Global, args: &[String]) -> Result<i32, String> {
    if args.iter().any(|a| a == "--native") {
        return cmd_add_native(g, args);
    }
    let (mut dep, dev) = parse_dep_args(args)?;
    let (path, is_env) = manifest_to_edit(g)?;
    // Path dependencies: relative to the manifest in a project (it moves
    // with the project), absolute in an environment.
    if let Source::Path(p) = &dep.source {
        let abs = rokc_core::real_path(p).map_err(|e| format!("--path {p}: {e}"))?;
        let dir = rokc_core::real_path(path.parent().unwrap_or_else(|| Path::new(".")))
            .map_err(|e| e.to_string())?;
        let shown = if is_env { abs } else { relative(&dir, &abs) };
        dep.source = Source::Path(shown.display().to_string().replace('\\', "/"));
    }
    // A stone without a requirement: `^` its newest version.
    if let Source::Registry { req, registry } = &mut dep.source {
        if req.is_empty() {
            let url = match registry {
                Some(r) => r.clone(),
                None => registry::default_url(&home())?,
            };
            let index = registry::open(&home(), &url, g.offline, g.quiet)?;
            let all = registry::entries(&index, &url, &dep.name)?;
            let star = semver::Req::parse("*")?;
            let e = registry::best(&all, &star)
                .ok_or_else(|| registry::no_match(&all, &dep.name, "*", &url))?;
            *req = format!("^{}", e.vers);
        }
    }
    let old = std::fs::read_to_string(&path).ok();
    let section = if dev { "dev_deps" } else { "deps" };
    let text = manifest::set_dep(
        old.as_deref().unwrap_or(manifest::EMPTY),
        &path.display().to_string(),
        section,
        &dep.name,
        &dep.source.to_rok(),
    )?;
    write_and_resolve(g, &path, old.as_deref(), &text)?;
    if !g.quiet {
        eprintln!(
            "       Added {} to {section} of {}",
            dep.name,
            path.display()
        );
    }
    Ok(0)
}

fn cmd_remove(g: &Global, args: &[String]) -> Result<i32, String> {
    let (sections, name) = match args {
        [name] => (&["deps", "dev_deps"][..], name),
        [f, name] if f == "--native" => (&["native"][..], name),
        _ => return Err("usage: rok remove [--native] <name>".into()),
    };
    let (path, _) = manifest_to_edit(g)?;
    let old = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let file = path.display().to_string();
    let mut text: Option<String> = None;
    for section in sections {
        let now = text.as_deref().unwrap_or(&old);
        if let Some(t) = manifest::remove_dep(now, &file, section, name)? {
            text = Some(t);
        }
    }
    let Some(text) = text else {
        return Err(format!("`{name}` is not a dependency in {file}"));
    };
    write_and_resolve(g, &path, Some(&old), &text)?;
    if !g.quiet {
        eprintln!("     Removed {name} from {}", path.display());
    }
    Ok(0)
}

fn cmd_update(g: &Global, names: &[String]) -> Result<i32, String> {
    let t = target_for(g, None)?;
    let manifest = &t.ctx.manifest;
    for n in names {
        if !manifest
            .deps
            .iter()
            .chain(&manifest.dev_deps)
            .any(|d| manifest::same(&d.name, n))
            && !manifest.native.iter().any(|d| manifest::same(&d.name, n))
        {
            let lock = t
                .ctx
                .lock_path
                .as_deref()
                .and_then(|p| lock::Lock::read(p).ok().flatten());
            if lock
                .as_ref()
                .is_none_or(|l| l.find(n).is_none() && l.find_native(n).is_none())
            {
                return Err(format!("`{n}` is not a dependency"));
            }
        }
    }
    let mut opts = options(g);
    opts.update = Some(names.to_vec());
    let r = resolve::resolve(&home(), &t.ctx, &opts)?;
    if !g.quiet {
        if let Some(p) = &t.ctx.lock_path {
            let count = r.packages.len() + r.natives.len();
            let s = if count == 1 { "" } else { "s" };
            eprintln!("     Updated {} ({count} package{s})", p.display());
        }
    }
    Ok(0)
}

/// `rok deps [path] [--dev]`: `name=<lib.rok>` per dependency, each after
/// its own; then per native package (for the host, dependents first) a
/// `# native <name> <vers>` line and its rokc arguments, one per line
/// (the REPL's `:add` reads it all).
fn cmd_deps(g: &Global, args: &[String]) -> Result<i32, String> {
    let path = args
        .iter()
        .find(|a| !a.starts_with('-'))
        .map(String::as_str);
    let t = target_for(g, path)?;
    let dev = args.iter().any(|a| a == "--dev");
    let graph = resolve::resolve(&home(), &t.ctx, &options(g))?;
    let deps: &[Resolved] = &graph.packages;
    for p in deps.iter().filter(|p| dev || !p.dev) {
        println!("{}={}", manifest::code_name(&p.name), p.root.display());
    }
    for n in graph.natives.iter().filter(|n| dev || !n.dev) {
        println!("# native {} {}", n.entry.name, n.entry.vers);
        for a in native::rokc_args(
            &home(),
            &[n],
            rokc_target::TargetSpec::host(),
            g.offline,
            g.quiet,
        )? {
            println!("{a}");
        }
    }
    Ok(0)
}

/// `rok search [--native] <query>`: `name newest — description` for each
/// stone (or native package) of the index whose name contains the query
/// (any case).
fn cmd_search(g: &Global, args: &[String]) -> Result<i32, String> {
    let (q, native) = match args {
        [q] if !q.starts_with('-') => (q, false),
        [f, q] if f == "--native" => (q, true),
        _ => return Err("usage: rok search [--native] <query>".into()),
    };
    let url = registry::default_url(&home())?;
    let index = registry::open(&home(), &url, g.offline, g.quiet)?;
    // `-` and `_` are one (9.10.3); file names are lowercase.
    let q = q.to_ascii_lowercase().replace('_', "-");
    let mut names: Vec<String> = index
        .files(&url)?
        .into_iter()
        .filter(|f| f.contains('/') && f.starts_with("native/") == native)
        .filter_map(|f| f.rsplit('/').next().map(str::to_owned))
        .filter(|n| n.replace('_', "-").contains(&q))
        .collect();
    names.sort();
    let star = semver::Req::parse("*")?;
    for n in names {
        let newest = if native {
            native::best(&native::entries(&index, &url, &n)?, &star)
                .map(|e| (e.name.clone(), e.vers.clone(), e.meta.clone()))
        } else {
            registry::best(&registry::entries(&index, &url, &n)?, &star)
                .map(|e| (e.name.clone(), e.vers.clone(), e.meta.clone()))
        };
        if let Some((name, vers, meta)) = newest {
            match meta.iter().find(|(k, _)| *k == "description") {
                Some((_, d)) => println!("{name} {vers} — {d}"),
                None => println!("{name} {vers}"),
            }
        }
    }
    Ok(0)
}

/// The current package's directory and manifest.
fn this_package() -> Result<(PathBuf, Manifest), String> {
    let dir = package_dir(Path::new("."))
        .filter(|d| manifest::find(d).is_some())
        .ok_or("not inside a package with a rok.rokon")?;
    let m = manifest::load(&dir.join(MANIFEST))?;
    Ok((dir, m))
}

/// Options with a value (`--f v` / `--f=v`), switches given, positionals.
type Flags = (Vec<(String, String)>, Vec<String>, Vec<String>);

/// `args` split by `valued` options and `switches`; others are errors.
fn flags(args: &[String], valued: &[&str], switches: &[&str]) -> Result<Flags, String> {
    let (mut vals, mut sw, mut pos) = (Vec::new(), Vec::new(), Vec::new());
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let (f, inline) = match a.split_once('=') {
            Some((f, v)) if f.starts_with("--") => (f, Some(v.to_owned())),
            _ => (a.as_str(), None),
        };
        if valued.contains(&f) {
            let v = inline
                .or_else(|| it.next().cloned())
                .ok_or_else(|| format!("`{f}` needs a value"))?;
            vals.push((f.to_owned(), v));
        } else if switches.contains(&f) {
            sw.push(f.to_owned());
        } else if f.starts_with('-') {
            return Err(format!("unknown option `{f}`"));
        } else {
            pos.push(a.clone());
        }
    }
    Ok((vals, sw, pos))
}

fn val<'a>(vals: &'a [(String, String)], f: &str) -> Option<&'a str> {
    vals.iter()
        .rev()
        .find(|(k, _)| k == f)
        .map(|(_, v)| v.as_str())
}

/// The registry API of the configured index, and the token for it.
fn api_token(g: &Global) -> Result<(String, String), String> {
    let home = home();
    let token = registry::token(&home)?;
    let api = registry::api(&home, &registry::default_url(&home)?, g.quiet)?;
    Ok((api, token))
}

/// `rok publish [--native <file>] [--index <dir>] [--commit]`: print the
/// index line; with `--index`, check it against that checkout. With
/// `--commit`, commit it there, or without `--index`, publish it through
/// the registry API.
fn cmd_publish(g: &Global, args: &[String]) -> Result<i32, String> {
    let (vals, sw, pos) = flags(args, &["--index", "--native"], &["--commit"])?;
    if let Some(p) = pos.first() {
        return Err(format!("unexpected argument `{p}`"));
    }
    let write = sw.iter().any(|s| s == "--commit");
    let index = val(&vals, "--index").map(Path::new);
    let remote = match index {
        None if write => Some(api_token(g)?),
        _ => None,
    };
    let (line, mut name, mut vers, rel, what) = if let Some(file) = val(&vals, "--native") {
        let e = native::publish(&home(), Path::new(file), index, write)?.0;
        let rel = native::path(&e.name);
        (e.to_line(), e.name, e.vers.to_string(), rel, "native ")
    } else {
        let (dir, m) = this_package()?;
        let e = registry::entry_for(&dir, &m)?;
        if let Some(i) = index {
            registry::publish(i, &e, write)?;
        }
        let rel = registry::path(&e.name);
        (e.to_line(), e.name, e.vers.to_string(), rel, "")
    };
    let to = match (index, remote) {
        (Some(i), _) => i.display().to_string(),
        (None, Some((api, token))) => {
            (name, vers) = registry::publish_api(&api, &token, &line)?;
            api
        }
        (None, None) => registry::default_url(&home())?,
    };
    println!("{line}");
    if !g.quiet {
        if write {
            eprintln!("   Published {what}{name} {vers} to {to}");
        } else {
            eprintln!("note: dry run; --commit adds it to {to} as {rel}");
        }
    }
    Ok(0)
}

/// `rok yank [--native] --vers <v> [--undo] [--index <dir>] [name]`
/// (default: this package's name; a native package is named): committed
/// to the checkout `--index`, else through the registry API.
fn cmd_yank(g: &Global, args: &[String]) -> Result<i32, String> {
    let (vals, sw, pos) = flags(args, &["--vers", "--index"], &["--undo", "--native"])?;
    let usage = "usage: rok yank [--native] --vers <version> [--undo] [--index <dir>] [name]";
    let Some(vers) = val(&vals, "--vers") else {
        return Err(usage.into());
    };
    let native = sw.iter().any(|s| s == "--native");
    let name = match pos.as_slice() {
        [n] => n.clone(),
        [] if !native => this_package()?.1.name.ok_or("rok.rokon has no `name`")?,
        _ => return Err(usage.into()),
    };
    let undo = sw.iter().any(|s| s == "--undo");
    let to = if let Some(i) = val(&vals, "--index") {
        registry::yank(Path::new(i), &name, vers, !undo, native)?;
        i.to_owned()
    } else {
        let (api, token) = api_token(g)?;
        registry::yank_api(&api, &token, &name, vers, undo, native)?;
        api
    };
    if !g.quiet {
        let verb = if undo { "Unyanked" } else { "Yanked" };
        eprintln!("   {verb} {name} {vers} in {to}");
    }
    Ok(0)
}

/// `rok login [<token>]`: keep a registry token whose account may
/// publish.
fn cmd_login(g: &Global, args: &[String]) -> Result<i32, String> {
    let (_, _, pos) = flags(args, &[], &[])?;
    if pos.len() > 1 {
        return Err("usage: rok login [<token>]".into());
    }
    let home = home();
    let api = registry::api(&home, &registry::default_url(&home)?, g.quiet)?;
    let token = match pos.first() {
        Some(t) => t.clone(),
        None => read_secret(&format!(
            "a token from {api}/me (not shown; Ctrl-C to cancel): "
        ))?,
    };
    registry::check_token(&token)?;
    let (login, publish) = registry::me(&api, &token)?;
    if !publish {
        return Err(
            "this account cannot publish yet: publishing is open to rokstones.io maintainers only"
                .into(),
        );
    }
    let file = registry::save_token(&home, &token)?;
    if !g.quiet {
        eprintln!(
            "   Logged in as {login} at {api} (token in {})",
            file.display()
        );
    }
    Ok(0)
}

/// `rok logout`: remove `rok login`'s token.
fn cmd_logout(g: &Global, args: &[String]) -> Result<i32, String> {
    if let Some(a) = args.first() {
        return Err(format!("unexpected argument `{a}`"));
    }
    let had = registry::logout(&home())?;
    if !g.quiet {
        eprintln!(
            "{}",
            if had {
                "   Logged out"
            } else {
                "note: not logged in"
            }
        );
    }
    Ok(0)
}

/// A line of stdin, trimmed; not echoed when stdin is a terminal (echo
/// comes back on Ctrl-C too).
fn read_secret(prompt: &str) -> Result<String, String> {
    use std::io::IsTerminal;
    let tty = std::io::stdin().is_terminal();
    let hidden = tty && {
        eprint!("{prompt}");
        echo::off()
    };
    let mut line = String::new();
    let r = std::io::stdin().read_line(&mut line);
    if hidden {
        echo::on();
    }
    if tty {
        eprintln!();
    }
    r.map_err(|e| format!("cannot read stdin: {e}"))?;
    Ok(line.trim().to_owned())
}

/// The terminal's echo of stdin, saved and turned off, then restored on
/// `on` or on Ctrl-C (which then ends the process as it would have).
#[cfg(unix)]
mod echo {
    use std::sync::atomic::{AtomicUsize, Ordering};

    // `struct termios` starts with `c_iflag`, `c_oflag`, `c_cflag`,
    // `c_lflag` (`tcflag_t`); the rest is copied as is.
    #[cfg(target_vendor = "apple")]
    type Flag = u64;
    #[cfg(not(target_vendor = "apple"))]
    type Flag = u32;
    const LFLAG: usize = 3 * size_of::<Flag>();
    const ECHO: Flag = 8;
    const SIGINT: i32 = 2;
    const TCSANOW: i32 = 0;

    /// The saved `termios`, larger than any.
    static mut SAVED: [u64; 32] = [0; 32];
    static HANDLER: AtomicUsize = AtomicUsize::new(0);

    unsafe extern "C" {
        fn tcgetattr(fd: i32, t: *mut u8) -> i32;
        fn tcsetattr(fd: i32, when: i32, t: *const u8) -> i32;
        fn signal(sig: i32, handler: usize) -> usize;
        fn raise(sig: i32) -> i32;
    }

    // Async-signal-safe calls only.
    extern "C" fn interrupted(_: i32) {
        // SAFETY: `SAVED` is written before this handler is installed.
        unsafe {
            tcsetattr(0, TCSANOW, (&raw const SAVED).cast());
            signal(SIGINT, 0);
            raise(SIGINT);
        }
    }

    pub fn off() -> bool {
        // SAFETY: `SAVED` is only touched here, before the handler is
        // installed, and by `on` / the handler afterwards.
        unsafe {
            if tcgetattr(0, (&raw mut SAVED).cast()) != 0 {
                return false;
            }
            let mut t = SAVED;
            let lflag = (&raw mut t).cast::<u8>().add(LFLAG).cast::<Flag>();
            lflag.write_unaligned(lflag.read_unaligned() & !ECHO);
            let h = interrupted as extern "C" fn(i32) as usize;
            HANDLER.store(signal(SIGINT, h), Ordering::Relaxed);
            tcsetattr(0, TCSANOW, (&raw const t).cast());
        }
        true
    }

    pub fn on() {
        // SAFETY: as in `off`.
        unsafe {
            tcsetattr(0, TCSANOW, (&raw const SAVED).cast());
            signal(SIGINT, HANDLER.load(Ordering::Relaxed));
        }
    }
}

#[cfg(windows)]
mod echo {
    use std::sync::atomic::{AtomicU32, Ordering};

    unsafe extern "system" {
        fn GetStdHandle(which: u32) -> isize;
        fn GetConsoleMode(h: isize, mode: *mut u32) -> i32;
        fn SetConsoleMode(h: isize, mode: u32) -> i32;
        fn SetConsoleCtrlHandler(handler: Option<extern "system" fn(u32) -> i32>, add: i32) -> i32;
    }
    const STD_INPUT_HANDLE: u32 = 0xFFFF_FFF6;
    const ENABLE_ECHO_INPUT: u32 = 4;
    static SAVED: AtomicU32 = AtomicU32::new(0);

    fn restore() {
        // SAFETY: the console input handle.
        unsafe {
            SetConsoleMode(
                GetStdHandle(STD_INPUT_HANDLE),
                SAVED.load(Ordering::Relaxed),
            )
        };
    }

    /// Restore, then let the next handler (the default one) end the
    /// process.
    extern "system" fn interrupted(_: u32) -> i32 {
        restore();
        0
    }

    pub fn off() -> bool {
        // SAFETY: the console input handle and a local out-parameter.
        unsafe {
            let h = GetStdHandle(STD_INPUT_HANDLE);
            let mut m = 0;
            if GetConsoleMode(h, &mut m) == 0 {
                return false;
            }
            SAVED.store(m, Ordering::Relaxed);
            SetConsoleCtrlHandler(Some(interrupted), 1);
            SetConsoleMode(h, m & !ENABLE_ECHO_INPUT);
        }
        true
    }

    pub fn on() {
        restore();
        // SAFETY: removes the handler `off` added.
        unsafe { SetConsoleCtrlHandler(Some(interrupted), 0) };
    }
}

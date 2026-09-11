//! `rok`: the toolchain front (spec 901). It owns `rok.rokon` /
//! `rok.lock`, dependency resolution and the git cache, environments,
//! toolchains, package scaffolding and the Jupyter kernelspec, and runs
//! the compiler `rokc` (next to itself, or a pinned toolchain's) with the
//! resolved dependencies as `--extern name=lib.rok`; rokc prebuilds them.
//!
//! ```text
//! $ROK_HOME/bin/{rok,rokc,rokls}     the toolchain
//! $ROK_HOME/lib/...                  runtime and standard library (rokc)
//! $ROK_HOME/cache/git/               shared git cache (see `git`)
//! $ROK_HOME/cache/scripts/<hash>/    a script's lock and prebuilt dependencies
//! $ROK_HOME/envs/<name>/             a named environment (rok.rokon, rok.lock, target/)
//! $ROK_HOME/envs/CURRENT             `rok env use`'s choice
//! $ROK_HOME/toolchains/<version>/    installed toolchains (`bin/rokc`, `lib/`)
//! ```

mod env;
mod git;
mod lock;
mod manifest;
mod resolve;
mod toolchain;

use std::path::{Path, PathBuf};
use std::process::Command;

use manifest::{Dep, GitRef, MANIFEST, Manifest, Source};
use resolve::{Context, Options, Resolved};
use rokc_diagnostic::Json;
use rokc_rokon::{Kind, Value};

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

const USAGE: &str = "\
usage: rok [options] <command> [args]
       rok [options]                same as `rok repl`

packages:
  new [--lib|--bin] <name>     create a package (with rok.rokon)
  init [--lib|--bin] [dir]     make a directory a package
  add <name> --path <dir>      add a dependency (--dev: to dev_deps)
  add <name> --git <url> [--rev <r> | --tag <t> | --branch <b>]
  remove <name>                remove a dependency
  update [name...]             re-resolve git dependencies, rewrite rok.lock
  deps                         print the resolved dependencies (name=lib.rok),
                               each after its own
  clean [path]                 remove target/

compiler commands (rokc, with the dependencies; see `rokc help`):
  build | check | run | test | bench | lint | doc | emit [path] ...
  repl [--replay] [--package <path>]
                               interactive session (`:add <dep>` adds to the
                               active environment)
  lsp                          language server (also `rokls`)
  jupyter --connection-file <f>  the kernel (Jupyter starts it)
  fmt [path]                   format .rok and .rokon files

  The path, if any, comes first after the command; it picks the project
  (or script) whose dependencies and `lints` apply.

jupyter:
  jupyter install              install the `rok` Jupyter kernel (with --env:
                               `rok-<env>`, running in that environment)

environments:
  env create|remove|use <name>      a named environment
  env list                          (`*`: the active one)
  env export <name> <dir>           write its rok.rokon / rok.lock to <dir>
  env import <name> <dir|rok.rokon> create it from a project or export
  env shell [name]                  a $SHELL with ROK_ENV=<name>

toolchains:
  toolchain list
  toolchain install <version> --from <dir | .tar[.gz]>
  toolchain remove <version>

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

environment: ROK_HOME (default: the parent of rok's bin/), ROK_ENV
";

#[derive(Default)]
struct Global {
    env: Option<String>,
    offline: bool,
    locked: bool,
    quiet: bool,
}

/// The install root (`rokc_core::rok_home`).
pub fn home() -> PathBuf {
    rokc_core::rok_home().unwrap_or_else(|| PathBuf::from("."))
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
            _ => rest.push(a),
        }
    }
    // The command: the first word that is not an option. rokc options
    // with a separate value go after it.
    let Some(i) = rest.iter().position(|a| !a.starts_with('-') || a == "--") else {
        if rest.iter().any(|a| a == "-V" || a == "--version") {
            println!("rok {VERSION}");
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
    run(&g, &rest[i], &rest[..i], &rest[i + 1..])
}

fn run(g: &Global, cmd: &str, pre: &[String], post: &[String]) -> i32 {
    let r = match cmd {
        "version" => {
            println!("rok {VERSION}");
            Ok(0)
        }
        "help" => {
            print!("{USAGE}");
            Ok(0)
        }
        "new" | "init" => cmd_new(g, cmd, post),
        "add" => cmd_add(g, post),
        "remove" => cmd_remove(g, post),
        "update" => cmd_update(g, post),
        "deps" => cmd_deps(g, post),
        "env" => env::cmd(g, post),
        "toolchain" => toolchain::cmd(post),
        "jupyter" if post.first().is_some_and(|p| p == "install") => install_kernel(g, &post[1..]),
        "build" | "check" | "run" | "test" | "repl" | "lsp" | "fmt" | "clean" | "demangle"
        | "emit" | "bench" | "doc" | "lint" | "jupyter" => delegate(g, cmd, pre, post),
        other => return usage(&format!("unknown command `{other}`")),
    };
    r.unwrap_or_else(|e| {
        // A rendered diagnostic (`file:line:col: error: ..`) as it is.
        if e.lines().next().is_some_and(|l| l.contains(": error: ")) {
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
        Some(p) => manifest::load(&p)?,
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
                || manifest.toolchain.is_some()
                || manifest.name.is_some()
                || manifest.version.is_some()
            {
                return Err(format!("{file}: a script block holds only `deps`"));
            }
            let abs = std::fs::canonicalize(start).map_err(|e| e.to_string())?;
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
    let t = target_for(g, path)?;
    let mut extra: Vec<String> = Vec::new();
    if !matches!(cmd, "fmt" | "clean" | "demangle") {
        let deps = match resolve::resolve(&home(), &t.ctx, &options(g)) {
            Ok(r) => r,
            // The language server still starts (without dependencies).
            Err(e) if cmd == "lsp" => {
                eprintln!("rok: warning: {e}");
                Vec::new()
            }
            Err(e) => return Err(e),
        };
        let dev_too = matches!(cmd, "test" | "bench");
        for p in deps.iter().filter(|p| dev_too || !p.dev) {
            extra.push("--extern".to_owned());
            extra.push(format!("{}={}", p.name, p.root.display()));
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
    let (rokc, toolchain_home) = toolchain::rokc_for(t.ctx.manifest.toolchain.as_deref())?;
    let mut c = Command::new(&rokc);
    c.args(pre).arg(cmd).args(&extra).args(post);
    if let Ok(me) = std::env::current_exe() {
        c.env("ROK", me);
    }
    if let Some(e) = &t.env {
        c.env("ROK_ENV", e);
    }
    if let Some(h) = toolchain_home {
        c.env("ROK_HOME", h);
    }
    Ok(exec(c, &rokc))
}

/// Replace this process with `c` (unix), else wait for it.
fn exec(mut c: Command, what: &Path) -> i32 {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        let e = c.exec();
        eprintln!("rok: error: cannot run {}: {e}", what.display());
        1
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
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let (file, text) = if lib {
        ("lib.rok", LIB_TEMPLATE)
    } else {
        ("main.rok", MAIN_TEMPLATE)
    };
    let root = dir.join(file);
    std::fs::write(&root, text).map_err(|e| format!("{}: {e}", root.display()))?;
    if manifest::find(&dir).is_none() {
        let abs = std::path::absolute(&dir).map_err(|e| e.to_string())?;
        let name = abs.file_name().and_then(|n| n.to_str()).unwrap_or("app");
        let value = Value::record(
            Some("Package"),
            vec![
                ("name", Value::str(name)),
                ("version", Value::str("0.1.0")),
                ("deps", Value::new(Kind::Dict(Vec::new()))),
            ],
        );
        let path = dir.join(MANIFEST);
        std::fs::write(&path, rokc_rokon::to_string(&value) + "\n")
            .map_err(|e| format!("{}: {e}", path.display()))?;
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
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let mut argv = vec![exe.display().to_string()];
    if let Some(e) = &g.env {
        argv.extend(["--env".to_owned(), e.clone()]);
    }
    argv.extend(["jupyter", "--connection-file", "{connection_file}"].map(str::to_owned));
    let (name, display) = match &g.env {
        Some(e) => (format!("rok-{e}"), format!("rok ({e})")),
        None => ("rok".to_owned(), "rok".to_owned()),
    };
    let user_home = || std::env::var_os("HOME").map(PathBuf::from);
    let data = std::env::var_os("JUPYTER_DATA_DIR")
        .filter(|d| !d.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            if cfg!(target_vendor = "apple") {
                Some(user_home()?.join("Library/Jupyter"))
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
    // A toolchain found through ROK_HOME needs it in the kernel too.
    if let Some(h) = std::env::var("ROK_HOME").ok().filter(|h| !h.is_empty()) {
        spec.push(("env".to_owned(), Json::obj([("ROK_HOME", Json::Str(h))])));
    }
    let file = dir.join("kernel.json");
    std::fs::write(&file, format!("{}\n", Json::Obj(spec)))
        .map_err(|e| format!("{}: {e}", file.display()))?;
    if !g.quiet {
        eprintln!("   Installed kernel `{name}` ({})", file.display());
    }
    Ok(0)
}

/// `rok add` arguments: `<name> --path <dir> | --git <url> [--rev ..|--tag ..|--branch ..]`,
/// plus `--dev`.
pub fn parse_dep_args(args: &[String]) -> Result<(Dep, bool), String> {
    let mut name = None;
    let (mut path, mut git, mut reference, mut dev) = (None, None, GitRef::Default, false);
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
            f if f.starts_with('-') => return Err(format!("unknown option `{f}`")),
            n if name.is_none() => name = Some(n.to_owned()),
            n => return Err(format!("unexpected argument `{n}`")),
        }
    }
    let usage =
        "usage: rok add <name> --path <dir> | --git <url> [--rev|--tag|--branch <r>] [--dev]";
    let name = name.ok_or(usage)?;
    manifest::check_name(&name)?;
    let source = match (path, git) {
        (Some(p), None) if reference == GitRef::Default => Source::Path(p),
        (None, Some(url)) => Source::Git { url, reference },
        (Some(_), None) => return Err("--rev / --tag / --branch go with --git".into()),
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

fn cmd_add(g: &Global, args: &[String]) -> Result<i32, String> {
    let (mut dep, dev) = parse_dep_args(args)?;
    let (path, is_env) = manifest_to_edit(g)?;
    // Path dependencies: relative to the manifest in a project (it moves
    // with the project), absolute in an environment.
    if let Source::Path(p) = &dep.source {
        let abs = std::fs::canonicalize(p).map_err(|e| format!("--path {p}: {e}"))?;
        let dir = std::fs::canonicalize(path.parent().unwrap_or_else(|| Path::new(".")))
            .map_err(|e| e.to_string())?;
        let shown = if is_env { abs } else { relative(&dir, &abs) };
        dep.source = Source::Path(shown.display().to_string().replace('\\', "/"));
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
    let [name] = args else {
        return Err("usage: rok remove <name>".into());
    };
    let (path, _) = manifest_to_edit(g)?;
    let old = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let file = path.display().to_string();
    let mut text: Option<String> = None;
    for section in ["deps", "dev_deps"] {
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
            .any(|d| d.name == *n)
        {
            let lock = t
                .ctx
                .lock_path
                .as_deref()
                .and_then(|p| lock::Lock::read(p).ok().flatten());
            if lock.as_ref().and_then(|l| l.find(n)).is_none() {
                return Err(format!("`{n}` is not a dependency"));
            }
        }
    }
    let mut opts = options(g);
    opts.update = Some(names.to_vec());
    let r = resolve::resolve(&home(), &t.ctx, &opts)?;
    if !g.quiet {
        if let Some(p) = &t.ctx.lock_path {
            eprintln!("     Updated {} ({} packages)", p.display(), r.len());
        }
    }
    Ok(0)
}

/// `rok deps [path] [--dev]`: `name=<lib.rok>` per dependency, each after
/// its own (the REPL's `:add` reads it).
fn cmd_deps(g: &Global, args: &[String]) -> Result<i32, String> {
    let path = args
        .iter()
        .find(|a| !a.starts_with('-'))
        .map(String::as_str);
    let t = target_for(g, path)?;
    let dev = args.iter().any(|a| a == "--dev");
    let deps: Vec<Resolved> = resolve::resolve(&home(), &t.ctx, &options(g))?;
    for p in deps.iter().filter(|p| dev || !p.dev) {
        println!("{}={}", p.name, p.root.display());
    }
    Ok(0)
}

//! `rok`: the toolchain front (spec 901). It owns `Rok.toml` /
//! `Rok.lock`, dependency resolution and the git cache, environments and
//! toolchains, and runs the compiler `rokc` (next to itself, or a pinned
//! toolchain's) with the resolved dependencies as `--extern name=root`.
//!
//! ```text
//! $ROK_HOME/bin/{rok,rokc,rokls}     the toolchain
//! $ROK_HOME/lib/...                  runtime and standard library (rokc)
//! $ROK_HOME/cache/git/               shared git cache (see `git`)
//! $ROK_HOME/cache/scripts/<hash>/    a script's lock
//! $ROK_HOME/envs/<name>/             a named environment (Rok.toml, Rok.lock)
//! $ROK_HOME/envs/CURRENT             `rok env use`'s choice
//! $ROK_HOME/toolchains/<version>/    installed toolchains (`bin/rokc`, `lib/`)
//! ```

mod env;
mod git;
mod lock;
mod manifest;
mod prebuilt;
mod resolve;
mod toolchain;

use std::path::{Path, PathBuf};
use std::process::Command;

use manifest::{Dep, GitRef, MANIFEST, Manifest, Source};
use resolve::{Context, Options, Resolved};

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

const USAGE: &str = "\
usage: rok [options] <command> [args]
       rok [options]                same as `rok repl`

packages:
  new [--lib|--bin] <name>     create a package (with Rok.toml)
  init [--lib|--bin] [dir]     make a directory a package
  add <name> --path <dir>      add a dependency (--dev: to [dev-deps])
  add <name> --git <url> [--rev <r> | --tag <t> | --branch <b>]
  remove <name>                remove a dependency
  update [name...]             re-resolve git dependencies, rewrite Rok.lock
  deps                         print the resolved dependencies (name=lib.rok)
  clean [path]                 remove target/

build (run by rokc, with the dependencies):
  build | check | run | test [path] ...   see `rokc help` for their options
  repl [--replay]              interactive session (`:add <dep>` adds to the
                               active environment; --replay reruns every
                               cell for each new one)
  lsp                          language server (also `rokls`)
  jupyter install [--user]     install the `rok` Jupyter kernel (with --env:
                               `rok-<env>`, running in that environment)
  jupyter --connection-file <f>  the kernel (Jupyter starts it)
  fmt [path]                   format .rok files
  bench [path] [filter]        time the `#[bench]` functions
  lint [path]                  lint (levels: Rok.toml [lints], then -A/-W/-D)
  doc [path]                   HTML docs (with dependencies) in target/doc/

environments:
  env create|remove|use <name>      a named environment
  env list                          (`*`: the active one)
  env export <name> <dir>           write its Rok.toml / Rok.lock to <dir>
  env import <name> <dir|Rok.toml>  create it from a project or export
  env shell [name]                  a $SHELL with ROK_ENV=<name>

toolchains:
  toolchain list
  toolchain install <version> --from <dir | .tar[.gz]>
  toolchain remove <version>

options:
  --env <name>    use that environment instead of the project's
  --offline       never fetch (git dependencies must be cached)
  --locked        fail instead of changing Rok.lock
  --cwd <dir>     change directory first
  -q, --quiet     less output
  version, help

A directory with Rok.toml is a project (its own environment). Outside one,
the environment is $ROK_ENV, else the one `rok env use` chose, else
`default`. A lone script may start with a //! ```toml block holding
[deps].

environment: ROK_HOME (default: the parent of rok's bin/), ROK_ENV
";

#[derive(Default)]
struct Global {
    env: Option<String>,
    offline: bool,
    locked: bool,
    quiet: bool,
}

/// rokc options that take a separate value (`--name value`).
const VALUE_FLAGS: &[&str] = &[
    "-o",
    "--out",
    "--output",
    "--bootstrap",
    "--cfg",
    "--target",
    "--rokr",
    "--emit",
    "--stage",
    "--threads",
    "--color",
    "--message-format",
    "--target-dir",
    "--extern",
    "-A",
    "-W",
    "-D",
    "--allow",
    "--warn",
    "--deny",
    "--iters",
    "--samples",
    "--connection-file",
];

/// `ROK_HOME`, else the parent of the directory holding `rok`.
pub fn home() -> PathBuf {
    std::env::var_os("ROK_HOME")
        .filter(|h| !h.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            let exe = std::env::current_exe().ok()?;
            Some(exe.parent()?.parent()?.to_path_buf())
        })
        .unwrap_or_else(|| PathBuf::from("."))
}

/// Run `rok` with `args` (without the program name); the exit code.
pub fn main_with(args: Vec<String>) -> i32 {
    let mut g = Global::default();
    let mut rest = Vec::new();
    let mut it = args.into_iter();
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
    // The command: the first word that is not an option or its value.
    let mut i = 0;
    while i < rest.len() && rest[i].starts_with('-') && rest[i] != "--" {
        i += if VALUE_FLAGS.contains(&rest[i].as_str()) {
            2
        } else {
            1
        };
    }
    if i >= rest.len() || rest[i] == "--" {
        match rest
            .iter()
            .find(|a| matches!(a.as_str(), "-V" | "--version" | "-h" | "--help"))
        {
            Some(v) if v == "-V" || v == "--version" => {
                println!("rok {VERSION}");
                return 0;
            }
            Some(_) => {
                print!("{USAGE}");
                return 0;
            }
            // Bare `rok` (options only) is `rok repl`, like `python` / `julia`.
            None => rest.insert(i, "repl".into()),
        }
    }
    let cmd = rest[i].clone();
    let pre = rest[..i].to_vec();
    let post = rest[i + 1..].to_vec();
    let r = match cmd.as_str() {
        "version" => {
            println!("rok {VERSION}");
            Ok(0)
        }
        "help" => {
            print!("{USAGE}");
            Ok(0)
        }
        "new" | "init" => cmd_new(&g, &cmd, &pre, &post),
        "add" => cmd_add(&g, &post),
        "remove" => cmd_remove(&g, &post),
        "update" => cmd_update(&g, &post),
        "deps" => cmd_deps(&g, &post),
        "env" => env::cmd(&g, &post),
        "toolchain" => toolchain::cmd(&post),
        // The kernelspec runs `rok [--env <name>] jupyter ..`: rokc writes it.
        "jupyter" if post.first().is_some_and(|p| p == "install") => {
            let mut args = vec!["--install-kernel".to_owned()];
            args.extend(post[1..].iter().cloned());
            args.extend(g.env.iter().flat_map(|e| ["--env".to_owned(), e.clone()]));
            delegate(&g, &cmd, &pre, &args)
        }
        "build" | "check" | "run" | "test" | "repl" | "lsp" | "fmt" | "clean" | "demangle"
        | "emit" | "bench" | "doc" | "lint" | "jupyter" => delegate(&g, &cmd, &pre, &post),
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

/// Positional arguments of a rokc command line (up to `--`).
fn positionals(args: &[String]) -> Vec<&str> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < args.len() && args[i] != "--" {
        let a = args[i].as_str();
        if VALUE_FLAGS.contains(&a) {
            i += 1;
        } else if !a.starts_with('-') || a == "-" {
            out.push(a);
        }
        i += 1;
    }
    out
}

/// The package directory `start` belongs to: the nearest directory at
/// or above it holding `main.rok`, `lib.rok` or `Rok.toml`.
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

/// What a command works on, the environment name to hand down, and
/// the pinned toolchain.
struct Target {
    ctx: Context,
    env: Option<String>,
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
            });
        }
    } else if start.is_file() {
        // A lone script: its own `//! ```toml` block, if any.
        let src = std::fs::read_to_string(start).unwrap_or_default();
        if let Some(block) = manifest::script_block(&src) {
            let file = format!("{} (//! toml block)", start.display());
            let manifest = manifest::parse(&block, &file)?;
            if manifest.dev_deps.len() + usize::from(manifest.toolchain.is_some()) > 0
                || manifest.name.is_some()
            {
                return Err(format!("{file}: a script block holds only [deps]"));
            }
            let abs = std::fs::canonicalize(start).map_err(|e| e.to_string())?;
            let key = format!("{}\0{block}", abs.display());
            let cache = home()
                .join("cache/scripts")
                .join(format!("{:016x}", git::fnv(&key)));
            std::fs::create_dir_all(&cache).map_err(|e| format!("{}: {e}", cache.display()))?;
            return Ok(Target {
                ctx: Context {
                    manifest,
                    base: abs.parent().unwrap_or_else(|| Path::new("/")).to_path_buf(),
                    lock_path: Some(cache.join(manifest::LOCK)),
                },
                env: None,
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

/// Run `rokc <pre> <cmd> --extern.. <post>` for `build` / `run` / ...
fn delegate(g: &Global, cmd: &str, pre: &[String], post: &[String]) -> Result<i32, String> {
    let pos = positionals(post);
    let path = match cmd {
        "build" | "check" | "run" | "clean" | "emit" | "lint" | "doc" => {
            pos.first().copied().filter(|p| *p != "-")
        }
        // `test [path] [filter]`: a lone non-path argument is the filter.
        "test" | "bench" => pos.first().copied().filter(|p| Path::new(p).exists()),
        _ => None,
    };
    let t = target_for(g, path)?;
    let externs: Vec<Resolved> = match cmd {
        "fmt" | "clean" | "demangle" => Vec::new(),
        "jupyter" if post.iter().any(|a| a == "--install-kernel") => Vec::new(),
        _ => match resolve::resolve(&home(), &t.ctx, &options(g)) {
            Ok(r) => r
                .into_iter()
                .filter(|p| matches!(cmd, "test" | "bench") || !p.dev)
                .collect(),
            // The language server still starts (without dependencies).
            Err(e) if cmd == "lsp" => {
                eprintln!("rok: warning: {e}");
                Vec::new()
            }
            Err(e) => return Err(e),
        },
    };
    let (rokc, toolchain_home) = toolchain::rokc_for(t.ctx.manifest.toolchain.as_deref())?;
    // A package's build links its dependencies prebuilt (`.a` + RHIR),
    // each rebuilt only when it changed; other commands (and scripts /
    // environments) compile them from source.
    let mut flags: Vec<String> = pre.to_vec();
    flags.extend(post.iter().cloned());
    if cmd == "bench"
        && !flags
            .iter()
            .any(|f| f == "--release" || f.starts_with("-O"))
    {
        flags.push("-O2".to_owned()); // rokc's bench default
    }
    let pkg = package_dir(Path::new(path.unwrap_or(".")));
    let roots: Vec<(String, PathBuf)> = match pkg {
        Some(dir) if t.env.is_none() && matches!(cmd, "build" | "run" | "test" | "bench") => {
            prebuilt::build(
                &rokc,
                toolchain_home.as_deref(),
                &dir,
                &flags,
                &externs,
                g.quiet,
            )?
        }
        _ => externs
            .iter()
            .map(|p| (p.name.clone(), p.root.clone()))
            .collect(),
    };
    let mut c = Command::new(&rokc);
    c.args(pre).arg(cmd);
    for (name, root) in &roots {
        c.arg("--extern").arg(format!("{name}={}", root.display()));
    }
    // `[lints]` go first: the command line's own `-A/-W/-D` win.
    if cmd == "lint" {
        for (name, level) in &t.ctx.manifest.lints {
            c.arg(level.flag()).arg(name);
        }
    }
    c.args(post);
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

/// `rok new` / `rok init`: rokc makes the package; rok adds `Rok.toml`.
fn cmd_new(g: &Global, cmd: &str, pre: &[String], post: &[String]) -> Result<i32, String> {
    let pos = positionals(post);
    let dir = PathBuf::from(pos.first().copied().unwrap_or("."));
    let (rokc, _) = toolchain::rokc_for(None)?;
    let status = Command::new(&rokc)
        .args(pre)
        .arg(cmd)
        .args(post)
        .status()
        .map_err(|e| format!("cannot run {}: {e}", rokc.display()))?;
    if !status.success() {
        return Ok(status.code().unwrap_or(1));
    }
    if manifest::find(&dir).is_none() {
        let abs = std::path::absolute(&dir).map_err(|e| e.to_string())?;
        let name = abs
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("app")
            .to_owned();
        let text = format!(
            "[package]\nname = {}\nversion = \"0.1.0\"\n\n[deps]\n",
            rokc_toml::format_value(&rokc_toml::Value::String(name))
        );
        let path = dir.join(MANIFEST);
        std::fs::write(&path, text).map_err(|e| format!("{}: {e}", path.display()))?;
        if !g.quiet {
            eprintln!("     Created {}", path.display());
        }
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
        "not inside a package (no main.rok, lib.rok or Rok.toml here or above); run `rok init`, \
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
    let mut doc = rokc_toml::Document::parse(old.as_deref().unwrap_or(""))
        .map_err(|e| e.render(old.as_deref().unwrap_or(""), &path.display().to_string()))?;
    let section = if dev { "dev-deps" } else { "deps" };
    doc.set(&[section], &dep.name, &dep.source.to_toml())
        .map_err(|e| format!("cannot edit {}: {e}", path.display()))?;
    write_and_resolve(g, &path, old.as_deref(), doc.text())?;
    if !g.quiet {
        eprintln!(
            "       Added {} to [{section}] of {}",
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
    let mut doc = rokc_toml::Document::parse(&old)
        .map_err(|e| e.render(&old, &path.display().to_string()))?;
    let mut removed = false;
    for section in ["deps", "dev-deps"] {
        removed |= doc
            .remove(&[section], name)
            .map_err(|e| format!("cannot edit {}: {e}", path.display()))?;
    }
    if !removed {
        return Err(format!(
            "`{name}` is not a dependency in {}",
            path.display()
        ));
    }
    write_and_resolve(g, &path, Some(&old), doc.text())?;
    if !g.quiet {
        eprintln!("     Removed {name} from {}", path.display());
    }
    Ok(0)
}

#[allow(clippy::many_single_char_names)]
fn cmd_update(g: &Global, names: &[String]) -> Result<i32, String> {
    let t = target_for(g, None)?;
    let m = &t.ctx.manifest;
    for n in names {
        if !m.deps.iter().chain(&m.dev_deps).any(|d| d.name == *n) {
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
    let mut o = options(g);
    o.update = Some(names.to_vec());
    let r = resolve::resolve(&home(), &t.ctx, &o)?;
    if !g.quiet {
        if let Some(p) = &t.ctx.lock_path {
            eprintln!("     Updated {} ({} packages)", p.display(), r.len());
        }
    }
    Ok(0)
}

/// `rok deps [path]`: `name=<lib.rok>` per dependency (plumbing for the
/// REPL's `:add`).
fn cmd_deps(g: &Global, args: &[String]) -> Result<i32, String> {
    let pos = positionals(args);
    let t = target_for(g, pos.first().copied())?;
    let dev = args.iter().any(|a| a == "--dev");
    for p in resolve::resolve(&home(), &t.ctx, &options(g))? {
        if dev || !p.dev {
            println!("{}={}", p.name, p.root.display());
        }
    }
    Ok(0)
}

//! Toolchains (spec 9.10.6, 9.2.19): `$ROK_HOME/toolchains/<version>-<triple>/`,
//! each self-contained (`bin/{rok,rokc,rokls}`, `lib/librokr.a`,
//! `lib/rok/`). `$ROK_HOME/bin/{rok,rokc,rokls}` are proxies: copies of
//! a toolchain's `rok` that run the active toolchain's executable of the
//! same name. The active toolchain: `+<version>` > `ROK_TOOLCHAIN` > the
//! nearest `rok.rokon`'s `toolchain` > `rok toolchain default`.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::{VERSION, home, manifest};

/// The triple this `rok` runs on.
pub const HOST: &str = env!("ROK_HOST");

const TOOLS: [&str; 3] = ["rok", "rokc", "rokls"];

fn exe_name(tool: &str) -> String {
    format!("{tool}{}", std::env::consts::EXE_SUFFIX)
}

/// `pin` (`"0.3"`) accepts `version` (`"0.3"`, `"0.3.1"`).
fn matches(pin: &str, version: &str) -> bool {
    version == pin
        || version
            .strip_prefix(pin)
            .is_some_and(|r| r.starts_with('.'))
}

fn root(home: &Path) -> PathBuf {
    home.join("toolchains")
}

/// `(directory name, version)` of the installed toolchains for this
/// host, oldest first.
fn installed(home: &Path) -> Vec<(String, String)> {
    let suffix = format!("-{HOST}");
    let mut v: Vec<(String, String)> = std::fs::read_dir(root(home))
        .map(|rd| {
            rd.flatten()
                .filter(|e| e.path().is_dir())
                .filter_map(|e| e.file_name().into_string().ok())
                .filter_map(|n| Some((n.clone(), n.strip_suffix(&suffix)?.to_owned())))
                .collect()
        })
        .unwrap_or_default();
    // Numeric order: 0.10 after 0.9.
    v.sort_by_key(|(_, ver)| {
        ver.split(['.', '-'])
            .map(|p| p.parse::<u64>().unwrap_or(0))
            .collect::<Vec<_>>()
    });
    v
}

/// The newest installed toolchain `pin` accepts (a version prefix, or a
/// whole directory name).
fn find(home: &Path, pin: &str) -> Option<PathBuf> {
    installed(home)
        .into_iter()
        .rev()
        .find(|(name, ver)| name == pin || matches(pin, ver))
        .map(|(name, _)| root(home).join(name))
}

fn not_installed(pin: &str, why: &str) -> String {
    format!(
        "toolchain {pin} ({why}) is not installed; install it with `rok toolchain install {pin} \
         --from <dir | .tar.gz | .zip | url>`"
    )
}

/// The nearest `rok.rokon` at or above the working directory, and its
/// `toolchain` (a manifest that does not load pins nothing here).
fn manifest_pin() -> Option<(PathBuf, String)> {
    let cwd = std::env::current_dir().ok()?;
    let path = cwd.ancestors().find_map(manifest::find)?;
    let pin = manifest::load(&path).ok()?.toolchain?;
    Some((path, pin))
}

/// `toolchain` of `$ROK_HOME/config.rokon`.
fn default_pin(home: &Path) -> Result<Option<String>, String> {
    crate::config(home, "toolchain")
}

/// The toolchain to run: `plus` (`+<version>`), else `ROK_TOOLCHAIN`,
/// else the manifest's, else the default.
fn active(home: &Path, plus: Option<&str>) -> Result<PathBuf, String> {
    let env = std::env::var("ROK_TOOLCHAIN")
        .ok()
        .filter(|t| !t.is_empty());
    let (pin, why) = if let Some(p) = plus {
        (p.to_owned(), "`+` on the command line".to_owned())
    } else if let Some(p) = env {
        (p, "ROK_TOOLCHAIN".to_owned())
    } else if let Some((path, p)) = manifest_pin() {
        (p, format!("pinned by {}", path.display()))
    } else if let Some(p) = default_pin(home)? {
        (p, "the default".to_owned())
    } else {
        return Err(
            "no default toolchain; install one (`rok toolchain install`) or choose one with \
             `rok toolchain default <version>`"
                .to_owned(),
        );
    };
    find(home, &pin).ok_or_else(|| not_installed(&pin, &why))
}

/// Run as a proxy, when this executable is one; the exit code.
///
/// A proxy is `$ROK_HOME/bin/<tool>` beside `$ROK_HOME/toolchains/`: it
/// runs the active toolchain's `<tool>` with the same arguments. `None`:
/// not a proxy, or `rok toolchain ..` (the proxy manages the toolchains
/// itself).
pub fn proxy(args: &[OsString]) -> Option<i32> {
    let exe = rokc_core::current_exe()?;
    let h = exe.parent()?.parent()?;
    if !h.join("toolchains").is_dir() {
        return None;
    }
    let tool = exe.file_stem()?.to_str()?;
    let tool = TOOLS.into_iter().find(|t| *t == tool)?;
    let (plus, rest) = match args.first().and_then(|a| a.to_str()) {
        Some(p) if p.len() > 1 && p.starts_with('+') => (Some(&p[1..]), &args[1..]),
        _ => (None, args),
    };
    let command = rest
        .iter()
        .find(|a| !a.to_str().is_some_and(|a| a.starts_with('-')));
    if tool == "rok" && plus.is_none() && command.is_some_and(|c| c == "toolchain") {
        return None;
    }
    let dir = match active(h, plus) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("{tool}: error: {e}");
            return Some(1);
        }
    };
    let target = dir.join("bin").join(exe_name(tool));
    let mut c = Command::new(&target);
    c.args(rest).env("ROK_HOME", h);
    if let Some(p) = plus {
        // The toolchain's `rok` runs the same toolchain's `rokc`.
        c.env("ROK_TOOLCHAIN", p);
    }
    Some(crate::exec(c, &target))
}

/// The `rokc` to run: this `rok`'s own, unless the active pin (`+`,
/// `ROK_TOOLCHAIN`, then the manifest's `pin`) names another version;
/// then that installed toolchain's.
pub fn rokc_for(plus: Option<&str>, pin: Option<&str>) -> Result<PathBuf, String> {
    let env = std::env::var("ROK_TOOLCHAIN")
        .ok()
        .filter(|t| !t.is_empty());
    let chosen = plus
        .map(|p| (p.to_owned(), "`+` on the command line"))
        .or_else(|| env.map(|p| (p, "ROK_TOOLCHAIN")))
        .or_else(|| pin.map(|p| (p.to_owned(), "rok.rokon")));
    if let Some((p, why)) = chosen.filter(|(p, _)| !matches(p, VERSION)) {
        let dir = find(&home(), &p).ok_or_else(|| not_installed(&p, why))?;
        return Ok(dir.join("bin").join(exe_name("rokc")));
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let rokc = exe.with_file_name(exe_name("rokc"));
    if !rokc.is_file() {
        return Err(format!("no `rokc` next to {}", exe.display()));
    }
    Ok(rokc)
}

fn copy_tree(from: &Path, to: &Path) -> Result<(), String> {
    std::fs::create_dir_all(to).map_err(|e| format!("{}: {e}", to.display()))?;
    for e in std::fs::read_dir(from).map_err(|e| format!("{}: {e}", from.display()))? {
        let e = e.map_err(|e| e.to_string())?;
        let (src, dst) = (e.path(), to.join(e.file_name()));
        if src.is_dir() {
            copy_tree(&src, &dst)?;
        } else {
            // `copy` keeps the permission bits (executables stay so).
            std::fs::copy(&src, &dst).map_err(|e| format!("{}: {e}", src.display()))?;
        }
    }
    Ok(())
}

fn run(c: &mut Command, what: &str) -> Result<String, String> {
    let out = c.output().map_err(|e| format!("cannot run {what}: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "{what} failed:\n{}",
            String::from_utf8_lossy(&out.stderr).trim_end()
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Check `archive` against the SHA-256 in `sum` (a release's
/// `<archive>.sha256`: the hex digest, then optionally the file name).
fn check_sum(archive: &Path, sum: &Path, what: &str) -> Result<(), String> {
    let text = std::fs::read_to_string(sum).map_err(|e| format!("{}: {e}", sum.display()))?;
    let want = text
        .split_whitespace()
        .next()
        .unwrap_or("")
        .to_ascii_lowercase();
    if want.len() != 64 || !want.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!("{}: not a SHA-256 digest", sum.display()));
    }
    let bytes = std::fs::read(archive).map_err(|e| format!("{}: {e}", archive.display()))?;
    let got = rokc_core::hash::hex(&rokc_core::hash::sha256(&bytes));
    if got != want {
        return Err(format!(
            "{what} has SHA-256 {got}, but its .sha256 says {want} (a damaged or altered download)"
        ));
    }
    Ok(())
}

/// Unpack `from` (a directory, a `.tar[.gz]`, a `.zip` (Windows' `tar`
/// reads it), or an `http(s)://` URL of one) into `tmp`; the
/// toolchain's top directory there. A download is checked against the
/// `.sha256` beside it at the same place, an archive file against its
/// `.sha256` when one is beside it.
fn unpack(from: &str, tmp: &Path) -> Result<PathBuf, String> {
    let mut archive = PathBuf::from(from);
    let curl = |url: &str, to: &Path| {
        run(
            Command::new("curl")
                .args(["-fsSL", "--proto", "=https,http", "-o"])
                .arg(to)
                .arg(url),
            &format!("curl {url}"),
        )
    };
    if from.starts_with("https://") || from.starts_with("http://") {
        // `tar` tells the format by the content.
        archive = tmp.join("download");
        let sum = tmp.join("download.sha256");
        curl(from, &archive)?;
        curl(&format!("{from}.sha256"), &sum)?;
        check_sum(&archive, &sum, from)?;
    } else {
        let mut sum = archive.clone().into_os_string();
        sum.push(".sha256");
        let sum = PathBuf::from(sum);
        if archive.is_file() && sum.is_file() {
            check_sum(&archive, &sum, from)?;
        }
    }
    let files = tmp.join("files");
    if archive.is_dir() {
        copy_tree(&archive, &files)?;
    } else if archive.is_file() {
        std::fs::create_dir_all(&files).map_err(|e| e.to_string())?;
        run(
            Command::new("tar")
                .arg("-xf")
                .arg(&archive)
                .arg("-C")
                .arg(&files),
            &format!("tar -xf {}", archive.display()),
        )?;
    } else {
        return Err(format!("{from} does not exist"));
    }
    // An archive holding one top directory: that directory.
    if !files.join("bin").is_dir() {
        let entries: Vec<PathBuf> = std::fs::read_dir(&files)
            .map_err(|e| e.to_string())?
            .flatten()
            .map(|e| e.path())
            .collect();
        if let [only] = entries.as_slice() {
            return Ok(only.clone());
        }
    }
    Ok(files)
}

/// Check that the toolchain at `top` is whole and is `version` for this
/// host (its `bin/rokc --version --verbose`); its full version.
fn verify(top: &Path, version: &str) -> Result<String, String> {
    let rokc = top.join("bin").join(exe_name("rokc"));
    if !rokc.is_file() {
        return Err("not a rok toolchain: no bin/rokc".to_owned());
    }
    for need in [
        format!("bin/{}", exe_name("rok")),
        format!("lib/{}", rokc_target::TargetSpec::host().runtime_lib()),
        "lib/rok/core/src/lib.rok".to_owned(),
    ] {
        if !top.join(&need).exists() {
            return Err(format!("incomplete toolchain: no {need}"));
        }
    }
    let out = run(
        Command::new(&rokc).args(["--version", "--verbose"]),
        &rokc.display().to_string(),
    )?;
    let full = out
        .lines()
        .find_map(|l| l.strip_prefix("rokc "))
        .and_then(|l| l.split_whitespace().next())
        .ok_or_else(|| format!("unexpected `rokc --version` output: {out:?}"))?;
    if !matches(version, full) {
        return Err(format!(
            "the toolchain is rokc {full}, not {version} (its `bin/rokc --version`)"
        ));
    }
    if let Some(h) = out.lines().find_map(|l| l.strip_prefix("host: ")) {
        if h.trim() != HOST {
            return Err(format!(
                "the toolchain is built for {}, but this machine is {HOST}",
                h.trim()
            ));
        }
    }
    Ok(full.to_owned())
}

/// A scratch directory under `toolchains/`, removed when dropped.
struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Unpack and check `from` in a scratch directory: it, the toolchain's
/// top directory in it, and the toolchain's full version.
fn stage(home: &Path, version: &str, from: &str) -> Result<(Scratch, PathBuf, String), String> {
    std::fs::create_dir_all(root(home)).map_err(|e| e.to_string())?;
    let tmp = Scratch(root(home).join(format!(".tmp-{}", std::process::id())));
    let _ = std::fs::remove_dir_all(&tmp.0);
    std::fs::create_dir_all(&tmp.0).map_err(|e| format!("{}: {e}", tmp.0.display()))?;
    let top = unpack(from, &tmp.0)?;
    let full = verify(&top, version)?;
    Ok((tmp, top, full))
}

/// Move the staged toolchain `top` to `toolchains/<full>-<host>`; its
/// name. One already there is moved aside into `tmp` first, and back if
/// the move fails.
fn place(home: &Path, tmp: &Scratch, top: &Path, full: &str) -> Result<String, String> {
    let name = format!("{full}-{HOST}");
    let dest = root(home).join(&name);
    let old = tmp.0.join("old");
    let had = dest.exists();
    if had {
        std::fs::rename(&dest, &old).map_err(|e| format!("{}: {e}", dest.display()))?;
    }
    if let Err(e) = std::fs::rename(top, &dest) {
        if had {
            let _ = std::fs::rename(&old, &dest);
        }
        return Err(format!("{}: {e}", dest.display()));
    }
    Ok(name)
}

fn install(home: &Path, version: &str, from: &str) -> Result<String, String> {
    let (tmp, top, full) = stage(home, version, from)?;
    place(home, &tmp, &top, &full)
}

/// `$ROK_HOME/bin/{rok,rokc,rokls}`: copies of `toolchain`'s `rok`.
fn write_proxies(home: &Path, toolchain: &Path) -> Result<(), String> {
    let bin = home.join("bin");
    std::fs::create_dir_all(&bin).map_err(|e| format!("{}: {e}", bin.display()))?;
    let src = toolchain.join("bin").join(exe_name("rok"));
    for t in TOOLS {
        let dst = bin.join(exe_name(t));
        // Copy beside, then rename: a running proxy keeps its file.
        let tmp = bin.join(format!(".{t}.tmp"));
        std::fs::copy(&src, &tmp).map_err(|e| format!("{}: {e}", src.display()))?;
        if cfg!(windows) {
            set_aside(&bin, &dst);
        }
        std::fs::rename(&tmp, &dst).map_err(|e| format!("{}: {e}", dst.display()))?;
    }
    Ok(())
}

/// Windows cannot replace a running executable (this proxy, when `rok
/// toolchain default` runs through it), but can rename it: move `exe`
/// to `.old-<n>` in `bin`, and delete earlier ones no longer running.
fn set_aside(bin: &Path, exe: &Path) {
    for e in std::fs::read_dir(bin).into_iter().flatten().flatten() {
        if e.file_name().to_string_lossy().starts_with(".old-") {
            let _ = std::fs::remove_file(e.path());
        }
    }
    if exe.exists() {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let _ = std::fs::rename(exe, bin.join(format!(".old-{nanos:x}")));
    }
}

fn set_default(home: &Path, pin: &str) -> Result<PathBuf, String> {
    let dir = find(home, pin).ok_or_else(|| not_installed(pin, "the default"))?;
    crate::set_config(home, "toolchain", pin)?;
    write_proxies(home, &dir)?;
    Ok(dir)
}

/// The release server: `<dist>/download/v<version>/rok-<version>-<triple>.<ext>`
/// with its `.sha256`, and `<dist>/latest/download/rok-version`, the
/// newest release's version (GitHub releases' layout). `ROK_DIST`
/// overrides it.
fn dist() -> String {
    std::env::var("ROK_DIST")
        .ok()
        .filter(|d| !d.is_empty())
        .unwrap_or_else(|| "https://github.com/rok-lang/rok/releases".to_owned())
        .trim_end_matches('/')
        .to_owned()
}

const ARCHIVE: &str = if cfg!(windows) { "zip" } else { "tar.gz" };

/// `v` if it can be a release's full version.
fn release_version(v: &str, from: &str) -> Result<String, String> {
    let ok = v.starts_with(|c: char| c.is_ascii_digit())
        && v.chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '+'));
    if ok {
        Ok(v.to_owned())
    } else {
        Err(format!("{from}: `{v}` is not a version"))
    }
}

/// The newest release's version, from `<dist>/latest/download/rok-version`.
fn latest(dist: &str) -> Result<String, String> {
    let url = format!("{dist}/latest/download/rok-version");
    let out = run(
        Command::new("curl").args(["-fsSL", "--proto", "=https,http", &url]),
        &format!("curl {url}"),
    )?;
    release_version(out.trim(), &url)
}

/// `bin/rok` runs and `bin/rokc` is `full`, as the default toolchain
/// (no `ROK_TOOLCHAIN`, outside any project).
fn check_proxies(home: &Path, full: &str) -> Result<(), String> {
    let version = |tool: &str| {
        let exe = home.join("bin").join(exe_name(tool));
        run(
            Command::new(&exe)
                .arg("--version")
                .env("ROK_HOME", home)
                .env_remove("ROK_TOOLCHAIN")
                .current_dir(home),
            &exe.display().to_string(),
        )
    };
    version("rok")?;
    let out = version("rokc")?;
    let first = out.lines().next().unwrap_or("");
    let want = format!("rokc {full}");
    if first != want && !first.starts_with(&format!("{want} ")) {
        return Err(format!("the rokc proxy says {first:?}, not {want}"));
    }
    Ok(())
}

/// Make `full` (installed at `dir`) the default and write its proxies,
/// then check that they run it. On failure the config and the proxies
/// are put back, and `dir` removed if `fresh` (installed for this).
fn switch(home: &Path, full: &str, dir: &Path, fresh: bool) -> Result<(), String> {
    let bin = home.join("bin");
    let config = home.join("config.rokon");
    let old_config = std::fs::read(&config).ok();
    let mut kept = Vec::new();
    for t in TOOLS {
        let p = bin.join(exe_name(t));
        if p.is_file() {
            let prev = bin.join(format!(".{t}.prev"));
            std::fs::copy(&p, &prev).map_err(|e| format!("{}: {e}", p.display()))?;
            kept.push((p, prev));
        }
    }
    let Err(e) = set_default(home, full).and_then(|_| check_proxies(home, full)) else {
        for (_, prev) in &kept {
            let _ = std::fs::remove_file(prev);
        }
        return Ok(());
    };
    let mut lost = Vec::new();
    let restored = match &old_config {
        Some(c) => std::fs::write(&config, c),
        None => std::fs::remove_file(&config),
    };
    if let Err(e) = restored {
        lost.push(format!("{}: {e}", config.display()));
    }
    for t in TOOLS {
        let p = bin.join(exe_name(t));
        let r = match kept.iter().find(|(q, _)| *q == p) {
            Some((_, prev)) => {
                if cfg!(windows) {
                    set_aside(&bin, &p);
                }
                std::fs::rename(prev, &p)
            }
            None if p.exists() => std::fs::remove_file(&p),
            None => Ok(()),
        };
        if let Err(e) = r {
            lost.push(format!("{}: {e}", p.display()));
        }
    }
    if fresh {
        let _ = std::fs::remove_dir_all(dir);
    }
    if lost.is_empty() {
        Err(format!(
            "{e}\nrolled back: the default toolchain and the proxies are as they were"
        ))
    } else {
        Err(format!("{e}\nrolling back failed: {}", lost.join("; ")))
    }
}

/// `rok toolchain update`: install release `version` (default: the newest), make
/// it the default and update the proxies.
fn update(home: &Path, version: Option<&str>, quiet: bool) -> Result<(), String> {
    let dist = dist();
    let full = match version {
        Some(v) => release_version(v, "rok toolchain update")?,
        None => latest(&dist)?,
    };
    let name = format!("{full}-{HOST}");
    let dir = root(home).join(&name);
    let current = default_pin(home)?.and_then(|p| find(home, &p));
    if current.as_ref() == Some(&dir) && check_proxies(home, &full).is_ok() {
        if !quiet {
            eprintln!("rok {full} is up to date");
        }
        return Ok(());
    }
    let fresh = !dir.is_dir();
    if fresh {
        let url = format!("{dist}/download/v{full}/rok-{full}-{HOST}.{ARCHIVE}");
        if !quiet {
            eprintln!(" Downloading {url}");
        }
        let (tmp, top, _) = stage(home, &full, &url)?;
        place(home, &tmp, &top, &full)?;
    }
    switch(home, &full, &dir, fresh)?;
    if !quiet {
        eprintln!("     Updated to rok {full} ({name})");
        if let Some(old) = current.filter(|c| *c != dir) {
            let old = old.file_name().unwrap_or_default().to_string_lossy();
            eprintln!("        note: {old} stays installed (`rok toolchain remove {old}`)");
        }
    }
    Ok(())
}

pub const USAGE: &str = "\
usage: rok toolchain list
       rok toolchain install <version> --from <dir | .tar[.gz] | .zip | url>
       rok toolchain default [<version>]
       rok toolchain remove <version>
       rok toolchain update [<version>]";

pub fn cmd(args: &[String], quiet: bool) -> Result<i32, String> {
    let h = home();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["list"] => {
            let def = default_pin(&h)?.and_then(|p| find(&h, &p));
            let all = installed(&h);
            if all.is_empty() {
                println!("no toolchains installed (this rok is {VERSION})");
            }
            for (name, _) in all {
                let mark = if def.as_ref().is_some_and(|d| d.ends_with(&name)) {
                    " (default)"
                } else {
                    ""
                };
                println!("{name}{mark}");
            }
        }
        ["install", version, rest @ ..] => {
            let from = match rest {
                ["--from", f] => *f,
                [f] if f.starts_with("--from=") => &f[7..],
                _ => return Err(USAGE.into()),
            };
            let name = install(&h, version, from)?;
            if !quiet {
                eprintln!("   Installed toolchain {name}");
            }
            // The first toolchain becomes the default; the proxies are
            // made once.
            let def = default_pin(&h)?;
            if def.is_none() {
                set_default(&h, &name)?;
                if !quiet {
                    eprintln!("     Default toolchain {name}");
                }
            } else if !h.join("bin").join(exe_name("rok")).is_file() {
                let d = def.as_deref().and_then(|p| find(&h, p));
                write_proxies(&h, &d.unwrap_or_else(|| root(&h).join(&name)))?;
            }
        }
        ["update"] => update(&h, None, quiet)?,
        ["update", v] if !v.starts_with('-') => update(&h, Some(v), quiet)?,
        ["default"] => match default_pin(&h)? {
            Some(p) => println!("{p}"),
            None => return Err("no default toolchain".into()),
        },
        ["default", pin] => {
            let dir = set_default(&h, pin)?;
            if !quiet {
                let name = dir.file_name().unwrap_or_default().to_string_lossy();
                eprintln!("     Default toolchain {pin} ({name})");
            }
        }
        ["remove", name] if !name.contains(['/', '\\']) && !name.starts_with('.') => {
            let dir = [root(&h).join(name), root(&h).join(format!("{name}-{HOST}"))]
                .into_iter()
                .find(|d| d.is_dir())
                .ok_or_else(|| format!("toolchain {name} is not installed"))?;
            std::fs::remove_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        }
        _ => return Err(USAGE.into()),
    }
    Ok(0)
}

#[cfg(test)]
mod tests {
    #[test]
    fn pins_match_prefixes() {
        assert!(super::matches("0.3", "0.3.1"));
        assert!(super::matches("0.3.1", "0.3.1"));
        assert!(!super::matches("0.3", "0.30.0"));
        assert!(!super::matches("0.3.1", "0.3"));
    }
}

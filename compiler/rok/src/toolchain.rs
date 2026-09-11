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
         --from <dir | .tar.gz | url>`"
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
    let exe = std::env::current_exe().ok()?;
    let exe = std::fs::canonicalize(&exe).unwrap_or(exe);
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

/// Unpack `from` (a directory, a `.tar[.gz]`, or an `http(s)://` URL of
/// one) into `tmp`; the toolchain's top directory there.
fn unpack(from: &str, tmp: &Path) -> Result<PathBuf, String> {
    let mut archive = PathBuf::from(from);
    if from.starts_with("https://") || from.starts_with("http://") {
        archive = tmp.join("download.tar.gz");
        run(
            Command::new("curl")
                .args(["-fsSL", "--proto", "=https,http", "-o"])
                .arg(&archive)
                .arg(from),
            &format!("curl {from}"),
        )?;
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
    for need in ["bin/rok", "lib/librokr.a", "lib/rok/core/lib.rok"] {
        if !top.join(need).exists() {
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

fn install(home: &Path, version: &str, from: &str) -> Result<String, String> {
    std::fs::create_dir_all(root(home)).map_err(|e| e.to_string())?;
    let tmp = root(home).join(format!(".tmp-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?;
    let result = (|| {
        let top = unpack(from, &tmp)?;
        let full = verify(&top, version)?;
        let name = format!("{full}-{HOST}");
        let dest = root(home).join(&name);
        // Reinstalling replaces.
        if dest.exists() {
            std::fs::remove_dir_all(&dest).map_err(|e| format!("{}: {e}", dest.display()))?;
        }
        std::fs::rename(&top, &dest).map_err(|e| format!("{}: {e}", dest.display()))?;
        Ok(name)
    })();
    let _ = std::fs::remove_dir_all(&tmp);
    result
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
        std::fs::rename(&tmp, &dst).map_err(|e| format!("{}: {e}", dst.display()))?;
    }
    Ok(())
}

fn set_default(home: &Path, pin: &str) -> Result<PathBuf, String> {
    let dir = find(home, pin).ok_or_else(|| not_installed(pin, "the default"))?;
    crate::set_config(home, "toolchain", pin)?;
    write_proxies(home, &dir)?;
    Ok(dir)
}

pub const USAGE: &str = "\
usage: rok toolchain list
       rok toolchain install <version> --from <dir | .tar[.gz] | url>
       rok toolchain default [<version>]
       rok toolchain remove <version>";

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

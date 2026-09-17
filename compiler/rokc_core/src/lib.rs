//! Definitions shared by the compiler and the `rok` tool.

pub mod codec;
pub mod def;
pub mod hash;
pub mod lint;

use std::path::{Path, PathBuf};

pub use def::{DefId, DefInfo, DefKind, DefTable, Visibility};

/// The user's rok directory (spec 9.2.19).
///
/// `$ROK_HOME`; else the home the running executable belongs to
/// (`<home>/bin/rok`, a proxy, or `<home>/toolchains/<name>/bin/rok`);
/// else `~/.rok` (`%USERPROFILE%\.rok` on Windows).
#[must_use]
pub fn rok_home() -> Option<PathBuf> {
    if let Some(h) = std::env::var_os("ROK_HOME").filter(|h| !h.is_empty()) {
        return Some(PathBuf::from(h));
    }
    if let Some(h) = std::env::current_exe().ok().and_then(|e| home_of(&e)) {
        return Some(h);
    }
    Some(user_home()?.join(".rok"))
}

/// The user's home directory: `%USERPROFILE%` on Windows, else `$HOME`.
#[must_use]
pub fn user_home() -> Option<PathBuf> {
    let var = if cfg!(windows) { "USERPROFILE" } else { "HOME" };
    std::env::var_os(var)
        .filter(|h| !h.is_empty())
        .map(PathBuf::from)
}

/// `fs::canonicalize`, in the spelling users and tools know on Windows:
/// `C:\..` and `\\server\share\..` rather than `\\?\C:\..` and
/// `\\?\UNC\server\share\..`.
pub fn real_path(p: impl AsRef<Path>) -> std::io::Result<PathBuf> {
    let real = std::fs::canonicalize(p)?;
    if cfg!(windows) {
        if let Some(plain) = real.to_str().and_then(unverbatim) {
            return Ok(PathBuf::from(plain));
        }
    }
    Ok(real)
}

/// A Windows verbatim path without its `\\?\` prefix, when it has an
/// ordinary spelling.
fn unverbatim(s: &str) -> Option<String> {
    if let Some(unc) = s.strip_prefix(r"\\?\UNC\") {
        return Some(format!(r"\\{unc}"));
    }
    let rest = s.strip_prefix(r"\\?\")?;
    let drive = rest.as_bytes();
    (drive.len() >= 3 && drive[0].is_ascii_alphabetic() && &drive[1..3] == b":\\")
        .then(|| rest.to_owned())
}

/// The running executable, through symlinks ([`real_path`]).
#[must_use]
pub fn current_exe() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    Some(real_path(&exe).unwrap_or(exe))
}

/// The rok home an executable is installed in: `<home>/bin/<exe>` (a
/// proxy: `<home>/toolchains/` exists) or `<home>/toolchains/<name>/bin/<exe>`.
#[must_use]
pub fn home_of(exe: &Path) -> Option<PathBuf> {
    let exe = real_path(exe).unwrap_or_else(|_| exe.to_path_buf());
    let up = exe.parent()?.parent()?;
    if up.join("toolchains").is_dir() {
        return Some(up.to_path_buf());
    }
    let tcs = up.parent()?;
    (tcs.file_name()? == "toolchains").then(|| tcs.parent().map(Path::to_path_buf))?
}

/// The entry of `cmd` in a usage text: its lines (`  cmd ...`, or
/// `  a | cmd | b ...`) and the more indented lines after each.
#[must_use]
pub fn command_help(usage: &str, cmd: &str) -> Option<String> {
    let indent = |l: &str| l.len() - l.trim_start().len();
    let mut out = String::new();
    let mut entry: Option<usize> = None;
    for line in usage.lines() {
        let head = line.trim_start();
        let names = head
            .split("  ")
            .next()
            .unwrap_or("")
            .split(|c: char| c == '|' || c.is_whitespace())
            .take_while(|w| !w.starts_with(['<', '[', '-']))
            .any(|w| w == cmd);
        let starts = indent(line) > 0 && names;
        let continues = entry.is_some_and(|e| indent(line) > e) && !head.is_empty();
        if starts && entry.is_none_or(|e| indent(line) <= e) {
            entry = Some(indent(line));
        } else if !continues {
            entry = None;
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    (!out.is_empty()).then_some(out)
}

#[cfg(test)]
mod tests {
    #[test]
    fn verbatim_windows_paths_get_their_plain_spelling() {
        let u = super::unverbatim;
        assert_eq!(
            u(r"\\?\C:\Users\é\a.rok").as_deref(),
            Some(r"C:\Users\é\a.rok")
        );
        assert_eq!(u(r"\\?\UNC\srv\share\x").as_deref(), Some(r"\\srv\share\x"));
        assert_eq!(u(r"\\?\Volume{1}\x"), None);
        assert_eq!(u(r"C:\x"), None);
    }

    #[test]
    fn command_help_takes_the_entry_and_its_continuations() {
        let usage = "usage: x\n\ncmds:\n  add <n>      add\n               more\n  add <n> --p  \
                     path\n  rm <n>       rm\n  a | b [x]    ab\n";
        assert_eq!(
            super::command_help(usage, "add").unwrap(),
            "  add <n>      add\n               more\n  add <n> --p  path\n"
        );
        assert_eq!(
            super::command_help(usage, "rm").unwrap(),
            "  rm <n>       rm\n"
        );
        assert_eq!(
            super::command_help(usage, "b").unwrap(),
            "  a | b [x]    ab\n"
        );
        assert!(super::command_help(usage, "x").is_none());
        assert!(super::command_help(usage, "n").is_none());
    }
}

//! Definitions shared by the compiler and the `rok` tool.

pub mod def;
pub mod hash;
pub mod lint;

use std::path::PathBuf;

pub use def::{DefId, DefInfo, DefKind, DefTable, Visibility};

/// The install root: `$ROK_HOME`, else the parent of the running
/// executable's directory (`<home>/bin/rok`).
#[must_use]
pub fn rok_home() -> Option<PathBuf> {
    std::env::var_os("ROK_HOME")
        .filter(|h| !h.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            let exe = std::env::current_exe().ok()?;
            Some(exe.parent()?.parent()?.to_path_buf())
        })
}

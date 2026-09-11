//! Incremental builds (902.16) at package granularity: a build is skipped
//! when its output is there and nothing it was made from changed. The
//! record (`.<out>.fp` next to the output) holds the key, the output's
//! size and mtime (a replaced output rebuilds) and the build's rendered
//! warnings, which a skipped build prints again.
//!
//! The key covers the compiler, the report style, the build words
//! (options, paths), every source file the build can read and the
//! prebuilt archives it links. One key per package: any change rebuilds
//! the package whole.

use std::path::{Path, PathBuf};

use rokc_core::hash::{FNV_OFFSET, fnv_add};

use crate::package::source_files;

/// `size-mtime` of a file, or `-` when it is missing.
fn identity(p: &Path) -> String {
    std::fs::metadata(p).map_or_else(
        |_| "-".to_owned(),
        |m| {
            let t = m
                .modified()
                .ok()
                .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                .map_or(0, |d| d.as_nanos());
            format!("{}-{t}", m.len())
        },
    )
}

/// A build's fingerprint and where it is kept.
pub struct Fingerprint {
    key: String,
    file: PathBuf,
    out: PathBuf,
    /// More files that must exist (a library's RHIR).
    also: Vec<PathBuf>,
}

impl Fingerprint {
    /// `words`: what the build is (options, paths); `inputs`: files it
    /// reads (a directory: its source files); `stamped`: big files known
    /// by size and mtime (the runtime, prebuilt archives).
    #[must_use]
    pub fn new(
        out: &Path,
        also: Vec<PathBuf>,
        words: &[String],
        inputs: &[PathBuf],
        stamped: &[PathBuf],
    ) -> Self {
        let mut h = FNV_OFFSET;
        let own = [
            rokc_driver::rhir::producer(),
            rokc_diagnostic::report_style().to_string(),
        ];
        for w in own.iter().chain(words) {
            h = fnv_add(fnv_add(h, w.as_bytes()), b"\0");
        }
        for p in stamped {
            h = fnv_add(h, format!("{}\0{}\0", p.display(), identity(p)).as_bytes());
        }
        let mut files = Vec::new();
        for i in inputs {
            if i.is_file() {
                files.push(i.clone());
            } else {
                files.extend(source_files(i));
            }
        }
        files.sort();
        files.dedup();
        for f in files {
            h = fnv_add(h, f.display().to_string().as_bytes());
            h = fnv_add(h, &std::fs::read(&f).unwrap_or_default());
        }
        let name = out
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        Self {
            key: format!("{h:016x}"),
            file: out.with_file_name(format!(".{name}.fp")),
            out: out.to_path_buf(),
            also,
        }
    }

    fn head(&self) -> String {
        format!("{}\n{}\n", self.key, identity(&self.out))
    }

    /// The recorded warnings when the output is up to date.
    #[must_use]
    pub fn fresh(&self) -> Option<String> {
        if !self.out.is_file() || !self.also.iter().all(|p| p.is_file()) {
            return None;
        }
        let record = std::fs::read_to_string(&self.file).ok()?;
        record.strip_prefix(&self.head()).map(str::to_owned)
    }

    /// Before building: a failed build leaves no record.
    pub fn clear(&self) {
        let _ = std::fs::remove_file(&self.file);
    }

    /// After a successful build that printed `warnings`.
    pub fn save(&self, warnings: &str) {
        let _ = std::fs::write(&self.file, self.head() + warnings);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_until_an_input_or_the_output_changes() {
        let dir = std::env::temp_dir().join(format!("rokc-fresh-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("target")).unwrap();
        let src = dir.join("main.rok");
        let out = dir.join("target/app");
        std::fs::write(&src, "fn main() {}").unwrap();
        // `target/` is not an input.
        std::fs::write(dir.join("target/skip.rok"), "x").unwrap();
        let fp = |w: &str| Fingerprint::new(&out, vec![], &[w.into()], &[dir.clone()], &[]);
        assert!(fp("a").fresh().is_none());
        std::fs::write(&out, "exe").unwrap();
        fp("a").save("warning: w\n");
        assert_eq!(fp("a").fresh().as_deref(), Some("warning: w\n"));
        assert!(fp("b").fresh().is_none());
        std::fs::write(dir.join("target/skip.rok"), "y").unwrap();
        assert!(fp("a").fresh().is_some());
        std::fs::write(&src, "fn main() { }").unwrap();
        assert!(fp("a").fresh().is_none());
        fp("a").save("");
        std::fs::write(&out, "other exe").unwrap();
        assert!(fp("a").fresh().is_none());
        fp("a").save("");
        fp("a").clear();
        assert!(fp("a").fresh().is_none());
        let _ = std::fs::remove_dir_all(&dir);
    }
}

//! Incremental builds (902.16) at package granularity: a build is skipped
//! when its output is there and nothing it was made from changed. The
//! record (`.<out>.fp` next to the output) holds the key, the output's
//! stamp (`file_stamp`: a replaced output rebuilds) and the build's
//! rendered warnings, which a skipped build prints again.
//!
//! The key covers the compiler, the report style, the build words
//! (options, paths), every source file the build can read and the
//! prebuilt archives it links. Files the build read beyond those (a
//! `#[path]` module outside the package, an `include_str!` /
//! `include_bytes!` file) are listed in the record with their content
//! hashes. One key per package: any change rebuilds the package whole.

use std::path::{Path, PathBuf};

use rokc_core::file_stamp;
use rokc_core::hash::{FNV_OFFSET, fnv_add};

use crate::package::source_files;

/// A build's fingerprint and where it is kept.
pub struct Fingerprint {
    key: String,
    file: PathBuf,
    out: PathBuf,
    /// More files that must exist (a library's ROKHIR).
    also: Vec<PathBuf>,
    /// The inputs the key covers, canonical.
    covered: Vec<PathBuf>,
}

fn content_hash(p: &Path) -> String {
    format!(
        "{:016x}",
        fnv_add(FNV_OFFSET, &std::fs::read(p).unwrap_or_default())
    )
}

impl Fingerprint {
    /// `words`: what the build is (options, paths); `inputs`: files it
    /// reads (a directory: its source files); `stamped`: big files known
    /// by `file_stamp` (the runtime, prebuilt archives).
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
            rokc_driver::rokhir::producer(),
            rokc_diagnostic::report_style().to_string(),
        ];
        for w in own.iter().chain(words) {
            h = fnv_add(fnv_add(h, w.as_bytes()), b"\0");
        }
        for p in stamped {
            h = fnv_add(
                h,
                format!("{}\0{}\0", p.display(), file_stamp(p)).as_bytes(),
            );
        }
        let mut files = Vec::new();
        let covered: Vec<PathBuf> = inputs
            .iter()
            .filter_map(|i| i.canonicalize().ok())
            .collect();
        // Canonical: `run s.rok` in two directories is two builds (the
        // record lists the files read beside it by full path).
        for i in &covered {
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
            covered,
        }
    }

    /// Keep the record in `file` instead of `.<out>.fp` beside the output.
    #[must_use]
    pub fn kept_in(mut self, file: PathBuf) -> Self {
        self.file = file;
        self
    }

    /// The hash of everything the build is made from.
    #[must_use]
    pub fn key(&self) -> &str {
        &self.key
    }

    /// The same build into `out` instead (its record beside it), with
    /// `also` to exist.
    #[must_use]
    pub fn moved_to(self, out: &Path, also: Vec<PathBuf>) -> Self {
        let name = out.file_name().unwrap_or_default().to_string_lossy();
        Self {
            file: out.with_file_name(format!(".{name}.fp")),
            out: out.to_path_buf(),
            also,
            ..self
        }
    }

    fn head(&self) -> String {
        format!("{}\n{}\n", self.key, file_stamp(&self.out))
    }

    /// The recorded warnings when the output is up to date.
    #[must_use]
    pub fn fresh(&self) -> Option<String> {
        if !self.out.is_file() || !self.also.iter().all(|p| p.is_file()) {
            return None;
        }
        let record = std::fs::read_to_string(&self.file).ok()?;
        let rest = record.strip_prefix(&self.head())?;
        let (n, mut rest) = rest.split_once('\n')?;
        for _ in 0..n.parse::<usize>().ok()? {
            let (line, tail) = rest.split_once('\n')?;
            let (hash, path) = line.split_once(' ')?;
            if content_hash(Path::new(path)) != hash {
                return None;
            }
            rest = tail;
        }
        Some(rest.to_owned())
    }

    /// Before building: a failed build leaves no record.
    pub fn clear(&self) {
        let _ = std::fs::remove_file(&self.file);
    }

    /// After a successful build that read `read` and printed `warnings`.
    pub fn save(&self, read: &[PathBuf], warnings: &str) {
        let mut extra: Vec<PathBuf> = read
            .iter()
            .filter_map(|p| p.canonicalize().ok())
            .filter(|p| {
                !self.covered.iter().any(|c| p.starts_with(c))
                    || !p.extension().is_some_and(|x| x == "rok" || x == "rokon")
            })
            .collect();
        extra.sort();
        extra.dedup();
        let mut record = self.head() + &format!("{}\n", extra.len());
        for p in &extra {
            record += &format!("{} {}\n", content_hash(p), p.display());
        }
        let _ = std::fs::write(&self.file, record + warnings);
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
        fp("a").save(&[], "warning: w\n");
        assert_eq!(fp("a").fresh().as_deref(), Some("warning: w\n"));
        assert!(fp("b").fresh().is_none());
        std::fs::write(dir.join("target/skip.rok"), "y").unwrap();
        assert!(fp("a").fresh().is_some());
        std::fs::write(&src, "fn main() { }").unwrap();
        assert!(fp("a").fresh().is_none());
        fp("a").save(&[], "");
        std::fs::write(&out, "other exe").unwrap();
        assert!(fp("a").fresh().is_none());
        fp("a").save(&[], "");
        fp("a").clear();
        assert!(fp("a").fresh().is_none());
        // A file read outside the inputs is checked by content.
        let outside = std::env::temp_dir().join(format!("rokc-fresh-{}.rok", std::process::id()));
        std::fs::write(&outside, "a").unwrap();
        fp("a").save(&[src, outside.clone()], "");
        assert!(fp("a").fresh().is_some());
        std::fs::write(&outside, "b").unwrap();
        assert!(fp("a").fresh().is_none());
        let _ = std::fs::remove_file(&outside);
        let _ = std::fs::remove_dir_all(&dir);
    }
}

//! Incremental build (902.16), at package granularity: `build` / `run`
//! skip the whole compile when the output is there and nothing it was
//! made from changed. The key (`.<out>.fp` next to the output) hashes
//! the compiler, the build words (options, paths), every `.rok` the
//! build can read (the package, the library roots, source
//! dependencies) and the prebuilt dependencies' files; the record also
//! holds the output's size and mtime, so a replaced output rebuilds.
//!
//! ponytail: one key per package, so any change recompiles the package
//! whole; per-file parse / per-specialization / per-object reuse
//! (902.16 steps 1–3) needs a split codegen unit first. A build with
//! warnings is not recorded (no replay of its diagnostics), so it
//! always rebuilds.

use std::path::{Path, PathBuf};

fn fnv(h: u64, bytes: &[u8]) -> u64 {
    bytes
        .iter()
        .fold(h, |h, &b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
}

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

/// `path` if a file, else every `.rok` under it (not `target/`, not
/// dot directories).
fn sources(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_file() {
        out.push(path.to_path_buf());
        return;
    }
    let Ok(rd) = std::fs::read_dir(path) else {
        return;
    };
    for e in rd.flatten() {
        let p = e.path();
        let name = e.file_name().to_string_lossy().into_owned();
        if p.is_dir() {
            if name != "target" && !name.starts_with('.') {
                sources(&p, out);
            }
        } else if p.extension().is_some_and(|x| x == "rok") {
            out.push(p);
        }
    }
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
    /// `words`: what the build is (options, paths); `inputs`: files
    /// whose contents it reads (directories: their `.rok` files);
    /// `stamped`: big files known by size and mtime (the compiler, the
    /// runtime, prebuilt archives).
    pub fn new(
        out: &Path,
        also: Vec<PathBuf>,
        words: &[String],
        inputs: &[PathBuf],
        stamped: &[PathBuf],
    ) -> Self {
        let mut h = 0xcbf2_9ce4_8422_2325;
        for w in words {
            h = fnv(fnv(h, w.as_bytes()), b"\0");
        }
        for p in stamped {
            h = fnv(h, format!("{}\0{}\0", p.display(), identity(p)).as_bytes());
        }
        let mut files = Vec::new();
        for i in inputs {
            sources(i, &mut files);
        }
        files.sort();
        files.dedup();
        for f in files {
            h = fnv(h, f.display().to_string().as_bytes());
            h = fnv(h, &std::fs::read(&f).unwrap_or_default());
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

    fn record(&self) -> String {
        format!("{}\n{}\n", self.key, identity(&self.out))
    }

    /// The output is there and was built from the same inputs.
    pub fn fresh(&self) -> bool {
        self.out.is_file()
            && self.also.iter().all(|p| p.is_file())
            && std::fs::read_to_string(&self.file).is_ok_and(|r| r == self.record())
    }

    /// Before building: a failed build leaves no record.
    pub fn clear(&self) {
        let _ = std::fs::remove_file(&self.file);
    }

    /// After a successful build.
    pub fn save(&self) {
        let _ = std::fs::write(&self.file, self.record());
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
        assert!(!fp("a").fresh());
        std::fs::write(&out, "exe").unwrap();
        fp("a").save();
        assert!(fp("a").fresh());
        assert!(!fp("b").fresh());
        std::fs::write(dir.join("target/skip.rok"), "y").unwrap();
        assert!(fp("a").fresh());
        std::fs::write(&src, "fn main() { }").unwrap();
        assert!(!fp("a").fresh());
        fp("a").save();
        std::fs::write(&out, "other exe").unwrap();
        assert!(!fp("a").fresh());
        fp("a").save();
        fp("a").clear();
        assert!(!fp("a").fresh());
        let _ = std::fs::remove_dir_all(&dir);
    }
}

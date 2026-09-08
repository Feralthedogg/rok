//! The global git cache, shared by every project and environment:
//!
//! ```text
//! $ROK_HOME/cache/git/db/<repo>-<hash of url>/   bare clone, one per url
//! $ROK_HOME/cache/git/checkouts/<commit>/        a commit's files
//! ```
//!
//! Everything goes through the `git` command line.

// `^{commit}` / `^{tree}` are git revision syntax, not format arguments.
#![allow(clippy::literal_string_with_formatting_args)]

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::manifest::GitRef;

pub struct Cache {
    root: PathBuf,
}

/// FNV-1a: a stable short name for a url (std's hasher may change).
pub fn fnv(s: &str) -> u64 {
    s.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3)
    })
}

fn git(dir: &Path, args: &[&str], index: Option<&Path>) -> Result<String, String> {
    let mut cmd = Command::new("git");
    cmd.arg("--git-dir")
        .arg(dir)
        .args(args)
        .env_remove("GIT_DIR")
        .env_remove("GIT_WORK_TREE")
        .env_remove("GIT_INDEX_FILE")
        .env("GIT_TERMINAL_PROMPT", "0");
    if let Some(i) = index {
        cmd.env("GIT_INDEX_FILE", i);
    }
    let out = cmd
        .output()
        .map_err(|e| format!("cannot run `git` (is it installed?): {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "`git {}` failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_owned())
}

impl Cache {
    pub fn new(home: &Path) -> Self {
        Self {
            root: home.join("cache/git"),
        }
    }

    fn db(&self, url: &str) -> PathBuf {
        let base = url
            .trim_end_matches('/')
            .rsplit(['/', ':', '\\'])
            .next()
            .unwrap_or("repo")
            .trim_end_matches(".git");
        let base: String = base
            .chars()
            .filter(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.'))
            .collect();
        self.root
            .join("db")
            .join(format!("{base}-{:016x}", fnv(url)))
    }

    /// Bring the bare clone of `url` up to date (branches, tags, HEAD).
    pub fn fetch(&self, url: &str) -> Result<(), String> {
        let db = self.db(url);
        if !db.join("HEAD").is_file() {
            std::fs::create_dir_all(&db).map_err(|e| format!("{}: {e}", db.display()))?;
            git(&db, &["init", "--quiet", "--bare"], None)?;
        }
        git(
            &db,
            &[
                "fetch",
                "--quiet",
                "--force",
                url,
                "+refs/heads/*:refs/heads/*",
                "+refs/tags/*:refs/tags/*",
                "+HEAD:refs/rok/HEAD",
            ],
            None,
        )
        .map(drop)
        .map_err(|e| format!("cannot fetch {url}: {e}"))
    }

    /// The commit `reference` names in the cached clone of `url`.
    pub fn resolve(&self, url: &str, reference: &GitRef) -> Result<String, String> {
        let spec = match reference {
            GitRef::Default => "refs/rok/HEAD".to_owned(),
            GitRef::Branch(b) => format!("refs/heads/{b}"),
            GitRef::Tag(t) => format!("refs/tags/{t}"),
            GitRef::Rev(r) => r.clone(),
        };
        let db = self.db(url);
        if !db.join("HEAD").is_file() {
            return Err(format!("{url} is not in the cache"));
        }
        git(
            &db,
            &["rev-parse", "--verify", "--quiet", &(spec + "^{commit}")],
            None,
        )
        .map_err(|_| {
            let what = reference.pair().map_or_else(
                || "its default branch".to_owned(),
                |(k, v)| format!("{k} `{v}`"),
            );
            format!("{url} has no {what}")
        })
    }

    pub fn has_commit(&self, url: &str, commit: &str) -> bool {
        let db = self.db(url);
        db.join("HEAD").is_file()
            && git(
                &db,
                &["cat-file", "-e", &(commit.to_owned() + "^{commit}")],
                None,
            )
            .is_ok()
    }

    /// The files of `commit` at `checkouts/<commit>/` (extracted once,
    /// and again if they were changed), and the commit's tree hash.
    pub fn checkout(&self, url: &str, commit: &str) -> Result<(PathBuf, String), String> {
        let db = self.db(url);
        let tree = git(&db, &["rev-parse", &(commit.to_owned() + "^{tree}")], None)?;
        let dir = self.root.join("checkouts").join(commit);
        if dir.is_dir() {
            if self.disk_tree(&db, &dir)? == tree {
                return Ok((dir, tree));
            }
            eprintln!(
                "rok: warning: {} was modified; checking it out again",
                dir.display()
            );
            std::fs::remove_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        }
        let tmp = self
            .root
            .join("checkouts")
            .join(format!(".tmp-{commit}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        std::fs::create_dir_all(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?;
        let index = tmp.with_extension("index");
        git(&db, &["read-tree", commit], Some(&index))?;
        let work = format!("--work-tree={}", tmp.display());
        git(
            &db,
            &[&work, "checkout-index", "--all", "--force"],
            Some(&index),
        )?;
        let _ = std::fs::remove_file(&index);
        // Another process may have won the race: theirs is as good.
        if std::fs::rename(&tmp, &dir).is_err() {
            let _ = std::fs::remove_dir_all(&tmp);
        }
        Ok((dir, tree))
    }

    /// The git tree hash of what is on disk in `dir`.
    fn disk_tree(&self, db: &Path, dir: &Path) -> Result<String, String> {
        let index = self
            .root
            .join(format!(".verify-{}.index", std::process::id()));
        let _ = std::fs::remove_file(&index);
        let work = format!("--work-tree={}", dir.display());
        git(db, &[&work, "add", "--all", "--force", "."], Some(&index))?;
        let tree = git(db, &["write-tree"], Some(&index));
        let _ = std::fs::remove_file(&index);
        tree
    }
}

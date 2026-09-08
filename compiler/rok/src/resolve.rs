//! Dependency resolution: from a manifest's `[deps]` (and `[dev-deps]`)
//! through every dependency's own `Rok.toml`, to one package per name.
//! Git packages come from the lock unless `update` names them.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::git::Cache;
use crate::lock::{Lock, Locked};
use crate::manifest::{self, Dep, Manifest, Source};

#[derive(Default)]
pub struct Options {
    pub offline: bool,
    /// `--locked`: fail instead of changing `Rok.lock`.
    pub locked: bool,
    /// `rok update [names]`: re-resolve these git packages (empty: all).
    pub update: Option<Vec<String>>,
    pub quiet: bool,
}

/// What a command works on: a project (a directory with `Rok.toml`), a
/// named environment, a script's `//! ```toml` block, or nothing.
pub struct Context {
    pub manifest: Manifest,
    /// Path dependencies are relative to this directory.
    pub base: PathBuf,
    /// `None`: nothing to lock (no dependencies).
    pub lock_path: Option<PathBuf>,
}

pub struct Resolved {
    pub name: String,
    /// The package's `lib.rok`.
    pub root: PathBuf,
    /// Reached only through the root's `[dev-deps]`.
    pub dev: bool,
}

/// Where a package came from: two requirements of one name must agree.
#[derive(PartialEq, Eq)]
enum Id {
    Path(PathBuf),
    Git { url: String, commit: String },
}

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Path(p) => write!(f, "path {}", p.display()),
            Self::Git { url, commit } => {
                write!(f, "git {url} at {}", &commit[..commit.len().min(12)])
            }
        }
    }
}

struct Resolver<'a> {
    cache: Cache,
    opts: &'a Options,
    old: Lock,
    new: Lock,
    fetched: Vec<String>,
    seen: HashMap<String, (Id, String)>,
    out: Vec<Resolved>,
}

pub fn resolve(home: &Path, ctx: &Context, opts: &Options) -> Result<Vec<Resolved>, String> {
    let old = match &ctx.lock_path {
        Some(p) => Lock::read(p)?.unwrap_or_default(),
        None => Lock::default(),
    };
    if opts.locked && ctx.lock_path.as_ref().is_some_and(|p| !p.is_file()) {
        let any_git = ctx
            .manifest
            .deps
            .iter()
            .chain(&ctx.manifest.dev_deps)
            .any(|d| matches!(d.source, Source::Git { .. }));
        if any_git {
            return Err("there is no Rok.lock, and --locked forbids writing one".to_owned());
        }
    }
    let mut r = Resolver {
        cache: Cache::new(home),
        opts,
        old,
        new: Lock::default(),
        fetched: Vec::new(),
        seen: HashMap::new(),
        out: Vec::new(),
    };
    // Normal dependencies first: whatever they reach is not dev-only.
    r.walk(&ctx.manifest.deps, &ctx.base, "the root package", false)?;
    r.walk(&ctx.manifest.dev_deps, &ctx.base, "the root package", true)?;
    if let Some(path) = &ctx.lock_path {
        let text = r.new.to_text();
        let old_text = std::fs::read_to_string(path).ok();
        let empty = r.new.packages.is_empty();
        if old_text.as_deref() != Some(text.as_str()) && !(empty && old_text.is_none()) {
            if opts.locked {
                return Err(format!(
                    "{} is out of date and --locked forbids changing it (run `rok update`)",
                    path.display()
                ));
            }
            std::fs::write(path, text)
                .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
        }
    }
    Ok(r.out)
}

impl Resolver<'_> {
    fn walk(&mut self, deps: &[Dep], base: &Path, by: &str, dev: bool) -> Result<(), String> {
        let mut queue: Vec<(Dep, PathBuf, String)> = deps
            .iter()
            .map(|d| (d.clone(), base.to_path_buf(), by.to_owned()))
            .collect();
        let mut i = 0;
        while i < queue.len() {
            let (dep, base, by) = queue[i].clone();
            i += 1;
            let (dir, id) = self.locate(&dep, &base)?;
            if let Some((prev, prev_by)) = self.seen.get(&dep.name) {
                if *prev == id {
                    continue;
                }
                return Err(format!(
                    "conflicting requirements for package `{}`:\n  {prev} (required by {prev_by})\n  \
                     {id} (required by {by})\none build has one version of a package",
                    dep.name
                ));
            }
            let root = dir.join("lib.rok");
            if !root.is_file() {
                return Err(format!(
                    "dependency `{}` ({id}) is not a library package: no lib.rok in {}",
                    dep.name,
                    dir.display()
                ));
            }
            if let Some(m) = manifest::find(&dir) {
                let m = manifest::load(&m)?;
                let me = format!("`{}`", dep.name);
                queue.extend(m.deps.into_iter().map(|d| (d, dir.clone(), me.clone())));
            }
            self.seen.insert(dep.name.clone(), (id, by));
            self.out.push(Resolved {
                name: dep.name,
                root,
                dev,
            });
        }
        Ok(())
    }

    /// The package directory of `dep`, and its identity.
    fn locate(&mut self, dep: &Dep, base: &Path) -> Result<(PathBuf, Id), String> {
        let (url, reference) = match &dep.source {
            Source::Path(p) => {
                let dir = base.join(p);
                let dir = std::fs::canonicalize(&dir).map_err(|e| {
                    format!("dependency `{}`: path {}: {e}", dep.name, dir.display())
                })?;
                return Ok((dir.clone(), Id::Path(dir)));
            }
            Source::Git { url, reference } => (url, reference),
        };
        let updating = self
            .opts
            .update
            .as_ref()
            .is_some_and(|names| names.is_empty() || names.contains(&dep.name));
        let pinned = self
            .old
            .find(&dep.name)
            .filter(|l| !updating && l.url == *url && l.reference == *reference)
            .cloned();
        let commit = if let Some(l) = &pinned {
            if !self.cache.has_commit(url, &l.commit) {
                self.fetch(url, &dep.name)?;
                if !self.cache.has_commit(url, &l.commit) {
                    return Err(format!(
                        "`{}`: locked commit {} is not in {url} (run `rok update {}`)",
                        dep.name, l.commit, dep.name
                    ));
                }
            }
            l.commit.clone()
        } else {
            if self.opts.locked && !updating {
                return Err(format!(
                    "`{}` is not in Rok.lock (or its source changed), and --locked forbids \
                     changing it",
                    dep.name
                ));
            }
            if self.opts.offline {
                self.cache
                    .resolve(url, reference)
                    .map_err(|e| format!("`{}`: {e} (--offline: nothing is fetched)", dep.name))?
            } else {
                self.fetch(url, &dep.name)?;
                self.cache.resolve(url, reference)?
            }
        };
        let (dir, tree) = self.cache.checkout(url, &commit)?;
        if let Some(l) = &pinned {
            if l.tree != tree {
                return Err(format!(
                    "`{}`: commit {} has tree {tree}, but Rok.lock says {}",
                    dep.name, l.commit, l.tree
                ));
            }
        }
        if !self.new.packages.iter().any(|p| p.name == dep.name) {
            self.new.packages.push(Locked {
                name: dep.name.clone(),
                url: url.clone(),
                reference: reference.clone(),
                commit: commit.clone(),
                tree,
            });
        }
        Ok((
            dir,
            Id::Git {
                url: url.clone(),
                commit,
            },
        ))
    }

    fn fetch(&mut self, url: &str, name: &str) -> Result<(), String> {
        if self.fetched.iter().any(|u| u == url) {
            return Ok(());
        }
        if self.opts.offline {
            return Err(format!(
                "`{name}` needs a fetch of {url}, but --offline is set (it is not in the cache)"
            ));
        }
        if !self.opts.quiet {
            eprintln!("    Fetching {url}");
        }
        self.cache.fetch(url)?;
        self.fetched.push(url.to_owned());
        Ok(())
    }
}

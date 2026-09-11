//! Dependency resolution: from a manifest's `deps` (and `dev_deps`)
//! through every dependency's own `rok.rokon`, to one package per name,
//! each after its own dependencies (the order rokc builds them in). Git
//! packages and stones come from the lock unless `update` names them.
//!
//! A stone requirement takes the highest non-yanked version in its index
//! that matches (the locked one while it still matches); its dependencies
//! are the index entry's. One version per name: a later requirement the
//! chosen version does not meet is a conflict.
// Greedy, no backtracking: a root requirement both sides accept
// (`rok add x@=1.2.0`) settles a conflict.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::git::Cache;
use crate::lock::{Lock, Locked};
use crate::manifest::{self, Dep, Manifest, Source};
use crate::registry;
use crate::semver::{Req, Version};

#[derive(Default)]
pub struct Options {
    pub offline: bool,
    /// `--locked`: fail instead of changing `rok.lock`.
    pub locked: bool,
    /// `rok update [names]`: re-resolve these git packages and stones
    /// (empty: all).
    pub update: Option<Vec<String>>,
    pub quiet: bool,
}

/// What a command works on: a project (a directory with `rok.rokon`), a
/// named environment, a script's `//! ```rokon` block, or nothing.
pub struct Context {
    pub manifest: Manifest,
    /// Path dependencies are relative to this directory.
    pub base: PathBuf,
    /// `None`: nothing to lock (no dependencies).
    pub lock_path: Option<PathBuf>,
}

#[derive(Clone)]
pub struct Resolved {
    pub name: String,
    /// The package's `lib.rok`.
    pub root: PathBuf,
    /// Reached only through the root's `dev_deps`.
    pub dev: bool,
    /// Its own dependencies' names.
    pub deps: Vec<String>,
}

/// Where a package came from: two requirements of one name must agree.
#[derive(PartialEq, Eq)]
enum Id {
    Path(PathBuf),
    Git { url: String, commit: String },
    Stone { registry: String, vers: Version },
}

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Path(p) => write!(f, "path {}", p.display()),
            Self::Git { url, commit } => {
                write!(f, "git {url} at {}", &commit[..commit.len().min(12)])
            }
            Self::Stone { registry, vers } => write!(f, "stone {vers} from {registry}"),
        }
    }
}

struct Resolver<'a> {
    cache: Cache,
    index: Cache,
    /// For `Dep::version(..)` without `registry`.
    registry: String,
    opts: &'a Options,
    old: Lock,
    new: Lock,
    fetched: Vec<String>,
    /// What each name resolved to, who required it, and how (a stone's
    /// requirement).
    seen: HashMap<String, (Id, String, String)>,
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
            .any(|d| !matches!(d.source, Source::Path(_)));
        if any_git {
            return Err("there is no rok.lock, and --locked forbids writing one".to_owned());
        }
    }
    let mut r = Resolver {
        cache: Cache::new(home),
        index: Cache::index(home),
        registry: registry::default_url(home)?,
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
    Ok(order(r.out))
}

/// Each package after its own dependencies.
fn order(deps: Vec<Resolved>) -> Vec<Resolved> {
    fn visit(i: usize, all: &[Resolved], state: &mut [u8], out: &mut Vec<usize>) {
        // 0 new, 1 on the stack (a cycle is cut there), 2 placed.
        if state[i] != 0 {
            return;
        }
        state[i] = 1;
        for n in &all[i].deps {
            if let Some(j) = all.iter().position(|x| x.name == *n) {
                visit(j, all, state, out);
            }
        }
        state[i] = 2;
        out.push(i);
    }
    let mut state = vec![0; deps.len()];
    let mut idx = Vec::new();
    for i in 0..deps.len() {
        visit(i, &deps, &mut state, &mut idx);
    }
    let mut slots: Vec<Option<Resolved>> = deps.into_iter().map(Some).collect();
    idx.into_iter().filter_map(|i| slots[i].take()).collect()
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
            if let (
                Some((Id::Stone { registry, vers }, prev_by, prev_req)),
                Source::Registry { req, .. },
            ) = (self.seen.get(&dep.name), &dep.source)
            {
                let url = self.registry_of(&dep.source);
                if *registry == url && Req::parse(req)?.matches(vers) {
                    continue;
                }
                return Err(format!(
                    "conflicting requirements for stone `{}`:\n  `{prev_req}` (required by \
                     {prev_by}) chose {vers} from {registry}\n  `{req}` (required by {by}) from \
                     {url}\none build has one version of a stone; require a version both accept \
                     in the root package",
                    dep.name
                ));
            }
            let (dir, id, stone_deps) = self.locate(&dep, &base)?;
            if let Some((prev, prev_by, _)) = self.seen.get(&dep.name) {
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
            let me = format!("`{}`", dep.name);
            let next = match stone_deps {
                Some(d) => d,
                None => match manifest::find(&dir) {
                    Some(m) => manifest::load(&m)?.deps,
                    None => Vec::new(),
                },
            };
            let deps = next.iter().map(|d| d.name.clone()).collect();
            queue.extend(next.into_iter().map(|d| (d, dir.clone(), me.clone())));
            let req = match &dep.source {
                Source::Registry { req, .. } => req.clone(),
                _ => String::new(),
            };
            self.seen.insert(dep.name.clone(), (id, by, req));
            self.out.push(Resolved {
                name: dep.name,
                root,
                dev,
                deps,
            });
        }
        Ok(())
    }

    fn registry_of(&self, source: &Source) -> String {
        match source {
            Source::Registry {
                registry: Some(r), ..
            } => r.clone(),
            _ => self.registry.clone(),
        }
    }

    fn updating(&self, name: &str) -> bool {
        self.opts
            .update
            .as_ref()
            .is_some_and(|names| names.is_empty() || names.iter().any(|n| n == name))
    }

    /// The package directory of `dep`, its identity, and for a stone its
    /// dependencies (the index's).
    fn locate(
        &mut self,
        dep: &Dep,
        base: &Path,
    ) -> Result<(PathBuf, Id, Option<Vec<Dep>>), String> {
        let (url, reference) = match &dep.source {
            Source::Path(p) => {
                let dir = base.join(p);
                let dir = std::fs::canonicalize(&dir).map_err(|e| {
                    format!("dependency `{}`: path {}: {e}", dep.name, dir.display())
                })?;
                return Ok((dir.clone(), Id::Path(dir), None));
            }
            Source::Git { url, reference } => (url, reference),
            Source::Registry { req, .. } => {
                let url = self.registry_of(&dep.source);
                return self.locate_stone(&dep.name, req, &url);
            }
        };
        let updating = self.updating(&dep.name);
        let pinned = self
            .old
            .find(&dep.name)
            .filter(|l| !updating && l.vers.is_none() && l.url == *url && l.reference == *reference)
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
                    "`{}` is not in rok.lock (or its source changed), and --locked forbids \
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
                    "`{}`: commit {} has tree {tree}, but rok.lock says {}",
                    dep.name, l.commit, l.tree
                ));
            }
        }
        if !self.new.packages.iter().any(|p| p.name == dep.name) {
            self.new.packages.push(Locked {
                name: dep.name.clone(),
                vers: None,
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
            None,
        ))
    }

    /// Stone `name` from index `url`: the version `req` picks, checked
    /// out and verified against the entry's `cksum`.
    fn locate_stone(
        &mut self,
        name: &str,
        req: &str,
        url: &str,
    ) -> Result<(PathBuf, Id, Option<Vec<Dep>>), String> {
        let parsed = Req::parse(req).map_err(|e| format!("stone `{name}`: {e}"))?;
        let updating = self.updating(name);
        let pinned = self
            .old
            .find(name)
            .filter(|l| !updating && l.url == url)
            .and_then(|l| Some((l.clone(), Version::parse(l.vers.as_deref()?).ok()?)))
            .filter(|(_, v)| parsed.matches(v));
        if pinned.is_none() && self.opts.locked && !updating {
            return Err(format!(
                "`{name}` is not in rok.lock (or its requirement changed), and --locked forbids \
                 changing it"
            ));
        }
        if updating || !self.index.has(url) {
            self.fetch_index(url, name)?;
        }
        let pick = |all: &[registry::Entry]| match &pinned {
            Some((_, v)) => all.iter().find(|e| e.vers == *v).cloned(),
            None => registry::best(all, &parsed).cloned(),
        };
        let mut all = registry::entries(&self.index, url, name)?;
        let mut chosen = pick(&all);
        if chosen.is_none() && !self.fetched.iter().any(|u| u == url) && !self.opts.offline {
            self.fetch_index(url, name)?;
            all = registry::entries(&self.index, url, name)?;
            chosen = pick(&all);
        }
        let e = match (chosen, &pinned) {
            (Some(e), _) => e,
            (None, Some((_, v))) => {
                return Err(format!(
                    "`{name}` {v} (in rok.lock) is not in the index {url} (run `rok update {name}`)"
                ));
            }
            (None, None) => return Err(registry::no_match(&all, name, req, url)),
        };
        if let Some((l, _)) = &pinned {
            if l.commit != e.rev {
                return Err(format!(
                    "the index {url} now says {name} {} is commit {}, but rok.lock says {} \
                     (run `rok update {name}` to accept it)",
                    e.vers, e.rev, l.commit
                ));
            }
        }
        if !self.cache.has_commit(&e.url, &e.rev) {
            self.fetch(&e.url, name)?;
            if !self.cache.has_commit(&e.url, &e.rev) {
                return Err(format!(
                    "stone `{name}` {}: commit {} is not in {}",
                    e.vers, e.rev, e.url
                ));
            }
        }
        let (dir, tree) = self.cache.checkout(&e.url, &e.rev)?;
        if tree != e.cksum {
            return Err(format!(
                "stone `{name}` {}: commit {} has tree {tree}, but the index's cksum is {}",
                e.vers, e.rev, e.cksum
            ));
        }
        if !self.new.packages.iter().any(|p| p.name == name) {
            self.new.packages.push(Locked {
                name: name.to_owned(),
                vers: Some(e.vers.to_string()),
                url: url.to_owned(),
                reference: crate::manifest::GitRef::Default,
                commit: e.rev.clone(),
                tree,
            });
        }
        let deps = e
            .deps
            .iter()
            .filter(|d| !d.dev)
            .map(|d| Dep {
                name: d.name.clone(),
                source: Source::Registry {
                    req: d.req.clone(),
                    registry: Some(d.registry.clone().unwrap_or_else(|| url.to_owned())),
                },
            })
            .collect();
        Ok((
            dir,
            Id::Stone {
                registry: url.to_owned(),
                vers: e.vers,
            },
            Some(deps),
        ))
    }

    /// Bring index `url` up to date, once per run.
    fn fetch_index(&mut self, url: &str, name: &str) -> Result<(), String> {
        if self.fetched.iter().any(|u| u == url) {
            return Ok(());
        }
        if self.opts.offline {
            if self.index.has(url) {
                return Ok(());
            }
            return Err(format!(
                "stone `{name}` needs the index {url}, but --offline is set (it is not in the cache)"
            ));
        }
        if !self.opts.quiet {
            eprintln!("    Updating index {url}");
        }
        self.index.fetch(url)?;
        self.fetched.push(url.to_owned());
        Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dependencies_come_first() {
        let r = |n: &str, deps: &[&str]| Resolved {
            name: n.into(),
            root: PathBuf::new(),
            dev: false,
            deps: deps.iter().map(|d| (*d).to_owned()).collect(),
        };
        // Breadth-first from the root: b, a, c; c needs a.
        let all = vec![r("b", &["a", "c"]), r("a", &[]), r("c", &["a"])];
        let names: Vec<String> = order(all).into_iter().map(|d| d.name).collect();
        assert_eq!(names, ["a", "c", "b"]);
    }
}

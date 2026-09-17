//! Incremental compilation below the package (spec 9.2.16): what one
//! build computed, kept in the package's incremental directory for the
//! next. A store is a file of entries by key; a build reads the entries
//! it needs and writes back the ones it used or made (others go). Spans
//! are kept with their files' paths and renumbered on reading; an entry
//! that does not read back is a miss, and a miss computes afresh.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use rokc_core::codec::{Codec, Dec, Enc};
/// An entry key: a hash of the parts.
pub fn key(parts: &[&[u8]]) -> u64 {
    parts.iter().fold(0, |h, p| rokc_core::hash::fast_add(h, p))
}

/// One store file.
pub struct Store {
    path: PathBuf,
    /// The file read at the start, and its entries (key → range).
    data: Vec<u8>,
    index: HashMap<u64, (usize, usize)>,
    /// Entries to write back: read ones (their range) and new ones.
    kept: Mutex<Vec<(u64, Kept)>>,
}

enum Kept {
    Old(usize, usize),
    New(Vec<u8>),
}

impl Store {
    /// The store at `path` (empty when missing, of another compiler or
    /// unreadable). `magic` names the format.
    pub fn open(path: PathBuf, magic: &str) -> Self {
        let mut s = Self {
            path,
            data: Vec::new(),
            index: HashMap::new(),
            kept: Mutex::new(Vec::new()),
        };
        let head = header(magic);
        let Ok(data) = std::fs::read(&s.path) else {
            return s;
        };
        if !data.starts_with(&head) {
            return s;
        }
        let mut d = Dec::new(&data[head.len()..]);
        let mut index = HashMap::new();
        while !d.done() {
            let (Some(k), Some(b)) = (d.u(), d.bytes()) else {
                return s;
            };
            let start = b.as_ptr() as usize - data.as_ptr() as usize;
            index.insert(k, (start, start + b.len()));
        }
        s.data = data;
        s.index = index;
        s
    }

    /// The value at `k`, read with spans renumbered for this build.
    pub fn get<T: Codec>(&self, k: u64, ids: &Ids) -> Option<T> {
        let &(a, b) = self.index.get(&k)?;
        let v = read_value(&self.data[a..b], ids)?;
        self.lock().push((k, Kept::Old(a, b)));
        Some(v)
    }

    /// Keep `v` at `k`.
    pub fn put<T: Codec>(&self, k: u64, v: &T, ids: &Ids) {
        let mut e = Enc::new(true);
        v.enc(&mut e);
        let mut out = Enc::new(true);
        e.files
            .iter()
            .filter_map(|&id| Some((id, ids.paths.get((id as usize).checked_sub(1)?)?.clone())))
            .collect::<Vec<_>>()
            .enc(&mut out);
        out.buf.extend_from_slice(&e.buf);
        self.lock().push((k, Kept::New(out.buf)));
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Vec<(u64, Kept)>> {
        self.kept
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Write the kept entries back (atomically: a concurrent build reads
    /// the old file or the new one).
    pub fn save(&self, magic: &str) {
        let kept = std::mem::take(&mut *self.lock());
        let mut e = Enc::new(true);
        e.buf.extend_from_slice(&header(magic));
        // The last entry at a key wins (a read one, then its new value).
        let mut seen = std::collections::HashSet::new();
        for (k, v) in kept.iter().rev() {
            if !seen.insert(*k) {
                continue;
            }
            e.u(*k);
            e.bytes(match v {
                Kept::Old(a, b) => &self.data[*a..*b],
                Kept::New(b) => b,
            });
        }
        let Some(dir) = self.path.parent() else {
            return;
        };
        if std::fs::create_dir_all(dir).is_err() {
            return;
        }
        let tmp = self
            .path
            .with_extension(format!("tmp{}", std::process::id()));
        if std::fs::write(&tmp, &e.buf).is_ok() && std::fs::rename(&tmp, &self.path).is_err() {
            let _ = std::fs::remove_file(&tmp);
        }
    }
}

fn header(magic: &str) -> Vec<u8> {
    format!("{magic}\n{}\n", crate::rokhir::producer()).into_bytes()
}

/// The files of a compile: path by id and id by path.
pub struct Ids {
    paths: Vec<String>,
    by_path: HashMap<String, u32>,
}

impl Ids {
    pub fn of(files: &rokc_diagnostic::SourceMap) -> Self {
        let paths: Vec<String> = files.files().iter().map(|(p, _)| p.clone()).collect();
        let by_path = paths
            .iter()
            .enumerate()
            .filter_map(|(i, p)| Some((p.clone(), u32::try_from(i + 1).ok()?)))
            .collect();
        Self { paths, by_path }
    }
}

/// An entry's value: its files (old id, path), then the value.
fn read_value<T: Codec>(bytes: &[u8], ids: &Ids) -> Option<T> {
    let mut d = Dec::new(bytes);
    let files = Vec::<(u32, String)>::dec(&mut d)?;
    let mut map = vec![0u32; files.iter().map(|f| f.0 as usize + 1).max().unwrap_or(0)];
    for (old, path) in &files {
        map[*old as usize] = *ids.by_path.get(path)?;
    }
    let mut d = Dec::new(&bytes[bytes.len() - d.rest()..]);
    d.files = Some(&map);
    let v = T::dec(&mut d)?;
    d.done().then_some(v)
}

thread_local! {
    /// This compile's stores (`CompilerConfig::incremental`).
    static INCR: std::cell::RefCell<Option<std::sync::Arc<Incr>>> =
        const { std::cell::RefCell::new(None) };
}

/// The incremental state of one compile.
pub struct Incr {
    pub parse: Store,
    pub bodies: Store,
    /// Files whose parse was read from the store, and all files.
    pub parsed_reused: AtomicUsize,
    pub parsed: AtomicUsize,
    /// `HirModule::reuse` of the compile.
    pub body_reuse: std::sync::Mutex<(usize, usize)>,
}

/// What a compile took from the incremental stores (`-v`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Reuse {
    /// Files parsed: from the store, and in all.
    pub files: (usize, usize),
    /// Bodies lowered: replayed, and in all.
    pub bodies: (usize, usize),
}

impl Incr {
    /// What HIR lowering replayed of what it lowered.
    pub fn bodies_reused(&self, replayed: usize, lowered: usize) {
        *self
            .body_reuse
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = (replayed, lowered);
    }

    /// Count a file's parse, `reused` or not.
    pub fn count_parse(&self, reused: bool) {
        self.parsed.fetch_add(1, Ordering::Relaxed);
        if reused {
            self.parsed_reused.fetch_add(1, Ordering::Relaxed);
        }
    }
}

const PARSE: &str = "ROKAST";
const BODIES: &str = "ROKBODY";

impl Incr {
    fn open(dir: &Path) -> Self {
        Self {
            parse: Store::open(dir.join("parse.rokast"), PARSE),
            bodies: Store::open(dir.join("bodies.rokbody"), BODIES),
            parsed_reused: AtomicUsize::new(0),
            parsed: AtomicUsize::new(0),
            body_reuse: std::sync::Mutex::new((0, 0)),
        }
    }

    fn save(&self) {
        self.parse.save(PARSE);
        self.bodies.save(BODIES);
    }
}

/// Run `f` with the stores of `dir` (none: no caching), then save them;
/// what was reused.
pub fn with<T>(dir: Option<&Path>, f: impl FnOnce() -> T) -> (T, Option<Reuse>) {
    let incr = dir.map(|d| std::sync::Arc::new(Incr::open(d)));
    INCR.with(|i| i.borrow_mut().clone_from(&incr));
    let r = f();
    INCR.with(|i| *i.borrow_mut() = None);
    let reuse = incr.map(|i| {
        i.save();
        Reuse {
            files: (
                i.parsed_reused.load(Ordering::Relaxed),
                i.parsed.load(Ordering::Relaxed),
            ),
            bodies: *i
                .body_reuse
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
        }
    });
    (r, reuse)
}

/// This compile's stores.
pub fn current() -> Option<std::sync::Arc<Incr>> {
    INCR.with(|i| i.borrow().clone())
}

/// What of the target and the build's flags a cached result depends on:
/// the target's spec and the cfg.
pub fn target_key(cfg: &crate::CfgEnv, target: &rokc_mir::Target) -> String {
    format!("{:016x}|{cfg:?}", target.hash())
}

/// The body store of a compile, for HIR lowering.
struct BodyStore(std::sync::Arc<Incr>, Ids);

impl rokc_hir::BodyCache for BodyStore {
    fn get(&self, key: u64) -> Option<rokc_hir::Unit> {
        self.0.bodies.get(key, &self.1)
    }
    fn put(&self, key: u64, unit: &rokc_hir::Unit) {
        self.0.bodies.put(key, unit, &self.1);
    }
}

pub fn bodies(i: std::sync::Arc<Incr>, files: &rokc_diagnostic::SourceMap) -> rokc_hir::Bodies {
    rokc_hir::Bodies(std::sync::Arc::new(BodyStore(i, Ids::of(files))))
}

/// `ROKC_INCR_VERIFY=1`: lowering is done twice, without the stores and
/// with them, and the two must agree; the check of the second against
/// the first (a difference is an error of the build).
pub fn verify() -> Option<fn(&rokc_hir::HirModule, &mut rokc_hir::HirModule)> {
    let on = std::env::var_os("ROKC_INCR_VERIFY").is_some_and(|v| !v.is_empty() && v != "0");
    on.then_some(check)
}

fn check(clean: &rokc_hir::HirModule, incr: &mut rokc_hir::HirModule) {
    let parts = |m: &rokc_hir::HirModule| {
        let mut vis: Vec<_> = m.type_visibility.iter().collect();
        vis.sort_by(|a, b| a.0.cmp(b.0));
        let fns = m
            .functions
            .iter()
            .map(|f| (f.name.clone(), format!("{f:?}")));
        let rest = [
            ("structs", format!("{:?}", m.structs)),
            ("enums", format!("{:?}", m.enums)),
            ("statics", format!("{:?}", m.statics)),
            ("diagnostics", format!("{:?}", m.diagnostics)),
            ("roots", format!("{:?}", (&m.roots, &m.unlowered))),
            (
                "any",
                format!("{:?}", (&m.any_seeds, &m.any_types, &m.any_tags)),
            ),
            ("visibility", format!("{vis:?}")),
        ]
        .map(|(k, v)| (k.to_owned(), v));
        fns.chain(rest).collect::<Vec<_>>()
    };
    let (a, b) = (parts(clean), parts(incr));
    let differ = if a.len() == b.len() {
        a.iter()
            .zip(&b)
            .find(|(x, y)| x != y)
            .map(|(x, _)| x.0.clone())
    } else {
        Some(format!("{} functions, not {}", b.len(), a.len()))
    };
    if let Some(what) = differ {
        incr.diagnostics.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Internal,
            rokc_diagnostic::Span::DUMMY,
            format!(
                "ROKC_INCR_VERIFY: the incremental lowering differs from a clean one at `{what}`"
            ),
        ));
    }
}

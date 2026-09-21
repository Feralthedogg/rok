//! Incremental body lowering (spec 9.2.16): a declaration's lowered
//! body, with everything its lowering added to the shared state
//! (closures, instances, type instances, `any` tags, warnings), is kept
//! as a unit and replayed in a later build instead of lowered again.
//!
//! A unit is keyed by the program's interface (`interface_key`: every
//! item but the bodies of the plain declarations, positions left out)
//! and the declaration itself (its body with positions). Lowering a
//! body reads the shared state; each read that could come out
//! otherwise in another build is logged with its answer (`Lookup`).
//! A unit replays when every read answers alike now and the files its
//! spans point into outside its body are unchanged. The functions,
//! types and inference variables it made are renumbered from where
//! this build's counters stand, and the older ones it names by what
//! the reads answer now. Otherwise the body is lowered and the unit
//! made anew: a miss is always safe.
//!
//! A body is plain when nothing else is derived from it: not generic,
//! not `const`, its return type written (or `()`), not a trait's
//! default. A lowering that reports an error or touches state beyond
//! what it logs makes no unit.

use std::collections::{HashMap, HashSet};

use rokc_ast::{FnDef, ImplItem, Item, Program};
use rokc_core::codec::{Codec, Dec, Enc, IdKind};
use rokc_core::{codec_enum, codec_struct};
use rokc_diagnostic::{RokDiagnostic, Span};
use rokc_ir_common::FunctionId;

use super::expr::AnyDispatch;
use super::{AliasUse, Env, FnSig, MethodOrFn, RefOut, mangle_inst, ty_mangle};
use crate::{EnumId, HirEnumDef, HirFunction, HirStructDef, HirTy, StructId};

/// Where an embedder keeps units between builds, and the errors of
/// generic body checks (`bounds`).
pub trait BodyCache {
    fn get(&self, key: u64) -> Option<Unit>;
    fn put(&self, key: u64, unit: &Unit);
    fn get_check(&self, key: u64) -> Option<Vec<RokDiagnostic>>;
    fn put_check(&self, key: u64, errors: &[RokDiagnostic]);
}

/// A `BodyCache` for `HirInput::bodies`.
#[derive(Clone)]
pub struct Bodies(pub std::sync::Arc<dyn BodyCache + Send + Sync>);

impl std::fmt::Debug for Bodies {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Bodies")
    }
}

/// How many bodies were lowered and how many of them replayed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BodyReuse {
    pub replayed: usize,
    pub lowered: usize,
}

/// The counters of the shared state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Counts {
    next_id: u32,
    structs: u32,
    enums: u32,
    any_tags: u32,
    any_dispatch: u32,
    extras: u32,
    infer_vars: u32,
}

/// A read of the shared state, with its answer.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum Lookup {
    Mono(String, Vec<HirTy>, Option<FunctionId>),
    /// A type by its path (not an instance's key).
    Struct(String, Option<StructId>),
    Enum(String, Option<EnumId>),
    /// The instance of a generic type over these arguments.
    StructInst(String, Vec<HirTy>, Option<StructId>),
    EnumInst(String, Vec<HirTy>, Option<EnumId>),
    /// Every instance of a generic type.
    StructInsts(String, Vec<StructId>),
    EnumInsts(String, Vec<EnumId>),
    Thunk(Key, Option<FunctionId>),
    AnyTag(HirTy, Option<u32>),
    AnyDispatch(HirTy, String, String, Option<FunctionId>),
    /// `inferred_ret`'s entry (`Some(None)`: being inferred).
    #[allow(clippy::option_option)]
    InferredRet(FunctionId, Option<Option<HirTy>>),
    /// The signature at a `fn_table` key, by its hash.
    Sig(String, u64),
    /// A declaration (its body evaluated), by its hash.
    Body(FunctionId, u64),
}

/// An `InstanceWarns` change.
#[derive(Clone, Debug)]
pub(super) enum WarnEvent {
    Instance(Span, FunctionId),
    Warn(Span, RokDiagnostic, FunctionId),
}

/// A key of `mono_cache`, `thunks` or `unknown_spans`.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum Key {
    Mono(String, Vec<HirTy>),
    /// `throws::thunk_key`'s parts.
    Thunk(&'static str, Option<FunctionId>, HirTy, HirTy),
    Unknown(String),
}

impl Key {
    /// The table's key.
    fn mono(name: &str, args: &[HirTy]) -> (String, Vec<String>) {
        (name.to_owned(), args.iter().map(ty_mangle).collect())
    }
}

/// One declaration's lowering and what it added: what a replay checks
/// (read with the ids as they were), and the rest (read renumbered).
pub struct Unit {
    head: Head,
    body: Vec<u8>,
    /// The files `body`'s spans name (encoding), or the old → new file
    /// ids to read it with (decoding).
    files: Vec<u32>,
}

struct Head {
    start: Counts,
    end: Counts,
    lookups: Vec<Lookup>,
    /// Files its spans point into outside its body: path, the end of
    /// the line its furthest span there ends on, and the hash of the
    /// text up to it (the spans' positions, and what they show).
    deps: Vec<(String, u32, u64)>,
    /// The generic type each new struct, then enum, instantiates.
    bases: Vec<String>,
    /// The functions and types made before it that it names: kind, id,
    /// build-independent name (a function's name, a type's
    /// `crate::name_type`).
    named: Vec<(u8, u32, String)>,
}

struct Body {
    func: HirFunction,
    extras: Vec<HirFunction>,
    structs: Vec<HirStructDef>,
    enums: Vec<HirEnumDef>,
    /// The final entries of each function it touched.
    entries: Vec<Entries>,
    /// The final `mono_cache` / `thunks` entry at each key it set.
    keyed: Vec<(Key, Option<FunctionId>)>,
    unknown_spans: Vec<(String, Span)>,
    any_tags: Vec<(HirTy, u32)>,
    any_dispatch: Vec<AnyDispatch>,
    /// `let` inference variables (their numbers name type instances).
    infer_vars: Vec<super::infer::Var>,
    warns: Vec<WarnEvent>,
    diagnostics: Vec<RokDiagnostic>,
    name_diags: Vec<RokDiagnostic>,
    alias_uses: Vec<AliasUse>,
}

/// The entries of one function in the tables by function (`None`:
/// none).
#[derive(Clone)]
struct Entries {
    id: FunctionId,
    ref_out: Option<RefOut>,
    mono_sig: Option<FnSig>,
    fn_origin: Option<(bool, bool)>,
    track_caller: bool,
    #[allow(clippy::option_option)] // an entry of a table of options
    inferred_ret: Option<Option<HirTy>>,
    /// How far past the unit's first function id its lowering started.
    inferred_fn: Option<(u32, HirFunction)>,
}

codec_struct!(Counts {
    next_id,
    structs,
    enums,
    any_tags,
    any_dispatch,
    extras,
    infer_vars
});
codec_enum!(Lookup {
    Mono(x0, x1, x2),
    Struct(x0, x1),
    Enum(x0, x1),
    StructInst(x0, x1, x2),
    EnumInst(x0, x1, x2),
    StructInsts(x0, x1),
    EnumInsts(x0, x1),
    Thunk(x0, x1),
    AnyTag(x0, x1),
    AnyDispatch(x0, x1, x2, x3),
    InferredRet(x0, x1),
    Sig(x0, x1),
    Body(x0, x1),
});
codec_enum!(WarnEvent {
    Instance(x0, x1),
    Warn(x0, x1, x2)
});
codec_enum!(Key {
    Mono(x0, x1),
    Thunk(x0, x1, x2, x3),
    Unknown(x0)
});
codec_struct!(FnSig {
    id,
    ret_ty,
    param_defaults,
    param_tys,
    param_names,
    param_refs,
    variadic
});
codec_struct!(RefOut { ret, refs });
codec_struct!(AnyDispatch {
    id,
    recv_ty,
    trait_key,
    method,
    params,
    ret,
    span
});
codec_struct!(Entries {
    id,
    ref_out,
    mono_sig,
    fn_origin,
    track_caller,
    inferred_ret,
    inferred_fn
});
codec_struct!(Head {
    start,
    end,
    lookups,
    deps,
    bases,
    named
});
codec_struct!(Body {
    func,
    extras,
    structs,
    enums,
    entries,
    keyed,
    unknown_spans,
    any_tags,
    any_dispatch,
    infer_vars,
    warns,
    diagnostics,
    name_diags,
    alias_uses,
});

impl Codec for Unit {
    fn enc(&self, e: &mut Enc) {
        self.head.enc(e);
        e.bytes(&self.body);
        for f in &self.files {
            if !e.files.contains(f) {
                e.files.push(*f);
            }
        }
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        let head = Head::dec(d)?;
        let body = d.bytes()?.to_vec();
        Some(Self {
            head,
            body,
            files: d.files.map(<[u32]>::to_vec).unwrap_or_default(),
        })
    }
}

/// A lowering being recorded.
struct Rec {
    /// Struct and enum ids below these are the program's own types
    /// (the same in every build of the interface).
    base: (u32, u32),
    lookups: Vec<Lookup>,
    /// Keys looked up so far (the first answer is the one that counts).
    seen: HashSet<String>,
    warns: Vec<WarnEvent>,
    /// Functions whose entries in the tables by function this lowering
    /// may have set or removed, and keys of the tables by key.
    touched: Vec<FunctionId>,
    keys: Vec<Key>,
}

thread_local! {
    static REC: std::cell::RefCell<Option<Rec>> = const { std::cell::RefCell::new(None) };
}

/// Log a read of the shared state (while a unit is recorded): `key`
/// names what was read, `answer` makes the log entry.
pub(super) fn log(key: impl FnOnce() -> String, answer: impl FnOnce() -> Lookup) {
    REC.with(|r| {
        if let Some(rec) = r.borrow_mut().as_mut() {
            if rec.seen.insert(key()) {
                rec.lookups.push(answer());
            }
        }
    });
}

/// `log` of a struct (`enum_`: enum) id lookup by path: answers other
/// than one of the program's own types.
pub(super) fn log_type(enum_: bool, key: &str, found: Option<u32>) {
    REC.with(|r| {
        if let Some(rec) = r.borrow_mut().as_mut() {
            let base = if enum_ { rec.base.1 } else { rec.base.0 };
            if found.is_some_and(|id| id < base) || !rec.seen.insert(format!("t{enum_}|{key}")) {
                return;
            }
            rec.lookups.push(if enum_ {
                Lookup::Enum(key.to_owned(), found.map(EnumId))
            } else {
                Lookup::Struct(key.to_owned(), found.map(StructId))
            });
        }
    });
}

/// Note that the entries of function `id` may change.
pub(super) fn touch(id: FunctionId) {
    REC.with(|r| {
        if let Some(rec) = r.borrow_mut().as_mut() {
            rec.touched.push(id);
        }
    });
}

/// Note that the entry at a key may change.
pub(super) fn touch_key(k: impl FnOnce() -> Key) {
    REC.with(|r| {
        if let Some(rec) = r.borrow_mut().as_mut() {
            rec.keys.push(k());
        }
    });
}

/// Log an `InstanceWarns` change.
pub(super) fn log_warn(e: impl FnOnce() -> WarnEvent) {
    REC.with(|r| {
        if let Some(rec) = r.borrow_mut().as_mut() {
            rec.warns.push(e());
        }
    });
}

/// The incremental state of one `lower_full`.
pub(super) struct Incr<'a> {
    cache: &'a dyn BodyCache,
    /// `interface_key`.
    interface: u64,
    /// Per declaration: plain (see the module doc).
    plain: Vec<bool>,
    base: (u32, u32),
    /// Per file: each line's end and the hash of the text up to it.
    lines: std::cell::RefCell<HashMap<u32, Vec<(u32, u64)>>>,
    names: std::cell::RefCell<Names>,
    pub reuse: std::cell::Cell<BodyReuse>,
}

/// The names of the functions and types made so far, both ways (a name
/// given twice names neither).
#[derive(Default)]
struct Names {
    /// Functions, structs, enums looked at so far.
    done: [usize; 3],
    by_id: HashMap<(u8, u32), String>,
    by_name: HashMap<(u8, String), Option<u32>>,
}

impl Names {
    fn update(&mut self, env: &Env<'_>) {
        let mut add = |k: u8, id: u32, name: String| {
            self.by_name
                .entry((k, name.clone()))
                .and_modify(|v| *v = None)
                .or_insert(Some(id));
            self.by_id.insert((k, id), name);
        };
        let extras = env.sink.extras.borrow();
        for f in extras.iter().skip(self.done[0]) {
            add(0, f.id.0, f.name.clone());
        }
        self.done[0] = extras.len();
        for (k, len) in [
            (1u8, env.defs.structs.borrow().len()),
            (2, env.defs.enums.borrow().len()),
        ] {
            let from = self.done[usize::from(k)];
            for id in from..len {
                let id = u32::try_from(id).unwrap_or(u32::MAX);
                if let Some(name) = crate::type_name(k == 2, id) {
                    add(k, id, name);
                }
            }
            self.done[usize::from(k)] = len;
        }
    }

    fn name_of(&self, k: u8, id: u32) -> Option<&str> {
        self.by_id.get(&(k, id)).map(String::as_str)
    }

    fn id_of(&self, k: u8, name: &str) -> Option<u32> {
        self.by_name.get(&(k, name.to_owned())).copied().flatten()
    }
}

impl<'a> Incr<'a> {
    pub(super) fn new(
        env: &Env<'_>,
        cache: &'a dyn BodyCache,
        program: &Program,
        raw_uses: &[(String, rokc_core::Visibility, rokc_ast::UseTree)],
        input: &crate::HirInput,
    ) -> Self {
        let plain: Vec<bool> = (0..env.decls.len()).map(|i| is_plain(env, i)).collect();
        let bodies: HashSet<(&str, Span)> = env
            .decls
            .iter()
            .zip(&plain)
            .filter(|(_, p)| **p)
            .map(|(d, _)| (d.def().name.as_str(), d.def().span))
            .collect();
        let interface = interface_key(env, &bodies, program, raw_uses, input);
        Self {
            cache,
            interface,
            plain,
            base: declared(env),
            lines: std::cell::RefCell::new(HashMap::new()),
            names: std::cell::RefCell::new(Names::default()),
            reuse: std::cell::Cell::new(BodyReuse::default()),
        }
    }

    /// The end of the line of file `id` that offset `end` is on (`exact`:
    /// `end` must be one), and the hash of the text up to it.
    fn prefix(&self, env: &Env<'_>, id: u32, end: u32, exact: bool) -> Option<(u32, u64)> {
        let mut lines = self.lines.borrow_mut();
        let table = lines.entry(id).or_insert_with(|| {
            let Some((_, text)) = env.sources.file(id) else {
                return Vec::new();
            };
            let (mut h, mut at) = (0u64, 0usize);
            let mut out = Vec::new();
            for line in text.split_inclusive('\n') {
                h = rokc_core::hash::fast_add(h, line.as_bytes());
                at += line.len();
                out.push((u32::try_from(at).unwrap_or(u32::MAX), h));
            }
            out
        });
        let k = table.partition_point(|(at, _)| *at < end);
        let found = *table.get(k)?;
        (!exact || found.0 == end).then_some(found)
    }

    /// The errors of checking generic body `f` (`owner`: its impl's
    /// target or its trait), from the store or from `check`. They follow
    /// from the interface and the body (positions in), so they are kept
    /// unless one points outside the body.
    pub(super) fn checked(
        &self,
        env: &Env<'_>,
        f: &FnDef,
        owner: &[u8],
        check: impl FnOnce() -> Vec<RokDiagnostic>,
    ) -> Vec<RokDiagnostic> {
        let mut e = Enc::new(true);
        f.enc(&mut e);
        let path = env.sources.path(f.span.file).unwrap_or_default();
        let key = [b"check".as_slice(), path.as_bytes(), owner, &e.buf]
            .iter()
            .fold(self.interface, |h, part| rokc_core::hash::fast_add(h, part));
        if let Some(errors) = self.cache.get_check(key) {
            return errors;
        }
        let errors = check();
        let inside =
            |s: &Span| s.file == f.span.file && s.start >= f.span.start && s.end <= f.span.end;
        let local = errors.iter().all(|d| {
            d.primary
                .iter()
                .map(|l| &l.span)
                .chain(d.secondary.iter().map(|l| &l.span))
                .all(inside)
        });
        if local {
            self.cache.put_check(key, &errors);
        }
        errors
    }

    /// Lower declaration `i` (not a stub): replayed from its unit, or
    /// lowered and kept as one.
    pub(super) fn lower(&self, env: &Env<'_>, i: usize) -> HirFunction {
        if !self.plain[i] {
            return super::collect::lower_decl(env, i, false);
        }
        let def = env.decls[i].def();
        let mut e = Enc::new(true);
        def.enc(&mut e);
        let path = env.sources.path(def.span.file).unwrap_or_default();
        let key = [&(i as u64).to_le_bytes()[..], path.as_bytes(), &e.buf]
            .iter()
            .fold(self.interface, |h, part| rokc_core::hash::fast_add(h, part));
        let mut r = self.reuse.get();
        r.lowered += 1;
        if let Some(f) = self.cache.get(key).and_then(|u| self.replay(env, &u)) {
            r.replayed += 1;
            self.reuse.set(r);
            return f;
        }
        self.reuse.set(r);
        let start = counts(env);
        let before = Sizes::of(env);
        REC.with(|r| {
            *r.borrow_mut() = Some(Rec {
                base: self.base,
                lookups: Vec::new(),
                seen: HashSet::new(),
                warns: Vec::new(),
                touched: Vec::new(),
                keys: Vec::new(),
            });
        });
        let f = super::collect::lower_decl(env, i, false);
        let rec = REC.with(|r| r.borrow_mut().take());
        let unit = rec.and_then(|rec| self.record(env, i, &f, start, &before, rec));
        if let Some(unit) = unit {
            self.cache.put(key, &unit);
        }
        f
    }

    /// The unit of declaration `i` lowered as `f` from `start`, unless
    /// the lowering did more than it logged.
    fn record(
        &self,
        env: &Env<'_>,
        i: usize,
        f: &HirFunction,
        start: Counts,
        before: &Sizes,
        rec: Rec,
    ) -> Option<Unit> {
        let sink = &env.sink;
        let end = counts(env);
        let own = |id: &FunctionId| id.0 >= start.next_id && id.0 < end.next_id;
        let diagnostics = sink.diagnostics.borrow()[before.diagnostics..].to_vec();
        let name_diags = env.names.diags.borrow()[before.name_diags..].to_vec();
        if diagnostics
            .iter()
            .chain(&name_diags)
            .any(RokDiagnostic::is_error)
            || sink.uninferred.get() != before.uninferred
            || !sink.tentative_ret.borrow().is_empty()
            || !sink.recursive_ret.borrow().is_empty()
        {
            return None;
        }
        // Every table entry it may have set, as it is now.
        let mut touched = rec.touched;
        touched.push(FunctionId(u32::try_from(i).ok()?));
        touched.sort_unstable();
        touched.dedup();
        let entries: Vec<Entries> = touched
            .into_iter()
            .map(|id| {
                let inferred_fn = match sink.inferred_fns.borrow().get(&id) {
                    Some((at, f)) => Some((at.checked_sub(start.next_id)?, f.clone())),
                    None => None,
                };
                Some(Entries {
                    id,
                    ref_out: sink.ref_out.borrow().get(&id).cloned(),
                    mono_sig: sink.mono_sigs.borrow().get(&id).cloned(),
                    fn_origin: sink.fn_origin.borrow().get(&id).copied(),
                    track_caller: sink.track_caller.borrow().contains(&id),
                    inferred_ret: sink.inferred_ret.borrow().get(&id).cloned(),
                    inferred_fn,
                })
            })
            .collect::<Option<_>>()?;
        let mut keyed: Vec<(Key, Option<FunctionId>)> = Vec::new();
        let mut unknown_spans: Vec<(String, Span)> = Vec::new();
        for k in rec.keys {
            if let Key::Unknown(path) = &k {
                if !unknown_spans.iter().any(|(p, _)| p == path) {
                    let at = env.names.unknown_spans.borrow().get(path).copied()?;
                    unknown_spans.push((path.clone(), at));
                }
                continue;
            }
            if keyed.iter().any(|(old, _)| *old == k) {
                continue;
            }
            let v = match &k {
                Key::Mono(name, args) => sink
                    .mono_cache
                    .borrow()
                    .get(&Key::mono(name, args))
                    .copied(),
                Key::Thunk(kind, target, slot, callee) => sink
                    .thunks
                    .borrow()
                    .get(&super::throws::thunk_key(kind, *target, slot, callee))
                    .copied(),
                Key::Unknown(_) => None,
            };
            keyed.push((k, v));
        }
        // Tables that grew past what it touched: something it did is
        // not accounted for.
        let grew = |now: usize, then: usize, mine: usize| now > then + mine;
        let count = |pick: &dyn Fn(&Entries) -> bool| entries.iter().filter(|e| pick(e)).count();
        let monos = keyed
            .iter()
            .filter(|(k, _)| matches!(k, Key::Mono(..)))
            .count();
        if grew(sink.mono_cache.borrow().len(), before.mono_cache, monos)
            || grew(
                sink.thunks.borrow().len(),
                before.thunks,
                keyed.len() - monos,
            )
            || grew(
                sink.ref_out.borrow().len(),
                before.ref_out,
                count(&|e| e.ref_out.is_some()),
            )
            || grew(
                sink.mono_sigs.borrow().len(),
                before.mono_sigs,
                count(&|e| e.mono_sig.is_some()),
            )
            || grew(
                sink.fn_origin.borrow().len(),
                before.fn_origin,
                count(&|e| e.fn_origin.is_some()),
            )
            || grew(
                sink.track_caller.borrow().len(),
                before.track_caller,
                count(&|e| e.track_caller),
            )
            || grew(
                sink.inferred_ret.borrow().len(),
                before.inferred_ret,
                count(&|e| e.inferred_ret.is_some()),
            )
            || grew(
                sink.inferred_fns.borrow().len(),
                before.inferred_fns,
                count(&|e| e.inferred_fn.is_some()),
            )
            || grew(
                env.names.unknown_spans.borrow().len(),
                before.unknown_spans,
                unknown_spans.len(),
            )
        {
            return None;
        }
        // The functions it made are its own, numbered from `start`.
        let extras = sink.extras.borrow()[start.extras as usize..].to_vec();
        if extras.iter().any(|f| !own(&f.id))
            || sink.any_dispatch.borrow()[start.any_dispatch as usize..]
                .iter()
                .any(|d| !own(&d.id))
        {
            return None;
        }
        let structs = env.defs.structs.borrow()[start.structs as usize..].to_vec();
        let enums = env.defs.enums.borrow()[start.enums as usize..].to_vec();
        // Each new type is an instance `base__args` (`mangle_inst`).
        let base = |name: &str, args: &[HirTy]| {
            let tail = mangle_inst("", args);
            name.strip_suffix(&tail).map(str::to_owned)
        };
        let bases: Vec<String> = structs
            .iter()
            .map(|s| base(&s.name, &s.generic_args))
            .chain(enums.iter().map(|e| base(&e.name, &e.generic_args)))
            .collect::<Option<_>>()?;
        let body = Body {
            func: f.clone(),
            extras,
            structs,
            enums,
            entries,
            keyed,
            unknown_spans,
            any_tags: sink.any_tags.borrow()[start.any_tags as usize..].to_vec(),
            any_dispatch: sink.any_dispatch.borrow()[start.any_dispatch as usize..].to_vec(),
            infer_vars: sink.infer_vars.borrow()[start.infer_vars as usize..].to_vec(),
            warns: rec.warns,
            diagnostics,
            name_diags,
            alias_uses: env.names.alias_uses.borrow()[before.alias_uses..].to_vec(),
        };
        // The files its spans point into outside its body.
        let span = env.decls[i].def().span;
        let mut e = Enc::new(true);
        e.home = Some((span.file, span.start, span.end));
        e.ids = Some(Vec::new());
        body.enc(&mut e);
        let mut head = Head {
            start,
            end,
            lookups: rec.lookups,
            deps: Vec::new(),
            bases,
            named: Vec::new(),
        };
        let mut h = Enc::new(true);
        h.home = e.home;
        h.ids = Some(Vec::new());
        head.enc(&mut h);
        let written = e.ids.take().into_iter().chain(h.ids.take()).flatten();
        head.named = self.named(env, start, end, written)?;
        let mut foreign: Vec<(u32, u32)> = Vec::new();
        for (f, end) in e.foreign.into_iter().chain(h.foreign) {
            match foreign.iter_mut().find(|(g, _)| *g == f) {
                Some((_, e)) => *e = (*e).max(end),
                None => foreign.push((f, end)),
            }
        }
        foreign.sort_unstable();
        head.deps = foreign
            .iter()
            .map(|&(id, end)| {
                let (at, hash) = self.prefix(env, id, end, false)?;
                Some((env.sources.path(id)?.to_owned(), at, hash))
            })
            .collect::<Option<_>>()?;
        Some(Unit {
            head,
            body: e.buf,
            files: e.files,
        })
    }

    /// The ids of what was made before `start` that `encodings` (of a
    /// unit made from `start` to `end`) name, with their names.
    fn named(
        &self,
        env: &Env<'_>,
        start: Counts,
        end: Counts,
        written: impl Iterator<Item = (IdKind, u32)>,
    ) -> Option<Vec<(u8, u32, String)>> {
        let mut seen = HashSet::new();
        let decls = u32::try_from(env.decls.len()).ok()?;
        let mut names = self.names.borrow_mut();
        names.update(env);
        let mut out = Vec::new();
        for (kind, id) in written {
            let (fixed, from, to) = match kind {
                IdKind::Function => (decls, start.next_id, end.next_id),
                IdKind::Struct => (self.base.0, start.structs, end.structs),
                IdKind::Enum => (self.base.1, start.enums, end.enums),
                IdKind::InferVar => (0, start.infer_vars, end.infer_vars),
            };
            let k = (kind_tag(kind), id);
            if id >= fixed && !(from..to).contains(&id) && seen.insert(k) {
                out.push((k.0, id, names.name_of(k.0, id)?.to_owned()));
            }
        }
        Some(out)
    }

    /// Replay `u` when it holds for this build (see the module doc).
    fn replay(&self, env: &Env<'_>, u: &Unit) -> Option<HirFunction> {
        let sink = &env.sink;
        let head = &u.head;
        for (path, at, hash) in &head.deps {
            let id = env.sources.id_of(path)?;
            if self.prefix(env, id, *at, true) != Some((*at, *hash)) {
                return None;
            }
        }
        let ids = Ids::new(head, counts(env), self.base, env.decls.len());
        {
            let mut names = self.names.borrow_mut();
            names.update(env);
            let mut learned = ids.learned.borrow_mut();
            for (k, old, name) in &head.named {
                if let Some(now) = names.id_of(*k, name) {
                    learned.insert((*k, *old), now);
                }
            }
        }
        if !head.lookups.iter().all(|l| answers(env, &ids, l)) {
            return None;
        }
        let map = |kind, id| ids.map(kind, id);
        let mut d = Dec::new(&u.body);
        d.files = Some(&u.files);
        d.ids = Some(&map);
        let b = Body::dec(&mut d)?;
        // A new tag must still be free (`any_tag` probes past a taken one).
        {
            let tags = sink.any_tags.borrow();
            if b.any_tags
                .iter()
                .any(|(_, t)| tags.iter().any(|(_, old)| old == t))
            {
                return None;
            }
        }
        let now = ids.now;
        // Names made of this build's ids follow them.
        let renamed = |mut f: HirFunction| {
            let old = f.id.0 - now.next_id + head.start.next_id;
            for p in ["__closure_", "__coro_", "__thunk_"] {
                if f.name == format!("{p}{old}") {
                    f.name = format!("{p}{}", f.id.0);
                }
            }
            f
        };
        sink.extras
            .borrow_mut()
            .extend(b.extras.into_iter().map(renamed));
        let (struct_bases, enum_bases) = head.bases.split_at(b.structs.len());
        {
            let mut table = env.defs.struct_table.borrow_mut();
            let mut structs = env.defs.structs.borrow_mut();
            for (mut s, base) in b.structs.into_iter().zip(struct_bases) {
                s.name = mangle_inst(base, &s.generic_args);
                crate::name_type(false, s.id.0, base, &s.generic_args);
                table.insert(s.name.clone(), s.id);
                structs.push(s);
            }
        }
        {
            let mut table = env.defs.enum_table.borrow_mut();
            let mut enums = env.defs.enums.borrow_mut();
            for (mut e, base) in b.enums.into_iter().zip(enum_bases) {
                e.name = mangle_inst(base, &e.generic_args);
                crate::name_type(true, e.id.0, base, &e.generic_args);
                table.insert(e.name.clone(), e.id);
                enums.push(e);
            }
        }
        for e in b.entries {
            set(&mut sink.ref_out.borrow_mut(), e.id, e.ref_out);
            set(&mut sink.mono_sigs.borrow_mut(), e.id, e.mono_sig);
            set(&mut sink.fn_origin.borrow_mut(), e.id, e.fn_origin);
            set(&mut sink.inferred_ret.borrow_mut(), e.id, e.inferred_ret);
            set(
                &mut sink.inferred_fns.borrow_mut(),
                e.id,
                e.inferred_fn.map(|(at, f)| (now.next_id + at, f)),
            );
            if e.track_caller {
                sink.track_caller.borrow_mut().insert(e.id);
            } else {
                sink.track_caller.borrow_mut().remove(&e.id);
            }
        }
        for (k, v) in b.keyed {
            match k {
                Key::Mono(name, args) => {
                    set(
                        &mut sink.mono_cache.borrow_mut(),
                        Key::mono(&name, &args),
                        v,
                    );
                }
                Key::Thunk(kind, target, slot, callee) => set(
                    &mut sink.thunks.borrow_mut(),
                    super::throws::thunk_key(kind, target, &slot, &callee),
                    v,
                ),
                Key::Unknown(_) => {}
            }
        }
        {
            let mut unknown = env.names.unknown_spans.borrow_mut();
            for (path, at) in b.unknown_spans {
                unknown.entry(path).or_insert(at);
            }
        }
        sink.any_tags.borrow_mut().extend(b.any_tags);
        sink.any_dispatch.borrow_mut().extend(b.any_dispatch);
        sink.infer_vars.borrow_mut().extend(b.infer_vars);
        {
            let mut iw = sink.instance_warns.borrow_mut();
            for w in b.warns {
                match w {
                    WarnEvent::Instance(t, id) => iw.instance(t, id),
                    WarnEvent::Warn(t, d, id) => iw.warn(t, d, id),
                }
            }
        }
        sink.diagnostics.borrow_mut().extend(b.diagnostics);
        env.names.diags.borrow_mut().extend(b.name_diags);
        env.names.alias_uses.borrow_mut().extend(b.alias_uses);
        sink.next_id
            .set(head.end.next_id - head.start.next_id + now.next_id);
        Some(b.func)
    }
}

/// A replay's renumbering: what the unit made moves to where this
/// build's counters stand; what it found made before is what the reads
/// answer now (`learn`); the program's own declarations and types keep
/// their ids.
struct Ids {
    start: Counts,
    end: Counts,
    now: Counts,
    base: (u32, u32),
    decls: u32,
    learned: std::cell::RefCell<HashMap<(u8, u32), u32>>,
}

const fn kind_tag(k: IdKind) -> u8 {
    match k {
        IdKind::Function => 0,
        IdKind::Struct => 1,
        IdKind::Enum => 2,
        IdKind::InferVar => 3,
    }
}

impl Ids {
    fn new(head: &Head, now: Counts, base: (u32, u32), decls: usize) -> Self {
        Self {
            start: head.start,
            end: head.end,
            now,
            base,
            decls: u32::try_from(decls).unwrap_or(u32::MAX),
            learned: std::cell::RefCell::new(HashMap::new()),
        }
    }

    /// The id `id` of `kind` of the unit is in this build.
    fn map(&self, kind: IdKind, id: u32) -> Option<u32> {
        let (from, to, now, fixed) = match kind {
            IdKind::Function => (
                self.start.next_id,
                self.end.next_id,
                self.now.next_id,
                self.decls,
            ),
            IdKind::Struct => (
                self.start.structs,
                self.end.structs,
                self.now.structs,
                self.base.0,
            ),
            IdKind::Enum => (
                self.start.enums,
                self.end.enums,
                self.now.enums,
                self.base.1,
            ),
            IdKind::InferVar => (
                self.start.infer_vars,
                self.end.infer_vars,
                self.now.infer_vars,
                0,
            ),
        };
        if id < fixed {
            Some(id)
        } else if (from..to).contains(&id) {
            Some(id - from + now)
        } else {
            self.learned.borrow().get(&(kind_tag(kind), id)).copied()
        }
    }

    /// Whether `old` (a read's answer then) is `new` (its answer now):
    /// an id made before the unit and not known yet is learned.
    fn same(&self, kind: IdKind, old: Option<u32>, new: Option<u32>) -> bool {
        match (old, new) {
            (None, None) => true,
            (Some(o), Some(n)) => {
                if let Some(m) = self.map(kind, o) {
                    return m == n;
                }
                self.learned.borrow_mut().insert((kind_tag(kind), o), n);
                true
            }
            _ => false,
        }
    }

    /// `ty` with its ids as this build numbers them.
    fn ty(&self, ty: &HirTy) -> Option<HirTy> {
        let mut e = Enc::new(true);
        ty.enc(&mut e);
        let map = |kind, id| self.map(kind, id);
        let mut d = Dec::new(&e.buf);
        d.ids = Some(&map);
        HirTy::dec(&mut d)
    }

    fn tys(&self, tys: &[HirTy]) -> Option<Vec<HirTy>> {
        tys.iter().map(|t| self.ty(t)).collect()
    }
}

/// How many structs and enums the program declares: they come first,
/// in item order (the instances follow), so their ids are the same in
/// every build of the interface.
fn declared(env: &Env<'_>) -> (u32, u32) {
    let n = |x: usize| u32::try_from(x).unwrap_or(u32::MAX);
    let structs = env.defs.structs.borrow();
    let enums = env.defs.enums.borrow();
    (
        n(structs
            .iter()
            .position(|s| !s.generic_args.is_empty())
            .unwrap_or(structs.len())),
        n(enums
            .iter()
            .position(|e| !e.generic_args.is_empty())
            .unwrap_or(enums.len())),
    )
}

/// The hash of `v`'s encoding, positions in.
fn hash_of<T: Codec>(v: &T) -> u64 {
    let mut e = Enc::new(true);
    v.enc(&mut e);
    rokc_core::hash::fast(&e.buf)
}

/// Log a read of the signature at `fn_table` key `key`.
pub(super) fn log_sig(key: &str, sig: &FnSig) {
    log(
        || format!("s|{key}"),
        || Lookup::Sig(key.to_owned(), hash_of(sig)),
    );
}

/// Log a use of declaration `id`'s body (a compile-time evaluation).
pub(super) fn log_body(id: FunctionId, def: &FnDef) {
    log(|| format!("b|{}", id.0), || Lookup::Body(id, hash_of(def)));
}

/// Set or remove the entry at `k`.
fn set<K: std::hash::Hash + Eq, V>(map: &mut HashMap<K, V>, k: K, v: Option<V>) {
    match v {
        Some(v) => {
            map.insert(k, v);
        }
        None => {
            map.remove(&k);
        }
    }
}

fn counts(env: &Env<'_>) -> Counts {
    let n = |x: usize| u32::try_from(x).unwrap_or(u32::MAX);
    Counts {
        next_id: env.sink.next_id.get(),
        structs: n(env.defs.structs.borrow().len()),
        enums: n(env.defs.enums.borrow().len()),
        any_tags: n(env.sink.any_tags.borrow().len()),
        any_dispatch: n(env.sink.any_dispatch.borrow().len()),
        extras: n(env.sink.extras.borrow().len()),
        infer_vars: n(env.sink.infer_vars.borrow().len()),
    }
}

/// Sizes of the shared tables before a lowering.
struct Sizes {
    diagnostics: usize,
    name_diags: usize,
    alias_uses: usize,
    unknown_spans: usize,
    uninferred: u32,
    inferred_fns: usize,
    mono_cache: usize,
    mono_sigs: usize,
    ref_out: usize,
    thunks: usize,
    fn_origin: usize,
    track_caller: usize,
    inferred_ret: usize,
}

impl Sizes {
    fn of(env: &Env<'_>) -> Self {
        let sink = &env.sink;
        Self {
            diagnostics: sink.diagnostics.borrow().len(),
            name_diags: env.names.diags.borrow().len(),
            alias_uses: env.names.alias_uses.borrow().len(),
            unknown_spans: env.names.unknown_spans.borrow().len(),
            uninferred: sink.uninferred.get(),
            inferred_fns: sink.inferred_fns.borrow().len(),
            mono_cache: sink.mono_cache.borrow().len(),
            mono_sigs: sink.mono_sigs.borrow().len(),
            ref_out: sink.ref_out.borrow().len(),
            thunks: sink.thunks.borrow().len(),
            fn_origin: sink.fn_origin.borrow().len(),
            track_caller: sink.track_caller.borrow().len(),
            inferred_ret: sink.inferred_ret.borrow().len(),
        }
    }
}

/// Whether the shared state answers `l` (read under `ids`) as it did
/// when it was logged.
fn answers(env: &Env<'_>, ids: &Ids, l: &Lookup) -> bool {
    let sink = &env.sink;
    let raw = |id: Option<FunctionId>| id.map(|i| i.0);
    let fun = |old: &Option<FunctionId>, new: Option<FunctionId>| {
        ids.same(IdKind::Function, raw(*old), raw(new))
    };
    let list = |kind, old: Vec<u32>, new: Vec<u32>| {
        old.len() == new.len()
            && old
                .into_iter()
                .zip(new)
                .all(|(o, n)| ids.same(kind, Some(o), Some(n)))
    };
    match l {
        Lookup::Mono(name, args, r) => {
            let Some(args) = ids.tys(args) else {
                return false;
            };
            let now = sink
                .mono_cache
                .borrow()
                .get(&Key::mono(name, &args))
                .copied();
            fun(r, now)
        }
        Lookup::Struct(k, r) => {
            let now = env.defs.struct_table.borrow().get(k).copied();
            ids.same(IdKind::Struct, r.map(|i| i.0), now.map(|i| i.0))
        }
        Lookup::Enum(k, r) => {
            let now = env.defs.enum_table.borrow().get(k).copied();
            ids.same(IdKind::Enum, r.map(|i| i.0), now.map(|i| i.0))
        }
        Lookup::StructInst(base, args, r) => {
            let Some(args) = ids.tys(args) else {
                return false;
            };
            let now = env
                .defs
                .struct_table
                .borrow()
                .get(&mangle_inst(base, &args))
                .copied();
            ids.same(IdKind::Struct, r.map(|i| i.0), now.map(|i| i.0))
        }
        Lookup::EnumInst(base, args, r) => {
            let Some(args) = ids.tys(args) else {
                return false;
            };
            let now = env
                .defs
                .enum_table
                .borrow()
                .get(&mangle_inst(base, &args))
                .copied();
            ids.same(IdKind::Enum, r.map(|i| i.0), now.map(|i| i.0))
        }
        Lookup::StructInsts(base, r) => {
            let now = super::LowerCtx::instantiations(&env.defs.struct_table.borrow(), base);
            list(
                IdKind::Struct,
                r.iter().map(|i| i.0).collect(),
                now.iter().map(|i| i.0).collect(),
            )
        }
        Lookup::EnumInsts(base, r) => {
            let now = super::LowerCtx::instantiations(&env.defs.enum_table.borrow(), base);
            list(
                IdKind::Enum,
                r.iter().map(|i| i.0).collect(),
                now.iter().map(|i| i.0).collect(),
            )
        }
        Lookup::Thunk(Key::Thunk(kind, target, slot, callee), r) => {
            let target = match target {
                Some(t) => match ids.map(IdKind::Function, t.0) {
                    Some(t) => Some(FunctionId(t)),
                    None => return false,
                },
                None => None,
            };
            let (Some(slot), Some(callee)) = (ids.ty(slot), ids.ty(callee)) else {
                return false;
            };
            let key = super::throws::thunk_key(kind, target, &slot, &callee);
            fun(r, sink.thunks.borrow().get(&key).copied())
        }
        Lookup::Thunk(..) => false,
        Lookup::AnyTag(ty, r) => {
            let Some(ty) = ids.ty(ty) else {
                return false;
            };
            sink.any_tags
                .borrow()
                .iter()
                .find(|(t, _)| *t == ty)
                .map(|(_, tag)| *tag)
                == *r
        }
        Lookup::AnyDispatch(recv, trait_key, method, r) => {
            let Some(recv) = ids.ty(recv) else {
                return false;
            };
            let now = sink
                .any_dispatch
                .borrow()
                .iter()
                .find(|d| d.recv_ty == recv && d.method == *method && d.trait_key == *trait_key)
                .map(|d| d.id);
            fun(r, now)
        }
        Lookup::Sig(key, h) => env.fn_table.get(key).is_some_and(|s| hash_of(s) == *h),
        Lookup::Body(id, h) => env
            .decls
            .get(id.0 as usize)
            .is_some_and(|d| hash_of(d.def()) == *h),
        Lookup::InferredRet(id, r) => {
            let Some(id) = ids.map(IdKind::Function, id.0) else {
                return false;
            };
            let now = sink.inferred_ret.borrow().get(&FunctionId(id)).cloned();
            match (r, now) {
                (None, None) | (Some(None), Some(None)) => true,
                (Some(Some(t)), Some(Some(n))) => ids.ty(t).is_some_and(|t| t == n),
                _ => false,
            }
        }
    }
}

/// Declaration `i` is plain (see the module doc).
fn is_plain(env: &Env<'_>, i: usize) -> bool {
    let id = FunctionId(u32::try_from(i).unwrap_or(u32::MAX));
    let (def, borrowed) = match &env.decls[i] {
        MethodOrFn::Fn(f) => (*f, true),
        MethodOrFn::Method { fn_def, subst, .. } => (
            &**fn_def,
            matches!(fn_def, std::borrow::Cow::Borrowed(_)) && subst.is_empty(),
        ),
    };
    borrowed
        && def.body.is_some()
        && def.generics.params.is_empty()
        && !env.infer_ret.contains(&id)
        && !def
            .attrs
            .iter()
            .any(|a| a.path == [rokc_ast::CONST_FN_ATTR])
}

/// The program's interface: everything lowering a body can see of it,
/// but the plain bodies (`bodies`) and source positions.
fn interface_key(
    env: &Env<'_>,
    bodies: &HashSet<(&str, Span)>,
    program: &Program,
    raw_uses: &[(String, rokc_core::Visibility, rokc_ast::UseTree)],
    input: &crate::HirInput,
) -> u64 {
    let mut e = Enc::new(false);
    input.fingerprint.enc(&mut e);
    e.bytes(format!("{:?}", (&input.packages, &input.lib, &input.prebuilt)).as_bytes());
    e.bytes(
        format!(
            "{} {:?} {} {} {}",
            input.check_library,
            input.root_main,
            input.inline_prebuilt,
            input.pointer_width,
            input.stdcall_system
        )
        .as_bytes(),
    );
    input.item_modules.enc(&mut e);
    e.u(raw_uses.len() as u64);
    for u in raw_uses {
        u.enc(&mut e);
    }
    let mut infer: Vec<u32> = env.infer_ret.iter().map(|id| id.0).collect();
    infer.sort_unstable();
    e.u(infer.len() as u64);
    for id in infer {
        e.u(u64::from(id));
    }
    // Files by id (spans name them by id).
    for (p, _) in env.sources.files() {
        e.bytes(p.as_bytes());
    }
    let fn_def = |f: &FnDef, e: &mut Enc| {
        // A plain declaration's body and parameters and return type are
        // read through `Lookup::Sig` (its callers) and its unit's key
        // (itself).
        if bodies.contains(&(f.name.as_str(), f.span)) {
            e.buf.push(1);
            f.vis.enc(e);
            f.attrs.enc(e);
            f.name.enc(e);
            f.generics.enc(e);
            // The parameters but a method's receiver are the signature's.
            f.params
                .first()
                .filter(|p| p.name == "self")
                .map(|p| p.by_ref)
                .enc(e);
            f.ret_ty.is_some().enc(e);
            (f.is_async, f.is_generator, f.is_unsafe).enc(e);
            match &f.throws {
                rokc_ast::ThrowsKind::None => e.u(0),
                rokc_ast::ThrowsKind::Untyped => e.u(1),
                rokc_ast::ThrowsKind::Typed(t) => e.u(2 + t.len() as u64),
            }
            f.where_clause.enc(e);
        } else {
            e.buf.push(0);
            f.enc(e);
        }
    };
    e.u(program.items.len() as u64);
    for item in &program.items {
        match item {
            Item::Fn(f) => {
                e.buf.push(0);
                fn_def(f, &mut e);
            }
            Item::Impl(imp) => {
                e.buf.push(1);
                imp.vis.enc(&mut e);
                imp.attrs.enc(&mut e);
                imp.generics.enc(&mut e);
                imp.trait_path.enc(&mut e);
                (imp.is_unsafe, imp.negative).enc(&mut e);
                imp.self_ty.enc(&mut e);
                imp.where_clause.enc(&mut e);
                imp.module.enc(&mut e);
                e.u(imp.items.len() as u64);
                for i in &imp.items {
                    match i {
                        ImplItem::Method(f) => fn_def(f, &mut e),
                        other => other.enc(&mut e),
                    }
                }
            }
            other => {
                e.buf.push(2);
                other.enc(&mut e);
            }
        }
    }
    rokc_core::hash::fast(&e.buf)
}

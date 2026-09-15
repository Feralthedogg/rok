//! Codegen units (spec 9.2.16): a program cut into parts that compile
//! to objects of their own, so an incremental build compiles only the
//! parts whose key changed and reuses the others' objects.
//!
//! A function's unit is its home module (a generic instance from a
//! library also by a hash of its type arguments): an edit to one module
//! leaves the others' units as they were. A *glue* unit holds what is
//! the whole program's: the statics, the C `main`, `rok.register_types`.
//!
//! The units of one plan agree on everything a unit cannot see alone:
//!
//! - GC type ids: one table for the program (`Plan::gc_tables`), the
//!   previous build's ids kept and new ones appended;
//! - linkage: a function another unit uses is external, and a private
//!   copy of a prebuilt package's code that is (a generic instance)
//!   gets the symbol `<symbol>.copy`, as the package's `.a` may define
//!   the same instance;
//! - the user package's hash in symbols: a placeholder
//!   ([`Plan::placeholder`]) the driver replaces in the objects, so a
//!   source edit (which changes the content hash) does not change every
//!   unit's code;
//! - the whole-program analyses (`quiet_functions`, `reentrant_functions`,
//!   the local calling convention).
//!
//! A unit's key hashes what its object depends on: its functions' MIR
//! (ids replaced by symbols and type names), the signatures and facts
//! of what it calls in other units, the statics and GC types it uses,
//! and the build's options (`salt`).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write;
use std::sync::Arc;

use rokc_core::hash::{fnv, hex, sha256};
use rokc_ir_common::{Abi, FnRole, FunctionId, Linkage};
use rokc_mir::{
    BasicBlock, DebugTy, Link, MirFunction, MirModule, MirTy, Operand, RValue, Statement,
    Terminator,
};

use crate::emit::{quiet_functions, reentrant_functions, scan_table};
use crate::mangle::{self, Pkgs};

/// Library generic instances are spread over this many units per module.
const INSTANCE_BUCKETS: u64 = 8;

/// One unit.
#[derive(Clone, Debug)]
pub struct Unit {
    /// Its home module (`#k` for an instance bucket; `<root>` the
    /// package root), or `<glue>`.
    pub name: String,
    /// The functions it defines.
    pub fns: Vec<FunctionId>,
    pub glue: bool,
    /// Hex hash of everything its object depends on.
    pub key: String,
}

/// A program's units and what they share.
pub struct Plan {
    pub units: Vec<Unit>,
    /// Every GC `ScanTable` of the program: type id `USER_TYPE_BASE +
    /// type_offset + i`.
    pub gc_tables: Vec<Vec<u32>>,
    pub core: Arc<Core>,
}

/// What a unit's emitter takes from its plan.
pub struct Core {
    pub placeholder: String,
    pub unit_of: HashMap<FunctionId, usize>,
    /// Defined in one unit, used by another (or by the glue).
    pub shared: HashSet<FunctionId>,
    /// Shared private copies: `<symbol>.copy`.
    pub renamed: HashSet<FunctionId>,
    pub quiet: Arc<HashSet<FunctionId>>,
    pub reentrant: Arc<HashSet<FunctionId>>,
    /// The functions with the module-local calling convention.
    pub local_abi: Arc<HashSet<FunctionId>>,
    /// Lazy statics: name → symbol of the initializer.
    pub lazy_statics: HashMap<String, String>,
    /// Per unit: the functions it refers to but does not define
    /// (through prebuilt bodies kept for inlining too).
    pub refs: Vec<Vec<FunctionId>>,
    /// Per unit: the statics it refers to.
    pub statics: Vec<BTreeSet<String>>,
}

/// How to plan: `salt` names the build (compiler, target, options);
/// `gc_tables`: the previous build's table (its ids are kept).
pub struct PlanOptions<'a> {
    pub salt: &'a str,
    pub gc_tables: Vec<Vec<u32>>,
    pub debug: bool,
    /// The compile's sources (spans name them).
    pub sources: &'a rokc_diagnostic::SourceMap,
}

impl Plan {
    /// The user package's hash in this plan's symbols.
    #[must_use]
    pub fn placeholder(&self) -> &str {
        &self.core.placeholder
    }
}

impl Core {
    /// Unit `u` defines `f`.
    pub fn defines(&self, u: usize, f: FunctionId) -> bool {
        self.unit_of.get(&f) == Some(&u)
    }

    /// The functions unit `u` sees: its own, and what they refer to.
    pub fn view<'m>(&self, module: &'m MirModule, u: usize) -> Vec<&'m MirFunction> {
        let refs: HashSet<FunctionId> = self.refs[u].iter().copied().collect();
        module
            .functions
            .iter()
            .filter(|f| self.defines(u, f.id) || refs.contains(&f.id))
            .collect()
    }

    /// `link` with the user package's hash the placeholder.
    pub fn hide_hash(&self, link: &mut Link) {
        for (p, h) in &mut link.packages {
            if p.is_empty() {
                h.clone_from(&self.placeholder);
            }
        }
    }
}

/// The symbol of `f` in a unit (`mangle::symbol_for`), `.copy` when
/// `renamed` (`Core::renamed`).
#[must_use]
pub fn symbol(f: &MirFunction, pkgs: &Pkgs, renamed: bool) -> String {
    copy(mangle::symbol_for(f, pkgs), renamed)
}

/// The body symbol of a C-ABI definition in a unit (`mangle::mangled`).
#[must_use]
pub fn body_symbol(f: &MirFunction, pkgs: &Pkgs, renamed: bool) -> String {
    copy(mangle::mangled(f, pkgs), renamed)
}

fn copy(s: String, renamed: bool) -> String {
    if renamed { s + ".copy" } else { s }
}

/// The units of `module`, a program (not a library, not a REPL cell).
#[must_use]
pub fn plan(module: &MirModule, opts: &PlanOptions<'_>) -> Plan {
    let link = &module.link;
    let mut placeholder = 0u32;
    while link
        .packages
        .iter()
        .any(|(p, h)| !p.is_empty() && *h == format!("{placeholder:08x}"))
    {
        placeholder += 1;
    }
    let placeholder = format!("{placeholder:08x}");
    let index: HashMap<FunctionId, usize> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, i))
        .collect();

    // Units: by home, sorted by name; the glue last.
    let mut homes: BTreeMap<String, Vec<FunctionId>> = BTreeMap::new();
    for f in &module.functions {
        if f.facts.linkage == Linkage::Defined {
            homes.entry(home(f, link)).or_default().push(f.id);
        }
    }
    let mut units: Vec<Unit> = homes
        .into_iter()
        .map(|(name, fns)| Unit {
            name,
            fns,
            glue: false,
            key: String::new(),
        })
        .collect();
    units.push(Unit {
        name: "<glue>".to_owned(),
        fns: Vec::new(),
        glue: true,
        key: String::new(),
    });
    let glue = units.len() - 1;
    let unit_of: HashMap<FunctionId, usize> = units
        .iter()
        .enumerate()
        .flat_map(|(u, unit)| unit.fns.iter().map(move |f| (*f, u)))
        .collect();

    // What each unit refers to: its functions' calls and function
    // addresses, through the bodies of prebuilt functions kept for
    // inlining (emitted with each unit that calls them).
    let mut refs: Vec<BTreeSet<FunctionId>> = vec![BTreeSet::new(); units.len()];
    let mut statics: Vec<BTreeSet<String>> = vec![BTreeSet::new(); units.len()];
    for (u, unit) in units.iter().enumerate() {
        let mut work: Vec<FunctionId> = unit.fns.clone();
        let mut seen: HashSet<FunctionId> = work.iter().copied().collect();
        while let Some(id) = work.pop() {
            let f = &module.functions[index[&id]];
            each_ref(f, &mut |r| match r {
                Ref::Fn(g) => {
                    if unit_of.get(&g) != Some(&u) {
                        refs[u].insert(g);
                    }
                    let inline = index
                        .get(&g)
                        .is_some_and(|&j| kept_body(&module.functions[j]));
                    if inline && seen.insert(g) {
                        work.push(g);
                    }
                }
                Ref::Static(s) => {
                    statics[u].insert(s.to_owned());
                }
            });
        }
    }
    // The glue calls `main` and the lazy statics' initializers.
    for f in &module.functions {
        if f.facts.role == FnRole::Main && f.facts.linkage == Linkage::Defined {
            refs[glue].insert(f.id);
        }
    }
    for s in &module.statics {
        if let Some(i) = s.init_fn.filter(|i| index.contains_key(i)) {
            refs[glue].insert(i);
        }
        statics[glue].insert(s.name.clone());
    }
    let shared: HashSet<FunctionId> = refs
        .iter()
        .flatten()
        .filter(|g| unit_of.contains_key(g))
        .copied()
        .collect();
    let renamed: HashSet<FunctionId> = shared
        .iter()
        .filter(|g| link.in_prebuilt(module.functions[index[g]].path()))
        .copied()
        .collect();

    let mut pkgs = Pkgs {
        link: link.clone(),
        ..Pkgs::default()
    };
    for (p, h) in &mut pkgs.link.packages {
        if p.is_empty() {
            h.clone_from(&placeholder);
        }
    }
    pkgs.extern_statics = module
        .statics
        .iter()
        .filter(|s| s.is_extern)
        .map(|s| s.name.clone())
        .collect();
    let symbols: HashMap<FunctionId, String> = module
        .functions
        .iter()
        .map(|f| (f.id, symbol(f, &pkgs, renamed.contains(&f.id))))
        .collect();
    pkgs.lazy_statics = module
        .statics
        .iter()
        .filter_map(|s| {
            let init = s.init_fn.and_then(|i| symbols.get(&i)).cloned();
            let init = init.or_else(|| link.in_prebuilt(&s.name).then(String::new));
            Some((s.name.clone(), init?))
        })
        .collect();
    let quiet = quiet_functions(module, &pkgs, &module.target);
    let reentrant = reentrant_functions(module);
    let local_abi = local_abi(module, link, &shared);

    // GC types: the previous build's ids, then the new tables.
    let mut gc_tables = opts.gc_tables.clone();
    let known: HashSet<Vec<u32>> = gc_tables.iter().cloned().collect();
    let mut fresh: BTreeSet<Vec<u32>> = BTreeSet::new();
    let fn_tables: HashMap<FunctionId, Vec<Vec<u32>>> = module
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| (f.id, tables(f, &module.target)))
        .collect();
    for t in fn_tables.values().flatten() {
        if !known.contains(t) {
            fresh.insert(t.clone());
        }
    }
    gc_tables.extend(fresh);

    let core = Core {
        placeholder,
        unit_of,
        shared,
        renamed,
        quiet: Arc::new(quiet),
        reentrant: Arc::new(reentrant),
        local_abi: Arc::new(local_abi),
        lazy_statics: pkgs.lazy_statics.clone(),
        refs: refs.into_iter().map(|r| r.into_iter().collect()).collect(),
        statics,
    };
    let ids: HashMap<&Vec<u32>, usize> =
        gc_tables.iter().enumerate().map(|(i, t)| (t, i)).collect();
    let fn_tables: HashMap<FunctionId, Vec<usize>> = fn_tables
        .iter()
        .map(|(f, ts)| (*f, ts.iter().map(|t| ids[t]).collect()))
        .collect();
    let shared = Shared {
        m: module,
        index: &index,
        symbols: &symbols,
        core: &core,
        tables: &fn_tables,
        init_fns: module.statics.iter().filter_map(|s| s.init_fn).collect(),
        files: opts
            .sources
            .files()
            .iter()
            .map(|(p, _)| p.clone())
            .collect(),
        gc_tables: &gc_tables,
        salt: opts.salt,
        debug: opts.debug,
    };
    // Each unit's key, on a thread per core.
    let next = std::sync::atomic::AtomicUsize::new(0);
    let keys: Vec<std::sync::Mutex<String>> =
        units.iter().map(|_| std::sync::Mutex::default()).collect();
    let cores = std::thread::available_parallelism().map_or(1, usize::from);
    std::thread::scope(|s| {
        for _ in 0..cores.min(units.len()) {
            s.spawn(|| {
                loop {
                    let u = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(unit) = units.get(u) else { break };
                    let mut k = Key {
                        b: String::new(),
                        s: &shared,
                        structs: BTreeSet::new(),
                    };
                    k.unit(u, unit);
                    let key = hex(&sha256(k.b.as_bytes()));
                    *keys[u]
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner) = key;
                }
            });
        }
    });
    for (unit, key) in units.iter_mut().zip(keys) {
        unit.key = key
            .into_inner()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
    }
    Plan {
        units,
        gc_tables,
        core: Arc::new(core),
    }
}

/// A prebuilt function whose body is here for the optimizer to inline.
fn kept_body(f: &MirFunction) -> bool {
    f.facts.linkage == Linkage::Prebuilt && !f.blocks.is_empty()
}

/// The unit `f` belongs to: the module of its item path (an instance's:
/// its generic's; a closure's: its creator's); a library instance's
/// also a bucket of its type arguments.
fn home(f: &MirFunction, link: &Link) -> String {
    let path = f.path();
    // A type's arguments (`Pair<..>__m`) or a closure (`f::{closure#0}`)
    // are not modules.
    let cut = path.find(['<', '{']).unwrap_or(path.len());
    let head = path[..cut].trim_end_matches(':');
    let module = head.rsplit_once("::").map_or("", |(m, _)| m);
    let library = link
        .packages
        .iter()
        .find(|(p, _)| p.is_empty() || Link::owns(p, path))
        .is_some_and(|(p, _)| !p.is_empty());
    match &f.facts.mono_args {
        Some(args) if library => {
            format!("{module}#{}", fnv(args.as_bytes()) % INSTANCE_BUCKETS)
        }
        _ if module.is_empty() => "<root>".to_owned(),
        _ => module.to_owned(),
    }
}

enum Ref<'a> {
    Fn(FunctionId),
    Static(&'a str),
}

/// Every function and static `f`'s body refers to.
fn each_ref<'a>(f: &'a MirFunction, out: &mut dyn FnMut(Ref<'a>)) {
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        match s {
            Statement::Assign { rvalue, .. } => match rvalue {
                RValue::Call { callee, .. } | RValue::FnAddr { callee, .. } => {
                    out(Ref::Fn(*callee));
                }
                RValue::StaticLoad { name, .. } | RValue::StaticAddr(name) => {
                    out(Ref::Static(name));
                }
                _ => {}
            },
            Statement::StaticStore { name, .. } => out(Ref::Static(name)),
            _ => {}
        }
    }
}

/// The module-local calling convention (`Emitter::local_abi_functions`)
/// of a unit build: internal functions only their own unit calls,
/// directly.
fn local_abi(module: &MirModule, link: &Link, shared: &HashSet<FunctionId>) -> HashSet<FunctionId> {
    let mut out: HashSet<FunctionId> = module
        .functions
        .iter()
        .filter(|f| {
            f.facts.linkage == Linkage::Defined
                && f.facts.role == FnRole::Plain
                && f.facts.abi == Abi::Rok
                && (link.in_prebuilt(f.path()) || f.facts.export_name.is_none())
                && !shared.contains(&f.id)
        })
        .map(|f| f.id)
        .collect();
    for s in &module.statics {
        if let Some(id) = s.init_fn {
            out.remove(&id);
        }
    }
    for f in &module.functions {
        for s in f.blocks.iter().flat_map(|b| &b.stmts) {
            if let Statement::Assign {
                rvalue: RValue::FnAddr { callee, .. },
                ..
            } = s
            {
                out.remove(callee);
            }
        }
    }
    out
}

/// The `ScanTable`s `f`'s allocations register (`gc_type_id`'s uses).
pub fn tables(f: &MirFunction, t: &rokc_mir::Target) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    for s in f.blocks.iter().flat_map(|b| &b.stmts) {
        let Statement::Assign { rvalue, .. } = s else {
            continue;
        };
        match rvalue {
            RValue::HeapBox { ty, .. } if !t.any_inline(ty) => out.push(scan_table(ty, false, t)),
            RValue::HeapAlloc { ty } => out.push(scan_table(ty, false, t)),
            RValue::BufAlloc { elem_ty, .. } if t.has_gc_ref(elem_ty) => {
                out.push(scan_table(elem_ty, true, t));
            }
            _ => {}
        }
    }
    out
}

/// What every unit's key reads.
struct Shared<'a> {
    m: &'a MirModule,
    index: &'a HashMap<FunctionId, usize>,
    symbols: &'a HashMap<FunctionId, String>,
    core: &'a Core,
    /// The GC type ids of each function's allocations.
    tables: &'a HashMap<FunctionId, Vec<usize>>,
    init_fns: HashSet<FunctionId>,
    /// Source paths by `Span::file` - 1.
    files: Vec<String>,
    gc_tables: &'a [Vec<u32>],
    salt: &'a str,
    debug: bool,
}

/// A unit's key material: text, ids replaced by build-independent names.
struct Key<'a> {
    b: String,
    s: &'a Shared<'a>,
    /// Structs the text names (their layouts follow at the end).
    structs: BTreeSet<u32>,
}

impl Key<'_> {
    fn unit(&mut self, u: usize, unit: &Unit) {
        let s = self.s;
        let (m, core) = (s.m, s.core);
        let _ = writeln!(self.b, "{}\n{}\n{}", s.salt, unit.name, unit.glue);
        // The link names the packages and what is prebuilt.
        let mut link = m.link.clone();
        core.hide_hash(&mut link);
        let _ = writeln!(self.b, "{link:?}");
        let by_symbol = |ids: &mut Vec<&MirFunction>| {
            ids.sort_by(|a, b| s.symbols[&a.id].cmp(&s.symbols[&b.id]));
        };
        let mut fns: Vec<&MirFunction> = unit
            .fns
            .iter()
            .map(|id| &m.functions[s.index[id]])
            .collect();
        by_symbol(&mut fns);
        let mut used: BTreeSet<usize> = BTreeSet::new();
        for f in fns {
            self.b.push_str("def ");
            self.decl(f);
            self.body(f);
            used.extend(s.tables.get(&f.id).into_iter().flatten());
        }
        let mut refs: Vec<&MirFunction> = core.refs[u]
            .iter()
            .filter_map(|id| s.index.get(id).map(|&i| &m.functions[i]))
            .collect();
        by_symbol(&mut refs);
        for f in refs {
            self.b.push_str("ref ");
            self.decl(f);
            if kept_body(f) {
                self.body(f);
                used.extend(s.tables.get(&f.id).into_iter().flatten());
            }
        }
        for st in m
            .statics
            .iter()
            .filter(|st| core.statics[u].contains(&st.name))
        {
            let _ = write!(
                self.b,
                "static {} {:?} {} {} {:?} ",
                st.name,
                core.lazy_statics.get(&st.name),
                st.is_mut,
                st.is_extern,
                unit.glue.then_some(&st.init)
            );
            self.ty(&st.ty);
            self.b.push('\n');
        }
        if unit.glue {
            // The registration of every type, and `main`.
            let _ = writeln!(self.b, "tables {:?}", s.gc_tables);
            for f in m.functions.iter().filter(|f| f.facts.role == FnRole::Main) {
                let _ = write!(self.b, "main {} ", s.symbols[&f.id]);
                self.ty(&f.ret_ty);
            }
        } else {
            for i in used {
                let _ = writeln!(self.b, "table {i} {:?}", s.gc_tables[i]);
            }
        }
        self.layouts();
    }

    /// What a call sees of `f`: its symbol, signature, facts and the
    /// plan's analyses.
    fn decl(&mut self, f: &MirFunction) {
        let (s, c) = (self.s, self.s.core);
        let _ = write!(
            self.b,
            "{} {:?} {} {} {} {} {} {} (",
            s.symbols[&f.id],
            f.facts,
            c.shared.contains(&f.id),
            c.renamed.contains(&f.id),
            c.quiet.contains(&f.id),
            c.reentrant.contains(&f.id),
            c.local_abi.contains(&f.id),
            s.init_fns.contains(&f.id),
        );
        for t in &f.param_tys {
            self.ty(t);
            self.b.push(',');
        }
        self.b.push_str(") ");
        self.ty(&f.ret_ty);
        self.b.push('\n');
    }

    fn body(&mut self, f: &MirFunction) {
        self.span(f.span);
        let _ = writeln!(self.b, "{:?}", f.params);
        for l in &f.locals {
            // Only `-g` shows names, and not the compiler's (`#..`).
            let name = l
                .name
                .as_deref()
                .filter(|n| self.s.debug && !n.starts_with('#'));
            let _ = write!(self.b, "{} {name:?} ", l.id.0);
            self.ty(&l.ty);
            if self.s.debug {
                if let Some(d) = self.s.m.debug.locals.get(&(f.id, l.id)) {
                    self.debug_ty(d);
                }
            }
            self.b.push('\n');
        }
        for b in &f.blocks {
            self.block(b);
        }
    }

    fn block(&mut self, b: &BasicBlock) {
        let _ = writeln!(self.b, "bb{} {:?}", b.id.0, b.params);
        for s in &b.stmts {
            self.stmt(s);
            self.b.push('\n');
        }
        match &b.terminator {
            Terminator::Goto { target, args } => {
                let _ = write!(self.b, "goto {}", target.0);
                self.operands(args);
            }
            Terminator::If {
                cond,
                then_bb,
                then_args,
                else_bb,
                else_args,
            } => {
                self.b.push_str("if ");
                self.operand(cond);
                let _ = write!(self.b, " {}", then_bb.0);
                self.operands(then_args);
                let _ = write!(self.b, " {}", else_bb.0);
                self.operands(else_args);
            }
            Terminator::Return(v) => {
                self.b.push_str("ret ");
                if let Some(v) = v {
                    self.operand(v);
                }
            }
            Terminator::Unreachable => self.b.push_str("unreachable"),
            Terminator::Suspend {
                value,
                resume,
                is_final,
            } => {
                self.b.push_str("suspend ");
                if let Some(v) = value {
                    self.operand(v);
                }
                let _ = write!(self.b, " {} {is_final}", resume.0);
            }
        }
        self.b.push('\n');
    }

    fn stmt(&mut self, s: &Statement) {
        match s {
            Statement::Assign { target, rvalue } => {
                let _ = write!(self.b, "{} = ", target.0);
                self.rvalue(rvalue);
            }
            Statement::ArrayWrite {
                array,
                index,
                value,
                elem_ty,
                len,
            } => {
                let _ = write!(self.b, "awrite {} {len} ", array.0);
                self.operand(index);
                self.operand(value);
                self.ty(elem_ty);
            }
            Statement::StorageDead(l) => {
                let _ = write!(self.b, "dead {}", l.0);
            }
            Statement::BufStore {
                buf,
                index,
                value,
                elem_ty,
            } => {
                self.b.push_str("bstore ");
                self.operand(buf);
                self.operand(index);
                self.operand(value);
                self.ty(elem_ty);
            }
            Statement::Loc(span, scope) => {
                self.b.push_str("loc ");
                self.span(*span);
                let _ = write!(self.b, "{scope:?}");
            }
            Statement::RawStore {
                addr,
                value,
                ty,
                volatile,
            } => {
                let _ = write!(self.b, "rstore {volatile} ");
                self.operand(addr);
                self.operand(value);
                self.ty(ty);
            }
            Statement::HeapStore {
                ptr,
                ty,
                index,
                value,
            } => {
                let _ = write!(self.b, "hstore {index} ");
                self.operand(ptr);
                self.operand(value);
                self.ty(ty);
            }
            Statement::StaticStore { name, value, ty } => {
                let _ = write!(self.b, "sstore {name} ");
                self.operand(value);
                self.ty(ty);
            }
            Statement::MlirRegion { params } => {
                let _ = write!(self.b, "region {params:?}");
            }
            Statement::MlirRegionEnd => self.b.push_str("endregion"),
        }
    }

    fn rvalue(&mut self, r: &RValue) {
        match r {
            RValue::Use(o) => {
                self.b.push_str("use ");
                self.operand(o);
            }
            RValue::BinOp {
                op,
                op_ty,
                lhs,
                rhs,
            } => {
                let _ = write!(self.b, "bin {op:?} ");
                self.ty(op_ty);
                self.operand(lhs);
                self.operand(rhs);
            }
            RValue::UnaryOp { op, op_ty, operand } => {
                let _ = write!(self.b, "un {op:?} ");
                self.ty(op_ty);
                self.operand(operand);
            }
            RValue::Call {
                callee,
                args,
                ret_ty,
            } => {
                self.b.push_str("call ");
                self.callee(*callee);
                self.operands(args);
                self.ty(ret_ty);
            }
            RValue::StructInit { ty, fields } => {
                self.b.push_str("struct ");
                self.ty(ty);
                self.operands(fields);
            }
            RValue::FieldRead {
                target,
                index,
                field_ty,
            } => {
                let _ = write!(self.b, "field {index} ");
                self.operand(target);
                self.ty(field_ty);
            }
            RValue::Cast {
                source,
                from_ty,
                to_ty,
            } => {
                self.b.push_str("cast ");
                self.operand(source);
                self.ty(from_ty);
                self.ty(to_ty);
            }
            RValue::Bitcast {
                source,
                from_ty,
                to_ty,
            } => {
                self.b.push_str("bitcast ");
                self.operand(source);
                self.ty(from_ty);
                self.ty(to_ty);
            }
            RValue::WithField {
                source,
                struct_ty,
                index,
                value,
            } => {
                let _ = write!(self.b, "with {index} ");
                self.operand(source);
                self.ty(struct_ty);
                self.operand(value);
            }
            RValue::ArrayInit { elem_ty, elements } => {
                self.b.push_str("array ");
                self.ty(elem_ty);
                self.operands(elements);
            }
            RValue::ArrayIndex {
                array,
                index,
                elem_ty,
                len,
            } => {
                let _ = write!(self.b, "aindex {} {len} ", array.0);
                self.operand(index);
                self.ty(elem_ty);
            }
            RValue::FnAddr { callee, fn_ty } => {
                self.b.push_str("fnaddr ");
                self.callee(*callee);
                self.ty(fn_ty);
            }
            RValue::StaticLoad { name, ty } => {
                let _ = write!(self.b, "sload {name} ");
                self.ty(ty);
            }
            RValue::HeapBox { value, ty } => {
                self.b.push_str("box ");
                self.operand(value);
                self.ty(ty);
            }
            RValue::BufAlloc { elem_ty, len } => {
                self.b.push_str("balloc ");
                self.ty(elem_ty);
                self.operand(len);
            }
            RValue::RawLoad { addr, ty, volatile } => {
                let _ = write!(self.b, "rload {volatile} ");
                self.operand(addr);
                self.ty(ty);
            }
            RValue::AddrOf(l) => {
                let _ = write!(self.b, "addr {}", l.0);
            }
            RValue::StaticAddr(name) => {
                let _ = write!(self.b, "saddr {name}");
            }
            RValue::SizeOf { ty, align } => {
                let _ = write!(self.b, "size {align} ");
                self.ty(ty);
            }
            RValue::BufLoad {
                buf,
                index,
                elem_ty,
            } => {
                self.b.push_str("bload ");
                self.operand(buf);
                self.operand(index);
                self.ty(elem_ty);
            }
            RValue::BufAtomic {
                op,
                buf,
                index,
                args,
                elem_ty,
                order,
            } => {
                let _ = write!(self.b, "batomic {op} {order:?} ");
                self.operand(buf);
                self.operand(index);
                self.operands(args);
                self.ty(elem_ty);
            }
            RValue::MlirOp {
                op,
                attrs,
                args,
                ty,
                regions,
            } => {
                let _ = write!(self.b, "mlir {op} {attrs:?} {regions} ");
                for (a, t) in args {
                    self.operand(a);
                    self.ty(t);
                }
                self.ty(ty);
            }
            RValue::HeapLoad { ptr, ty } => {
                self.b.push_str("hload ");
                self.operand(ptr);
                self.ty(ty);
            }
            RValue::HeapAlloc { ty } => {
                self.b.push_str("halloc ");
                self.ty(ty);
            }
            RValue::HeapField { ptr, ty, index } => {
                let _ = write!(self.b, "hfield {index} ");
                self.operand(ptr);
                self.ty(ty);
            }
            RValue::CallIndirect {
                callee,
                args,
                arg_tys,
                ret_ty,
                abi,
            } => {
                let _ = write!(self.b, "icall {abi:?} ");
                self.operand(callee);
                self.operands(args);
                for t in arg_tys {
                    self.ty(t);
                }
                self.ty(ret_ty);
            }
        }
    }

    fn callee(&mut self, id: FunctionId) {
        match self.s.symbols.get(&id) {
            Some(s) => {
                let _ = write!(self.b, "@{s} ");
            }
            None => {
                let _ = write!(self.b, "@?{} ", id.0);
            }
        }
    }

    fn operands(&mut self, ops: &[Operand]) {
        self.b.push('(');
        for o in ops {
            self.operand(o);
        }
        self.b.push(')');
    }

    fn operand(&mut self, o: &Operand) {
        match o {
            Operand::Const(c) => {
                let _ = write!(self.b, "{c:?} ");
            }
            Operand::Copy(l) => {
                let _ = write!(self.b, "%{} ", l.0);
            }
        }
    }

    fn span(&mut self, at: rokc_diagnostic::Span) {
        let s = self.s;
        let file = (at.file as usize)
            .checked_sub(1)
            .and_then(|i| s.files.get(i))
            .map_or("", String::as_str);
        let _ = write!(
            self.b,
            "[{file}:{}:{}:{}:{}] ",
            at.line, at.col, at.start, at.end
        );
    }

    fn ty(&mut self, t: &MirTy) {
        match t {
            MirTy::Unit => self.b.push_str("()"),
            MirTy::Prim(p) => {
                let _ = write!(self.b, "{p:?}");
            }
            MirTy::Any => self.b.push_str("any"),
            MirTy::Tuple(ts) => {
                self.b.push('(');
                for t in ts {
                    self.ty(t);
                    self.b.push(',');
                }
                self.b.push(')');
            }
            MirTy::Struct(id, fields) => {
                self.structs.insert(id.0);
                let _ = write!(self.b, "S{{{}}}{{", self.struct_name(id.0));
                for t in fields {
                    self.ty(t);
                    self.b.push(',');
                }
                self.b.push('}');
            }
            MirTy::Array(t, n) => {
                self.b.push('[');
                self.ty(t);
                let _ = write!(self.b, ";{n}]");
            }
            MirTy::Fn(ps, r) => {
                self.b.push_str("fn(");
                for t in ps {
                    self.ty(t);
                    self.b.push(',');
                }
                self.b.push_str(")->");
                self.ty(r);
            }
            MirTy::GcRef => self.b.push_str("gcref"),
            MirTy::Union(vs, words) => {
                let _ = write!(self.b, "union{words}<");
                for (tag, t) in vs {
                    let _ = write!(self.b, "{tag}:");
                    self.ty(t);
                    self.b.push(',');
                }
                self.b.push('>');
            }
            MirTy::Mlir(s) => {
                let _ = write!(self.b, "mlir<{s:?}>");
            }
        }
        self.b.push(' ');
    }

    fn struct_name(&self, id: u32) -> String {
        self.s
            .m
            .struct_keys
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("#{id}"))
    }

    fn debug_ty(&mut self, d: &DebugTy) {
        match d {
            DebugTy::Mir(t) => self.ty(t),
            DebugTy::Sum(n, t, vs) => {
                let _ = write!(self.b, "sum {n} ");
                self.ty(t);
                for (tag, name, v) in vs {
                    let _ = write!(self.b, "{tag} {name} ");
                    self.debug_ty(v);
                }
            }
            DebugTy::Buf(n, e) => {
                let _ = write!(self.b, "buf {n} ");
                self.debug_ty(e);
            }
            DebugTy::Any => self.b.push_str("dany "),
            DebugTy::Boxed(e) => {
                self.b.push_str("boxed ");
                self.debug_ty(e);
            }
            DebugTy::Cell(e) => {
                self.b.push_str("cell ");
                self.debug_ty(e);
            }
        }
    }

    /// The layout facts of the structs named so far (`#[repr]`; under
    /// `-g` the names and field types debug info shows), and under `-g`
    /// the `any` types.
    fn layouts(&mut self) {
        let mut done: BTreeSet<u32> = BTreeSet::new();
        loop {
            let todo: Vec<u32> = self.structs.difference(&done).copied().collect();
            if todo.is_empty() {
                break;
            }
            for id in todo {
                done.insert(id);
                let _ = write!(
                    self.b,
                    "struct {} {:?}",
                    self.struct_name(id),
                    self.s.m.target.reprs.get(&id)
                );
                if self.s.debug {
                    let _ = write!(self.b, " {:?}", self.s.m.struct_names.get(&id));
                    for d in self.s.m.debug.fields.get(&id).into_iter().flatten() {
                        self.debug_ty(d);
                    }
                }
                self.b.push('\n');
            }
        }
        if self.s.debug {
            let any = self.s.m.debug.any.clone();
            for (tag, name, d) in &any {
                let _ = write!(self.b, "any {tag} {name} ");
                self.debug_ty(d);
            }
        }
    }
}

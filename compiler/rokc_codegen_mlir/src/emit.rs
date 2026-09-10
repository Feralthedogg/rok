//! Standard-MLIR text emission.
//!
//! Output format follows upstream MLIR exactly. SSA value numbering is
//! local to each `func.func`. The pipeline stops here; downstream tools
//! (`mlir-opt`, `mlir-translate`, `clang`/`lld`) handle the rest.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use rokc_ir_common::{ConstVal, FunctionId, LocalId, PrimOp, PrimTy};
use rokc_mir::{BasicBlock, MirFunction, MirModule, MirTy, Operand, RValue, Statement, Terminator};

/// GC object header size (801 §8.1.1); the payload starts here.
const HEADER_SIZE: u32 = 16;
/// First compiler-assigned type id (801 §8.1.2 user range).
const GC_TYPE_BASE: u32 = 0x10000;
/// The REPL session's package hash (`"repl"`).
const REPL_PKG_HASH: &str = "7265706c";
/// Runtime type ids of a `BufAlloc` buffer (`rokr`): no traced children
/// (the string type), or every payload word a candidate reference.
const BUF_PLAIN_TYPE_ID: u32 = 1;
/// `ScanTable` `field_kind`s (802 §8.2.3): a reference to an object
/// header, a pointer into an object (`str`), an `any` (tag + payload),
/// and the implementation kind for a word that may hold a reference or
/// other bits (an enum union payload word: the collector keeps its
/// referent and never moves it).
const STRONG_REF: u32 = 0;
const INTERIOR_REF: u32 = 2;
const ANY_SLOT: u32 = 3;
const AMBIGUOUS: u32 = 5;
/// `ScanTable` `version` bit (implementation, `rokr_gc`): the table
/// describes one element of `total_size` bytes repeated over the payload
/// (a `BufAlloc` buffer).
const TABLE_ARRAY: u32 = 0x8000;
/// `gc_flags` bit of an old object not yet in the remembered set
/// (`rokr_common::object_header::FLAG_UNLOGGED`).
const GC_FLAG_UNLOGGED: u32 = 1 << 6;
/// `gc_flags` bit of an old large object whose stores mark cards
/// (`rokr_common::object_header::FLAG_CARDED`); its card table pointer
/// is the word before the header, one byte per [`GC_CARD_SHIFT`] card
/// of the object (`rokr_gc::CARD_SIZE`).
const GC_FLAG_CARDED: u32 = 1 << 7;
const GC_CARD_SHIFT: u32 = 9;
/// Objects this large go to the runtime's large-object space, never to
/// a TLAB (`rokr_gc::LOS_THRESHOLD`, 702 §7.2.3).
const LOS_THRESHOLD: u32 = 8 << 10;

pub struct Emitter {
    out: String,
    pointer_width: u32,
    // Interned string-literal globals: content → symbol name. Shared by
    // every function of the module and emitted once at module top.
    str_globals: std::collections::BTreeMap<String, String>,
    /// Unsupported constructs found while emitting. Non-empty → the
    /// module is rejected instead of shipping placeholder IR.
    pub errors: Vec<String>,
    /// Some codegen-inserted runtime check called `rok_panic`.
    uses_panic: bool,
    /// Runtime helpers codegen calls on its own (`rok_cstr_len`,
    /// `rok_str_cmp`); declared at the end unless the module declares
    /// them.
    needs: std::collections::BTreeSet<&'static str>,
    /// Some `HeapBox` (an `any Tr` payload) called `rok_gc_alloc_slow`.
    uses_alloc: bool,
    /// Payload type of each GC object type; index `i` is type id
    /// `GC_TYPE_BASE + i` and gets a `ScanTable` (802). `true`: a buffer
    /// of such elements (`BufAlloc`, an array table).
    gc_types: Vec<(MirTy, bool)>,
    /// Package hash for mangled symbols (spec 905).
    pkgs: crate::mangle::Pkgs,
    /// Panic on integer `+ - *` / negation overflow (debug builds); wrap
    /// otherwise (stdlib spec 0.5: debug=panic, release=wrap).
    pub overflow_checks: bool,
    /// C ABI used for aggregates crossing `extern "C"` (spec 8.6.3).
    pub c_target: crate::abi::CTarget,
    /// `-g`: DWARF state (spec 9.9.6).
    pub debug: Option<crate::debug::DebugInfo>,
    /// Build a REPL cell instead of a program (`crate::ReplCell`).
    pub repl: Option<crate::ReplCell>,
    /// Linking with prebuilt dependencies (`MirModule::link`).
    link: rokc_mir::Link,
}

/// Symbol + signature of a module function, for call-site typing.
pub(crate) struct FnSig {
    name: String,
    params: Vec<MirTy>,
    ret: MirTy,
    /// External C function: `str` crosses as a NUL-terminated `char*`.
    c_abi: bool,
    /// C lowering of its aggregates (`c_abi` only, spec 8.6.3).
    abi: Option<crate::abi::FnAbi>,
    /// C variadic (spec 8.6.10): an `llvm.func` called with `llvm.call`.
    variadic: bool,
    /// An `extern "C" fn` definition with aggregates (spec 5.9.10,
    /// 8.6.3): the symbol and `(params) -> ret` type of its C ABI entry
    /// (`emit_c_entry`), which C calls; `name` is the rok-ABI body.
    c_entry: Option<(String, String)>,
}

/// An external declaration other than the runtime's own `rok_*` symbols
/// uses the C ABI for `str` (a NUL-terminated `char*`); `rok_*` symbols
/// take `str` by value as `(ptr, len)` (808).
// ponytail: decided by symbol prefix because MIR has no ABI field;
// carry the extern block's ABI string through HIR/MIR when a second
// ABI appears.
fn is_c_abi(f: &MirFunction, pkgs: &crate::mangle::Pkgs) -> bool {
    f.blocks.is_empty() && !f.name.starts_with("rok_") && !pkgs.prebuilt.contains(&f.id)
}

/// An `any Tr` method dispatcher (HIR `build_dispatcher`).
fn is_any_dispatcher(name: &str) -> bool {
    name.starts_with("__any_")
}

/// `name` (a function or static path) belongs to package `pkg`.
fn owned_by(pkg: &str, name: &str) -> bool {
    name.strip_prefix(pkg).is_some_and(|r| r.starts_with("::"))
}

impl Emitter {
    #[must_use]
    pub fn new(pointer_width: u32) -> Self {
        Self {
            out: String::new(),
            pointer_width,
            str_globals: std::collections::BTreeMap::new(),
            errors: Vec::new(),
            uses_panic: false,
            needs: std::collections::BTreeSet::new(),
            uses_alloc: false,
            gc_types: Vec::new(),
            pkgs: crate::mangle::Pkgs::default(),
            overflow_checks: true,
            c_target: crate::abi::CTarget::from_triple(None),
            debug: None,
            repl: None,
            link: rokc_mir::Link::default(),
        }
    }

    /// First GC type id of this module.
    fn gc_type_base(&self) -> u32 {
        GC_TYPE_BASE + self.link.type_offset + self.repl.as_ref().map_or(0, |r| r.type_offset)
    }

    /// An `extern` static this REPL cell defines (`ReplCell::define`).
    fn defines(&self, name: &str) -> bool {
        self.repl
            .as_ref()
            .is_some_and(|r| r.define.iter().any(|d| d == name))
    }

    /// A definition kept to this object (spec 904 separate compilation):
    /// in a prebuilt library everything but the package's own items; with
    /// prebuilt dependencies, the copies of their code compiled here.
    fn private_copy(&self, name: &str) -> bool {
        match &self.link.lib {
            Some(lib) => !owned_by(lib, name) && !is_any_dispatcher(name),
            None => self.link.prebuilt.iter().any(|d| owned_by(d, name)),
        }
    }

    /// A static whose storage a prebuilt dependency's `.a` defines, or
    /// (a REPL cell) an earlier cell (`ReplCell::statics`).
    fn prebuilt_static(&self, name: &str) -> bool {
        self.link.prebuilt.iter().any(|d| owned_by(d, name))
            || self
                .repl
                .as_ref()
                .is_some_and(|r| r.statics.iter().any(|s| s == name))
    }

    /// Linkage of a static this object defines: a prebuilt library
    /// exports its package's statics (its users declare them), a REPL
    /// cell all of them (later cells use them).
    fn static_linkage(&self, name: &str) -> &'static str {
        if self.repl.is_some() || self.link.lib.as_deref().is_some_and(|l| owned_by(l, name)) {
            "external"
        } else {
            "internal"
        }
    }

    pub fn emit_module(&mut self, module: &MirModule) {
        // The user's `fn main` is renamed to its mangled symbol; the real
        // C entry point is a synthetic wrapper that brackets the user
        // body with runtime init / shutdown calls.
        let user_main = module.functions.iter().find(|f| f.name == "main");
        self.link = module.link.clone();
        if let Some(di) = self.debug.as_mut() {
            di.struct_names.clone_from(&module.struct_names);
        }
        self.pkgs.prebuilt = module.link.prebuilt_fns.iter().copied().collect();
        // Content-based package hash: the printed MIR of the whole unit.
        // Content-based package hashes (spec 0.3.3) from the driver; a
        // bare MIR module (tests) hashes its printed MIR.
        self.pkgs.extern_statics = module
            .statics
            .iter()
            .filter(|s| s.is_extern)
            .map(|s| s.name.clone())
            .collect();
        self.pkgs.hashes = if module.pkg_hashes.is_empty() {
            vec![(
                String::new(),
                crate::mangle::pkg_hash(&rokc_mir::print_mir(module)),
            )]
        } else {
            module.pkg_hashes.clone()
        };
        if self.repl.is_some() {
            // The session's package is one program: its symbols (statics
            // that later cells share) do not change with each cell's text.
            for (p, h) in &mut self.pkgs.hashes {
                if p.is_empty() {
                    REPL_PKG_HASH.clone_into(h);
                }
            }
        }

        let mut fns: HashMap<FunctionId, FnSig> = HashMap::new();
        let mut c_entries: Vec<(FunctionId, crate::abi::FnAbi)> = Vec::new();
        for f in &module.functions {
            let export = module
                .exports
                .iter()
                .find(|(id, _)| *id == f.id)
                .map(|(_, s)| s.as_str());
            let entry_abi = (module.c_defs.contains(&f.id) && !f.blocks.is_empty())
                .then(|| {
                    crate::abi::classify(self.c_target, &f.param_tys, &f.ret_ty, self.pointer_width)
                })
                .filter(|a| !a.is_trivial());
            let body = crate::mangle::symbol_for(f, &self.pkgs, export);
            let mut c_entry = None;
            if let Some(abi) = entry_abi {
                // The exported name (or `<body>.c`) is the C entry.
                let body = crate::mangle::symbol_for(f, &self.pkgs, None);
                let entry = export.map_or_else(|| format!("{body}.c"), str::to_owned);
                let (params, ret) = c_signature(
                    &FnSig {
                        name: entry.clone(),
                        params: f.param_tys.clone(),
                        ret: f.ret_ty.clone(),
                        c_abi: true,
                        abi: Some(abi.clone()),
                        variadic: false,
                        c_entry: None,
                    },
                    self.pointer_width,
                );
                let params: Vec<String> = params.into_iter().map(|(t, _)| t).collect();
                let ty = format!(
                    "({}) -> {}",
                    params.join(", "),
                    ret.unwrap_or_else(|| "()".to_owned())
                );
                c_entry = Some((entry, ty));
                c_entries.push((f.id, abi));
            }
            fns.insert(
                f.id,
                FnSig {
                    name: if c_entry.is_some() {
                        crate::mangle::symbol_for(f, &self.pkgs, None)
                    } else {
                        body
                    },
                    params: f.param_tys.clone(),
                    ret: f.ret_ty.clone(),
                    c_abi: is_c_abi(f, &self.pkgs),
                    abi: is_c_abi(f, &self.pkgs).then(|| {
                        crate::abi::classify(
                            self.c_target,
                            &f.param_tys,
                            &f.ret_ty,
                            self.pointer_width,
                        )
                    }),
                    variadic: module.c_variadic.contains(&f.id),
                    c_entry,
                },
            );
            if self.c_target == crate::abi::CTarget::Other
                && (is_c_abi(f, &self.pkgs) || module.c_defs.contains(&f.id))
                && f.param_tys
                    .iter()
                    .chain([&f.ret_ty])
                    .any(crate::abi::is_aggregate)
            {
                self.errors.push(format!(
                    "unsupported in codegen: `{}` passes a `struct` by value across the C ABI, \
                     which is only implemented for aarch64 and x86_64 targets",
                    f.name
                ));
            }
        }

        self.pkgs.lazy_statics = module
            .statics
            .iter()
            .filter_map(|s| Some((s.name.clone(), fns.get(&s.init_fn?)?.name.clone())))
            .collect();

        self.out.push_str("module {\n");
        // An `extern "C"` declaration of a symbol this module defines
        // (`#[export_name]`, spec 9.5.8) is the same function: no
        // second `func.func`.
        let defined: std::collections::HashSet<&str> = module
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .flat_map(|f| {
                let sig = &fns[&f.id];
                [
                    Some(sig.name.as_str()),
                    sig.c_entry.as_ref().map(|(e, _)| e.as_str()),
                ]
            })
            .flatten()
            .collect();
        for f in &module.functions {
            if f.blocks.is_empty() && defined.contains(fns[&f.id].name.as_str()) {
                continue;
            }
            let symbol = fns[&f.id].name.clone();
            self.emit_function(f, &symbol, &fns);
        }
        for (id, abi) in &c_entries {
            self.emit_c_entry(&fns[id], abi, module.exports.iter().any(|(e, _)| e == id));
        }
        if let Some(m) = user_main {
            let symbol = fns[&m.id].name.clone();
            if self.repl.is_some() {
                // The host already runs the runtime: register this
                // cell's types and roots, then its statements.
                let (ret, ty) = match &m.ret_ty {
                    MirTy::Unit => ("", "()".to_owned()),
                    t => ("%0 = ", mlir_type(t, self.pointer_width)),
                };
                let _ = write!(
                    self.out,
                    "  func.func @rok_repl_cell() {{\n    func.call @rok.register_types() : () -> ()\n    {ret}func.call @{symbol}() : () -> {ty}\n    func.return\n  }}\n"
                );
            } else {
                self.emit_main_wrapper(&symbol, &m.ret_ty);
            }
        }
        self.emit_gc_support(module);
        let panic_declared = module
            .functions
            .iter()
            .any(|f| f.name == "rok_panic" && f.blocks.is_empty());
        if self.uses_panic && !panic_declared {
            let _ = writeln!(
                self.out,
                "  func.func private @rok_panic({}, i{})",
                mlir_prim(PrimTy::Str, self.pointer_width),
                self.pointer_width
            );
        }
        let pw = self.pointer_width;
        let s = mlir_prim(PrimTy::Str, pw);
        for name in std::mem::take(&mut self.needs) {
            if module
                .functions
                .iter()
                .any(|f| f.name == name && f.blocks.is_empty())
            {
                continue;
            }
            let sig = match name {
                "rok_cstr_len" => format!("(!llvm.ptr) -> i{pw}"),
                "rok_str_cmp" => format!("({s}, {s}) -> i32"),
                "rok_gc_wb_slow" => format!("(i{pw})"),
                _ => unreachable!("unknown runtime helper `{name}`"),
            };
            let _ = writeln!(self.out, "  func.func private @{name}{sig}");
        }
        self.emit_static_globals(module);
        if !self.pkgs.lazy_statics.is_empty() {
            self.out.push_str(
                "  func.func private @rok_static_init_begin(!llvm.ptr) -> i32\n  func.func private @rok_static_init_end(!llvm.ptr)\n",
            );
        }
        self.emit_string_globals();
        self.out.push_str("}\n");
    }

    /// Runtime declarations the GC lowering uses, the `ScanTable`s (802)
    /// and `rok.register_types`, which the C `main` calls right after
    /// `rok_runtime_init` (802 §8.2.12).
    fn emit_gc_support(&mut self, module: &MirModule) {
        let pw = self.pointer_width;
        let declared = |name: &str| {
            module
                .functions
                .iter()
                .any(|f| f.name == name && f.blocks.is_empty())
        };
        if self.uses_alloc && !declared("rok_gc_alloc_slow") {
            let _ = writeln!(
                self.out,
                "  func.func private @rok_gc_alloc_slow(i{pw}, i{pw}, i32) -> i{pw}"
            );
        }
        self.out.push_str(
                "  llvm.mlir.global external thread_local @rok_tls_shadow_stack_top() {addr_space = 0 : i32} : !llvm.ptr\n  llvm.mlir.global external thread_local @rok_tls_yield_flag() {addr_space = 0 : i32} : i8\n",
            );
        if self.uses_alloc {
            let _ = writeln!(
                self.out,
                "  llvm.mlir.global external thread_local @rok_tls_tlab_cursor() {{addr_space = 0 : i32}} : i{pw}\n  llvm.mlir.global external thread_local @rok_tls_tlab_limit() {{addr_space = 0 : i32}} : i{pw}"
            );
        }
        if !declared("rok_runtime_yield") {
            self.out
                .push_str("  func.func private @rok_runtime_yield()\n");
        }
        if !declared("rok_gc_register_type") {
            self.out
                .push_str("  func.func private @rok_gc_register_type(i32, !llvm.ptr)\n");
        }
        let mut calls = String::new();
        for (i, (ty, array)) in self.gc_types.iter().enumerate() {
            let mut offsets = Vec::new();
            // Header {total_size u32, version u16 = 1, num_entries u16},
            // then {field_offset u32, field_kind u32} each. An array
            // table's size is the element stride, its offsets
            // element-relative.
            let (total, version) = if *array {
                gc_offsets(ty, pw, 0, &mut offsets);
                (size_align(ty, pw).0, 1 | TABLE_ARRAY)
            } else {
                gc_offsets(ty, pw, HEADER_SIZE, &mut offsets);
                (gc_object_size(ty, pw).0, 1)
            };
            let mut words = vec![total, version | ((offsets.len() as u32) << 16)];
            for (o, kind) in offsets {
                words.extend(<[u32; 2]>::from((o, kind)));
            }
            let list = words.iter().map(u32::to_string).collect::<Vec<_>>();
            let n = words.len();
            let _ = writeln!(
                self.out,
                "  llvm.mlir.global internal constant @rok.scan{i}(dense<[{}]> : tensor<{n}xi32>) {{addr_space = 0 : i32}} : !llvm.array<{n} x i32>",
                list.join(", ")
            );
            let id = self.gc_type_base() + i as u32;
            let _ = write!(
                calls,
                "    %t{i} = arith.constant {id} : i32\n    %s{i} = llvm.mlir.addressof @rok.scan{i} : !llvm.ptr\n    func.call @rok_gc_register_type(%t{i}, %s{i}) : (i32, !llvm.ptr) -> ()\n"
            );
        }
        // Statics are GC roots: every reference word of their storage.
        let mut roots = 0;
        for s in module
            .statics
            .iter()
            .filter(|s| (!s.is_extern || self.defines(&s.name)) && !self.prebuilt_static(&s.name))
        {
            let mut paths = Vec::new();
            gc_paths(&s.ty, &mut Vec::new(), &mut paths);
            let sym = self.pkgs.static_sym(&s.name);
            let ty = mlir_type(&s.ty, pw);
            for path in paths {
                let a = format!("%r{roots}");
                let _ = writeln!(calls, "    {a} = llvm.mlir.addressof @{sym} : !llvm.ptr");
                let w = if path.is_empty() {
                    a
                } else {
                    let idx = path
                        .iter()
                        .map(u32::to_string)
                        .collect::<Vec<_>>()
                        .join(", ");
                    let _ = writeln!(
                        calls,
                        "    {a}w = llvm.getelementptr {a}[0, {idx}] : (!llvm.ptr) -> !llvm.ptr, {ty}"
                    );
                    format!("{a}w")
                };
                let _ = writeln!(
                    calls,
                    "    func.call @rok_gc_add_root({w}) : (!llvm.ptr) -> ()"
                );
                roots += 1;
            }
        }
        if roots > 0 && !declared("rok_gc_add_root") {
            self.out
                .push_str("  func.func private @rok_gc_add_root(!llvm.ptr)\n");
        }
        // A prebuilt library exports its registration as
        // `rok.register_types.<pkg>`; a program's calls its dependencies'.
        for dep in &self.link.prebuilt {
            let _ = writeln!(self.out, "  func.func private @rok.register_types.{dep}()");
            let _ = writeln!(
                calls,
                "    func.call @rok.register_types.{dep}() : () -> ()"
            );
        }
        let head = match &self.link.lib {
            Some(lib) => format!("func.func @rok.register_types.{lib}"),
            None => "func.func private @rok.register_types".to_owned(),
        };
        let _ = write!(self.out, "  {head}() {{\n{calls}    func.return\n  }}\n");
    }

    fn emit_static_globals(&mut self, module: &MirModule) {
        let pw = self.pointer_width;
        for s in &module.statics {
            let ty_str = mlir_type(&s.ty, pw);
            let constness = if s.is_mut { "" } else { "constant " };
            let sym = self.pkgs.static_sym(&s.name);
            if s.is_extern && self.defines(&s.name) {
                // A REPL binding's slot: zeroed, exported.
                let _ = writeln!(
                    self.out,
                    "  llvm.mlir.global external @{sym}() {{addr_space = 0 : i32}} : {ty_str} {{\n    %0 = llvm.mlir.zero : {ty_str}\n    llvm.return %0 : {ty_str}\n  }}"
                );
                continue;
            }
            if self.prebuilt_static(&s.name) {
                // In the dependency's `.a`; a lazy one's state byte too
                // (`.init` stays a private copy here).
                let _ = writeln!(
                    self.out,
                    "  llvm.mlir.global external {constness}@{sym}() {{addr_space = 0 : i32}} : {ty_str}"
                );
                if let Some(init) = self.pkgs.lazy_statics.get(&s.name).cloned() {
                    let _ = writeln!(
                        self.out,
                        "  llvm.mlir.global external @{sym}.state() {{addr_space = 0 : i32}} : i8"
                    );
                    self.emit_lazy_init(&sym, &ty_str, &init);
                }
                continue;
            }
            if s.is_extern {
                // Defined elsewhere (spec 5.9.3): a declaration only.
                let _ = writeln!(
                    self.out,
                    "  llvm.mlir.global external {constness}@{sym}() {{addr_space = 0 : i32}} : {ty_str}"
                );
                continue;
            }
            let linkage = self.static_linkage(&s.name);
            if let Some(init) = self.pkgs.lazy_statics.get(&s.name).cloned() {
                self.emit_lazy_static(&sym, &ty_str, &init, linkage);
                continue;
            }
            if let ConstVal::Str(text) = &s.init {
                // A pointer-valued global needs an initializer region
                // that takes the literal's address.
                let lit = self.intern_global_string(text);
                let n = text.len();
                let _ = writeln!(
                    self.out,
                    "  llvm.mlir.global {linkage} {constness}@{sym}() {{addr_space = 0 : i32}} : {ty_str} {{\n    %0 = llvm.mlir.addressof @{lit} : !llvm.ptr\n    %1 = llvm.mlir.constant({n} : i{pw}) : i{pw}\n    %2 = llvm.mlir.undef : {ty_str}\n    %3 = llvm.insertvalue %0, %2[0] : {ty_str}\n    %4 = llvm.insertvalue %1, %3[1] : {ty_str}\n    llvm.return %4 : {ty_str}\n  }}"
                );
                continue;
            }
            match format_const_attr(&s.init, &s.ty, pw) {
                Some(init) => {
                    let _ = writeln!(
                        self.out,
                        "  llvm.mlir.global {linkage} {constness}@{sym}({init}) {{addr_space = 0 : i32}} : {ty_str}"
                    );
                }
                None => self.errors.push(format!(
                    "unsupported in codegen: initializer of static `{}` : `{ty_str}`",
                    s.name
                )),
            }
        }
    }

    /// A static with a non-literal initializer: zeroed storage, a state
    /// byte (0 new, 1 running, 2 ready) and `@sym.init`, which runs the
    /// initializer `init` exactly once across threads
    /// (`rok_static_init_begin` / `_end`). Every access first checks the
    /// state (`FnEmit::ensure_static_init`).
    fn emit_lazy_static(&mut self, sym: &str, ty: &str, init: &str, linkage: &str) {
        let _ = write!(
            self.out,
            "  llvm.mlir.global {linkage} @{sym}() {{addr_space = 0 : i32}} : {ty} {{
    %0 = llvm.mlir.zero : {ty}
    llvm.return %0 : {ty}
  }}
  llvm.mlir.global {linkage} @{sym}.state(0 : i8) {{addr_space = 0 : i32}} : i8
"
        );
        self.emit_lazy_init(sym, ty, init);
    }

    /// `@sym.init`: runs initializer `init` once (see `emit_lazy_static`).
    fn emit_lazy_init(&mut self, sym: &str, ty: &str, init: &str) {
        let _ = write!(
            self.out,
            "  func.func private @{sym}.init() attributes {{llvm.linkage = #llvm.linkage<internal>}} {{
    %0 = llvm.mlir.addressof @{sym}.state : !llvm.ptr
    %1 = func.call @rok_static_init_begin(%0) : (!llvm.ptr) -> i32
    %2 = arith.constant 0 : i32
    %3 = arith.cmpi ne, %1, %2 : i32
    cf.cond_br %3, ^bb1, ^bb2
  ^bb1:
    %4 = func.call @{init}() : () -> {ty}
    %5 = llvm.mlir.addressof @{sym} : !llvm.ptr
    llvm.store %4, %5 : {ty}, !llvm.ptr
    func.call @rok_static_init_end(%0) : (!llvm.ptr) -> ()
    func.return
  ^bb2:
    func.return
  }}
"
        );
    }

    fn intern_global_string(&mut self, text: &str) -> String {
        let n = self.str_globals.len();
        self.str_globals
            .entry(text.to_owned())
            .or_insert_with(|| format!("rok.str{n}"))
            .clone()
    }

    // Emit one `llvm.mlir.global` per interned string literal. The
    // literals are stored as `internal constant` byte arrays with a
    // trailing NUL so they can be passed to C-string-expecting APIs.
    fn emit_string_globals(&mut self) {
        let entries: Vec<(String, String)> = self
            .str_globals
            .iter()
            .map(|(content, sym)| (content.clone(), sym.clone()))
            .collect();
        for (content, sym) in entries {
            let bytes = content.as_bytes();
            let mut escaped = String::new();
            for &b in bytes {
                if b == b'\\' || b == b'"' {
                    escaped.push('\\');
                    escaped.push(b as char);
                } else if (0x20..0x7f).contains(&b) {
                    escaped.push(b as char);
                } else {
                    let _ = write!(escaped, "\\{:02X}", b);
                }
            }
            // `\00` terminator so `puts` / `printf` see a C string.
            let len = bytes.len() + 1;
            let _ = writeln!(
                self.out,
                "  llvm.mlir.global internal constant @{sym}(\"{escaped}\\00\") {{addr_space = 0 : i32}} : !llvm.array<{len} x i8>"
            );
        }
    }

    fn emit_function(&mut self, f: &MirFunction, symbol: &str, fns: &HashMap<FunctionId, FnSig>) {
        // Empty-body functions become external declarations — no body
        // braces, just a signature with `private` linkage.
        let is_decl = f.blocks.is_empty();
        if is_decl && is_c_abi(f, &self.pkgs) {
            self.emit_c_decl(symbol, &fns[&f.id]);
            return;
        }
        if is_decl || self.private_copy(&f.name) {
            self.out.push_str("  func.func private @");
        } else {
            self.out.push_str("  func.func @");
        }
        self.out.push_str(symbol);
        self.out.push('(');
        let c_abi = is_c_abi(f, &self.pkgs);
        for (i, _p) in f.params.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            let ty = f.param_tys.get(i).cloned().unwrap_or(MirTy::Any);
            let _ = write!(
                self.out,
                "%arg{i}: {}",
                abi_type(&ty, c_abi, self.pointer_width)
            );
        }
        self.out.push(')');
        if !matches!(f.ret_ty, MirTy::Unit) {
            let _ = write!(
                self.out,
                " -> {}",
                abi_type(&f.ret_ty, c_abi, self.pointer_width)
            );
        }
        if is_decl {
            self.out.push('\n');
            return;
        }
        if self.private_copy(&f.name) {
            // `private` is MLIR visibility only; this is the LLVM linkage.
            self.out
                .push_str(" attributes {llvm.linkage = #llvm.linkage<internal>}");
        } else if self.link.lib.is_some() && is_any_dispatcher(&f.name) {
            // The program's own (complete) dispatcher replaces it.
            self.out
                .push_str(" attributes {llvm.linkage = #llvm.linkage<weak>}");
        }
        self.out.push_str(" {\n");

        let str_globals = std::mem::take(&mut self.str_globals);
        let mut emit = FnEmit::new(f, self.pointer_width, fns, str_globals, &self.pkgs);
        emit.overflow_checks = self.overflow_checks;
        emit.c_target = self.c_target;
        emit.gc_type_base = self.gc_type_base();
        emit.gc_types = std::mem::take(&mut self.gc_types);
        if let Some(di) = self.debug.as_mut() {
            let name = f.name.split(crate::mangle::MONO_MARK).next().unwrap_or("");
            emit.dbg = di.subprogram(f, name);
            if let Some(d) = &emit.dbg {
                let lines = crate::debug::decl_lines(f);
                for l in &f.locals {
                    let Some(name) = l.name.as_deref().filter(|n| !n.starts_with('#')) else {
                        continue;
                    };
                    if emit.is_block_param(l.id) {
                        continue;
                    }
                    let arg = f.params.iter().position(|p| *p == l.id).map(|i| i + 1);
                    let (line, scope) = lines.get(&l.id.0).copied().unwrap_or((d.line, 0));
                    let scope = d.scopes.get(&scope).unwrap_or(&d.subprogram);
                    if let Some(var) = di.local(scope, f.span.file, name, &l.ty, line, arg) {
                        // LLVM puts a stack variable in the scope of its
                        // declare's location, not of the variable.
                        let at = format!("loc(fused<{scope}>[\"{}\":{line}:1])", d.file);
                        emit.dbg_vars.push((l.id.0, var, at));
                    }
                }
            }
        }
        emit.emit_prelude();
        for b in &f.blocks {
            emit.emit_block(b);
        }
        self.str_globals = std::mem::take(&mut emit.str_globals);
        self.uses_panic |= emit.uses_panic;
        self.needs.append(&mut emit.needs);
        self.uses_alloc |= emit.uses_alloc;
        self.gc_types = std::mem::take(&mut emit.gc_types);
        for e in std::mem::take(&mut emit.errors) {
            self.errors.push(format!("in `{}`: {e}", f.name));
        }
        let fn_loc = emit.dbg.as_ref().map(|d| {
            format!(
                " loc(fused<{}>[\"{}\":{}:{}])",
                d.subprogram, d.file, d.line, d.col
            )
        });
        self.out.push_str(&emit.finish());

        self.out.push_str("  }");
        self.out.push_str(fn_loc.as_deref().unwrap_or_default());
        self.out.push('\n');
    }

    /// The C ABI entry of an `extern "C" fn` definition `sig` (spec
    /// 8.6.3): takes the arguments as C passes them (coerced, by
    /// pointer, `sret`), calls the rok body with the values, returns
    /// the result the C way. Exported under `#[export_name]`, else
    /// internal (C gets it as a function pointer).
    fn emit_c_entry(&mut self, sig: &FnSig, abi: &crate::abi::FnAbi, exported: bool) {
        use crate::abi::{ArgAbi, RetAbi};
        let pw = self.pointer_width;
        let Some((entry, _)) = &sig.c_entry else {
            return;
        };
        let c = FnSig {
            name: entry.clone(),
            params: sig.params.clone(),
            ret: sig.ret.clone(),
            c_abi: true,
            abi: Some(abi.clone()),
            variadic: false,
            c_entry: None,
        };
        let (params, ret) = c_signature(&c, pw);
        let head: Vec<String> = params
            .iter()
            .enumerate()
            .map(|(i, (t, a))| format!("%arg{i}: {t}{a}"))
            .collect();
        let arrow = ret.as_ref().map(|r| format!(" -> {r}")).unwrap_or_default();
        let (vis, linkage) = if exported {
            ("", "")
        } else {
            (
                "private ",
                " attributes {llvm.linkage = #llvm.linkage<internal>}",
            )
        };
        let mut b = format!(
            "  func.func {vis}@{entry}({}){arrow}{linkage} {{
    %one = llvm.mlir.constant(1 : i32) : i32
",
            head.join(", ")
        );
        let slot = |b: &mut String, n: &str, ty: &MirTy| {
            let size = size_align(ty, pw).0.max(16);
            let _ = writeln!(
                b,
                "    {n} = llvm.alloca %one x !llvm.array<{size} x i8> {{alignment = 16 : i64}} : (i32) -> !llvm.ptr"
            );
        };
        let sret = usize::from(abi.ret == RetAbi::Sret);
        let mut vals = Vec::new();
        for (i, t) in sig.params.iter().enumerate() {
            let a = format!("%arg{}", i + sret);
            let ty = mlir_type(t, pw);
            match abi.args.get(i).unwrap_or(&ArgAbi::Direct) {
                ArgAbi::Direct => vals.push(a),
                ArgAbi::Coerce(c) => {
                    slot(&mut b, &format!("%s{i}"), t);
                    let _ = write!(
                        b,
                        "    llvm.store {a}, %s{i} : {c}, !llvm.ptr
    %v{i} = llvm.load %s{i} : !llvm.ptr -> {ty}
"
                    );
                    vals.push(format!("%v{i}"));
                }
                ArgAbi::Indirect { .. } => {
                    let _ = writeln!(b, "    %v{i} = llvm.load {a} : !llvm.ptr -> {ty}");
                    vals.push(format!("%v{i}"));
                }
            }
        }
        let tys: Vec<String> = sig.params.iter().map(|t| mlir_type(t, pw)).collect();
        let rty = mlir_type(&sig.ret, pw);
        let unit = sig.ret == MirTy::Unit;
        let _ = writeln!(
            b,
            "    {}func.call @{}({}) : ({}) -> {}",
            if unit { "" } else { "%r = " },
            sig.name,
            vals.join(", "),
            tys.join(", "),
            if unit { "()" } else { &rty }
        );
        match &abi.ret {
            _ if unit => b.push_str(
                "    func.return
",
            ),
            RetAbi::Direct => {
                let _ = writeln!(b, "    func.return %r : {rty}");
            }
            RetAbi::Coerce(c) => {
                slot(&mut b, "%rs", &sig.ret);
                let _ = write!(
                    b,
                    "    llvm.store %r, %rs : {rty}, !llvm.ptr
    %rc = llvm.load %rs : !llvm.ptr -> {c}
    func.return %rc : {c}
"
                );
            }
            RetAbi::Sret => {
                let _ = write!(
                    b,
                    "    llvm.store %r, %arg0 : {rty}, !llvm.ptr
    func.return
"
                );
            }
        }
        b.push_str(
            "  }
",
        );
        self.out.push_str(&b);
    }

    /// An `extern "C"` declaration under the platform C ABI (spec 8.6):
    /// aggregates per `abi::classify`, `str` as `char*`, small integers
    /// caller-extended, variadic ones as an `llvm.func` with `...`.
    fn emit_c_decl(&mut self, symbol: &str, sig: &FnSig) {
        let (params, ret) = c_signature(sig, self.pointer_width);
        let ret = ret.map(|r| format!(" -> {r}")).unwrap_or_default();
        let mut params: Vec<String> = params.into_iter().map(|(t, a)| t + &a).collect();
        if sig.variadic {
            params.push("...".to_owned());
            let _ = writeln!(
                self.out,
                "  llvm.func @{symbol}({}){ret}",
                params.join(", ")
            );
            return;
        }
        let params: Vec<String> = params
            .iter()
            .enumerate()
            .map(|(i, p)| format!("%arg{i}: {p}"))
            .collect();
        let _ = writeln!(
            self.out,
            "  func.func private @{symbol}({}){ret}",
            params.join(", ")
        );
    }

    // Synthetic C `main` (spec 905.9) wrapping the user's body with
    // runtime calls. Both runtime functions are forward-declared as
    // private extern.
    fn emit_main_wrapper(&mut self, user_main: &str, user_ret_ty: &MirTy) {
        let pw = self.pointer_width;
        self.out.push_str(
            "  func.func private @rok_runtime_init() -> ()\n  func.func private @rok_runtime_shutdown() -> ()\n",
        );
        self.out.push_str("  func.func @main() -> i32 {\n");
        self.out.push_str(
            "    func.call @rok_runtime_init() : () -> ()\n    func.call @rok.register_types() : () -> ()\n",
        );
        if matches!(user_ret_ty, MirTy::Unit) {
            let _ = writeln!(self.out, "    func.call @{user_main}() : () -> ()");
            self.out
                .push_str("    func.call @rok_runtime_shutdown() : () -> ()\n");
            self.out.push_str("    %0 = arith.constant 0 : i32\n");
            self.out.push_str("    func.return %0 : i32\n");
            self.out.push_str("  }\n");
            return;
        }
        let ret = mlir_type(user_ret_ty, pw);
        let _ = writeln!(self.out, "    %0 = func.call @{user_main}() : () -> {ret}");
        self.out
            .push_str("    func.call @rok_runtime_shutdown() : () -> ()\n");
        // The OS wants an `i32` exit code.
        let conv = match user_ret_ty {
            MirTy::Prim(p) if p.is_int() || *p == PrimTy::Bool => {
                let w = if *p == PrimTy::Bool {
                    1
                } else {
                    p.bit_width(pw)
                };
                match w.cmp(&32) {
                    std::cmp::Ordering::Equal => None,
                    std::cmp::Ordering::Greater => Some("arith.trunci"),
                    std::cmp::Ordering::Less if p.is_signed_int() => Some("arith.extsi"),
                    std::cmp::Ordering::Less => Some("arith.extui"),
                }
            }
            _ => {
                self.errors
                    .push(format!("unsupported in codegen: `main` returning `{ret}`"));
                None
            }
        };
        if let Some(op) = conv {
            let _ = writeln!(self.out, "    %1 = {op} %0 : {ret} to i32");
            self.out.push_str("    func.return %1 : i32\n");
        } else {
            self.out.push_str("    func.return %0 : i32\n");
        }
        self.out.push_str("  }\n");
    }

    #[must_use]
    pub fn gc_type_count(&self) -> u32 {
        self.gc_types.len() as u32
    }

    #[must_use]
    pub fn finish(self) -> String {
        match self.debug {
            Some(d) => d.defs + &self.out,
            None => self.out,
        }
    }

    #[must_use]
    pub const fn pointer_width(&self) -> u32 {
        self.pointer_width
    }
}

struct FnEmit<'a> {
    f: &'a MirFunction,
    pointer_width: u32,
    /// C ABI of the target, for calls through `extern "C" fn` pointers.
    c_target: crate::abi::CTarget,
    body: String,
    /// SSA name for each local: function/block params hold their MLIR SSA
    /// directly; stack-slotted locals hold the memref ptr value here as a
    /// fallback if a load is requested before the slot is initialised.
    local_names: Vec<Option<String>>,
    /// `Some(slot_ssa)` for stack-slotted locals; `None` for params.
    slot_names: Vec<Option<String>>,
    /// Locals whose slot is allocated via `llvm.alloca` rather than
    /// `memref.alloca` — needed for aggregate types that the memref
    /// dialect can't hold (`!llvm.struct<...>`, `!llvm.ptr`).
    llvm_slot: HashSet<u32>,
    /// One `llvm.alloca` per byte-array union type (keyed by its MLIR
    /// type), the scratch memory aggregate payload bitcasts go through.
    union_scratch: HashMap<String, String>,
    /// Set of locals that are block parameters (consumed as SSA values
    /// rather than stack-slotted).
    block_param_set: HashSet<u32>,
    next_ssa: u32,
    fns: &'a HashMap<FunctionId, FnSig>,
    /// The module-wide string table, lent to this function while it is
    /// emitted so identical literals share one global across functions.
    str_globals: std::collections::BTreeMap<String, String>,
    errors: Vec<String>,
    uses_panic: bool,
    needs: std::collections::BTreeSet<&'static str>,
    uses_alloc: bool,
    /// Lent `Emitter::gc_types`.
    gc_types: Vec<(MirTy, bool)>,
    /// `(address of rok_tls_shadow_stack_top, caller's frame)` once this
    /// function linked a shadow-stack frame; every return restores it.
    gc_frame: Option<(String, String)>,
    /// Root slot of each GC-holding block param, stored on block entry.
    gc_param_slots: HashMap<u32, String>,
    /// Counter for the extra blocks runtime checks split off.
    next_check: u32,
    pkgs: &'a crate::mangle::Pkgs,
    overflow_checks: bool,
    /// Lent `Emitter::gc_type_base()`.
    gc_type_base: u32,
    /// Blocks whose terminator takes a loop back-edge: a safepoint poll
    /// goes right before it (804 §8.4.8).
    back_edge_blocks: HashSet<u32>,
    /// Where the frame-rooted locals die (their slots are cleared there),
    /// and each block's index in `f.blocks`.
    deaths: rokc_mir::Deaths,
    block_pos: HashMap<u32, usize>,
    /// `llvm.alloca`s hoisted to the entry block (`entry_alloca`), so a
    /// scratch slot used in a loop does not grow the stack.
    entry_allocas: String,
    /// `-g`: this function's subprogram, and its described locals
    /// (local id, `#di_var` alias, the declare's location).
    dbg: Option<crate::debug::FnDebug>,
    dbg_vars: Vec<(u32, String, String)>,
    /// `__mlir_op` regions (bare 1.9): the enclosing bodies of the open
    /// regions, the text of the closed ones (the next op takes them),
    /// and root clears put off until the op is out of every region (a
    /// cleared root slot could be the local a loop region reads again).
    region_outer: Vec<String>,
    regions_closed: Vec<String>,
    region_deaths: Vec<LocalId>,
}

/// Blocks with an edge to a block on the current DFS path (a loop
/// back-edge), found by an iterative DFS from the entry block.
fn back_edge_blocks(f: &MirFunction) -> HashSet<u32> {
    let succs = |b: &BasicBlock| -> Vec<u32> {
        match &b.terminator {
            Terminator::Goto { target, .. } => vec![target.0],
            Terminator::If {
                then_bb, else_bb, ..
            } => vec![then_bb.0, else_bb.0],
            Terminator::Suspend { resume, .. } => vec![resume.0],
            Terminator::Return(_) | Terminator::Unreachable => Vec::new(),
        }
    };
    let index: HashMap<u32, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id.0, i))
        .collect();
    let mut out = HashSet::new();
    // 0 = unvisited, 1 = on the DFS path, 2 = done.
    let mut state = vec![0u8; f.blocks.len()];
    let mut stack: Vec<(usize, Vec<u32>)> = Vec::new();
    if let Some(b) = f.blocks.first() {
        state[0] = 1;
        stack.push((0, succs(b)));
    }
    while let Some((i, rest)) = stack.last_mut() {
        let i = *i;
        let Some(t) = rest.pop() else {
            state[i] = 2;
            stack.pop();
            continue;
        };
        let Some(&j) = index.get(&t) else { continue };
        if state[j] == 0 {
            state[j] = 1;
            stack.push((j, succs(&f.blocks[j])));
        } else if state[j] == 1 {
            out.insert(f.blocks[i].id.0);
        }
    }
    out
}

impl<'a> FnEmit<'a> {
    fn new(
        f: &'a MirFunction,
        pointer_width: u32,
        fns: &'a HashMap<FunctionId, FnSig>,
        str_globals: std::collections::BTreeMap<String, String>,
        pkgs: &'a crate::mangle::Pkgs,
    ) -> Self {
        // Block params are SSA values; everything else gets a stack slot.
        let mut block_param_set: HashSet<u32> = HashSet::new();
        for b in &f.blocks {
            for p in &b.params {
                block_param_set.insert(p.0);
            }
        }
        let mut local_names = vec![None; f.locals.len()];
        for (i, p) in f.params.iter().enumerate() {
            local_names[p.0 as usize] = Some(format!("%arg{i}"));
        }
        Self {
            f,
            pointer_width,
            c_target: crate::abi::CTarget::from_triple(None),
            body: String::new(),
            local_names,
            slot_names: vec![None; f.locals.len()],
            llvm_slot: HashSet::new(),
            union_scratch: HashMap::new(),
            region_outer: Vec::new(),
            regions_closed: Vec::new(),
            region_deaths: Vec::new(),
            block_param_set,
            next_ssa: 0,
            fns,
            str_globals,
            errors: Vec::new(),
            uses_panic: false,
            needs: std::collections::BTreeSet::new(),
            uses_alloc: false,
            gc_types: Vec::new(),
            gc_frame: None,
            gc_param_slots: HashMap::new(),
            next_check: 0,
            pkgs,
            overflow_checks: true,
            gc_type_base: GC_TYPE_BASE,
            back_edge_blocks: back_edge_blocks(f),
            deaths: rokc_mir::Deaths::default(),
            block_pos: f
                .blocks
                .iter()
                .enumerate()
                .map(|(i, b)| (b.id.0, i))
                .collect(),
            entry_allocas: String::new(),
            dbg: None,
            dbg_vars: Vec::new(),
        }
    }

    /// Scratch for reinterpreting an aggregate `ty` as its C coerced
    /// type: big enough for either (a coerced type is at most 16 bytes,
    /// or the HFA's own size).
    fn coerce_slot(&mut self, ty: &MirTy) -> String {
        let size = size_align(ty, self.pointer_width).0.max(16);
        self.entry_alloca(&format!("!llvm.array<{size} x i8>"), 16)
    }

    /// A stack slot of type `ty` allocated once in the entry block.
    fn entry_alloca(&mut self, ty: &str, align: u32) -> String {
        let [one, slot] = std::array::from_fn(|_| self.fresh_value());
        let _ = write!(
            self.entry_allocas,
            "    {one} = llvm.mlir.constant(1 : i32) : i32
    {slot} = llvm.alloca {one} x {ty} {{alignment = {align} : i64}} : (i32) -> !llvm.ptr
"
        );
        slot
    }

    /// Before touching a lazily initialized static: an acquire load of
    /// its state byte, and `@sym.init()` unless it reads 2 (ready).
    fn ensure_static_init(&mut self, name: &str) {
        if !self.pkgs.lazy_statics.contains_key(name) {
            return;
        }
        let sym = self.pkgs.static_sym(name);
        let n = self.next_check;
        self.next_check += 1;
        let [a, s, two, ready] = std::array::from_fn(|_| self.fresh_value());
        let _ = write!(
            self.body,
            "    {a} = llvm.mlir.addressof @{sym}.state : !llvm.ptr
    {s} = llvm.load {a} atomic acquire {{alignment = 1 : i64}} : !llvm.ptr -> i8
    {two} = arith.constant 2 : i8
    {ready} = arith.cmpi eq, {s}, {two} : i8
    cf.cond_br {ready}, ^rok_sready{n}, ^rok_sinit{n}
  ^rok_sinit{n}:
    func.call @{sym}.init() : () -> ()
    cf.br ^rok_sready{n}
  ^rok_sready{n}:
"
        );
    }

    /// A value of `ty` has words the collector traces.
    fn holds_gc_ref(&self, ty: &MirTy) -> bool {
        let mut offs = Vec::new();
        gc_offsets(ty, self.pointer_width, 0, &mut offs);
        !offs.is_empty()
    }

    /// Write barrier (704 §7.4.2, 809 §8.9.10) before storing a GC
    /// reference into the GC object `obj` at `slot` (`len` bytes): the
    /// inline fast path tests the header's `UNLOGGED | CARDED` bits (set
    /// only on old objects). `CARDED` (a large old object): mark the
    /// cards of the slot's first and last byte inline; else
    /// `rok_gc_wb_slow(obj)`. Not a safepoint. Emission continues in a
    /// fresh fall-through block.
    fn emit_write_barrier(&mut self, obj: &Operand, slot: &str, len: u32) {
        let pw = self.pointer_width;
        let obj_v = self.materialize_operand(obj, &MirTy::GcRef);
        let n = self.next_check;
        self.next_check += 1;
        self.needs.insert("rok_gc_wb_slow");
        let [hp, fp, flags, bits, masked, zero, set] = std::array::from_fn(|_| self.fresh_value());
        let [
            cbit,
            cmask,
            carded,
            ctp,
            ct,
            si,
            off,
            last,
            sh,
            i0,
            e1,
            i1,
            c0,
            c1,
            one,
        ] = std::array::from_fn(|_| self.fresh_value());
        let mask = GC_FLAG_UNLOGGED | GC_FLAG_CARDED;
        let tail = len.max(1) - 1;
        let _ = write!(
            self.body,
            "    {hp} = llvm.inttoptr {obj_v} : i{pw} to !llvm.ptr
    {fp} = llvm.getelementptr {hp}[4] : (!llvm.ptr) -> !llvm.ptr, i8
    {flags} = llvm.load {fp} atomic monotonic {{alignment = 4 : i64}} : !llvm.ptr -> i32
    {bits} = arith.constant {mask} : i32
    {masked} = arith.andi {flags}, {bits} : i32
    {zero} = arith.constant 0 : i32
    {set} = arith.cmpi ne, {masked}, {zero} : i32
    cf.cond_br {set}, ^rok_wb{n}, ^rok_wbok{n}
  ^rok_wb{n}:
    {cbit} = arith.constant {GC_FLAG_CARDED} : i32
    {cmask} = arith.andi {flags}, {cbit} : i32
    {carded} = arith.cmpi ne, {cmask}, {zero} : i32
    cf.cond_br {carded}, ^rok_wbcard{n}, ^rok_wbslow{n}
  ^rok_wbcard{n}:
    {ctp} = llvm.getelementptr {hp}[-8] : (!llvm.ptr) -> !llvm.ptr, i8
    {ct} = llvm.load {ctp} : !llvm.ptr -> !llvm.ptr
    {si} = llvm.ptrtoint {slot} : !llvm.ptr to i{pw}
    {off} = arith.subi {si}, {obj_v} : i{pw}
    {last} = arith.constant {tail} : i{pw}
    {sh} = arith.constant {GC_CARD_SHIFT} : i{pw}
    {i0} = arith.shrui {off}, {sh} : i{pw}
    {e1} = arith.addi {off}, {last} : i{pw}
    {i1} = arith.shrui {e1}, {sh} : i{pw}
    {c0} = llvm.getelementptr {ct}[{i0}] : (!llvm.ptr, i{pw}) -> !llvm.ptr, i8
    {c1} = llvm.getelementptr {ct}[{i1}] : (!llvm.ptr, i{pw}) -> !llvm.ptr, i8
    {one} = arith.constant 1 : i8
    llvm.store {one}, {c0} : i8, !llvm.ptr
    llvm.store {one}, {c1} : i8, !llvm.ptr
    cf.br ^rok_wbok{n}
  ^rok_wbslow{n}:
    func.call @rok_gc_wb_slow({obj_v}) : (i{pw}) -> ()
    cf.br ^rok_wbok{n}
  ^rok_wbok{n}:
"
        );
    }

    /// Safepoint poll (804 §8.4.1, 809 §8.9.11): a relaxed load of this
    /// thread's `rok_tls_yield_flag`, `rok_runtime_yield` when set.
    /// Emission continues in a fresh fall-through block.
    fn emit_poll(&mut self) {
        let n = self.next_check;
        self.next_check += 1;
        let [a, flag, zero, set] = std::array::from_fn(|_| self.fresh_value());
        let _ = write!(
            self.body,
            "    {a} = llvm.mlir.addressof @rok_tls_yield_flag : !llvm.ptr
    {flag} = llvm.load {a} atomic monotonic {{alignment = 1 : i64}} : !llvm.ptr -> i8
    {zero} = arith.constant 0 : i8
    {set} = arith.cmpi ne, {flag}, {zero} : i8
    cf.cond_br {set}, ^rok_yield{n}, ^rok_run{n}
  ^rok_yield{n}:
    func.call @rok_runtime_yield() : () -> ()
    cf.br ^rok_run{n}
  ^rok_run{n}:
"
        );
    }

    fn intern_string(&mut self, s: &str) -> String {
        if let Some(name) = self.str_globals.get(s) {
            return name.clone();
        }
        let name = format!("rok.str{}", self.str_globals.len());
        self.str_globals.insert(s.to_owned(), name.clone());
        name
    }

    fn is_block_param(&self, id: LocalId) -> bool {
        self.block_param_set.contains(&id.0)
    }

    /// Emit `memref.alloca` slots for every reassignable local, then
    /// store function args into their slots so subsequent loads see the
    /// initial value. Called once at the start of the entry block.
    fn emit_prelude(&mut self) {
        // `llvm.alloca` needs a size operand. Materialize a single
        // `i32 1` once and reuse it across the prelude.
        let mut alloca_size: Option<String> = None;
        for local in &self.f.locals {
            if self.is_block_param(local.id) {
                continue;
            }
            // `[T; N]` arrays use an `llvm.alloca` of `!llvm.array<N x T>`
            // uniformly. The `memref` dialect only accepts a narrow set
            // of element types, but the LLVM dialect accepts anything,
            // including nested arrays and aggregates.
            if let MirTy::Array(elem, n) = &local.ty {
                let slot = format!("%p{}", local.id.0);
                self.slot_names[local.id.0 as usize] = Some(slot.clone());
                let elem_ty = mlir_type(elem, self.pointer_width);
                let size = if let Some(s) = &alloca_size {
                    s.clone()
                } else {
                    let s = self.fresh_value();
                    let _ = writeln!(self.body, "    {s} = llvm.mlir.constant(1 : i32) : i32");
                    alloca_size = Some(s.clone());
                    s
                };
                self.llvm_slot.insert(local.id.0);
                let _ = writeln!(
                    self.body,
                    "    {slot} = llvm.alloca {size} x !llvm.array<{n} x {elem_ty}> : (i32) -> !llvm.ptr"
                );
                continue;
            }
            // `-g` keeps every scalar in an `llvm.alloca`, the address an
            // `llvm.intr.dbg.declare` describes.
            if is_memref_storable(&local.ty) && self.dbg.is_none() {
                let ty = mlir_type(&local.ty, self.pointer_width);
                let slot = format!("%p{}", local.id.0);
                self.slot_names[local.id.0 as usize] = Some(slot.clone());
                let _ = writeln!(self.body, "    {slot} = memref.alloca() : memref<{ty}>");
                continue;
            }
            // Aggregates and pointer-shaped values get an LLVM-dialect
            // slot so they can survive across loop back-edges.
            if is_llvm_storable(&local.ty) || is_memref_storable(&local.ty) {
                let ty = mlir_type(&local.ty, self.pointer_width);
                let slot = format!("%p{}", local.id.0);
                let size = if let Some(s) = &alloca_size {
                    s.clone()
                } else {
                    let s = self.fresh_value();
                    let _ = writeln!(self.body, "    {s} = llvm.mlir.constant(1 : i32) : i32");
                    alloca_size = Some(s.clone());
                    s
                };
                self.slot_names[local.id.0 as usize] = Some(slot.clone());
                self.llvm_slot.insert(local.id.0);
                let _ = writeln!(
                    self.body,
                    "    {slot} = llvm.alloca {size} x {ty} : (i32) -> !llvm.ptr"
                );
            }
        }
        // Scratch slots for aggregate payload bitcasts (allocated here,
        // in the entry block, so a bitcast in a loop doesn't grow the
        // stack).
        for b in &self.f.blocks {
            for st in &b.stmts {
                let Statement::Assign {
                    rvalue: RValue::Bitcast { from_ty, to_ty, .. },
                    ..
                } = st
                else {
                    continue;
                };
                let Some(union_ty) = [from_ty, to_ty]
                    .into_iter()
                    .find(|t| matches!(t, MirTy::Array(_, _)))
                else {
                    continue;
                };
                let ty = mlir_type(union_ty, self.pointer_width);
                if self.union_scratch.contains_key(&ty) {
                    continue;
                }
                let size = if let Some(s) = &alloca_size {
                    s.clone()
                } else {
                    let s = self.fresh_value();
                    let _ = writeln!(self.body, "    {s} = llvm.mlir.constant(1 : i32) : i32");
                    alloca_size = Some(s.clone());
                    s
                };
                let slot = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {slot} = llvm.alloca {size} x {ty} : (i32) -> !llvm.ptr"
                );
                self.union_scratch.insert(ty, slot);
            }
        }
        for (l, var, at) in std::mem::take(&mut self.dbg_vars) {
            if let (true, Some(slot)) = (
                self.llvm_slot.contains(&l),
                self.slot_names[l as usize].clone(),
            ) {
                let _ = writeln!(
                    self.body,
                    "    llvm.intr.dbg.declare {var} = {slot} : !llvm.ptr {at}"
                );
            }
        }
        self.emit_gc_frame();
        // Seed each function-arg slot with the incoming SSA arg.
        for (i, p) in self.f.params.iter().enumerate() {
            let Some(slot) = self
                .slot_names
                .get(p.0 as usize)
                .and_then(Option::as_ref)
                .cloned()
            else {
                continue;
            };
            let ty = mlir_type(&self.f.locals[p.0 as usize].ty, self.pointer_width);
            if self.llvm_slot.contains(&p.0) {
                let _ = writeln!(
                    self.body,
                    "    llvm.store %arg{i}, {slot} : {ty}, !llvm.ptr"
                );
            } else {
                let _ = writeln!(
                    self.body,
                    "    memref.store %arg{i}, {slot}[] : memref<{ty}>"
                );
            }
        }
        // Entry poll, once the frame roots the arguments.
        self.emit_poll();
    }

    /// Shadow-stack frame (704 §7.4.1) for a function that holds GC
    /// references and calls something (only calls can collect). Layout
    /// `{prev, count, slots[count]}`; each slot is the address of a word
    /// that holds a GC reference: a `GcRef` leaf of a local's stack slot,
    /// or of a block param's spill slot. The slots are zeroed here so the
    /// collector never reads garbage, then the frame becomes this
    /// thread's `rok_tls_shadow_stack_top`; every return restores it.
    /// A rooted local's slot is cleared right after its last use (MIR
    /// liveness, `rokc_mir::deaths`), so it stops retaining garbage.
    fn emit_gc_frame(&mut self) {
        // A loop's back-edge poll can stop this thread for a collection
        // mid-function, like a call.
        let calls = !self.back_edge_blocks.is_empty()
            || self.f.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
                matches!(
                    s,
                    Statement::Assign {
                        rvalue: RValue::Call { .. }
                            | RValue::CallIndirect { .. }
                            | RValue::HeapBox { .. }
                            | RValue::HeapAlloc { .. }
                            | RValue::BufAlloc { .. },
                        ..
                    }
                )
            });
        if !calls {
            return;
        }
        let pw = self.pointer_width;
        let one = self.fresh_value();
        let mut header = format!("    {one} = llvm.mlir.constant(1 : i32) : i32\n");
        let mut roots = Vec::new();
        let mut rooted = HashSet::new();
        for local in &self.f.locals {
            let mut paths = Vec::new();
            gc_paths(&local.ty, &mut Vec::new(), &mut paths);
            if paths.is_empty() {
                continue;
            }
            let id = local.id.0;
            let ty = mlir_type(&local.ty, pw);
            let slot = if self.is_block_param(local.id) {
                let s = format!("%gp{id}");
                let _ = writeln!(
                    header,
                    "    {s} = llvm.alloca {one} x {ty} : (i32) -> !llvm.ptr"
                );
                self.gc_param_slots.insert(id, s.clone());
                s
            } else if self.llvm_slot.contains(&id) {
                self.slot_names[id as usize].clone().unwrap()
            } else {
                continue; // unslotted: never holds a value across a call
            };
            rooted.insert(id);
            let zero = self.fresh_value();
            let _ = writeln!(header, "    {zero} = llvm.mlir.zero : {ty}");
            let _ = writeln!(header, "    llvm.store {zero}, {slot} : {ty}, !llvm.ptr");
            for path in paths {
                if path.is_empty() {
                    roots.push(slot.clone());
                    continue;
                }
                let a = self.fresh_value();
                let idx = path
                    .iter()
                    .map(u32::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                let _ = writeln!(
                    header,
                    "    {a} = llvm.getelementptr {slot}[0, {idx}] : (!llvm.ptr) -> !llvm.ptr, {ty}"
                );
                roots.push(a);
            }
        }
        if roots.is_empty() {
            return;
        }
        let n = roots.len();
        let frame_ty = format!("!llvm.struct<(ptr, i{pw}, array<{n} x ptr>)>");
        let [frame, tls, prev, count, f0, f1] = std::array::from_fn(|_| self.fresh_value());
        let _ = write!(
            header,
            "    {frame} = llvm.alloca {one} x {frame_ty} : (i32) -> !llvm.ptr
    {tls} = llvm.mlir.addressof @rok_tls_shadow_stack_top : !llvm.ptr
    {prev} = llvm.load {tls} : !llvm.ptr -> !llvm.ptr
    {f0} = llvm.getelementptr {frame}[0, 0] : (!llvm.ptr) -> !llvm.ptr, {frame_ty}
    llvm.store {prev}, {f0} : !llvm.ptr, !llvm.ptr
    {count} = llvm.mlir.constant({n} : i{pw}) : i{pw}
    {f1} = llvm.getelementptr {frame}[0, 1] : (!llvm.ptr) -> !llvm.ptr, {frame_ty}
    llvm.store {count}, {f1} : i{pw}, !llvm.ptr
"
        );
        for (i, r) in roots.iter().enumerate() {
            let a = self.fresh_value();
            let _ = writeln!(
                header,
                "    {a} = llvm.getelementptr {frame}[0, 2, {i}] : (!llvm.ptr) -> !llvm.ptr, {frame_ty}"
            );
            let _ = writeln!(header, "    llvm.store {r}, {a} : !llvm.ptr, !llvm.ptr");
        }
        let _ = writeln!(
            header,
            "    llvm.store {frame}, {tls} : !llvm.ptr, !llvm.ptr"
        );
        self.body.push_str(&header);
        self.gc_frame = Some((tls, prev));
        self.deaths = rokc_mir::deaths(self.f, |l| rooted.contains(&l.0));
    }

    /// Null the root slot of dead local `l` (all its `GcRef` leaves).
    fn clear_root(&mut self, l: LocalId) {
        let slot = match self.gc_param_slots.get(&l.0) {
            Some(s) => s.clone(),
            None => self.slot_names[l.0 as usize].clone().unwrap(),
        };
        let ty = mlir_type(&self.local_ty(l), self.pointer_width);
        let z = self.fresh_value();
        let _ = writeln!(self.body, "    {z} = llvm.mlir.zero : {ty}");
        let _ = writeln!(self.body, "    llvm.store {z}, {slot} : {ty}, !llvm.ptr");
    }

    /// Unlink this function's shadow-stack frame (before every return).
    fn emit_gc_frame_pop(&mut self) {
        if let Some((tls, prev)) = &self.gc_frame {
            let _ = writeln!(
                self.body,
                "    llvm.store {prev}, {tls} : !llvm.ptr, !llvm.ptr"
            );
        }
    }

    // Read a local. Block params and non-slotted locals return their SSA
    // name directly; memref-slotted locals get `memref.load`; llvm-slotted
    // locals get `llvm.load`.
    fn read_local(&mut self, id: LocalId) -> String {
        // `()` has one value and no storage: every read is a fresh one
        // (a remapped SSA name could come from a non-dominating block).
        if self.local_ty(id) == MirTy::Unit {
            let v = self.fresh_value();
            let _ = writeln!(self.body, "    {v} = llvm.mlir.zero : {UNIT_TY}");
            return v;
        }
        if self.is_block_param(id) || self.slot_names[id.0 as usize].is_none() {
            return self
                .local_names
                .get(id.0 as usize)
                .and_then(Option::as_ref)
                .cloned()
                .unwrap_or_else(|| {
                    // Truly unknown — emit a typed zero so callers stay valid.
                    let v = self.fresh_value();
                    let ty = mlir_type(&self.local_ty(id), self.pointer_width);
                    let _ = writeln!(self.body, "    {v} = arith.constant 0 : {ty}");
                    v
                });
        }
        let slot = self.slot_names[id.0 as usize].clone().unwrap();
        let v = self.fresh_value();
        let ty = mlir_type(&self.local_ty(id), self.pointer_width);
        if self.llvm_slot.contains(&id.0) {
            let _ = writeln!(self.body, "    {v} = llvm.load {slot} : !llvm.ptr -> {ty}");
        } else {
            let _ = writeln!(self.body, "    {v} = memref.load {slot}[] : memref<{ty}>");
        }
        v
    }

    fn write_local(&mut self, id: LocalId, value: &str) {
        if self.is_block_param(id) || self.local_ty(id) == MirTy::Unit {
            return;
        }
        // Non-slotted locals: just remap the SSA name.
        if self.slot_names[id.0 as usize].is_none() {
            self.local_names[id.0 as usize] = Some(value.to_owned());
            return;
        }
        let slot = self.slot_names[id.0 as usize].clone().unwrap();
        let ty = mlir_type(&self.local_ty(id), self.pointer_width);
        if self.llvm_slot.contains(&id.0) {
            let _ = writeln!(
                self.body,
                "    llvm.store {value}, {slot} : {ty}, !llvm.ptr"
            );
        } else {
            let _ = writeln!(
                self.body,
                "    memref.store {value}, {slot}[] : memref<{ty}>"
            );
        }
    }

    fn finish(self) -> String {
        let body = self.entry_allocas + &self.body;
        match &self.dbg {
            Some(d) => crate::debug::locate(&body, d),
            None => body,
        }
    }

    fn fresh_value(&mut self) -> String {
        let n = self.next_ssa;
        self.next_ssa += 1;
        format!("%{n}")
    }

    fn emit_block(&mut self, b: &BasicBlock) {
        // Multi-block functions need labels; the entry block is unlabeled
        // per MLIR convention. Block parameters appear in the header.
        if b.id.0 != 0 {
            // Allocate SSA names for block params.
            let mut header_args: Vec<String> = Vec::new();
            for p in &b.params {
                let name = self.fresh_value();
                let ty = self.local_ty(*p);
                header_args.push(format!("{name}: {}", mlir_type(&ty, self.pointer_width)));
                self.local_names[p.0 as usize] = Some(name);
            }
            if header_args.is_empty() {
                let _ = writeln!(self.body, "  ^bb{}:", b.id.0);
            } else {
                let _ = writeln!(self.body, "  ^bb{}({}):", b.id.0, header_args.join(", "));
            }
            for p in &b.params {
                if let Some(slot) = self.gc_param_slots.get(&p.0) {
                    let v = self.local_names[p.0 as usize].clone().unwrap();
                    let ty = mlir_type(&self.local_ty(*p), self.pointer_width);
                    let _ = writeln!(self.body, "    llvm.store {v}, {slot} : {ty}, !llvm.ptr");
                }
            }
        }
        let pos = self.block_pos[&b.id.0];
        for l in self.deaths.on_entry.get(pos).cloned().unwrap_or_default() {
            self.clear_root(l);
        }
        for (i, s) in b.stmts.iter().enumerate() {
            self.emit_stmt(s);
            let dead = self
                .deaths
                .after_stmt
                .get(pos)
                .map(|d| d[i].clone())
                .unwrap_or_default();
            self.region_deaths.extend(dead);
            if self.region_outer.is_empty() {
                for l in std::mem::take(&mut self.region_deaths) {
                    self.clear_root(l);
                }
            }
        }
        self.emit_terminator(b.id.0, &b.terminator);
    }

    fn emit_stmt(&mut self, s: &Statement) {
        match s {
            Statement::Assign { target, rvalue } => {
                // `[a, b, c]` writes directly into the target's
                // memref slot — no intermediate SSA value.
                if let RValue::ArrayInit { elem_ty, elements } = rvalue {
                    self.emit_array_init(*target, elem_ty, elements);
                    return;
                }
                let ty = self.local_ty(*target);
                // `let x = ();` / a unit-valued `try .. catch`: a `()`
                // copy has no value to materialize (`()` is not an MLIR
                // type).
                if ty == MirTy::Unit && matches!(rvalue, RValue::Use(_)) {
                    return;
                }
                let val = self.compute_rvalue(&ty, rvalue);
                self.write_local(*target, &val);
            }
            Statement::ArrayWrite {
                array,
                index,
                value,
                elem_ty,
                len,
            } => {
                self.emit_array_write(*array, index, value, elem_ty, *len);
            }
            Statement::Loc(sp, scope) => {
                if self.dbg.is_some() {
                    let _ = writeln!(
                        self.body,
                        "{}{} {} {}",
                        crate::debug::MARK,
                        sp.line,
                        sp.col.max(1),
                        scope.id
                    );
                }
            }
            Statement::MlirRegion { params } => {
                self.region_outer.push(std::mem::take(&mut self.body));
                let pw = self.pointer_width;
                let args: Vec<(String, MirTy)> = params
                    .iter()
                    .map(|p| (self.fresh_value(), self.local_ty(*p)))
                    .collect();
                let header: Vec<String> = args
                    .iter()
                    .map(|(v, t)| format!("{v}: {}", mlir_type(t, pw)))
                    .collect();
                let _ = writeln!(self.body, "  ^bb0({}):", header.join(", "));
                for (p, (v, _)) in params.iter().zip(&args) {
                    self.write_local(*p, v);
                }
            }
            Statement::MlirRegionEnd => {
                let outer = self.region_outer.pop().unwrap_or_default();
                let text = std::mem::replace(&mut self.body, outer);
                self.regions_closed.push(text);
            }
            // Inside a region the root stays until the liveness clear
            // after the op.
            Statement::StorageDead(_) if !self.region_outer.is_empty() => {}
            Statement::StorageDead(l) => {
                // Only a frame-rooted slot matters; zero it (all its
                // `GcRef` leaves become null).
                if self.gc_frame.is_some() && self.llvm_slot.contains(&l.0) {
                    let slot = self.slot_names[l.0 as usize].clone().unwrap();
                    let ty = mlir_type(&self.local_ty(*l), self.pointer_width);
                    let z = self.fresh_value();
                    let _ = writeln!(self.body, "    {z} = llvm.mlir.zero : {ty}");
                    let _ = writeln!(self.body, "    llvm.store {z}, {slot} : {ty}, !llvm.ptr");
                }
            }
            Statement::RawStore {
                addr,
                value,
                ty,
                volatile,
            } => {
                let p = self.raw_addr(addr);
                let v = self.materialize_operand(value, ty);
                let t = mlir_type(ty, self.pointer_width);
                let vol = if *volatile { "volatile " } else { "" };
                let _ = writeln!(self.body, "    llvm.store {vol}{v}, {p} : {t}, !llvm.ptr");
            }
            // `()` elements take no memory (`GcBuf<()>`: a unit result).
            Statement::BufStore { elem_ty, .. } if *elem_ty == MirTy::Unit => {}
            Statement::BufStore {
                buf,
                index,
                value,
                elem_ty,
            } => {
                let p = self.buf_elem_addr(buf, index, elem_ty);
                let v = self.materialize_operand(value, elem_ty);
                if self.holds_gc_ref(elem_ty) {
                    let len = size_align(elem_ty, self.pointer_width).0;
                    self.emit_write_barrier(buf, &p, len);
                }
                let ty = mlir_type(elem_ty, self.pointer_width);
                let _ = writeln!(self.body, "    llvm.store {v}, {p} : {ty}, !llvm.ptr");
            }
            Statement::HeapStore {
                ptr,
                ty,
                index,
                value,
            } => {
                let field = struct_field_tys(ty)[*index as usize].clone();
                let v = self.materialize_operand(value, &field);
                let (addr, field_ty) = self.heap_field_addr(ptr, ty, *index);
                if self.holds_gc_ref(&field) {
                    let len = size_align(&field, self.pointer_width).0;
                    self.emit_write_barrier(ptr, &addr, len);
                }
                let _ = writeln!(
                    self.body,
                    "    llvm.store {v}, {addr} : {field_ty}, !llvm.ptr"
                );
            }
            Statement::StaticStore { name, value, ty } => {
                self.ensure_static_init(name);
                let val = self.materialize_operand(value, ty);
                let ty_str = mlir_type(ty, self.pointer_width);
                let addr = self.fresh_value();
                let sym = self.pkgs.static_sym(name);
                let _ = writeln!(
                    self.body,
                    "    {addr} = llvm.mlir.addressof @{sym} : !llvm.ptr"
                );
                let _ = writeln!(
                    self.body,
                    "    llvm.store {val}, {addr} : {ty_str}, !llvm.ptr"
                );
            }
        }
    }

    fn emit_array_write(
        &mut self,
        array: LocalId,
        index: &Operand,
        value: &Operand,
        elem_ty: &MirTy,
        len: u32,
    ) {
        let Some(slot) = self.slot_names[array.0 as usize].clone() else {
            return;
        };
        let val = self.materialize_operand(value, elem_ty);
        let elem_str = mlir_type(elem_ty, self.pointer_width);
        let (idx_int, from_str) = self.checked_index(index, len);
        if self.llvm_slot.contains(&array.0) {
            // GEP into the LLVM array slot for aggregate elements.
            let ptr = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {ptr} = llvm.getelementptr {slot}[0, {idx_int}] : (!llvm.ptr, {from_str}) -> !llvm.ptr, !llvm.array<{len} x {elem_str}>"
            );
            let _ = writeln!(
                self.body,
                "    llvm.store {val}, {ptr} : {elem_str}, !llvm.ptr"
            );
            return;
        }
        let idx_index = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {idx_index} = arith.index_cast {idx_int} : {from_str} to index"
        );
        let _ = writeln!(
            self.body,
            "    memref.store {val}, {slot}[{idx_index}] : memref<{len} x {elem_str}>"
        );
    }

    fn emit_array_init(&mut self, target: LocalId, elem_ty: &MirTy, elements: &[Operand]) {
        let Some(slot) = self.slot_names[target.0 as usize].clone() else {
            return;
        };
        let len = elements.len();
        let elem_str = mlir_type(elem_ty, self.pointer_width);
        let llvm_path = self.llvm_slot.contains(&target.0);
        for (i, e) in elements.iter().enumerate() {
            let v = self.materialize_operand(e, elem_ty);
            if llvm_path {
                let ptr = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {ptr} = llvm.getelementptr {slot}[0, {i}] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<{len} x {elem_str}>"
                );
                let _ = writeln!(
                    self.body,
                    "    llvm.store {v}, {ptr} : {elem_str}, !llvm.ptr"
                );
            } else {
                let idx = self.fresh_value();
                let _ = writeln!(self.body, "    {idx} = arith.constant {i} : index");
                let _ = writeln!(
                    self.body,
                    "    memref.store {v}, {slot}[{idx}] : memref<{len} x {elem_str}>"
                );
            }
        }
    }

    /// Materialize an array index at its own integer type and panic
    /// unless `0 <= index < len` (one unsigned compare). Statically
    /// in-range constants skip the check.
    fn checked_index(&mut self, index: &Operand, len: u32) -> (String, String) {
        let ty = match index {
            Operand::Copy(id) => self.local_ty(*id),
            Operand::Const(c) => const_ty(c),
        };
        let v = self.materialize_operand(index, &ty);
        let ty_str = mlir_type(&ty, self.pointer_width);
        let in_range = const_int(index).is_some_and(|c| (0..i128::from(len)).contains(&c));
        if !in_range {
            let fail = self.cmp_const("uge", &v, i128::from(len), &ty_str);
            self.emit_check(&fail, "index out of bounds");
        }
        (v, ty_str)
    }

    // Materialise an rvalue into a single SSA name and return it.
    fn compute_rvalue(&mut self, dst_ty: &MirTy, r: &RValue) -> String {
        match r {
            RValue::Use(op) => self.materialize_operand(op, dst_ty),
            RValue::BinOp {
                op,
                op_ty,
                lhs,
                rhs,
            } => {
                let dst = self.fresh_value();
                self.emit_bin_op(&dst, dst_ty, *op, op_ty, lhs, rhs);
                dst
            }
            RValue::UnaryOp { op, op_ty, operand } => {
                let dst = self.fresh_value();
                self.emit_unary_op(&dst, dst_ty, *op, op_ty, operand);
                dst
            }
            RValue::Call { callee, args, .. } => {
                let dst = self.fresh_value();
                self.emit_call(&dst, *callee, args);
                dst
            }
            RValue::StructInit { ty, fields } => self.emit_struct_init(ty, fields),
            RValue::FieldRead {
                target,
                index,
                field_ty,
            } => self.emit_field_read(target, *index, field_ty, dst_ty),
            RValue::Cast {
                source,
                from_ty,
                to_ty,
            } => self.emit_cast(source, from_ty, to_ty),
            RValue::Bitcast {
                source,
                from_ty,
                to_ty,
            } => {
                let v = self.materialize_operand(source, from_ty);
                self.bitcast_value(v, from_ty, to_ty)
            }
            RValue::WithField {
                source,
                struct_ty,
                index,
                value,
            } => self.emit_with_field(source, struct_ty, *index, value),
            RValue::ArrayInit { .. } => {
                // Array init doesn't return an SSA value; it stores
                // into the destination slot. Routed via emit_stmt.
                self.fresh_value()
            }
            RValue::ArrayIndex {
                array,
                index,
                elem_ty,
                len,
            } => self.emit_array_index(*array, index, elem_ty, *len),
            RValue::FnAddr { callee, fn_ty } => self.emit_fn_addr(*callee, fn_ty),
            RValue::CallIndirect {
                callee,
                args,
                arg_tys,
                ret_ty,
                c_abi: false,
            } => self.emit_call_indirect(callee, args, arg_tys, ret_ty),
            RValue::CallIndirect {
                callee,
                args,
                arg_tys,
                ret_ty,
                c_abi: true,
            } => self.emit_c_call_indirect(callee, args, arg_tys, ret_ty),
            RValue::HeapBox { value, ty } => self.emit_heap_box(value, ty),
            RValue::HeapAlloc { ty } => self.emit_gc_object(ty),
            RValue::HeapField { ptr, ty, index } => {
                let (addr, field_ty) = self.heap_field_addr(ptr, ty, *index);
                let v = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {v} = llvm.load {addr} : !llvm.ptr -> {field_ty}"
                );
                v
            }
            RValue::BufAlloc { elem_ty, len } => self.emit_buf_alloc(elem_ty, len),
            RValue::RawLoad { addr, ty, volatile } => {
                let p = self.raw_addr(addr);
                let t = mlir_type(ty, self.pointer_width);
                let v = self.fresh_value();
                let vol = if *volatile { "volatile " } else { "" };
                let _ = writeln!(self.body, "    {v} = llvm.load {vol}{p} : !llvm.ptr -> {t}");
                v
            }
            RValue::SizeOf { ty, align } => {
                let pw = self.pointer_width;
                let (size, al) = size_align(ty, pw);
                let n = if *align { al } else { size };
                let v = self.fresh_value();
                let _ = writeln!(self.body, "    {v} = arith.constant {n} : i{pw}");
                v
            }
            RValue::BufLoad { elem_ty, .. } if *elem_ty == MirTy::Unit => {
                let v = self.fresh_value();
                let _ = writeln!(self.body, "    {v} = arith.constant 0 : i1");
                v
            }
            RValue::BufLoad {
                buf,
                index,
                elem_ty,
            } => {
                let p = self.buf_elem_addr(buf, index, elem_ty);
                let ty = mlir_type(elem_ty, self.pointer_width);
                let v = self.fresh_value();
                let _ = writeln!(self.body, "    {v} = llvm.load {p} : !llvm.ptr -> {ty}");
                v
            }
            RValue::BufAtomic {
                op,
                buf,
                index,
                args,
                elem_ty,
                order,
            } => self.emit_buf_atomic(op, buf, index, args, elem_ty, *order),
            RValue::MlirOp {
                op,
                attrs,
                args,
                ty,
                regions,
            } => self.emit_mlir_op(op, attrs, args, ty, *regions),
            RValue::HeapLoad { ptr, ty } => {
                let pw = self.pointer_width;
                let p = self.materialize_operand(ptr, &MirTy::GcRef);
                if self.inline_payload(ty) {
                    return self.bitcast_value(p, &MirTy::Prim(PrimTy::Usize), ty);
                }
                let [obj, addr] = std::array::from_fn(|_| self.fresh_value());
                let _ = writeln!(
                    self.body,
                    "    {obj} = llvm.inttoptr {p} : i{pw} to !llvm.ptr\n    {addr} = llvm.getelementptr {obj}[{HEADER_SIZE}] : (!llvm.ptr) -> !llvm.ptr, i8"
                );
                let dst = self.fresh_value();
                let ty_str = mlir_type(ty, pw);
                let _ = writeln!(
                    self.body,
                    "    {dst} = llvm.load {addr} : !llvm.ptr -> {ty_str}"
                );
                dst
            }
            RValue::StaticLoad { name, ty } => {
                self.ensure_static_init(name);
                let ty_str = mlir_type(ty, self.pointer_width);
                let addr = self.fresh_value();
                let sym = self.pkgs.static_sym(name);
                let _ = writeln!(
                    self.body,
                    "    {addr} = llvm.mlir.addressof @{sym} : !llvm.ptr"
                );
                let dst = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {dst} = llvm.load {addr} : !llvm.ptr -> {ty_str}"
                );
                dst
            }
        }
    }

    /// `__mlir_op` (stdlib bare 1.9): the op in MLIR's generic form,
    /// `%r = "d.op"(%a, %b) ({ ^bb0(..): .. }, ..) {name = attr} : (A, B) -> R`
    /// with the last `regions` closed. A unit result is no result (the
    /// target is never read: nothing may follow a region's terminator).
    fn emit_mlir_op(
        &mut self,
        op: &str,
        attrs: &[(String, String)],
        args: &[(Operand, MirTy)],
        ty: &MirTy,
        regions: u32,
    ) -> String {
        let pw = self.pointer_width;
        let (vals, tys): (Vec<String>, Vec<String>) = args
            .iter()
            .map(|(a, t)| (self.materialize_operand(a, t), mlir_type(t, pw)))
            .unzip();
        let attrs = if attrs.is_empty() {
            String::new()
        } else {
            let kv: Vec<String> = attrs.iter().map(|(k, v)| format!("{k} = {v}")).collect();
            format!(" {{{}}}", kv.join(", "))
        };
        let first = self.regions_closed.len() - regions as usize;
        let regions = self.regions_closed.split_off(first);
        let regions = if regions.is_empty() {
            String::new()
        } else {
            format!(" ({{\n{}    }})", regions.join("    }, {\n"))
        };
        let unit = *ty == MirTy::Unit;
        let ret = if unit {
            "()".to_owned()
        } else {
            mlir_type(ty, pw)
        };
        let v = self.fresh_value();
        let lhs = if unit {
            String::new()
        } else {
            format!("{v} = ")
        };
        let _ = writeln!(
            self.body,
            "    {lhs}\"{op}\"({}){regions}{attrs} : ({}) -> {ret}",
            vals.join(", "),
            tys.join(", ")
        );
        v
    }

    /// A `HeapBox` payload that fits the `usize` word itself (spec 2.2.2:
    /// small primitives are stored directly).
    fn inline_payload(&self, ty: &MirTy) -> bool {
        rokc_mir::any_inline(ty, self.pointer_width)
    }

    /// `rok_gc_alloc_slow(total_size, align, type_id)` + store of the
    /// payload; the object's `GcRef`. The size is computed here, not by
    /// the `gep null[1]` idiom: MLIR folds that under LLVM's default data
    /// layout (`i64` 4-aligned), which undersizes objects for the target.
    fn emit_heap_box(&mut self, value: &Operand, ty: &MirTy) -> String {
        let pw = self.pointer_width;
        let v = self.materialize_operand(value, ty);
        if self.inline_payload(ty) {
            return self.bitcast_value(v, ty, &MirTy::Prim(PrimTy::Usize));
        }
        let obj = self.emit_gc_object(ty);
        let [addr, payload] = std::array::from_fn(|_| self.fresh_value());
        let ty_str = mlir_type(ty, pw);
        let _ = write!(
            self.body,
            "    {addr} = llvm.inttoptr {obj} : i{pw} to !llvm.ptr
    {payload} = llvm.getelementptr {addr}[{HEADER_SIZE}] : (!llvm.ptr) -> !llvm.ptr, i8
    llvm.store {v}, {payload} : {ty_str}, !llvm.ptr
"
        );
        obj
    }

    /// A zeroed GC object with a `ty` payload, its type id registered
    /// with `ty`'s `ScanTable`; the object's `GcRef`. Small objects bump
    /// this thread's TLAB inline (702 §7.2.2, 809 §8.9.9) and write the
    /// header (`type_id`; `gc_word` = size, which the block heap parses
    /// by; the flags are already 0); `rok_gc_alloc_slow` otherwise.
    fn emit_gc_object(&mut self, ty: &MirTy) -> String {
        let pw = self.pointer_width;
        let type_id = self.gc_type_id(ty, false);
        let (size, align) = gc_object_size(ty, pw);
        let [total, align_v, tid] = std::array::from_fn(|_| self.fresh_value());
        self.uses_alloc = true;
        let _ = write!(
            self.body,
            "    {total} = arith.constant {size} : i{pw}
    {align_v} = arith.constant {align} : i{pw}
    {tid} = arith.constant {type_id} : i32
"
        );
        if size >= LOS_THRESHOLD || align > 8 {
            let obj = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {obj} = func.call @rok_gc_alloc_slow({total}, {align_v}, {tid}) : (i{pw}, i{pw}, i32) -> i{pw}"
            );
            return obj;
        }
        let n = self.next_check;
        self.next_check += 1;
        let [cp, lp, cur, lim, room, fits, next, hp, wp, slow, obj] =
            std::array::from_fn(|_| self.fresh_value());
        let _ = write!(
            self.body,
            "    {cp} = llvm.mlir.addressof @rok_tls_tlab_cursor : !llvm.ptr
    {lp} = llvm.mlir.addressof @rok_tls_tlab_limit : !llvm.ptr
    {cur} = llvm.load {cp} : !llvm.ptr -> i{pw}
    {lim} = llvm.load {lp} : !llvm.ptr -> i{pw}
    {room} = arith.subi {lim}, {cur} : i{pw}
    {fits} = arith.cmpi ule, {total}, {room} : i{pw}
    cf.cond_br {fits}, ^rok_afast{n}, ^rok_aslow{n}
  ^rok_afast{n}:
    {next} = arith.addi {cur}, {total} : i{pw}
    llvm.store {next}, {cp} : i{pw}, !llvm.ptr
    {hp} = llvm.inttoptr {cur} : i{pw} to !llvm.ptr
    llvm.store {tid}, {hp} : i32, !llvm.ptr
    {wp} = llvm.getelementptr {hp}[8] : (!llvm.ptr) -> !llvm.ptr, i8
    llvm.store {total}, {wp} : i{pw}, !llvm.ptr
    cf.br ^rok_aobj{n}({cur} : i{pw})
  ^rok_aslow{n}:
    {slow} = func.call @rok_gc_alloc_slow({total}, {align_v}, {tid}) : (i{pw}, i{pw}, i32) -> i{pw}
    cf.br ^rok_aobj{n}({slow} : i{pw})
  ^rok_aobj{n}({obj}: i{pw}):
"
        );
        obj
    }

    /// Address of field `index` of the `ty` (tuple) payload of GC object
    /// `ptr`, and the field's MLIR type.
    fn heap_field_addr(&mut self, ptr: &Operand, ty: &MirTy, index: u32) -> (String, String) {
        let pw = self.pointer_width;
        let p = self.materialize_operand(ptr, &MirTy::GcRef);
        let field = struct_field_tys(ty)[index as usize].clone();
        let ty_str = mlir_type(ty, pw);
        let [obj, payload, addr] = std::array::from_fn(|_| self.fresh_value());
        let _ = write!(
            self.body,
            "    {obj} = llvm.inttoptr {p} : i{pw} to !llvm.ptr
    {payload} = llvm.getelementptr {obj}[{HEADER_SIZE}] : (!llvm.ptr) -> !llvm.ptr, i8
    {addr} = llvm.getelementptr {payload}[0, {index}] : (!llvm.ptr) -> !llvm.ptr, {ty_str}
"
        );
        (addr, mlir_type(&field, pw))
    }

    /// The GC type id of `ty` objects (`array`: of buffers of `ty`
    /// elements), registered with its `ScanTable` at startup.
    fn gc_type_id(&mut self, ty: &MirTy, array: bool) -> u32 {
        let key = (ty.clone(), array);
        let index = self
            .gc_types
            .iter()
            .position(|t| *t == key)
            .unwrap_or_else(|| {
                self.gc_types.push(key);
                self.gc_types.len() - 1
            });
        self.gc_type_base + index as u32
    }

    /// `rok_gc_alloc_slow(header + len * size, align, type_id)` for a
    /// buffer of `len` `elem_ty`s (zeroed by the runtime): a byte buffer
    /// (type id 1, untraced) unless the elements hold GC references, then
    /// traced element by element through an array `ScanTable`.
    fn emit_buf_alloc(&mut self, elem_ty: &MirTy, len: &Operand) -> String {
        let pw = self.pointer_width;
        let usize_ty = MirTy::Prim(PrimTy::Usize);
        let n = self.materialize_operand(len, &usize_ty);
        let type_id = if self.holds_gc_ref(elem_ty) {
            self.gc_type_id(elem_ty, true)
        } else {
            BUF_PLAIN_TYPE_ID
        };
        let (size, align) = size_align(elem_ty, pw);
        let align = align.max(8);
        let [sz, hd, bytes, total, align_v, tid, obj] = std::array::from_fn(|_| self.fresh_value());
        self.uses_alloc = true;
        let _ = write!(
            self.body,
            "    {sz} = arith.constant {size} : i{pw}
    {hd} = arith.constant {HEADER_SIZE} : i{pw}
    {bytes} = arith.muli {n}, {sz} : i{pw}
    {total} = arith.addi {bytes}, {hd} : i{pw}
    {align_v} = arith.constant {align} : i{pw}
    {tid} = arith.constant {type_id} : i32
    {obj} = func.call @rok_gc_alloc_slow({total}, {align_v}, {tid}) : (i{pw}, i{pw}, i32) -> i{pw}
"
        );
        obj
    }

    /// Address of element `index` of buffer `buf` (header + index * size).
    /// `inttoptr` of a raw `usize` address operand.
    fn raw_addr(&mut self, addr: &Operand) -> String {
        let pw = self.pointer_width;
        let a = self.materialize_operand(addr, &MirTy::Prim(PrimTy::Usize));
        let p = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {p} = llvm.inttoptr {a} : i{pw} to !llvm.ptr"
        );
        p
    }

    /// LLVM atomics on a buffer element (stdlib 2.16.2). `bool` (`i1`)
    /// goes through its `i8` storage byte.
    /// `order`: the LLVM ordering (a `cas`: success, failure).
    fn emit_buf_atomic(
        &mut self,
        op: &str,
        buf: &Operand,
        index: &Operand,
        args: &[Operand],
        elem_ty: &MirTy,
        order: [&str; 2],
    ) -> String {
        let pw = self.pointer_width;
        let p = self.buf_elem_addr(buf, index, elem_ty);
        let ty = mlir_type(elem_ty, pw);
        let is_bool = ty == "i1";
        let at = if is_bool { "i8".to_owned() } else { ty };
        let align = size_align(elem_ty, pw).0;
        let ops: Vec<String> = args
            .iter()
            .map(|a| {
                let v = self.materialize_operand(a, elem_ty);
                if !is_bool {
                    return v;
                }
                let w = self.fresh_value();
                let _ = writeln!(self.body, "    {w} = arith.extui {v} : i1 to i8");
                w
            })
            .collect();
        let v = self.fresh_value();
        match op {
            "load" => {
                let _ = writeln!(
                    self.body,
                    "    {v} = llvm.load {p} atomic {} {{alignment = {align} : i64}} : !llvm.ptr -> {at}",
                    order[0]
                );
            }
            "cas" => {
                let r = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {r} = llvm.cmpxchg {p}, {}, {} {} {} : !llvm.ptr, {at}\n    {v} = llvm.extractvalue {r}[0] : !llvm.struct<({at}, i1)>",
                    ops[0], ops[1], order[0], order[1]
                );
            }
            _ => {
                let kw = match op {
                    "and" | "or" | "xor" => format!("_{op}"),
                    _ => op.to_owned(),
                };
                let _ = writeln!(
                    self.body,
                    "    {v} = llvm.atomicrmw {kw} {p}, {} {} : !llvm.ptr, {at}",
                    ops[0], order[0]
                );
            }
        }
        if !is_bool {
            return v;
        }
        let b = self.fresh_value();
        let _ = writeln!(self.body, "    {b} = arith.trunci {v} : i8 to i1");
        b
    }

    fn buf_elem_addr(&mut self, buf: &Operand, index: &Operand, elem_ty: &MirTy) -> String {
        let pw = self.pointer_width;
        let usize_ty = MirTy::Prim(PrimTy::Usize);
        let b = self.materialize_operand(buf, &MirTy::GcRef);
        let i = self.materialize_operand(index, &usize_ty);
        let size = size_align(elem_ty, pw).0;
        let [sz, hd, off, at, addr, p] = std::array::from_fn(|_| self.fresh_value());
        let _ = write!(
            self.body,
            "    {sz} = arith.constant {size} : i{pw}
    {hd} = arith.constant {HEADER_SIZE} : i{pw}
    {off} = arith.muli {i}, {sz} : i{pw}
    {at} = arith.addi {off}, {hd} : i{pw}
    {addr} = llvm.inttoptr {b} : i{pw} to !llvm.ptr
    {p} = llvm.getelementptr {addr}[{at}] : (!llvm.ptr, i{pw}) -> !llvm.ptr, i8
"
        );
        p
    }

    fn emit_fn_addr(&mut self, callee: FunctionId, fn_ty: &MirTy) -> String {
        let name = self.fns[&callee].name.clone();
        if self.fns[&callee].variadic {
            // An `llvm.func`: no `func.constant` of it.
            let dst = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {dst} = llvm.mlir.addressof @{name} : !llvm.ptr"
            );
            return dst;
        }
        let MirTy::Fn(args, ret) = fn_ty else {
            return self.unsupported("address of a function with a non-function type");
        };
        // `func.constant` accepts a `func.func` symbol; bridge to
        // `!llvm.ptr` so it can flow through closure structs and
        // llvm-dialect call sites.
        let typed = self.fresh_value();
        let mut name = name;
        let sig = if let Some((entry, ty)) = &self.fns[&callee].c_entry {
            // An `extern "C" fn` handed to C: its C ABI entry.
            name.clone_from(entry);
            ty.clone()
        } else if self.fns[&callee].c_abi {
            // The C declaration's own (lowered) type; calling it back
            // through the pointer from rok does not redo the C ABI.
            let (params, ret) = c_signature(&self.fns[&callee], self.pointer_width);
            let params: Vec<String> = params.into_iter().map(|(t, _)| t).collect();
            format!(
                "({}) -> {}",
                params.join(", "),
                ret.unwrap_or_else(|| "()".to_owned())
            )
        } else {
            mlir_fn_signature(args, ret, self.pointer_width)
        };
        let _ = writeln!(self.body, "    {typed} = func.constant @{name} : {sig}");
        let dst = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {dst} = builtin.unrealized_conversion_cast {typed} : {sig} to !llvm.ptr"
        );
        dst
    }

    /// A call through an `extern "C" fn` pointer (spec 5.9.4): the
    /// arguments and result take the C ABI like a direct call of an
    /// `extern` declaration (`abi::classify`, `str` as `char*`).
    fn emit_c_call_indirect(
        &mut self,
        callee: &Operand,
        args: &[Operand],
        arg_tys: &[MirTy],
        ret_ty: &MirTy,
    ) -> String {
        let pw = self.pointer_width;
        let fn_ty = MirTy::Fn(arg_tys.to_vec(), Box::new(ret_ty.clone()));
        let ptr = self.materialize_operand(callee, &fn_ty);
        let str_ty = MirTy::Prim(PrimTy::Str);
        let mut vals = Vec::with_capacity(args.len());
        for (op, t) in args.iter().zip(arg_tys) {
            let mut v = self.materialize_operand(op, t);
            if *t == str_ty {
                let p = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {p} = llvm.extractvalue {v}[0] : {}",
                    mlir_prim(PrimTy::Str, pw)
                );
                v = p;
            }
            vals.push(v);
        }
        if self.c_target == crate::abi::CTarget::Other
            && arg_tys.iter().chain([ret_ty]).any(crate::abi::is_aggregate)
        {
            return self.unsupported(
                "a `struct` by value through an `extern \"C\" fn` pointer (only aarch64 and \
                 x86_64 targets)",
            );
        }
        let abi = crate::abi::classify(self.c_target, arg_tys, ret_ty, pw);
        let sig = FnSig {
            name: String::new(),
            params: arg_tys.to_vec(),
            ret: ret_ty.clone(),
            c_abi: true,
            abi: Some(abi.clone()),
            variadic: false,
            c_entry: None,
        };
        let dst = self.fresh_value();
        self.emit_c_call(&dst, &sig, &abi, vals, arg_tys, Some(&ptr));
        dst
    }

    fn emit_call_indirect(
        &mut self,
        callee: &Operand,
        args: &[Operand],
        arg_tys: &[MirTy],
        ret_ty: &MirTy,
    ) -> String {
        let fn_ty = MirTy::Fn(arg_tys.to_vec(), Box::new(ret_ty.clone()));
        let callee_v = self.materialize_operand(callee, &fn_ty);
        let arg_vals: Vec<String> = args
            .iter()
            .zip(arg_tys.iter())
            .map(|(op, t)| self.materialize_operand(op, t))
            .collect();
        let arg_ty_list = arg_tys
            .iter()
            .map(|t| mlir_type(t, self.pointer_width))
            .collect::<Vec<_>>()
            .join(", ");
        let arg_list = arg_vals.join(", ");
        let ret = if matches!(ret_ty, MirTy::Unit) {
            "()".to_owned()
        } else {
            mlir_type(ret_ty, self.pointer_width)
        };
        if matches!(ret_ty, MirTy::Unit) {
            let _ = writeln!(
                self.body,
                "    llvm.call {callee_v}({arg_list}) : !llvm.ptr, ({arg_ty_list}) -> ()"
            );
            let dst = self.fresh_value();
            let _ = writeln!(self.body, "    {dst} = arith.constant 0 : i1");
            dst
        } else {
            let dst = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {dst} = llvm.call {callee_v}({arg_list}) : !llvm.ptr, ({arg_ty_list}) -> {ret}"
            );
            dst
        }
    }

    fn emit_array_index(
        &mut self,
        array: LocalId,
        index: &Operand,
        elem_ty: &MirTy,
        len: u32,
    ) -> String {
        let slot = self
            .slot_names
            .get(array.0 as usize)
            .and_then(Option::as_ref)
            .cloned()
            .unwrap_or_default();
        let elem_str = mlir_type(elem_ty, self.pointer_width);
        let (idx_int, from_str) = self.checked_index(index, len);
        if self.llvm_slot.contains(&array.0) {
            let ptr = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {ptr} = llvm.getelementptr {slot}[0, {idx_int}] : (!llvm.ptr, {from_str}) -> !llvm.ptr, !llvm.array<{len} x {elem_str}>"
            );
            let dst = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {dst} = llvm.load {ptr} : !llvm.ptr -> {elem_str}"
            );
            return dst;
        }
        let idx_index = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {idx_index} = arith.index_cast {idx_int} : {from_str} to index"
        );
        let dst = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {dst} = memref.load {slot}[{idx_index}] : memref<{len} x {elem_str}>"
        );
        dst
    }

    // `llvm.insertvalue` writes one element of an aggregate, returning
    // a new aggregate value (no in-place mutation).
    fn emit_with_field(
        &mut self,
        source: &Operand,
        struct_ty: &MirTy,
        index: u32,
        value: &Operand,
    ) -> String {
        let src_v = self.materialize_operand(source, struct_ty);
        let field_tys = struct_field_tys(struct_ty);
        let val_ty = field_tys.get(index as usize).cloned().unwrap_or(MirTy::Any);
        let v = self.materialize_operand(value, &val_ty);
        let ty_str = mlir_type(struct_ty, self.pointer_width);
        let dst = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {dst} = llvm.insertvalue {v}, {src_v}[{index}] : {ty_str}"
        );
        dst
    }

    // Integer width adjust. Wider via signed/unsigned extend, narrower
    // via truncate. Same-size acts as a no-op alias.
    fn emit_cast(&mut self, source: &Operand, from_ty: &MirTy, to_ty: &MirTy) -> String {
        let v = self.materialize_operand(source, from_ty);
        self.cast_value(v, from_ty, to_ty)
    }

    fn cast_value(&mut self, v: String, from_ty: &MirTy, to_ty: &MirTy) -> String {
        let from = mlir_type(from_ty, self.pointer_width);
        let to = mlir_type(to_ty, self.pointer_width);
        if from == to {
            return v;
        }
        // A C function pointer as an address (the null niche's test).
        if let (MirTy::Fn(..), MirTy::Prim(_)) = (from_ty, to_ty) {
            let pw = self.pointer_width;
            let addr = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {addr} = llvm.ptrtoint {v} : !llvm.ptr to i{pw}"
            );
            return self.cast_value(addr, &MirTy::Prim(PrimTy::Usize), to_ty);
        }
        let (MirTy::Prim(fp), MirTy::Prim(tp)) = (from_ty, to_ty) else {
            return self.unsupported(&format!("cast from `{from}` to `{to}`"));
        };
        if matches!(fp, PrimTy::Str) || matches!(tp, PrimTy::Str) {
            return self.unsupported(&format!("cast from `{from}` to `{to}`"));
        }
        let dst = self.fresh_value();
        // Bool participates in cast logic as a 1-bit unsigned int. The
        // is_int helpers don't include it (operator dispatch wants Bool
        // separate), so widen the int classification locally.
        let from_int_like = fp.is_int() || matches!(fp, PrimTy::Bool);
        let to_int_like = tp.is_int() || matches!(tp, PrimTy::Bool);
        // Pick the right arith op for each four-way (int/float) combination.
        match (from_int_like, to_int_like, fp.is_float(), tp.is_float()) {
            (true, true, _, _) => {
                // `bit_width` for bool reports 8 because it represents
                // storage size, but the codegen type is i1. Use 1
                // explicitly here so the ext/trunc decision is right.
                let bool_aware = |p: PrimTy| -> u32 {
                    if matches!(p, PrimTy::Bool) {
                        1
                    } else {
                        p.bit_width(self.pointer_width)
                    }
                };
                let from_w = bool_aware(*fp);
                let to_w = bool_aware(*tp);
                match to_w.cmp(&from_w) {
                    std::cmp::Ordering::Greater => {
                        // i1 / u-types zero-extend; signed-int sign-extend.
                        let mn = if matches!(fp, PrimTy::Bool) || !fp.is_signed_int() {
                            "arith.extui"
                        } else {
                            "arith.extsi"
                        };
                        let _ = writeln!(self.body, "    {dst} = {mn} {v} : {from} to {to}");
                    }
                    std::cmp::Ordering::Less => {
                        if matches!(tp, PrimTy::Bool) {
                            // Truncating to i1 — use a comparison with 0
                            // since `arith.trunci ... to i1` is supported
                            // but `cmpi ne` is more explicit about intent.
                            let zero = self.fresh_value();
                            let _ = writeln!(self.body, "    {zero} = arith.constant 0 : {from}");
                            let _ = writeln!(
                                self.body,
                                "    {dst} = arith.cmpi ne, {v}, {zero} : {from}"
                            );
                        } else {
                            let _ = writeln!(
                                self.body,
                                "    {dst} = arith.trunci {v} : {from} to {to}"
                            );
                        }
                    }
                    std::cmp::Ordering::Equal => {
                        return self.unsupported(&format!("cast from `{from}` to `{to}`"));
                    }
                }
            }
            (false, true, true, false) => {
                // float → int.
                let mn = if tp.is_signed_int() {
                    "arith.fptosi"
                } else {
                    "arith.fptoui"
                };
                let _ = writeln!(self.body, "    {dst} = {mn} {v} : {from} to {to}");
            }
            (true, false, false, true) => {
                // int → float.
                let mn = if fp.is_signed_int() {
                    "arith.sitofp"
                } else {
                    "arith.uitofp"
                };
                let _ = writeln!(self.body, "    {dst} = {mn} {v} : {from} to {to}");
            }
            (false, false, true, true) => {
                // float → float.
                let from_w = fp.bit_width(self.pointer_width);
                let to_w = tp.bit_width(self.pointer_width);
                match to_w.cmp(&from_w) {
                    std::cmp::Ordering::Greater => {
                        let _ = writeln!(self.body, "    {dst} = arith.extf {v} : {from} to {to}");
                    }
                    std::cmp::Ordering::Less => {
                        let _ =
                            writeln!(self.body, "    {dst} = arith.truncf {v} : {from} to {to}");
                    }
                    std::cmp::Ordering::Equal => {
                        return self.unsupported(&format!("cast from `{from}` to `{to}`"));
                    }
                }
            }
            _ => return self.unsupported(&format!("cast from `{from}` to `{to}`")),
        }
        dst
    }

    /// Bit-preserving scalar move (payload slot ↔ variant type): floats
    /// are reinterpreted as same-width ints, ints zero-extend into a
    /// wider slot and truncate back out.
    fn bitcast_value(&mut self, v: String, from_ty: &MirTy, to_ty: &MirTy) -> String {
        let pw = self.pointer_width;
        // `()` carries no bits: going in, the slot just reads zero; coming
        // out, it is the one unit value.
        if *from_ty == MirTy::Unit || *to_ty == MirTy::Unit {
            let n = self.fresh_value();
            let to = mlir_type(to_ty, pw);
            let _ = writeln!(self.body, "    {n} = llvm.mlir.zero : {to}");
            return n;
        }
        let (MirTy::Prim(fp), MirTy::Prim(tp)) = (from_ty, to_ty) else {
            // Byte-array union: store as one type, load as the other.
            let (from, to) = (mlir_type(from_ty, pw), mlir_type(to_ty, pw));
            let scratch = self
                .union_scratch
                .get(&from)
                .or_else(|| self.union_scratch.get(&to))
                .cloned();
            let Some(slot) = scratch else {
                return self.unsupported(&format!("payload of `{from}` stored as `{to}`"));
            };
            let _ = writeln!(self.body, "    llvm.store {v}, {slot} : {from}, !llvm.ptr");
            let n = self.fresh_value();
            let _ = writeln!(self.body, "    {n} = llvm.load {slot} : !llvm.ptr -> {to}");
            return n;
        };
        let width = |p: &PrimTy| {
            if *p == PrimTy::Bool {
                1
            } else {
                p.bit_width(pw)
            }
        };
        let (fw, tw) = (width(fp), width(tp));
        let mut v = v;
        if fp.is_float() {
            let n = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {n} = arith.bitcast {v} : {} to i{fw}",
                mlir_prim(*fp, pw)
            );
            v = n;
        }
        if fw != tw {
            let n = self.fresh_value();
            let op = if tw > fw {
                "arith.extui"
            } else {
                "arith.trunci"
            };
            let _ = writeln!(self.body, "    {n} = {op} {v} : i{fw} to i{tw}");
            v = n;
        }
        if tp.is_float() {
            let n = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {n} = arith.bitcast {v} : i{tw} to {}",
                mlir_prim(*tp, pw)
            );
            v = n;
        }
        v
    }

    // Build a struct value by chaining `llvm.insertvalue` from zero (not
    // `undef`: a GC reference in an unset field must read as null).
    fn emit_struct_init(&mut self, ty: &MirTy, fields: &[Operand]) -> String {
        let ty_str = mlir_type(ty, self.pointer_width);
        let acc0 = self.fresh_value();
        let _ = writeln!(self.body, "    {acc0} = llvm.mlir.zero : {ty_str}");
        let field_tys = struct_field_tys(ty);
        let mut acc = acc0;
        for (i, f) in fields.iter().enumerate() {
            let f_ty = field_tys.get(i).cloned().unwrap_or_else(|| match f {
                Operand::Copy(id) => self.local_ty(*id),
                Operand::Const(c) => const_ty(c),
            });
            let v = self.materialize_operand(f, &f_ty);
            let next = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {next} = llvm.insertvalue {v}, {acc}[{i}] : {ty_str}"
            );
            acc = next;
        }
        acc
    }

    fn emit_field_read(
        &mut self,
        target: &Operand,
        index: u32,
        field_ty: &MirTy,
        _dst_ty: &MirTy,
    ) -> String {
        let target_ty = match target {
            Operand::Copy(id) => self.local_ty(*id),
            Operand::Const(c) => const_ty(c),
        };
        let target_v = self.materialize_operand(target, &target_ty);
        let target_ty_str = mlir_type(&target_ty, self.pointer_width);
        let dst = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {dst} = llvm.extractvalue {target_v}[{index}] : {target_ty_str}"
        );
        let _ = field_ty;
        dst
    }

    fn emit_call(&mut self, dst: &str, callee: FunctionId, args: &[Operand]) {
        // Materialize each argument at the callee's parameter type so the
        // `func.call` operand list matches the declaration; literals take
        // that type directly and mismatched locals get a cast.
        let fns = self.fns;
        let sig = &fns[&callee];
        let ret_ty = &sig.ret;
        let arg_tys: Vec<MirTy> = args
            .iter()
            .enumerate()
            .map(|(i, op)| match (sig.params.get(i), op) {
                (Some(t), _) => t.clone(),
                (None, Operand::Copy(id)) => self.local_ty(*id),
                (None, Operand::Const(c)) => const_ty(c),
            })
            .collect();
        let mut arg_vals: Vec<String> = args
            .iter()
            .zip(arg_tys.iter())
            .map(|(op, ty)| self.materialize_operand(op, ty))
            .collect();
        let pw = self.pointer_width;
        let str_ty = MirTy::Prim(PrimTy::Str);
        if sig.c_abi {
            // C side sees the NUL-terminated byte pointer.
            for (v, t) in arg_vals.iter_mut().zip(&arg_tys) {
                if *t == str_ty {
                    let p = self.fresh_value();
                    let _ = writeln!(
                        self.body,
                        "    {p} = llvm.extractvalue {v}[0] : {}",
                        mlir_prim(PrimTy::Str, pw)
                    );
                    *v = p;
                }
            }
        }
        if let Some(abi) = sig.abi.as_ref().filter(|a| sig.variadic || !a.is_trivial()) {
            let abi = abi.clone();
            self.emit_c_call(dst, sig, &abi, arg_vals, &arg_tys, None);
            return;
        }
        let abi_ty = |t: &MirTy| abi_type(t, sig.c_abi, pw);

        let name = sig.name.clone();
        let arg_list = arg_vals.join(", ");
        let arg_ty_list = arg_tys.iter().map(abi_ty).collect::<Vec<_>>().join(", ");
        let ret = abi_ty(ret_ty);
        if sig.c_abi && *ret_ty == str_ty {
            // A `char*` result becomes `(ptr, strlen)`; null reads as "".
            let [p, l, u, h] = std::array::from_fn(|_| self.fresh_value());
            let ty = mlir_prim(PrimTy::Str, pw);
            let _ = write!(
                self.body,
                "    {p} = func.call @{name}({arg_list}) : ({arg_ty_list}) -> !llvm.ptr
    {l} = func.call @rok_cstr_len({p}) : (!llvm.ptr) -> i{pw}
    {u} = llvm.mlir.undef : {ty}
    {h} = llvm.insertvalue {p}, {u}[0] : {ty}
    {dst} = llvm.insertvalue {l}, {h}[1] : {ty}
"
            );
            self.needs.insert("rok_cstr_len");
            return;
        }

        if matches!(ret_ty, MirTy::Unit) {
            // Unit-returning calls produce no SSA value; emit the call
            // and bind `dst` to a dummy zero so downstream code keeps
            // the slot wired up.
            let _ = writeln!(
                self.body,
                "    func.call @{name}({arg_list}) : ({arg_ty_list}) -> ()"
            );
            let _ = writeln!(self.body, "    {dst} = arith.constant 0 : i1");
        } else {
            let _ = writeln!(
                self.body,
                "    {dst} = func.call @{name}({arg_list}) : ({arg_ty_list}) -> {ret}"
            );
        }
    }

    /// A call to a C function whose aggregates need the C ABI rewrite
    /// (`abi::classify`) or that is variadic. `vals` are the arguments
    /// at their rok types (`str` already a `char*`).
    /// `ptr`: call through this `!llvm.ptr` (an `extern "C" fn` value)
    /// instead of `@sig.name`.
    fn emit_c_call(
        &mut self,
        dst: &str,
        sig: &FnSig,
        abi: &crate::abi::FnAbi,
        vals: Vec<String>,
        tys: &[MirTy],
        ptr: Option<&str>,
    ) {
        use crate::abi::{ArgAbi, RetAbi};
        let pw = self.pointer_width;
        let mut ops: Vec<String> = Vec::new();
        let mut op_tys: Vec<String> = Vec::new();
        let ret_mlir = mlir_type(&sig.ret, pw);
        let sret = if abi.ret == RetAbi::Sret {
            let slot = self.entry_alloca(&ret_mlir, size_align(&sig.ret, pw).1);
            ops.push(slot.clone());
            op_tys.push("!llvm.ptr".to_owned());
            Some(slot)
        } else {
            None
        };
        for (i, (v, t)) in vals.into_iter().zip(tys).enumerate() {
            let ty = mlir_type(t, pw);
            match abi.args.get(i).unwrap_or(&ArgAbi::Direct) {
                ArgAbi::Direct => {
                    ops.push(v);
                    op_tys.push(abi_type(t, true, pw));
                }
                ArgAbi::Coerce(c) => {
                    // Store as the struct, reload as the coerced type
                    // (16 bytes or less, but an HFA: up to 32).
                    let slot = self.coerce_slot(t);
                    let r = self.fresh_value();
                    let _ = write!(
                        self.body,
                        "    llvm.store {v}, {slot} : {ty}, !llvm.ptr
    {r} = llvm.load {slot} : !llvm.ptr -> {c}
"
                    );
                    ops.push(r);
                    op_tys.push(c.clone());
                }
                ArgAbi::Indirect { .. } => {
                    let slot = self.entry_alloca(&ty, size_align(t, pw).1.max(8));
                    let _ = writeln!(self.body, "    llvm.store {v}, {slot} : {ty}, !llvm.ptr");
                    ops.push(slot);
                    op_tys.push("!llvm.ptr".to_owned());
                }
            }
        }
        let call_ret = match &abi.ret {
            RetAbi::Direct if sig.ret != MirTy::Unit => Some(abi_type(&sig.ret, true, pw)),
            RetAbi::Coerce(c) => Some(c.clone()),
            _ => None,
        };
        let name = &sig.name;
        let list = ops.join(", ");
        let tlist = op_tys.join(", ");
        let plain = abi.ret == RetAbi::Direct && sig.ret != MirTy::Prim(PrimTy::Str);
        let res = call_ret.as_ref().map(|_| {
            if plain {
                dst.to_owned()
            } else {
                self.fresh_value()
            }
        });
        let lhs = res.as_ref().map(|r| format!("{r} = ")).unwrap_or_default();
        let rty = call_ret.clone().unwrap_or_else(|| "()".to_owned());
        if sig.variadic {
            // Fixed part of the prototype: the hidden sret pointer and
            // the declared parameters.
            let fixed = usize::from(sret.is_some()) + sig.params.len();
            let fn_ret = call_ret.unwrap_or_else(|| "!llvm.void".to_owned());
            let mut proto: Vec<&str> = op_tys[..fixed].iter().map(String::as_str).collect();
            proto.push("...");
            let _ = writeln!(
                self.body,
                "    {lhs}llvm.call @{name}({list}) vararg(!llvm.func<{fn_ret} ({})>) : ({tlist}) -> {rty}",
                proto.join(", ")
            );
        } else if let Some(p) = ptr {
            // The declaration's parameter attributes (`sret` in `x8` on
            // arm64, `byval`, `signext` / `zeroext`) go on the call.
            let attrs: Vec<String> = c_signature(sig, pw)
                .0
                .into_iter()
                .map(|(_, a)| match a.trim() {
                    "" => "{}".to_owned(),
                    a => a.to_owned(),
                })
                .collect();
            let _ = writeln!(
                self.body,
                "    {lhs}llvm.call {p}({list}) {{arg_attrs = [{}]}} : !llvm.ptr, ({tlist}) -> {rty}",
                attrs.join(", ")
            );
        } else {
            let _ = writeln!(
                self.body,
                "    {lhs}func.call @{name}({list}) : ({tlist}) -> {rty}"
            );
        }
        match (&abi.ret, res) {
            (RetAbi::Sret, _) => {
                let slot = sret.expect("sret slot");
                let _ = writeln!(
                    self.body,
                    "    {dst} = llvm.load {slot} : !llvm.ptr -> {ret_mlir}"
                );
            }
            (RetAbi::Coerce(c), Some(r)) => {
                let slot = self.coerce_slot(&sig.ret);
                let _ = write!(
                    self.body,
                    "    llvm.store {r}, {slot} : {c}, !llvm.ptr
    {dst} = llvm.load {slot} : !llvm.ptr -> {ret_mlir}
"
                );
            }
            (_, Some(r)) if sig.ret == MirTy::Prim(PrimTy::Str) => {
                // A `char*` result becomes `(ptr, strlen)`.
                let [l, u, h] = std::array::from_fn(|_| self.fresh_value());
                let _ = write!(
                    self.body,
                    "    {l} = func.call @rok_cstr_len({r}) : (!llvm.ptr) -> i{pw}
    {u} = llvm.mlir.undef : {ret_mlir}
    {h} = llvm.insertvalue {r}, {u}[0] : {ret_mlir}
    {dst} = llvm.insertvalue {l}, {h}[1] : {ret_mlir}
"
                );
                self.needs.insert("rok_cstr_len");
            }
            (_, Some(_)) => {} // `dst` is the call's own result.
            (_, None) => {
                let _ = writeln!(self.body, "    {dst} = arith.constant 0 : i1");
            }
        }
    }

    /// `{dst} = str` value of a literal: its NUL-terminated global and
    /// byte length.
    fn str_literal_into(&mut self, dst: &str, text: &str) {
        let pw = self.pointer_width;
        let sym = self.intern_string(text);
        let ty = mlir_prim(PrimTy::Str, pw);
        let [p, l, u, h] = std::array::from_fn(|_| self.fresh_value());
        let _ = write!(
            self.body,
            "    {p} = llvm.mlir.addressof @{sym} : !llvm.ptr
    {l} = arith.constant {} : i{pw}
    {u} = llvm.mlir.undef : {ty}
    {h} = llvm.insertvalue {p}, {u}[0] : {ty}
    {dst} = llvm.insertvalue {l}, {h}[1] : {ty}
",
            text.len()
        );
    }

    /// Record an unsupported construct; returns a dummy SSA name so
    /// emission can continue and collect further errors.
    fn unsupported(&mut self, what: &str) -> String {
        self.errors.push(format!("unsupported in codegen: {what}"));
        self.fresh_value()
    }

    fn unsupported_at(&mut self, _dst: &str, what: &str) {
        self.errors.push(format!("unsupported in codegen: {what}"));
    }

    /// Branch to a `rok_panic(msg, len)` block when `fail` (an `i1`) is
    /// set; emission continues in a fresh fall-through block.
    fn emit_check(&mut self, fail: &str, msg: &str) {
        let n = self.next_check;
        self.next_check += 1;
        let pw = self.pointer_width;
        let _ = writeln!(
            self.body,
            "    cf.cond_br {fail}, ^rok_panic{n}, ^rok_ok{n}"
        );
        let _ = writeln!(self.body, "  ^rok_panic{n}:");
        let s = self.fresh_value();
        self.str_literal_into(&s, msg);
        let l = self.fresh_value();
        let str_ty = mlir_prim(PrimTy::Str, pw);
        let _ = writeln!(self.body, "    {l} = arith.constant {} : i{pw}", msg.len());
        let _ = writeln!(
            self.body,
            "    func.call @rok_panic({s}, {l}) : ({str_ty}, i{pw}) -> ()"
        );
        self.body.push_str("    llvm.unreachable\n");
        let _ = writeln!(self.body, "  ^rok_ok{n}:");
        self.uses_panic = true;
    }

    /// `fail = (v <pred> c)` for an integer constant `c`.
    fn cmp_const(&mut self, pred: &str, v: &str, c: i128, ty: &str) -> String {
        let k = self.fresh_value();
        let r = self.fresh_value();
        let _ = writeln!(self.body, "    {k} = arith.constant {c} : {ty}");
        let _ = writeln!(self.body, "    {r} = arith.cmpi {pred}, {v}, {k} : {ty}");
        r
    }

    /// Runtime checks that must panic rather than hit LLVM poison / UB:
    /// integer division by zero, signed `MIN / -1`, and shift amounts
    /// at or beyond the bit width. Constant divisors / shift amounts
    /// that are statically fine skip the check.
    fn emit_arith_checks(
        &mut self,
        op: PrimOp,
        prim: PrimTy,
        rhs: &Operand,
        lhs_v: &str,
        rhs_v: &str,
        ty: &str,
    ) {
        if !prim.is_int() {
            return;
        }
        let rhs_const = const_int(rhs);
        let bits = prim.bit_width(self.pointer_width);
        match op {
            PrimOp::Div | PrimOp::Rem => {
                let (zero_msg, ovf_msg) = if op == PrimOp::Div {
                    (
                        "attempt to divide by zero",
                        "attempt to divide with overflow",
                    )
                } else {
                    (
                        "attempt to calculate the remainder with a divisor of zero",
                        "attempt to calculate the remainder with overflow",
                    )
                };
                if rhs_const.is_none_or(|c| c == 0) {
                    let fail = self.cmp_const("eq", rhs_v, 0, ty);
                    self.emit_check(&fail, zero_msg);
                }
                if prim.is_signed_int() && rhs_const.is_none_or(|c| c == -1) {
                    let is_min = self.cmp_const("eq", lhs_v, -(1i128 << (bits - 1)), ty);
                    let is_neg1 = self.cmp_const("eq", rhs_v, -1, ty);
                    let fail = self.fresh_value();
                    let _ = writeln!(
                        self.body,
                        "    {fail} = arith.andi {is_min}, {is_neg1} : i1"
                    );
                    self.emit_check(&fail, ovf_msg);
                }
            }
            PrimOp::Shl | PrimOp::Shr => {
                if rhs_const.is_some_and(|c| (0..i128::from(bits)).contains(&c)) {
                    return;
                }
                // Unsigned compare also rejects negative amounts.
                let fail = self.cmp_const("uge", rhs_v, i128::from(bits), ty);
                let msg = if op == PrimOp::Shl {
                    "attempt to shift left with overflow"
                } else {
                    "attempt to shift right with overflow"
                };
                self.emit_check(&fail, msg);
            }
            _ => {}
        }
    }

    /// Overflow check on an integer `+ - *` result `dst`, without
    /// widening: sign-bit tricks for add/sub, the high half of the
    /// extended product for mul.
    fn emit_overflow_check(
        &mut self,
        op: PrimOp,
        prim: PrimTy,
        dst: &str,
        (lhs, rhs): (&str, &str),
        consts: (Option<i128>, Option<i128>),
        ty: &str,
    ) {
        let signed = prim.is_signed_int();
        if !self.overflow_checks
            || !(signed || prim.is_unsigned_int())
            || cannot_overflow(op, prim, prim.bit_width(self.pointer_width), consts)
        {
            return;
        }
        let fail = match op {
            PrimOp::Add | PrimOp::Sub if signed => {
                // add: lhs and rhs share a sign that dst lacks.
                // sub: lhs and rhs differ in sign and dst's differs from lhs.
                let pairs = if op == PrimOp::Add {
                    [(lhs, dst), (rhs, dst)]
                } else {
                    [(lhs, rhs), (lhs, dst)]
                };
                let [x0, x1] = pairs.map(|(p, q)| {
                    let v = self.fresh_value();
                    let _ = writeln!(self.body, "    {v} = arith.xori {p}, {q} : {ty}");
                    v
                });
                let both = self.fresh_value();
                let _ = writeln!(self.body, "    {both} = arith.andi {x0}, {x1} : {ty}");
                self.cmp_const("slt", &both, 0, ty)
            }
            PrimOp::Add => self.cmp2("ult", dst, lhs, ty),
            PrimOp::Sub => self.cmp2("ult", lhs, rhs, ty),
            PrimOp::Mul => {
                let lo = self.fresh_value();
                let hi = self.fresh_value();
                let ext = if signed {
                    "mulsi_extended"
                } else {
                    "mului_extended"
                };
                let _ = writeln!(
                    self.body,
                    "    {lo}, {hi} = arith.{ext} {lhs}, {rhs} : {ty}"
                );
                if signed {
                    // No overflow iff the high half is the sign extension of lo.
                    let bits = prim.bit_width(self.pointer_width);
                    let k = self.fresh_value();
                    let sign = self.fresh_value();
                    let _ = writeln!(self.body, "    {k} = arith.constant {} : {ty}", bits - 1);
                    let _ = writeln!(self.body, "    {sign} = arith.shrsi {lo}, {k} : {ty}");
                    self.cmp2("ne", &hi, &sign, ty)
                } else {
                    self.cmp_const("ne", &hi, 0, ty)
                }
            }
            _ => return,
        };
        let msg = match op {
            PrimOp::Add => "attempt to add with overflow",
            PrimOp::Sub => "attempt to subtract with overflow",
            _ => "attempt to multiply with overflow",
        };
        self.emit_check(&fail, msg);
    }

    /// `fail = (a <pred> b)`.
    fn cmp2(&mut self, pred: &str, a: &str, b: &str, ty: &str) -> String {
        let r = self.fresh_value();
        let _ = writeln!(self.body, "    {r} = arith.cmpi {pred}, {a}, {b} : {ty}");
        r
    }

    fn emit_bin_op(
        &mut self,
        dst: &str,
        _dst_ty: &MirTy,
        op: PrimOp,
        op_ty: &MirTy,
        lhs: &Operand,
        rhs: &Operand,
    ) {
        let lhs_v = self.materialize_operand(lhs, op_ty);
        let rhs_v = self.materialize_operand(rhs, op_ty);
        let ty = mlir_type(op_ty, self.pointer_width);
        let MirTy::Prim(prim) = op_ty else {
            self.unsupported_at(dst, &format!("binary `{op:?}` on `{ty}`"));
            return;
        };
        // String literal patterns: content equality.
        if *prim == PrimTy::Str && matches!(op, PrimOp::Eq | PrimOp::Ne) {
            let c = self.fresh_value();
            let z = self.fresh_value();
            let pred = if op == PrimOp::Eq { "eq" } else { "ne" };
            let _ = write!(
                self.body,
                "    {c} = func.call @rok_str_cmp({lhs_v}, {rhs_v}) : ({ty}, {ty}) -> i32
    {z} = arith.constant 0 : i32
    {dst} = arith.cmpi {pred}, {c}, {z} : i32
"
            );
            self.needs.insert("rok_str_cmp");
            return;
        }
        self.emit_arith_checks(op, *prim, rhs, &lhs_v, &rhs_v, &ty);
        if let Some(line) = arith_binop(op, *prim, dst, &lhs_v, &rhs_v, &ty) {
            self.body.push_str(&line);
            let consts = (const_int(lhs), const_int(rhs));
            self.emit_overflow_check(op, *prim, dst, (&lhs_v, &rhs_v), consts, &ty);
            return;
        }
        self.unsupported_at(dst, &format!("binary `{op:?}` on `{ty}`"));
    }

    fn emit_unary_op(
        &mut self,
        dst: &str,
        dst_ty: &MirTy,
        op: PrimOp,
        op_ty: &MirTy,
        operand: &Operand,
    ) {
        let v = self.materialize_operand(operand, op_ty);
        let ty = mlir_type(op_ty, self.pointer_width);
        let MirTy::Prim(prim) = op_ty else {
            let _ = dst_ty;
            self.unsupported_at(dst, &format!("unary `{op:?}` on `{ty}`"));
            return;
        };
        match (op, prim) {
            (PrimOp::Neg, p) if p.is_signed_int() => {
                // arith has no `negi`; lower to `0 - x`.
                let zero = self.fresh_value();
                let _ = writeln!(self.body, "    {zero} = arith.constant 0 : {ty}");
                let _ = writeln!(self.body, "    {dst} = arith.subi {zero}, {v} : {ty}");
                let bits = p.bit_width(self.pointer_width);
                if self.overflow_checks
                    && const_int(operand).is_none_or(|c| c == -(1i128 << (bits - 1)))
                {
                    let fail = self.cmp_const("eq", &v, -(1i128 << (bits - 1)), &ty);
                    self.emit_check(&fail, "attempt to negate with overflow");
                }
            }
            (PrimOp::Neg, p) if p.is_float() => {
                let _ = writeln!(self.body, "    {dst} = arith.negf {v} : {ty}");
            }
            (PrimOp::Sqrt, p) if p.is_float() => {
                let _ = writeln!(
                    self.body,
                    "    {dst} = llvm.intr.sqrt({v}) : ({ty}) -> {ty}"
                );
            }
            (PrimOp::CountOnes | PrimOp::SwapBytes, p) if p.is_int() => {
                let name = if op == PrimOp::CountOnes {
                    "ctpop"
                } else {
                    "bswap"
                };
                let _ = writeln!(
                    self.body,
                    "    {dst} = llvm.intr.{name}({v}) : ({ty}) -> {ty}"
                );
            }
            (PrimOp::LeadingZeros | PrimOp::TrailingZeros, p) if p.is_int() => {
                let name = if op == PrimOp::LeadingZeros {
                    "ctlz"
                } else {
                    "cttz"
                };
                let _ = writeln!(
                    self.body,
                    "    {dst} = \"llvm.intr.{name}\"({v}) <{{is_zero_poison = false}}> : ({ty}) -> {ty}"
                );
            }
            (PrimOp::Not, p) if p.is_int() => {
                // Bitwise NOT = xor with all-ones.
                let ones = self.fresh_value();
                let _ = writeln!(self.body, "    {ones} = arith.constant -1 : {ty}");
                let _ = writeln!(self.body, "    {dst} = arith.xori {v}, {ones} : {ty}");
            }
            (PrimOp::LogicalNot, PrimTy::Bool) => {
                let one = self.fresh_value();
                let _ = writeln!(self.body, "    {one} = arith.constant 1 : i1");
                let _ = writeln!(self.body, "    {dst} = arith.xori {v}, {one} : i1");
            }
            _ => self.unsupported_at(dst, &format!("unary `{op:?}` on `{ty}`")),
        }
    }

    fn emit_const_assign(&mut self, dst: &str, dst_ty: &MirTy, c: &ConstVal) {
        let ty = mlir_type(dst_ty, self.pointer_width);
        match c {
            // Numeric literals take the destination's type when it is
            // numeric (`g(3)` with an `i64` param, `let x: i64 = 3`);
            // otherwise they keep their own literal type.
            ConstVal::Int { ty: prim, .. } | ConstVal::UInt { ty: prim, .. } => {
                let (value, as_f64) = match c {
                    ConstVal::Int { value, .. } => (value.to_string(), *value as f64),
                    ConstVal::UInt { value, .. } => (value.to_string(), *value as f64),
                    _ => unreachable!(),
                };
                let lit = match dst_ty {
                    MirTy::Any | MirTy::GcRef => ty.clone(),
                    MirTy::Prim(p) if p.is_int() => ty.clone(),
                    MirTy::Prim(p) if p.is_float() => {
                        let f = format_float_decimal(as_f64);
                        let _ = writeln!(self.body, "    {dst} = arith.constant {f} : {ty}");
                        return;
                    }
                    _ => mlir_prim(*prim, self.pointer_width),
                };
                let _ = writeln!(self.body, "    {dst} = arith.constant {value} : {lit}");
            }
            ConstVal::Bool(b) => {
                let _ = writeln!(
                    self.body,
                    "    {dst} = arith.constant {} : i1",
                    u32::from(*b)
                );
            }
            ConstVal::Float { bits, ty: prim } => {
                // `f32` / `f64` destination wins over the literal's width.
                let (prim, val) = match dst_ty {
                    MirTy::Prim(p) if p.is_float() && p != prim => {
                        let v = if *prim == PrimTy::F32 {
                            f64::from(f32::from_bits(*bits as u32))
                        } else {
                            f64::from_bits(*bits)
                        };
                        let b = if *p == PrimTy::F32 {
                            u64::from((v as f32).to_bits())
                        } else {
                            v.to_bits()
                        };
                        (*p, b)
                    }
                    _ => (*prim, *bits),
                };
                let lit = format_float(val, prim);
                let _ = writeln!(
                    self.body,
                    "    {dst} = arith.constant {lit} : {}",
                    mlir_prim(prim, self.pointer_width)
                );
            }
            ConstVal::Unit | ConstVal::None if *dst_ty == MirTy::Unit => {
                let _ = writeln!(self.body, "    {dst} = llvm.mlir.zero : {UNIT_TY}");
            }
            ConstVal::Unit | ConstVal::None => {
                // For aggregate destinations, materialize a zero value
                // (null GC references); for primitives, a zero constant (also the unused
                // payload of a `throws` carrier). Unit really shouldn't
                // reach codegen but a placeholder keeps the pipeline
                // well-typed.
                if matches!(
                    dst_ty,
                    MirTy::Struct(_, _)
                        | MirTy::Tuple(_)
                        | MirTy::Sum(_)
                        | MirTy::Array(_, _)
                        | MirTy::Prim(PrimTy::Str)
                ) {
                    let _ = writeln!(self.body, "    {dst} = llvm.mlir.zero : {ty}");
                } else if matches!(dst_ty, MirTy::Fn(_, _)) {
                    let _ = writeln!(self.body, "    {dst} = llvm.mlir.zero : !llvm.ptr");
                } else if matches!(dst_ty, MirTy::Prim(PrimTy::F32 | PrimTy::F64)) {
                    let _ = writeln!(self.body, "    {dst} = arith.constant 0.0 : {ty}");
                } else {
                    let _ = writeln!(self.body, "    {dst} = arith.constant 0 : {ty}");
                }
            }
            ConstVal::Char(c) => {
                let _ = writeln!(self.body, "    {dst} = arith.constant {c} : {ty}");
            }
            ConstVal::Str(s) => self.str_literal_into(dst, s),
        }
    }

    fn emit_terminator(&mut self, b: u32, t: &Terminator) {
        if self.back_edge_blocks.contains(&b) {
            self.emit_poll();
        }
        match t {
            // A generic body returning a `T = ()` value returns nothing.
            Terminator::Return(None) => {
                self.emit_gc_frame_pop();
                self.body.push_str("    func.return\n");
            }
            Terminator::Return(Some(_)) if matches!(self.f.ret_ty, MirTy::Unit) => {
                self.emit_gc_frame_pop();
                self.body.push_str("    func.return\n");
            }
            Terminator::Return(Some(op)) => {
                let val = self.materialize_operand(op, &self.f.ret_ty.clone());
                self.emit_gc_frame_pop();
                let ty = mlir_type(&self.f.ret_ty, self.pointer_width);
                let _ = writeln!(self.body, "    func.return {val} : {ty}");
            }
            Terminator::Goto { target, args } => {
                self.emit_branch("    cf.br", target.0, args, None);
            }
            Terminator::If {
                cond,
                then_bb,
                then_args,
                else_bb,
                else_args,
            } => {
                let v = self.materialize_operand(cond, &MirTy::Prim(PrimTy::Bool));
                let then_part = self.format_block_target(then_bb.0, then_args);
                let else_part = self.format_block_target(else_bb.0, else_args);
                let _ = writeln!(self.body, "    cf.cond_br {v}, {then_part}, {else_part}");
            }
            Terminator::Unreachable => {
                self.body.push_str("    llvm.unreachable\n");
            }
            Terminator::Suspend { .. } => {
                self.errors
                    .push("internal: a coroutine suspend point survived MIR".to_owned());
                self.body.push_str("    llvm.unreachable\n");
            }
        }
    }

    fn emit_branch(&mut self, op: &str, target: u32, args: &[Operand], _label: Option<&str>) {
        if args.is_empty() {
            let _ = writeln!(self.body, "{op} ^bb{target}");
            return;
        }
        let parts: Vec<(String, String)> = args
            .iter()
            .map(|a| {
                let ty = match a {
                    Operand::Copy(id) => self.local_ty(*id),
                    Operand::Const(c) => const_ty(c),
                };
                let v = self.materialize_operand(a, &ty);
                (v, mlir_type(&ty, self.pointer_width))
            })
            .collect();
        let vals: Vec<String> = parts.iter().map(|(v, _)| v.clone()).collect();
        let tys: Vec<String> = parts.iter().map(|(_, t)| t.clone()).collect();
        let _ = writeln!(
            self.body,
            "{op} ^bb{target}({} : {})",
            vals.join(", "),
            tys.join(", ")
        );
    }

    fn format_block_target(&mut self, target: u32, args: &[Operand]) -> String {
        if args.is_empty() {
            return format!("^bb{target}");
        }
        let parts: Vec<(String, String)> = args
            .iter()
            .map(|a| {
                let ty = match a {
                    Operand::Copy(id) => self.local_ty(*id),
                    Operand::Const(c) => const_ty(c),
                };
                let v = self.materialize_operand(a, &ty);
                (v, mlir_type(&ty, self.pointer_width))
            })
            .collect();
        let vals: Vec<String> = parts.iter().map(|(v, _)| v.clone()).collect();
        let tys: Vec<String> = parts.iter().map(|(_, t)| t.clone()).collect();
        format!("^bb{target}({} : {})", vals.join(", "), tys.join(", "))
    }

    fn materialize_operand(&mut self, op: &Operand, ty: &MirTy) -> String {
        match op {
            Operand::Copy(id) => {
                let v = self.read_local(*id);
                // A primitive local requested at another primitive type
                // (e.g. an `i32` local passed to an `i64` parameter) gets
                // an explicit conversion rather than ill-typed IR.
                let from = self.local_ty(*id);
                let pw = self.pointer_width;
                if matches!((&from, ty), (MirTy::Prim(_), MirTy::Prim(_)))
                    && mlir_type(&from, pw) != mlir_type(ty, pw)
                {
                    return self.cast_value(v, &from, ty);
                }
                v
            }
            Operand::Const(c) => {
                let v = self.fresh_value();
                self.emit_const_assign(&v, ty, c);
                v
            }
        }
    }

    fn local_ty(&self, id: rokc_ir_common::LocalId) -> MirTy {
        self.f
            .locals
            .get(id.0 as usize)
            .map_or(MirTy::Any, |l| l.ty.clone())
    }
}

/// A `()` value (argument, field, element): an empty struct. A function
/// returning `()` returns nothing instead (`mlir_fn_signature`).
const UNIT_TY: &str = "!llvm.struct<()>";

fn mlir_type(ty: &MirTy, pointer_width: u32) -> String {
    match ty {
        MirTy::Unit => UNIT_TY.to_owned(),
        MirTy::Prim(p) => mlir_prim(*p, pointer_width),
        MirTy::Any | MirTy::GcRef => format!("i{pointer_width}"),
        MirTy::Sum(parts) => mlir_type(&rokc_mir::sum_layout(parts), pointer_width),
        MirTy::Tuple(parts) | MirTy::Struct(_, parts) => {
            let inner: Vec<String> = parts.iter().map(|t| mlir_type(t, pointer_width)).collect();
            format!("!llvm.struct<({})>", inner.join(", "))
        }
        MirTy::Array(elem, n) => {
            format!("!llvm.array<{n} x {}>", mlir_type(elem, pointer_width))
        }
        // Function values flow as opaque pointers so they can live
        // alongside other fields inside `!llvm.struct`. The full
        // `(args) -> ret` shape is supplied at each call site.
        MirTy::Fn(_, _) => "!llvm.ptr".to_owned(),
        MirTy::Mlir(t) => t.clone(),
    }
}

/// A C declaration's lowered parameters `(MLIR type, attributes)` (a
/// leading `sret` pointer included) and result type.
fn c_signature(sig: &FnSig, pw: u32) -> (Vec<(String, String)>, Option<String>) {
    use crate::abi::{ArgAbi, RetAbi};
    let abi = sig.abi.as_ref().expect("C declaration has an ABI");
    let mut params = Vec::new();
    if abi.ret == RetAbi::Sret {
        params.push((
            "!llvm.ptr".to_owned(),
            format!(
                " {{llvm.sret = {}, llvm.align = {} : i64}}",
                mlir_type(&sig.ret, pw),
                size_align(&sig.ret, pw).1
            ),
        ));
    }
    for (t, a) in sig.params.iter().zip(&abi.args) {
        params.push(match a {
            ArgAbi::Direct => (abi_type(t, true, pw), c_ext_attr(t).to_owned()),
            ArgAbi::Coerce(c) => (c.clone(), String::new()),
            ArgAbi::Indirect { byval: true } => (
                "!llvm.ptr".to_owned(),
                format!(
                    " {{llvm.byval = {}, llvm.align = {} : i64}}",
                    mlir_type(t, pw),
                    size_align(t, pw).1.max(8)
                ),
            ),
            ArgAbi::Indirect { byval: false } => ("!llvm.ptr".to_owned(), String::new()),
        });
    }
    let ret = match &abi.ret {
        RetAbi::Direct if sig.ret != MirTy::Unit => Some(abi_type(&sig.ret, true, pw)),
        RetAbi::Coerce(c) => Some(c.clone()),
        _ => None,
    };
    (params, ret)
}

/// Caller-side extension of a narrow integer C parameter: Apple arm64
/// and `x86_64` callees (clang) assume it (`signext` / `zeroext`).
// ponytail: `c_char` taken as signed everywhere (Linux aarch64's is
// unsigned; only values > 127 would see the difference).
const fn c_ext_attr(ty: &MirTy) -> &'static str {
    match ty {
        MirTy::Prim(PrimTy::I8 | PrimTy::I16 | PrimTy::CChar) => " {llvm.signext}",
        MirTy::Prim(PrimTy::U8 | PrimTy::U16 | PrimTy::Bool) => " {llvm.zeroext}",
        _ => "",
    }
}

/// `mlir_type`, except that a C function sees `str` as `char*`.
fn abi_type(ty: &MirTy, c_abi: bool, pointer_width: u32) -> String {
    if c_abi && *ty == MirTy::Prim(PrimTy::Str) {
        return "!llvm.ptr".to_owned();
    }
    mlir_type(ty, pointer_width)
}

// `(args) -> ret` rendering for func.constant / call sites.
fn mlir_fn_signature(args: &[MirTy], ret: &MirTy, pointer_width: u32) -> String {
    let arg_list = args
        .iter()
        .map(|t| mlir_type(t, pointer_width))
        .collect::<Vec<_>>()
        .join(", ");
    let ret_str = if matches!(ret, MirTy::Unit) {
        "()".to_owned()
    } else {
        mlir_type(ret, pointer_width)
    };
    format!("({arg_list}) -> {ret_str}")
}

fn mlir_prim(p: PrimTy, pointer_width: u32) -> String {
    match p {
        PrimTy::I8 | PrimTy::U8 | PrimTy::CChar => "i8".to_owned(),
        PrimTy::I16 | PrimTy::U16 => "i16".to_owned(),
        PrimTy::I32 | PrimTy::U32 | PrimTy::Char => "i32".to_owned(),
        PrimTy::I64 | PrimTy::U64 => "i64".to_owned(),
        PrimTy::Isize | PrimTy::Usize => format!("i{pointer_width}"),
        PrimTy::F32 => "f32".to_owned(),
        PrimTy::F64 => "f64".to_owned(),
        PrimTy::Bool => "i1".to_owned(),
        // FFI-friendly form: opaque pointer to a NUL-terminated byte
        // sequence. The spec's `(ptr, len)` view is kept as a future
        // refinement under a separate stdlib type.
        // `(ptr, len)` (808); the bytes are followed by a NUL so the
        // pointer alone is a C string at the FFI boundary.
        PrimTy::Str => format!("!llvm.struct<(ptr, i{pointer_width})>"),
    }
}

/// Build a single MLIR line for a primitive binary op. Returns `None` if
/// the (op, prim) combo is not handled.
#[allow(clippy::cognitive_complexity)] // flat (op, prim) dispatch table; splitting it hurts readability
fn arith_binop(
    op: PrimOp,
    prim: PrimTy,
    dst: &str,
    lhs: &str,
    rhs: &str,
    ty: &str,
) -> Option<String> {
    let int = prim.is_int();
    let signed = prim.is_signed_int();
    let float = prim.is_float();
    let bool_ = matches!(prim, PrimTy::Bool);

    let mnemonic: Option<String> = match op {
        // `Wrapping*` skip `emit_overflow_check` (it ignores them).
        PrimOp::Add | PrimOp::WrappingAdd if int => Some("arith.addi".into()),
        PrimOp::Add if float => Some("arith.addf".into()),
        PrimOp::Sub | PrimOp::WrappingSub if int => Some("arith.subi".into()),
        PrimOp::Sub if float => Some("arith.subf".into()),
        PrimOp::Mul | PrimOp::WrappingMul if int => Some("arith.muli".into()),
        PrimOp::Mul if float => Some("arith.mulf".into()),
        PrimOp::Div if signed => Some("arith.divsi".into()),
        PrimOp::Div if int => Some("arith.divui".into()),
        PrimOp::Div if float => Some("arith.divf".into()),
        PrimOp::Rem if signed => Some("arith.remsi".into()),
        PrimOp::Rem if int => Some("arith.remui".into()),
        PrimOp::Rem if float => Some("arith.remf".into()),
        PrimOp::BitAnd if int || bool_ => Some("arith.andi".into()),
        PrimOp::BitOr if int || bool_ => Some("arith.ori".into()),
        PrimOp::BitXor if int || bool_ => Some("arith.xori".into()),
        PrimOp::LogicalAnd if bool_ => Some("arith.andi".into()),
        PrimOp::LogicalOr if bool_ => Some("arith.ori".into()),
        PrimOp::Shl if int => Some("arith.shli".into()),
        PrimOp::Shr if signed => Some("arith.shrsi".into()),
        PrimOp::Shr if int => Some("arith.shrui".into()),
        _ => None,
    };
    if let Some(m) = mnemonic {
        return Some(format!("    {dst} = {m} {lhs}, {rhs} : {ty}\n"));
    }

    // Comparisons return i1; the predicate selector encodes signed-ness.
    let pred = match (op, prim) {
        (PrimOp::Eq, p) if p.is_int() || matches!(p, PrimTy::Bool) => Some(("arith.cmpi", "eq")),
        (PrimOp::Ne, p) if p.is_int() || matches!(p, PrimTy::Bool) => Some(("arith.cmpi", "ne")),
        (PrimOp::Lt, p) if p.is_signed_int() => Some(("arith.cmpi", "slt")),
        (PrimOp::Le, p) if p.is_signed_int() => Some(("arith.cmpi", "sle")),
        (PrimOp::Gt, p) if p.is_signed_int() => Some(("arith.cmpi", "sgt")),
        (PrimOp::Ge, p) if p.is_signed_int() => Some(("arith.cmpi", "sge")),
        (PrimOp::Lt, p) if p.is_int() => Some(("arith.cmpi", "ult")),
        (PrimOp::Le, p) if p.is_int() => Some(("arith.cmpi", "ule")),
        (PrimOp::Gt, p) if p.is_int() => Some(("arith.cmpi", "ugt")),
        (PrimOp::Ge, p) if p.is_int() => Some(("arith.cmpi", "uge")),
        (PrimOp::Eq, p) if p.is_float() => Some(("arith.cmpf", "oeq")),
        // `!=` is true when either side is NaN → unordered-or-not-equal.
        (PrimOp::Ne, p) if p.is_float() => Some(("arith.cmpf", "une")),
        (PrimOp::Lt, p) if p.is_float() => Some(("arith.cmpf", "olt")),
        (PrimOp::Le, p) if p.is_float() => Some(("arith.cmpf", "ole")),
        (PrimOp::Gt, p) if p.is_float() => Some(("arith.cmpf", "ogt")),
        (PrimOp::Ge, p) if p.is_float() => Some(("arith.cmpf", "oge")),
        _ => None,
    };
    if let Some((mn, pred)) = pred {
        return Some(format!("    {dst} = {mn} {pred}, {lhs}, {rhs} : {ty}\n"));
    }
    None
}

// Struct / tuple / pointer values live in SSA — `memref` can't hold an
// arbitrary `!llvm.struct` or `!llvm.ptr`, so they aren't stack-slotted.
// Arrays go through memref directly (`memref<N x T>`) for dynamic
// indexing — handled separately from primitive slots.
/// Types stored via `memref.alloca`. Limited to plain primitives that
/// the memref dialect understands. Aggregates and pointer-shaped values
/// (including nested arrays) take the `llvm.alloca` path instead.
const fn is_memref_storable(ty: &MirTy) -> bool {
    matches!(ty, MirTy::Prim(p) if !matches!(p, PrimTy::Str))
}

/// Types stored via `llvm.alloca` — aggregates and pointer-shaped
/// values that flow through the LLVM dialect.
const fn is_llvm_storable(ty: &MirTy) -> bool {
    matches!(
        ty,
        MirTy::Struct(_, _)
            | MirTy::Tuple(_)
            | MirTy::Sum(_)
            | MirTy::Prim(PrimTy::Str)
            | MirTy::Fn(_, _)
            | MirTy::GcRef
    )
}

/// `insertvalue`-style index paths to every `GcRef` inside `ty`.
fn gc_paths(ty: &MirTy, path: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
    let mut each = |i: u32, t: &MirTy, out: &mut Vec<Vec<u32>>| {
        path.push(i);
        gc_paths(t, path, out);
        path.pop();
    };
    match ty {
        MirTy::GcRef => out.push(path.clone()),
        // A runtime-built string's pointer points into a GC object.
        MirTy::Prim(PrimTy::Str) => {
            path.push(0);
            out.push(path.clone());
            path.pop();
        }
        MirTy::Tuple(ps) | MirTy::Struct(_, ps) => {
            for (i, t) in ps.iter().enumerate() {
                each(i as u32, t, out);
            }
        }
        MirTy::Array(t, n) => {
            for i in 0..*n {
                each(i, t, out);
            }
        }
        MirTy::Sum(ps) => gc_paths(&rokc_mir::sum_layout(ps), path, out),
        _ => {}
    }
}

thread_local! {
    /// ABI alignment of `i64` / `u64` / `f64` on the target being
    /// compiled: 4 on 32-bit x86 outside Windows (the SysV i386 ABI;
    /// LLVM's `i64:32` / `f64:32`), else 8.
    // ponytail: per thread like the codegen run that sets it
    // (`codegen_with_target`); a field threaded through `size_align`'s
    // ~30 callers if targets ever mix in one thread.
    pub(crate) static WIDE_ALIGN: std::cell::Cell<u32> = const { std::cell::Cell::new(8) };
}

/// `WIDE_ALIGN` for a target triple (`None`: the host).
pub(crate) fn wide_align_for_target(target: Option<&str>) -> u32 {
    let x86_32 = |t: &str| {
        ["i386", "i486", "i586", "i686"]
            .iter()
            .any(|p| t.starts_with(p))
    };
    let sysv_i386 = match target {
        Some(t) => x86_32(t) && !t.contains("windows"),
        None => cfg!(all(target_arch = "x86", not(windows))),
    };
    if sysv_i386 { 4 } else { 8 }
}

/// `(size, align)` in bytes of `ty` as lowered by `mlir_type`, under the
/// C struct layout LLVM uses on the target (`WIDE_ALIGN`).
pub(crate) fn size_align(ty: &MirTy, pw: u32) -> (u32, u32) {
    let word = (pw / 8, pw / 8);
    match ty {
        MirTy::Unit => (0, 1),
        MirTy::Prim(p) => match p {
            PrimTy::I8 | PrimTy::U8 | PrimTy::CChar | PrimTy::Bool => (1, 1),
            PrimTy::I16 | PrimTy::U16 => (2, 2),
            PrimTy::I32 | PrimTy::U32 | PrimTy::Char | PrimTy::F32 => (4, 4),
            PrimTy::I64 | PrimTy::U64 | PrimTy::F64 => (8, WIDE_ALIGN.get()),
            PrimTy::Isize | PrimTy::Usize => word,
            PrimTy::Str => (2 * word.0, word.1),
        },
        MirTy::Any | MirTy::GcRef | MirTy::Fn(_, _) | MirTy::Mlir(_) => word,
        MirTy::Sum(ps) => size_align(&rokc_mir::sum_layout(ps), pw),
        MirTy::Tuple(ps) | MirTy::Struct(_, ps) => {
            let (mut size, mut align) = (0u32, 1);
            for t in ps {
                let (s, a) = size_align(t, pw);
                size = size.next_multiple_of(a) + s;
                align = align.max(a);
            }
            (size.next_multiple_of(align), align)
        }
        MirTy::Array(t, n) => {
            let (s, a) = size_align(t, pw);
            (s * n, a)
        }
    }
}

/// `(total_size, align)` of a GC object with a `ty` payload (801 §8.1.7).
fn gc_object_size(ty: &MirTy, pw: u32) -> (u32, u32) {
    let (size, align) = size_align(ty, pw);
    let align = align.max(8);
    (HEADER_SIZE + size.next_multiple_of(align), align)
}

/// `(byte offset, ScanTable kind)` of every word inside a `ty` that
/// starts at `at` that may hold a GC reference.
fn gc_offsets(ty: &MirTy, pw: u32, at: u32, out: &mut Vec<(u32, u32)>) {
    match ty {
        MirTy::GcRef => out.push((at, STRONG_REF)),
        MirTy::Prim(PrimTy::Str) => out.push((at, INTERIOR_REF)),
        MirTy::Struct(rokc_mir::ANY_STRUCT, _) => out.push((at, ANY_SLOT)),
        // An enum union payload (`unify_payload`) holds references or
        // other bits depending on the tag; a real `[GcRef; n]` array
        // looks the same.
        // ponytail: ambiguous words; a per-variant `SUM_PAYLOAD` table
        // (802 §8.2.6) needs MIR unions that keep their variants.
        MirTy::Array(t, n) if **t == MirTy::GcRef => {
            out.extend((0..*n).map(|i| (at + i * (pw / 8), AMBIGUOUS)));
        }
        MirTy::Tuple(ps) | MirTy::Struct(_, ps) => {
            let mut off = 0u32;
            for t in ps {
                let (s, a) = size_align(t, pw);
                off = off.next_multiple_of(a);
                gc_offsets(t, pw, at + off, out);
                off += s;
            }
        }
        MirTy::Array(t, n) => {
            let s = size_align(t, pw).0;
            for i in 0..*n {
                gc_offsets(t, pw, at + i * s, out);
            }
        }
        MirTy::Sum(ps) => gc_offsets(&rokc_mir::sum_layout(ps), pw, at, out),
        _ => {}
    }
}

fn struct_field_tys(ty: &MirTy) -> Vec<MirTy> {
    match ty {
        MirTy::Struct(_, fs) | MirTy::Tuple(fs) => fs.clone(),
        _ => Vec::new(),
    }
}

/// Integer value of a constant operand (`Int` / in-range `UInt`).
/// `+ - *` whose constant operands rule out overflow: both constant and
/// the result fits, or an identity / absorbing constant (`x + 0`, `x - 0`,
/// `x * 1`, `x * 0`).
fn cannot_overflow(
    op: PrimOp,
    prim: PrimTy,
    bits: u32,
    (l, r): (Option<i128>, Option<i128>),
) -> bool {
    if let (Some(a), Some(b)) = (l, r) {
        let v = match op {
            PrimOp::Add => a.checked_add(b),
            PrimOp::Sub => a.checked_sub(b),
            PrimOp::Mul => a.checked_mul(b),
            _ => None,
        };
        let (lo, hi) = if prim.is_signed_int() {
            (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
        } else {
            (
                0,
                if bits >= 127 {
                    i128::MAX
                } else {
                    (1i128 << bits) - 1
                },
            )
        };
        return v.is_some_and(|v| (lo..=hi).contains(&v));
    }
    match op {
        PrimOp::Add => l == Some(0) || r == Some(0),
        PrimOp::Sub => r == Some(0),
        PrimOp::Mul => matches!(l, Some(0 | 1)) || matches!(r, Some(0 | 1)),
        _ => false,
    }
}

fn const_int(op: &Operand) -> Option<i128> {
    match op {
        Operand::Const(ConstVal::Int { value, .. }) => Some(*value),
        Operand::Const(ConstVal::UInt { value, .. }) => i128::try_from(*value).ok(),
        _ => None,
    }
}

/// Best-effort type for a `ConstVal`. Used at call sites where we have a
/// raw const operand and need to pick an MLIR type for it.
const fn const_ty(c: &ConstVal) -> MirTy {
    match c {
        ConstVal::Int { ty, .. } | ConstVal::UInt { ty, .. } | ConstVal::Float { ty, .. } => {
            MirTy::Prim(*ty)
        }
        ConstVal::Bool(_) => MirTy::Prim(PrimTy::Bool),
        ConstVal::Str(_) => MirTy::Prim(PrimTy::Str),
        ConstVal::Char(_) => MirTy::Prim(PrimTy::Char),
        ConstVal::Unit | ConstVal::None => MirTy::Unit,
    }
}

fn format_float(bits: u64, prim: PrimTy) -> String {
    if prim == PrimTy::F32 {
        let v = f32::from_bits(bits as u32);
        if v.is_nan() {
            "0x7FC00000".to_owned()
        } else {
            format_float_decimal(f64::from(v))
        }
    } else {
        let v = f64::from_bits(bits);
        if v.is_nan() {
            "0x7FF8000000000000".to_owned()
        } else {
            format_float_decimal(v)
        }
    }
}

// MLIR's float literal grammar requires a decimal point — `3e0` is
// rejected. `{:?}` on `f64` emits `3.0`, but `1e300` for big / tiny
// values, which gets its `.0` here.
fn format_float_decimal(v: f64) -> String {
    if v.is_infinite() {
        if v.is_sign_negative() {
            "0xFFF0000000000000".to_owned()
        } else {
            "0x7FF0000000000000".to_owned()
        }
    } else {
        let s = format!("{v:?}");
        match s.split_once('e') {
            Some((m, e)) if !m.contains('.') => format!("{m}.0e{e}"),
            _ => s,
        }
    }
}

/// Render a scalar `ConstVal` as the attribute body of an
/// `llvm.mlir.global`, typed at the static's declared type. `None` for
/// shapes with no attribute form.
fn format_const_attr(v: &ConstVal, ty: &MirTy, pointer_width: u32) -> Option<String> {
    let ty_str = mlir_type(ty, pointer_width);
    let MirTy::Prim(p) = ty else { return None };
    Some(match v {
        ConstVal::Int { value, .. } if p.is_int() => format!("{value} : {ty_str}"),
        ConstVal::UInt { value, .. } if p.is_int() => format!("{value} : {ty_str}"),
        ConstVal::Char(c) if p.is_int() => format!("{c} : {ty_str}"),
        ConstVal::Bool(b) if *p == PrimTy::Bool => format!("{} : i1", u8::from(*b)),
        ConstVal::Float { bits, ty: fp } if p.is_float() => {
            let v = if *fp == PrimTy::F32 {
                f64::from(f32::from_bits(*bits as u32))
            } else {
                f64::from_bits(*bits)
            };
            let b = if *p == PrimTy::F32 {
                u64::from((v as f32).to_bits())
            } else {
                v.to_bits()
            };
            format!("{} : {ty_str}", format_float(b, *p))
        }
        ConstVal::Int { value, .. } if p.is_float() => {
            format!("{} : {ty_str}", format_float_decimal(*value as f64))
        }
        _ => return None,
    })
}

#[cfg(test)]
mod overflow_tests {
    use super::*;

    #[test]
    fn constant_operands_skip_the_check() {
        let i8_ = |op, l, r| cannot_overflow(op, PrimTy::I8, 8, (l, r));
        assert!(i8_(PrimOp::Add, Some(100), Some(27)));
        assert!(!i8_(PrimOp::Add, Some(100), Some(28)));
        assert!(i8_(PrimOp::Mul, None, Some(1)));
        assert!(i8_(PrimOp::Sub, None, Some(0)));
        assert!(!i8_(PrimOp::Sub, Some(0), None));
        assert!(!i8_(PrimOp::Add, None, Some(1)));
        assert!(!cannot_overflow(
            PrimOp::Sub,
            PrimTy::U8,
            8,
            (Some(1), Some(2))
        ));
        assert!(cannot_overflow(
            PrimOp::Mul,
            PrimTy::U64,
            64,
            (Some(1 << 40), Some(2))
        ));
    }
}

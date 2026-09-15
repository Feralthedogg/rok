//! A whole MIR module → one object: signatures and symbols, function
//! bodies, the generated functions, statics, GC tables (the MLIR
//! emitter's `emit_module`).

use std::collections::{HashMap, HashSet};

use rokc_codegen_mlir::abi;
use rokc_codegen_mlir::mangle::{self, Pkgs};
use rokc_ir_common::{Abi, ConstVal, FnRole, FunctionId, Linkage, PrimTy};
use rokc_mir::{Link, MirModule, MirTy};

use crate::cc;
use crate::lir::{Func, SymId};
use crate::lower::{Ctx, FnLower, Sig, classify};
use crate::obj::{Obj, Sect};
use crate::{Options, wrap};

/// What one module compiled to.
pub struct Compiled {
    pub obj: Obj,
    pub gc_types: Vec<Vec<u32>>,
    pub errors: Vec<(rokc_diagnostic::Span, String)>,
}

pub fn compile(
    module: &MirModule,
    opts: &Options,
    emit: &mut dyn FnMut(&mut Obj, &Func),
) -> Compiled {
    let t = &module.target;
    let conv = cc::Conv::of(t).expect("a supported target");
    let mut pkgs = Pkgs {
        link: module.link.clone(),
        ..Pkgs::default()
    };
    pkgs.extern_statics = module
        .statics
        .iter()
        .filter(|s| s.is_extern)
        .map(|s| s.name.clone())
        .collect();
    if pkgs.link.packages.is_empty() {
        pkgs.link.packages = vec![(
            String::new(),
            mangle::pkg_hash(&rokc_mir::print_mir(module)),
        )];
    }
    if opts.repl.is_some() {
        for (p, h) in &mut pkgs.link.packages {
            if p.is_empty() {
                rokc_codegen_mlir::emit::REPL_PKG_HASH.clone_into(h);
            }
        }
    }
    let coff = t.os == "windows";
    let mut obj = Obj::new(t.arch == "x86_64", !coff && t.os != "macos", coff);
    let mut errors = Vec::new();
    let defines = |name: &str| {
        opts.repl
            .as_ref()
            .is_some_and(|r| r.define.iter().any(|d| d == name))
    };
    let prebuilt_static = |name: &str| {
        pkgs.link.in_prebuilt(name)
            || opts
                .repl
                .as_ref()
                .is_some_and(|r| r.statics.iter().any(|s| s == name))
    };

    // Signatures.
    let mut fns: HashMap<FunctionId, Sig> = HashMap::new();
    let mut c_entries = Vec::new();
    for f in &module.functions {
        let c = match f.facts.abi {
            Abi::C { variadic } => {
                classify(&mut errors, f.span, t, &f.param_tys, &f.ret_ty, variadic)
            }
            Abi::Rok if f.facts.linkage == Linkage::Extern => {
                abi::classify_rok(t, &f.param_tys, &f.ret_ty)
            }
            Abi::Rok => None,
        };
        let mut name = mangle::symbol_for(f, &pkgs);
        let mut sig_c = None;
        let mut c_entry = None;
        match c {
            Some(a) if f.facts.linkage == Linkage::Extern => sig_c = Some(a),
            Some(a) => {
                name = mangle::mangled(f, &pkgs);
                let entry = f
                    .facts
                    .export_name
                    .clone()
                    .unwrap_or_else(|| format!("{name}.c"));
                c_entry = Some(obj.sym(&entry));
                c_entries.push((f.id, a, f.facts.export_name.is_some(), f.span));
            }
            None => {}
        }
        let sym = obj.sym(&name);
        fns.insert(
            f.id,
            Sig {
                sym,
                params: f.param_tys.clone(),
                ret: f.ret_ty.clone(),
                c: sig_c,
                c_entry,
                local: false,
            },
        );
    }
    let private_copy = |f: &rokc_mir::MirFunction| match &pkgs.link.lib {
        Some(lib) => !Link::owns(lib, f.path()) && f.facts.role != FnRole::AnyDispatcher,
        None => pkgs.link.in_prebuilt(f.path()),
    };
    // A REPL cell compiles only what the session does not have.
    let compiled: HashSet<FunctionId> = module
        .functions
        .iter()
        .filter(|f| {
            f.facts.linkage == Linkage::Defined
                && (private_copy(f)
                    || opts
                        .fresh_fns
                        .as_ref()
                        .is_none_or(|s| s.contains(&mangle::symbol_for(f, &pkgs))))
        })
        .map(|f| f.id)
        .collect();
    // Defined here: reached directly, not through the GOT.
    let defined: HashSet<SymId> = module
        .functions
        .iter()
        .filter(|f| compiled.contains(&f.id))
        .flat_map(|f| [Some(fns[&f.id].sym), fns[&f.id].c_entry])
        .flatten()
        .collect();
    for s in fns.values_mut() {
        s.local = defined.contains(&s.sym);
    }
    pkgs.lazy_statics = module
        .statics
        .iter()
        .filter_map(|s| {
            let init = s
                .init_fn
                .and_then(|i| fns.get(&i))
                .map(|f| obj.syms[f.sym as usize].name.clone());
            // A prebuilt library's static is initialized by its `.a`.
            let init = init.or_else(|| pkgs.link.in_prebuilt(&s.name).then(String::new));
            Some((s.name.clone(), init?))
        })
        .collect();
    let local_statics: HashSet<String> = module
        .statics
        .iter()
        .filter(|s| (!s.is_extern || defines(&s.name)) && !prebuilt_static(&s.name))
        .map(|s| s.name.clone())
        .collect();

    let gc_type_base = rokc_mir::gc_abi::USER_TYPE_BASE + pkgs.link.type_offset;
    let mut gc_types: Vec<Vec<u32>> = opts
        .repl
        .as_ref()
        .map(|r| r.gc_tables.clone())
        .unwrap_or_default();
    let pre_tables = gc_types.len();
    let quiet = rokc_codegen_mlir::emit::quiet_functions(module, &pkgs, t);
    let reentrant = rokc_codegen_mlir::emit::reentrant_functions(module);
    let mut ctx = Ctx {
        t,
        conv,
        obj: &mut obj,
        fns: &fns,
        pkgs: &pkgs,
        gc_types: &mut gc_types,
        gc_type_base,
        overflow_checks: opts.overflow_checks,
        debug: opts.debug.then_some(&module.debug),
        local_statics: &local_statics,
        quiet: &quiet,
        reentrant: &reentrant,
        errors: Vec::new(),
    };
    let mut funcs: Vec<(Func, bool, bool)> = Vec::new();

    for f in &module.functions {
        if !compiled.contains(&f.id) {
            continue;
        }
        let sym = fns[&f.id].sym;
        let func = FnLower::new(&mut ctx, f, sym).lower();
        let weak = pkgs.link.lib.is_some() && f.facts.role == FnRole::AnyDispatcher;
        let private = match &pkgs.link.lib {
            Some(lib) => !Link::owns(lib, f.path()) && f.facts.role != FnRole::AnyDispatcher,
            None => pkgs.link.in_prebuilt(f.path()),
        };
        funcs.push((func, !private, weak));
    }
    for (id, a, exported, span) in &c_entries {
        let sig = &fns[id];
        let Some(entry) = sig.c_entry else { continue };
        let name = ctx.obj.syms[entry as usize].name.clone();
        let func = wrap::generated(&mut ctx, &name, entry, *span, |l| l.c_entry(sig, a));
        funcs.push((func, *exported, false));
    }
    // `rok.register_types` (the dependencies' first), called from `main`.
    let register_name = match &pkgs.link.lib {
        Some(lib) => format!("rok.register_types.{lib}"),
        None => "rok.register_types".to_owned(),
    };
    let register = ctx.sym(&register_name);
    if let Some(m) = module
        .functions
        .iter()
        .find(|f| f.facts.role == FnRole::Main)
    {
        let user = fns[&m.id].sym;
        if opts.repl.is_some() {
            let s = ctx.sym("rok_repl_cell");
            let func = wrap::generated(&mut ctx, "rok_repl_cell", s, m.span, |l| {
                l.repl_cell(user, &m.ret_ty, register)
            });
            funcs.push((func, true, false));
        } else {
            let s = ctx.sym("main");
            let func = wrap::generated(&mut ctx, "main", s, m.span, |l| {
                l.main_wrapper(user, &m.ret_ty, register)
            });
            funcs.push((func, true, false));
        }
    }
    // Statics.
    for s in &module.statics {
        let name = pkgs.static_sym(&s.name);
        let sym = ctx.sym(&name);
        let (size, align) = t.size_align(&s.ty);
        if s.is_extern && defines(&s.name) {
            ctx.obj
                .define_data(sym, Sect::Data, &vec![0; size as usize], align, true);
            continue;
        }
        let lazy = pkgs.lazy_statics.get(&s.name).cloned();
        if prebuilt_static(&s.name) {
            // A prebuilt library's `.init` is in its `.a`; an earlier REPL
            // cell's stays to itself (a private copy here).
            if let Some(init) = lazy.filter(|_| !pkgs.link.in_prebuilt(&s.name)) {
                let state = ctx.sym(&format!("{name}.state"));
                let init = ctx.sym(&init);
                let f_sym = ctx.sym(&format!("{name}.init"));
                let iname = format!("{name}.init");
                let func =
                    wrap::generated(&mut ctx, &iname, f_sym, rokc_diagnostic::Span::DUMMY, |l| {
                        l.lazy_init(state, sym, true, init, &s.ty)
                    });
                funcs.push((func, false, false));
            }
            continue;
        }
        if s.is_extern {
            continue;
        }
        let global = opts.repl.is_some()
            || pkgs
                .link
                .lib
                .as_deref()
                .is_some_and(|l| Link::owns(l, &s.name));
        if let Some(init) = lazy {
            ctx.obj
                .define_data(sym, Sect::Data, &vec![0; size as usize], align, global);
            let state = ctx.sym(&format!("{name}.state"));
            ctx.obj.define_data(state, Sect::Data, &[0], 1, global);
            let init = ctx.sym(&init);
            let f_sym = ctx.sym(&format!("{name}.init"));
            let iname = format!("{name}.init");
            let func =
                wrap::generated(&mut ctx, &iname, f_sym, rokc_diagnostic::Span::DUMMY, |l| {
                    l.lazy_init(state, sym, false, init, &s.ty)
                });
            // Exported by a prebuilt library that owns the static.
            let export = pkgs
                .link
                .lib
                .as_deref()
                .is_some_and(|l| Link::owns(l, &s.name));
            funcs.push((func, export, false));
            continue;
        }
        if let ConstVal::Str(text) = &s.init {
            let lit = ctx.obj.string(text);
            let pw = t.pointer_width / 8;
            let mut bytes = vec![0u8; 2 * pw as usize];
            bytes[pw as usize..].copy_from_slice(&(text.len() as u64).to_le_bytes()[..pw as usize]);
            let sect = if s.is_mut {
                Sect::Data
            } else {
                Sect::DataConst
            };
            let off = ctx.obj.define_data(sym, sect, &bytes, pw, global);
            ctx.obj.abs64(sect, off, lit);
            continue;
        }
        match const_bytes(&s.init, &s.ty, t) {
            Some(bytes) => {
                let sect = if s.is_mut { Sect::Data } else { Sect::Const };
                ctx.obj.define_data(sym, sect, &bytes, align, global);
            }
            None => errors.push((
                rokc_diagnostic::Span::DUMMY,
                format!("unsupported in codegen: initializer of static `{}`", s.name),
            )),
        }
    }
    // GC support: the ScanTables and the static roots.
    let mut tables = Vec::new();
    for i in pre_tables..ctx.gc_types.len() {
        let words = ctx.gc_types[i].clone();
        let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        let sym = ctx.sym(&format!("rok.scan{i}"));
        ctx.obj.define_data(sym, Sect::Const, &bytes, 4, false);
        tables.push((gc_type_base + i as u32, sym));
    }
    let mut roots = Vec::new();
    for s in &module.statics {
        if !((!s.is_extern || defines(&s.name)) && !prebuilt_static(&s.name)) {
            continue;
        }
        let sym = ctx.sym(&pkgs.static_sym(&s.name));
        for off in t.root_offsets(&s.ty) {
            roots.push((sym, true, off));
        }
    }
    let deps: Vec<SymId> = pkgs
        .link
        .prebuilt
        .iter()
        .map(|d| ctx.sym(&format!("rok.register_types.{d}")))
        .collect();
    let func = wrap::generated(
        &mut ctx,
        &register_name,
        register,
        rokc_diagnostic::Span::DUMMY,
        |l| l.register_types(&tables, &roots, &deps),
    );
    funcs.push((func, pkgs.link.lib.is_some(), false));
    errors.append(&mut ctx.errors);
    drop(ctx);

    for (f, global, weak) in &funcs {
        emit(&mut obj, f);
        let s = &mut obj.syms[f.sym as usize];
        s.global = *global;
        s.weak = *weak;
    }
    Compiled {
        obj,
        gc_types,
        errors,
    }
}

/// A scalar static's initial bytes (the emitter's `format_const_attr`).
fn const_bytes(v: &ConstVal, ty: &MirTy, t: &rokc_mir::Target) -> Option<Vec<u8>> {
    let MirTy::Prim(p) = ty else { return None };
    let size = t.size_align(ty).0 as usize;
    let int = |x: i128| Some(x.to_le_bytes()[..size].to_vec());
    match v {
        ConstVal::Int { value, .. } if p.is_int() => int(*value),
        ConstVal::UInt { value, .. } if p.is_int() => int(*value as i128),
        ConstVal::Char(c) if p.is_int() => int(i128::from(*c)),
        ConstVal::Bool(b) if *p == PrimTy::Bool => Some(vec![u8::from(*b)]),
        ConstVal::Float { bits, ty: fp } if p.is_float() => {
            let v = if *fp == PrimTy::F32 {
                f64::from(f32::from_bits(*bits as u32))
            } else {
                f64::from_bits(*bits)
            };
            Some(if *p == PrimTy::F32 {
                (v as f32).to_bits().to_le_bytes().to_vec()
            } else {
                v.to_bits().to_le_bytes().to_vec()
            })
        }
        ConstVal::Int { value, .. } if p.is_float() => {
            let v = *value as f64;
            Some(if *p == PrimTy::F32 {
                (v as f32).to_bits().to_le_bytes().to_vec()
            } else {
                v.to_bits().to_le_bytes().to_vec()
            })
        }
        _ => None,
    }
}

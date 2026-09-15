//! `-g` (spec 9.9.6): DWARF 4 for the functions of an object, as the
//! MLIR emitter's debug info describes them (`rokc_codegen_mlir::debug`):
//! one subprogram per function with a source position, named by its rok
//! path; its parameters and named locals in their stack slots (`fp`
//! relative), in lexical blocks; their types (primitives, structs with
//! field names, tuples, `str`, `any`, arrays); a line table.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rokc_ir_common::PrimTy;
use rokc_mir::{MirTy, Target};

use crate::obj::{FnRange, Obj, RelKind, Reloc, Section};

const DW_TAG_ARRAY_TYPE: u8 = 0x01;
const DW_TAG_FORMAL_PARAMETER: u8 = 0x05;
const DW_TAG_LEXICAL_BLOCK: u8 = 0x0b;
const DW_TAG_MEMBER: u8 = 0x0d;
const DW_TAG_POINTER_TYPE: u8 = 0x0f;
const DW_TAG_COMPILE_UNIT: u8 = 0x11;
const DW_TAG_STRUCTURE_TYPE: u8 = 0x13;
const DW_TAG_SUBRANGE_TYPE: u8 = 0x21;
const DW_TAG_BASE_TYPE: u8 = 0x24;
const DW_TAG_SUBPROGRAM: u8 = 0x2e;
const DW_TAG_VARIABLE: u8 = 0x34;

const DW_AT_NAME: u8 = 0x03;
const DW_AT_BYTE_SIZE: u8 = 0x0b;
const DW_AT_STMT_LIST: u8 = 0x10;
const DW_AT_LOW_PC: u8 = 0x11;
const DW_AT_HIGH_PC: u8 = 0x12;
const DW_AT_LANGUAGE: u8 = 0x13;
const DW_AT_COMP_DIR: u8 = 0x1b;
const DW_AT_PRODUCER: u8 = 0x25;
const DW_AT_COUNT: u8 = 0x37;
const DW_AT_DATA_MEMBER_LOCATION: u8 = 0x38;
const DW_AT_DECL_FILE: u8 = 0x3a;
const DW_AT_DECL_LINE: u8 = 0x3b;
const DW_AT_ENCODING: u8 = 0x3e;
const DW_AT_FRAME_BASE: u8 = 0x40;
const DW_AT_LOCATION: u8 = 0x02;
const DW_AT_TYPE: u8 = 0x49;
const DW_AT_RANGES: u8 = 0x55;

const DW_FORM_ADDR: u8 = 0x01;
const DW_FORM_DATA1: u8 = 0x0b;
const DW_FORM_DATA2: u8 = 0x05;
const DW_FORM_DATA4: u8 = 0x06;
const DW_FORM_STRING: u8 = 0x08;
const DW_FORM_UDATA: u8 = 0x0f;
const DW_FORM_REF4: u8 = 0x13;
const DW_FORM_SEC_OFFSET: u8 = 0x17;
const DW_FORM_EXPRLOC: u8 = 0x18;

const DW_OP_FBREG: u8 = 0x91;
/// `DW_OP_reg29` (arm64 `x29`) / `DW_OP_reg6` (`x86_64` `rbp`).
const DW_OP_REG29: u8 = 0x6d;
const DW_OP_REG6: u8 = 0x56;
const DW_LANG_C: u16 = 0x0c;

const DW_ATE_BOOLEAN: u8 = 0x02;
const DW_ATE_FLOAT: u8 = 0x04;
const DW_ATE_SIGNED: u8 = 0x05;
const DW_ATE_SIGNED_CHAR: u8 = 0x06;
const DW_ATE_UNSIGNED: u8 = 0x08;
const DW_ATE_UTF: u8 = 0x10;

// Abbreviation codes.
const A_CU: u8 = 1;
const A_SUB: u8 = 2;
const A_PARAM: u8 = 3;
const A_VAR: u8 = 4;
const A_BLOCK: u8 = 5;
const A_BASE: u8 = 6;
const A_PTR_NAMED: u8 = 7;
const A_PTR_TO: u8 = 8;
const A_STRUCT: u8 = 9;
const A_MEMBER1: u8 = 10;
const A_ARRAY: u8 = 11;
const A_SUBRANGE: u8 = 12;
const A_STRUCT_EMPTY: u8 = 13;
const A_MEMBER4: u8 = 14;

fn uleb(b: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            b.push(byte);
            return;
        }
        b.push(byte | 0x80);
    }
}

fn sleb(b: &mut Vec<u8>, mut v: i64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        let done = (v == 0 && byte & 0x40 == 0) || (v == -1 && byte & 0x40 != 0);
        b.push(if done { byte } else { byte | 0x80 });
        if done {
            return;
        }
    }
}

fn cstr(b: &mut Vec<u8>, s: &str) {
    b.extend_from_slice(s.as_bytes());
    b.push(0);
}

fn abbrevs() -> Vec<u8> {
    let mut b = Vec::new();
    let mut add = |code: u8, tag: u8, children: bool, attrs: &[(u8, u8)]| {
        b.push(code);
        b.push(tag);
        b.push(u8::from(children));
        for (a, f) in attrs {
            b.push(*a);
            b.push(*f);
        }
        b.extend_from_slice(&[0, 0]);
    };
    add(
        A_CU,
        DW_TAG_COMPILE_UNIT,
        true,
        &[
            (DW_AT_PRODUCER, DW_FORM_STRING),
            (DW_AT_LANGUAGE, DW_FORM_DATA2),
            (DW_AT_NAME, DW_FORM_STRING),
            (DW_AT_COMP_DIR, DW_FORM_STRING),
            (DW_AT_STMT_LIST, DW_FORM_SEC_OFFSET),
            (DW_AT_LOW_PC, DW_FORM_ADDR),
            (DW_AT_HIGH_PC, DW_FORM_DATA4),
        ],
    );
    add(
        A_SUB,
        DW_TAG_SUBPROGRAM,
        true,
        &[
            (DW_AT_NAME, DW_FORM_STRING),
            (DW_AT_DECL_FILE, DW_FORM_UDATA),
            (DW_AT_DECL_LINE, DW_FORM_UDATA),
            (DW_AT_LOW_PC, DW_FORM_ADDR),
            (DW_AT_HIGH_PC, DW_FORM_DATA4),
            (DW_AT_FRAME_BASE, DW_FORM_EXPRLOC),
        ],
    );
    let var = [
        (DW_AT_NAME, DW_FORM_STRING),
        (DW_AT_DECL_FILE, DW_FORM_UDATA),
        (DW_AT_DECL_LINE, DW_FORM_UDATA),
        (DW_AT_TYPE, DW_FORM_REF4),
        (DW_AT_LOCATION, DW_FORM_EXPRLOC),
    ];
    add(A_PARAM, DW_TAG_FORMAL_PARAMETER, false, &var);
    add(A_VAR, DW_TAG_VARIABLE, false, &var);
    add(
        A_BLOCK,
        DW_TAG_LEXICAL_BLOCK,
        true,
        &[(DW_AT_RANGES, DW_FORM_SEC_OFFSET)],
    );
    add(
        A_BASE,
        DW_TAG_BASE_TYPE,
        false,
        &[
            (DW_AT_NAME, DW_FORM_STRING),
            (DW_AT_ENCODING, DW_FORM_DATA1),
            (DW_AT_BYTE_SIZE, DW_FORM_UDATA),
        ],
    );
    add(
        A_PTR_NAMED,
        DW_TAG_POINTER_TYPE,
        false,
        &[
            (DW_AT_NAME, DW_FORM_STRING),
            (DW_AT_BYTE_SIZE, DW_FORM_UDATA),
        ],
    );
    add(
        A_PTR_TO,
        DW_TAG_POINTER_TYPE,
        false,
        &[(DW_AT_TYPE, DW_FORM_REF4), (DW_AT_BYTE_SIZE, DW_FORM_UDATA)],
    );
    add(
        A_STRUCT,
        DW_TAG_STRUCTURE_TYPE,
        true,
        &[
            (DW_AT_NAME, DW_FORM_STRING),
            (DW_AT_BYTE_SIZE, DW_FORM_UDATA),
        ],
    );
    add(
        A_MEMBER1,
        DW_TAG_MEMBER,
        false,
        &[
            (DW_AT_NAME, DW_FORM_STRING),
            (DW_AT_TYPE, DW_FORM_REF4),
            (DW_AT_DATA_MEMBER_LOCATION, DW_FORM_DATA1),
        ],
    );
    add(
        A_ARRAY,
        DW_TAG_ARRAY_TYPE,
        true,
        &[(DW_AT_TYPE, DW_FORM_REF4)],
    );
    add(
        A_SUBRANGE,
        DW_TAG_SUBRANGE_TYPE,
        false,
        &[(DW_AT_COUNT, DW_FORM_UDATA)],
    );
    add(
        A_STRUCT_EMPTY,
        DW_TAG_STRUCTURE_TYPE,
        false,
        &[
            (DW_AT_NAME, DW_FORM_STRING),
            (DW_AT_BYTE_SIZE, DW_FORM_UDATA),
        ],
    );
    add(
        A_MEMBER4,
        DW_TAG_MEMBER,
        false,
        &[
            (DW_AT_NAME, DW_FORM_STRING),
            (DW_AT_TYPE, DW_FORM_REF4),
            (DW_AT_DATA_MEMBER_LOCATION, DW_FORM_DATA4),
        ],
    );
    b.push(0);
    b
}

/// The `.debug_info` unit being written: type DIEs by key.
struct Info<'a> {
    b: Vec<u8>,
    relocs: Vec<Reloc>,
    types: HashMap<String, u32>,
    t: &'a Target,
    names: &'a HashMap<u32, (String, Vec<String>)>,
    /// `.debug_ranges`, entries relative to the unit's `low_pc`.
    ranges: Vec<u8>,
    cu_low: u32,
}

impl Info<'_> {
    fn u32(&mut self, v: u32) {
        self.b.extend_from_slice(&v.to_le_bytes());
    }

    /// Offset `v` into debug section `sect` (an index of `Obj::extra`).
    fn sec_off(&mut self, sect: u32, v: u32) {
        self.relocs.push(Reloc {
            off: self.b.len() as u32,
            kind: RelKind::SecOff32,
            sym: sect,
        });
        self.u32(v);
    }

    /// The address `at` of function `sym`: its object address (a
    /// section-relative relocation, as LLVM writes them for dsymutil).
    fn addr(&mut self, sym: u32, at: u32) {
        self.relocs.push(Reloc {
            off: self.b.len() as u32,
            kind: RelKind::Abs64,
            sym,
        });
        self.b.extend_from_slice(&u64::from(at).to_le_bytes());
    }

    fn base(&mut self, p: PrimTy) -> Option<u32> {
        let w = self.t.pointer_width / 8;
        let (name, size, enc) = match p {
            PrimTy::I8 => ("i8", 1, DW_ATE_SIGNED),
            PrimTy::I16 => ("i16", 2, DW_ATE_SIGNED),
            PrimTy::I32 => ("i32", 4, DW_ATE_SIGNED),
            PrimTy::I64 => ("i64", 8, DW_ATE_SIGNED),
            PrimTy::Isize => ("isize", w, DW_ATE_SIGNED),
            PrimTy::U8 => ("u8", 1, DW_ATE_UNSIGNED),
            PrimTy::U16 => ("u16", 2, DW_ATE_UNSIGNED),
            PrimTy::U32 => ("u32", 4, DW_ATE_UNSIGNED),
            PrimTy::U64 => ("u64", 8, DW_ATE_UNSIGNED),
            PrimTy::Usize => ("usize", w, DW_ATE_UNSIGNED),
            PrimTy::F32 => ("f32", 4, DW_ATE_FLOAT),
            PrimTy::F64 => ("f64", 8, DW_ATE_FLOAT),
            PrimTy::Bool => ("bool", 1, DW_ATE_BOOLEAN),
            PrimTy::CChar => ("c_char", 1, DW_ATE_SIGNED_CHAR),
            PrimTy::Char => ("char", 4, DW_ATE_UTF),
            PrimTy::Str => return None,
        };
        if let Some(o) = self.types.get(name) {
            return Some(*o);
        }
        let off = self.b.len() as u32;
        self.b.push(A_BASE);
        cstr(&mut self.b, name);
        self.b.push(enc);
        uleb(&mut self.b, u64::from(size));
        self.types.insert(name.to_owned(), off);
        Some(off)
    }

    fn structure(&mut self, name: &str, size: u32, members: &[(String, u32, u32)]) -> u32 {
        let off = self.b.len() as u32;
        if members.is_empty() {
            self.b.push(A_STRUCT_EMPTY);
            cstr(&mut self.b, name);
            uleb(&mut self.b, u64::from(size));
            return off;
        }
        self.b.push(A_STRUCT);
        cstr(&mut self.b, name);
        uleb(&mut self.b, u64::from(size));
        for (n, ty, at) in members {
            if *at < 256 {
                self.b.push(A_MEMBER1);
                cstr(&mut self.b, n);
                self.u32(*ty);
                self.b.push(*at as u8);
            } else {
                self.b.push(A_MEMBER4);
                cstr(&mut self.b, n);
                self.u32(*ty);
                self.u32(*at);
            }
        }
        self.b.push(0);
        off
    }

    /// The type DIE of `ty`, written on first use; `None` for `()`.
    fn ty(&mut self, ty: &MirTy) -> Option<u32> {
        let key = format!("{ty:?}");
        if let Some(o) = self.types.get(&key) {
            return Some(*o);
        }
        let t = self.t;
        let w = t.pointer_width / 8;
        let size = t.size_align(ty).0;
        let off = match ty {
            MirTy::Unit => return None,
            MirTy::Prim(PrimTy::Str) => {
                let u8_ = self.base(PrimTy::U8)?;
                let ptr = self.b.len() as u32;
                self.b.push(A_PTR_TO);
                self.u32(u8_);
                uleb(&mut self.b, u64::from(w));
                let len = self.base(PrimTy::Usize)?;
                self.structure(
                    "str",
                    size,
                    &[("ptr".into(), ptr, 0), ("len".into(), len, w)],
                )
            }
            MirTy::Prim(p) => return self.base(*p),
            MirTy::GcRef | MirTy::Fn(..) | MirTy::Mlir(_) => {
                let name = match ty {
                    MirTy::GcRef => "gcref",
                    MirTy::Fn(..) => "fn",
                    _ => "mlir",
                };
                let o = self.b.len() as u32;
                self.b.push(A_PTR_NAMED);
                cstr(&mut self.b, name);
                uleb(&mut self.b, u64::from(w));
                o
            }
            MirTy::Any => {
                let tag = self.base(PrimTy::I32)?;
                let payload = self.base(PrimTy::Usize)?;
                self.structure(
                    "any",
                    size,
                    &[("tag".into(), tag, 0), ("payload".into(), payload, w)],
                )
            }
            MirTy::Tuple(ps) => {
                let m = self.members(ty, ps, &[]);
                self.structure("tuple", size, &m)
            }
            MirTy::Struct(id, ps) => {
                let (name, names) = self
                    .names
                    .get(&id.0)
                    .cloned()
                    .unwrap_or_else(|| (format!("Struct#{}", id.0), Vec::new()));
                let names = if names.len() == ps.len() {
                    names
                } else {
                    Vec::new()
                };
                let m = self.members(ty, ps, &names);
                self.structure(&name, size, &m)
            }
            MirTy::Array(..) | MirTy::Union(..) => {
                let (elem, n) = match ty {
                    MirTy::Array(e, n) => ((**e).clone(), *n),
                    MirTy::Union(_, n) => (MirTy::Prim(PrimTy::Usize), *n),
                    _ => unreachable!(),
                };
                let base = self.ty(&elem)?;
                let o = self.b.len() as u32;
                self.b.push(A_ARRAY);
                self.u32(base);
                self.b.push(A_SUBRANGE);
                uleb(&mut self.b, u64::from(n));
                self.b.push(0);
                o
            }
        };
        self.types.insert(key, off);
        Some(off)
    }

    fn members(
        &mut self,
        agg: &MirTy,
        parts: &[MirTy],
        names: &[String],
    ) -> Vec<(String, u32, u32)> {
        let offs = self.t.field_offsets(agg);
        let mut out = Vec::new();
        for (i, (p, off)) in parts.iter().zip(offs).enumerate() {
            if let Some(ty) = self.ty(p) {
                let n = names.get(i).cloned().unwrap_or_else(|| i.to_string());
                out.push((n, ty, off));
            }
        }
        out
    }
}

/// The code of scope `id` of `f` and its nested scopes, as merged
/// `[start, end)` ranges: interleaved with other scopes' code, so not
/// one range.
fn scope_code(id: u32, d: &crate::lir::FnDebug, f: &FnRange) -> Vec<(u32, u32)> {
    let mut ids = vec![id];
    let mut n = 0;
    while n < ids.len() {
        let p = ids[n];
        ids.extend(d.scopes.iter().filter(|s| s.1 == p).map(|s| s.0));
        n += 1;
    }
    let mut out: Vec<(u32, u32)> = Vec::new();
    for (i, &(at, _, _, sc)) in f.lines.iter().enumerate() {
        let end = f.lines.get(i + 1).map_or(f.len, |n| n.0);
        if end <= at || !ids.contains(&sc) {
            continue;
        }
        match out.last_mut() {
            Some(last) if last.1 == at => last.1 = end,
            _ => out.push((at, end)),
        }
    }
    out
}

/// Add the debug sections of `obj`'s functions.
pub fn write(obj: &mut Obj, t: &Target, names: &HashMap<u32, (String, Vec<String>)>) {
    let fns: Vec<&FnRange> = obj.fns.iter().filter(|f| f.debug.is_some()).collect();
    let Some(first) = fns.first() else { return };
    let cwd = std::env::current_dir().unwrap_or_default();
    let files: Vec<PathBuf> = rokc_diagnostic::registered_files()
        .into_iter()
        .map(|(p, _)| cwd.join(p))
        .collect();
    let first_file = first.debug.as_ref().map_or(1, |d| d.0.file);
    let cu_path = files
        .get(first_file as usize - 1)
        .cloned()
        .unwrap_or_default();
    let dir_of = |p: &Path| {
        p.parent()
            .map_or_else(String::new, |d| d.to_string_lossy().into_owned())
    };

    // The sections this adds, by `Obj::extra` index.
    let base = obj.extra.len() as u32;
    let (abbrev_sect, line_sect, ranges_sect) = (base, base + 2, base + 3);
    let first = obj.fns.iter().min_by_key(|f| f.start);
    let mut info = Info {
        b: Vec::new(),
        relocs: Vec::new(),
        types: HashMap::new(),
        t,
        names,
        ranges: Vec::new(),
        cu_low: first.map_or(0, |f| f.start),
    };
    // Header (length patched below), then the unit.
    info.u32(0);
    info.b.extend_from_slice(&4u16.to_le_bytes());
    info.sec_off(abbrev_sect, 0);
    info.b.push(8);
    info.b.push(A_CU);
    cstr(&mut info.b, "rokc");
    info.b.extend_from_slice(&DW_LANG_C.to_le_bytes());
    cstr(
        &mut info.b,
        &cu_path
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned()),
    );
    cstr(&mut info.b, &dir_of(&cu_path));
    info.sec_off(line_sect, 0);
    // The text section is one range from its first function.
    let text_start = obj.fns.first().map_or(0, |f| f.start);
    let text_end = obj.fns.last().map_or(0, |f| f.start + f.len);
    info.addr(first.map_or(0, |f| f.sym), first.map_or(0, |f| f.start));
    info.u32(text_end - text_start);
    // Types first, so variables refer back to them.
    for f in &fns {
        for v in &f.debug.as_ref().expect("debug").0.vars {
            info.ty(&v.ty);
        }
    }
    for f in &fns {
        let (d, offs) = f.debug.as_ref().expect("debug");
        info.b.push(A_SUB);
        cstr(&mut info.b, &d.name);
        uleb(&mut info.b, u64::from(d.file));
        uleb(&mut info.b, u64::from(d.line));
        info.addr(f.sym, f.start);
        info.u32(f.len);
        // The frame pointer: `x29` / `rbp`.
        info.b
            .extend_from_slice(&[1, if obj.x86 { DW_OP_REG6 } else { DW_OP_REG29 }]);
        // Scopes that hold a variable (or one that does).
        let mut live: Vec<u32> = Vec::new();
        for v in &d.vars {
            let mut s = v.scope;
            while s != 0 && !live.contains(&s) {
                live.push(s);
                s = d.scopes.iter().find(|(i, _)| *i == s).map_or(0, |x| x.1);
            }
        }
        let var_die = |info: &mut Info<'_>, i: usize| {
            let v = &d.vars[i];
            let Some(ty) = info.ty(&v.ty) else { return };
            info.b.push(if v.arg.is_some() { A_PARAM } else { A_VAR });
            cstr(&mut info.b, &v.name);
            uleb(&mut info.b, u64::from(d.file));
            uleb(&mut info.b, u64::from(v.line));
            info.u32(ty);
            let mut loc = vec![DW_OP_FBREG];
            sleb(&mut loc, i64::from(offs[i]));
            uleb(&mut info.b, loc.len() as u64);
            info.b.extend_from_slice(&loc);
        };
        scope(&mut info, 0, d, &live, f, ranges_sect, &var_die);
        info.b.push(0);
    }
    info.b.push(0);
    let len = info.b.len() as u32 - 4;
    info.b[..4].copy_from_slice(&len.to_le_bytes());

    let line = line_program(&fns, &files, &dir_of, if obj.x86 { 1 } else { 4 });
    let mut sect = |name: &'static str, data: Vec<u8>, relocs: Vec<Reloc>| {
        obj.extra.push((
            "__DWARF",
            name,
            0x0200_0000,
            Section {
                data,
                relocs,
                align: 0,
            },
        ));
    };
    sect("__debug_abbrev", abbrevs(), Vec::new());
    sect("__debug_info", info.b, info.relocs);
    sect("__debug_line", line.0, line.1);
    sect("__debug_ranges", info.ranges, Vec::new());
}

/// The variables of scope `id` and its lexical blocks (those holding a
/// variable), nested.
fn scope(
    info: &mut Info<'_>,
    id: u32,
    d: &crate::lir::FnDebug,
    live: &[u32],
    f: &FnRange,
    ranges_sect: u32,
    var_die: &dyn Fn(&mut Info<'_>, usize),
) {
    for (i, v) in d.vars.iter().enumerate() {
        if v.scope == id || (id == 0 && !live.contains(&v.scope) && v.scope != 0) {
            var_die(info, i);
        }
    }
    for &(c, parent) in &d.scopes {
        if parent != id || !live.contains(&c) {
            continue;
        }
        info.b.push(A_BLOCK);
        let at = info.ranges.len() as u32;
        info.sec_off(ranges_sect, at);
        let rel = f.start - info.cu_low;
        for (lo, hi) in scope_code(c, d, f) {
            info.ranges
                .extend_from_slice(&u64::from(rel + lo).to_le_bytes());
            info.ranges
                .extend_from_slice(&u64::from(rel + hi).to_le_bytes());
        }
        info.ranges.extend_from_slice(&[0; 16]);
        scope(info, c, d, live, f, ranges_sect, var_die);
        info.b.push(0);
    }
}

/// `.debug_line`: one sequence per function, rows `unit`-byte aligned
/// (the instruction size, 1 on `x86_64`).
fn line_program(
    fns: &[&FnRange],
    files: &[PathBuf],
    dir_of: &dyn Fn(&Path) -> String,
    unit: u32,
) -> (Vec<u8>, Vec<Reloc>) {
    let mut b = Vec::new();
    let mut relocs = Vec::new();
    b.extend_from_slice(&0u32.to_le_bytes());
    b.extend_from_slice(&4u16.to_le_bytes());
    let hl = b.len();
    b.extend_from_slice(&0u32.to_le_bytes());
    let header_start = b.len();
    b.extend_from_slice(&[unit as u8, 1, 1]); // min inst length, max ops, default_is_stmt
    b.push((-5i8) as u8);
    b.push(14);
    b.push(13);
    b.extend_from_slice(&[0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1]);
    let mut dirs: Vec<String> = Vec::new();
    let mut entries = Vec::new();
    for f in files {
        let d = dir_of(f);
        let k = dirs.iter().position(|x| *x == d).unwrap_or_else(|| {
            dirs.push(d.clone());
            dirs.len() - 1
        });
        entries.push((
            f.file_name()
                .map_or_else(String::new, |n| n.to_string_lossy().into_owned()),
            k + 1,
        ));
    }
    for d in &dirs {
        cstr(&mut b, d);
    }
    b.push(0);
    for (n, d) in &entries {
        cstr(&mut b, n);
        uleb(&mut b, *d as u64);
        b.extend_from_slice(&[0, 0]);
    }
    b.push(0);
    let header_len = (b.len() - header_start) as u32;
    b[hl..hl + 4].copy_from_slice(&header_len.to_le_bytes());
    for f in fns {
        let (d, _) = f.debug.as_ref().expect("debug");
        // DW_LNE_set_address
        b.extend_from_slice(&[0, 9, 2]);
        relocs.push(Reloc {
            off: b.len() as u32,
            kind: RelKind::Abs64,
            sym: f.sym,
        });
        b.extend_from_slice(&u64::from(f.start).to_le_bytes());
        // DW_LNS_set_file
        b.push(4);
        uleb(&mut b, u64::from(d.file));
        let (mut addr, mut line) = (0u32, 1i64);
        let mut rows = vec![(0u32, d.line, 1u32)];
        rows.extend(f.lines.iter().map(|&(a, l, c, _)| (a, l, c)));
        for (a, l, c) in rows {
            if a > addr {
                b.push(2); // advance_pc
                uleb(&mut b, u64::from((a - addr) / unit));
                addr = a;
            }
            if i64::from(l) != line {
                b.push(3); // advance_line
                sleb(&mut b, i64::from(l) - line);
                line = i64::from(l);
            }
            b.push(5); // set_column
            uleb(&mut b, u64::from(c));
            b.push(1); // copy
        }
        if f.len > addr {
            b.push(2);
            uleb(&mut b, u64::from((f.len - addr) / unit));
        }
        b.extend_from_slice(&[0, 1, 1]); // end_sequence
    }
    let total = b.len() as u32 - 4;
    b[..4].copy_from_slice(&total.to_le_bytes());
    (b, relocs)
}

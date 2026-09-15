//! A relocatable object in the making: sections, symbols, relocations.
//! The container format (`macho`, ..) only serializes it.

use std::collections::HashMap;

use crate::lir::SymId;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Sect {
    Text,
    /// Read-only data without relocations.
    Const,
    /// Read-only data with relocations (pointers).
    DataConst,
    Data,
}

pub const SECTS: [Sect; 4] = [Sect::Text, Sect::Const, Sect::DataConst, Sect::Data];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RelKind {
    /// `bl` / `b` to a symbol.
    Branch26,
    /// `adrp` of a symbol's page / the low 12 bits (`add` or a scaled
    /// load / store offset).
    Page21,
    PageOff12,
    /// `adrp` / `ldr` of the symbol's GOT slot.
    GotPage21,
    GotPageOff12,
    /// `adrp` / `ldr` of a thread-local's descriptor.
    TlvPage21,
    TlvPageOff12,
    /// A 64-bit absolute address (data).
    Abs64,
    /// `x86_64` `call rel32` to a function.
    X86Call,
    /// `x86_64` `[rip + rel32]` of a symbol.
    X86Pc32,
    /// `x86_64` `mov reg, [rip + rel32]` of the symbol's GOT slot.
    X86GotLoad,
    /// `x86_64` `mov reg, [rip + rel32]` of a thread-local: its TLV
    /// descriptor (Mach-O), its thread-pointer offset (ELF initial exec).
    X86Tls,
    /// COFF: a thread-local's 32-bit offset in the TLS section (`x86_64`
    /// displacement).
    X86SecRel,
    /// COFF arm64: `add` of bits 12..24 / 0..12 of a thread-local's TLS
    /// section offset.
    SecRelHi12,
    SecRelLo12,
    /// DWARF `sec_offset`: 32 bits into the debug section `sym` (an
    /// index of `Obj::extra`). ELF relocates it (the linker joins the
    /// sections of all objects); Mach-O keeps the offset in the object.
    SecOff32,
}

#[derive(Clone, Copy, Debug)]
pub struct Reloc {
    pub off: u32,
    pub kind: RelKind,
    pub sym: SymId,
}

#[derive(Clone, Debug, Default)]
pub struct Section {
    pub data: Vec<u8>,
    pub relocs: Vec<Reloc>,
    /// log2 of the alignment.
    pub align: u32,
}

impl Section {
    /// Align the end to `align` bytes; the offset there.
    pub fn align_to(&mut self, align: u32) -> u32 {
        let a = align.max(1);
        while self.data.len() % a as usize != 0 {
            self.data.push(0);
        }
        self.align = self.align.max(a.trailing_zeros());
        self.data.len() as u32
    }
}

#[derive(Clone, Debug)]
pub struct Sym {
    pub name: String,
    /// `(section, offset, size)` when defined here.
    pub def: Option<(Sect, u32, u32)>,
    pub global: bool,
    pub weak: bool,
}

/// A code range of a function (unwind info, debug info).
#[derive(Clone, Debug)]
pub struct FnRange {
    pub sym: SymId,
    pub start: u32,
    pub len: u32,
    /// `(code offset, line, column, scope)` rows.
    pub lines: Vec<(u32, u32, u32, u32)>,
    /// `-g`: the function's facts, and each variable's offset from the
    /// frame pointer.
    pub debug: Option<(crate::lir::FnDebug, Vec<i32>)>,
}

#[derive(Default)]
pub struct Obj {
    pub syms: Vec<Sym>,
    by_name: HashMap<String, SymId>,
    pub sects: HashMap<Sect, Section>,
    strings: HashMap<String, SymId>,
    pub fns: Vec<FnRange>,
    /// More sections: `(segment, section, flags, contents)` (debug info).
    pub extra: Vec<(&'static str, &'static str, u32, Section)>,
    /// `x86_64` code (else arm64).
    pub x86: bool,
    /// An ELF object (else Mach-O, or COFF).
    pub elf: bool,
    /// A COFF object (Windows: no GOT, TLS through `_tls_index`).
    pub coff: bool,
}

impl Obj {
    #[must_use]
    pub fn new(x86: bool, elf: bool, coff: bool) -> Self {
        let mut o = Self {
            x86,
            elf,
            coff,
            ..Self::default()
        };
        for s in SECTS {
            o.sects.insert(s, Section::default());
        }
        o
    }

    /// The symbol named `name` (undefined until `define`d).
    pub fn sym(&mut self, name: &str) -> SymId {
        if let Some(s) = self.by_name.get(name) {
            return *s;
        }
        self.syms.push(Sym {
            name: name.to_owned(),
            def: None,
            global: true,
            weak: false,
        });
        let id = self.syms.len() as SymId - 1;
        self.by_name.insert(name.to_owned(), id);
        id
    }

    pub fn sect(&mut self, s: Sect) -> &mut Section {
        self.sects.get_mut(&s).expect("section")
    }

    /// Define `sym` at the end of `sect` with `bytes` (aligned to
    /// `align`); returns its offset.
    pub fn define_data(
        &mut self,
        sym: SymId,
        sect: Sect,
        bytes: &[u8],
        align: u32,
        global: bool,
    ) -> u32 {
        let s = self.sect(sect);
        let off = s.align_to(align);
        s.data.extend_from_slice(bytes);
        let sy = &mut self.syms[sym as usize];
        sy.def = Some((sect, off, bytes.len() as u32));
        sy.global = global;
        off
    }

    /// A pointer-sized relocated word at `off` of `sect`.
    pub fn abs64(&mut self, sect: Sect, off: u32, target: SymId) {
        self.sect(sect).relocs.push(Reloc {
            off,
            kind: RelKind::Abs64,
            sym: target,
        });
    }

    /// A string literal's NUL-terminated bytes (one per content).
    pub fn string(&mut self, text: &str) -> SymId {
        if let Some(s) = self.strings.get(text) {
            return *s;
        }
        let name = rokc_codegen_mlir::mangle::str_global(text);
        let sym = self.sym(&name);
        let mut bytes = text.as_bytes().to_vec();
        bytes.push(0);
        self.define_data(sym, Sect::Const, &bytes, 1, false);
        self.strings.insert(text.to_owned(), sym);
        sym
    }
}

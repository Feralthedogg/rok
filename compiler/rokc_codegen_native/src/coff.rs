//! COFF relocatable object writer (Windows), `x86_64` and arm64.
//!
//! Sections `.text .rdata .data`, their relocations, the unwind tables
//! `.pdata` / `.xdata` (every function is a frame-pointer frame: the
//! unwinder takes the stack pointer back from it), symbols and the
//! string table. A weak definition is a weak external aliasing a local
//! default, as LLVM writes one. No debug info (`-g` builds for Windows go
//! through LLVM, whose `CodeView` lld-link turns into a PDB).

use crate::obj::{FnRange, Obj, RelKind, SECTS, Sect};

const MACHINE_AMD64: u16 = 0x8664;
const MACHINE_ARM64: u16 = 0xaa64;
const SCN_CNT_CODE: u32 = 0x20;
const SCN_CNT_INITIALIZED_DATA: u32 = 0x40;
const SCN_MEM_EXECUTE: u32 = 0x2000_0000;
const SCN_MEM_READ: u32 = 0x4000_0000;
const SCN_MEM_WRITE: u32 = 0x8000_0000;
const SCN_LNK_NRELOC_OVFL: u32 = 0x0100_0000;
const SYM_CLASS_EXTERNAL: u8 = 2;
const SYM_CLASS_STATIC: u8 = 3;
const SYM_CLASS_WEAK_EXTERNAL: u8 = 105;
const SYM_DTYPE_FUNCTION: u16 = 0x20;
const WEAK_EXTERN_SEARCH_ALIAS: u32 = 3;

const REL_AMD64_ADDR64: u16 = 1;
const REL_AMD64_ADDR32NB: u16 = 3;
const REL_AMD64_REL32: u16 = 4;
const REL_AMD64_SECREL: u16 = 0xb;
const REL_ARM64_ADDR32NB: u16 = 2;
const REL_ARM64_BRANCH26: u16 = 3;
const REL_ARM64_PAGEBASE_REL21: u16 = 4;
const REL_ARM64_PAGEOFFSET_12A: u16 = 6;
const REL_ARM64_PAGEOFFSET_12L: u16 = 7;
const REL_ARM64_SECREL_LOW12A: u16 = 9;
const REL_ARM64_SECREL_HIGH12A: u16 = 0xa;
const REL_ARM64_ADDR64: u16 = 0xe;

/// x64 `UNWIND_INFO` of every function: version 1, a 4-byte prolog,
/// `rbp` the frame register at offset 0; the codes in reverse order:
/// `mov rbp, rsp` at 4 (`UWOP_SET_FPREG`), `push rbp` at 1
/// (`UWOP_PUSH_NONVOL`). What `x64::prologue` emits.
const X64_UNWIND: [u8; 8] = [0x01, 0x04, 0x02, 0x05, 0x04, 0x03, 0x01, 0x50];

/// arm64 unwind codes of every prolog and epilog (shared, index 0):
/// `set_fp` (`mov x29, sp`), `save_fplr_x` 16 (`stp x29, x30, [sp,
/// #-16]!`), `end`, a `nop` pad. What `a64::prologue` / `epilogue` emit.
const A64_CODES: [u8; 4] = [0xe1, 0x81, 0xe4, 0xe3];
/// The first two instructions of `a64::epilogue`.
const A64_EPILOG: [u32; 2] = [0x9100_03bf, 0xa8c1_7bfd];

/// `(offset, type, symbol table index)`.
type Rel = (u32, u16, u32);

struct Out {
    name: &'static str,
    flags: u32,
    data: Vec<u8>,
    /// log2 of the alignment.
    align: u32,
    relocs: Vec<Rel>,
}

fn put16(b: &mut Vec<u8>, v: u16) {
    b.extend_from_slice(&v.to_le_bytes());
}

fn put32(b: &mut Vec<u8>, v: u32) {
    b.extend_from_slice(&v.to_le_bytes());
}

/// Symbol table records and the string table of the longer names.
#[derive(Default)]
struct SymTab {
    recs: Vec<u8>,
    strs: Vec<u8>,
}

impl SymTab {
    /// A record, its name inline or in the string table; `aux`
    /// auxiliary records follow.
    fn add(&mut self, name: &str, value: u32, sect: i16, ty: u16, class: u8, aux: u8) {
        let b = &mut self.recs;
        if name.len() <= 8 {
            let mut n = [0u8; 8];
            n[..name.len()].copy_from_slice(name.as_bytes());
            b.extend_from_slice(&n);
        } else {
            put32(b, 0);
            put32(b, self.strs.len() as u32 + 4);
            self.strs.extend_from_slice(name.as_bytes());
            self.strs.push(0);
        }
        put32(b, value);
        b.extend_from_slice(&sect.to_le_bytes());
        put16(b, ty);
        b.push(class);
        b.push(aux);
    }

    fn len(&self) -> u32 {
        (self.recs.len() / 18) as u32
    }
}

/// Serialize `obj`.
#[must_use]
pub fn write(obj: &Obj) -> Vec<u8> {
    let x86 = obj.x86;
    // Symbol table indexes: a weak definition takes three records (its
    // local default, the weak external and its auxiliary record), the
    // others one; `.xdata`'s label comes last.
    let mut index = Vec::with_capacity(obj.syms.len());
    let mut n = 0u32;
    for s in &obj.syms {
        let weak = s.weak && s.def.is_some();
        index.push(if weak { n + 1 } else { n });
        n += if weak { 3 } else { 1 };
    }
    let xdata_sym = n;

    let mut outs: Vec<Out> = Vec::new();
    let mut sect_index = std::collections::HashMap::new();
    for s in SECTS {
        let sec = &obj.sects[&s];
        if sec.data.is_empty() {
            continue;
        }
        let (name, flags) = match s {
            Sect::Text => (".text", SCN_CNT_CODE | SCN_MEM_EXECUTE | SCN_MEM_READ),
            Sect::Const | Sect::DataConst => (".rdata", SCN_CNT_INITIALIZED_DATA | SCN_MEM_READ),
            Sect::Data => (
                ".data",
                SCN_CNT_INITIALIZED_DATA | SCN_MEM_READ | SCN_MEM_WRITE,
            ),
        };
        let relocs = sec
            .relocs
            .iter()
            .map(|r| {
                let ty = if x86 {
                    match r.kind {
                        RelKind::X86Call | RelKind::X86Pc32 => REL_AMD64_REL32,
                        RelKind::X86SecRel => REL_AMD64_SECREL,
                        RelKind::Abs64 => REL_AMD64_ADDR64,
                        k => unreachable!("{k:?} in a COFF object"),
                    }
                } else {
                    match r.kind {
                        RelKind::Branch26 => REL_ARM64_BRANCH26,
                        RelKind::Page21 => REL_ARM64_PAGEBASE_REL21,
                        // A load / store scales the offset; an `add` not.
                        RelKind::PageOff12 => {
                            let at = r.off as usize;
                            let ins = u32::from_le_bytes(
                                sec.data[at..at + 4].try_into().unwrap_or([0; 4]),
                            );
                            if ins & 0x3b00_0000 == 0x3900_0000 {
                                REL_ARM64_PAGEOFFSET_12L
                            } else {
                                REL_ARM64_PAGEOFFSET_12A
                            }
                        }
                        RelKind::SecRelHi12 => REL_ARM64_SECREL_HIGH12A,
                        RelKind::SecRelLo12 => REL_ARM64_SECREL_LOW12A,
                        RelKind::Abs64 => REL_ARM64_ADDR64,
                        k => unreachable!("{k:?} in a COFF object"),
                    }
                };
                (r.off, ty, index[r.sym as usize])
            })
            .collect();
        sect_index.insert(s, outs.len() as i16 + 1);
        outs.push(Out {
            name,
            flags,
            data: sec.data.clone(),
            align: sec.align.max(if s == Sect::Text { 4 } else { 0 }),
            relocs,
        });
    }
    let xdata_sect = outs.len() as i16 + 1;
    if !obj.fns.is_empty() {
        let (xdata, pdata) = if x86 {
            x64_unwind(&obj.fns, &index, xdata_sym)
        } else {
            a64_unwind(obj, &index, xdata_sym)
        };
        for (name, (data, relocs)) in [(".xdata", xdata), (".pdata", pdata)] {
            outs.push(Out {
                name,
                flags: SCN_CNT_INITIALIZED_DATA | SCN_MEM_READ,
                data,
                align: 2,
                relocs,
            });
        }
    }

    // Symbols.
    let mut syms = SymTab::default();
    for s in &obj.syms {
        let (sect, value, ty) = match s.def {
            Some((sec, off, _)) => (
                sect_index.get(&sec).copied().unwrap_or(0),
                off,
                if sec == Sect::Text {
                    SYM_DTYPE_FUNCTION
                } else {
                    0
                },
            ),
            None => (0, 0, 0),
        };
        if s.weak && s.def.is_some() {
            let default = syms.len();
            let local = format!(".weak.{}.default", s.name);
            syms.add(&local, value, sect, ty, SYM_CLASS_STATIC, 0);
            syms.add(&s.name, 0, 0, ty, SYM_CLASS_WEAK_EXTERNAL, 1);
            put32(&mut syms.recs, default);
            put32(&mut syms.recs, WEAK_EXTERN_SEARCH_ALIAS);
            syms.recs.extend_from_slice(&[0; 10]);
            continue;
        }
        let class = if s.def.is_some() && !s.global {
            SYM_CLASS_STATIC
        } else {
            SYM_CLASS_EXTERNAL
        };
        syms.add(&s.name, value, sect, ty, class, 0);
    }
    syms.add("$xdata", 0, xdata_sect, 0, SYM_CLASS_STATIC, 0);

    // Layout: header, section headers, each section's data and
    // relocations, symbols, strings.
    let mut b = Vec::new();
    put16(&mut b, if x86 { MACHINE_AMD64 } else { MACHINE_ARM64 });
    put16(&mut b, outs.len() as u16);
    put32(&mut b, 0);
    let symoff_at = b.len();
    put32(&mut b, 0);
    put32(&mut b, syms.len());
    put16(&mut b, 0);
    put16(&mut b, 0);
    let headers = b.len();
    b.resize(headers + 40 * outs.len(), 0);
    for (k, o) in outs.iter().enumerate() {
        b.resize(b.len().next_multiple_of(1 << o.align.min(4)), 0);
        let data = b.len() as u32;
        b.extend_from_slice(&o.data);
        let rel = b.len() as u32;
        // More than 0xfffe: the count is in a first, extra record.
        let ovfl = o.relocs.len() > 0xfffe;
        if ovfl {
            put32(&mut b, o.relocs.len() as u32 + 1);
            put32(&mut b, 0);
            put16(&mut b, 0);
        }
        for &(off, ty, sym) in &o.relocs {
            put32(&mut b, off);
            put32(&mut b, sym);
            put16(&mut b, ty);
        }
        let mut h = Vec::with_capacity(40);
        let mut name = [0u8; 8];
        name[..o.name.len()].copy_from_slice(o.name.as_bytes());
        h.extend_from_slice(&name);
        put32(&mut h, 0);
        put32(&mut h, 0);
        put32(&mut h, o.data.len() as u32);
        put32(&mut h, data);
        put32(&mut h, if o.relocs.is_empty() { 0 } else { rel });
        put32(&mut h, 0);
        put16(&mut h, if ovfl { 0xffff } else { o.relocs.len() as u16 });
        put16(&mut h, 0);
        // `IMAGE_SCN_ALIGN_<n>BYTES`: log2 + 1 in bits 20..24.
        let ovfl_flag = if ovfl { SCN_LNK_NRELOC_OVFL } else { 0 };
        put32(&mut h, o.flags | ovfl_flag | ((o.align.min(13) + 1) << 20));
        b[headers + 40 * k..headers + 40 * (k + 1)].copy_from_slice(&h);
    }
    let symoff = b.len() as u32;
    b[symoff_at..symoff_at + 4].copy_from_slice(&symoff.to_le_bytes());
    b.extend_from_slice(&syms.recs);
    put32(&mut b, syms.strs.len() as u32 + 4);
    b.extend_from_slice(&syms.strs);
    b
}

/// Section contents and relocations of `.xdata` and `.pdata`.
type Unwind = ((Vec<u8>, Vec<Rel>), (Vec<u8>, Vec<Rel>));

/// x64: one shared `UNWIND_INFO`; a `RUNTIME_FUNCTION` (begin, end,
/// unwind info) per function.
fn x64_unwind(fns: &[FnRange], index: &[u32], xdata: u32) -> Unwind {
    let mut pdata = Vec::new();
    let mut relocs = Vec::new();
    for f in fns {
        let at = pdata.len() as u32;
        let s = index[f.sym as usize];
        relocs.push((at, REL_AMD64_ADDR32NB, s));
        relocs.push((at + 4, REL_AMD64_ADDR32NB, s));
        relocs.push((at + 8, REL_AMD64_ADDR32NB, xdata));
        put32(&mut pdata, 0);
        put32(&mut pdata, f.len);
        put32(&mut pdata, 0);
    }
    ((X64_UNWIND.to_vec(), Vec::new()), (pdata, relocs))
}

/// arm64: per function an `.xdata` record (its length, one epilog scope
/// per epilog, the shared codes) and a `.pdata` entry (begin, record).
fn a64_unwind(obj: &Obj, index: &[u32], xdata_sym: u32) -> Unwind {
    let text = &obj.sects[&Sect::Text].data;
    let word = |at: usize| u32::from_le_bytes(text[at..at + 4].try_into().unwrap_or([0; 4]));
    let (mut xdata, mut pdata, mut relocs) = (Vec::new(), Vec::new(), Vec::new());
    for f in &obj.fns {
        let epilogs: Vec<u32> = (0..f.len.saturating_sub(4))
            .step_by(4)
            .filter(|&o| {
                let at = (f.start + o) as usize;
                [word(at), word(at + 4)] == A64_EPILOG
            })
            .collect();
        let at = xdata.len() as u32;
        // Function length in words (18 bits), one code word; more than
        // 31 epilogs need the extended header.
        let len = (f.len / 4) & 0x3_ffff;
        let n = epilogs.len() as u32;
        if n <= 31 {
            put32(&mut xdata, len | (n << 22) | (1 << 27));
        } else {
            put32(&mut xdata, len);
            put32(&mut xdata, n | (1 << 16));
        }
        for e in epilogs {
            put32(&mut xdata, e / 4);
        }
        xdata.extend_from_slice(&A64_CODES);
        let p = pdata.len() as u32;
        relocs.push((p, REL_ARM64_ADDR32NB, index[f.sym as usize]));
        relocs.push((p + 4, REL_ARM64_ADDR32NB, xdata_sym));
        put32(&mut pdata, 0);
        put32(&mut pdata, at);
    }
    ((xdata, Vec::new()), (pdata, relocs))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A function calling an undefined one, a string constant, a weak
    /// definition: section, symbol and relocation records as
    /// `llvm-readobj` reads them (checked by hand once).
    #[test]
    fn x64_object_layout() {
        let mut o = Obj::new(true, false, true);
        let f = o.sym("f");
        let g = o.sym("g");
        let w = o.sym("w");
        o.sect(Sect::Text)
            .data
            .extend_from_slice(&[0x55, 0x48, 0x89, 0xe5, 0xe8, 0, 0, 0, 0, 0x5d, 0xc3]);
        o.sect(Sect::Text).relocs.push(crate::obj::Reloc {
            off: 5,
            kind: RelKind::X86Call,
            sym: g,
        });
        o.syms[f as usize].def = Some((Sect::Text, 0, 11));
        o.syms[w as usize].def = Some((Sect::Text, 0, 11));
        o.syms[w as usize].weak = true;
        o.fns.push(FnRange {
            sym: f,
            start: 0,
            len: 11,
            lines: Vec::new(),
            debug: None,
        });
        let b = write(&o);
        assert_eq!(u16::from_le_bytes([b[0], b[1]]), MACHINE_AMD64);
        // .text, .xdata, .pdata.
        assert_eq!(u16::from_le_bytes([b[2], b[3]]), 3);
        let symoff = u32::from_le_bytes(b[8..12].try_into().unwrap()) as usize;
        // f, g, the weak default + external + aux, `$xdata`.
        assert_eq!(u32::from_le_bytes(b[12..16].try_into().unwrap()), 6);
        let sym = |i: usize| &b[symoff + 18 * i..symoff + 18 * (i + 1)];
        assert_eq!(&sym(0)[..8], b"f\0\0\0\0\0\0\0");
        assert_eq!(sym(0)[16], SYM_CLASS_EXTERNAL);
        assert_eq!(i16::from_le_bytes([sym(1)[12], sym(1)[13]]), 0);
        assert_eq!(sym(3)[16], SYM_CLASS_WEAK_EXTERNAL);
        // The weak external's tag: the default, record 2.
        assert_eq!(u32::from_le_bytes(sym(4)[..4].try_into().unwrap()), 2);
        // The call's REL32 against g (record 1).
        let text = 20;
        let rel = u32::from_le_bytes(b[text + 24..text + 28].try_into().unwrap()) as usize;
        assert_eq!(&b[rel..rel + 10], &[5, 0, 0, 0, 1, 0, 0, 0, 4, 0]);
    }
}

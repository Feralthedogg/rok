//! ELF64 relocatable object (`ET_REL`) writer, `x86_64` and arm64.
//!
//! Sections `.text .rodata .data.rel.ro .data`, their `.rela.*`, an
//! `.eh_frame` with one FDE per function (a frame-pointer frame) so
//! unwinders and debuggers walk through it, the debug sections when
//! present, a non-executable stack note; symbols local first.

use crate::obj::{FnRange, Obj, RelKind, SECTS, Sect};

const SHT_PROGBITS: u32 = 1;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHF_WRITE: u64 = 1;
const SHF_ALLOC: u64 = 2;
const SHF_EXECINSTR: u64 = 4;
const SHF_INFO_LINK: u64 = 0x40;
const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;
const STT_NOTYPE: u8 = 0;
const STT_OBJECT: u8 = 1;
const STT_FUNC: u8 = 2;
const STT_SECTION: u8 = 3;
const EM_X86_64: u16 = 62;
const EM_AARCH64: u16 = 183;

const R_X86_64_64: u32 = 1;
const R_X86_64_PC32: u32 = 2;
const R_X86_64_PLT32: u32 = 4;
const R_X86_64_32: u32 = 10;
const R_X86_64_GOTTPOFF: u32 = 22;
const R_X86_64_REX_GOTPCRELX: u32 = 42;
const R_AARCH64_ABS64: u32 = 257;
const R_AARCH64_ABS32: u32 = 258;
const R_AARCH64_PREL32: u32 = 261;
const R_AARCH64_ADR_PREL_PG_HI21: u32 = 275;
const R_AARCH64_ADD_ABS_LO12_NC: u32 = 277;
const R_AARCH64_CALL26: u32 = 283;
const R_AARCH64_ADR_GOT_PAGE: u32 = 311;
const R_AARCH64_LD64_GOT_LO12_NC: u32 = 312;
const R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21: u32 = 541;
const R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC: u32 = 542;

/// `(offset, type, symbol table index, addend)`.
type Rela = (u64, u32, usize, i64);

struct Out {
    name: String,
    ty: u32,
    flags: u64,
    data: Vec<u8>,
    align: u64,
    link: u32,
    info: u32,
    entsize: u64,
}

fn put16(b: &mut Vec<u8>, v: u16) {
    b.extend_from_slice(&v.to_le_bytes());
}

fn put32(b: &mut Vec<u8>, v: u32) {
    b.extend_from_slice(&v.to_le_bytes());
}

fn put64(b: &mut Vec<u8>, v: u64) {
    b.extend_from_slice(&v.to_le_bytes());
}

/// `.eh_frame`: a CIE and one FDE per function; the relocations of the
/// FDEs' `pc_begin` (`(offset, symbol)`).
fn eh_frame(fns: &[FnRange], x86: bool) -> (Vec<u8>, Vec<(u32, u32)>) {
    let mut b = Vec::new();
    let mut relocs = Vec::new();
    // CIE: "zR", code align 1, data align -8, pc-relative sdata4 FDEs.
    let (ra, init): (u8, &[u8]) = if x86 {
        // CFA = rsp + 8, return address at CFA - 8.
        (16, &[0x0c, 7, 8, 0x90, 1])
    } else {
        // CFA = sp + 0.
        (30, &[0x0c, 31, 0])
    };
    let mut cie = vec![0, 0, 0, 0, 1, b'z', b'R', 0, 1, 0x78, ra, 1, 0x1b];
    cie.extend_from_slice(init);
    while (cie.len() + 4) % 8 != 0 {
        cie.push(0); // DW_CFA_nop
    }
    put32(&mut b, cie.len() as u32);
    b.extend_from_slice(&cie);
    for f in fns {
        let start = b.len();
        let mut fde = Vec::new();
        put32(&mut fde, start as u32 + 4); // CIE pointer: back to offset 0
        relocs.push(((start + 8) as u32, f.sym));
        put32(&mut fde, 0); // pc_begin
        put32(&mut fde, f.len);
        fde.push(0); // augmentation data
        if x86 {
            // push rbp; mov rbp, rsp
            fde.extend_from_slice(&[0x41, 0x0e, 16, 0x86, 2, 0x43, 0x0d, 6]);
        } else {
            // stp x29, x30, [sp, #-16]!; mov x29, sp
            fde.extend_from_slice(&[0x44, 0x0e, 16, 0x9e, 1, 0x9d, 2, 0x44, 0x0d, 29]);
        }
        while (fde.len() + 4) % 8 != 0 {
            fde.push(0);
        }
        put32(&mut b, fde.len() as u32);
        b.extend_from_slice(&fde);
    }
    put32(&mut b, 0); // terminator
    (b, relocs)
}

/// Serialize `obj`.
#[must_use]
pub fn write(obj: &Obj) -> Vec<u8> {
    let x86 = obj.x86;
    let mut outs: Vec<Out> = vec![Out {
        name: String::new(),
        ty: 0,
        flags: 0,
        data: Vec::new(),
        align: 0,
        link: 0,
        info: 0,
        entsize: 0,
    }];
    // Symbols: null, the section symbols (code and data, then the extra
    // sections), locals, then globals.
    let nsect_syms = SECTS
        .iter()
        .filter(|s| !obj.sects[s].data.is_empty())
        .count()
        + obj.extra.len();
    let mut order: Vec<usize> = (0..obj.syms.len()).collect();
    let local = |i: usize| obj.syms[i].def.is_some() && !obj.syms[i].global;
    order.sort_by_key(|&i| (!local(i), i));
    let mut index = vec![0usize; obj.syms.len()];
    for (k, &i) in order.iter().enumerate() {
        index[i] = 1 + nsect_syms + k;
    }
    // The section index of each section symbol.
    let mut sect_syms: Vec<usize> = Vec::new();
    // The relocations of each section by its index.
    let mut relas: Vec<(usize, Vec<Rela>)> = Vec::new();
    let mut sect_index = std::collections::HashMap::new();
    for s in SECTS {
        let sec = &obj.sects[&s];
        if sec.data.is_empty() {
            continue;
        }
        let (name, flags) = match s {
            Sect::Text => (".text", SHF_ALLOC | SHF_EXECINSTR),
            Sect::Const => (".rodata", SHF_ALLOC),
            Sect::DataConst => (".data.rel.ro", SHF_ALLOC | SHF_WRITE),
            Sect::Data => (".data", SHF_ALLOC | SHF_WRITE),
        };
        sect_index.insert(s, outs.len());
        sect_syms.push(outs.len());
        let rs = sec
            .relocs
            .iter()
            .map(|r| {
                let (ty, addend) = reloc(r.kind, x86);
                (u64::from(r.off), ty, index[r.sym as usize], addend)
            })
            .collect();
        relas.push((outs.len(), rs));
        outs.push(Out {
            name: name.to_owned(),
            ty: SHT_PROGBITS,
            flags,
            data: sec.data.clone(),
            align: 1 << sec.align.max(if s == Sect::Text { 4 } else { 0 }),
            link: 0,
            info: 0,
            entsize: 0,
        });
    }
    // Unwind tables.
    if !obj.fns.is_empty() {
        let (data, rs) = eh_frame(&obj.fns, x86);
        let ty = if x86 { R_X86_64_PC32 } else { R_AARCH64_PREL32 };
        relas.push((
            outs.len(),
            rs.into_iter()
                .map(|(off, s)| (u64::from(off), ty, index[s as usize], 0))
                .collect(),
        ));
        outs.push(Out {
            name: ".eh_frame".to_owned(),
            ty: SHT_PROGBITS,
            flags: SHF_ALLOC,
            data,
            align: 8,
            link: 0,
            info: 0,
            entsize: 0,
        });
    }
    // Debug sections: the Mach-O contents (the target's object address,
    // an offset into a debug section) become explicit addends.
    let extra_sym = 1 + sect_syms.len();
    for (_, name, _, sec) in &obj.extra {
        let mut data = sec.data.clone();
        let mut rs = Vec::new();
        for r in &sec.relocs {
            let at = r.off as usize;
            if r.kind == RelKind::SecOff32 {
                let v = u32::from_le_bytes(data[at..at + 4].try_into().unwrap_or([0; 4]));
                data[at..at + 4].fill(0);
                let ty = if x86 { R_X86_64_32 } else { R_AARCH64_ABS32 };
                rs.push((
                    u64::from(r.off),
                    ty,
                    extra_sym + r.sym as usize,
                    i64::from(v),
                ));
                continue;
            }
            let v = u64::from_le_bytes(data[at..at + 8].try_into().unwrap_or([0; 8]));
            let base = obj.syms[r.sym as usize].def.map_or(0, |d| u64::from(d.1));
            data[at..at + 8].fill(0);
            let ty = if x86 { R_X86_64_64 } else { R_AARCH64_ABS64 };
            rs.push((
                u64::from(r.off),
                ty,
                index[r.sym as usize],
                (v - base) as i64,
            ));
        }
        sect_syms.push(outs.len());
        relas.push((outs.len(), rs));
        outs.push(Out {
            name: format!(".{}", name.trim_start_matches('_')),
            ty: SHT_PROGBITS,
            flags: 0,
            data,
            align: 1,
            link: 0,
            info: 0,
            entsize: 0,
        });
    }
    outs.push(Out {
        name: ".note.GNU-stack".to_owned(),
        ty: SHT_PROGBITS,
        flags: 0,
        data: Vec::new(),
        align: 1,
        link: 0,
        info: 0,
        entsize: 0,
    });

    let mut strtab = vec![0u8];
    let mut symtab = vec![0u8; 24];
    for shndx in &sect_syms {
        put32(&mut symtab, 0);
        symtab.push(STT_SECTION);
        symtab.push(0);
        put16(&mut symtab, *shndx as u16);
        put64(&mut symtab, 0);
        put64(&mut symtab, 0);
    }
    let first_global = 1 + nsect_syms + order.iter().filter(|&&i| local(i)).count();
    for &i in &order {
        let s = &obj.syms[i];
        let name = strtab.len() as u32;
        strtab.extend_from_slice(s.name.as_bytes());
        strtab.push(0);
        let (shndx, value, size, ty) = match s.def {
            Some((sec, off, size)) => (
                sect_index.get(&sec).copied().unwrap_or(0) as u16,
                u64::from(off),
                u64::from(size),
                if sec == Sect::Text {
                    STT_FUNC
                } else {
                    STT_OBJECT
                },
            ),
            None => (0, 0, 0, STT_NOTYPE),
        };
        let bind = if local(i) {
            STB_LOCAL
        } else if s.weak {
            STB_WEAK
        } else {
            STB_GLOBAL
        };
        put32(&mut symtab, name);
        symtab.push((bind << 4) | ty);
        symtab.push(0);
        put16(&mut symtab, shndx);
        put64(&mut symtab, value);
        put64(&mut symtab, size);
    }
    let symtab_index = outs.len() + relas.iter().filter(|r| !r.1.is_empty()).count();
    for (target, rs) in &relas {
        if rs.is_empty() {
            continue;
        }
        let mut data = Vec::new();
        for &(off, ty, sym, addend) in rs {
            put64(&mut data, off);
            put64(&mut data, ((sym as u64) << 32) | u64::from(ty));
            put64(&mut data, addend as u64);
        }
        outs.push(Out {
            name: format!(".rela{}", outs[*target].name),
            ty: SHT_RELA,
            flags: SHF_INFO_LINK,
            data,
            align: 8,
            link: symtab_index as u32,
            info: *target as u32,
            entsize: 24,
        });
    }
    let strtab_index = symtab_index + 1;
    outs.push(Out {
        name: ".symtab".to_owned(),
        ty: SHT_SYMTAB,
        flags: 0,
        data: symtab,
        align: 8,
        link: strtab_index as u32,
        info: first_global as u32,
        entsize: 24,
    });
    outs.push(Out {
        name: ".strtab".to_owned(),
        ty: SHT_STRTAB,
        flags: 0,
        data: strtab,
        align: 1,
        link: 0,
        info: 0,
        entsize: 0,
    });
    let mut shstrtab = vec![0u8];
    let mut names = Vec::new();
    for o in &outs {
        names.push(shstrtab.len() as u32);
        shstrtab.extend_from_slice(o.name.as_bytes());
        shstrtab.push(0);
    }
    names.push(shstrtab.len() as u32);
    shstrtab.extend_from_slice(b".shstrtab\0");
    outs.push(Out {
        name: ".shstrtab".to_owned(),
        ty: SHT_STRTAB,
        flags: 0,
        data: shstrtab,
        align: 1,
        link: 0,
        info: 0,
        entsize: 0,
    });

    // Layout: header, section contents, section headers.
    let mut b = vec![0u8; 64];
    let mut offs = Vec::new();
    for o in &outs {
        let a = o.align.max(1) as usize;
        b.resize(b.len().next_multiple_of(a), 0);
        offs.push(b.len() as u64);
        b.extend_from_slice(&o.data);
    }
    b.resize(b.len().next_multiple_of(8), 0);
    let shoff = b.len() as u64;
    for (k, o) in outs.iter().enumerate() {
        put32(&mut b, names[k]);
        put32(&mut b, o.ty);
        put64(&mut b, o.flags);
        put64(&mut b, 0);
        put64(&mut b, if k == 0 { 0 } else { offs[k] });
        put64(&mut b, o.data.len() as u64);
        put32(&mut b, o.link);
        put32(&mut b, o.info);
        put64(&mut b, o.align);
        put64(&mut b, o.entsize);
    }
    let mut h = Vec::new();
    h.extend_from_slice(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0]);
    h.resize(16, 0);
    put16(&mut h, 1); // ET_REL
    put16(&mut h, if x86 { EM_X86_64 } else { EM_AARCH64 });
    put32(&mut h, 1);
    put64(&mut h, 0);
    put64(&mut h, 0);
    put64(&mut h, shoff);
    put32(&mut h, 0);
    put16(&mut h, 64);
    put16(&mut h, 0);
    put16(&mut h, 0);
    put16(&mut h, 64);
    put16(&mut h, outs.len() as u16);
    put16(&mut h, (outs.len() - 1) as u16);
    b[..64].copy_from_slice(&h);
    b
}

/// ELF relocation type and addend of `kind`.
const fn reloc(kind: RelKind, x86: bool) -> (u32, i64) {
    if x86 {
        match kind {
            RelKind::X86Call => (R_X86_64_PLT32, -4),
            RelKind::X86GotLoad => (R_X86_64_REX_GOTPCRELX, -4),
            RelKind::X86Tls => (R_X86_64_GOTTPOFF, -4),
            RelKind::Abs64 => (R_X86_64_64, 0),
            _ => (R_X86_64_PC32, -4),
        }
    } else {
        match kind {
            RelKind::Branch26 => (R_AARCH64_CALL26, 0),
            RelKind::Page21 => (R_AARCH64_ADR_PREL_PG_HI21, 0),
            RelKind::PageOff12 => (R_AARCH64_ADD_ABS_LO12_NC, 0),
            RelKind::GotPage21 => (R_AARCH64_ADR_GOT_PAGE, 0),
            RelKind::GotPageOff12 => (R_AARCH64_LD64_GOT_LO12_NC, 0),
            RelKind::TlvPage21 => (R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21, 0),
            RelKind::TlvPageOff12 => (R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC, 0),
            _ => (R_AARCH64_ABS64, 0),
        }
    }
}

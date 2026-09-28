//! ELF64 relocatable object (`ET_REL`) writer, `x86_64` and arm64.
//!
//! A section per function and data object (`.text.<sym>`, `.rodata.`,
//! `.data.rel.ro.`, `.data.`, `.bss.`), so `--gc-sections` drops what
//! nothing uses; their `.rela.*`, an `.eh_frame` with one FDE per
//! function (a frame-pointer frame) so unwinders and debuggers walk
//! through it, the debug sections when present, a non-executable stack
//! note; symbols local first.

use crate::obj::{FnRange, Obj, RelKind, Sect};

const SHT_PROGBITS: u32 = 1;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHT_SYMTAB_SHNDX: u32 = 18;
const SHN_LORESERVE: usize = 0xff00;
const SHN_XINDEX: u16 = 0xffff;
const SHF_WRITE: u64 = 1;
const SHF_ALLOC: u64 = 2;
const SHF_EXECINSTR: u64 = 4;
const SHF_INFO_LINK: u64 = 0x40;
const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;
const STV_HIDDEN: u8 = 2;
const STT_NOTYPE: u8 = 0;
const STT_OBJECT: u8 = 1;
const STT_FUNC: u8 = 2;
const STT_SECTION: u8 = 3;
const STT_TLS: u8 = 6;
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
/// FDEs' `pc_begin` (`(offset, function index)`).
fn eh_frame(fns: &[FnRange], x86: bool) -> (Vec<u8>, Vec<(u32, usize)>) {
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
    for (i, f) in fns.iter().enumerate() {
        let start = b.len();
        let mut fde = Vec::new();
        put32(&mut fde, start as u32 + 4); // CIE pointer: back to offset 0
        relocs.push(((start + 8) as u32, i));
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
    let (pieces, piece_of) = obj.pieces();
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
    // Symbols: null, the section symbols (the pieces, then the extra
    // sections), locals, then globals. Unwind and debug info refer to
    // code by its section symbol, so they go with a dropped section.
    let nsect_syms = pieces.len() + obj.extra.len();
    let mut order: Vec<usize> = (0..obj.syms.len()).collect();
    let local = |i: usize| obj.syms[i].def.is_some() && !obj.syms[i].global;
    order.sort_by_key(|&i| (!local(i), i));
    let mut index = vec![0usize; obj.syms.len()];
    for (k, &i) in order.iter().enumerate() {
        index[i] = 1 + nsect_syms + k;
    }
    // A thread-local (the runtime's, undefined here) is STT_TLS: GNU ld
    // rejects a TLS definition for a reference of another type.
    let mut tls = vec![false; obj.syms.len()];
    for r in pieces.iter().flat_map(|p| &p.relocs) {
        if matches!(
            r.kind,
            RelKind::X86Tls | RelKind::TlvPage21 | RelKind::TlvPageOff12
        ) {
            tls[r.sym as usize] = true;
        }
    }
    // The section symbol of `sym`'s piece and the object address `at`
    // as an offset in it.
    let in_piece = |sym: u32, at: u64| match piece_of.get(sym as usize).copied().flatten() {
        Some(k) => (1 + k, at - u64::from(pieces[k].start)),
        None => (index[sym as usize], at),
    };
    // The section index of each section symbol.
    let mut sect_syms: Vec<usize> = Vec::new();
    // The relocations of each section by its index.
    let mut relas: Vec<(usize, Vec<Rela>)> = Vec::new();
    for p in &pieces {
        let data = &obj.sects[&p.sect].data[p.start as usize..p.end as usize];
        let bss = p.sect == Sect::Data && p.relocs.is_empty() && data.iter().all(|&b| b == 0);
        let (prefix, flags) = match p.sect {
            Sect::Text => (".text", SHF_ALLOC | SHF_EXECINSTR),
            Sect::Const => (".rodata", SHF_ALLOC),
            Sect::DataConst => (".data.rel.ro", SHF_ALLOC | SHF_WRITE),
            Sect::Data if bss => (".bss", SHF_ALLOC | SHF_WRITE),
            Sect::Data => (".data", SHF_ALLOC | SHF_WRITE),
        };
        sect_syms.push(outs.len());
        let rs = p
            .relocs
            .iter()
            .map(|r| {
                let (ty, addend) = reloc(r.kind, x86);
                (u64::from(r.off), ty, index[r.sym as usize], addend)
            })
            .collect();
        relas.push((outs.len(), rs));
        outs.push(Out {
            name: format!("{prefix}.{}", obj.syms[p.syms[0] as usize].name),
            ty: if bss { SHT_NOBITS } else { SHT_PROGBITS },
            flags,
            data: data.to_vec(),
            align: 1 << p.align,
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
                .map(|(off, f)| {
                    let f = &obj.fns[f];
                    let (s, at) = in_piece(f.sym, u64::from(f.start));
                    (u64::from(off), ty, s, at as i64)
                })
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
    let extra_sym = 1 + pieces.len();
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
            data[at..at + 8].fill(0);
            let ty = if x86 { R_X86_64_64 } else { R_AARCH64_ABS64 };
            let (s, addend) = in_piece(r.sym, v);
            rs.push((u64::from(r.off), ty, s, addend as i64));
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

    // Section indexes from `SHN_LORESERVE` on are in `.symtab_shndx`.
    let xindex = outs.len() > SHN_LORESERVE;
    let mut shndx_tab = Vec::new();
    if xindex {
        put32(&mut shndx_tab, 0);
    }
    let mut strtab = vec![0u8];
    let mut symtab = vec![0u8; 24];
    let mut entry =
        |symtab: &mut Vec<u8>, name: u32, info: u8, other, shndx: usize, value, size| {
            put32(symtab, name);
            symtab.push(info);
            symtab.push(other);
            put16(
                symtab,
                if shndx >= SHN_LORESERVE {
                    SHN_XINDEX
                } else {
                    shndx as u16
                },
            );
            put64(symtab, value);
            put64(symtab, size);
            if xindex {
                put32(&mut shndx_tab, shndx as u32);
            }
        };
    for shndx in &sect_syms {
        entry(&mut symtab, 0, STT_SECTION, 0, *shndx, 0, 0);
    }
    let first_global = 1 + nsect_syms + order.iter().filter(|&&i| local(i)).count();
    for &i in &order {
        let s = &obj.syms[i];
        let name = strtab.len() as u32;
        strtab.extend_from_slice(s.name.as_bytes());
        strtab.push(0);
        let (shndx, value, size, ty) = match (s.def, piece_of[i]) {
            (Some((sec, off, size)), Some(k)) => (
                sect_syms[k],
                u64::from(off - pieces[k].start),
                u64::from(size),
                if sec == Sect::Text {
                    STT_FUNC
                } else {
                    STT_OBJECT
                },
            ),
            _ => (0, 0, 0, if tls[i] { STT_TLS } else { STT_NOTYPE }),
        };
        let bind = if local(i) {
            STB_LOCAL
        } else if s.weak {
            STB_WEAK
        } else {
            STB_GLOBAL
        };
        let other = if s.hidden { STV_HIDDEN } else { 0 };
        entry(
            &mut symtab,
            name,
            (bind << 4) | ty,
            other,
            shndx,
            value,
            size,
        );
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
    let strtab_index = symtab_index + 1 + usize::from(xindex);
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
    if xindex {
        outs.push(Out {
            name: ".symtab_shndx".to_owned(),
            ty: SHT_SYMTAB_SHNDX,
            flags: 0,
            data: shndx_tab,
            align: 4,
            link: symtab_index as u32,
            info: 0,
            entsize: 4,
        });
    }
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
    // A count or index from `SHN_LORESERVE` on is in section 0's header.
    let (n, shstrndx) = (outs.len(), outs.len() - 1);
    if shstrndx >= SHN_LORESERVE {
        outs[0].link = shstrndx as u32;
    }

    // Layout: header, section contents, section headers.
    let mut b = vec![0u8; 64];
    let mut offs = Vec::new();
    for o in &outs {
        let a = o.align.max(1) as usize;
        b.resize(b.len().next_multiple_of(a), 0);
        offs.push(b.len() as u64);
        if o.ty != SHT_NOBITS {
            b.extend_from_slice(&o.data);
        }
    }
    b.resize(b.len().next_multiple_of(8), 0);
    let shoff = b.len() as u64;
    for (k, o) in outs.iter().enumerate() {
        put32(&mut b, names[k]);
        put32(&mut b, o.ty);
        put64(&mut b, o.flags);
        put64(&mut b, 0);
        put64(&mut b, if k == 0 { 0 } else { offs[k] });
        let size = if k == 0 && n >= SHN_LORESERVE {
            n
        } else {
            o.data.len()
        };
        put64(&mut b, size as u64);
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
    put16(&mut h, if n >= SHN_LORESERVE { 0 } else { n as u16 });
    put16(
        &mut h,
        if shstrndx >= SHN_LORESERVE {
            SHN_XINDEX
        } else {
            shstrndx as u16
        },
    );
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Past `SHN_LORESERVE` sections: the counts in section 0, the
    /// symbols' section indexes in `.symtab_shndx`.
    #[test]
    fn many_sections_use_extended_numbering() {
        let mut o = Obj::new(true, true, false);
        for i in 0..0xff00u32 {
            let s = o.sym(&format!("d{i}"));
            o.define_data(s, Sect::Const, &[1], 1, true);
        }
        let b = write(&o);
        if let Some(p) = std::env::var_os("ROK_DUMP_XINDEX") {
            std::fs::write(p, &b).unwrap();
        }
        let u16_at = |at: usize| u16::from_le_bytes([b[at], b[at + 1]]);
        let shoff = u64::from_le_bytes(b[40..48].try_into().unwrap()) as usize;
        assert_eq!((u16_at(60), u16_at(62)), (0, SHN_XINDEX));
        let n = u64::from_le_bytes(b[shoff + 32..shoff + 40].try_into().unwrap());
        let shstrndx = u32::from_le_bytes(b[shoff + 40..shoff + 44].try_into().unwrap());
        // The pieces, the stack note, symtab, its indexes, strtab, shstrtab.
        assert_eq!((n, shstrndx), (0xff00 + 6, 0xff00 + 5));
        let shndx = shoff + 64 * (0xff00 + 3);
        assert_eq!(
            u32::from_le_bytes(b[shndx + 4..shndx + 8].try_into().unwrap()),
            SHT_SYMTAB_SHNDX
        );
    }
}

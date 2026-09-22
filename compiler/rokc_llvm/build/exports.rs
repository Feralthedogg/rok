//! What rokc exports for MLIR plugins: the symbols of archive members
//! (COFF read here; ELF / Mach-O through `nm` in build.rs) and the module
//! definition file rokc.exe is linked with. Shared by build.rs and
//! `tests/exports.rs`.

/// The globals of an archive member: defined (weak / COMDAT ones apart),
/// which of those are data (COFF only), and undefined (weak undefined
/// ones load no member and are left out).
#[derive(Default)]
pub struct Member {
    pub defs: Vec<String>,
    pub weak: Vec<String>,
    pub data: Vec<String>,
    pub undefs: Vec<String>,
}

use std::collections::HashMap;

const IMAGE_SCN_LNK_COMDAT: u32 = 0x1000;
const IMAGE_COMDAT_SELECT_NODUPLICATES: u8 = 1;
const IMAGE_SYM_CLASS_EXTERNAL: u8 = 2;
const IMAGE_SYM_CLASS_STATIC: u8 = 3;
const IMAGE_SYM_DTYPE_FUNCTION: u16 = 2;
/// i386, ARMNT, AMD64, ARM64, ARM64EC, ARM64X.
const MACHINES: [u16; 6] = [0x14c, 0x1c4, 0x8664, 0xaa64, 0xa641, 0xa64e];
/// `ANON_OBJECT_HEADER_BIGOBJ`'s class id, D1BAA1C7-BAEE-4BA9-AF20-FAF66AA4DCB8.
const BIGOBJ_CLASS_ID: [u8; 16] = [
    0xc7, 0xa1, 0xba, 0xd1, 0xee, 0xba, 0xa9, 0x4b, 0xaf, 0x20, 0xfa, 0xf6, 0x6a, 0xa4, 0xdc, 0xb8,
];

/// The object members of a COFF archive (`.lib`), in order. Linker and
/// import members are skipped.
pub fn coff_members(lib: &[u8]) -> Vec<Member> {
    let mut v = Vec::new();
    let Some(mut rest) = lib.strip_prefix(b"!<arch>\n") else {
        return v;
    };
    while rest.len() >= 60 {
        let (hdr, body) = rest.split_at(60);
        let size: usize = std::str::from_utf8(&hdr[48..58])
            .ok()
            .and_then(|s| s.trim().parse().ok())
            .unwrap_or(usize::MAX);
        let Some(data) = body.get(..size) else { break };
        // `/`, `//`, `/<ECSYMBOLS>/`: not objects (`/<n>` names one).
        if hdr[0] != b'/' || hdr[1].is_ascii_digit() {
            v.extend(coff_object(data));
        }
        rest = body.get(size + (size & 1)..).unwrap_or_default();
    }
    v
}

/// The externals of one COFF object (plain or `/bigobj`).
pub fn coff_object(d: &[u8]) -> Option<Member> {
    let u16_at = |o: usize| Some(u16::from_le_bytes(d.get(o..o + 2)?.try_into().ok()?));
    let u32_at = |o: usize| Some(u32::from_le_bytes(d.get(o..o + 4)?.try_into().ok()?));
    // Section headers, symbol table, symbol count, symbol record size.
    let (sections, symtab, nsyms, symsize) = if u16_at(0)? == 0 && u16_at(2)? == 0xffff {
        // Otherwise a short import member.
        if u16_at(4)? < 2 || d.get(12..28)? != BIGOBJ_CLASS_ID {
            return None;
        }
        (56, u32_at(48)? as usize, u32_at(52)? as usize, 20)
    } else {
        if !MACHINES.contains(&u16_at(0)?) {
            return None;
        }
        let sections = 20 + usize::from(u16_at(16)?);
        (sections, u32_at(8)? as usize, u32_at(12)? as usize, 18)
    };
    let strtab = symtab + nsyms * symsize;
    let comdat = |s: usize| {
        u32_at(sections + (s - 1) * 40 + 36).is_some_and(|c| c & IMAGE_SCN_LNK_COMDAT != 0)
    };
    // A COMDAT section's selection, from the aux record of its section
    // symbol (the first symbol in it). /Gy puts every function in one:
    // only those of any other selection than "no duplicates" are weak.
    let mut selection: HashMap<i32, u8> = HashMap::new();
    let mut m = Member::default();
    let mut i = 0;
    while i < nsyms {
        let rec = d.get(symtab + i * symsize..symtab + (i + 1) * symsize)?;
        let (section, tail) = if symsize == 20 {
            (i32::from_le_bytes(rec[12..16].try_into().ok()?), &rec[16..])
        } else {
            let s = i16::from_le_bytes(rec[12..14].try_into().ok()?);
            (i32::from(s), &rec[14..])
        };
        let (ty, class, aux) = (u16::from_le_bytes([tail[0], tail[1]]), tail[2], tail[3]);
        if class == IMAGE_SYM_CLASS_STATIC && aux > 0 && section > 0 && comdat(section as usize) {
            let at = symtab + (i + 1) * symsize + 14;
            selection.entry(section).or_insert(*d.get(at)?);
        }
        i += 1 + usize::from(aux);
        // Weak externals (class 105) are aliases with a fallback, like
        // ELF's weak undefined symbols.
        if class != IMAGE_SYM_CLASS_EXTERNAL {
            continue;
        }
        let name = if rec[..4] == [0; 4] {
            let at = strtab + u32::from_le_bytes(rec[4..8].try_into().ok()?) as usize;
            let s = d.get(at..)?;
            &s[..s.iter().position(|&b| b == 0)?]
        } else {
            let n = &rec[..8];
            &n[..n.iter().position(|&b| b == 0).unwrap_or(8)]
        };
        let name = String::from_utf8_lossy(name).into_owned();
        let value = u32::from_le_bytes(rec[8..12].try_into().ok()?);
        match section {
            0 if value == 0 => m.undefs.push(name),
            // A common symbol.
            0 => {
                m.data.push(name.clone());
                m.defs.push(name);
            }
            s if s > 0
                && comdat(s as usize)
                && selection.get(&s) != Some(&IMAGE_COMDAT_SELECT_NODUPLICATES) =>
            {
                m.weak.push(name);
            }
            s if s > 0 => {
                if ty >> 4 != IMAGE_SYM_DTYPE_FUNCTION {
                    m.data.push(name.clone());
                }
                m.defs.push(name);
            }
            // Absolute and debug symbols.
            _ => {}
        }
    }
    Some(m)
}

/// The most exports a PE image holds (ordinals are 16-bit).
pub const MAX_EXPORTS: usize = 65535;

/// rokc.exe's module definition file for `syms` (name, is data), filtered
/// as `llvm/utils/extract_symbols.py` does for MSVC: no deleting destructors
/// (link.exe refuses to export them), nothing in an anonymous namespace,
/// x86's decoration of C names dropped. Data is exported `DATA`: the
/// import library then has only `__imp_<name>`, so a plugin reference that
/// would bind to a jump thunk fails its link rather than reading the
/// thunk.
pub fn def_file(syms: &[(String, bool)], x86: bool) -> Result<String, String> {
    let mut lines: Vec<String> = syms
        .iter()
        .filter_map(|(s, data)| {
            let name = if s.starts_with('?') {
                if s.starts_with("??_G") || s.starts_with("??_E") || anonymous(s) {
                    return None;
                }
                s.as_str()
            } else if x86 {
                // `_f`, `_f@8` (stdcall), `@f@8` (fastcall): `f`.
                s.strip_prefix(['_', '@'])
                    .map_or(s.as_str(), |t| t.split('@').next().unwrap_or(t))
            } else {
                s.as_str()
            };
            Some(if *data {
                format!("  {name} DATA")
            } else {
                format!("  {name}")
            })
        })
        .collect();
    lines.sort();
    lines.dedup();
    if lines.len() > MAX_EXPORTS {
        return Err(format!(
            "rokc.exe would export {} symbols, more than a PE image holds ({MAX_EXPORTS})",
            lines.len()
        ));
    }
    Ok(format!("EXPORTS\n{}\n", lines.join("\n")))
}

/// An MSVC name mentioning an anonymous namespace (`?A@`, `?A0x<hex>@`).
fn anonymous(s: &str) -> bool {
    s.match_indices("?A").any(|(i, _)| {
        let t = &s[i + 2..];
        t.starts_with('@')
            || t.strip_prefix("0x").is_some_and(|h| {
                let n = h.bytes().take_while(u8::is_ascii_hexdigit).count();
                n > 0 && h[n..].starts_with('@')
            })
    })
}

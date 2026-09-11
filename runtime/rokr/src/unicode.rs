//! Unicode `char` properties and case mapping (stdlib 2.15.2 / 2.15.4)
//! over the tables `gen_unicode.py` generates from the UCD.
//!
//! Text that is not UTF-8 (`str` can carry raw OS bytes) falls back to
//! ASCII-only trimming and case mapping.

use core::cmp::Ordering;
use core::ptr;

use crate::str::{RokStr, alloc_str, build, sub};
use crate::unicode_tables as t;

fn in_ranges(table: &[(u32, u32)], c: u32) -> bool {
    table
        .binary_search_by(|&(lo, hi)| {
            if hi < c {
                Ordering::Less
            } else if lo > c {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        })
        .is_ok()
}

fn lookup<V: Copy>(table: &[(u32, V)], c: u32) -> Option<V> {
    table
        .binary_search_by_key(&c, |&(k, _)| k)
        .ok()
        .map(|i| table[i].1)
}

/// Property bits of `c`: 1 Alphabetic, 2 Lowercase, 4 Uppercase,
/// 8 `White_Space`, 16 numeric (general category Nd / Nl / No).
#[unsafe(no_mangle)]
pub extern "C" fn rok_char_props(c: u32) -> u32 {
    let tables = [
        t::ALPHABETIC,
        t::LOWERCASE,
        t::UPPERCASE,
        t::WHITE_SPACE,
        t::NUMERIC,
    ];
    let mut bits = 0;
    for (i, table) in tables.into_iter().enumerate() {
        if in_ranges(table, c) {
            bits |= 1 << i;
        }
    }
    bits
}

/// Simple (one-char) case mapping; `c` itself when it has none.
#[unsafe(no_mangle)]
pub extern "C" fn rok_char_to_case(c: u32, upper: i32) -> u32 {
    let table = if upper != 0 { t::TO_UPPER } else { t::TO_LOWER };
    lookup(table, c).unwrap_or(c)
}

fn is_white_space(c: char) -> bool {
    in_ranges(t::WHITE_SPACE, c as u32)
}

/// Unicode 3.13 `Final_Sigma`: a cased letter before the `Σ` at byte
/// `i` and none after (case-ignorable chars skipped both ways).
fn final_sigma(s: &str, i: usize) -> bool {
    let cased = |c: char| in_ranges(t::CASED, c as u32);
    let ignorable = |c: char| in_ranges(t::CASE_IGNORABLE, c as u32);
    let before = s[..i].chars().rev().find(|&c| !ignorable(c));
    let after = s[i + 'Σ'.len_utf8()..].chars().find(|&c| !ignorable(c));
    before.is_some_and(cased) && !after.is_some_and(cased)
}

/// The full case mapping of `c` (at byte `i` of `s`), char by char.
fn map_full(s: &str, i: usize, c: char, upper: bool, f: &mut impl FnMut(char)) {
    if c.is_ascii() {
        f(if upper {
            c.to_ascii_uppercase()
        } else {
            c.to_ascii_lowercase()
        });
        return;
    }
    let full = if upper { t::FULL_UPPER } else { t::FULL_LOWER };
    if let Some(m) = lookup(full, c as u32) {
        for &x in m.iter().filter(|&&x| x != 0) {
            f(char::from_u32(x).unwrap_or(c));
        }
    } else if !upper && c == 'Σ' && final_sigma(s, i) {
        f('ς');
    } else {
        f(char::from_u32(rok_char_to_case(c as u32, i32::from(upper))).unwrap_or(c));
    }
}

/// `upper` != 0 → uppercase, else lowercase: full Unicode mappings
/// (`ß` → `SS`) plus `Final_Sigma`; no locale-specific rules.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_case(s: RokStr, upper: i32) -> RokStr {
    let upper = upper != 0;
    let Ok(text) = core::str::from_utf8(s.bytes()) else {
        let out = build(&[s.bytes()]);
        // SAFETY: `out` is a fresh GC string of `len` bytes.
        let b = unsafe { core::slice::from_raw_parts_mut(out.ptr.cast_mut(), out.len) };
        if upper {
            b.make_ascii_uppercase();
        } else {
            b.make_ascii_lowercase();
        }
        return out;
    };
    // Two passes: measure, then encode.
    let mut len = 0;
    for (i, c) in text.char_indices() {
        map_full(text, i, c, upper, &mut |m| len += m.len_utf8());
    }
    let p = alloc_str(len);
    let mut at = 0;
    for (i, c) in text.char_indices() {
        map_full(text, i, c, upper, &mut |m| {
            let mut buf = [0u8; 4];
            let e = m.encode_utf8(&mut buf);
            // SAFETY: the first pass measured exactly `len` bytes.
            unsafe { ptr::copy_nonoverlapping(e.as_ptr(), p.add(at), e.len()) };
            at += e.len();
        });
    }
    RokStr { ptr: p, len }
}

/// `which`: 0 = both ends, 1 = start, 2 = end. Unicode `White_Space`.
/// Shares `s`'s bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_trim(s: RokStr, which: i32) -> RokStr {
    let Ok(text) = core::str::from_utf8(s.bytes()) else {
        let mut b = s.bytes();
        while which != 2 && b.first().is_some_and(u8::is_ascii_whitespace) {
            b = &b[1..];
        }
        while which != 1 && b.last().is_some_and(u8::is_ascii_whitespace) {
            b = &b[..b.len() - 1];
        }
        return sub(&s, b);
    };
    let text = match which {
        1 => text.trim_start_matches(is_white_space),
        2 => text.trim_end_matches(is_white_space),
        _ => text.trim_matches(is_white_space),
    };
    sub(&s, text.as_bytes())
}

#[cfg(test)]
pub mod tests {
    use super::*;

    const fn s(b: &'static [u8]) -> RokStr {
        RokStr {
            ptr: b.as_ptr(),
            len: b.len(),
        }
    }

    #[test]
    fn props_and_case() {
        assert_eq!(rok_char_props('A' as u32), 1 | 4);
        assert_eq!(rok_char_props('한' as u32), 1);
        assert_eq!(rok_char_props('٣' as u32), 16);
        assert_eq!(rok_char_props(0x3000), 8);
        assert_eq!(rok_char_to_case('É' as u32, 0), 'é' as u32);
        assert_eq!(rok_char_to_case('ß' as u32, 1), 'ß' as u32);
        assert!(final_sigma("ΟΔΟΣ", 6));
        assert!(!final_sigma("Σ", 0));
    }

    // Allocates: run from `str::tests::string_ops` (single GC mutator).
    pub fn str_case_and_trim() {
        assert_eq!(rok_str_case(s("straße".as_bytes()), 1).bytes(), b"STRASSE");
        assert_eq!(
            rok_str_case(s("ΟΔΟΣ Σ".as_bytes()), 0).bytes(),
            "οδος σ".as_bytes()
        );
        assert_eq!(
            rok_str_trim(s("\u{3000} x\u{85}".as_bytes()), 0).bytes(),
            b"x"
        );
        assert_eq!(rok_str_trim(s(b"\xff "), 2).bytes(), b"\xff");
    }
}

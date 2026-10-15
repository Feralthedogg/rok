//! Hand-off copies (stdlib 2.13.9): `rok::core::marker::transfer` copies
//! every collection a handed value reaches, once each. The memo maps an
//! original to its copy so a collection reached twice is copied once and
//! a cycle ends.
//!
//! A key is an object word and three plain words (a view's range; zero
//! for a collection's own object). The object word may point into an
//! object or outside the heap (a `str`'s bytes): it is only compared and
//! hashed, never read through.
//!
//! A table is `[current, len, cap, (key0, key1, key2, key3, copy)..]`, a
//! word-traced object ([`SCAN_WORDS_TYPE_ID`]); the memo is the first
//! table and its `current` names the one in use (itself until it grows).
//! An ambiguous word pins what it reaches, so the noted addresses stay
//! valid while the memo is alive. Stores go through the write barrier: a
//! memo that got old must keep a young table (and entry) alive.

#![allow(clippy::many_single_char_names)]
#![allow(clippy::cast_ptr_alignment)] // GC payloads are word-aligned

use core::mem::size_of;

use rokr_common::object_header::HEADER_SIZE;
use rokr_gc::SCAN_WORDS_TYPE_ID;

const W: usize = size_of::<usize>();

const CURRENT: usize = 0;
const LEN: usize = 1;
const CAP: usize = 2;
const ENTRIES: usize = 3;
/// Words per entry: four key words, then the copy.
const E: usize = 5;

const FIRST_CAP: usize = 16;

const fn words(obj: *mut u8) -> *mut usize {
    obj.wrapping_add(HEADER_SIZE).cast()
}

/// A zeroed table of `cap` entries (a power of two). May collect.
fn new_table(cap: usize) -> *mut u8 {
    let t = rokr_gc::alloc(HEADER_SIZE + W * (ENTRIES + E * cap), 8, SCAN_WORDS_TYPE_ID);
    // SAFETY: a fresh zeroed table with room for the counts.
    unsafe { *words(t).add(CAP) = cap };
    t
}

#[cfg(target_pointer_width = "64")]
const fn spread(k: [usize; 4]) -> usize {
    let mut h = k[0] >> 3;
    h = (h ^ k[1].wrapping_mul(0x9E37_79B9_7F4A_7C15)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    h = (h ^ k[2].wrapping_mul(0x94D0_49BB_1331_11EB)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    (h ^ k[3]).wrapping_mul(0xBF58_476D_1CE4_E5B9) >> 32
}

#[cfg(not(target_pointer_width = "64"))]
const fn spread(k: [usize; 4]) -> usize {
    let mut h = k[0] >> 3;
    h = (h ^ k[1].wrapping_mul(0x9E37_79B9)).wrapping_mul(0x85EB_CA6B);
    h = (h ^ k[2].wrapping_mul(0xC2B2_AE35)).wrapping_mul(0x9E37_79B9);
    (h ^ k[3]).wrapping_mul(0x85EB_CA6B) >> 8
}

/// Entry of key `k` in `t`: where it is, or the empty entry it would take.
///
/// # Safety
/// `t` is a live table that has an empty entry; `k[0]` is not 0.
unsafe fn probe(t: *mut u8, k: [usize; 4]) -> *mut usize {
    // SAFETY: caller contract; `i < cap`.
    unsafe {
        let w = words(t);
        let mask = *w.add(CAP) - 1;
        let mut i = spread(k) & mask;
        loop {
            let s = w.add(ENTRIES + E * i);
            if *s == 0
                || (*s == k[0] && *s.add(1) == k[1] && *s.add(2) == k[2] && *s.add(3) == k[3])
            {
                return s;
            }
            i = (i + 1) & mask;
        }
    }
}

/// A new, empty memo (`rok::core::marker::Memo`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_xfer_memo() -> *mut u8 {
    let m = new_table(FIRST_CAP);
    // SAFETY: fresh table.
    unsafe { *words(m).add(CURRENT) = m as usize };
    m
}

/// The copy noted in memo `m` for `orig` viewed as `(a, b, c)`, or
/// `orig` itself.
///
/// # Safety
/// `m` is a memo from [`rok_xfer_memo`]; `orig` is not 0.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_xfer_find(
    m: *mut u8,
    orig: *mut u8,
    a: usize,
    b: usize,
    c: usize,
) -> *mut u8 {
    // SAFETY: caller contract; a table always has an empty entry.
    unsafe {
        let t = *words(m).add(CURRENT) as *mut u8;
        let s = probe(t, [orig as usize, a, b, c]);
        if *s == 0 {
            return orig;
        }
        *s.add(4) as *mut u8
    }
}

/// Note `copy` as the copy of `orig` viewed as `(a, b, c)` in memo `m`.
/// May collect.
///
/// # Safety
/// `m` is a memo from [`rok_xfer_memo`]; the key is not noted yet and
/// `orig` is not 0.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_xfer_note(
    m: *mut u8,
    orig: *mut u8,
    a: usize,
    b: usize,
    c: usize,
    copy: *mut u8,
) {
    // SAFETY: caller contract. The table in use stays put while the
    // memo's word reaches it (ambiguous words pin).
    unsafe {
        let t = *words(m).add(CURRENT) as *mut u8;
        let (len, cap) = (*words(t).add(LEN), *words(t).add(CAP));
        // Into the table first (at most half full, so there is room):
        // the caller may not root `orig` past this call, and the growth
        // below may collect.
        let s = probe(t, [orig as usize, a, b, c]);
        rokr_gc::write_barrier(t, s.cast());
        rokr_gc::write_barrier(t, s.add(4).cast());
        *s = orig as usize;
        *s.add(1) = a;
        *s.add(2) = b;
        *s.add(3) = c;
        *s.add(4) = copy as usize;
        *words(t).add(LEN) = len + 1;
        if 2 * (len + 1) <= cap {
            return;
        }
        // This call may be the memo's last use in every frame: pin it
        // (and through it the table) across the allocation.
        rokr_gc::pin(m);
        let bigger = new_table(2 * cap);
        rokr_gc::unpin(m);
        for i in 0..cap {
            let s = words(t).add(ENTRIES + E * i);
            if *s != 0 {
                let d = probe(bigger, [*s, *s.add(1), *s.add(2), *s.add(3)]);
                for j in 0..E {
                    *d.add(j) = *s.add(j);
                }
            }
        }
        *words(bigger).add(LEN) = len + 1;
        rokr_gc::write_barrier(m, words(m).add(CURRENT).cast());
        *words(m).add(CURRENT) = bigger as usize;
    }
}

/// How many `size`-byte elements the GC object `buf` holds.
///
/// # Safety
/// `buf` is the start of a live GC object (never a view of a `str`'s
/// bytes).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_xfer_slots(buf: *mut u8, size: usize) -> usize {
    // SAFETY: caller contract.
    unsafe { rokr_gc::payload_bytes(buf) / size.max(1) }
}

/// Whether `buf` is the zero reference of a zeroed value.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_xfer_null(buf: *mut u8) -> bool {
    buf.is_null()
}

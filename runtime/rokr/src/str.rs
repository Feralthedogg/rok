//! Runtime side of `str` (stdlib 2.15, ABI 808): a `(ptr, len)` value.
//!
//! Literals point at static NUL-terminated bytes. Every string built at
//! run time is a GC object (type id [`STR_TYPE_ID`], no traced children)
//! whose payload holds the bytes plus a trailing NUL, so `ptr` alone is
//! also a C string. The collector treats `ptr` as an interior pointer.
//!
//! `rok_*` symbols take and return `str` by value: two words, the same
//! registers as the LLVM `{ptr, iN}` aggregate the compiler passes.
//! Allocating entries may collect; their `str` arguments stay alive
//! because the caller's shadow-stack frame roots them.

use core::ptr;

use rokr_common::object_header::{HEADER_ALIGN, HEADER_SIZE};

/// Standard-library type id of runtime strings (801 §8.1.2 reserved
/// range); never registered, so the collector traces nothing inside.
const STR_TYPE_ID: u32 = 1;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct RokStr {
    pub ptr: *const u8,
    pub len: usize,
}

impl RokStr {
    pub(crate) const fn bytes(&self) -> &[u8] {
        if self.len == 0 {
            return &[];
        }
        // SAFETY: a `str` value's `ptr` is valid for `len` bytes.
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}

/// A fresh GC string of `len` bytes (zeroed, NUL-terminated); returns
/// the writable byte pointer.
pub fn alloc_str(len: usize) -> *mut u8 {
    let Some(size) = len.checked_add(HEADER_SIZE + 1) else {
        rokr_common::fatal(b"rok runtime: string too long");
    };
    let obj = rokr_gc::alloc(size, HEADER_ALIGN, STR_TYPE_ID);
    // SAFETY: the payload follows the 16-byte header.
    unsafe { obj.add(HEADER_SIZE) }
}

/// GC string holding the concatenation of `parts`.
pub fn build(parts: &[&[u8]]) -> RokStr {
    let len = parts.iter().map(|p| p.len()).sum();
    let p = alloc_str(len);
    let mut at = 0;
    for part in parts {
        // SAFETY: `p` has room for `len` bytes; sources are distinct
        // (a fresh object never overlaps an argument).
        unsafe { ptr::copy_nonoverlapping(part.as_ptr(), p.add(at), part.len()) };
        at += part.len();
    }
    RokStr { ptr: p, len }
}

fn panic_msg(msg: &[u8]) -> ! {
    // SAFETY: valid slice.
    unsafe { crate::rok_panic(msg.as_ptr(), msg.len()) }
}

/// GC allocation of `size` zeroed bytes for library buffers (strings,
/// collection storage), returned as a `str`-shaped handle `(ptr, size)`:
/// a `str`-typed slot roots it like a string. `traced` != 0 makes every
/// pointer-aligned word of the buffer a candidate reference, so it may
/// hold `str` / `any` values; otherwise nothing inside is traced.
#[unsafe(no_mangle)]
pub extern "C" fn rok_gc_alloc_bytes(size: usize, traced: i32) -> RokStr {
    if traced == 0 {
        return RokStr {
            ptr: alloc_str(size),
            len: size,
        };
    }
    let Some(total) = size.checked_add(HEADER_SIZE) else {
        rokr_common::fatal(b"rok runtime: allocation size overflow");
    };
    let obj = rokr_gc::alloc(total, HEADER_ALIGN, rokr_gc::SCAN_WORDS_TYPE_ID);
    RokStr {
        // SAFETY: the payload follows the header.
        ptr: unsafe { obj.add(HEADER_SIZE) },
        len: size,
    }
}

/// `strlen` for a `char*` a C function returned; null → 0.
///
/// # Safety
/// `s` must be null or a valid NUL-terminated string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_cstr_len(s: *const u8) -> usize {
    if s.is_null() {
        return 0;
    }
    // SAFETY: caller contract.
    unsafe { libc::strlen(s.cast()) }
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_str_concat(a: RokStr, b: RokStr) -> RokStr {
    build(&[a.bytes(), b.bytes()])
}

/// Byte-wise three-way compare: -1, 0 or 1.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_cmp(a: RokStr, b: RokStr) -> i32 {
    a.bytes().cmp(b.bytes()) as i32
}

/// FNV-1a over the bytes: `str`'s `Hash` (stdlib 2.5.6; equal strings
/// hash alike).
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_hash(s: RokStr) -> u64 {
    s.bytes().iter().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(*b)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// `s[start:end]` (byte offsets): a copy. Panics outside `0..=len`, on a
/// reversed range, or off a UTF-8 char boundary (stdlib 2.15.3).
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_slice(s: RokStr, start: usize, end: usize) -> RokStr {
    let b = s.bytes();
    if start > end || end > b.len() {
        panic_msg(b"string slice out of range");
    }
    let boundary = |i: usize| i == b.len() || (b[i] & 0xC0) != 0x80;
    if !boundary(start) || !boundary(end) {
        panic_msg(b"string slice is not on a char boundary");
    }
    build(&[&b[start..end]])
}

/// Byte offset of the first `pat` in `s`, or -1.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_find(s: RokStr, pat: RokStr) -> isize {
    let (h, n) = (s.bytes(), pat.bytes());
    if n.is_empty() {
        return 0;
    }
    h.windows(n.len())
        .position(|w| w == n)
        .map_or(-1, |i| i as isize)
}

/// Byte offset of the last `pat` in `s`, or -1.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_rfind(s: RokStr, pat: RokStr) -> isize {
    let (h, n) = (s.bytes(), pat.bytes());
    if n.is_empty() {
        return h.len() as isize;
    }
    h.windows(n.len())
        .rposition(|w| w == n)
        .map_or(-1, |i| i as isize)
}

/// Every non-overlapping `from` replaced by `to`.
#[unsafe(no_mangle)]
#[allow(clippy::many_single_char_names)] // byte-crunching locals
pub extern "C" fn rok_str_replace(s: RokStr, from: RokStr, to: RokStr) -> RokStr {
    let (h, f, t) = (s.bytes(), from.bytes(), to.bytes());
    if f.is_empty() {
        return build(&[h]);
    }
    // Two passes: measure, then copy.
    let mut count = 0;
    let mut i = 0;
    while i + f.len() <= h.len() {
        if &h[i..i + f.len()] == f {
            count += 1;
            i += f.len();
        } else {
            i += 1;
        }
    }
    let len = h.len() - count * f.len() + count * t.len();
    let p = alloc_str(len);
    let (mut i, mut o) = (0, 0);
    // SAFETY: writes stay within the `len` bytes measured above.
    unsafe {
        while i < h.len() {
            if i + f.len() <= h.len() && &h[i..i + f.len()] == f {
                ptr::copy_nonoverlapping(t.as_ptr(), p.add(o), t.len());
                o += t.len();
                i += f.len();
            } else {
                *p.add(o) = h[i];
                o += 1;
                i += 1;
            }
        }
    }
    RokStr { ptr: p, len }
}

/// Number of chars (UTF-8 scalar values) in `s`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_char_count(s: RokStr) -> usize {
    s.bytes().iter().filter(|&&b| (b & 0xC0) != 0x80).count()
}

/// `Debug` of a string: double-quoted, with `\`, `"`, `\n`, `\r`, `\t`
/// and other control bytes escaped.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_debug(s: RokStr) -> RokStr {
    let mut len = 2;
    for &c in s.bytes() {
        len += match c {
            b'\\' | b'"' | b'\n' | b'\r' | b'\t' => 2,
            c if c < 0x20 || c == 0x7F => 6, // \u{XX}
            _ => 1,
        };
    }
    let p = alloc_str(len);
    let mut at = 0;
    let mut put = |bytes: &[u8]| {
        // SAFETY: exactly `len` bytes are written.
        unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(at), bytes.len()) };
        at += bytes.len();
    };
    put(b"\"");
    for &c in s.bytes() {
        match c {
            b'\\' => put(b"\\\\"),
            b'"' => put(b"\\\""),
            b'\n' => put(b"\\n"),
            b'\r' => put(b"\\r"),
            b'\t' => put(b"\\t"),
            c if c < 0x20 || c == 0x7F => {
                const HEX: &[u8; 16] = b"0123456789abcdef";
                put(&[
                    b'\\',
                    b'u',
                    b'{',
                    HEX[usize::from(c >> 4)],
                    HEX[usize::from(c & 15)],
                    b'}',
                ]);
            }
            c => put(&[c]),
        }
    }
    put(b"\"");
    RokStr { ptr: p, len }
}

/// UTF-8 encoding of `c` (U+FFFD for a non-scalar value).
fn utf8(c: u32, buf: &mut [u8; 4]) -> &[u8] {
    char::from_u32(c)
        .unwrap_or(char::REPLACEMENT_CHARACTER)
        .encode_utf8(buf)
        .as_bytes()
}

// Display bodies for primitives (stdlib 2.10). Floats use `%g`, like
// `rok_print_f64`.

#[unsafe(no_mangle)]
pub extern "C" fn rok_str_from_i64(n: i64) -> RokStr {
    let mut buf = [0u8; 24];
    let mut i = buf.len();
    let mut v = n.unsigned_abs();
    loop {
        i -= 1;
        buf[i] = b'0' + (v % 10) as u8;
        v /= 10;
        if v == 0 {
            break;
        }
    }
    if n < 0 {
        i -= 1;
        buf[i] = b'-';
    }
    build(&[&buf[i..]])
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_str_from_u64(n: u64) -> RokStr {
    let mut buf = [0u8; 20];
    let mut i = buf.len();
    let mut v = n;
    loop {
        i -= 1;
        buf[i] = b'0' + (v % 10) as u8;
        v /= 10;
        if v == 0 {
            break;
        }
    }
    build(&[&buf[i..]])
}

/// `prec` < 0: shortest `%g`; otherwise fixed `%.{prec}f`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_from_f64(d: f64, prec: i32) -> RokStr {
    let mut buf = [0u8; 512];
    // SAFETY: bounded write into `buf`; formats match the arguments.
    let n = unsafe {
        if prec < 0 {
            libc::snprintf(buf.as_mut_ptr().cast(), buf.len(), c"%g".as_ptr(), d)
        } else {
            libc::snprintf(
                buf.as_mut_ptr().cast(),
                buf.len(),
                c"%.*f".as_ptr(),
                prec,
                d,
            )
        }
    };
    let n = (n.max(0) as usize).min(buf.len() - 1);
    build(&[&buf[..n]])
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_str_from_char(c: u32) -> RokStr {
    let mut buf = [0u8; 4];
    build(&[utf8(c, &mut buf)])
}

/// Byte `i` of `s` (stdlib 2.15 `bytes()`); the caller checks `i < len`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_byte(s: RokStr, i: usize) -> u8 {
    s.bytes().get(i).copied().unwrap_or(0)
}

/// `s` as UTF-8 text (it always is: `str` holds UTF-8).
pub fn text(s: &RokStr) -> &str {
    core::str::from_utf8(s.bytes()).unwrap_or("")
}

/// Whether `s` parses as an integer of `bits` bits (`signed != 0`):
/// 0 = ok, 1 = empty, 2 = invalid digit, 3 = out of range
/// (`FromStr` for the integer types, stdlib 2.15.7).
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_int_status(s: RokStr, signed: i32, bits: u32) -> i32 {
    let t = text(&s);
    let digits = t.strip_prefix(['-', '+']).unwrap_or(t);
    if digits.is_empty() {
        return 1;
    }
    if !digits.bytes().all(|b| b.is_ascii_digit()) {
        return 2;
    }
    let fits = if signed != 0 {
        t.parse::<i64>()
            .is_ok_and(|v| bits >= 64 || (v >= -(1i64 << (bits - 1)) && v < (1i64 << (bits - 1))))
    } else {
        !t.starts_with('-')
            && t.parse::<u64>()
                .is_ok_and(|v| bits >= 64 || v < (1u64 << bits))
    };
    if fits { 0 } else { 3 }
}

/// `s` as an `i64` (checked first by `rok_str_int_status`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_to_i64(s: RokStr) -> i64 {
    text(&s).parse().unwrap_or(0)
}

/// `s` as a `u64` (checked first by `rok_str_int_status`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_to_u64(s: RokStr) -> u64 {
    text(&s).parse().unwrap_or(0)
}

/// Whether `s` parses as a float (`inf`, `NaN`, exponents included).
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_float_ok(s: RokStr) -> i32 {
    i32::from(text(&s).parse::<f64>().is_ok())
}

/// `s` as an `f64` (checked first by `rok_str_float_ok`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_str_to_f64(s: RokStr) -> f64 {
    text(&s).parse().unwrap_or(0.0)
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

    // Non-allocating entries: safe to run alongside other tests.
    #[test]
    fn non_allocating_ops() {
        // FNV-1a: the empty string hashes to the offset basis.
        assert_eq!(rok_str_hash(s(b"")), 0xcbf2_9ce4_8422_2325);
        assert_eq!(rok_str_hash(s(b"ab")), rok_str_hash(s(b"ab")));
        assert_ne!(rok_str_hash(s(b"ab")), rok_str_hash(s(b"ba")));
        assert_eq!(rok_str_char_count(s("a한😀".as_bytes())), 3);
        assert_eq!(rok_str_find(s(b"abc"), s(b"")), 0);
        assert_eq!(rok_str_find(s(b"abc"), s(b"x")), -1);
        assert_eq!(rok_str_rfind(s(b"abc"), s(b"")), 3);
        assert_eq!(rok_str_byte(s(b"ab"), 1), b'b');
        assert_eq!(rok_str_byte(s(b"ab"), 9), 0);
    }

    #[test]
    fn parse_numbers() {
        // FromStr status: 0 ok, 1 empty, 2 bad digit, 3 out of range.
        let st = |v: &'static [u8], signed, bits| rok_str_int_status(s(v), signed, bits);
        assert_eq!(st(b"-128", 1, 8), 0);
        assert_eq!(st(b"128", 1, 8), 3);
        assert_eq!(st(b"255", 0, 8), 0);
        assert_eq!(st(b"256", 0, 8), 3);
        assert_eq!(st(b"-1", 0, 32), 3);
        assert_eq!(st(b"+7", 1, 32), 0);
        assert_eq!(st(b"", 1, 32), 1);
        assert_eq!(st(b"-", 1, 32), 1);
        assert_eq!(st(b"1_000", 1, 32), 2);
        assert_eq!(st(b" 1", 1, 32), 2);
        assert_eq!(st(b"-9223372036854775808", 1, 64), 0);
        assert_eq!(st(b"18446744073709551616", 0, 64), 3);
        assert_eq!(rok_str_to_i64(s(b"-42")), -42);
        assert_eq!(rok_str_to_u64(s(b"18446744073709551615")), u64::MAX);
        assert_eq!(rok_str_float_ok(s(b"1e-3")), 1);
        assert_eq!(rok_str_float_ok(s(b"inf")), 1);
        assert_eq!(rok_str_float_ok(s(b"1.2.3")), 0);
        assert!((rok_str_to_f64(s(b"2.5")) - 2.5).abs() < f64::EPSILON);
    }

    // Run from `gc_alloc_initializes_header_and_alignment`: the GC heap is
    // single-mutator, so allocating tests must not run in parallel.
    pub fn string_ops() {
        assert_eq!(rok_str_concat(s(b"ab"), s(b"cd")).bytes(), b"abcd");
        assert_eq!(rok_str_cmp(s(b"ab"), s(b"b")), -1);
        assert_eq!(rok_str_cmp(s(b"ab"), s(b"ab")), 0);
        assert_eq!(
            rok_str_slice(s("a세b".as_bytes()), 1, 4).bytes(),
            "세".as_bytes()
        );
        assert_eq!(rok_str_find(s(b"hello"), s(b"ll")), 2);
        assert_eq!(rok_str_rfind(s(b"abab"), s(b"ab")), 2);
        assert_eq!(crate::unicode::rok_str_trim(s(b"  x "), 0).bytes(), b"x");
        crate::unicode::tests::str_case_and_trim();
        assert_eq!(
            rok_str_replace(s(b"a-b-c"), s(b"-"), s(b"+")).bytes(),
            b"a+b+c"
        );
        assert_eq!(rok_str_debug(s(b"a\"\n")).bytes(), b"\"a\\\"\\n\"");
        assert_eq!(rok_str_from_i64(-120).bytes(), b"-120");
        assert_eq!(rok_str_from_u64(u64::MAX).bytes(), b"18446744073709551615");
        assert_eq!(rok_str_from_f64(1.5, -1).bytes(), b"1.5");
        assert_eq!(rok_str_from_f64(1.0 / 3.0, 2).bytes(), b"0.33");
        assert_eq!(rok_str_from_char(0xD55C).bytes(), "한".as_bytes());
        // Runtime strings stay NUL-terminated for C.
        let c = rok_str_concat(s(b"x"), s(b"y"));
        // SAFETY: one byte past `len` is the terminator.
        assert_eq!(unsafe { *c.ptr.add(c.len) }, 0);
    }
}

//! f-string support (refs-lang 1.7.3, stdlib 2.10): spec parsing and
//! number digits. Padding and per-type dispatch live in `core::fmt`.

// `GcBuf` elements start 8-aligned after the header.
#![allow(clippy::cast_ptr_alignment)]

use core::fmt::Write as _;
use core::ptr;

use rokr_common::object_header::{HEADER_SIZE, ObjectHeader};

use crate::fmt_spec::parse;
use crate::fmt_spec::{FmtSpec, pack, unpack};
use crate::str::{RokStr, alloc_str, escape, text};

/// A panic message (cut at its size).
struct Buf {
    b: [u8; 256],
    n: usize,
}

impl Buf {
    const fn new() -> Self {
        Self { b: [0; 256], n: 0 }
    }
}

impl core::fmt::Write for Buf {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let end = self.n + s.len();
        if end > self.b.len() {
            return Err(core::fmt::Error);
        }
        self.b[self.n..end].copy_from_slice(s.as_bytes());
        self.n = end;
        Ok(())
    }
}

fn fail(spec: &str, why: &str) -> ! {
    let mut m = Buf::new();
    let _ = write!(m, "invalid format spec `{spec}`: {why}");
    // SAFETY: valid buffer.
    unsafe { crate::rok_panic(m.b.as_ptr(), m.n) }
}

/// `spec` parsed into `out`, a `GcBuf<i64>` of 8 words: fill, align,
/// sign, `#`, `0`, width, precision (-1 when absent), type (0 when absent
/// or the Display letters `s d g`). Panics on a malformed spec; only a
/// dynamic one gets here unchecked.
///
/// # Safety
/// `out` is a live `GcBuf<i64>` of at least 8 elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_fmt_spec_parse(spec: RokStr, out: *mut u8) {
    let t = text(&spec);
    let s = parse(t).unwrap_or_else(|why| fail(t, why));
    let opt = |v: Option<usize>| v.map_or(-1, |v| v as i64);
    let ty = if matches!(s.ty, b's' | b'd' | b'g') {
        0
    } else {
        s.ty
    };
    let words = [
        i64::from(u32::from(s.fill)),
        s.align.into(),
        s.sign.into(),
        s.alt.into(),
        s.zero.into(),
        s.width.map_or(-1, |w| w as i64),
        opt(s.precision),
        ty.into(),
    ];
    // SAFETY: caller contract; elements start after the header.
    unsafe {
        ptr::copy_nonoverlapping(
            words.as_ptr(),
            out.add(HEADER_SIZE).cast::<i64>(),
            words.len(),
        );
    }
}

/// The text of `v` (an `f32` widened when `is_f32 != 0`): Display for
/// `ty` 0, else `e`, `E` or `f`. Without a precision (`prec < 0`) the
/// digits are the shortest that read back as the same value of its own
/// width; `f` then takes 6 places. Every float rendering comes here.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_float(v: f64, is_f32: u32, ty: u32, prec: i64) -> RokStr {
    let mut w = W::of(rok_fmt_new(32));
    float_write(&mut w, v, is_f32, ty, prec);
    rok_fmt_finish(w.done())
}

#[allow(clippy::cast_possible_truncation)] // `f32` values widened by the caller
fn float_write(out: &mut W, v: f64, is_f32: u32, ty: u32, prec: i64) {
    let start = out.len;
    let p = usize::try_from(prec).ok();
    let x = v as f32;
    let exp = ty == u32::from(b'e') || ty == u32::from(b'E');
    let _ = match (exp, ty == u32::from(b'f'), p, is_f32 != 0) {
        (true, _, Some(d), true) => write!(out, "{x:.d$e}"),
        (true, _, Some(d), false) => write!(out, "{v:.d$e}"),
        (true, _, None, true) => write!(out, "{x:e}"),
        (true, _, None, false) => write!(out, "{v:e}"),
        (_, true, d, _) => write!(out, "{v:.*}", d.unwrap_or(6)),
        (_, _, Some(d), _) => write!(out, "{v:.d$}"),
        (_, _, None, true) => write!(out, "{x}"),
        (_, _, None, false) => write!(out, "{v}"),
    };
    if ty == u32::from(b'E') {
        // `inf` / `NaN` hold no `e`.
        out.tail_mut(start)
            .iter_mut()
            .filter(|c| **c == b'e')
            .for_each(|c| *c = b'E');
    }
}

/// The decimal digits `d` of an integer in `1.5e3` form: shortest
/// exact without a precision (`prec < 0`), else rounded half up to
/// `prec` fraction digits.
fn exp_write(out: &mut W, d: &[u8], prec: i64, upper: bool) {
    if d.is_empty() {
        out.put(b"0e0");
        return;
    }
    let mut exp = d.len() - 1;
    // `k` significant digits: `d[..keep]`, then `bump` on the last one
    // kept (a carry turns trailing `9`s into `0`s), then `0`s.
    let k = match usize::try_from(prec) {
        Err(_) => d.iter().rposition(|&c| c != b'0').map_or(1, |i| i + 1),
        Ok(p) => p.saturating_add(1),
    };
    let mut keep = k.min(d.len());
    let mut bump = false;
    if d.len() > k && d[k] >= b'5' {
        if let Some(i) = d[..k].iter().rposition(|&c| c != b'9') {
            keep = i;
            bump = true;
        } else {
            // 9.99 rounds to 10.0: one more exponent.
            keep = 0;
            exp += 1;
        }
    }
    let lead = match (bump, keep) {
        (true, _) => Some(d[keep] + 1),
        (false, 0) => Some(b'1'),
        _ => None,
    };
    let sig = d[..keep].iter().copied().chain(lead);
    let zeros = k - keep - usize::from(lead.is_some());
    for (i, c) in sig.chain(core::iter::repeat_n(b'0', zeros)).enumerate() {
        out.put(&[c]);
        if i == 0 && k > 1 {
            out.put(b".");
        }
    }
    let _ = write!(out, "{}{exp}", if upper { 'E' } else { 'e' });
}

// A `core::fmt::Formatter`'s text: a GC string being filled, held as a
// `str`-shaped handle `(text, len)`; its room is what the string object's
// size (`gc_word`) leaves past the header and the NUL. Each writing entry takes
// the handle and returns it: longer, and moved when the text outgrew
// its allocation. The spec comes with each call that applies one, as
// `fmt_spec::pack`'s two words. `rok_fmt_finish` hands the text over
// in place.

/// A formatter being written.
struct W {
    p: *mut u8,
    len: usize,
    cap: usize,
}

impl W {
    fn of(h: RokStr) -> Self {
        let p = h.ptr.cast_mut();
        // SAFETY: `p` is the payload of a live GC string (`alloc_str`),
        // which the caller roots, so it does not move.
        let size = unsafe { (*p.sub(HEADER_SIZE).cast::<ObjectHeader>()).gc_word };
        Self {
            p,
            len: h.len,
            #[allow(clippy::cast_possible_truncation)] // an object's size
            cap: size as usize - HEADER_SIZE - 1,
        }
    }
    const fn done(self) -> RokStr {
        RokStr {
            ptr: self.p,
            len: self.len,
        }
    }
    /// Room for `n` more bytes (doubling).
    fn reserve(&mut self, n: usize) {
        if self.len + n <= self.cap {
            return;
        }
        let cap = self.cap.saturating_mul(2).max(self.len + n);
        // May collect; the caller's frame roots the old text, which stays
        // in place.
        let p = alloc_str(cap);
        // SAFETY: the old text holds `len` bytes; a fresh object never
        // overlaps.
        unsafe { ptr::copy_nonoverlapping(self.p, p, self.len) };
        self.p = p;
        self.cap = cap;
    }
    fn put(&mut self, b: &[u8]) {
        if b.is_empty() {
            return;
        }
        self.reserve(b.len());
        // SAFETY: `reserve` made room; `b` is not in this buffer.
        unsafe { ptr::copy_nonoverlapping(b.as_ptr(), self.p.add(self.len), b.len()) };
        self.len += b.len();
    }
    /// The text written from `start`.
    const fn tail(&self, start: usize) -> &[u8] {
        if start >= self.len {
            return &[];
        }
        // SAFETY: `start < len <= cap` bytes of text.
        unsafe { core::slice::from_raw_parts(self.p.add(start), self.len - start) }
    }
    fn tail_mut(&mut self, start: usize) -> &mut [u8] {
        if start >= self.len {
            return &mut [];
        }
        // SAFETY: `start < len <= cap` bytes of text.
        unsafe { core::slice::from_raw_parts_mut(self.p.add(start), self.len - start) }
    }
    /// `count` copies of `c` at byte `at`, moving what follows.
    fn insert(&mut self, at: usize, c: char, count: usize) {
        if count == 0 {
            return;
        }
        let mut tmp = [0; 4];
        let one = c.encode_utf8(&mut tmp).as_bytes();
        let n = one.len() * count;
        self.reserve(n);
        let p = self.p;
        // SAFETY: `at <= len` and `len + n <= cap` after `reserve`.
        unsafe {
            ptr::copy(p.add(at), p.add(at + n), self.len - at);
            for k in 0..count {
                ptr::copy_nonoverlapping(one.as_ptr(), p.add(at + k * one.len()), one.len());
            }
        }
        self.len += n;
    }
}

impl core::fmt::Write for W {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.put(s.as_bytes());
        Ok(())
    }
}

/// What the sign shows: `-`, or what `+` / ` ` ask for.
const fn sign(spec: &FmtSpec, neg: bool) -> &'static [u8] {
    match (neg, spec.sign) {
        (true, _) => b"-",
        (false, b'+') => b"+",
        (false, b' ') => b" ",
        _ => b"",
    }
}

const fn radix(ty: u8) -> u32 {
    match ty {
        b'b' => 2,
        b'o' => 8,
        b'x' | b'X' => 16,
        _ => 10,
    }
}

/// Cut what was written since `start` to `precision` chars.
fn cut(w: &mut W, spec: &FmtSpec, start: usize) {
    if let Some(p) = spec.precision {
        let t = w.tail(start);
        let end = core::str::from_utf8(t)
            .ok()
            .and_then(|s| s.char_indices().nth(p))
            .map_or(t.len(), |(i, _)| i);
        w.len = start + end;
    }
}

/// Pad what was written since `start` to `width` (2.10.8). `numeric`
/// aligns right by default and lets `0` / `=` fill at `mid`, after the
/// sign and prefix.
fn pad(w: &mut W, spec: &FmtSpec, start: usize, mid: usize, numeric: bool) {
    let Some(width) = spec.width else {
        return;
    };
    let n = w
        .tail(start)
        .iter()
        .filter(|&&b| (b & 0xC0) != 0x80)
        .count();
    if width <= n {
        return;
    }
    let gap = width - n;
    let (mut fill, mut align) = (spec.fill, spec.align);
    if numeric && spec.zero && align == 0 {
        fill = '0';
        align = b'=';
    }
    let (at, before) = match align {
        b'=' if numeric => (mid, gap),
        b'<' => (start, 0),
        0 if !numeric => (start, 0),
        b'^' => (start, gap / 2),
        _ => (start, gap),
    };
    let end = w.len;
    w.insert(end, fill, gap - before);
    w.insert(at, fill, before);
}

/// How a number's body is written.
#[derive(Clone, Copy, Default)]
struct Body {
    /// Pads like text (inf / NaN).
    text: bool,
    /// Uppercase hex digits (`X`).
    upper: bool,
    /// `.` and this many `0`s after (`f` on an integer).
    zeros: usize,
}

/// A number: its sign, `prefix` under `#`, `body`, padded.
fn number(
    w: &mut W,
    spec: &FmtSpec,
    neg: bool,
    prefix: &[u8],
    body: impl FnOnce(&mut W),
    how: Body,
) {
    let start = w.len;
    w.put(sign(spec, neg));
    if spec.alt {
        w.put(prefix);
    }
    let mid = w.len;
    body(w);
    if how.upper {
        w.tail_mut(mid).make_ascii_uppercase();
    }
    if how.zeros > 0 {
        w.put(b".");
        for _ in 0..how.zeros {
            w.put(b"0");
        }
    }
    pad(w, spec, start, mid, !how.text);
}

const fn radix_prefix(ty: u8) -> &'static [u8] {
    match ty {
        b'b' => b"0b",
        b'o' => b"0o",
        _ => b"0x",
    }
}

/// An integer from its sign and its digits in the spec's radix (decimal
/// for `e` / `E` / `f`).
fn digits(w: &mut W, spec: &FmtSpec, neg: bool, d: &[u8]) {
    let plain = Body::default();
    match spec.ty {
        b'X' => number(
            w,
            spec,
            neg,
            b"0x",
            |w| w.put(d),
            Body {
                upper: true,
                ..plain
            },
        ),
        b'b' | b'o' | b'x' => number(w, spec, neg, radix_prefix(spec.ty), |w| w.put(d), plain),
        b'e' | b'E' => {
            let prec = spec.precision.map_or(-1, |p| p as i64);
            let upper = spec.ty == b'E';
            number(w, spec, neg, b"", |w| exp_write(w, d, prec, upper), plain);
        }
        b'f' => {
            let zeros = spec.precision.unwrap_or(6);
            number(w, spec, neg, b"", |w| w.put(d), Body { zeros, ..plain });
        }
        _ => number(w, spec, neg, b"", |w| w.put(d), plain),
    }
}

/// An empty formatter with room for `cap` bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_new(cap: usize) -> RokStr {
    RokStr {
        ptr: alloc_str(cap),
        len: 0,
    }
}

/// The text, as a `str` in place: NUL-terminated (the allocation has a
/// byte past `cap`). The handle is spent.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_fmt_finish(h: RokStr) -> RokStr {
    // SAFETY: the allocation holds a byte past the room `len` is within.
    unsafe { h.ptr.cast_mut().add(h.len).write(0) };
    h
}

#[unsafe(no_mangle)]
pub const extern "C" fn rok_fmt_len(h: RokStr) -> usize {
    h.len
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_str(h: RokStr, s: RokStr) -> RokStr {
    let mut w = W::of(h);
    w.put(s.bytes());
    w.done()
}

#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_char(h: RokStr, c: u32) -> RokStr {
    let c = char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER);
    let mut w = W::of(h);
    w.put(c.encode_utf8(&mut [0; 4]).as_bytes());
    w.done()
}

/// `s` as a rok literal between `quote`s, escaped (`rok_str_escape`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_escaped(h: RokStr, s: RokStr, quote: u32) -> RokStr {
    let mut w = W::of(h);
    escape(text(&s), quote, |b| w.put(b));
    w.done()
}

/// An integer under the spec `flags` / `counts`: the bits `v` of a
/// `bits`-wide integer, `signed` or not. `b o x X` show a signed one's
/// two's complement at that width, or its sign and magnitude when
/// `bits` is 0 (`int`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_int(
    h: RokStr,
    flags: u64,
    counts: u64,
    value: i64,
    signed: u32,
    bits: u32,
) -> RokStr {
    let mut w = W::of(h);
    let spec = unpack(flags, counts);
    let base = u64::from(radix(spec.ty));
    let (neg, mag) = if signed != 0 && (base == 10 || bits == 0) {
        (value < 0, value.unsigned_abs())
    } else if bits == 0 || bits >= 64 {
        (false, value as u64)
    } else {
        (false, (value as u64) & ((1u64 << bits) - 1))
    };
    let mut tmp = [0u8; 64];
    let mut at = tmp.len();
    let mut rest = mag;
    loop {
        at -= 1;
        tmp[at] = b"0123456789abcdef"[(rest % base) as usize];
        rest /= base;
        if rest == 0 {
            break;
        }
    }
    digits(&mut w, &spec, neg, &tmp[at..]);
    w.done()
}

/// An integer from its sign and `d`, its digits in the spec's radix
/// (decimal for `e` / `E` / `f`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_digits(
    h: RokStr,
    flags: u64,
    counts: u64,
    neg: u32,
    d: RokStr,
) -> RokStr {
    let mut w = W::of(h);
    digits(&mut w, &unpack(flags, counts), neg != 0, d.bytes());
    w.done()
}

/// `Formatter::pad_integral`: the sign, `prefix` under `#`, `buf`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_integral(
    h: RokStr,
    flags: u64,
    counts: u64,
    nonneg: u32,
    prefix: RokStr,
    buf: RokStr,
) -> RokStr {
    let mut w = W::of(h);
    let spec = unpack(flags, counts);
    number(
        &mut w,
        &spec,
        nonneg == 0,
        prefix.bytes(),
        |w| w.put(buf.bytes()),
        Body::default(),
    );
    w.done()
}

/// A float (`is_f32`: an `f32` widened); inf / NaN pad like text.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_f64(h: RokStr, flags: u64, counts: u64, v: f64, is_f32: u32) -> RokStr {
    let mut w = W::of(h);
    let spec = unpack(flags, counts);
    if radix(spec.ty) != 10 {
        let m = b"invalid format spec: a float has no binary / octal / hex form";
        // SAFETY: valid message.
        unsafe { crate::rok_panic(m.as_ptr(), m.len()) }
    }
    let neg = v.is_sign_negative() && !v.is_nan();
    let prec = spec.precision.map_or(-1, |p| p as i64);
    let how = Body {
        text: !v.is_finite(),
        ..Body::default()
    };
    let body = |w: &mut W| float_write(w, v.abs(), is_f32, spec.ty.into(), prec);
    number(&mut w, &spec, neg, b"", body, how);
    w.done()
}

/// Pad what was written since `start` per the spec: as text (cut to
/// `precision` chars first) when `numeric` is 0, else as a number whose
/// digits begin at `mid`.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_pad(
    h: RokStr,
    flags: u64,
    counts: u64,
    start: usize,
    mid: usize,
    numeric: u32,
) -> RokStr {
    let mut w = W::of(h);
    let spec = unpack(flags, counts);
    if numeric == 0 {
        cut(&mut w, &spec, start);
    }
    pad(&mut w, &spec, start, mid, numeric != 0);
    w.done()
}

/// The two spec words (`fmt_spec::pack`) of `spec`, parsed at run time
/// (a dynamic spec) into `out`; panics when malformed, or when
/// `text_only` and it has a number's type letter.
///
/// # Safety
/// `out` is a live `GcBuf<u64>` of at least 2 elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_fmt_pack(spec: RokStr, text_only: u32, out: *mut u8) {
    let src = text(&spec);
    let parsed = parse(src).unwrap_or_else(|why| fail(src, why));
    if text_only != 0 && !matches!(parsed.ty, 0 | b's' | b'd' | b'g' | b'?') {
        fail(src, "the type letter needs a number");
    }
    let (flags, counts) = pack(&parsed);
    // SAFETY: caller contract; elements start after the header.
    unsafe {
        let words = out.add(HEADER_SIZE).cast::<u64>();
        words.write(flags);
        words.add(1).write(counts);
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::fmt_spec::FmtSpec;

    const fn s(b: &'static str) -> RokStr {
        RokStr {
            ptr: b.as_ptr(),
            len: b.len(),
        }
    }

    // Allocates: called from the GC test (single mutator).
    pub fn fmt_ops() {
        let f = |v: f64, ty: u8, prec: i64| text(&rok_fmt_float(v, 0, ty.into(), prec)).to_owned();
        assert_eq!(f(0.1 + 0.2, 0, -1), "0.30000000000000004");
        assert_eq!(f(1.0, 0, -1), "1");
        assert_eq!(f(1e21, 0, -1), "1000000000000000000000");
        assert_eq!(f(f64::NAN, 0, -1), "NaN");
        assert_eq!(f(-f64::INFINITY, b'E', -1), "-inf");
        assert_eq!(f(core::f64::consts::PI, 0, 2), "3.14");
        assert_eq!(f(12345.678, b'e', -1), "1.2345678e4");
        assert_eq!(f(12345.678, b'e', 3), "1.235e4");
        assert_eq!(f(12345.678, b'E', 2), "1.23E4");
        assert_eq!(f(1.5, b'f', -1), "1.500000");
        let f32_text = |v: f32, ty: u8| text(&rok_fmt_float(v.into(), 1, ty.into(), -1)).to_owned();
        assert_eq!(f32_text(0.1, 0), "0.1");
        assert_eq!(f32_text(0.1, b'e'), "1e-1");
        let e = |d: &'static str, p: i64| {
            let mut w = W::of(rok_fmt_new(1));
            exp_write(&mut w, d.as_bytes(), p, false);
            text(&rok_fmt_finish(w.done())).to_owned()
        };
        assert_eq!(e("42", -1), "4.2e1");
        assert_eq!(e("1000", -1), "1e3");
        assert_eq!(e("12345", 2), "1.23e4");
        assert_eq!(e("99999", 1), "1.0e5");
        assert_eq!(
            parse("x>"),
            Ok(FmtSpec {
                fill: 'x',
                align: b'>',
                sign: 0,
                alt: false,
                zero: false,
                width: None,
                precision: None,
                ty: 0
            })
        );
        assert!(parse(".").is_err());
        assert!(parse("5q").is_err());
        assert!(parse("1.2.3").is_err());
        let sp = parse("*^+#012.3x").unwrap();
        let (fl, co) = pack(&sp);
        assert_eq!(unpack(fl, co), sp);
    }

    // Allocates: called from the GC test (single mutator).
    pub fn exp_rounding() {
        let e = |d: &'static str, p: i64| {
            let mut w = W::of(rok_fmt_new(1));
            exp_write(&mut w, d.as_bytes(), p, false);
            text(&rok_fmt_finish(w.done())).to_owned()
        };
        assert_eq!(e("19", 0), "2e1");
        assert_eq!(e("1295", 2), "1.30e3");
        assert_eq!(e("5", 3), "5.000e0");
        // No precision cap.
        assert_eq!(e("12", 600).len(), 2 + 600 + 2);
        assert_eq!(text(&rok_fmt_float(0.1, 0, 0, 700)).len(), 2 + 700);
    }

    // Allocates: called from the GC test (single mutator).
    pub fn formatter_ops() {
        // The formatter: `spec` applied to what `write` adds to "<".
        let fmt = |spec: &str, write: &dyn Fn(RokStr, u64, u64) -> RokStr| {
            let (fl, co) = pack(&parse(spec).unwrap());
            let t = rok_fmt_str(rok_fmt_new(1), s("<"));
            text(&rok_fmt_finish(write(t, fl, co))).to_owned()
        };
        let int = |v: i64, signed: u32, bits: u32| {
            move |t: RokStr, fl: u64, co: u64| rok_fmt_int(t, fl, co, v, signed, bits)
        };
        assert_eq!(fmt("", &int(-120, 1, 64)), "<-120");
        assert_eq!(fmt("", &int(i64::MIN, 1, 64)), "<-9223372036854775808");
        assert_eq!(fmt("", &int(-1, 0, 64)), "<18446744073709551615");
        assert_eq!(fmt("x", &int(-1, 1, 8)), "<ff");
        assert_eq!(fmt("x", &int(-255, 1, 0)), "<-ff");
        assert_eq!(fmt("#X", &int(0xCAFE, 1, 32)), "<0xCAFE");
        assert_eq!(fmt("08b", &int(42, 1, 32)), "<00101010");
        assert_eq!(fmt("=+5", &int(42, 1, 32)), "<+  42");
        assert_eq!(fmt("*^7", &int(42, 1, 32)), "<**42***");
        assert_eq!(fmt("06", &int(-42, 1, 32)), "<-00042");
        assert_eq!(fmt("e", &int(42, 1, 32)), "<4.2e1");
        assert_eq!(fmt(".2f", &int(3, 1, 32)), "<3.00");
        let float = |v: f64| move |t: RokStr, fl: u64, co: u64| rok_fmt_f64(t, fl, co, v, 0);
        assert_eq!(fmt("10.4", &float(core::f64::consts::PI)), "<    3.1416");
        assert_eq!(fmt("08", &float(f64::INFINITY)), "<inf     ");
        let pad = |t: RokStr, fl: u64, co: u64| {
            let start = rok_fmt_len(t);
            let t = rok_fmt_str(t, s("héllo world"));
            rok_fmt_pad(t, fl, co, start, start, 0)
        };
        assert_eq!(fmt("", &pad), "<héllo world");
        assert_eq!(fmt("_>8.4", &pad), "<____héll");
        let esc = |t: RokStr, _: u64, _: u64| {
            rok_fmt_escaped(t, s("a\"'\n\u{1}\u{85}\u{202E}é"), u32::from('"'))
        };
        assert_eq!(fmt("", &esc), "<\"a\\\"'\\n\\u{1}\\u{85}\\u{202e}é\"");
        // Grows past its first allocation; the text stays NUL-terminated.
        let long = |t: RokStr, _: u64, _: u64| (0..40).fold(t, |t, _| rok_fmt_str(t, s("ab")));
        assert_eq!(fmt("", &long).len(), 81);
        let done = rok_fmt_finish(rok_fmt_str(rok_fmt_new(1), s("xyz")));
        // SAFETY: one byte past `len` is the terminator.
        assert_eq!(unsafe { *done.ptr.add(done.len) }, 0);
    }
}

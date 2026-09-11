//! f-string support (refs-lang 1.7.3, stdlib 2.10): spec parsing and
//! number digits. Padding and per-type dispatch live in `core::fmt`.

// `GcBuf` elements start 8-aligned after the header.
#![allow(clippy::cast_ptr_alignment)]

use core::fmt::Write as _;
use core::ptr;

use rokr_common::object_header::HEADER_SIZE;

use crate::fmt_spec::parse;
use crate::str::{RokStr, build, text};

/// Fits any `f64` at [`MAX_PREC`] places.
struct Buf {
    b: [u8; 1100],
    n: usize,
}

/// Larger precisions are clamped.
const MAX_PREC: usize = 500;

impl Buf {
    const fn new() -> Self {
        Self { b: [0; 1100], n: 0 }
    }
    fn bytes(&self) -> &[u8] {
        &self.b[..self.n]
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
    let opt = |v: Option<usize>| v.map_or(-1, |v| v.min(MAX_PREC) as i64);
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
#[allow(clippy::cast_possible_truncation)] // `f32` values widened by the caller
pub extern "C" fn rok_fmt_float(v: f64, is_f32: u32, ty: u32, prec: i64) -> RokStr {
    let mut out = Buf::new();
    let p = usize::try_from(prec).ok().map(|p| p.min(MAX_PREC));
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
        out.b[..out.n]
            .iter_mut()
            .filter(|c| **c == b'e')
            .for_each(|c| *c = b'E');
    }
    build(&[out.bytes()])
}

/// The decimal digits `digits` of an integer in `1.5e3` form: shortest
/// exact without a precision (`prec < 0`), else rounded half up to
/// `prec` fraction digits.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_exp_digits(digits: RokStr, prec: i64, upper: u32) -> RokStr {
    let d = digits.bytes();
    if d.is_empty() {
        return build(&[b"0e0"]);
    }
    let mut exp = d.len() - 1;
    let mut m = [b'0'; MAX_PREC + 2];
    let k = match usize::try_from(prec) {
        Err(_) => d.iter().rposition(|&c| c != b'0').map_or(1, |i| i + 1),
        Ok(p) => p.min(MAX_PREC) + 1,
    };
    let take = k.min(d.len());
    m[..take].copy_from_slice(&d[..take]);
    if d.len() > k && d[k] >= b'5' {
        let mut i = k;
        loop {
            if i == 0 {
                // 9.99 rounds to 10.0: one more exponent.
                m[0] = b'1';
                m[1..k].fill(b'0');
                exp += 1;
                break;
            }
            i -= 1;
            if m[i] == b'9' {
                m[i] = b'0';
            } else {
                m[i] += 1;
                break;
            }
        }
    }
    let mut out = Buf::new();
    let _ = out.write_char(char::from(m[0]));
    if k > 1 {
        let _ = out.write_char('.');
        let _ = out.write_str(core::str::from_utf8(&m[1..k]).unwrap_or(""));
    }
    let _ = write!(out, "{}{exp}", if upper != 0 { 'E' } else { 'e' });
    build(&[out.bytes()])
}

/// Copy `src` into the fresh string `dst` at byte `off`: the f-string
/// join fills one allocation.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_str_write_at(dst: RokStr, off: usize, src: RokStr) {
    if src.len > 0 && off + src.len <= dst.len {
        // SAFETY: in bounds of `dst`, a fresh string the caller owns.
        unsafe { ptr::copy_nonoverlapping(src.ptr, dst.ptr.cast_mut().add(off), src.len) };
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
        let e = |d: &'static str, p: i64| text(&rok_fmt_exp_digits(s(d), p, 0)).to_owned();
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
    }
}

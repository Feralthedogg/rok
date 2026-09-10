//! f-string formatting (refs-lang 1.7.3, stdlib 2.10): one value and its
//! spec text to a fresh `str`. The compiler checks static specs and picks
//! the entry by the value's type; a dynamic (`${..}`) spec that does not
//! parse, or asks for a type letter the value can't take, panics here
//! ("형식화 시점 에러").

use core::fmt::Write as _;
use core::ptr;

use crate::fmt_spec::{FmtSpec, parse};
use crate::str::{RokStr, alloc_str, rok_str_from_f64, text};

/// Stack buffer for one formatted number. ponytail: fixed size; huge
/// precisions are clamped to [`MAX_PREC`].
struct Buf {
    b: [u8; 1100],
    n: usize,
}

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

fn spec_of(s: &RokStr) -> FmtSpec {
    let t = text(s);
    parse(t).unwrap_or_else(|why| fail(t, why))
}

fn fail(spec: &str, why: &str) -> ! {
    let mut m = Buf::new();
    let _ = write!(m, "invalid format spec `{spec}`: {why}");
    // SAFETY: valid buffer.
    unsafe { crate::rok_panic(m.b.as_ptr(), m.n) }
}

/// `sign`, `prefix` and `body` padded per `spec` into a new string.
/// Numbers take the `0` flag (zeros after sign and prefix) and `=`.
fn assemble(spec: &FmtSpec, sign: &[u8], prefix: &[u8], body: &[u8], numeric: bool) -> RokStr {
    let chars = body.iter().filter(|&&c| (c & 0xC0) != 0x80).count();
    let n = sign.len() + prefix.len() + chars;
    let pad = spec.width.unwrap_or(0).saturating_sub(n);
    let mut fb = [0u8; 4];
    let (fill, align): (&[u8], u8) = if numeric && spec.zero && spec.align == 0 {
        (b"0", b'=')
    } else {
        (spec.fill.encode_utf8(&mut fb).as_bytes(), spec.align)
    };
    let (left, mid, right) = match align {
        b'=' if numeric => (0, pad, 0),
        b'>' | b'=' => (pad, 0, 0),
        b'^' => (pad / 2, 0, pad - pad / 2),
        // No align: numbers right, everything else left (spec 2.10.8).
        0 if numeric => (pad, 0, 0),
        _ => (0, 0, pad),
    };
    let total = sign.len() + prefix.len() + body.len() + pad * fill.len();
    let p = alloc_str(total);
    let mut at = 0;
    let mut put = |bytes: &[u8]| {
        // SAFETY: exactly `total` bytes are written.
        unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(at), bytes.len()) };
        at += bytes.len();
    };
    (0..left).for_each(|_| put(fill));
    put(sign);
    put(prefix);
    (0..mid).for_each(|_| put(fill));
    put(body);
    (0..right).for_each(|_| put(fill));
    RokStr { ptr: p, len: total }
}

const fn sign_of(spec: &FmtSpec, negative: bool) -> &'static [u8] {
    match (negative, spec.sign) {
        (true, _) => b"-",
        (false, b'+') => b"+",
        (false, b' ') => b" ",
        _ => b"",
    }
}

/// Mantissa / exponent form of the decimal digits `d` (no sign): `1.5e3`.
/// Without a precision the shortest exact form; with one, rounded half
/// up to `prec` fraction digits.
fn exp_digits(d: &[u8], prec: Option<usize>, upper: bool, out: &mut Buf) {
    let mut exp = d.len() - 1;
    let mut m = [b'0'; MAX_PREC + 2];
    let k = match prec {
        None => d.iter().rposition(|&c| c != b'0').map_or(1, |i| i + 1),
        Some(p) => p.min(MAX_PREC) + 1,
    };
    let take = k.min(d.len());
    m[..take].copy_from_slice(&d[..take]);
    if d.len() > k && d[k] >= b'5' {
        let mut i = k;
        loop {
            if i == 0 {
                // 9.99 → 10.0: one more exponent, the digits shift.
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
    let _ = out.write_char(char::from(m[0]));
    if k > 1 {
        let _ = out.write_char('.');
        // SAFETY-free: ASCII digits.
        let _ = out.write_str(core::str::from_utf8(&m[1..k]).unwrap_or(""));
    }
    let _ = write!(out, "{}{exp}", if upper { 'E' } else { 'e' });
}

/// An integer: `v` is the value's bits sign- (`kind & 0x100`) or
/// zero-extended to 64; `kind & 0xFF` its width in bits.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_int(v: u64, kind: u32, spec: RokStr) -> RokStr {
    let s = spec_of(&spec);
    let signed = kind & 0x100 != 0;
    let bits = kind & 0xFF;
    #[allow(clippy::cast_possible_wrap)] // sign-extended bits
    let neg = signed && (v as i64) < 0;
    let mag = if neg { (v as i64).unsigned_abs() } else { v };
    let mut out = Buf::new();
    match s.ty {
        b'b' | b'o' | b'x' | b'X' => {
            // Two's complement at the type's own width.
            let bits_v = if bits >= 64 {
                v
            } else {
                v & ((1u64 << bits) - 1)
            };
            let _ = match s.ty {
                b'b' => write!(out, "{bits_v:b}"),
                b'o' => write!(out, "{bits_v:o}"),
                b'x' => write!(out, "{bits_v:x}"),
                _ => write!(out, "{bits_v:X}"),
            };
            let prefix: &[u8] = match (s.alt, s.ty) {
                (false, _) => b"",
                (true, b'b') => b"0b",
                (true, b'o') => b"0o",
                _ => b"0x",
            };
            return assemble(&s, sign_of(&s, false), prefix, out.bytes(), true);
        }
        b'e' | b'E' => {
            let mut d = Buf::new();
            let _ = write!(d, "{mag}");
            exp_digits(d.bytes(), s.precision, s.ty == b'E', &mut out);
        }
        b'f' => {
            #[allow(clippy::cast_precision_loss)] // `{n:f}` is a float view
            let f = if neg { -(mag as f64) } else { mag as f64 };
            return float(f, false, &s);
        }
        _ => {
            let _ = write!(out, "{mag}");
        }
    }
    assemble(&s, sign_of(&s, neg), b"", out.bytes(), true)
}

/// A float (`is_f32` != 0: an `f32` widened, formatted as `f32`).
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_float(v: f64, is_f32: u32, spec: RokStr) -> RokStr {
    let s = spec_of(&spec);
    if matches!(s.ty, b'b' | b'o' | b'x' | b'X') {
        fail(text(&spec), "a float has no binary / octal / hex form");
    }
    float(v, is_f32 != 0, &s)
}

#[allow(clippy::cast_possible_truncation)] // `f32` values widened by the caller
fn float(value: f64, is_f32: bool, spec: &FmtSpec) -> RokStr {
    let mut out = Buf::new();
    let neg = value.is_sign_negative() && !value.is_nan();
    let mag = value.abs();
    let prec = spec.precision.map(|digits| digits.min(MAX_PREC));
    let _ = match (spec.ty, prec) {
        (b'e' | b'E', digits) => {
            let written = match (digits, is_f32) {
                (Some(d), true) => write!(out, "{:.*e}", d, mag as f32),
                (Some(d), false) => write!(out, "{mag:.d$e}"),
                (None, true) => write!(out, "{:e}", mag as f32),
                (None, false) => write!(out, "{mag:e}"),
            };
            if spec.ty == b'E' {
                out.b[..out.n]
                    .iter_mut()
                    .for_each(|c| *c = c.to_ascii_uppercase());
            }
            written
        }
        (b'f', digits) => write!(out, "{mag:.*}", digits.unwrap_or(6)),
        (_, Some(d)) => write!(out, "{mag:.d$}"),
        // Display (`%g`, as `f64::display`).
        _ => out.write_str(text(&rok_str_from_f64(mag, -1))),
    };
    assemble(spec, sign_of(spec, neg), b"", out.bytes(), mag.is_finite())
}

/// The parts of `spec` a library formatter needs (`int` / `float`):
/// the type letter (bits 0..8, 0 if none), `#` (bit 8), the precision
/// plus one (bits 16.., 0 if none). Panics on a bad spec.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_spec_info(spec: RokStr) -> u64 {
    let s = spec_of(&spec);
    let prec = s.precision.map_or(0, |p| p.min(MAX_PREC) as u64 + 1);
    u64::from(s.ty) | (u64::from(s.alt) << 8) | (prec << 16)
}

/// `1.5e3` form of the decimal digits `digits` (an integer; `prec < 0`:
/// shortest exact), as `{n:e}` prints an integer.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_exp_digits(digits: RokStr, prec: i64, upper: u32) -> RokStr {
    let mut out = Buf::new();
    exp_digits(
        text(&digits).as_bytes(),
        usize::try_from(prec).ok(),
        upper != 0,
        &mut out,
    );
    build_str(out.bytes())
}

/// A number the library already rendered (`body`, no sign; `prefix`
/// like `0x`) padded per `spec` with the sign (`neg != 0`) — the `int`
/// / `float` f-string hooks.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_num(neg: u32, prefix: RokStr, body: RokStr, spec: RokStr) -> RokStr {
    let s = spec_of(&spec);
    assemble(
        &s,
        sign_of(&s, neg != 0),
        prefix.bytes(),
        body.bytes(),
        true,
    )
}

fn build_str(b: &[u8]) -> RokStr {
    let p = alloc_str(b.len());
    // SAFETY: a fresh allocation of `b.len()` bytes.
    unsafe { ptr::copy_nonoverlapping(b.as_ptr(), p, b.len()) };
    RokStr {
        ptr: p,
        len: b.len(),
    }
}

/// Any other value, already rendered: `disp` (Display) or, for `?`, `dbg`
/// (Debug). A precision keeps that many chars.
#[unsafe(no_mangle)]
pub extern "C" fn rok_fmt_str(disp: RokStr, dbg: RokStr, spec: RokStr) -> RokStr {
    let s = spec_of(&spec);
    if !matches!(s.ty, 0 | b's' | b'd' | b'g' | b'?') {
        fail(text(&spec), "the type letter needs a number");
    }
    let v = if s.ty == b'?' { &dbg } else { &disp };
    let t = text(v);
    let body = match s.precision {
        Some(p) => t.char_indices().nth(p).map_or(t, |(i, _)| &t[..i]),
        None => t,
    };
    assemble(&s, b"", b"", body.as_bytes(), false)
}

/// Copy `src` into the fresh string `dst` at byte `off` (the f-string
/// join fills one allocation).
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

    const fn s(b: &'static str) -> RokStr {
        RokStr {
            ptr: b.as_ptr(),
            len: b.len(),
        }
    }

    // Allocates: called from the GC test (single mutator).
    #[allow(clippy::cognitive_complexity)] // a flat list of cases
    pub fn fmt_ops() {
        let i = |v: i64, bits: u32, sp| {
            let r = rok_fmt_int(v as u64, bits | 0x100, s(sp));
            text(&r).to_owned()
        };
        let u = |v: u64, bits: u32, sp| text(&rok_fmt_int(v, bits, s(sp))).to_owned();
        assert_eq!(i(42, 32, "5"), "   42");
        assert_eq!(i(42, 32, "<5"), "42   ");
        assert_eq!(i(42, 32, ">5"), "   42");
        assert_eq!(i(-42, 32, "05"), "-0042");
        assert_eq!(i(42, 32, "+"), "+42");
        assert_eq!(i(42, 32, "=+6"), "+   42");
        assert_eq!(i(42, 32, "*^7"), "**42***");
        assert_eq!(i(-1, 8, "x"), "ff");
        assert_eq!(i(-1, 32, "#X"), "0xFFFFFFFF");
        assert_eq!(u(0xCAFE, 32, "#b"), "0b1100101011111110");
        assert_eq!(i(42, 32, "08b"), "00101010");
        assert_eq!(i(42, 32, "#010x"), "0x0000002a");
        assert_eq!(i(42, 32, "e"), "4.2e1");
        assert_eq!(i(1000, 32, "e"), "1e3");
        assert_eq!(i(12345, 32, ".2e"), "1.23e4");
        assert_eq!(i(99999, 32, ".1E"), "1.0E5");
        assert_eq!(i(5, 32, ".2f"), "5.00");
        let f = |v: f64, sp| text(&rok_fmt_float(v, 0, s(sp))).to_owned();
        assert_eq!(f(core::f64::consts::PI, ".2"), "3.14");
        assert_eq!(f(core::f64::consts::PI, ">10.4"), "    3.1416");
        assert_eq!(f(12345.678, "e"), "1.2345678e4");
        assert_eq!(f(12345.678, ".3e"), "1.235e4");
        assert_eq!(f(12345.678, ".2E"), "1.23E4");
        assert_eq!(f(-1.5, "08.2"), "-0001.50");
        assert_eq!(f(1.5, "+"), "+1.5");
        assert_eq!(f(0.1, ""), "0.1");
        assert_eq!(text(&rok_fmt_float(0.1f32.into(), 1, s("e"))), "1e-1");
        let st = |v, sp| text(&rok_fmt_str(s(v), s("\"dbg\""), s(sp))).to_owned();
        assert_eq!(st("hello world", ".5"), "hello");
        assert_eq!(st("ab", "^6"), "  ab  ");
        assert_eq!(st("한", "-<3"), "한--");
        assert_eq!(st("x", "?"), "\"dbg\"");
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

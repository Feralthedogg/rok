//! WTF-8 (UTF-8 plus encoded lone surrogates) and UTF-16, and a small
//! `malloc` buffer: how Windows text crosses into rok strings. Plain
//! code, built everywhere so its tests run on any host.

use core::mem::size_of;
use core::ptr;

/// Code points of WTF-8 bytes; an invalid byte is U+FFFD. Encoded
/// surrogates come back as themselves.
pub struct Decoder<'a> {
    pub s: &'a [u8],
    pub i: usize,
}

impl Iterator for Decoder<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        let s = self.s;
        let b0 = *s.get(self.i)?;
        let (len, init, min) = match b0 {
            0..0x80 => {
                self.i += 1;
                return Some(u32::from(b0));
            }
            0xC2..0xE0 => (2, u32::from(b0 & 0x1F), 0x80),
            0xE0..0xF0 => (3, u32::from(b0 & 0x0F), 0x800),
            0xF0..0xF5 => (4, u32::from(b0 & 0x07), 0x10000),
            _ => {
                self.i += 1;
                return Some(0xFFFD);
            }
        };
        let mut c = init;
        for k in 1..len {
            match s.get(self.i + k) {
                Some(&b) if b & 0xC0 == 0x80 => c = (c << 6) | u32::from(b & 0x3F),
                _ => {
                    self.i += k;
                    return Some(0xFFFD);
                }
            }
        }
        self.i += len;
        Some(if c < min || c > 0x10FFFF { 0xFFFD } else { c })
    }
}

/// The length of the incomplete sequence `s` ends with (a lead byte
/// and fewer continuation bytes than it needs; 0: none).
pub fn incomplete_tail(s: &[u8]) -> usize {
    for k in 1..=s.len().min(3) {
        let b = s[s.len() - k];
        if b & 0xC0 != 0x80 {
            let need = match b {
                0xC2..0xE0 => 2,
                0xE0..0xF0 => 3,
                0xF0..0xF5 => 4,
                _ => 0,
            };
            return if need > k { k } else { 0 };
        }
    }
    0
}

/// Code points of UTF-16 units; a lone surrogate comes back as itself.
pub struct Utf16<'a> {
    pub s: &'a [u16],
    pub i: usize,
}

impl Iterator for Utf16<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        let u = u32::from(*self.s.get(self.i)?);
        self.i += 1;
        if (0xD800..0xDC00).contains(&u) {
            if let Some(&lo) = self.s.get(self.i) {
                let lo = u32::from(lo);
                if (0xDC00..0xE000).contains(&lo) {
                    self.i += 1;
                    return Some(0x10000 + ((u - 0xD800) << 10) + (lo - 0xDC00));
                }
            }
        }
        Some(u)
    }
}

/// `c` as UTF-16 into `out` (room for 2): the unit count.
pub fn encode_utf16(c: u32, out: &mut [u16]) -> usize {
    if c >= 0x10000 {
        let c = c - 0x10000;
        out[0] = 0xD800 | (c >> 10) as u16;
        out[1] = 0xDC00 | (c & 0x3FF) as u16;
        2
    } else {
        out[0] = c as u16;
        1
    }
}

/// `c` (a surrogate allowed) as WTF-8 into `out`: the byte count.
pub fn encode_wtf8(c: u32, out: &mut [u8; 4]) -> usize {
    match c {
        0..0x80 => {
            out[0] = c as u8;
            1
        }
        0x80..0x800 => {
            out[0] = 0xC0 | (c >> 6) as u8;
            out[1] = 0x80 | (c & 0x3F) as u8;
            2
        }
        0x800..0x10000 => {
            out[0] = 0xE0 | (c >> 12) as u8;
            out[1] = 0x80 | ((c >> 6) & 0x3F) as u8;
            out[2] = 0x80 | (c & 0x3F) as u8;
            3
        }
        _ => {
            out[0] = 0xF0 | (c >> 18) as u8;
            out[1] = 0x80 | ((c >> 12) & 0x3F) as u8;
            out[2] = 0x80 | ((c >> 6) & 0x3F) as u8;
            out[3] = 0x80 | (c & 0x3F) as u8;
            4
        }
    }
}

/// A growable `malloc` buffer (the runtime has no allocator crate).
pub struct MBuf<T: Copy> {
    ptr: *mut T,
    len: usize,
    cap: usize,
}

impl<T: Copy> MBuf<T> {
    pub const fn new() -> Self {
        Self {
            ptr: ptr::null_mut(),
            len: 0,
            cap: 0,
        }
    }

    /// Room for at least `cap` elements in all.
    pub fn reserve(&mut self, cap: usize) {
        if cap <= self.cap {
            return;
        }
        let cap = cap.max(self.cap * 2).max(64);
        // SAFETY: grows our own block (or allocates the first).
        let p = unsafe { libc::realloc(self.ptr.cast(), cap * size_of::<T>()) }.cast::<T>();
        if p.is_null() {
            crate::oom();
        }
        self.ptr = p;
        self.cap = cap;
    }

    /// # Safety
    /// The first `len` elements (within the reserved room) must be
    /// initialized.
    pub const unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    pub fn push(&mut self, v: T) {
        self.reserve(self.len + 1);
        // SAFETY: `len < cap`.
        unsafe { self.ptr.add(self.len).write(v) };
        self.len += 1;
    }

    pub fn extend(&mut self, vs: &[T]) {
        for v in vs {
            self.push(*v);
        }
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn truncate(&mut self, len: usize) {
        self.len = self.len.min(len);
    }

    pub const fn as_slice(&self) -> &[T] {
        if self.ptr.is_null() {
            return &[];
        }
        // SAFETY: `len` initialized elements.
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        if self.ptr.is_null() {
            return &mut [];
        }
        // SAFETY: `len` initialized elements, borrowed exclusively.
        unsafe { core::slice::from_raw_parts_mut(self.ptr, self.len) }
    }

    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr
    }
}

impl<T: Copy> Default for MBuf<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy> Drop for MBuf<T> {
    fn drop(&mut self) {
        // SAFETY: our own block (free(NULL) is a no-op).
        unsafe { libc::free(self.ptr.cast()) };
    }
}

/// A NUL-terminated UTF-16 string.
pub type Wide = MBuf<u16>;

impl Wide {
    /// The units with a NUL after them, for a `*const u16` argument.
    pub fn ptr(&mut self) -> *const u16 {
        self.push(0);
        self.len -= 1;
        self.ptr
    }
}

/// WTF-8 `s` as UTF-16.
pub fn wide(s: &[u8]) -> Wide {
    let mut w = Wide::new();
    push_wide(&mut w, s);
    w
}

/// Append WTF-8 `s` to `w` as UTF-16.
pub fn push_wide(w: &mut Wide, s: &[u8]) {
    for c in (Decoder { s, i: 0 }) {
        let mut u = [0u16; 2];
        let n = encode_utf16(c, &mut u);
        w.extend(&u[..n]);
    }
}

/// UTF-16 `w` as WTF-8.
pub fn narrow(w: &[u16]) -> MBuf<u8> {
    let mut out = MBuf::new();
    for c in (Utf16 { s: w, i: 0 }) {
        let mut b = [0u8; 4];
        let n = encode_wtf8(c, &mut b);
        out.extend(&b[..n]);
    }
    out
}

/// The units of the NUL-terminated `p`.
///
/// # Safety
/// `p` must be a NUL-terminated UTF-16 string that outlives the slice.
pub const unsafe fn wide_cstr<'a>(p: *const u16) -> &'a [u16] {
    let mut n = 0;
    // SAFETY: caller contract.
    unsafe {
        while *p.add(n) != 0 {
            n += 1;
        }
        core::slice::from_raw_parts(p, n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wtf8_round_trips_utf16() {
        // ASCII, 2/3/4-byte UTF-8, a lone high and a lone low surrogate.
        let units = [0x41, 0xE9, 0x20AC, 0xD83D, 0xDE00, 0xD800, 0x42, 0xDC00];
        let bytes = narrow(&units);
        assert_eq!(
            bytes.as_slice(),
            b"A\xC3\xA9\xE2\x82\xAC\xF0\x9F\x98\x80\xED\xA0\x80B\xED\xB0\x80"
        );
        assert_eq!(wide(bytes.as_slice()).as_slice(), units);
    }

    #[test]
    fn invalid_utf8_decodes_to_replacement() {
        let w = wide(b"a\xFFb\xC3");
        assert_eq!(w.as_slice(), [0x61, 0xFFFD, 0x62, 0xFFFD]);
        // An overlong encoding is not a character.
        assert_eq!(wide(b"\xC0\x80").as_slice(), [0xFFFD, 0xFFFD]);
    }

    #[test]
    fn incomplete_tail_is_a_cut_sequence() {
        assert_eq!(incomplete_tail(b""), 0);
        assert_eq!(incomplete_tail(b"ab"), 0);
        assert_eq!(incomplete_tail(b"a\xC3"), 1);
        assert_eq!(incomplete_tail(b"a\xC3\xA9"), 0);
        assert_eq!(incomplete_tail(b"\xE2\x82"), 2);
        assert_eq!(incomplete_tail(b"\xF0\x9F\x98"), 3);
        assert_eq!(incomplete_tail(b"\xF0\x9F\x98\x80"), 0);
        // Not a lead byte, or continuation bytes alone.
        assert_eq!(incomplete_tail(b"\xFF"), 0);
        assert_eq!(incomplete_tail(b"\x80\x80"), 0);
    }
}

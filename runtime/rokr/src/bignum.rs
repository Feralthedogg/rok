//! `int` limb kernels (`library/core/num/bigint.rok`): the quadratic
//! inner loops over `GcBuf<u32>` limbs (little-endian, base 2^32), which
//! run several times faster here than as rok loops. The library does
//! the rest (signs, normalization, Karatsuba, allocation). None of these
//! allocate, so no collection runs while they hold the buffers.

// Knuth's names (q, r, u, v, m, n) read better than long ones here.
#![allow(clippy::many_single_char_names)]
// `GcBuf` elements start 8-aligned after the header.
#![allow(clippy::cast_ptr_alignment)]

use core::slice;

use rokr_common::object_header::HEADER_SIZE;

/// The first `n` limbs of the `GcBuf<u32>` at `buf`.
///
/// # Safety
/// `buf` is a live `GcBuf<u32>` of at least `n` elements.
unsafe fn limbs<'a>(buf: *mut u8, n: usize) -> &'a mut [u32] {
    // SAFETY: caller contract; elements start after the header.
    unsafe { slice::from_raw_parts_mut(buf.add(HEADER_SIZE).cast::<u32>(), n) }
}

/// `r[0..an + bn] = a * b` (schoolbook). `r` is zeroed and distinct
/// from `a` / `b` (which may be the same buffer).
///
/// # Safety
/// Live `GcBuf<u32>`s of at least those lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_mul(r: *mut u8, a: *mut u8, an: usize, b: *mut u8, bn: usize) {
    // SAFETY: caller contract; `a` / `b` only read.
    let (a, b) = unsafe { (&*limbs(a, an), &*limbs(b, bn)) };
    // SAFETY: caller contract; `r` is its own buffer.
    let r = unsafe { limbs(r, an + bn) };
    // The shorter operand drives the outer loop.
    let (a, b) = if a.len() < b.len() { (a, b) } else { (b, a) };
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        let x = u64::from(x);
        let mut carry = 0u64;
        for (j, &y) in b.iter().enumerate() {
            // (2^32 - 1)^2 + 2 (2^32 - 1) < 2^64.
            let t = x * u64::from(y) + u64::from(r[i + j]) + carry;
            r[i + j] = t as u32;
            carry = t >> 32;
        }
        r[i + b.len()] = carry as u32;
    }
}

/// `q[0..n] = a / v`; the remainder.
///
/// # Safety
/// Live `GcBuf<u32>`s of at least `n` elements; `v != 0`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_divmod_small(q: *mut u8, a: *mut u8, n: usize, v: u32) -> u32 {
    // SAFETY: caller contract (`q` may be `a`: each limb is read first).
    let (q, a) = unsafe { (limbs(q, n), limbs(a, n)) };
    let d = u64::from(v);
    let mut rem = 0u64;
    for i in (0..n).rev() {
        let cur = (rem << 32) | u64::from(a[i]);
        q[i] = (cur / d) as u32;
        rem = cur % d;
    }
    rem as u32
}

/// Knuth TAOCP 4.3.1 algorithm D (Hacker's Delight `divmnu`) on
/// normalized operands: `un` (`m + n + 1` limbs) / `vn` (`n >= 2` limbs,
/// top bit set) → quotient `q[0..=m]`; the remainder is left in
/// `un[0..n]` (still shifted).
///
/// # Safety
/// Live, distinct `GcBuf<u32>`s of those lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_divmod(q: *mut u8, un: *mut u8, vn: *mut u8, m: usize, n: usize) {
    // SAFETY: caller contract.
    let (q, un, vn) = unsafe { (limbs(q, m + 1), limbs(un, m + n + 1), limbs(vn, n)) };
    let base = 1u64 << 32;
    let top = u64::from(vn[n - 1]);
    let next = u64::from(vn[n - 2]);
    for j in (0..=m).rev() {
        let num = (u64::from(un[j + n]) << 32) | u64::from(un[j + n - 1]);
        let mut qhat = num / top;
        let mut rhat = num % top;
        while qhat >= base || qhat * next > ((rhat << 32) | u64::from(un[j + n - 2])) {
            qhat -= 1;
            rhat += top;
            if rhat >= base {
                break;
            }
        }
        // un[j..=j+n] -= qhat * vn.
        let mut k = 0i64;
        for i in 0..n {
            let p = qhat * u64::from(vn[i]);
            let t = i64::from(un[i + j]) - k - (p & 0xFFFF_FFFF) as i64;
            un[i + j] = t as u32;
            k = (p >> 32) as i64 - (t >> 32);
        }
        let t = i64::from(un[j + n]) - k;
        un[j + n] = t as u32;
        if t < 0 {
            // `qhat` was one too big: add the divisor back.
            qhat -= 1;
            let mut c = 0u64;
            for i in 0..n {
                let s = u64::from(un[i + j]) + u64::from(vn[i]) + c;
                un[i + j] = s as u32;
                c = s >> 32;
            }
            un[j + n] = un[j + n].wrapping_add(c as u32);
        }
        q[j] = qhat as u32;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A heap buffer laid out like a `GcBuf<u32>` (header + limbs).
    fn buf(limbs: &[u32], len: usize) -> Vec<u64> {
        let mut v = vec![0u64; (HEADER_SIZE + 4 * len.max(limbs.len())).div_ceil(8) + 1];
        let p = v.as_mut_ptr().cast::<u8>();
        for (i, &l) in limbs.iter().enumerate() {
            // SAFETY: in bounds of `v`.
            unsafe { p.add(HEADER_SIZE).cast::<u32>().add(i).write(l) };
        }
        v
    }

    fn read(v: &mut [u64], n: usize) -> Vec<u32> {
        // SAFETY: `v` came from `buf` with room for `n` limbs.
        unsafe { limbs(v.as_mut_ptr().cast(), n).to_vec() }
    }

    #[test]
    fn mul_divmod_round_trip() {
        let a = [0xFFFF_FFFFu32, 0x9ABC_DEF0];
        let b = [0x8000_0001u32, 0xFFFF_FFFF];
        let (mut ab, mut bb, mut r) = (buf(&a, 2), buf(&b, 2), buf(&[], 4));
        // SAFETY: test buffers sized above.
        unsafe {
            rok_nat_mul(
                r.as_mut_ptr().cast(),
                ab.as_mut_ptr().cast(),
                2,
                bb.as_mut_ptr().cast(),
                2,
            );
        }
        let prod = read(&mut r, 4);
        let want = num(&a) * num(&b);
        assert_eq!(num(&prod), want);
        // prod / b (b is normalized: top bit set) == a, remainder 0.
        let mut un = buf(&prod, 5);
        let mut q = buf(&[], 3);
        // SAFETY: as above.
        unsafe {
            rok_nat_divmod(
                q.as_mut_ptr().cast(),
                un.as_mut_ptr().cast(),
                bb.as_mut_ptr().cast(),
                2,
                2,
            );
        }
        assert_eq!(num(&read(&mut q, 3)), num(&a));
        assert_eq!(num(&read(&mut un, 2)), 0);
        let mut sq = buf(&[], 2);
        // SAFETY: as above.
        let rem =
            unsafe { rok_nat_divmod_small(sq.as_mut_ptr().cast(), ab.as_mut_ptr().cast(), 2, 10) };
        assert_eq!(num(&read(&mut sq, 2)) * 10 + u128::from(rem), num(&a));
    }

    fn num(l: &[u32]) -> u128 {
        l.iter()
            .rev()
            .fold(0u128, |acc, &x| (acc << 32) | u128::from(x))
    }
}

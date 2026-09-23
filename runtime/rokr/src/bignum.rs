//! `int` limb kernels (`library/core/src/num/bigint.rok`) over
//! `GcBuf<u32>` limbs (little-endian, base 2^32), computed on machine
//! words: multiplication (schoolbook, Karatsuba, Toom-3, three-prime
//! NTT, squaring variants, products by an operand transformed once),
//! Knuth D division, single-limb division, Lehmer gcd, add / sub /
//! shifts and the base case of decimal output. The library
//! does the rest (signs, recursive division, radix conversion,
//! allocation). None of these allocate, so no collection runs while
//! they hold the buffers: scratch space comes from the caller.

// Knuth's names (q, r, u, v, m, n) read better than long ones here.
#![allow(clippy::many_single_char_names)]
// `GcBuf` elements start 8-aligned after the header.
#![allow(clippy::cast_ptr_alignment)]

use core::slice;

use rokr_common::object_header::HEADER_SIZE;

// Multiplication runs on machine-word limbs: the `u32` operands are
// packed into `L`s in the scratch buffer and the product unpacked.
#[cfg(target_pointer_width = "64")]
type L = u64;
#[cfg(target_pointer_width = "64")]
type W = u128;
#[cfg(not(target_pointer_width = "64"))]
type L = u32;
#[cfg(not(target_pointer_width = "64"))]
type W = u64;
// Signed `L` / `W` (Lehmer cofactors and their sums).
#[cfg(target_pointer_width = "64")]
type SL = i64;
#[cfg(target_pointer_width = "64")]
type SW = i128;
#[cfg(not(target_pointer_width = "64"))]
type SL = i32;
#[cfg(not(target_pointer_width = "64"))]
type SW = i64;

const LB: u32 = L::BITS;
/// `u32` limbs per `L`.
const PER: usize = (L::BITS / 32) as usize;

/// `L` limbs from which products split (Karatsuba), then Toom-3, then
/// go to the NTT, and the same for squares. Measured on aarch64 (64-bit
/// limbs) in cycles; the curves are flat around these.
const KARA: usize = 32;
const TOOM3: usize = 150;
const KARA_SQR: usize = 32;
const TOOM3_SQR: usize = 200;
const NTT: usize = 700;
const NTT_SQR: usize = 1000;
const NTT_LO: usize = if NTT < NTT_SQR { NTT } else { NTT_SQR };

// `scratch_bound` relies on these (see there).
const _: () = assert!(KARA >= 18 && KARA_SQR >= KARA && TOOM3 >= KARA && TOOM3_SQR >= KARA_SQR);

/// The first `n` limbs of the `GcBuf<u32>` at `buf`.
///
/// # Safety
/// `buf` is a live `GcBuf<u32>` of at least `n` elements.
unsafe fn limbs<'a>(buf: *mut u8, n: usize) -> &'a mut [u32] {
    // SAFETY: caller contract; elements start after the header.
    unsafe { slice::from_raw_parts_mut(buf.add(HEADER_SIZE).cast::<u32>(), n) }
}

/// `r += a` over `r` (`a.len() <= r.len()`); the carry out.
fn add_in(r: &mut [L], a: &[L]) -> bool {
    let (lo, hi) = r.split_at_mut(a.len());
    let mut c = 0 as W;
    for (x, &y) in lo.iter_mut().zip(a) {
        let s = *x as W + y as W + c;
        *x = s as L;
        c = s >> LB;
    }
    if c == 0 {
        return false;
    }
    for x in hi {
        *x = x.wrapping_add(1);
        if *x != 0 {
            return false;
        }
    }
    true
}

/// `r -= a` over `r` (`a.len() <= r.len()`); the borrow out.
fn sub_in(r: &mut [L], a: &[L]) -> bool {
    let (lo, hi) = r.split_at_mut(a.len());
    let mut b = false;
    for (x, &y) in lo.iter_mut().zip(a) {
        let (d, b1) = x.overflowing_sub(y);
        let (d, b2) = d.overflowing_sub(L::from(b));
        *x = d;
        b = b1 | b2;
    }
    if !b {
        return false;
    }
    for x in hi {
        let old = *x;
        *x = old.wrapping_sub(1);
        if old != 0 {
            return false;
        }
    }
    true
}

/// `r = -r` (two's complement over `r.len()` limbs).
fn neg_in(r: &mut [L]) {
    let mut c = true;
    for x in r {
        let (v, o) = (!*x).overflowing_add(L::from(c));
        *x = v;
        c = o;
    }
}

/// `r <<= 1`; the top bit must be clear.
fn shl1_in(r: &mut [L]) {
    let mut top = 0;
    for x in r {
        let v = *x;
        *x = (v << 1) | top;
        top = v >> (LB - 1);
    }
    debug_assert!(top == 0);
}

/// `r >>= 1`, arithmetic (two's complement).
fn sar1_in(r: &mut [L]) {
    let n = r.len();
    for i in 0..n - 1 {
        r[i] = (r[i] >> 1) | (r[i + 1] << (LB - 1));
    }
    r[n - 1] = (r[n - 1] >> 1) | (r[n - 1] & (1 << (LB - 1)));
}

/// `r /= 3`, exact (Hensel division, so two's complement values too).
fn divexact3_in(r: &mut [L]) {
    const INV3: L = L::MAX / 3 * 2 + 1;
    let mut c: L = 0;
    for x in r {
        let (s, b) = x.overflowing_sub(c);
        let q = s.wrapping_mul(INV3);
        *x = q;
        c = ((q as W * 3) >> LB) as L + L::from(b);
    }
}

/// `r[..a.len()] += a * x`; the carry limb.
fn addmul_1(r: &mut [L], a: &[L], x: L) -> L {
    let mut c: L = 0;
    for (y, &v) in r.iter_mut().zip(a) {
        // (2^b - 1)^2 + 2 (2^b - 1) < 2^2b.
        let t = v as W * x as W + *y as W + c as W;
        *y = t as L;
        c = (t >> LB) as L;
    }
    c
}

/// `dst = src` zero-extended.
fn copy_ext(dst: &mut [L], src: &[L]) {
    let (lo, hi) = dst.split_at_mut(src.len());
    lo.copy_from_slice(src);
    hi.fill(0);
}

/// `r[off..] += v` where the sum fits `r` (limbs of `v` past the end of
/// `r` are zero).
fn add_at(r: &mut [L], off: usize, v: &[L]) {
    let n = v.len().min(r.len() - off);
    debug_assert!(v[n..].iter().all(|&x| x == 0));
    let c = add_in(&mut r[off..], &v[..n]);
    debug_assert!(!c);
}

/// `r[..a.len()] = a * x`; the carry limb.
fn mul_1(r: &mut [L], a: &[L], x: L) -> L {
    let mut c: L = 0;
    for (y, &v) in r.iter_mut().zip(a) {
        let t = v as W * x as W + c as W;
        *y = t as L;
        c = (t >> LB) as L;
    }
    c
}

/// `r[..a.len()] += a * (x0 + x1 B)`: two rows per pass over `r`; the
/// limbs for `r[a.len()]` and `r[a.len() + 1]`.
fn addmul_2(r: &mut [L], a: &[L], x0: L, x1: L) -> (L, L) {
    // Pending carries into the next two positions.
    let (mut c0, mut c1): (L, L) = (0, 0);
    for (y, &v) in r.iter_mut().zip(a) {
        let t = *y as W + v as W * x0 as W + c0 as W;
        *y = t as L;
        let u = v as W * x1 as W + c1 as W + (t >> LB);
        c0 = u as L;
        c1 = (u >> LB) as L;
    }
    (c0, c1)
}

/// `r = a * b`, `a.len() >= b.len() >= 1`. Row `i` writes `r[i + n]`,
/// so nothing needs clearing first.
fn mul_basecase(r: &mut [L], a: &[L], b: &[L]) {
    let n = a.len();
    r[n] = mul_1(&mut r[..n], a, b[0]);
    let mut i = 1;
    while i + 1 < b.len() {
        (r[i + n], r[i + n + 1]) = addmul_2(&mut r[i..i + n], a, b[i], b[i + 1]);
        i += 2;
    }
    if i < b.len() {
        r[i + n] = addmul_1(&mut r[i..i + n], a, b[i]);
    }
}

/// `r = a^2`: the cross products once, then doubled plus the diagonal
/// in one pass.
fn sqr_basecase(r: &mut [L], a: &[L]) {
    let n = a.len();
    r[0] = 0;
    r[2 * n - 1] = 0;
    if n > 1 {
        r[n] = mul_1(&mut r[1..n], &a[1..], a[0]);
        for i in 1..n - 1 {
            r[i + n] = addmul_1(&mut r[2 * i + 1..i + n], &a[i + 1..], a[i]);
        }
    }
    let mut top: L = 0;
    let mut c = 0 as W;
    for (p, &x) in r.chunks_exact_mut(2).zip(a) {
        let (lo, hi) = (p[0], p[1]);
        let sq = x as W * x as W;
        let s0 = ((lo << 1) | top) as W + (sq as L) as W + c;
        let s1 = ((hi << 1) | (lo >> (LB - 1))) as W + (sq >> LB) + (s0 >> LB);
        top = hi >> (LB - 1);
        p[0] = s0 as L;
        p[1] = s1 as L;
        c = s1 >> LB;
    }
    debug_assert!(c == 0 && top == 0);
}

/// Scratch `L`s that `mul(r, a, b, t)` / `sqr` may use, for operands of
/// `n` and `m` limbs. By induction over the dispatch: a balanced step
/// on `N = max(n, m)` limbs uses at most `4k + 4` (Karatsuba, `k =
/// ceil(N/2)`) or `8k + 8` (Toom-3, `k = ceil(N/3)`) limbs plus its
/// recursion on `k + 1`, which stays within `6N + 40 bits(N)` once
/// `N >= 18`; an unbalanced one uses `2m` plus a balanced `m` product.
const fn scratch_bound(n: usize, m: usize) -> usize {
    let (lo, hi) = if n < m { (n, m) } else { (m, n) };
    if lo < KARA {
        return 0;
    }
    let bits = (usize::BITS - hi.leading_zeros()) as usize;
    // NTT steps anywhere below use at most this on top (the largest
    // transform bounds it for huge operands).
    let ntt = if hi < NTT_LO {
        0
    } else if ntt_len(hi, hi) <= NTT_MAX {
        ntt_scratch(hi, hi)
    } else {
        6 * NTT_MAX / PER
    };
    6 * hi + 40 * bits + ntt
}

/// `r = a * b` (`r.len() == a.len() + b.len()`), scratch `t`.
fn mul(r: &mut [L], a: &[L], b: &[L], t: &mut [L]) {
    let (a, b) = if a.len() < b.len() { (b, a) } else { (a, b) };
    let (n, m) = (a.len(), b.len());
    if m == 0 {
        r.fill(0);
    } else if m < KARA {
        mul_basecase(r, a, b);
    } else if m >= NTT && ntt_len(n, m) <= NTT_MAX {
        ntt_mul(r, a, b, t);
    } else if 2 * m <= n {
        // Unbalanced: `m`-limb pieces of `a`, each against all of `b`.
        r.fill(0);
        let (p, t) = t.split_at_mut(2 * m);
        for (i, piece) in a.chunks(m).enumerate() {
            let p = &mut p[..piece.len() + m];
            mul(p, piece, b, t);
            let c = add_in(&mut r[i * m..], p);
            debug_assert!(!c);
        }
    } else if m < TOOM3 || m <= 2 * n.div_ceil(3) {
        karatsuba(r, a, b, t);
    } else {
        toom3(r, a, b, t);
    }
}

/// `r = a^2` (`r.len() == 2 a.len()`), scratch `t`.
fn sqr(r: &mut [L], a: &[L], t: &mut [L]) {
    let n = a.len();
    if n == 0 {
        r.fill(0);
    } else if n < KARA_SQR {
        sqr_basecase(r, a);
    } else if n < TOOM3_SQR {
        karatsuba_sqr(r, a, t);
    } else if n >= NTT_SQR && ntt_len(n, n) <= NTT_MAX {
        ntt_mul(r, a, &[], t);
    } else {
        toom3_sqr(r, a, t);
    }
}

/// a = a1 B^k + a0, b = b1 B^k + b0 (`n >= m > n / 2`):
/// ab = a1 b1 B^2k + ((a0 + a1)(b0 + b1) - a0 b0 - a1 b1) B^k + a0 b0.
fn karatsuba(r: &mut [L], a: &[L], b: &[L], t: &mut [L]) {
    let k = a.len().div_ceil(2);
    let (a0, a1) = a.split_at(k);
    let (b0, b1) = b.split_at(k);
    {
        let (lo, hi) = r.split_at_mut(2 * k);
        mul(lo, a0, b0, t);
        mul(hi, a1, b1, t);
    }
    let (sa, t) = t.split_at_mut(k + 1);
    let (sb, t) = t.split_at_mut(k + 1);
    let (z, t) = t.split_at_mut(2 * k + 2);
    copy_ext(sa, a0);
    add_in(sa, a1);
    copy_ext(sb, b0);
    add_in(sb, b1);
    mul(z, sa, sb, t);
    sub_in(z, &r[..2 * k]);
    sub_in(z, &r[2 * k..]);
    add_at(r, k, z);
}

fn karatsuba_sqr(r: &mut [L], a: &[L], t: &mut [L]) {
    let k = a.len().div_ceil(2);
    let (a0, a1) = a.split_at(k);
    {
        let (lo, hi) = r.split_at_mut(2 * k);
        sqr(lo, a0, t);
        sqr(hi, a1, t);
    }
    let (sa, t) = t.split_at_mut(k + 1);
    let (z, t) = t.split_at_mut(2 * k + 2);
    copy_ext(sa, a0);
    add_in(sa, a1);
    sqr(z, sa, t);
    sub_in(z, &r[..2 * k]);
    sub_in(z, &r[2 * k..]);
    add_at(r, k, z);
}

/// The three pieces of `a` at `k` limbs (`a2` may be shorter).
const fn split3(a: &[L], k: usize) -> (&[L], &[L], &[L]) {
    let (a0, rest) = a.split_at(k);
    let (a1, a2) = rest.split_at(k);
    (a0, a1, a2)
}

/// `e = a(1)`.
fn eval_1(e: &mut [L], a: (&[L], &[L], &[L])) {
    copy_ext(e, a.0);
    add_in(e, a.1);
    add_in(e, a.2);
}

/// `e = |a(-1)|` (`p` scratch); whether `a(-1) < 0`.
fn eval_m1(e: &mut [L], p: &mut [L], a: (&[L], &[L], &[L])) -> bool {
    copy_ext(p, a.0);
    add_in(p, a.2);
    copy_ext(e, a.1);
    let lt = {
        // p < a1?
        let mut lt = false;
        for (x, y) in p.iter().zip(e.iter()).rev() {
            if x != y {
                lt = x < y;
                break;
            }
        }
        lt
    };
    if lt {
        sub_in(e, p);
    } else {
        neg_in(e);
        add_in(e, p);
    }
    lt
}

/// `e = a(2) = a0 + 2 a1 + 4 a2`.
fn eval_2(e: &mut [L], a: (&[L], &[L], &[L])) {
    copy_ext(e, a.2);
    shl1_in(e);
    add_in(e, a.1);
    shl1_in(e);
    add_in(e, a.0);
}

/// Toom-3 interpolation from the point values at 0 (`r[..2k]`), 1
/// (`v1`), -1 (`vm1`), 2 (`v2`) and infinity (`r[4k..]`; the middle of
/// `r` zero), each `2k + 2`-limb two's complement; adds the inner
/// coefficients c1..c3 into `r`.
fn toom3_interpolate(r: &mut [L], k: usize, v1: &mut [L], vm1: &mut [L], v2: &mut [L]) {
    let (v0, rest) = r.split_at(2 * k);
    let vinf = &rest[2 * k..];
    // v2 = (v2 - vm1) / 3 = c1 + c2 + 3 c3 + 5 c4
    sub_in(v2, vm1);
    divexact3_in(v2);
    // vm1 = (v1 - vm1) / 2 = c1 + c3
    neg_in(vm1);
    add_in(vm1, v1);
    sar1_in(vm1);
    // v1 = v1 - v0 = c1 + c2 + c3 + c4
    sub_in(v1, v0);
    // v2 = (v2 - v1) / 2 - 2 c4 = c3
    sub_in(v2, v1);
    sar1_in(v2);
    sub_in(v2, vinf);
    sub_in(v2, vinf);
    // v1 = v1 - vm1 - c4 = c2
    sub_in(v1, vm1);
    sub_in(v1, vinf);
    // vm1 = vm1 - c3 = c1
    sub_in(vm1, v2);
    add_at(r, k, vm1);
    add_at(r, 2 * k, v1);
    add_at(r, 3 * k, v2);
}

/// Toom-3 on pieces of `k = ceil(n/3)` limbs (`m > 2k`).
fn toom3(r: &mut [L], a: &[L], b: &[L], t: &mut [L]) {
    let k = a.len().div_ceil(3);
    let a3 = split3(a, k);
    let b3 = split3(b, k);
    {
        let (lo, rest) = r.split_at_mut(2 * k);
        let (mid, hi) = rest.split_at_mut(2 * k);
        mul(lo, a3.0, b3.0, t);
        mul(hi, a3.2, b3.2, t);
        mid.fill(0);
    }
    let w = 2 * k + 2;
    let (v1, t) = t.split_at_mut(w);
    let (vm1, t) = t.split_at_mut(w);
    let (v2, t) = t.split_at_mut(w);
    let (p, t) = t.split_at_mut(k + 1);
    let (ea, t) = t.split_at_mut(k + 1);
    let (eb, t) = t.split_at_mut(k + 1);
    eval_1(ea, a3);
    eval_1(eb, b3);
    mul(v1, ea, eb, t);
    let na = eval_m1(ea, p, a3);
    let nb = eval_m1(eb, p, b3);
    mul(vm1, ea, eb, t);
    if na != nb {
        neg_in(vm1);
    }
    eval_2(ea, a3);
    eval_2(eb, b3);
    mul(v2, ea, eb, t);
    toom3_interpolate(r, k, v1, vm1, v2);
}

fn toom3_sqr(r: &mut [L], a: &[L], t: &mut [L]) {
    let k = a.len().div_ceil(3);
    let a3 = split3(a, k);
    {
        let (lo, rest) = r.split_at_mut(2 * k);
        let (mid, hi) = rest.split_at_mut(2 * k);
        sqr(lo, a3.0, t);
        sqr(hi, a3.2, t);
        mid.fill(0);
    }
    let w = 2 * k + 2;
    let (v1, t) = t.split_at_mut(w);
    let (vm1, t) = t.split_at_mut(w);
    let (v2, t) = t.split_at_mut(w);
    let (p, t) = t.split_at_mut(k + 1);
    let (ea, t) = t.split_at_mut(k + 1);
    eval_1(ea, a3);
    sqr(v1, ea, t);
    eval_m1(ea, p, a3);
    sqr(vm1, ea, t);
    eval_2(ea, a3);
    sqr(v2, ea, t);
    toom3_interpolate(r, k, v1, vm1, v2);
}

/// `L`s holding `n` `u32` limbs.
const fn packed(n: usize) -> usize {
    n.div_ceil(PER)
}

// ---- three-prime NTT ----
//
// The `u32` digits of both operands are coefficients; their cyclic
// convolution is computed modulo three primes p < 2^30 with 2^23 | p - 1
// (Montgomery arithmetic, R = 2^32) and put back together by Garner's
// CRT. A coefficient of the product is below min(len) 2^64 <= 2^86 <
// p1 p2 p3 (2^88.2), so transform lengths up to 2^23 are exact. The
// butterflies keep values in [0, 2p) (Harvey's lazy reduction, which
// needs 4p < 2^32).

/// The primes.
const P1: u32 = 998_244_353;
const P2: u32 = 754_974_721;
const P3: u32 = 469_762_049;
/// The longest transform (`u32` coefficients).
const NTT_MAX: usize = 1 << 23;

const fn pow_mod(b: u64, e: u64, p: u64) -> u64 {
    let (mut b, mut e, mut r) = (b % p, e, 1u64);
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % p;
        }
        b = b * b % p;
        e >>= 1;
    }
    r
}

/// Montgomery arithmetic modulo the prime `P` (R = 2^32).
struct Mont<const P: u32>;

impl<const P: u32> Mont<P> {
    /// -P^-1 mod 2^32 (Newton: x (2 - P x) doubles the correct bits).
    const PINV: u32 = {
        assert!(P < 1 << 30);
        let mut x = 1u32;
        let mut i = 0;
        while i < 5 {
            x = x.wrapping_mul(2u32.wrapping_sub(P.wrapping_mul(x)));
            i += 1;
        }
        x.wrapping_neg()
    };

    /// a b / R mod P, in [0, 2P) for `a b < 2^32 P` (`a < 4P, b < P`, or
    /// both below 2P).
    #[inline]
    const fn mul(a: u32, b: u32) -> u32 {
        let t = a as u64 * b as u64;
        // The low half of `t`, as 32-bit products (vectorizes).
        let m = a.wrapping_mul(b).wrapping_mul(Self::PINV);
        ((t + m as u64 * P as u64) >> 32) as u32
    }

    /// [0, 2k P) to [0, k P) (`k` = 1, 2): wraps unless `x >= k P`.
    #[inline]
    const fn fold<const K: u32>(x: u32) -> u32 {
        let y = x.wrapping_sub(K * P);
        if y < x { y } else { x }
    }

    /// `x R mod P`.
    const fn to_mont(x: u64) -> u32 {
        (((x % P as u64) << 32) % P as u64) as u32
    }

    /// Root tables for length `n`: `rt[h + j] = w_2h^j` for each half
    /// length `h` (Montgomery form, below P), `irt` the same for the
    /// inverses.
    fn roots(g: u32, n: usize, rt: &mut [u32], irt: &mut [u32]) {
        // The first `K` powers in sequence, then each from the one `K`
        // back: independent products instead of one chain of `h`.
        const K: usize = 16;
        let p = u64::from(P);
        let w = pow_mod(u64::from(g), (p - 1) / n as u64, p);
        let wi = pow_mod(w, p - 2, p);
        let h = n / 2;
        let (mut x, mut y) = (Self::to_mont(1), Self::to_mont(1));
        let (wm, wim) = (Self::to_mont(w), Self::to_mont(wi));
        for j in 0..h.min(K) {
            rt[h + j] = x;
            irt[h + j] = y;
            x = Self::fold::<1>(Self::mul(x, wm));
            y = Self::fold::<1>(Self::mul(y, wim));
        }
        for j in K..h {
            rt[h + j] = Self::fold::<1>(Self::mul(rt[h + j - K], x));
            irt[h + j] = Self::fold::<1>(Self::mul(irt[h + j - K], y));
        }
        let mut h = h / 2;
        while h >= 1 {
            for j in 0..h {
                rt[h + j] = rt[2 * h + 2 * j];
                irt[h + j] = irt[2 * h + 2 * j];
            }
            h /= 2;
        }
    }

    /// Forward transform (decimation in frequency, length >= 4): natural
    /// order in, bit-reversed out; values in [0, 2P) both ends.
    fn forward(a: &mut [u32], rt: &[u32]) {
        let mut h = a.len() / 2;
        while h >= 4 {
            let w = &rt[h..2 * h];
            for blk in a.chunks_exact_mut(2 * h) {
                let (x, y) = blk.split_at_mut(h);
                for ((u, v), &w) in x.iter_mut().zip(y.iter_mut()).zip(w) {
                    let (s, d) = (*u, *v);
                    *u = Self::fold::<2>(s + d);
                    *v = Self::mul(s + 2 * P - d, w);
                }
            }
            h /= 2;
        }
        // h = 2 and 1 together; the twiddles are 1 but for w_4.
        let w4 = rt[3];
        for p in a.chunks_exact_mut(4) {
            let (y0, y2) = (
                Self::fold::<2>(p[0] + p[2]),
                Self::fold::<2>(p[0] + 2 * P - p[2]),
            );
            let (y1, y3) = (
                Self::fold::<2>(p[1] + p[3]),
                Self::mul(p[1] + 2 * P - p[3], w4),
            );
            p[0] = Self::fold::<2>(y0 + y1);
            p[1] = Self::fold::<2>(y0 + 2 * P - y1);
            p[2] = Self::fold::<2>(y2 + y3);
            p[3] = Self::fold::<2>(y2 + 2 * P - y3);
        }
    }

    /// Inverse transform without the 1/n (decimation in time, length >=
    /// 4): bit-reversed in, natural order out; values in [0, 2P) both
    /// ends.
    fn inverse(a: &mut [u32], irt: &[u32]) {
        let n = a.len();
        // h = 1 and 2 together; the twiddles are 1 but for w_4^-1.
        let w4 = irt[3];
        for p in a.chunks_exact_mut(4) {
            let (y0, y1) = (
                Self::fold::<2>(p[0] + p[1]),
                Self::fold::<2>(p[0] + 2 * P - p[1]),
            );
            let (y2, y3) = (
                Self::fold::<2>(p[2] + p[3]),
                Self::fold::<2>(p[2] + 2 * P - p[3]),
            );
            let t = Self::mul(y3, w4);
            p[0] = Self::fold::<2>(y0 + y2);
            p[2] = Self::fold::<2>(y0 + 2 * P - y2);
            p[1] = Self::fold::<2>(y1 + t);
            p[3] = Self::fold::<2>(y1 + 2 * P - t);
        }
        let mut h = 4;
        while h < n {
            let w = &irt[h..2 * h];
            for blk in a.chunks_exact_mut(2 * h) {
                let (x, y) = blk.split_at_mut(h);
                for ((u, v), &w) in x.iter_mut().zip(y.iter_mut()).zip(w) {
                    let (s, d) = (*u, Self::mul(*v, w));
                    *u = Self::fold::<2>(s + d);
                    *v = Self::fold::<2>(s + 2 * P - d);
                }
            }
            h *= 2;
        }
    }

    /// `f = d mod P`, zero-extended.
    fn load(f: &mut [u32], d: &[u32]) {
        for (x, &v) in f.iter_mut().zip(d) {
            *x = v % P;
        }
        f[d.len()..].fill(0);
    }

    /// `f = f g` pointwise (`g` empty: `f^2`).
    fn pointwise(f: &mut [u32], g: &[u32]) {
        if g.is_empty() {
            for x in f.iter_mut() {
                *x = Self::mul(*x, *x);
            }
        } else {
            for (x, &y) in f.iter_mut().zip(g) {
                *x = Self::mul(*x, y);
            }
        }
    }

    /// The factor that undoes the 1/R of the pointwise products and the
    /// factor `n` of the transforms (applied in the CRT pass).
    const fn scale(n: usize) -> u32 {
        let p = P as u64;
        let r2 = (1u64 << 32) % p;
        (r2 * r2 % p * pow_mod(n as u64, p - 2, p) % p) as u32
    }
}

/// Primitive roots of P1, P2, P3.
const G: [u32; 3] = [3, 11, 3];

/// The `u32` limbs of `res` (three residue vectors of `n`, in [0, 2p),
/// each times its `s`) put back together (Garner: x = r1 + p1 (t2 + p2
/// t3)) and carried into `out`.
fn garner(out: &mut [u32], res: &[u32], n: usize, s: [u32; 3]) {
    let (r1, rest) = res.split_at(n);
    let (r2, r3) = rest.split_at(n);
    let (p1, p2, p3) = (u64::from(P1), u64::from(P2), u64::from(P3));
    let i12 = const { pow_mod(P1 as u64, P2 as u64 - 2, P2 as u64) };
    let i123 = const { pow_mod(P1 as u64 * P2 as u64 % P3 as u64, P3 as u64 - 2, P3 as u64) };
    let mut carry = 0u128;
    for (i, o) in out.iter_mut().enumerate() {
        let x1 = u64::from(Mont::<P1>::fold::<1>(Mont::<P1>::mul(r1[i], s[0])));
        let x2 = u64::from(Mont::<P2>::fold::<1>(Mont::<P2>::mul(r2[i], s[1])));
        let x3 = u64::from(Mont::<P3>::fold::<1>(Mont::<P3>::mul(r3[i], s[2])));
        let t2 = (x2 + p2 - x1 % p2) % p2 * i12 % p2;
        let x12 = x1 + p1 * t2;
        let t3 = (x3 + p3 - x12 % p3) % p3 * i123 % p3;
        let v = carry + x12 as u128 + (p1 * p2) as u128 * t3 as u128;
        *o = v as u32;
        carry = v >> 32;
    }
    debug_assert!(carry == 0);
}

/// Root tables for transforms up to length `n`: per prime `rt` then
/// `irt`, `n` each. `rt[h + j]` depends on `h` only, so a table serves
/// every shorter transform.
fn ntt_roots(w: &mut [u32], n: usize) {
    let (w1, rest) = w.split_at_mut(2 * n);
    let (w2, w3) = rest.split_at_mut(2 * n);
    let (a, b) = w1.split_at_mut(n);
    Mont::<P1>::roots(G[0], n, a, b);
    let (a, b) = w2.split_at_mut(n);
    Mont::<P2>::roots(G[1], n, a, b);
    let (a, b) = w3[..2 * n].split_at_mut(n);
    Mont::<P3>::roots(G[2], n, a, b);
}

/// The forward transforms of `d` into `f` (`n` per prime), roots `w`
/// (`ntt_roots` for at least `n`, of `wn`).
fn ntt_forward(f: &mut [u32], n: usize, d: &[u32], w: &[u32], wn: usize) {
    let (f1, rest) = f.split_at_mut(n);
    let (f2, f3) = rest.split_at_mut(n);
    Mont::<P1>::load(f1, d);
    Mont::<P1>::forward(f1, &w[..wn]);
    Mont::<P2>::load(f2, d);
    Mont::<P2>::forward(f2, &w[2 * wn..3 * wn]);
    Mont::<P3>::load(&mut f3[..n], d);
    Mont::<P3>::forward(&mut f3[..n], &w[4 * wn..5 * wn]);
}

/// `res = ntt_forward(d) * g` pointwise, inverted (`g` the transforms of
/// the other operand, empty to square `d`); the CRT factors.
fn ntt_finish(res: &mut [u32], n: usize, g: &[u32], w: &[u32], wn: usize) -> [u32; 3] {
    let (f1, rest) = res.split_at_mut(n);
    let (f2, f3) = rest.split_at_mut(n);
    let f3 = &mut f3[..n];
    let gi = |i: usize| {
        if g.is_empty() {
            g
        } else {
            &g[i * n..(i + 1) * n]
        }
    };
    Mont::<P1>::pointwise(f1, gi(0));
    Mont::<P1>::inverse(f1, &w[wn..2 * wn]);
    Mont::<P2>::pointwise(f2, gi(1));
    Mont::<P2>::inverse(f2, &w[3 * wn..4 * wn]);
    Mont::<P3>::pointwise(f3, gi(2));
    Mont::<P3>::inverse(f3, &w[5 * wn..6 * wn]);
    [
        Mont::<P1>::scale(n),
        Mont::<P2>::scale(n),
        Mont::<P3>::scale(n),
    ]
}

/// The `u32` digits of `a`.
const fn digits32(a: &[L]) -> &[u32] {
    // SAFETY: `L` is `PER` little-endian `u32`s (see `pack`).
    unsafe { slice::from_raw_parts(a.as_ptr().cast::<u32>(), a.len() * PER) }
}

/// Transform length (`u32` coefficients) for an `n` × `m` product.
const fn ntt_len(n: usize, m: usize) -> usize {
    ((n + m) * PER).next_power_of_two()
}

/// Scratch `L`s `ntt_mul` uses.
const fn ntt_scratch(n: usize, m: usize) -> usize {
    6 * ntt_len(n, m) / PER
}

/// `f` = the cyclic convolution of `da` and `db` (`db` empty: `da` with
/// itself) mod P, in [0, 2P); `fb`, `rt`, `irt` scratch of `f.len()`.
fn convolve<const P: u32>(
    g: u32,
    f: &mut [u32],
    fb: &mut [u32],
    rt: &mut [u32],
    irt: &mut [u32],
    da: &[u32],
    db: &[u32],
) {
    Mont::<P>::roots(g, f.len(), rt, irt);
    Mont::<P>::load(f, da);
    Mont::<P>::forward(f, rt);
    if db.is_empty() {
        Mont::<P>::pointwise(f, &[]);
    } else {
        Mont::<P>::load(fb, db);
        Mont::<P>::forward(fb, rt);
        Mont::<P>::pointwise(f, fb);
    }
    Mont::<P>::inverse(f, irt);
}

/// `r = a * b` by the NTT (`b` empty squares `a`), scratch `t`: one
/// prime at a time.
fn ntt_mul(r: &mut [L], a: &[L], b: &[L], t: &mut [L]) {
    let n = ntt_len(a.len(), if b.is_empty() { a.len() } else { b.len() });
    let (da, db) = (digits32(a), digits32(b));
    // SAFETY: `t` is `L`s; any bit pattern is a `u32`.
    let t = unsafe { slice::from_raw_parts_mut(t.as_mut_ptr().cast::<u32>(), t.len() * PER) };
    let (res, t) = t.split_at_mut(3 * n);
    let (fb, t) = t.split_at_mut(n);
    let (rt, t) = t.split_at_mut(n);
    let irt = &mut t[..n];
    let (r1, rest) = res.split_at_mut(n);
    let (r2, r3) = rest.split_at_mut(n);
    convolve::<P1>(G[0], r1, fb, rt, irt, da, db);
    convolve::<P2>(G[1], r2, fb, rt, irt, da, db);
    convolve::<P3>(G[2], r3, fb, rt, irt, da, db);
    // SAFETY: as `t` above.
    let out = unsafe { slice::from_raw_parts_mut(r.as_mut_ptr().cast::<u32>(), r.len() * PER) };
    let s = [
        Mont::<P1>::scale(n),
        Mont::<P2>::scale(n),
        Mont::<P3>::scale(n),
    ];
    garner(out, res, n, s);
}

/// The transform length `rok_nat_mul` takes for an `an` × `bn` product
/// (`u32` limbs), 0 when it does not use the NTT.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_nat_ntt_len(an: usize, bn: usize) -> usize {
    let (na, nb) = (packed(an), packed(bn));
    let lo = if na < nb { na } else { nb };
    let n = ntt_len(na, nb);
    if lo >= NTT && n <= NTT_MAX { n } else { 0 }
}

/// `w[0..6 n]` = root tables for transforms up to length `n` (a power of
/// two, at most what `rok_nat_ntt_len` returns).
///
/// # Safety
/// A live `GcBuf<u32>` of at least `6 n` elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_ntt_roots(w: *mut u8, n: usize) {
    assert!(n.is_power_of_two() && n <= NTT_MAX);
    // SAFETY: caller contract.
    ntt_roots(unsafe { limbs(w, 6 * n) }, n);
}

/// `f[0..3 n]` = the transforms of `b[0..bn]` for products of up to `n`
/// limbs, roots `w` from `rok_nat_ntt_roots(w, wn)`, `wn >= n`.
///
/// # Safety
/// Live `GcBuf<u32>`s of at least those lengths; `f` distinct from the
/// others.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_ntt_prep(
    f: *mut u8,
    b: *mut u8,
    bn: usize,
    n: usize,
    w: *mut u8,
    wn: usize,
) {
    assert!(n.is_power_of_two() && bn <= n && n <= wn);
    // SAFETY: caller contract; `b` and `w` only read.
    let (f, b, w) = unsafe { (limbs(f, 3 * n), &*limbs(b, bn), &*limbs(w, 6 * wn)) };
    ntt_forward(f, n, b, w, wn);
}

/// `r[0..an + bn] = a * b` for `b` prepared in `f` (`rok_nat_ntt_prep`,
/// length `n >= an + bn`, roots `w` of `wn`); `t` holds `3 n` limbs.
///
/// # Safety
/// Live `GcBuf<u32>`s of at least those lengths; `r` and `t` distinct
/// from each other and from the rest.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_ntt_mul(
    r: *mut u8,
    a: *mut u8,
    an: usize,
    f: *mut u8,
    bn: usize,
    n: usize,
    w: *mut u8,
    wn: usize,
    t: *mut u8,
) {
    assert!(an + bn <= n && n <= wn);
    // SAFETY: caller contract; `a`, `f` and `w` only read.
    let (r, a, f, w, t) = unsafe {
        (
            limbs(r, an + bn),
            &*limbs(a, an),
            &*limbs(f, 3 * n),
            &*limbs(w, 6 * wn),
            limbs(t, 3 * n),
        )
    };
    ntt_forward(t, n, a, w, wn);
    let s = ntt_finish(t, n, f, w, wn);
    garner(r, t, n, s);
}

// `PER` consecutive `u32` limbs are one `L` in memory.
const _: () = assert!(cfg!(target_endian = "little"));

/// `dst = src` (`dst.len() == packed(src.len())`).
fn pack(dst: &mut [L], src: &[u32]) {
    dst[dst.len() - 1] = 0;
    // SAFETY: `dst` holds at least `src.len()` `u32`s; distinct buffers.
    unsafe {
        core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr().cast::<u32>(), src.len());
    };
}

/// `dst = src` truncated to `dst.len()` `u32`s.
fn unpack(dst: &mut [u32], src: &[L]) {
    assert!(dst.len() <= src.len() * PER);
    // SAFETY: as in `pack`.
    unsafe {
        core::ptr::copy_nonoverlapping(src.as_ptr().cast::<u32>(), dst.as_mut_ptr(), dst.len());
    };
}

/// `u32` limbs of scratch `rok_nat_mul` needs for an `an` × `bn` product.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_nat_mul_scratch(an: usize, bn: usize) -> usize {
    let (na, nb) = (packed(an), packed(bn));
    (2 * (na + nb) + scratch_bound(na, nb)) * PER
}

/// `r[0..an + bn] = a * b`; `t` holds `rok_nat_mul_scratch(an, bn)`
/// limbs. `a` and `b` may be the same buffer (`an == bn` squares).
///
/// # Safety
/// Live `GcBuf<u32>`s of at least those lengths; `r` and `t` distinct
/// from each other and from `a` / `b`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_mul(
    r: *mut u8,
    a: *mut u8,
    an: usize,
    b: *mut u8,
    bn: usize,
    t: *mut u8,
) {
    let square = a == b && an == bn;
    let (na, nb) = (packed(an), packed(bn));
    let tn = rok_nat_mul_scratch(an, bn) / PER;
    // SAFETY: caller contract; `a` / `b` only read; elements are 8-aligned.
    let (a, b, r) = unsafe { (&*limbs(a, an), &*limbs(b, bn), limbs(r, an + bn)) };
    // SAFETY: as above; `t` is its own buffer of `tn * PER` limbs.
    let t = unsafe { slice::from_raw_parts_mut(t.add(HEADER_SIZE).cast::<L>(), tn) };
    let (pa, t) = t.split_at_mut(na);
    let (pb, t) = t.split_at_mut(nb);
    let (pr, t) = t.split_at_mut(na + nb);
    pack(pa, a);
    if square {
        sqr(pr, pa, t);
    } else {
        pack(pb, b);
        mul(pr, pa, pb, t);
    }
    unpack(r, pr);
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

/// Writes the digits of `a[0..n]` (`n <= 64`) in base `radix` ending at
/// `out[end]` (exclusive), zero-padded to `width`; the start. Chunks of
/// the largest power of `radix` in an `L`, by single-limb division with
/// a reciprocal.
///
/// # Safety
/// Live `GcBuf`s: `out` (`u8`) of at least `end` bytes with room for the
/// digits, `a` (`u32`) of at least `n` limbs.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_put_digits(
    out: *mut u8,
    end: usize,
    a: *mut u8,
    n: usize,
    width: usize,
    radix: u32,
) -> usize {
    const DIGITS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";
    // SAFETY: caller contract.
    let (out, a) = unsafe {
        (
            slice::from_raw_parts_mut(out.add(HEADER_SIZE), end),
            &*limbs(a, n),
        )
    };
    let mut buf = [0 as L; 64 / PER];
    let mut wn = packed(n);
    if wn > 0 {
        pack(&mut buf[..wn], a);
    }
    let rx = L::from(radix);
    let (mut chunk, mut per) = (rx, 1usize);
    while let Some(c) = chunk.checked_mul(rx) {
        chunk = c;
        per += 1;
    }
    let s = chunk.leading_zeros();
    let dn = chunk << s;
    let inv = reciprocal(dn);
    let mut at = end;
    while wn > 0 && buf[wn - 1] == 0 {
        wn -= 1;
    }
    while wn > 0 {
        let mut rem: L = 0;
        for x in buf[..wn].iter_mut().rev() {
            // (rem B + x) / chunk as (that << s) / (chunk << s).
            let n1 = if s == 0 {
                rem
            } else {
                (rem << s) | (*x >> (LB - s))
            };
            let (q, r) = div2by1(n1, *x << s, dn, inv);
            *x = q;
            rem = r >> s;
        }
        while wn > 0 && buf[wn - 1] == 0 {
            wn -= 1;
        }
        // A full chunk unless it is the leading one.
        let mut k = 0;
        while k < per && (wn > 0 || rem != 0) {
            at -= 1;
            out[at] = DIGITS[(rem % rx) as usize];
            rem /= rx;
            k += 1;
        }
    }
    while end - at < width {
        at -= 1;
        out[at] = b'0';
    }
    at
}

/// floor((B^2 - 1) / d) - B for a normalized `d` (top bit set): the
/// reciprocal of Möller and Granlund, "Improved division by invariant
/// integers" (2011).
const fn reciprocal(d: L) -> L {
    (((((!d) as W) << LB) | L::MAX as W) / d as W) as L
}

/// `(u1 B + u0) / d` for `u1 < d`, `d` normalized, `v = reciprocal(d)`:
/// quotient and remainder (algorithm 4 of the paper).
const fn div2by1(u1: L, u0: L, d: L, v: L) -> (L, L) {
    let p = v as W * u1 as W + (((u1 as W) << LB) | u0 as W);
    let mut q1 = ((p >> LB) as L).wrapping_add(1);
    let q0 = p as L;
    let mut r = u0.wrapping_sub(q1.wrapping_mul(d));
    if r > q0 {
        q1 = q1.wrapping_sub(1);
        r = r.wrapping_add(d);
    }
    if r >= d {
        q1 += 1;
        r -= d;
    }
    (q1, r)
}

/// `r[..a.len()] -= a * x`; the borrow limb.
fn submul_1(r: &mut [L], a: &[L], x: L) -> L {
    let mut c: L = 0;
    for (y, &v) in r.iter_mut().zip(a) {
        let p = v as W * x as W + c as W;
        let (d, b) = y.overflowing_sub(p as L);
        *y = d;
        c = (p >> LB) as L + L::from(b);
    }
    c
}

/// `r <<= s` (`s < LB`); the bits shifted out.
fn shl_in(r: &mut [L], s: u32) -> L {
    if s == 0 {
        return 0;
    }
    let mut top = 0;
    for x in r {
        let v = *x;
        *x = (v << s) | top;
        top = v >> (LB - s);
    }
    top
}

/// `r >>= s` (`s < LB`), zero filled.
fn shr_in(r: &mut [L], s: u32) {
    if s == 0 {
        return;
    }
    let n = r.len();
    for i in 0..n - 1 {
        r[i] = (r[i] >> s) | (r[i + 1] << (LB - s));
    }
    r[n - 1] >>= s;
}

/// Knuth TAOCP 4.3.1 algorithm D: `u` (`m + n + 1` limbs, `u[m + n] <
/// v[n - 1]`) / `v` (`n` limbs, top bit set) → `q[0..=m]`, the
/// remainder left in `u[..n]`.
fn knuth_d(q: &mut [L], u: &mut [L], v: &[L]) {
    let n = v.len();
    let top = v[n - 1];
    let inv = reciprocal(top);
    if n == 1 {
        let mut rem = u[u.len() - 1];
        for i in (0..u.len() - 1).rev() {
            (q[i], rem) = div2by1(rem, u[i], top, inv);
            u[i] = 0;
        }
        u[0] = rem;
        return;
    }
    let next = v[n - 2];
    for j in (0..q.len()).rev() {
        let (u1, u0, u2) = (u[j + n], u[j + n - 1], u[j + n - 2]);
        let (mut qhat, mut rhat, mut big) = if u1 >= top {
            // q̂ = B - 1; r̂ = u1 B + u0 - (B - 1) top = u0 + top.
            let (r, o) = u0.overflowing_add(top);
            (L::MAX, r, o)
        } else {
            let (q, r) = div2by1(u1, u0, top, inv);
            (q, r, false)
        };
        // At most two steps make q̂ exact or one too big.
        while !big && qhat as W * next as W > (((rhat as W) << LB) | u2 as W) {
            qhat -= 1;
            (rhat, big) = rhat.overflowing_add(top);
        }
        let c = submul_1(&mut u[j..j + n], v, qhat);
        let (t, b) = u[j + n].overflowing_sub(c);
        u[j + n] = t;
        if b {
            // One too big: add the divisor back.
            qhat -= 1;
            let c = add_in(&mut u[j..j + n], v);
            u[j + n] = u[j + n].wrapping_add(L::from(c));
        }
        q[j] = qhat;
    }
}

/// `u32` limbs of scratch `rok_nat_divmod` needs.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_nat_divmod_scratch(an: usize, bn: usize) -> usize {
    let (na, nb) = (packed(an), packed(bn));
    (2 * na + nb + 2) * PER
}

/// `q[0..=an - bn] = a / b`, `r[0..bn] = a % b` for `an >= bn >= 2`, the
/// top limb of `b` nonzero; `t` holds `rok_nat_divmod_scratch(an, bn)`.
///
/// # Safety
/// Live `GcBuf<u32>`s of at least those lengths; `q`, `r` and `t`
/// distinct from each other and from `a` / `b`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_divmod(
    q: *mut u8,
    r: *mut u8,
    a: *mut u8,
    an: usize,
    b: *mut u8,
    bn: usize,
    t: *mut u8,
) {
    let (na, nb) = (packed(an), packed(bn));
    let tn = rok_nat_divmod_scratch(an, bn) / PER;
    // SAFETY: caller contract; `a` / `b` only read.
    let (a, b, q, r) = unsafe {
        (
            &*limbs(a, an),
            &*limbs(b, bn),
            limbs(q, an - bn + 1),
            limbs(r, bn),
        )
    };
    // SAFETY: as above; `t` is its own buffer of `tn * PER` limbs.
    let t = unsafe { slice::from_raw_parts_mut(t.add(HEADER_SIZE).cast::<L>(), tn) };
    let (u, t) = t.split_at_mut(na + 1);
    let (v, t) = t.split_at_mut(nb);
    let qs = &mut t[..=na - nb];
    pack(&mut u[..na], a);
    u[na] = 0;
    pack(v, b);
    let s = v[nb - 1].leading_zeros();
    shl_in(v, s);
    u[na] = shl_in(&mut u[..na], s);
    knuth_d(qs, u, v);
    shr_in(&mut u[..nb], s);
    unpack(q, qs);
    unpack(r, &u[..nb]);
}

/// gcd of two words (binary).
const fn gcd_word(mut a: L, mut b: L) -> L {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let k = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            (a, b) = (b, a);
        }
        b -= a;
        if b == 0 {
            return a << k;
        }
    }
}

/// Lehmer cofactors stay below 2^LEHMER in magnitude (see
/// `lehmer_apply`).
const LEHMER: u32 = LB - 2;

/// Knuth TAOCP 4.5.2 algorithm L on the top `2 LB - 2` bits of `x >= y`
/// (`n >= 2` limbs, `x[n - 1] != 0`; `y` at the same shift): cofactors
/// `(a, b, c, d)` such that `a x + b y` and `c x + d y` are two
/// consecutive remainders of Euclid's sequence; `b == 0` when not even
/// the first quotient is certain. `a`, `b` (and `c`, `d`) have opposite
/// signs. Two limbs of precision give quotients until the cofactors
/// reach about one limb, where the bound stops them.
fn lehmer(x: &[L], y: &[L]) -> (SL, SL, SL, SL) {
    const CAP: SW = 1 << LEHMER;
    let n = x.len();
    let z = x[n - 1].leading_zeros();
    let top = |v: &[L]| {
        let hi = (((v[n - 1] as W) << LB) | v[n - 2] as W) << z;
        let lo = if n > 2 && z > 0 {
            (v[n - 3] >> (LB - z)) as W
        } else {
            0
        };
        ((hi | lo) >> 2) as SW
    };
    let (mut xh, mut yh) = (top(x), top(y));
    let (mut a, mut b, mut c, mut d): (SW, SW, SW, SW) = (1, 0, 0, 1);
    while yh + c != 0 && yh + d != 0 {
        let q = (xh + a) / (yh + c);
        if q != (xh + b) / (yh + d) {
            break;
        }
        let next = |u: SW, v: SW| {
            q.checked_mul(v)
                .and_then(|p| u.checked_sub(p))
                .filter(|t| t.abs() < CAP)
        };
        let (Some(nc), Some(nd)) = (next(a, c), next(b, d)) else {
            break;
        };
        (a, c) = (c, nc);
        (b, d) = (d, nd);
        (xh, yh) = (yh, xh - q * yh);
    }
    (a as SL, b as SL, c as SL, d as SL)
}

/// `(x, y) = (a x + b y, c x + d y)` for Lehmer cofactors (both results
/// non-negative and at most `x`).
fn lehmer_apply(x: &mut [L], y: &mut [L], (a, b, c, d): (SL, SL, SL, SL)) {
    // |a u + b v| < 2^LEHMER 2^LB (opposite signs), so the sums fit `SW`.
    let (mut cx, mut cy): (SW, SW) = (0, 0);
    for (u, v) in x.iter_mut().zip(y.iter_mut()) {
        let (p, q) = (*u as SW, *v as SW);
        cx += a as SW * p + b as SW * q;
        cy += c as SW * p + d as SW * q;
        *u = cx as L;
        *v = cy as L;
        cx >>= LB;
        cy >>= LB;
    }
    debug_assert!(cx == 0 && cy == 0);
}

/// Limbs of `a` without leading zeros.
fn significant(a: &[L]) -> usize {
    a.iter().rposition(|&v| v != 0).map_or(0, |i| i + 1)
}

/// `gcd(x, y)` (`x >= y`, both `x.len()` limbs, zero-extended); the
/// result is left in `x` or `y`: which, and its limbs. Lehmer steps
/// replace runs of single-limb quotients by one linear pass; a step
/// that finds no quotient divides (Knuth D, scratch `t` of `3 x.len() +
/// 1`).
fn gcd_lehmer<'a>(mut x: &'a mut [L], mut y: &'a mut [L], t: &mut [L]) -> (&'a [L], usize) {
    let mut n = significant(x);
    loop {
        let yn = significant(&y[..n]);
        if yn == 0 {
            return (x, n);
        }
        if n == 1 {
            x[0] = gcd_word(x[0], y[0]);
            return (x, 1);
        }
        let f = lehmer(&x[..n], &y[..n]);
        if f.1 != 0 {
            lehmer_apply(&mut x[..n], &mut y[..n], f);
            n = significant(&x[..n]);
            continue;
        }
        // x = x mod y, then swap.
        let (u, rest) = t.split_at_mut(n + 1);
        let (v, rest) = rest.split_at_mut(yn);
        let q = &mut rest[..=n - yn];
        let sh = y[yn - 1].leading_zeros();
        v.copy_from_slice(&y[..yn]);
        shl_in(v, sh);
        u[..n].copy_from_slice(&x[..n]);
        u[n] = shl_in(&mut u[..n], sh);
        knuth_d(q, u, v);
        shr_in(&mut u[..yn], sh);
        x[..yn].copy_from_slice(&u[..yn]);
        x[yn..n].fill(0);
        core::mem::swap(&mut x, &mut y);
        n = yn;
    }
}

/// `u32` limbs of scratch `rok_nat_gcd` needs.
#[unsafe(no_mangle)]
pub const extern "C" fn rok_nat_gcd_scratch(an: usize, bn: usize) -> usize {
    let m = packed(if an > bn { an } else { bn });
    (5 * m + 1) * PER
}

/// `r = gcd(a, b)` (`an >= bn >= 1`, `a >= b`, both without leading
/// zero limbs); its limbs (at most `bn`). `t` holds
/// `rok_nat_gcd_scratch(an, bn)` limbs.
///
/// # Safety
/// Live `GcBuf<u32>`s of at least those lengths (`r` of `bn`); `r` and
/// `t` distinct from each other and from `a` / `b`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_gcd(
    r: *mut u8,
    a: *mut u8,
    an: usize,
    b: *mut u8,
    bn: usize,
    t: *mut u8,
) -> usize {
    let m = packed(an);
    let tn = rok_nat_gcd_scratch(an, bn) / PER;
    // SAFETY: caller contract; `a` / `b` only read.
    let (a, b, r) = unsafe { (&*limbs(a, an), &*limbs(b, bn), limbs(r, bn)) };
    // SAFETY: as above; `t` is its own buffer of `tn * PER` limbs.
    let t = unsafe { slice::from_raw_parts_mut(t.add(HEADER_SIZE).cast::<L>(), tn) };
    let (x, t) = t.split_at_mut(m);
    let (y, t) = t.split_at_mut(m);
    pack(x, a);
    y.fill(0);
    pack(&mut y[..packed(bn)], b);
    let (g, gn) = gcd_lehmer(x, y, t);
    // SAFETY: as in `digits32`.
    let g32 = unsafe { slice::from_raw_parts(g.as_ptr().cast::<u32>(), gn * PER) };
    let k = g32.iter().rposition(|&v| v != 0).map_or(0, |i| i + 1);
    r[..k].copy_from_slice(&g32[..k]);
    k
}

/// `r[0..an] = a + b` (`an >= bn`); the carry.
///
/// # Safety
/// Live `GcBuf<u32>`s of at least those lengths; `r` distinct from `a`
/// and `b`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_add(
    r: *mut u8,
    a: *mut u8,
    an: usize,
    b: *mut u8,
    bn: usize,
) -> u32 {
    // SAFETY: caller contract; `a` / `b` only read.
    let (r, a, b) = unsafe { (limbs(r, an), &*limbs(a, an), &*limbs(b, bn)) };
    let (lo, hi) = r.split_at_mut(bn);
    let mut c = 0u64;
    for ((x, &p), &q) in lo.iter_mut().zip(a).zip(b) {
        let s = u64::from(p) + u64::from(q) + c;
        *x = s as u32;
        c = s >> 32;
    }
    for (x, &p) in hi.iter_mut().zip(&a[bn..]) {
        let s = u64::from(p) + c;
        *x = s as u32;
        c = s >> 32;
    }
    c as u32
}

/// `r[0..an] = a - b` (`a >= b`, `an >= bn`).
///
/// # Safety
/// As `rok_nat_add`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_sub(r: *mut u8, a: *mut u8, an: usize, b: *mut u8, bn: usize) {
    // SAFETY: as in `rok_nat_add`.
    let (r, a, b) = unsafe { (limbs(r, an), &*limbs(a, an), &*limbs(b, bn)) };
    let (lo, hi) = r.split_at_mut(bn);
    let mut borrow = 0u32;
    for ((x, &p), &q) in lo.iter_mut().zip(a).zip(b) {
        let (d, b1) = p.overflowing_sub(q);
        let (d, b2) = d.overflowing_sub(borrow);
        *x = d;
        borrow = u32::from(b1 | b2);
    }
    for (x, &p) in hi.iter_mut().zip(&a[bn..]) {
        let (d, b1) = p.overflowing_sub(borrow);
        *x = d;
        borrow = u32::from(b1);
    }
}

/// `r[off..=off + n] = a[0..n] << s` (`s < 32`).
///
/// # Safety
/// Live, distinct `GcBuf<u32>`s of at least those lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_shl(r: *mut u8, off: usize, a: *mut u8, n: usize, s: u32) {
    // SAFETY: caller contract.
    let (r, a) = unsafe { (&mut limbs(r, off + n + 1)[off..], &*limbs(a, n)) };
    let mut top = 0u64;
    for (x, &v) in r.iter_mut().zip(a) {
        let w = (u64::from(v) << s) | top;
        *x = w as u32;
        top = w >> 32;
    }
    r[n] = top as u32;
}

/// `r[0..n - s / 32] = a[0..n] >> s` (`s < 32 n`).
///
/// # Safety
/// Live, distinct `GcBuf<u32>`s of at least those lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rok_nat_shr(r: *mut u8, a: *mut u8, n: usize, s: u64) {
    let skip = (s / 32) as usize;
    // SAFETY: caller contract.
    let (r, a) = unsafe { (limbs(r, n - skip), &limbs(a, n)[skip..]) };
    for (i, x) in r.iter_mut().enumerate() {
        let next = a.get(i + 1).copied().unwrap_or(0);
        *x = (((u64::from(next) << 32) | u64::from(a[i])) >> (s % 32)) as u32;
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

    fn num(l: &[u32]) -> u128 {
        l.iter()
            .rev()
            .fold(0u128, |acc, &x| (acc << 32) | u128::from(x))
    }

    /// xorshift64*; all-ones limbs now and then (carry chains).
    fn rand_limbs(seed: &mut u64, n: usize) -> Vec<L> {
        (0..n)
            .map(|_| {
                *seed ^= *seed >> 12;
                *seed ^= *seed << 25;
                *seed ^= *seed >> 27;
                let v = seed.wrapping_mul(0x2545_F491_4F6C_DD1D);
                if v % 7 == 0 { L::MAX } else { v as L }
            })
            .collect()
    }

    #[test]
    fn mul_matches_schoolbook() {
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        let sizes = [
            1,
            2,
            17,
            KARA - 1,
            KARA,
            KARA + 1,
            2 * KARA + 3,
            KARA_SQR,
            TOOM3 - 1,
            TOOM3,
            TOOM3 + 1,
            TOOM3_SQR,
            TOOM3_SQR + 1,
            3 * TOOM3 + 2,
            700,
            NTT - 1,
            NTT,
            NTT_SQR + 1,
            2 * NTT + 7,
        ];
        for &n in &sizes {
            for &m in &sizes {
                if m > n {
                    continue;
                }
                let a = rand_limbs(&mut seed, n);
                let b = rand_limbs(&mut seed, m);
                let mut want = vec![0; n + m];
                mul_basecase(&mut want, &a, &b);
                let mut got = vec![0; n + m];
                let mut t = vec![0; scratch_bound(n, m)];
                mul(&mut got, &a, &b, &mut t);
                assert_eq!(got, want, "{n} x {m}");
            }
            let a = rand_limbs(&mut seed, n);
            let mut want = vec![0; 2 * n];
            mul_basecase(&mut want, &a, &a);
            let mut got = vec![0; 2 * n];
            let mut t = vec![0; scratch_bound(n, n)];
            sqr(&mut got, &a, &mut t);
            assert_eq!(got, want, "{n}^2");
        }
    }

    /// Binary gcd on `L` vectors (reference).
    fn gcd_ref(mut a: Vec<L>, mut b: Vec<L>) -> Vec<L> {
        let n = a.len().max(b.len());
        a.resize(n, 0);
        b.resize(n, 0);
        let zero = |v: &[L]| v.iter().all(|&x| x == 0);
        let even = |v: &[L]| v[0] & 1 == 0;
        let less =
            |x: &[L], y: &[L]| x.iter().rev().cmp(y.iter().rev()) == core::cmp::Ordering::Less;
        if zero(&a) {
            return b;
        }
        let mut k = 0;
        while even(&a) && even(&b) && !zero(&b) {
            shr_in(&mut a, 1);
            shr_in(&mut b, 1);
            k += 1;
        }
        while !zero(&b) {
            while even(&a) {
                shr_in(&mut a, 1);
            }
            while !zero(&b) && even(&b) {
                shr_in(&mut b, 1);
            }
            if zero(&b) {
                break;
            }
            if less(&b, &a) {
                core::mem::swap(&mut a, &mut b);
            }
            sub_in(&mut b, &a);
        }
        a.push(0);
        for _ in 0..k {
            shl1_in(&mut a);
        }
        a
    }

    /// (B^k - 1)^2 = B^2k - 2 B^k + 1 (`u32` digits): every coefficient
    /// of the convolution at its maximum, the products and squares
    /// through the NTT (`k` u32 limbs).
    #[test]
    fn ntt_max_coefficients() {
        let k = 1 << 16;
        let a = vec![L::MAX; k / PER];
        let mut want = vec![0u32; 2 * k];
        want[0] = 1;
        want[k] = 0xFFFF_FFFE;
        want[k + 1..].fill(u32::MAX);
        let mut t = vec![0; ntt_scratch(a.len(), a.len())];
        for square in [false, true] {
            let mut r = vec![0; 2 * a.len()];
            ntt_mul(&mut r, &a, if square { &[] } else { &a }, &mut t);
            assert_eq!(digits32(&r), &want[..], "square {square}");
        }
    }

    #[test]
    fn ntt_prepared_matches_mul() {
        let mut seed = 0xA076_1D64_78BD_642Fu64;
        let wn = 1 << 13;
        let mut w = vec![0u32; 6 * wn];
        ntt_roots(&mut w, wn);
        for &(an, bn, n) in &[
            (1usize, 1usize, 4usize),
            (1500, 1400, 4096),
            (2000, 2096, 4096),
            (3000, 2000, 8192),
        ] {
            let a = digits32(&rand_limbs(&mut seed, an.div_ceil(PER)))[..an].to_vec();
            let b = digits32(&rand_limbs(&mut seed, bn.div_ceil(PER)))[..bn].to_vec();
            let mut f = vec![0u32; 3 * n];
            ntt_forward(&mut f, n, &b, &w, wn);
            let mut t = vec![0u32; 3 * n];
            ntt_forward(&mut t, n, &a, &w, wn);
            let s = ntt_finish(&mut t, n, &f, &w, wn);
            let mut got = vec![0u32; an + bn];
            garner(&mut got, &t, n, s);
            // Schoolbook on u32 digits.
            let mut want = vec![0u32; an + bn];
            for (i, &x) in a.iter().enumerate() {
                let mut c = 0u64;
                for (j, &y) in b.iter().enumerate() {
                    let v = u64::from(x) * u64::from(y) + u64::from(want[i + j]) + c;
                    want[i + j] = v as u32;
                    c = v >> 32;
                }
                want[i + bn] = c as u32;
            }
            assert_eq!(got, want, "{an} x {bn} in {n}");
        }
    }

    #[test]
    fn gcd_matches_binary_gcd() {
        let mut seed = 0x5DEE_CE66_D1CE_4E5Bu64;
        for &(n, m, gl) in &[
            (1, 1, 1),
            (2, 1, 1),
            (2, 2, 1),
            (3, 2, 2),
            (5, 5, 3),
            (9, 4, 4),
            (17, 16, 6),
            (30, 30, 1),
        ] {
            for _ in 0..30 {
                // Shared factor g, cofactors without the all-ones bias.
                let g = rand_limbs(&mut seed, gl);
                let mut a = vec![0; n + gl];
                let mut b = vec![0; m + gl];
                let (ca, cb) = (rand_limbs(&mut seed, n), rand_limbs(&mut seed, m));
                mul_basecase(&mut a, &ca, &g);
                if m >= gl {
                    mul_basecase(&mut b, &cb, &g);
                } else {
                    mul_basecase(&mut b, &g, &cb);
                }
                let mut want = gcd_ref(a.clone(), b.clone());
                let (a, b) = if gcd_ref_less(&a, &b) { (b, a) } else { (a, b) };
                let w = a.len();
                let mut x = a.clone();
                let mut y = b.clone();
                y.resize(w, 0);
                let mut t = vec![0; 3 * w + 1];
                let (gv, gn) = gcd_lehmer(&mut x, &mut y, &mut t);
                let mut got = gv[..gn].to_vec();
                got.resize(want.len().max(gn), 0);
                want.resize(got.len(), 0);
                assert_eq!(got, want, "{n} {m} {gl}");
            }
        }
    }

    fn gcd_ref_less(x: &[L], y: &[L]) -> bool {
        let n = x.len().max(y.len());
        (0..n)
            .rev()
            .map(|i| {
                (
                    x.get(i).copied().unwrap_or(0),
                    y.get(i).copied().unwrap_or(0),
                )
            })
            .find(|(p, q)| p != q)
            .is_some_and(|(p, q)| p < q)
    }

    #[test]
    fn knuth_d_recovers_quotient() {
        let mut seed = 0x0123_4567_89AB_CDEFu64;
        for &(nq, nv) in &[
            (1, 1),
            (5, 1),
            (1, 2),
            (7, 2),
            (3, 9),
            (40, 17),
            (17, 40),
            (64, 64),
        ] {
            for _ in 0..20 {
                let q = rand_limbs(&mut seed, nq);
                let mut v = rand_limbs(&mut seed, nv);
                v[nv - 1] |= 1 << (LB - 1);
                let mut r = rand_limbs(&mut seed, nv);
                r[nv - 1] &= v[nv - 1] - 1;
                // u = q v + r in nq + nv + 1 limbs.
                let mut u = vec![0; nq + nv + 1];
                mul_basecase(
                    &mut u[..nq + nv],
                    if nq >= nv { &q } else { &v },
                    if nq >= nv { &v } else { &q },
                );
                add_in(&mut u, &r);
                let mut got = vec![0; nq + 1];
                knuth_d(&mut got, &mut u, &v);
                assert_eq!(&got[..nq], &q[..], "{nq} / {nv}");
                assert_eq!(got[nq], 0);
                assert_eq!(&u[..nv], &r[..]);
            }
        }
    }

    #[test]
    fn mul_divmod_round_trip() {
        let a = [0x9ABC_DEF7u32];
        let b = [0x8000_0001u32, 0xFFFF_FFFF];
        let (mut ab, mut bb, mut r) = (buf(&a, 1), buf(&b, 2), buf(&[], 3));
        let mut t = buf(&[], rok_nat_mul_scratch(1, 2));
        // SAFETY: test buffers sized above.
        unsafe {
            rok_nat_mul(
                r.as_mut_ptr().cast(),
                ab.as_mut_ptr().cast(),
                1,
                bb.as_mut_ptr().cast(),
                2,
                t.as_mut_ptr().cast(),
            );
        }
        let prod = read(&mut r, 3);
        assert_eq!(num(&prod), num(&a) * num(&b));
        // (prod + 5) / b == a, remainder 5 (`b` not normalized).
        let b = [5u32, 0x0000_0FFF];
        let bb = buf(&b, 2);
        let mut rb = buf(&[], 3);
        let mut t = buf(&[], rok_nat_mul_scratch(1, 2));
        // SAFETY: as above.
        unsafe {
            rok_nat_mul(
                rb.as_mut_ptr().cast(),
                ab.as_mut_ptr().cast(),
                1,
                bb.as_ptr().cast_mut().cast(),
                2,
                t.as_mut_ptr().cast(),
            );
        }
        let mut prod = read(&mut rb, 3);
        prod[0] += 5;
        let mut un = buf(&prod, 3);
        let (mut q, mut rem) = (buf(&[], 2), buf(&[], 2));
        let mut t = buf(&[], rok_nat_divmod_scratch(3, 2));
        let mut bb = bb;
        // SAFETY: as above.
        unsafe {
            rok_nat_divmod(
                q.as_mut_ptr().cast(),
                rem.as_mut_ptr().cast(),
                un.as_mut_ptr().cast(),
                3,
                bb.as_mut_ptr().cast(),
                2,
                t.as_mut_ptr().cast(),
            );
        }
        assert_eq!(num(&read(&mut q, 2)), num(&a));
        assert_eq!(num(&read(&mut rem, 2)), 5);
        let mut sq = buf(&[], 1);
        // SAFETY: as above.
        let rem =
            unsafe { rok_nat_divmod_small(sq.as_mut_ptr().cast(), ab.as_mut_ptr().cast(), 1, 10) };
        assert_eq!(num(&read(&mut sq, 1)) * 10 + u128::from(rem), num(&a));
    }
}

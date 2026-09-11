//! Seeded fuzz loops over the string / number / format helpers, each
//! against a Rust std oracle. Budget `ROK_FUZZ_SECS` (default 1),
//! seed `ROK_FUZZ_SEED`.

use std::time::{Duration, Instant};

use crate::str::{
    RokStr, rok_str_char_count, rok_str_concat, rok_str_eq_at, rok_str_find, rok_str_parse_float,
    rok_str_parse_int, rok_str_replace, rok_str_rfind, rok_str_slice, text,
};
use crate::unicode::{rok_str_case, rok_str_trim};
use rokr_common::object_header::HEADER_SIZE;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn budget() -> Duration {
    let secs = std::env::var("ROK_FUZZ_SECS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1.0_f64);
    Duration::from_secs_f64(secs)
}

fn seed() -> u64 {
    std::env::var("ROK_FUZZ_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x0005_eed0_0f0e)
}

/// `f(rng)` for inputs `0..` until the budget; `f` asserts.
fn fuzz(name: &str, max: u64, f: &mut dyn FnMut(&mut Rng)) {
    let deadline = Instant::now() + budget();
    let mut i = 0;
    while i < max && Instant::now() < deadline {
        let mut rng = Rng(seed() ^ i.wrapping_mul(0xa076_1d64_78bd_642f));
        f(&mut rng);
        i += 1;
    }
    std::println!("{name}: {i} inputs, seed {}", seed());
}

const fn rs(s: &str) -> RokStr {
    RokStr {
        ptr: s.as_ptr(),
        len: s.len(),
    }
}

/// Strings over a small alphabet, so patterns recur.
fn word(rng: &mut Rng, max: usize) -> String {
    const ALPHA: &[&str] = &[
        "a", "b", "ab", " ", "\t", "\n", "é", "한", "😀", "\u{a0}", "\u{2003}", "\u{3000}", "Σ",
        "ß", "İ", "ﬃ", "ǅ", "\u{1c}",
    ];
    (0..rng.below(max + 1))
        .map(|_| ALPHA[rng.below(ALPHA.len())])
        .collect()
}

#[test]
fn search_trim_count() {
    fuzz("str search", u64::MAX, &mut |rng| {
        let h = word(rng, 12);
        let n = word(rng, 3);
        let want = |o: Option<usize>| o.map_or(-1, |i| i as isize);
        assert_eq!(
            rok_str_find(rs(&h), rs(&n)),
            want(h.find(&n)),
            "find {h:?} {n:?}"
        );
        assert_eq!(
            rok_str_rfind(rs(&h), rs(&n)),
            want(h.rfind(&n)),
            "rfind {h:?} {n:?}"
        );
        assert_eq!(rok_str_char_count(rs(&h)), h.chars().count(), "{h:?}");
        let at = rng.below(h.len() + 2);
        let eq = h
            .as_bytes()
            .get(at..)
            .is_some_and(|r| r.starts_with(n.as_bytes()));
        assert_eq!(
            rok_str_eq_at(rs(&h), at, rs(&n)) != 0,
            eq,
            "eq_at {h:?} {at} {n:?}"
        );
        for (which, want) in [(0, h.trim()), (1, h.trim_start()), (2, h.trim_end())] {
            let got = rok_str_trim(rs(&h), which);
            assert_eq!(text(&got), want, "trim {which} {h:?}");
        }
    });
}

#[test]
fn parse_int_and_float() {
    #[repr(align(16))]
    struct Out([u8; HEADER_SIZE + 8]);
    let mut o = Out([0; HEADER_SIZE + 8]);
    fuzz("str parse", u64::MAX, &mut |rng| {
        const BITS: &[&str] = &[
            "0",
            "1",
            "7",
            "9",
            "a",
            "F",
            "z",
            "-",
            "+",
            "_",
            " ",
            "e",
            "E",
            ".",
            "inf",
            "NaN",
            "99999999999",
            "18446744073709551615",
        ];
        let s: String = (0..rng.below(6))
            .map(|_| BITS[rng.below(BITS.len())])
            .collect();
        let radix = [2u32, 8, 10, 16, 36][rng.below(5)];
        let signed = rng.below(2) as i32;
        let bits = [8u32, 16, 32, 64][rng.below(4)];
        // SAFETY: `o` holds one element after the header.
        let st = unsafe { rok_str_parse_int(rs(&s), radix, signed, bits, o.0.as_mut_ptr()) };
        let got = i64::from_ne_bytes(o.0[HEADER_SIZE..].try_into().unwrap());
        // Oracle: i128 parse (sign then digits), then the type's range;
        // no `-` on an unsigned type (`-0` too, as Rust).
        let digits = s.strip_prefix(['-', '+']).unwrap_or(&s);
        let want = i128::from_str_radix(&s, radix)
            .ok()
            .filter(|_| !digits.starts_with(['-', '+']))
            .filter(|_| signed != 0 || !s.starts_with('-'))
            .filter(|&v| {
                let (lo, hi) = if signed != 0 {
                    (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
                } else {
                    (0, (1i128 << bits) - 1)
                };
                (lo..=hi).contains(&v)
            });
        match want {
            Some(v) => assert_eq!(
                (st, got),
                (0, v as i64),
                "{s:?} radix {radix} {signed} {bits}"
            ),
            None => assert_ne!(st, 0, "{s:?} radix {radix} signed {signed} bits {bits}"),
        }

        // SAFETY: as above.
        let st = unsafe { rok_str_parse_float(rs(&s), o.0.as_mut_ptr()) };
        let got = f64::from_ne_bytes(o.0[HEADER_SIZE..].try_into().unwrap());
        match s.parse::<f64>() {
            Ok(v) => assert!(
                st == 0 && (got.to_bits() == v.to_bits() || got.is_nan() && v.is_nan()),
                "{s:?}"
            ),
            Err(_) => assert_ne!(st, 0, "{s:?}"),
        }
    });
    fuzz("fmt spec", u64::MAX, &mut |rng| {
        const BITS: &[&str] = &[
            "<", ">", "^", "=", "+", "-", " ", "#", "0", "1", "9", ".", "x", "X", "e", "f", "?",
            "*", "é", "{", "}", "$", "q",
        ];
        let s: String = (0..rng.below(8))
            .map(|_| BITS[rng.below(BITS.len())])
            .collect();
        // Must return, never panic.
        let _ = crate::fmt_spec::parse(&s);
    });
}

/// Characters with long-settled case mappings (Unicode <= 13), so the
/// runtime's tables (UCD 18) and std's agree.
fn cased(rng: &mut Rng) -> String {
    const RANGES: &[(u32, u32)] = &[
        (0x20, 0x7f),
        (0xa0, 0x250),
        (0x370, 0x3ff),
        (0x400, 0x530),
        (0x1e00, 0x1fff),
        (0x2160, 0x2190),
        (0x24b6, 0x24ea),
        (0xff21, 0xff5b),
        (0x10400, 0x10450),
    ];
    (0..rng.below(8))
        .filter_map(|_| {
            let (lo, hi) = RANGES[rng.below(RANGES.len())];
            char::from_u32(lo + rng.below((hi - lo) as usize) as u32)
        })
        .collect()
}

/// Inputs per allocating loop: together well under the 4 MiB first
/// collection, which would stop the world with other tests' threads
/// registered.
const ALLOC_INPUTS: u64 = 1500;

/// Allocates: called from the GC test (single mutator).
#[allow(clippy::many_single_char_names)]
pub fn allocating() {
    fuzz("str alloc", ALLOC_INPUTS, &mut |rng| {
        let a = word(rng, 6);
        let b = word(rng, 6);
        assert_eq!(text(&rok_str_concat(rs(&a), rs(&b))), a.clone() + &b);
        let from = word(rng, 2);
        let to = word(rng, 2);
        if !from.is_empty() {
            let got = rok_str_replace(rs(&a), rs(&from), rs(&to));
            assert_eq!(text(&got), a.replace(&from, &to), "{a:?} {from:?} {to:?}");
        }
        let (i, j) = (rng.below(a.len() + 1), rng.below(a.len() + 1));
        if i <= j && a.is_char_boundary(i) && a.is_char_boundary(j) {
            assert_eq!(text(&rok_str_slice(rs(&a), i, j, rs(""))), &a[i..j]);
        }
        let c = cased(rng);
        assert_eq!(
            text(&rok_str_case(rs(&c), 1)),
            c.to_uppercase(),
            "upper {c:?}"
        );
        assert_eq!(
            text(&rok_str_case(rs(&c), 0)),
            c.to_lowercase(),
            "lower {c:?}"
        );
    });
    fuzz("fmt float", ALLOC_INPUTS, &mut |rng| {
        let v = match rng.below(3) {
            0 => f64::from_bits(rng.next()),
            1 => (rng.next() % 1_000_000) as f64 / 1000.0,
            _ => f64::from(f32::from_bits(rng.next() as u32)),
        };
        let show = |is_f32: u32, ty: u8| {
            text(&crate::fmt::rok_fmt_float(v, is_f32, ty.into(), -1)).to_owned()
        };
        // Shortest digits that read back: the Display and `e` forms
        // round-trip, and match std's shortest.
        for ty in [0, b'e'] {
            let t = show(0, ty);
            let back: f64 = t.parse().unwrap_or(f64::NAN);
            assert!(
                back.to_bits() == v.to_bits() || v.is_nan() && back.is_nan(),
                "{v:e}: {t}"
            );
        }
        let x = v as f32;
        if x.is_finite() {
            let t = show(1, 0);
            assert_eq!(t.parse::<f32>().ok(), Some(x), "f32 {x:e}: {t}");
            assert_eq!(t, std::format!("{x}"));
        }
    });
}

//! Symbol mangling (spec 905).
//!
//! `_Y<pkg8>_<path>_<name>_<typehash16>`; concrete items end in `_`
//! (empty typehash). `extern` declarations keep their C name (905.8).
//!
//! Identifier bytes outside `[A-Za-z0-9]` are escaped so the `_`
//! separators stay unambiguous: a literal `_` is `_0`, anything else is
//! `_1<hex codepoint>_`. Identifiers never start with a digit, so a
//! separator `_` is never followed by `0`/`1`. Thus `mod a { fn b }` →
//! `…_a_b_` while a root `fn a__b` → `…__a_0_0b_`.

use rokc_mir::MirFunction;

/// Monomorphized names carry their type arguments after this marker
/// (`first__mono__i32`); they become the typehash.
const MONO_MARK: &str = "__mono__";

/// Linker symbol for a MIR function.
pub fn symbol_for(f: &MirFunction, pkg: &str) -> String {
    if f.blocks.is_empty() {
        return f.name.clone();
    }
    match f.name.split_once(MONO_MARK) {
        Some((base, args)) => item(pkg, base, &hex(&sha256(args.as_bytes()))[..16]),
        None => item(pkg, &f.name, ""),
    }
}

/// Mangle a `::`-qualified item path.
pub fn item(pkg: &str, qualified: &str, typehash: &str) -> String {
    let mut segs: Vec<&str> = qualified.split("::").collect();
    let name = segs.pop().unwrap_or_default();
    let path: Vec<String> = segs.iter().map(|s| escape(s)).collect();
    format!("_Y{pkg}_{}_{}_{typehash}", path.join("_"), escape(name))
}

/// 8-hex-digit package hash over the package's content.
pub fn pkg_hash(content: &str) -> String {
    hex(&sha256(content.as_bytes()))[..8].to_owned()
}

fn escape(ident: &str) -> String {
    let mut out = String::with_capacity(ident.len());
    for ch in ident.chars() {
        match ch {
            'a'..='z' | 'A'..='Z' | '0'..='9' => out.push(ch),
            '_' => out.push_str("_0"),
            _ => out.push_str(&format!("_1{:x}_", u32::from(ch))),
        }
    }
    out
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// FIPS 180-4 SHA-256 (no external crates allowed).
fn sha256(msg: &[u8]) -> [u8; 32] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut data = msg.to_vec();
    data.push(0x80);
    while data.len() % 64 != 56 {
        data.push(0);
    }
    data.extend_from_slice(&((msg.len() as u64) * 8).to_be_bytes());
    for chunk in data.chunks(64) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (x, y) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *x = x.wrapping_add(y);
        }
    }
    let mut out = [0u8; 32];
    for (i, x) in h.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&x.to_be_bytes());
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_known_vectors() {
        assert_eq!(
            hex(&sha256(b"")),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex(&sha256(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn module_path_and_underscore_names_do_not_collide() {
        assert_eq!(item("3f8a1c2b", "a::b", ""), "_Y3f8a1c2b_a_b_");
        assert_eq!(item("3f8a1c2b", "a__b", ""), "_Y3f8a1c2b__a_0_0b_");
        assert_ne!(item("p", "a::b_c", ""), item("p", "a_b::c", ""));
        assert_eq!(item("p", "malloc", ""), "_Yp__malloc_");
    }
}

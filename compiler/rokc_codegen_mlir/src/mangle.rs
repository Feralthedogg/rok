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

use std::fmt::Write as _;

use rokc_ir_common::Linkage;
use rokc_mir::{Link, MirFunction};

/// What symbol naming needs to know about the whole program.
#[derive(Default)]
pub struct Pkgs {
    pub link: Link,
    /// `extern` statics: they keep their C name.
    pub extern_statics: std::collections::HashSet<String>,
    /// Lazily initialized statics: name → symbol of their initializer.
    pub lazy_statics: std::collections::HashMap<String, String>,
}

impl Pkgs {
    /// Linker symbol of static `name`.
    pub fn static_sym(&self, name: &str) -> String {
        if self.extern_statics.contains(name) {
            return name.to_owned();
        }
        item(self.link.hash_of(name), name, "")
    }
}

/// Linker symbol of a MIR function: its `#[export_name]`, its own name
/// (an `extern` declaration), or the mangled path.
pub fn symbol_for(f: &MirFunction, pkgs: &Pkgs) -> String {
    if let Some(sym) = &f.facts.export_name {
        return sym.clone();
    }
    if f.facts.linkage == Linkage::Extern {
        return f.name.clone();
    }
    mangled(f, pkgs)
}

/// The mangled symbol of a MIR function; an instance's type arguments
/// become the typehash.
pub fn mangled(f: &MirFunction, pkgs: &Pkgs) -> String {
    let path = f.path();
    let hash = f
        .facts
        .mono_args
        .as_ref()
        .map(|a| hex(&sha256(a.as_bytes()))[..16].to_owned())
        .unwrap_or_default();
    item(pkgs.link.hash_of(path), path, &hash)
}

/// Mangle a `::`-qualified item path. The package is the hash, so a
/// library's `rok::` root is dropped (`rok::std::vec` → `std_vec`, 905.3).
pub fn item(pkg: &str, qualified: &str, typehash: &str) -> String {
    let qualified = qualified.strip_prefix("rok::").unwrap_or(qualified);
    let mut segs: Vec<&str> = qualified.split("::").collect();
    let name = segs.pop().unwrap_or_default();
    let path: Vec<String> = segs.iter().map(|s| escape(s)).collect();
    format!("_Y{pkg}_{}_{}_{typehash}", path.join("_"), escape(name))
}

/// A string literal's global, named by its content: the same literal
/// has the same name in every module, so a REPL cell's function text
/// compares equal to an earlier cell's (`crate::repl`).
pub fn str_global(text: &str) -> String {
    format!("rok.str.{}", &hex(&sha256(text.as_bytes()))[..16])
}

/// 8-hex-digit package hash over the package's content.
pub fn pkg_hash(content: &str) -> String {
    hex(&sha256(content.as_bytes()))[..8].to_owned()
}

/// A `_Y` symbol taken apart (spec 905.4).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Demangled {
    pub pkg: String,
    /// Module path segments, without the dropped `rok::` / `pkg::` root.
    pub path: Vec<String>,
    pub name: String,
    /// `None` for a concrete (non-generic) item.
    pub typehash: Option<String>,
}

impl Demangled {
    /// `rok::std::vec::push` style. The mangled form drops the root
    /// segment, so a path starting with a library tier (`core` / `std` /
    /// `bare`) gets `rok::` back (a user module named `std` too).
    #[must_use]
    pub fn qualified_path(&self) -> String {
        let mut segs: Vec<&str> = Vec::new();
        if self
            .path
            .first()
            .is_some_and(|s| matches!(s.as_str(), "core" | "std" | "bare"))
        {
            segs.push("rok");
        }
        segs.extend(self.path.iter().map(String::as_str));
        segs.join("::")
    }

    /// `rok::std::vec::push` (path + name).
    #[must_use]
    pub fn qualified_name(&self) -> String {
        let path = self.qualified_path();
        if path.is_empty() {
            self.name.clone()
        } else {
            format!("{path}::{}", self.name)
        }
    }
}

/// Inverse of [`item`]: `None` when `sym` is not a well-formed `_Y`
/// symbol (including the reserved `_YK` / `_YL` / `_YI` / `_YM`).
#[must_use]
pub fn demangle(sym: &str) -> Option<Demangled> {
    let rest = sym.strip_prefix("_Y")?;
    let is_hex = |s: &str| s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
    let (pkg, rest) = (rest.get(..8)?, rest.get(8..)?);
    if !is_hex(pkg) {
        return None;
    }
    let rest = rest.strip_prefix('_')?;
    // A typehash is 16 hex digits after the last separator; a concrete
    // item ends in the separator (empty typehash) or, per 905.2, omits it.
    let (body, typehash) = if let Some(b) = rest.strip_suffix('_') {
        (b, None)
    } else {
        match rest.len().checked_sub(17).map(|i| rest.split_at(i)) {
            Some((b, h)) if h.starts_with('_') && is_hex(&h[1..]) => (b, Some(h[1..].to_owned())),
            _ => (rest, None),
        }
    };
    // `_0` is `_`, `_1<hex>_` a code point, any other `_` a separator.
    let mut segs = vec![String::new()];
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '_' {
            segs.last_mut()?.push(c);
            continue;
        }
        match chars.peek() {
            Some('0') => {
                chars.next();
                segs.last_mut()?.push('_');
            }
            Some('1') => {
                chars.next();
                let hex: String = chars.by_ref().take_while(|&c| c != '_').collect();
                segs.last_mut()?
                    .push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
            }
            _ => segs.push(String::new()),
        }
    }
    let name = segs.pop()?;
    // An empty path mangles as one empty segment (`_Yp__name_`).
    if segs.len() == 1 && segs[0].is_empty() {
        segs.clear();
    }
    if name.is_empty() || segs.iter().any(String::is_empty) {
        return None;
    }
    Some(Demangled {
        pkg: pkg.to_owned(),
        path: segs,
        name,
        typehash,
    })
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
    bytes.iter().fold(String::new(), |mut out, b| {
        let _ = write!(out, "{b:02x}");
        out
    })
}

/// FIPS 180-4 SHA-256 (no external crates allowed).
#[allow(clippy::many_single_char_names)] // a..h, w, k follow the FIPS 180-4 names
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
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
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
        assert_eq!(item("p", "rok::std::vec::new", ""), "_Yp_std_vec_new_");
        let link = Link {
            packages: vec![
                ("rok::core".to_owned(), "c".to_owned()),
                (String::new(), "u".to_owned()),
            ],
            ..Link::default()
        };
        assert_eq!(link.hash_of("rok::core::str::len"), "c");
        assert_eq!(link.hash_of("rok::corex::f"), "u");
        assert_eq!(link.hash_of("main"), "u");
    }

    #[test]
    fn demangle_round_trips() {
        for (q, th) in [
            ("a::b", ""),
            ("a__b", ""),
            ("malloc", ""),
            ("rok::std::vec::push", "a7c91d8e44b2f190"),
            ("geom::α", "0123456789abcdef"),
            ("x_1::_y", ""),
        ] {
            let sym = item("3f8a1c2b", q, th);
            let d = demangle(&sym).unwrap_or_else(|| panic!("{sym}"));
            assert_eq!(d.qualified_name(), q, "{sym}");
            assert_eq!(d.typehash.as_deref().unwrap_or(""), th, "{sym}");
        }
        let d = demangle("_Y3f8a1c2b_geom_compute_main").unwrap();
        assert_eq!(d.qualified_name(), "geom::compute::main");
        assert_eq!(d.typehash, None);
        assert!(demangle("_YK00000000_x_").is_none());
        assert!(demangle("_ZN3foo").is_none());
    }
}

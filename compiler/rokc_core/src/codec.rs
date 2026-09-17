//! A compact binary encoding of compiler data (the incremental caches,
//! spec 9.2.16).
//!
//! LEB128 integers, length-prefixed strings and lists. `Codec` is
//! implemented next to each type, mostly by `codec_struct!` and
//! `codec_enum!`. A decode that fails yields `None`: a cache miss.

use std::collections::HashMap;

/// An encoder.
pub struct Enc {
    pub buf: Vec<u8>,
    /// `false`: source positions are left out (a position-independent
    /// fingerprint).
    pub spans: bool,
    /// The source file ids of the spans encoded.
    pub files: Vec<u32>,
    /// A stretch of one file (file id, start, end): `foreign` gets the
    /// files of the spans encoded outside it, each with the furthest end
    /// of those spans.
    pub home: Option<(u32, u32, u32)>,
    pub foreign: Vec<(u32, u32)>,
    /// When set, gets every id written by `Enc::id`.
    pub ids: Option<Vec<(IdKind, u32)>>,
}

impl Enc {
    #[must_use]
    pub const fn new(spans: bool) -> Self {
        Self {
            buf: Vec::new(),
            spans,
            files: Vec::new(),
            home: None,
            foreign: Vec::new(),
            ids: None,
        }
    }

    /// Write id `v` of `kind` (read back by `Dec::id`).
    pub fn id(&mut self, kind: IdKind, v: u32) {
        if let Some(ids) = &mut self.ids {
            ids.push((kind, v));
        }
        self.u(u64::from(v));
    }

    pub fn u(&mut self, mut v: u64) {
        loop {
            let b = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                self.buf.push(b);
                return;
            }
            self.buf.push(b | 0x80);
        }
    }

    #[allow(clippy::cast_sign_loss)]
    pub fn i(&mut self, v: i64) {
        self.u(((v << 1) ^ (v >> 63)) as u64);
    }

    pub fn bytes(&mut self, b: &[u8]) {
        self.u(b.len() as u64);
        self.buf.extend_from_slice(b);
    }
}

/// What an id read by `Dec::id` numbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IdKind {
    Function,
    Struct,
    Enum,
    /// A `let` inference variable.
    InferVar,
}

/// Renumbers the ids of an encoding for this build (`None`: no such id
/// here, the decode fails).
pub type IdMap<'a> = &'a dyn Fn(IdKind, u32) -> Option<u32>;

/// A decoder. `files` maps the encoded source file ids to this build's
/// (index: old id); an id not in it fails the decode. `ids` renumbers
/// the other ids.
pub struct Dec<'a> {
    buf: &'a [u8],
    pos: usize,
    pub files: Option<&'a [u32]>,
    pub ids: Option<IdMap<'a>>,
}

impl<'a> Dec<'a> {
    #[must_use]
    pub const fn new(buf: &'a [u8]) -> Self {
        Self {
            buf,
            pos: 0,
            files: None,
            ids: None,
        }
    }

    /// The bytes not read yet.
    #[must_use]
    pub const fn rest(&self) -> usize {
        self.buf.len() - self.pos
    }

    #[must_use]
    pub const fn done(&self) -> bool {
        self.pos == self.buf.len()
    }

    pub fn u(&mut self) -> Option<u64> {
        let mut v = 0u64;
        let mut shift = 0;
        loop {
            let b = *self.buf.get(self.pos)?;
            self.pos += 1;
            v |= u64::from(b & 0x7f).checked_shl(shift)?;
            if b & 0x80 == 0 {
                return Some(v);
            }
            shift += 7;
        }
    }

    #[allow(clippy::cast_possible_wrap)]
    pub fn i(&mut self) -> Option<i64> {
        let v = self.u()?;
        Some((v >> 1) as i64 ^ -((v & 1) as i64))
    }

    pub fn bytes(&mut self) -> Option<&'a [u8]> {
        let n = usize::try_from(self.u()?).ok()?;
        let end = self.pos.checked_add(n)?;
        let b = self.buf.get(self.pos..end)?;
        self.pos = end;
        Some(b)
    }

    /// An id of `kind`, as this build numbers it.
    pub fn id(&mut self, kind: IdKind) -> Option<u32> {
        let v = u32::try_from(self.u()?).ok()?;
        match self.ids {
            Some(map) => map(kind, v),
            None => Some(v),
        }
    }

    /// A source file id of the encoding, as this build numbers it.
    pub fn file(&self, id: u32) -> Option<u32> {
        match self.files {
            Some(map) if id != 0 => map.get(id as usize).copied().filter(|&n| n != 0),
            _ => Some(id),
        }
    }
}

pub trait Codec: Sized {
    fn enc(&self, e: &mut Enc);
    fn dec(d: &mut Dec<'_>) -> Option<Self>;
}

macro_rules! codec_uint {
    ($($t:ty),*) => {$(
        impl Codec for $t {
            fn enc(&self, e: &mut Enc) {
                e.u(u64::from(*self));
            }
            fn dec(d: &mut Dec<'_>) -> Option<Self> {
                Self::try_from(d.u()?).ok()
            }
        }
    )*};
}
codec_uint!(u8, u16, u32, u64);

macro_rules! codec_int {
    ($($t:ty),*) => {$(
        impl Codec for $t {
            fn enc(&self, e: &mut Enc) {
                e.i(i64::from(*self));
            }
            fn dec(d: &mut Dec<'_>) -> Option<Self> {
                Self::try_from(d.i()?).ok()
            }
        }
    )*};
}
codec_int!(i8, i16, i32, i64);

impl Codec for usize {
    fn enc(&self, e: &mut Enc) {
        e.u(*self as u64);
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Self::try_from(d.u()?).ok()
    }
}

impl Codec for i128 {
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    fn enc(&self, e: &mut Enc) {
        e.u(*self as u64);
        e.u((*self >> 64) as u64);
    }
    #[allow(clippy::cast_possible_wrap)]
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        let lo = d.u()?;
        let hi = d.u()?;
        Some(((u128::from(hi) << 64) | u128::from(lo)) as Self)
    }
}

#[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
impl Codec for u128 {
    fn enc(&self, e: &mut Enc) {
        (*self as i128).enc(e);
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Some(i128::dec(d)? as Self)
    }
}

impl Codec for f64 {
    fn enc(&self, e: &mut Enc) {
        e.u(self.to_bits());
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Some(Self::from_bits(d.u()?))
    }
}

impl Codec for bool {
    fn enc(&self, e: &mut Enc) {
        e.buf.push(u8::from(*self));
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        match d.u()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }
}

impl Codec for char {
    fn enc(&self, e: &mut Enc) {
        e.u(u64::from(*self));
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Self::from_u32(u32::try_from(d.u()?).ok()?)
    }
}

impl Codec for String {
    fn enc(&self, e: &mut Enc) {
        e.bytes(self.as_bytes());
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        std::str::from_utf8(d.bytes()?).ok().map(str::to_owned)
    }
}

impl Codec for std::path::PathBuf {
    fn enc(&self, e: &mut Enc) {
        e.bytes(self.to_string_lossy().as_bytes());
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        String::dec(d).map(Self::from)
    }
}

/// Interned: each distinct text is leaked once.
impl Codec for &'static str {
    fn enc(&self, e: &mut Enc) {
        e.bytes(self.as_bytes());
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        static TEXTS: std::sync::Mutex<Vec<&'static str>> = std::sync::Mutex::new(Vec::new());
        let s = std::str::from_utf8(d.bytes()?).ok()?;
        let mut texts = TEXTS
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(t) = texts.iter().find(|t| **t == s) {
            return Some(t);
        }
        let t: &'static str = Box::leak(s.to_owned().into_boxed_str());
        texts.push(t);
        drop(texts);
        Some(t)
    }
}

impl<T: Codec> Codec for Vec<T> {
    fn enc(&self, e: &mut Enc) {
        e.u(self.len() as u64);
        for x in self {
            x.enc(e);
        }
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        let n = usize::try_from(d.u()?).ok()?;
        // A corrupt length fails at the end of the input, not here.
        let mut v = Self::with_capacity(n.min(1 << 16));
        for _ in 0..n {
            v.push(T::dec(d)?);
        }
        Some(v)
    }
}

impl<T: Codec> Codec for Option<T> {
    fn enc(&self, e: &mut Enc) {
        match self {
            None => e.buf.push(0),
            Some(x) => {
                e.buf.push(1);
                x.enc(e);
            }
        }
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        match d.u()? {
            0 => Some(None),
            1 => Some(Some(T::dec(d)?)),
            _ => None,
        }
    }
}

impl<T: Codec> Codec for Box<T> {
    fn enc(&self, e: &mut Enc) {
        (**self).enc(e);
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        T::dec(d).map(Self::new)
    }
}

impl<T: Codec> Codec for std::sync::Arc<T> {
    fn enc(&self, e: &mut Enc) {
        (**self).enc(e);
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        T::dec(d).map(Self::new)
    }
}

impl<A: Codec, B: Codec> Codec for (A, B) {
    fn enc(&self, e: &mut Enc) {
        self.0.enc(e);
        self.1.enc(e);
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Some((A::dec(d)?, B::dec(d)?))
    }
}

impl<A: Codec, B: Codec, C: Codec> Codec for (A, B, C) {
    fn enc(&self, e: &mut Enc) {
        self.0.enc(e);
        self.1.enc(e);
        self.2.enc(e);
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Some((A::dec(d)?, B::dec(d)?, C::dec(d)?))
    }
}

impl<A: Codec, B: Codec, C: Codec, D: Codec> Codec for (A, B, C, D) {
    fn enc(&self, e: &mut Enc) {
        self.0.enc(e);
        self.1.enc(e);
        self.2.enc(e);
        self.3.enc(e);
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Some((A::dec(d)?, B::dec(d)?, C::dec(d)?, D::dec(d)?))
    }
}

impl<const N: usize, T: Codec> Codec for [T; N] {
    fn enc(&self, e: &mut Enc) {
        for x in self {
            x.enc(e);
        }
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        let v: Vec<T> = (0..N).map(|_| T::dec(d)).collect::<Option<_>>()?;
        v.try_into().ok()
    }
}

/// A map in key order (so equal maps encode equally).
impl<K, V, S> Codec for HashMap<K, V, S>
where
    K: Codec + Ord + Eq + std::hash::Hash,
    V: Codec,
    S: std::hash::BuildHasher + Default,
{
    fn enc(&self, e: &mut Enc) {
        let mut entries: Vec<(&K, &V)> = self.iter().collect();
        entries.sort_by(|a, b| a.0.cmp(b.0));
        e.u(entries.len() as u64);
        for (k, v) in entries {
            k.enc(e);
            v.enc(e);
        }
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Vec::<(K, V)>::dec(d).map(|v| v.into_iter().collect())
    }
}

impl<K, S> Codec for std::collections::HashSet<K, S>
where
    K: Codec + Ord + Eq + std::hash::Hash,
    S: std::hash::BuildHasher + Default,
{
    fn enc(&self, e: &mut Enc) {
        let mut keys: Vec<&K> = self.iter().collect();
        keys.sort();
        e.u(keys.len() as u64);
        for k in keys {
            k.enc(e);
        }
    }
    fn dec(d: &mut Dec<'_>) -> Option<Self> {
        Vec::<K>::dec(d).map(|v| v.into_iter().collect())
    }
}

/// `Codec` for a struct by its fields:
/// `codec_struct!(Point { x, y });`
#[macro_export]
macro_rules! codec_struct {
    ($t:ident { $($f:ident),* $(,)? }) => {
        impl $crate::codec::Codec for $t {
            fn enc(&self, e: &mut $crate::codec::Enc) {
                $( $crate::codec::Codec::enc(&self.$f, e); )*
            }
            fn dec(d: &mut $crate::codec::Dec<'_>) -> Option<Self> {
                Some(Self { $( $f: $crate::codec::Codec::dec(d)?, )* })
            }
        }
    };
}

/// `Codec` for an enum by its variants, each written as its pattern
/// (tuple fields named): `codec_enum!(E { A, B(x, y), C { f } });`
#[macro_export]
macro_rules! codec_enum {
    ($t:ident { $($v:ident $( ( $($p:ident),* ) )? $( { $($f:ident),* } )?),* $(,)? }) => {
        impl $crate::codec::Codec for $t {
            #[allow(unused_assignments, unused_variables, clippy::equatable_if_let)]
            fn enc(&self, e: &mut $crate::codec::Enc) {
                let mut tag = 0u64;
                $(
                    if let Self::$v $( ( $($p),* ) )? $( { $($f),* } )? = self {
                        e.u(tag);
                        $( $( $crate::codec::Codec::enc($p, e); )* )?
                        $( $( $crate::codec::Codec::enc($f, e); )* )?
                        return;
                    }
                    tag += 1;
                )*
            }
            #[allow(unused_assignments)]
            fn dec(d: &mut $crate::codec::Dec<'_>) -> Option<Self> {
                // Every variant is listed (a new one fails to compile).
                let _ = |x: &Self| match x {
                    $( Self::$v { .. } => {} )*
                };
                let want = d.u()?;
                let mut tag = 0u64;
                $(
                    if want == tag {
                        return Some(Self::$v
                            $( ( $( $crate::codec_field!($p, d) ),* ) )?
                            $( { $( $f: $crate::codec::Codec::dec(d)? ),* } )?);
                    }
                    tag += 1;
                )*
                None
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! codec_field {
    ($p:ident, $d:ident) => {
        $crate::codec::Codec::dec($d)?
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq)]
    struct P {
        a: u32,
        b: Vec<String>,
        c: Option<Box<E>>,
    }
    #[derive(Debug, PartialEq)]
    enum E {
        Unit,
        Tup(i64, bool),
        Named { x: f64, y: char },
    }
    codec_struct!(P { a, b, c });
    codec_enum!(E { Unit, Tup(a, b), Named { x, y } });

    #[test]
    fn round_trip() {
        for e in [E::Unit, E::Tup(-5, true), E::Named { x: 1.5, y: 'λ' }] {
            let p = P {
                a: 300,
                b: vec!["x".into(), String::new()],
                c: Some(Box::new(e)),
            };
            let mut enc = Enc::new(true);
            p.enc(&mut enc);
            let mut d = Dec::new(&enc.buf);
            assert_eq!(P::dec(&mut d), Some(p));
            assert!(d.done());
        }
        let mut enc = Enc::new(true);
        (i128::MIN, i64::MIN, u64::MAX).enc(&mut enc);
        assert_eq!(
            <(i128, i64, u64)>::dec(&mut Dec::new(&enc.buf)),
            Some((i128::MIN, i64::MIN, u64::MAX))
        );
        assert_eq!(P::dec(&mut Dec::new(&enc.buf[..3])), None);
    }
}

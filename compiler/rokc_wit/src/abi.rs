//! The canonical ABI's layout of WIT values (component model
//! `CanonicalABI.md`, 32-bit memory): size, alignment and flat (core
//! value) form.

use crate::parse::Prim;
use crate::resolve::{Resolve, Type, TypeKind};

/// A core wasm value type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flat {
    I32,
    I64,
    F32,
    F64,
}

impl Flat {
    pub const fn rok(self) -> &'static str {
        match self {
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }

    /// Two cases' slot, joined.
    const fn join(self, other: Self) -> Self {
        match (self, other) {
            (a, b) if a as u8 == b as u8 => a,
            (Self::I32 | Self::F32, Self::I32 | Self::F32) => Self::I32,
            _ => Self::I64,
        }
    }
}

pub const MAX_FLAT_PARAMS: usize = 16;
pub const MAX_FLAT_RESULTS: usize = 1;

pub const fn align_to(x: u32, a: u32) -> u32 {
    x.div_ceil(a) * a
}

/// The cases of a variant-like type: `option`, `result` and `enum`
/// despecialized.
pub fn cases(r: &Resolve, t: &Type) -> Option<Vec<Option<Type>>> {
    match t {
        Type::Option(t) => Some(vec![None, Some((**t).clone())]),
        Type::Result(a, b) => Some(vec![a.as_deref().cloned(), b.as_deref().cloned()]),
        Type::Id(id) => match &r.types[r.dealias(*id)].kind {
            TypeKind::Variant(cs) => Some(cs.iter().map(|(_, t)| t.clone()).collect()),
            TypeKind::Enum(cs) => Some(vec![None; cs.len()]),
            _ => None,
        },
        _ => None,
    }
}

/// The fields of a record-like type (`tuple` too).
pub fn fields(r: &Resolve, t: &Type) -> Option<Vec<Type>> {
    match t {
        Type::Tuple(ts) => Some(ts.clone()),
        Type::Id(id) => match &r.types[r.dealias(*id)].kind {
            TypeKind::Record(fs) => Some(fs.iter().map(|(_, t)| t.clone()).collect()),
            _ => None,
        },
        _ => None,
    }
}

/// The flag count of a `flags` type.
pub fn flag_count(r: &Resolve, t: &Type) -> Option<usize> {
    match t {
        Type::Id(id) => match &r.types[r.dealias(*id)].kind {
            TypeKind::Flags(f) => Some(f.len()),
            _ => None,
        },
        _ => None,
    }
}

/// Width in bytes of a discriminant for `n` cases.
pub const fn disc_size(n: usize) -> u32 {
    if n <= 1 << 8 {
        1
    } else if n <= 1 << 16 {
        2
    } else {
        4
    }
}

/// Size of `n` flags in bytes.
pub const fn flags_size(n: usize) -> u32 {
    if n == 0 {
        0
    } else if n <= 8 {
        1
    } else if n <= 16 {
        2
    } else {
        4
    }
}

pub fn align(r: &Resolve, t: &Type) -> u32 {
    match t {
        Type::Prim(p) => match p {
            Prim::Bool | Prim::U8 | Prim::S8 => 1,
            Prim::U16 | Prim::S16 => 2,
            Prim::U32 | Prim::S32 | Prim::F32 | Prim::Char | Prim::String => 4,
            Prim::U64 | Prim::S64 | Prim::F64 => 8,
        },
        Type::List(_)
        | Type::Own(_)
        | Type::Borrow(_)
        | Type::Future(_)
        | Type::Stream(_)
        | Type::ErrorContext => 4,
        Type::FixedList(e, _) => align(r, e),
        _ => {
            if let Some(fs) = fields(r, t) {
                return fs.iter().map(|f| align(r, f)).max().unwrap_or(1);
            }
            if let Some(cs) = cases(r, t) {
                let payload = cs.iter().flatten().map(|c| align(r, c)).max().unwrap_or(1);
                return disc_size(cs.len()).max(payload);
            }
            if let Some(n) = flag_count(r, t) {
                return flags_size(n).max(1);
            }
            if let Type::Id(id) = t {
                if let TypeKind::Alias(a) = &r.types[r.dealias(*id)].kind {
                    return align(r, a);
                }
            }
            4
        }
    }
}

pub fn size(r: &Resolve, t: &Type) -> u32 {
    match t {
        Type::Prim(p) => match p {
            Prim::Bool | Prim::U8 | Prim::S8 => 1,
            Prim::U16 | Prim::S16 => 2,
            Prim::U32 | Prim::S32 | Prim::F32 | Prim::Char => 4,
            Prim::U64 | Prim::S64 | Prim::F64 | Prim::String => 8,
        },
        Type::List(_) => 8,
        Type::Own(_) | Type::Borrow(_) | Type::Future(_) | Type::Stream(_) | Type::ErrorContext => {
            4
        }
        Type::FixedList(e, n) => size(r, e) * n,
        _ => {
            if let Some(fs) = fields(r, t) {
                let mut s = 0;
                for f in &fs {
                    s = align_to(s, align(r, f)) + size(r, f);
                }
                return align_to(s, align(r, t));
            }
            if let Some(cs) = cases(r, t) {
                let s = payload_offset(r, &cs)
                    + cs.iter().flatten().map(|c| size(r, c)).max().unwrap_or(0);
                return align_to(s, align(r, t));
            }
            if let Some(n) = flag_count(r, t) {
                return flags_size(n);
            }
            if let Type::Id(id) = t {
                if let TypeKind::Alias(a) = &r.types[r.dealias(*id)].kind {
                    return size(r, a);
                }
            }
            4
        }
    }
}

/// Offset of a variant's payload: past the discriminant, aligned for
/// the widest case.
pub fn payload_offset(r: &Resolve, cs: &[Option<Type>]) -> u32 {
    let payload = cs.iter().flatten().map(|c| align(r, c)).max().unwrap_or(1);
    align_to(disc_size(cs.len()), payload)
}

/// Offsets of a record's fields.
pub fn field_offsets(r: &Resolve, fs: &[Type]) -> Vec<u32> {
    let mut s = 0;
    fs.iter()
        .map(|f| {
            s = align_to(s, align(r, f));
            let at = s;
            s += size(r, f);
            at
        })
        .collect()
}

pub fn flatten(r: &Resolve, t: &Type) -> Vec<Flat> {
    match t {
        Type::Prim(p) => vec![match p {
            Prim::U64 | Prim::S64 => Flat::I64,
            Prim::F32 => Flat::F32,
            Prim::F64 => Flat::F64,
            Prim::String => return vec![Flat::I32, Flat::I32],
            _ => Flat::I32,
        }],
        Type::List(_) => vec![Flat::I32, Flat::I32],
        Type::Own(_) | Type::Borrow(_) | Type::Future(_) | Type::Stream(_) | Type::ErrorContext => {
            vec![Flat::I32]
        }
        Type::FixedList(e, n) => {
            let one = flatten(r, e);
            // Past the limit the count only has to be "too many".
            let n = (*n as usize).min(MAX_FLAT_PARAMS + 1);
            one.iter().copied().cycle().take(one.len() * n).collect()
        }
        _ => {
            if let Some(fs) = fields(r, t) {
                return fs.iter().flat_map(|f| flatten(r, f)).collect();
            }
            if let Some(cs) = cases(r, t) {
                return flatten_cases(r, &cs);
            }
            if let Some(n) = flag_count(r, t) {
                return vec![Flat::I32; n.div_ceil(32)];
            }
            if let Type::Id(id) = t {
                if let TypeKind::Alias(a) = &r.types[r.dealias(*id)].kind {
                    return flatten(r, a);
                }
            }
            vec![Flat::I32]
        }
    }
}

/// A variant's flat form: the discriminant, then each slot joined over
/// the cases.
pub fn flatten_cases(r: &Resolve, cs: &[Option<Type>]) -> Vec<Flat> {
    let mut slots: Vec<Flat> = Vec::new();
    for c in cs.iter().flatten() {
        for (i, f) in flatten(r, c).into_iter().enumerate() {
            match slots.get_mut(i) {
                Some(s) => *s = s.join(f),
                None => slots.push(f),
            }
        }
    }
    let mut out = vec![Flat::I32];
    out.extend(slots);
    out
}

//! Shared IR primitives used by HIR and MIR.

use rokc_core::DefId;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlockId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LocalId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FunctionId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PrimTy {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
    F32,
    F64,
    Bool,
    /// C `char` (FFI; `c'A'`).
    CChar,
    /// Unicode scalar value (`'가'`); 32-bit code point (spec 808).
    Char,
    /// stdlib `str` (UTF-8 view, primitive).
    Str,
}

impl PrimTy {
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::Isize => "isize",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Usize => "usize",
            Self::F32 => "f32",
            Self::F64 => "f64",
            Self::Bool => "bool",
            Self::CChar => "c_char",
            Self::Char => "char",
            Self::Str => "str",
        }
    }

    #[must_use]
    pub const fn is_signed_int(self) -> bool {
        matches!(
            self,
            Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::Isize
        )
    }

    #[must_use]
    pub const fn is_unsigned_int(self) -> bool {
        matches!(
            self,
            Self::U8 | Self::U16 | Self::U32 | Self::U64 | Self::Usize
        )
    }

    #[must_use]
    pub const fn is_int(self) -> bool {
        self.is_signed_int() || self.is_unsigned_int() || matches!(self, Self::CChar | Self::Char)
    }

    #[must_use]
    pub const fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }

    /// Bit width given the target pointer width (32 or 64).
    /// Returns 0 for `Str` since it lowers to (ptr, len).
    #[must_use]
    pub const fn bit_width(self, pointer_width: u32) -> u32 {
        match self {
            Self::I8 | Self::U8 | Self::Bool | Self::CChar => 8,
            Self::I16 | Self::U16 => 16,
            Self::I32 | Self::U32 | Self::F32 | Self::Char => 32,
            Self::I64 | Self::U64 | Self::F64 => 64,
            Self::Isize | Self::Usize => pointer_width,
            Self::Str => 0,
        }
    }
}

/// Primitive op after stdlib-trait desugaring.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
    Not,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    LogicalAnd,
    LogicalOr,
    LogicalNot,
    /// Square root (floats; `rok.sqrt.TYPE`, `√`).
    Sqrt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstVal {
    Unit,
    Bool(bool),
    Int { value: i128, ty: PrimTy },
    UInt { value: u128, ty: PrimTy },
    Float { bits: u64, ty: PrimTy },
    Char(u32),
    Str(String),
    None,
}

/// Runtime extern whose `fn` parameters take whole rok function values.
///
/// That is `{code, env}`, so closures are allowed; every other extern's
/// `fn` parameter is a thin C callback.
// ponytail: decided by symbol name like `str`'s ABI; an ABI field on
// extern declarations replaces both.
#[must_use]
pub fn takes_rok_fn_values(extern_name: &str) -> bool {
    extern_name == "rok_thread_spawn"
}

/// Callee form after name resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedFn {
    /// Statically resolved.
    Free(DefId),
    /// any-slot or sum-type narrowing path; resolved at runtime.
    Dynamic(String),
}

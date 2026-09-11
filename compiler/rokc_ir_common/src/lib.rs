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
    /// Integer `+ - *` that wrap even where overflow checks are on
    /// (`rok.wrapping_add.TYPE` ..; the `wrapping_*` methods).
    WrappingAdd,
    WrappingSub,
    WrappingMul,
    /// Bit counts / byte swap on integers, same type in and out
    /// (`rok.ctpop` / `rok.ctlz` / `rok.cttz` / `rok.bswap`).
    CountOnes,
    LeadingZeros,
    TrailingZeros,
    SwapBytes,
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

/// Calling convention of a function.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Abi {
    /// rok's own: `str` is `(ptr, len)` by value, a `fn` value is
    /// `{code, env}`. Every rok function, and `extern "rok"` runtime
    /// declarations.
    #[default]
    Rok,
    /// The platform C ABI (spec 8.6): `str` is a NUL-terminated `char*`,
    /// a `fn` parameter a bare C function pointer, aggregates classified.
    C { variadic: bool },
}

/// Where a function's code comes from.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Linkage {
    /// Its body is compiled here.
    #[default]
    Defined,
    /// A declaration of an outside symbol, under its own name.
    Extern,
    /// A declaration of a prebuilt dependency's function (spec 904):
    /// mangled, in the dependency's archive.
    Prebuilt,
}

/// A function the back end treats specially.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum FnRole {
    #[default]
    Plain,
    /// The user's `main`: the C `main` wraps it.
    Main,
    /// An `any Tr` method dispatcher: weak in a prebuilt library, so the
    /// program's complete one replaces it.
    AnyDispatcher,
}

/// Per-function facts HIR decides and MIR / codegen only read.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FnFacts {
    pub abi: Abi,
    pub linkage: Linkage,
    /// `#[export_name("sym")]` (spec 905.8).
    pub export_name: Option<String>,
    pub role: FnRole,
    /// A generic instance: its type arguments, mangled into the symbol's
    /// typehash (905.2). The function's name then ends in
    /// `MONO_MARK` + these.
    pub mono_args: Option<String>,
    /// `#[track_caller]`: the last parameter is the caller's location
    /// (`str`, `path:line:col`), which its panics report.
    pub track_caller: bool,
}

/// Separator between a generic function's path and its instance's type
/// arguments in the instance's name.
pub const MONO_MARK: &str = "__mono__";

impl FnFacts {
    /// The item path of a function named `name` (an instance's generic).
    #[must_use]
    pub fn path<'a>(&self, name: &'a str) -> &'a str {
        self.mono_args
            .as_ref()
            .and_then(|a| name.strip_suffix(a.as_str()))
            .and_then(|n| n.strip_suffix(MONO_MARK))
            .unwrap_or(name)
    }
}

/// Callee form after name resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedFn {
    /// Statically resolved.
    Free(DefId),
    /// any-slot or sum-type narrowing path; resolved at runtime.
    Dynamic(String),
}

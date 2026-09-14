//! Low-level IR between MIR and machine code. Every value lives in a
//! frame slot (or behind a pointer held in one); an instruction loads
//! its operands into scratch registers, computes, and stores. The ISA
//! modules only pick instructions: layout, the calling conventions,
//! GC frames, barriers and checks are decided here, once for all
//! targets.

/// A frame slot (a local, or a temporary).
pub type Slot = u32;

/// A jump target within a function.
pub type Label = u32;

/// A symbol of the object being built (`obj::Obj::syms`).
pub type SymId = u32;

/// Scalar kind: the size of a value in memory and its register class.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum K {
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
}

impl K {
    #[must_use]
    pub const fn size(self) -> u32 {
        match self {
            Self::I8 => 1,
            Self::I16 => 2,
            Self::I32 | Self::F32 => 4,
            Self::I64 | Self::F64 => 8,
        }
    }

    #[must_use]
    pub const fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.size() * 8
    }
}

/// A memory location.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mem {
    /// Byte `off` of a frame slot.
    Frame(Slot, u32),
    /// Byte `off` past the pointer stored in a frame slot.
    Ind(Slot, i32),
}

impl Mem {
    #[must_use]
    pub const fn at(self, d: u32) -> Self {
        match self {
            Self::Frame(s, o) => Self::Frame(s, o + d),
            Self::Ind(s, o) => Self::Ind(s, o + d as i32),
        }
    }
}

/// A scalar operand: memory, or an immediate (a float's bits).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum V {
    M(Mem),
    I(i64),
}

/// Where a call argument / result / incoming parameter is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Loc {
    /// The `n`th integer argument / result register.
    Int(u8),
    /// The `n`th float argument / result register.
    Fp(u8),
    /// Byte offset in the outgoing (caller) / incoming (callee) argument
    /// area.
    Stack(u32),
    /// The hidden result pointer (`x8` on arm64).
    Sret,
}

/// A scalar crossing a call boundary: its location, kind, and whether a
/// narrow integer sign-extends (else zero-extends) into its register.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Part {
    pub loc: Loc,
    pub k: K,
    pub signed: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Bin {
    Add,
    Sub,
    Mul,
    /// Division / remainder; the divisor is known non-zero (and not
    /// `MIN / -1`).
    Div,
    Rem,
    And,
    Or,
    Xor,
    /// Shift amount already checked below the width.
    Shl,
    Shr,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Un {
    Neg,
    Not,
    Sqrt,
    Popcnt,
    Clz,
    Ctz,
    Bswap,
}

/// Comparison predicate (integer signedness in `Cmp::signed`; floats are
/// the ordered predicates, `Ne` unordered).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Cc {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// A conversion between scalar kinds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Conv {
    /// Integer to integer: extend by `signed` from the source width, or
    /// truncate.
    Int { signed: bool },
    /// Integer to bool: `!= 0`.
    ToBool,
    /// Integer to float.
    IToF { signed: bool },
    /// Float to integer, saturating, NaN to 0; `max_bits` bits of the
    /// destination are the integer's (1 for `bool`).
    FToI { signed: bool, bits: u32 },
    /// Float to float.
    FToF,
    /// Bits reinterpreted (same size), int ↔ float.
    Bits,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rmw {
    Xchg,
    Add,
    Sub,
    And,
    Or,
    Xor,
}

#[derive(Clone, Debug)]
pub enum Callee {
    Sym(SymId),
    /// A code pointer in memory.
    Ptr(Mem),
}

#[derive(Clone, Debug)]
pub enum Inst {
    Label(Label),
    Jmp(Label),
    /// To `t` when the `I8` value is non-zero, else to `f`.
    Br {
        c: V,
        t: Label,
        f: Label,
    },
    Mov {
        k: K,
        dst: Mem,
        src: V,
    },
    Copy {
        dst: Mem,
        src: Mem,
        size: u32,
    },
    Zero {
        dst: Mem,
        size: u32,
    },
    /// The address of `src` (an `I64`).
    Addr {
        dst: Mem,
        src: Mem,
    },
    /// The address of a symbol; `got`: through the GOT (may be in
    /// another image).
    Sym {
        dst: Mem,
        sym: SymId,
        got: bool,
    },
    /// The address of this thread's instance of a thread-local symbol.
    Tls {
        dst: Mem,
        sym: SymId,
    },
    Bin {
        op: Bin,
        k: K,
        signed: bool,
        dst: Mem,
        a: V,
        b: V,
    },
    /// `+ - *` that jumps to `fail` on overflow (of `k`, by `signed`).
    Ovf {
        op: Bin,
        k: K,
        signed: bool,
        dst: Mem,
        a: V,
        b: V,
        fail: Label,
    },
    Un {
        op: Un,
        k: K,
        dst: Mem,
        a: V,
    },
    /// `dst: I8 = a <cc> b`.
    Cmp {
        cc: Cc,
        k: K,
        signed: bool,
        dst: Mem,
        a: V,
        b: V,
    },
    Conv {
        conv: Conv,
        from: K,
        to: K,
        dst: Mem,
        a: V,
    },
    /// `ptr` holds the address. `seq_cst` loads / stores and
    /// read-modify-writes are sequentially consistent (always fine:
    /// every ordering asked for is at most that).
    AtomicLoad {
        k: K,
        dst: Mem,
        ptr: Mem,
    },
    AtomicStore {
        k: K,
        ptr: Mem,
        src: V,
    },
    AtomicRmw {
        op: Rmw,
        k: K,
        dst: Mem,
        ptr: Mem,
        val: V,
    },
    /// `dst` = the old value; stores `new` when it was `expected`.
    Cas {
        k: K,
        dst: Mem,
        ptr: Mem,
        expected: V,
        new: V,
    },
    /// Load the arguments into place, call, store the results.
    /// `sret`: the hidden result pointer's memory (passed by address).
    Call {
        callee: Callee,
        args: Vec<(Part, V)>,
        rets: Vec<(Part, Mem)>,
        sret: Option<Mem>,
        /// A C variadic call (`x86_64`: `al` = the vector registers used).
        variadic: bool,
    },
    /// An incoming parameter (first, before anything else).
    Param {
        part: Part,
        dst: Mem,
    },
    /// Return, the results loaded into place.
    Ret {
        vals: Vec<(Part, V)>,
    },
    Trap,
    /// Source line, column and lexical scope of what follows (debug
    /// line info).
    Line(u32, u32, u32),
}

/// One function of LIR.
#[derive(Clone, Debug, Default)]
pub struct Func {
    pub sym: SymId,
    /// `(size, align)` of each slot.
    pub slots: Vec<(u32, u32)>,
    pub insts: Vec<Inst>,
    pub labels: u32,
    /// `-g`: what the debug info says about it.
    pub debug: Option<FnDebug>,
}

/// `-g` facts of a function (spec 9.9.6).
#[derive(Clone, Debug)]
pub struct FnDebug {
    /// The rok path.
    pub name: String,
    /// `Span::file` (1-based) and line of its declaration.
    pub file: u32,
    pub line: u32,
    /// Lexical scopes other than the body (0): `(id, parent)`.
    pub scopes: Vec<(u32, u32)>,
    pub vars: Vec<DebugVar>,
}

/// A named local in its stack slot.
#[derive(Clone, Debug)]
pub struct DebugVar {
    pub name: String,
    pub slot: Slot,
    pub ty: rokc_mir::MirTy,
    pub line: u32,
    pub scope: u32,
    /// 1-based parameter position.
    pub arg: Option<usize>,
}

impl Func {
    pub fn slot(&mut self, size: u32, align: u32) -> Slot {
        self.slots.push((size.max(1), align.max(1)));
        self.slots.len() as Slot - 1
    }

    pub const fn label(&mut self) -> Label {
        self.labels += 1;
        self.labels - 1
    }

    pub fn push(&mut self, i: Inst) {
        self.insts.push(i);
    }
}

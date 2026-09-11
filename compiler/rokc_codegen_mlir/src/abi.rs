//! C ABI lowering of aggregate parameters / results of `extern "C"`
//! functions (spec 8.6.3). LLVM does not classify aggregates: like
//! clang, the front end rewrites a by-value `struct` into the registers
//! / memory the platform C ABI uses, and the call site converts through
//! memory.
//!
//! - AAPCS64 (Linux / Windows / Apple arm64): a homogeneous float
//!   aggregate (HFA, 1-4 members of one float type) goes in `v`
//!   registers as `[n x fT]`; other aggregates up to 16 bytes as `i64` /
//!   `[2 x i64]` arguments (results ≤ 8 bytes as `iN`); bigger ones are
//!   passed as a pointer to a caller copy and returned through `x8`
//!   (`sret`). Apple's variant only differs for variadic arguments
//!   (all on the stack — LLVM does it, the call is marked variadic) and
//!   for caller-extended small integers (`signext` / `zeroext`, which
//!   the emitter puts on every C declaration).
//! - System V `x86_64`: each eightbyte is INTEGER or SSE; ≤ 16 bytes go
//!   in registers when enough of both kinds are left (else the whole
//!   aggregate is MEMORY), > 16 bytes are MEMORY (`byval` / `sret`).
//! - Windows x64: 1 / 2 / 4 / 8-byte aggregates as `iN`, others by
//!   reference / `sret`.
//!
//! Other targets reject aggregates across the C boundary.

use rokc_ir_common::PrimTy;
use rokc_mir::{CAbi, MirTy, Target};

/// How one parameter crosses the C boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArgAbi {
    /// As its own MLIR type (scalars).
    Direct,
    /// Bits reinterpreted as this MLIR type (through memory).
    Coerce(String),
    /// A pointer to a caller-owned copy; `byval` makes it an on-stack
    /// copy (System V MEMORY class) rather than a plain pointer argument.
    Indirect { byval: bool },
}

/// How the result comes back.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RetAbi {
    Direct,
    Coerce(String),
    /// Caller passes a hidden `sret` pointer first; nothing is returned.
    Sret,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FnAbi {
    pub ret: RetAbi,
    pub args: Vec<ArgAbi>,
    /// C variadic (spec 8.6.10): an `llvm.func` called with `llvm.call`;
    /// arguments past `args` are its `...`.
    pub variadic: bool,
}

impl FnAbi {
    /// Every value crosses as itself.
    #[must_use]
    pub fn is_trivial(&self) -> bool {
        !self.variadic
            && self.ret == RetAbi::Direct
            && self.args.iter().all(|a| *a == ArgAbi::Direct)
    }
}

/// A by-value aggregate (as opposed to a scalar, `str` or `()`).
#[must_use]
pub const fn is_aggregate(ty: &MirTy) -> bool {
    matches!(
        ty,
        MirTy::Struct(..) | MirTy::Tuple(_) | MirTy::Array(..) | MirTy::Union(..)
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Leaf {
    Int,
    F32,
    F64,
}

/// Scalar leaves of `ty` at their byte offsets (`str` is two words).
fn leaves(ty: &MirTy, at: u32, target: &Target, out: &mut Vec<(u32, u32, Leaf)>) {
    let word = target.pointer_width / 8;
    match ty {
        MirTy::Unit => {}
        MirTy::Prim(PrimTy::F32) => out.push((at, 4, Leaf::F32)),
        MirTy::Prim(PrimTy::F64) => out.push((at, 8, Leaf::F64)),
        MirTy::Prim(PrimTy::Str) => {
            out.push((at, word, Leaf::Int));
            out.push((at + word, word, Leaf::Int));
        }
        MirTy::Prim(_) | MirTy::Any | MirTy::GcRef | MirTy::Fn(..) | MirTy::Mlir(_) => {
            out.push((at, target.size_align(ty).0, Leaf::Int));
        }
        MirTy::Tuple(ps) | MirTy::Struct(_, ps) => {
            let mut off = 0u32;
            for p in ps {
                let (s, a) = target.size_align(p);
                off = off.next_multiple_of(a);
                leaves(p, at + off, target, out);
                off += s;
            }
        }
        MirTy::Array(e, n) => {
            let s = target.size_align(e).0;
            for i in 0..*n {
                leaves(e, at + i * s, target, out);
            }
        }
        MirTy::Union(_, n) => {
            for i in 0..*n {
                out.push((at + i * word, word, Leaf::Int));
            }
        }
    }
}

/// Homogeneous float aggregate: `[n x f32|f64]` for 1..=4 members.
fn hfa(ty: &MirTy, target: &Target) -> Option<String> {
    let mut ls = Vec::new();
    leaves(ty, 0, target, &mut ls);
    let first = ls.first()?.2;
    if first == Leaf::Int || ls.len() > 4 || ls.iter().any(|l| l.2 != first) {
        return None;
    }
    let elem = if first == Leaf::F32 { "f32" } else { "f64" };
    Some(format!("!llvm.array<{} x {elem}>", ls.len()))
}

/// Classify a C function's signature on `target`. `params` are the
/// declared (fixed) parameters; variadic extras are always scalars.
/// `None`: the target cannot pass these aggregates.
#[must_use]
pub fn classify(target: &Target, params: &[MirTy], ret: &MirTy, variadic: bool) -> Option<FnAbi> {
    let (ret, args) = match target.c_abi {
        CAbi::Aarch64 => (
            aapcs_ret(ret, target),
            params.iter().map(|p| aapcs_arg(p, target)).collect(),
        ),
        CAbi::X86_64Win => {
            let small = |t: &MirTy| match target.size_align(t).0 {
                s @ (1 | 2 | 4 | 8) => Some(format!("i{}", s * 8)),
                _ => None,
            };
            let ret = if is_aggregate(ret) {
                small(ret).map_or(RetAbi::Sret, RetAbi::Coerce)
            } else {
                RetAbi::Direct
            };
            let args = params
                .iter()
                .map(|p| {
                    if !is_aggregate(p) {
                        return ArgAbi::Direct;
                    }
                    small(p).map_or(ArgAbi::Indirect { byval: false }, ArgAbi::Coerce)
                })
                .collect();
            (ret, args)
        }
        CAbi::X86_64SysV => sysv(params, ret, target),
        CAbi::Other => {
            if params.iter().chain([ret]).any(is_aggregate) {
                return None;
            }
            (RetAbi::Direct, vec![ArgAbi::Direct; params.len()])
        }
    };
    Some(FnAbi {
        ret,
        args,
        variadic,
    })
}

fn aapcs_arg(ty: &MirTy, target: &Target) -> ArgAbi {
    if !is_aggregate(ty) {
        return ArgAbi::Direct;
    }
    let size = target.size_align(ty).0;
    if size == 0 {
        return ArgAbi::Direct;
    }
    if let Some(h) = hfa(ty, target) {
        return ArgAbi::Coerce(h);
    }
    match size {
        1..=8 => ArgAbi::Coerce("i64".to_owned()),
        9..=16 => ArgAbi::Coerce("!llvm.array<2 x i64>".to_owned()),
        _ => ArgAbi::Indirect { byval: false },
    }
}

fn aapcs_ret(ty: &MirTy, target: &Target) -> RetAbi {
    if !is_aggregate(ty) {
        return RetAbi::Direct;
    }
    let size = target.size_align(ty).0;
    if size == 0 {
        return RetAbi::Direct;
    }
    if let Some(h) = hfa(ty, target) {
        return RetAbi::Coerce(h);
    }
    match size {
        1..=8 => RetAbi::Coerce(format!("i{}", size * 8)),
        9..=16 => RetAbi::Coerce("!llvm.array<2 x i64>".to_owned()),
        _ => RetAbi::Sret,
    }
}

/// System V `x86_64` eightbyte classes of a ≤ 16-byte aggregate: the MLIR
/// type of each eightbyte and whether it is SSE.
fn sysv_eightbytes(ty: &MirTy, target: &Target) -> Vec<(String, bool)> {
    let size = target.size_align(ty).0;
    let mut ls = Vec::new();
    leaves(ty, 0, target, &mut ls);
    let mut out = Vec::new();
    for start in [0u32, 8] {
        if start >= size {
            break;
        }
        let here: Vec<_> = ls
            .iter()
            .filter(|(o, _, _)| *o >= start && *o < start + 8)
            .collect();
        if here.is_empty() {
            // Padding-only eightbyte (NO_CLASS): still occupies the
            // slot in the coerced type to keep offsets.
            out.push(("i64".to_owned(), false));
            continue;
        }
        let sse = here.iter().all(|l| l.2 != Leaf::Int);
        let t = if sse {
            match here.as_slice() {
                [(_, _, Leaf::F64)] => "f64".to_owned(),
                [(_, _, Leaf::F32)] => "f32".to_owned(),
                _ => "vector<2xf32>".to_owned(),
            }
        } else {
            // Up to the last data byte (tail padding excluded), like clang.
            let end = here.iter().map(|l| l.0 + l.1).max().unwrap_or(start);
            format!("i{}", (end - start).min(8) * 8)
        };
        out.push((t, sse));
    }
    out
}

fn sysv(params: &[MirTy], ret: &MirTy, target: &Target) -> (RetAbi, Vec<ArgAbi>) {
    let mut free_int = 6u32;
    let mut free_sse = 8u32;
    let ret_size = target.size_align(ret).0;
    let ret_abi = if !is_aggregate(ret) || ret_size == 0 {
        RetAbi::Direct
    } else if ret_size > 16 {
        free_int -= 1;
        RetAbi::Sret
    } else {
        RetAbi::Coerce(join(&sysv_eightbytes(ret, target)))
    };
    let mut args = Vec::new();
    for t in params {
        if !is_aggregate(t) {
            match t {
                MirTy::Prim(PrimTy::F32 | PrimTy::F64) => free_sse = free_sse.saturating_sub(1),
                MirTy::Unit => {}
                _ => free_int = free_int.saturating_sub(1),
            }
            args.push(ArgAbi::Direct);
            continue;
        }
        let size = target.size_align(t).0;
        if size == 0 {
            args.push(ArgAbi::Direct);
            continue;
        }
        if size > 16 {
            args.push(ArgAbi::Indirect { byval: true });
            continue;
        }
        let ebs = sysv_eightbytes(t, target);
        let need_sse = u32::try_from(ebs.iter().filter(|e| e.1).count()).unwrap_or(2);
        let need_int = u32::try_from(ebs.len()).unwrap_or(2) - need_sse;
        if need_int > free_int || need_sse > free_sse {
            // Not enough registers for all of it: the whole aggregate
            // goes on the stack.
            args.push(ArgAbi::Indirect { byval: true });
            continue;
        }
        free_int -= need_int;
        free_sse -= need_sse;
        args.push(ArgAbi::Coerce(join(&ebs)));
    }
    (ret_abi, args)
}

fn join(ebs: &[(String, bool)]) -> String {
    match ebs {
        [(one, _)] => one.clone(),
        _ => format!(
            "!llvm.struct<({})>",
            ebs.iter()
                .map(|e| e.0.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn st(fields: &[PrimTy]) -> MirTy {
        MirTy::Tuple(fields.iter().map(|p| MirTy::Prim(*p)).collect())
    }
    use PrimTy::{F32, F64, I8, I32, I64};

    fn on(triple: &str) -> Target {
        Target::new(Some(triple))
    }

    #[test]
    fn aapcs64() {
        let t = on("aarch64-unknown-linux-gnu");
        let a = |ty: &MirTy| aapcs_arg(ty, &t);
        let r = |ty: &MirTy| aapcs_ret(ty, &t);
        // div_t: one x register, both ways.
        assert_eq!(r(&st(&[I32, I32])), RetAbi::Coerce("i64".into()));
        assert_eq!(a(&st(&[I32, I32])), ArgAbi::Coerce("i64".into()));
        assert_eq!(r(&st(&[I8, I8, I8])), RetAbi::Coerce("i24".into()));
        assert_eq!(
            r(&st(&[I64, I32])),
            RetAbi::Coerce("!llvm.array<2 x i64>".into())
        );
        // HFA / HFA-like.
        assert_eq!(
            a(&st(&[F32, F32, F32])),
            ArgAbi::Coerce("!llvm.array<3 x f32>".into())
        );
        assert_eq!(
            r(&st(&[F64, F64, F64, F64])),
            RetAbi::Coerce("!llvm.array<4 x f64>".into())
        );
        // Mixed float kinds are not an HFA.
        assert_eq!(
            a(&st(&[F32, F64])),
            ArgAbi::Coerce("!llvm.array<2 x i64>".into())
        );
        // 5 floats: too many for an HFA, 20 bytes → memory.
        assert_eq!(a(&st(&[F32; 5])), ArgAbi::Indirect { byval: false });
        assert_eq!(r(&st(&[I64, I64, I64])), RetAbi::Sret);
        assert_eq!(a(&MirTy::Prim(I32)), ArgAbi::Direct);
    }

    #[test]
    fn sysv_x86_64() {
        let t = on("x86_64-unknown-linux-gnu");
        let f = |ps: &[MirTy], r: &MirTy| sysv(ps, r, &t);
        assert_eq!(f(&[], &st(&[I32, I32])).0, RetAbi::Coerce("i64".into()));
        assert_eq!(
            f(&[], &st(&[I64, F64])).0,
            RetAbi::Coerce("!llvm.struct<(i64, f64)>".into())
        );
        assert_eq!(
            f(&[], &st(&[F32, F32, F32])).0,
            RetAbi::Coerce("!llvm.struct<(vector<2xf32>, f32)>".into())
        );
        assert_eq!(
            f(&[], &st(&[I64, I32])).0,
            RetAbi::Coerce("!llvm.struct<(i64, i32)>".into())
        );
        assert_eq!(f(&[], &st(&[F32, I32])).0, RetAbi::Coerce("i64".into()));
        assert_eq!(f(&[], &st(&[I64, I64, I64])).0, RetAbi::Sret);
        assert_eq!(
            f(&[st(&[I64, I64, I64])], &MirTy::Unit).1,
            vec![ArgAbi::Indirect { byval: true }]
        );
        // Five ints use five GPRs; a two-INTEGER struct no longer fits
        // and goes to memory whole, while a one-eightbyte one still fits.
        let ints = vec![MirTy::Prim(I64); 5];
        let mut ps = ints.clone();
        ps.push(st(&[I64, I64]));
        assert_eq!(f(&ps, &MirTy::Unit).1[5], ArgAbi::Indirect { byval: true });
        let mut ps = ints;
        ps.push(st(&[I32, I32]));
        assert_eq!(f(&ps, &MirTy::Unit).1[5], ArgAbi::Coerce("i64".into()));
        // sret takes rdi.
        let mut ps = vec![MirTy::Prim(I64); 4];
        ps.push(st(&[I64, I64]));
        assert_eq!(
            f(&ps, &st(&[I64, I64, I64])).1[4],
            ArgAbi::Indirect { byval: true }
        );
    }

    #[test]
    fn win64_and_targets() {
        let w = classify(
            &on("x86_64-pc-windows-msvc"),
            &[st(&[I32, I32]), st(&[I32, I32, I32])],
            &st(&[I8; 3]),
            false,
        )
        .unwrap();
        assert_eq!(w.args[0], ArgAbi::Coerce("i64".into()));
        assert_eq!(w.args[1], ArgAbi::Indirect { byval: false });
        assert_eq!(w.ret, RetAbi::Sret);
        // i686 has no aggregate classification: aggregates are refused,
        // scalars pass as themselves.
        let i686 = on("i686-unknown-linux-gnu");
        assert!(classify(&i686, &[st(&[I32, I32])], &MirTy::Unit, false).is_none());
        let scalars = classify(&i686, &[MirTy::Prim(I32)], &MirTy::Unit, true).unwrap();
        assert!(scalars.variadic && !scalars.is_trivial());
    }
}

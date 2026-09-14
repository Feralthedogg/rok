//! LIR → arm64 machine code.
//!
//! Frame: `fp` / `lr` pushed, `fp` = that pair, then the slots, with
//! the outgoing argument area at `sp`. Only caller-saved registers are
//! used (`x9`..`x17`, `v16`..`v18`), so nothing else is saved and the
//! compact unwind entry is a plain frame. Values never stay in a
//! register across instructions: every LIR value lives in its slot.

use crate::lir::{Bin, Callee, Cc, Conv, Func, Inst, K, Label, Loc, Mem, Rmw, Un, V};
use crate::obj::{FnRange, Obj, RelKind, Reloc, Sect};

/// Stack probe interval.
const PAGE: u32 = 4096;
const SP: u32 = 31;
const ZR: u32 = 31;
const FP: u32 = 29;
/// Data scratch.
const X9: u32 = 9;
const X10: u32 = 10;
const X11: u32 = 11;
const X12: u32 = 12;
const X13: u32 = 13;
/// Pointer bases of indirect source / destination memory.
const X14: u32 = 14;
const X15: u32 = 15;
/// Call target; address legalization.
const X16: u32 = 16;
const X17: u32 = 17;
const V16: u32 = 16;
const V17: u32 = 17;

/// Load / store opcodes (unsigned-offset form; the unscaled form clears
/// bit 24), with log2 of the access size.
#[derive(Clone, Copy)]
struct Ls(u32, u32);

const STRB: Ls = Ls(0x3900_0000, 0);
const LDRB: Ls = Ls(0x3940_0000, 0);
const LDRSB: Ls = Ls(0x3980_0000, 0);
const STRH: Ls = Ls(0x7900_0000, 1);
const LDRH: Ls = Ls(0x7940_0000, 1);
const LDRSH: Ls = Ls(0x7980_0000, 1);
const STRW: Ls = Ls(0xb900_0000, 2);
const LDRW: Ls = Ls(0xb940_0000, 2);
const LDRSW: Ls = Ls(0xb980_0000, 2);
const STRX: Ls = Ls(0xf900_0000, 3);
const LDRX: Ls = Ls(0xf940_0000, 3);
const STRS: Ls = Ls(0xbd00_0000, 2);
const LDRS: Ls = Ls(0xbd40_0000, 2);
const STRD: Ls = Ls(0xfd00_0000, 3);
const LDRD: Ls = Ls(0xfd40_0000, 3);

/// Condition codes.
const EQ: u32 = 0;
const NE: u32 = 1;
const HS: u32 = 2;
const LO: u32 = 3;
const MI: u32 = 4;
const VS: u32 = 6;
const HI: u32 = 8;
const LS_: u32 = 9;
const GE: u32 = 10;
const LT: u32 = 11;
const GT: u32 = 12;
const LE: u32 = 13;

enum Fix {
    /// `b` (26-bit).
    B(Label),
}

struct Em<'a> {
    obj: &'a mut Obj,
    start: u32,
    code: Vec<u32>,
    relocs: Vec<(u32, RelKind, u32)>,
    fixes: Vec<(usize, Fix)>,
    labels: Vec<Option<usize>>,
    slot_off: Vec<u32>,
    frame: u32,
    lines: Vec<(u32, u32, u32, u32)>,
}

const fn sf(k: K) -> u32 {
    if matches!(k, K::I64 | K::F64) {
        1 << 31
    } else {
        0
    }
}

/// Emit `f` into `obj`'s text.
pub fn emit(obj: &mut Obj, f: &Func) {
    // The outgoing argument area: the most any call puts on the stack.
    let mut out = 0u32;
    for i in &f.insts {
        if let Inst::Call { args, .. } = i {
            for (p, _) in args {
                if let Loc::Stack(o) = p.loc {
                    out = out.max(o + p.k.size().max(8));
                }
            }
        }
    }
    let mut at = out.next_multiple_of(16);
    let mut slot_off = Vec::with_capacity(f.slots.len());
    for &(size, align) in &f.slots {
        at = at.next_multiple_of(align.min(16));
        slot_off.push(at);
        at += size;
    }
    let frame = at.next_multiple_of(16);
    let start = obj.sect(Sect::Text).align_to(4);
    let mut e = Em {
        obj,
        start,
        code: Vec::new(),
        relocs: Vec::new(),
        fixes: Vec::new(),
        labels: vec![None; f.labels as usize],
        slot_off,
        frame,
        lines: Vec::new(),
    };
    e.prologue();
    for (n, i) in f.insts.iter().enumerate() {
        e.inst(i, f.insts.get(n + 1));
    }
    let debug = f.debug.as_ref().map(|d| {
        let offs = d
            .vars
            .iter()
            .map(|v| e.slot_off[v.slot as usize] as i32 - frame as i32)
            .collect();
        (d.clone(), offs)
    });
    e.finish(f.sym, debug);
}

impl Em<'_> {
    fn ins(&mut self, w: u32) {
        self.code.push(w);
    }

    fn pos(&self) -> usize {
        self.code.len()
    }

    fn reloc(&mut self, kind: RelKind, sym: u32) {
        let off = self.start + 4 * self.code.len() as u32;
        self.relocs.push((off, kind, sym));
    }

    fn finish(mut self, sym: u32, debug: Option<(crate::lir::FnDebug, Vec<i32>)>) {
        for (at, fix) in std::mem::take(&mut self.fixes) {
            let Fix::B(l) = fix;
            let target = self.labels[l as usize].expect("bound label");
            let d = target as i64 - at as i64;
            self.code[at] |= (d as u32) & 0x03ff_ffff;
        }
        let len = 4 * self.code.len() as u32;
        let start = self.start;
        let text = self.obj.sect(Sect::Text);
        for w in &self.code {
            text.data.extend_from_slice(&w.to_le_bytes());
        }
        for (off, kind, s) in self.relocs {
            text.relocs.push(Reloc { off, kind, sym: s });
        }
        let lines = std::mem::take(&mut self.lines);
        let s = &mut self.obj.syms[sym as usize];
        s.def = Some((Sect::Text, start, len));
        self.obj.fns.push(FnRange {
            sym,
            start,
            len,
            lines,
            debug,
        });
    }

    // ---- encoders ----

    fn movz(&mut self, rd: u32, imm: u32, hw: u32) {
        self.ins(0xd280_0000 | (hw << 21) | (imm << 5) | rd);
    }

    fn movk(&mut self, rd: u32, imm: u32, hw: u32) {
        self.ins(0xf280_0000 | (hw << 21) | (imm << 5) | rd);
    }

    fn movn(&mut self, rd: u32, imm: u32, hw: u32) {
        self.ins(0x9280_0000 | (hw << 21) | (imm << 5) | rd);
    }

    fn mov_imm(&mut self, rd: u32, v: u64) {
        let halves = |x: u64| (0..4).filter(|h| (x >> (16 * h)) & 0xffff != 0).count();
        if halves(!v) < halves(v) {
            // `movn` then `movk` the halfwords that are not all ones.
            let mut first = true;
            for h in 0..4u32 {
                let part = ((v >> (16 * h)) & 0xffff) as u32;
                if first {
                    if part != 0xffff || h == 3 {
                        self.movn(rd, !part & 0xffff, h);
                        first = false;
                    }
                } else if part != 0xffff {
                    self.movk(rd, part, h);
                }
            }
            if first {
                self.movn(rd, 0, 0);
            }
            return;
        }
        let mut first = true;
        for h in 0..4u32 {
            let part = ((v >> (16 * h)) & 0xffff) as u32;
            if part != 0 {
                if first {
                    self.movz(rd, part, h);
                    first = false;
                } else {
                    self.movk(rd, part, h);
                }
            }
        }
        if first {
            self.movz(rd, 0, 0);
        }
    }

    /// `rd = rn + imm` (64-bit; `sp` allowed for both).
    fn add_imm(&mut self, rd: u32, rn: u32, imm: i64) {
        let (op, a) = if imm < 0 {
            (0xd100_0000u32, imm.unsigned_abs())
        } else {
            (0x9100_0000u32, imm as u64)
        };
        if a == 0 {
            if rd != rn {
                self.ins(0x9100_0000 | (rn << 5) | rd);
            }
            return;
        }
        if a < 1 << 24 {
            let (hi, lo) = ((a >> 12) as u32, (a & 0xfff) as u32);
            let mut src = rn;
            if hi != 0 {
                self.ins(op | (1 << 22) | (hi << 10) | (src << 5) | rd);
                src = rd;
            }
            if lo != 0 {
                self.ins(op | (lo << 10) | (src << 5) | rd);
            }
            return;
        }
        // Far: through x17, extended-register form (takes `sp`).
        self.mov_imm(X17, imm as u64);
        self.ins(0x8b20_6000 | (X17 << 16) | (rn << 5) | rd);
    }

    /// Load / store `rt` at `base + off`.
    fn ldst(&mut self, op: Ls, rt: u32, base: u32, off: i64) {
        let Ls(enc, sz) = op;
        let scale = 1i64 << sz;
        if off >= 0 && off % scale == 0 && off / scale < 4096 {
            self.ins(enc | (((off / scale) as u32) << 10) | (base << 5) | rt);
        } else if (-256..256).contains(&off) {
            self.ins((enc & !0x0100_0000) | (((off as u32) & 0x1ff) << 12) | (base << 5) | rt);
        } else {
            self.add_imm(X17, base, off);
            self.ins(enc | (X17 << 5) | rt);
        }
    }

    /// `(base register, offset)` of `m`; an indirect pointer goes into
    /// `tmp`.
    fn base(&mut self, m: Mem, tmp: u32) -> (u32, i64) {
        match m {
            Mem::Frame(s, o) => (SP, i64::from(self.slot_off[s as usize] + o)),
            Mem::Ind(s, o) => {
                let so = i64::from(self.slot_off[s as usize]);
                self.ldst(LDRX, tmp, SP, so);
                (tmp, i64::from(o))
            }
        }
    }

    fn addr(&mut self, rd: u32, m: Mem) {
        let (b, o) = self.base(m, rd);
        self.add_imm(rd, b, o);
    }

    const fn load_op(k: K, signed: bool) -> Ls {
        match (k, signed) {
            (K::I8, true) => LDRSB,
            (K::I8, false) => LDRB,
            (K::I16, true) => LDRSH,
            (K::I16, false) => LDRH,
            (K::I32, true) => LDRSW,
            (K::I32 | K::F32, _) => LDRW,
            (K::I64 | K::F64, _) => LDRX,
        }
    }

    const fn store_op(k: K) -> Ls {
        match k {
            K::I8 => STRB,
            K::I16 => STRH,
            K::I32 | K::F32 => STRW,
            K::I64 | K::F64 => STRX,
        }
    }

    /// Integer register `rd` = `v` as `k`, extended by `signed`.
    fn load(&mut self, rd: u32, v: V, k: K, signed: bool) {
        match v {
            V::I(i) => {
                let bits = k.bits();
                let x = if bits == 64 {
                    i as u64
                } else if signed {
                    ((i << (64 - bits)) >> (64 - bits)) as u64
                } else {
                    (i as u64) & ((1u64 << bits) - 1)
                };
                self.mov_imm(rd, x);
            }
            V::M(m) => {
                let (b, o) = self.base(m, X14);
                self.ldst(Self::load_op(k, signed), rd, b, o);
            }
        }
    }

    fn store(&mut self, rs: u32, m: Mem, k: K) {
        let (b, o) = self.base(m, X15);
        self.ldst(Self::store_op(k), rs, b, o);
    }

    fn load_fp(&mut self, vd: u32, v: V, k: K) {
        match v {
            V::I(bits) => {
                self.mov_imm(X13, bits as u64);
                // fmov s/d, w/x
                self.ins(
                    if k == K::F32 {
                        0x1e27_0000
                    } else {
                        0x9e67_0000
                    } | (X13 << 5)
                        | vd,
                );
            }
            V::M(m) => {
                let (b, o) = self.base(m, X14);
                self.ldst(if k == K::F32 { LDRS } else { LDRD }, vd, b, o);
            }
        }
    }

    fn store_fp(&mut self, vs: u32, m: Mem, k: K) {
        let (b, o) = self.base(m, X15);
        self.ldst(if k == K::F32 { STRS } else { STRD }, vs, b, o);
    }

    fn b(&mut self, l: Label) {
        let at = self.pos();
        self.ins(0x1400_0000);
        self.fixes.push((at, Fix::B(l)));
    }

    fn bcond(&mut self, cond: u32, l: Label) {
        // Inverted around an unconditional branch: any distance.
        self.ins(0x5400_0000 | (2 << 5) | (cond ^ 1));
        self.b(l);
    }

    fn cset(&mut self, rd: u32, cond: u32) {
        self.ins(0x1a9f_07e0 | ((cond ^ 1) << 12) | rd);
    }

    /// `cmp xn, xm` (`sf` from `k`).
    fn cmp_rr(&mut self, k: K, rn: u32, rm: u32) {
        self.ins(0x6b00_001f | sf(k) | (rm << 16) | (rn << 5));
    }

    fn prologue(&mut self) {
        self.ins(0xa9bf_7bfd); // stp x29, x30, [sp, #-16]!
        self.ins(0x9100_03fd); // mov x29, sp
        let n = self.frame;
        if n == 0 {
            return;
        }
        // Touch every page on the way down (a guard page cannot be
        // skipped).
        let pages = n / PAGE;
        if pages > 0 {
            if pages > 8 {
                self.mov_imm(X17, u64::from(pages));
                let top = self.pos();
                self.ins(0xd140_07ff); // sub sp, sp, #1, lsl #12
                self.ins(0xf900_03ff); // str xzr, [sp]
                self.ins(0xf100_0631); // subs x17, x17, #1
                let d = top as i64 - self.pos() as i64;
                self.ins(0x5400_0000 | (((d as u32) & 0x7ffff) << 5) | NE);
            } else {
                for _ in 0..pages {
                    self.ins(0xd140_07ff);
                    self.ins(0xf900_03ff);
                }
            }
        }
        let rest = n % PAGE;
        if rest != 0 {
            self.add_imm(SP, SP, -i64::from(rest));
        }
    }

    fn epilogue(&mut self) {
        self.ins(0x9100_03bf); // mov sp, x29
        self.ins(0xa8c1_7bfd); // ldp x29, x30, [sp], #16
        self.ins(0xd65f_03c0); // ret
    }

    fn copy(&mut self, dst: Mem, src: Mem, size: u32, zero: bool) {
        // Addresses into x14 (source) and x15 (destination).
        if !zero {
            self.addr(X14, src);
        }
        self.addr(X15, dst);
        let words = size / 8;
        let mut off = 0i64;
        if words > 16 {
            self.mov_imm(X13, u64::from(words));
            let top = self.pos();
            if zero {
                self.ins(0xf800_85ff); // str xzr, [x15], #8
            } else {
                self.ins(0xf840_85c9); // ldr x9, [x14], #8
                self.ins(0xf800_85e9); // str x9, [x15], #8
            }
            self.ins(0xf100_05ad); // subs x13, x13, #1
            let d = top as i64 - self.pos() as i64;
            self.ins(0x5400_0000 | (((d as u32) & 0x7ffff) << 5) | NE);
        } else {
            for _ in 0..words {
                if zero {
                    self.ldst(STRX, ZR, X15, off);
                } else {
                    self.ldst(LDRX, X9, X14, off);
                    self.ldst(STRX, X9, X15, off);
                }
                off += 8;
            }
        }
        let mut rest = size % 8;
        for (n, ld, st) in [(4, LDRW, STRW), (2, LDRH, STRH), (1, LDRB, STRB)] {
            while rest >= n {
                if zero {
                    self.ldst(st, ZR, X15, off);
                } else {
                    self.ldst(ld, X9, X14, off);
                    self.ldst(st, X9, X15, off);
                }
                off += i64::from(n);
                rest -= n;
            }
        }
    }

    fn bin_int(&mut self, op: Bin, k: K, signed: bool, rd: u32, a: u32, b: u32) {
        let s = sf(k);
        let w = match op {
            Bin::Add => 0x0b00_0000 | s | (b << 16) | (a << 5) | rd,
            Bin::Sub => 0x4b00_0000 | s | (b << 16) | (a << 5) | rd,
            Bin::Mul => 0x1b00_7c00 | s | (b << 16) | (a << 5) | rd,
            Bin::Div => {
                (if signed { 0x1ac0_0c00 } else { 0x1ac0_0800 }) | s | (b << 16) | (a << 5) | rd
            }
            Bin::Rem => {
                let q = X12;
                self.ins(
                    (if signed { 0x1ac0_0c00 } else { 0x1ac0_0800 }) | s | (b << 16) | (a << 5) | q,
                );
                // msub rd, q, b, a
                0x1b00_8000 | s | (b << 16) | (a << 10) | (q << 5) | rd
            }
            Bin::And => 0x0a00_0000 | s | (b << 16) | (a << 5) | rd,
            Bin::Or => 0x2a00_0000 | s | (b << 16) | (a << 5) | rd,
            Bin::Xor => 0x4a00_0000 | s | (b << 16) | (a << 5) | rd,
            Bin::Shl => 0x1ac0_2000 | s | (b << 16) | (a << 5) | rd,
            Bin::Shr => {
                (if signed { 0x1ac0_2800 } else { 0x1ac0_2400 }) | s | (b << 16) | (a << 5) | rd
            }
        };
        self.ins(w);
    }

    fn inst(&mut self, i: &Inst, next: Option<&Inst>) {
        match i {
            Inst::Label(l) => self.labels[*l as usize] = Some(self.pos()),
            Inst::Jmp(l) => {
                if !matches!(next, Some(Inst::Label(n)) if n == l) {
                    self.b(*l);
                }
            }
            Inst::Br { c, t, f } => {
                if let V::I(v) = c {
                    self.b(if *v & 0xff != 0 { *t } else { *f });
                    return;
                }
                self.load(X9, *c, K::I8, false);
                // cbz w9, +8; b t; b f
                self.ins(0x3400_0000 | (2 << 5) | X9);
                self.b(*t);
                if !matches!(next, Some(Inst::Label(n)) if n == f) {
                    self.b(*f);
                }
            }
            Inst::Mov { k, dst, src } => {
                self.load(X9, *src, *k, false);
                self.store(X9, *dst, *k);
            }
            Inst::Copy { dst, src, size } => self.copy(*dst, *src, *size, false),
            Inst::Zero { dst, size } => self.copy(*dst, *dst, *size, true),
            Inst::Addr { dst, src } => {
                self.addr(X9, *src);
                self.store(X9, *dst, K::I64);
            }
            Inst::Sym { dst, sym, got } => {
                let (p, o) = if *got {
                    (RelKind::GotPage21, RelKind::GotPageOff12)
                } else {
                    (RelKind::Page21, RelKind::PageOff12)
                };
                self.reloc(p, *sym);
                self.ins(0x9000_0000 | X9); // adrp x9
                self.reloc(o, *sym);
                if *got {
                    self.ins(0xf940_0000 | (X9 << 5) | X9); // ldr x9, [x9]
                } else {
                    self.ins(0x9100_0000 | (X9 << 5) | X9); // add x9, x9, #0
                }
                self.store(X9, *dst, K::I64);
            }
            Inst::Tls { dst, sym } => {
                self.reloc(RelKind::TlvPage21, *sym);
                self.ins(0x9000_0000); // adrp x0
                self.reloc(RelKind::TlvPageOff12, *sym);
                self.ins(0xf940_0000); // ldr x0, [x0]
                if self.obj.elf {
                    // Initial exec: the thread pointer plus the offset.
                    self.ins(0xd53b_d050); // mrs x16, tpidr_el0
                    self.ins(0x8b00_0200); // add x0, x16, x0
                } else {
                    // Mach-O: the descriptor's getter.
                    self.ins(0xf940_0010); // ldr x16, [x0]
                    self.ins(0xd63f_0200); // blr x16
                }
                self.store(0, *dst, K::I64);
            }
            Inst::Bin {
                op,
                k,
                signed,
                dst,
                a,
                b,
            } => {
                if k.is_float() {
                    self.load_fp(V16, *a, *k);
                    self.load_fp(V17, *b, *k);
                    let ty = if *k == K::F64 { 1 << 22 } else { 0 };
                    let opc = match op {
                        Bin::Add => 0x1e20_2800,
                        Bin::Sub => 0x1e20_3800,
                        Bin::Mul => 0x1e20_0800,
                        _ => 0x1e20_1800,
                    };
                    self.ins(opc | ty | (V17 << 16) | (V16 << 5) | V16);
                    self.store_fp(V16, *dst, *k);
                    return;
                }
                self.load(X9, *a, *k, *signed);
                self.load(X10, *b, *k, *signed);
                self.bin_int(*op, *k, *signed, X11, X9, X10);
                self.store(X11, *dst, *k);
            }
            Inst::Ovf {
                op,
                k,
                signed,
                dst,
                a,
                b,
                fail,
            } => self.ovf(*op, *k, *signed, *dst, *a, *b, *fail),
            Inst::Un { op, k, dst, a } => self.un(*op, *k, *dst, *a),
            Inst::Cmp {
                cc,
                k,
                signed,
                dst,
                a,
                b,
            } => {
                let cond = if k.is_float() {
                    self.load_fp(V16, *a, *k);
                    self.load_fp(V17, *b, *k);
                    let ty = if *k == K::F64 { 1 << 22 } else { 0 };
                    self.ins(0x1e20_2000 | ty | (V17 << 16) | (V16 << 5));
                    match cc {
                        Cc::Eq => EQ,
                        Cc::Ne => NE,
                        Cc::Lt => MI,
                        Cc::Le => LS_,
                        Cc::Gt => GT,
                        Cc::Ge => GE,
                    }
                } else {
                    self.load(X9, *a, *k, *signed);
                    self.load(X10, *b, *k, *signed);
                    self.cmp_rr(*k, X9, X10);
                    match (cc, signed) {
                        (Cc::Eq, _) => EQ,
                        (Cc::Ne, _) => NE,
                        (Cc::Lt, true) => LT,
                        (Cc::Lt, false) => LO,
                        (Cc::Le, true) => LE,
                        (Cc::Le, false) => LS_,
                        (Cc::Gt, true) => GT,
                        (Cc::Gt, false) => HI,
                        (Cc::Ge, true) => GE,
                        (Cc::Ge, false) => HS,
                    }
                };
                self.cset(X9, cond);
                self.store(X9, *dst, K::I8);
            }
            Inst::Conv {
                conv,
                from,
                to,
                dst,
                a,
            } => self.conv(*conv, *from, *to, *dst, *a),
            Inst::AtomicLoad { k, dst, ptr } => {
                self.addr_of_ptr(X14, *ptr);
                let sz = k.size().trailing_zeros();
                self.ins((sz << 30) | 0x08df_fc00 | (X14 << 5) | X9);
                self.store(X9, *dst, *k);
            }
            Inst::AtomicStore { k, ptr, src } => {
                self.load(X9, *src, *k, false);
                self.addr_of_ptr(X14, *ptr);
                let sz = k.size().trailing_zeros();
                self.ins((sz << 30) | 0x089f_fc00 | (X14 << 5) | X9);
            }
            Inst::AtomicRmw {
                op,
                k,
                dst,
                ptr,
                val,
            } => {
                self.load(X10, *val, *k, false);
                self.addr_of_ptr(X14, *ptr);
                let sz = k.size().trailing_zeros();
                let opc = match op {
                    Rmw::Add => 0,
                    Rmw::Sub => {
                        self.ins(0xcb0a_03ea); // neg x10, x10
                        0
                    }
                    Rmw::And => {
                        self.ins(0xaa2a_03ea); // mvn x10, x10
                        0x1000
                    }
                    Rmw::Xor => 0x2000,
                    Rmw::Or => 0x3000,
                    Rmw::Xchg => 0x8000,
                };
                self.ins((sz << 30) | 0x38e0_0000 | opc | (X10 << 16) | (X14 << 5) | X9);
                self.store(X9, *dst, *k);
            }
            Inst::Cas {
                k,
                dst,
                ptr,
                expected,
                new,
            } => {
                self.load(X9, *expected, *k, false);
                self.load(X10, *new, *k, false);
                self.addr_of_ptr(X14, *ptr);
                let sz = k.size().trailing_zeros();
                self.ins((sz << 30) | 0x08e0_fc00 | (X9 << 16) | (X14 << 5) | X10);
                self.store(X9, *dst, *k);
            }
            Inst::Call {
                callee,
                args,
                rets,
                sret,
                ..
            } => {
                for (p, v) in args {
                    match p.loc {
                        Loc::Stack(o) => {
                            if p.k.is_float() {
                                self.load(X9, *v, p.k, false);
                            } else {
                                self.load(X9, *v, p.k, p.signed);
                            }
                            self.ldst(Self::store_op(p.k), X9, SP, i64::from(o));
                        }
                        Loc::Int(r) => self.load(u32::from(r), *v, p.k, p.signed),
                        Loc::Fp(r) => self.load_fp(u32::from(r), *v, p.k),
                        Loc::Sret => {}
                    }
                }
                if let Some(m) = sret {
                    self.addr(8, *m);
                }
                match callee {
                    Callee::Sym(s) => {
                        self.reloc(RelKind::Branch26, *s);
                        self.ins(0x9400_0000);
                    }
                    Callee::Ptr(m) => {
                        self.load(X16, V::M(*m), K::I64, false);
                        self.ins(0xd63f_0000 | (X16 << 5));
                    }
                }
                for (p, m) in rets {
                    match p.loc {
                        Loc::Int(r) => self.store(u32::from(r), *m, p.k),
                        Loc::Fp(r) => self.store_fp(u32::from(r), *m, p.k),
                        _ => {}
                    }
                }
            }
            Inst::Param { part, dst } => match part.loc {
                Loc::Int(r) => self.store(u32::from(r), *dst, part.k),
                Loc::Fp(r) => self.store_fp(u32::from(r), *dst, part.k),
                Loc::Stack(o) => {
                    self.ldst(Self::load_op(part.k, false), X9, FP, 16 + i64::from(o));
                    self.store(X9, *dst, part.k);
                }
                Loc::Sret => self.store(8, *dst, K::I64),
            },
            Inst::Ret { vals } => {
                for (p, v) in vals {
                    match p.loc {
                        Loc::Int(r) => self.load(u32::from(r), *v, p.k, p.signed),
                        Loc::Fp(r) => self.load_fp(u32::from(r), *v, p.k),
                        _ => {}
                    }
                }
                self.epilogue();
            }
            Inst::Trap => self.ins(0xd420_0020), // brk #1
            Inst::Line(line, col, scope) => {
                let at = 4 * self.code.len() as u32;
                self.lines.push((at, *line, *col, *scope));
            }
        }
    }

    /// The address a `ptr` operand of an atomic names, in `rd`.
    fn addr_of_ptr(&mut self, rd: u32, m: Mem) {
        self.addr(rd, m);
    }

    #[allow(clippy::too_many_arguments)]
    fn ovf(&mut self, op: Bin, k: K, signed: bool, dst: Mem, a: V, b: V, fail: Label) {
        self.load(X9, a, k, signed);
        self.load(X10, b, k, signed);
        match (k, op) {
            (K::I64, Bin::Add | Bin::Sub) => {
                let base = if op == Bin::Add {
                    0xab00_0000
                } else {
                    0xeb00_0000
                };
                self.ins(base | (X10 << 16) | (X9 << 5) | X11);
                let cond = match (op, signed) {
                    (_, true) => VS,
                    (Bin::Add, false) => HS,
                    _ => LO,
                };
                self.bcond(cond, fail);
            }
            (K::I64, _) => {
                self.ins(0x9b00_7c00 | (X10 << 16) | (X9 << 5) | X11); // mul
                if signed {
                    self.ins(0x9b40_7c00 | (X10 << 16) | (X9 << 5) | X12); // smulh
                    // cmp x12, x11, asr #63
                    self.ins(0xeb80_001f | (X11 << 16) | (63 << 10) | (X12 << 5));
                } else {
                    self.ins(0x9bc0_7c00 | (X10 << 16) | (X9 << 5) | X12); // umulh
                    self.ins(0xeb1f_001f | (X12 << 5)); // cmp x12, xzr
                }
                self.bcond(NE, fail);
            }
            (K::I32, Bin::Add | Bin::Sub) => {
                let base = if op == Bin::Add {
                    0x2b00_0000
                } else {
                    0x6b00_0000
                };
                self.ins(base | (X10 << 16) | (X9 << 5) | X11);
                let cond = match (op, signed) {
                    (_, true) => VS,
                    (Bin::Add, false) => HS,
                    _ => LO,
                };
                self.bcond(cond, fail);
            }
            (K::I32, _) => {
                // smull / umull x11, w9, w10; the product must fit 32 bits.
                let m = if signed { 0x9b20_7c00 } else { 0x9ba0_7c00 };
                self.ins(m | (X10 << 16) | (X9 << 5) | X11);
                let option = if signed { 0b110 } else { 0b010 };
                // cmp x11, w11, sxtw / uxtw
                self.ins(0xeb20_001f | (X11 << 16) | (option << 13) | (X11 << 5));
                self.bcond(NE, fail);
            }
            _ => {
                // 8 / 16 bits, computed in 32 from extended operands: the
                // result must equal its own extension.
                self.bin_int(op, K::I32, signed, X11, X9, X10);
                let option = match (k, signed) {
                    (K::I8, true) => 0b100,
                    (K::I16, true) => 0b101,
                    (K::I8, false) => 0b000,
                    _ => 0b001,
                };
                self.ins(0x6b20_001f | (X11 << 16) | (option << 13) | (X11 << 5));
                self.bcond(NE, fail);
            }
        }
        self.store(X11, dst, k);
    }

    fn un(&mut self, op: Un, k: K, dst: Mem, a: V) {
        if k.is_float() {
            self.load_fp(V16, a, k);
            let ty = if k == K::F64 { 1 << 22 } else { 0 };
            let opc = if op == Un::Sqrt {
                0x1e21_c000
            } else {
                0x1e21_4000
            };
            self.ins(opc | ty | (V16 << 5) | V16);
            self.store_fp(V16, dst, k);
            return;
        }
        let s = sf(k);
        let bits = k.bits();
        match op {
            Un::Neg => {
                self.load(X9, a, k, true);
                self.ins(0x4b00_03e0 | s | (X9 << 16) | X9);
            }
            Un::Not => {
                self.load(X9, a, k, false);
                self.ins(0x2a20_03e0 | s | (X9 << 16) | X9);
            }
            Un::Popcnt => {
                self.load(X9, a, k, false);
                self.ins(0x9e67_0000 | (X9 << 5) | V16); // fmov d16, x9
                self.ins(0x0e20_5800 | (V16 << 5) | V16); // cnt v16.8b
                self.ins(0x0e31_b800 | (V16 << 5) | V16); // addv b16, v16.8b
                self.ins(0x1e26_0000 | (V16 << 5) | X9); // fmov w9, s16
            }
            Un::Clz => {
                self.load(X9, a, k, false);
                self.ins(0x5ac0_1000 | s | (X9 << 5) | X9);
                if bits < 32 {
                    // sub w9, w9, #(32 - bits)
                    self.ins(0x5100_0000 | ((32 - bits) << 10) | (X9 << 5) | X9);
                }
            }
            Un::Ctz => {
                self.load(X9, a, k, false);
                if bits < 32 {
                    self.mov_imm(X10, 1 << bits);
                    self.ins(0x2a00_0000 | (X10 << 16) | (X9 << 5) | X9);
                }
                self.ins(0x5ac0_0000 | s | (X9 << 5) | X9); // rbit
                self.ins(0x5ac0_1000 | s | (X9 << 5) | X9); // clz
            }
            Un::Bswap => {
                self.load(X9, a, k, false);
                match k {
                    K::I16 => self.ins(0x5ac0_0400 | (X9 << 5) | X9),
                    K::I32 => self.ins(0x5ac0_0800 | (X9 << 5) | X9),
                    K::I64 => self.ins(0xdac0_0c00 | (X9 << 5) | X9),
                    _ => {}
                }
            }
            Un::Sqrt => self.load(X9, a, k, false),
        }
        self.store(X9, dst, k);
    }

    fn conv(&mut self, conv: Conv, from: K, to: K, dst: Mem, a: V) {
        match conv {
            Conv::Int { signed } => {
                self.load(X9, a, from, signed);
                self.store(X9, dst, to);
            }
            Conv::ToBool => {
                self.load(X9, a, from, false);
                self.ins(0xf100_001f | (X9 << 5)); // cmp x9, #0
                self.cset(X9, NE);
                self.store(X9, dst, K::I8);
            }
            Conv::IToF { signed } => {
                self.load(X9, a, from, signed);
                let base = match (to, signed) {
                    (K::F32, true) => 0x9e22_0000,
                    (K::F32, false) => 0x9e23_0000,
                    (_, true) => 0x9e62_0000,
                    (_, false) => 0x9e63_0000,
                };
                self.ins(base | (X9 << 5) | V16);
                self.store_fp(V16, dst, to);
            }
            Conv::FToI { signed, bits } => {
                self.load_fp(V16, a, from);
                let ty = if from == K::F64 { 1 << 22 } else { 0 };
                let op = if signed { 0x9e38_0000 } else { 0x9e39_0000 };
                self.ins(op | ty | (V16 << 5) | X9);
                if bits < 64 {
                    let (max, min) = if signed {
                        ((1i64 << (bits - 1)) - 1, -(1i64 << (bits - 1)))
                    } else {
                        ((1i64 << bits) - 1, 0)
                    };
                    self.mov_imm(X10, max as u64);
                    self.cmp_rr(K::I64, X9, X10);
                    // csel x9, x10, x9, gt / hi
                    let c = if signed { GT } else { HI };
                    self.ins(0x9a80_0000 | (X9 << 16) | (c << 12) | (X10 << 5) | X9);
                    if signed {
                        self.mov_imm(X10, min as u64);
                        self.cmp_rr(K::I64, X9, X10);
                        self.ins(0x9a80_0000 | (X9 << 16) | (LT << 12) | (X10 << 5) | X9);
                    }
                }
                self.store(X9, dst, to);
            }
            Conv::FToF => {
                self.load_fp(V16, a, from);
                if from == K::F32 {
                    self.ins(0x1e22_c000 | (V16 << 5) | V16); // fcvt d, s
                } else {
                    self.ins(0x1e62_4000 | (V16 << 5) | V16); // fcvt s, d
                }
                self.store_fp(V16, dst, to);
            }
            Conv::Bits => {
                self.load(X9, a, from, false);
                self.store(X9, dst, to);
            }
        }
    }
}

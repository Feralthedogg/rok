//! LIR → `x86_64` machine code (System V).
//!
//! Frame: `rbp` pushed, `rbp` = it, then the slots, with the outgoing
//! argument area at `rsp`. Scratch: `rax rcx rdx` (data), `r10 r11`
//! (pointer bases), `xmm0 xmm1`; every LIR value lives in its slot, so
//! nothing is saved and unwinding sees a plain `rbp` frame. Only
//! baseline `x86_64` instructions (no `popcnt` / `lzcnt`).

use crate::lir::{Bin, Callee, Cc, Conv, Func, Inst, K, Label, Loc, Mem, Rmw, Un, V};
use crate::obj::{FnRange, Obj, RelKind, Reloc, Sect};

const RAX: u32 = 0;
const RCX: u32 = 1;
const RDX: u32 = 2;
const RSP: u32 = 4;
const RBP: u32 = 5;
const RSI: u32 = 6;
const RDI: u32 = 7;
const R10: u32 = 10;
const R11: u32 = 11;
const XMM0: u32 = 0;
const XMM1: u32 = 1;
/// Integer argument registers.
const ARGS: [u32; 6] = [RDI, RSI, RDX, RCX, 8, 9];
/// Integer result registers.
const RETS: [u32; 3] = [RAX, RDX, RCX];
/// Stack probe interval.
const PAGE: u32 = 4096;

// Condition codes.
const CC_O: u8 = 0;
const CC_B: u8 = 2;
const CC_AE: u8 = 3;
const CC_E: u8 = 4;
const CC_NE: u8 = 5;
const CC_BE: u8 = 6;
const CC_A: u8 = 7;
const CC_S: u8 = 8;
const CC_P: u8 = 0xa;
const CC_NP: u8 = 0xb;
const CC_L: u8 = 0xc;
const CC_GE: u8 = 0xd;
const CC_LE: u8 = 0xe;
const CC_G: u8 = 0xf;

/// A register-or-memory operand.
#[derive(Clone, Copy)]
enum Rm {
    R(u32),
    /// `[base + disp]`.
    M(u32, i32),
}

struct Em<'a> {
    obj: &'a mut Obj,
    start: u32,
    code: Vec<u8>,
    relocs: Vec<(u32, RelKind, u32)>,
    /// `(position of a rel32, label)`.
    fixes: Vec<(usize, Label)>,
    labels: Vec<Option<usize>>,
    slot_off: Vec<u32>,
    frame: u32,
    lines: Vec<(u32, u32, u32, u32)>,
}

/// Emit `f` into `obj`'s text.
pub fn emit(obj: &mut Obj, f: &Func) {
    let mut out = 0u32;
    for i in &f.insts {
        if let Inst::Call { args, .. } = i {
            for (p, _) in args {
                if let Loc::Stack(o) = p.loc {
                    out = out.max(o + 8);
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
    let start = obj.sect(Sect::Text).align_to(16);
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
    fn b(&mut self, x: u8) {
        self.code.push(x);
    }

    fn bytes(&mut self, x: &[u8]) {
        self.code.extend_from_slice(x);
    }

    fn d32(&mut self, x: i32) {
        self.code.extend_from_slice(&x.to_le_bytes());
    }

    fn finish(mut self, sym: u32, debug: Option<(crate::lir::FnDebug, Vec<i32>)>) {
        for (at, l) in std::mem::take(&mut self.fixes) {
            let target = self.labels[l as usize].expect("bound label");
            let d = target as i64 - (at as i64 + 4);
            self.code[at..at + 4].copy_from_slice(&(d as i32).to_le_bytes());
        }
        let len = self.code.len() as u32;
        let start = self.start;
        let text = self.obj.sect(Sect::Text);
        text.data.extend_from_slice(&self.code);
        for (off, kind, s) in self.relocs {
            text.relocs.push(Reloc { off, kind, sym: s });
        }
        let lines = std::mem::take(&mut self.lines);
        self.obj.syms[sym as usize].def = Some((Sect::Text, start, len));
        self.obj.fns.push(FnRange {
            sym,
            start,
            len,
            lines,
            debug,
        });
    }

    /// An instruction with a `ModRM` operand: optional legacy prefix,
    /// REX (`w`: 64-bit; `byte`: a byte register `reg` / `rm` that needs
    /// REX to be `spl`..`dil`), opcode, `reg` field, `rm`.
    fn op(&mut self, pre: Option<u8>, w: bool, byte: bool, opc: &[u8], reg: u32, rm: Rm) {
        if let Some(p) = pre {
            self.b(p);
        }
        let (rmreg, index) = match rm {
            Rm::R(r) => (r, 0),
            Rm::M(base, _) => (base, 0),
        };
        let mut rex = 0x40u8;
        if w {
            rex |= 8;
        }
        if reg >= 8 {
            rex |= 4;
        }
        if index >= 8 {
            rex |= 2;
        }
        if rmreg >= 8 {
            rex |= 1;
        }
        let force =
            byte && ((4..8).contains(&reg) || matches!(rm, Rm::R(r) if (4..8).contains(&r)));
        if rex != 0x40 || force {
            self.b(rex);
        }
        self.bytes(opc);
        let r = ((reg & 7) << 3) as u8;
        match rm {
            Rm::R(x) => self.b(0xc0 | r | (x & 7) as u8),
            Rm::M(base, disp) => {
                let lo = (base & 7) as u8;
                let (md, small) = if disp == 0 && lo != 5 {
                    (0u8, None)
                } else if (-128..128).contains(&disp) {
                    (0x40, Some(true))
                } else {
                    (0x80, Some(false))
                };
                self.b(md | r | lo);
                if lo == 4 {
                    self.b(0x24); // SIB: base only
                }
                match small {
                    Some(true) => self.b(disp as u8),
                    Some(false) => self.d32(disp),
                    None => {}
                }
            }
        }
    }

    /// `[rip + sym]` with relocation `kind` (the 32-bit field ends the
    /// instruction).
    fn op_rip(&mut self, pre: Option<u8>, w: bool, opc: &[u8], reg: u32, kind: RelKind, sym: u32) {
        if let Some(p) = pre {
            self.b(p);
        }
        let mut rex = 0x40u8;
        if w {
            rex |= 8;
        }
        if reg >= 8 {
            rex |= 4;
        }
        if rex != 0x40 {
            self.b(rex);
        }
        self.bytes(opc);
        self.b((((reg & 7) << 3) | 5) as u8);
        let off = self.start + self.code.len() as u32;
        self.relocs.push((off, kind, sym));
        self.d32(0);
    }

    /// `[base + disp]` of `m`; an indirect pointer goes into `tmp`.
    fn mem(&mut self, m: Mem, tmp: u32) -> Rm {
        match m {
            Mem::Frame(s, o) => Rm::M(RSP, (self.slot_off[s as usize] + o) as i32),
            Mem::Ind(s, o) => {
                let so = self.slot_off[s as usize] as i32;
                self.op(None, true, false, &[0x8b], tmp, Rm::M(RSP, so));
                Rm::M(tmp, o)
            }
        }
    }

    fn mov_imm(&mut self, r: u32, v: u64) {
        if u32::try_from(v).is_ok() {
            // mov r32, imm32 (zero-extends)
            if r >= 8 {
                self.b(0x41);
            }
            self.b(0xb8 + (r & 7) as u8);
            self.d32(v as u32 as i32);
        } else if (v as i64) >= i64::from(i32::MIN) && (v as i64) < 0 {
            // mov r64, simm32
            self.op(None, true, false, &[0xc7], 0, Rm::R(r));
            self.d32(v as i32);
        } else {
            self.b(0x48 | u8::from(r >= 8));
            self.b(0xb8 + (r & 7) as u8);
            self.bytes(&v.to_le_bytes());
        }
    }

    /// Integer register `r` = `v` as `k`, extended by `signed` to 64 bits.
    fn load(&mut self, r: u32, v: V, k: K, signed: bool) {
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
                self.mov_imm(r, x);
            }
            V::M(m) => {
                let rm = self.mem(m, R10);
                match (k, signed) {
                    (K::I8, true) => self.op(None, true, false, &[0x0f, 0xbe], r, rm),
                    (K::I8, false) => self.op(None, false, false, &[0x0f, 0xb6], r, rm),
                    (K::I16, true) => self.op(None, true, false, &[0x0f, 0xbf], r, rm),
                    (K::I16, false) => self.op(None, false, false, &[0x0f, 0xb7], r, rm),
                    (K::I32, true) => self.op(None, true, false, &[0x63], r, rm),
                    (K::I32 | K::F32, _) => self.op(None, false, false, &[0x8b], r, rm),
                    (K::I64 | K::F64, _) => self.op(None, true, false, &[0x8b], r, rm),
                }
            }
        }
    }

    fn store(&mut self, r: u32, m: Mem, k: K) {
        let rm = self.mem(m, R11);
        match k {
            K::I8 => self.op(None, false, true, &[0x88], r, rm),
            K::I16 => self.op(Some(0x66), false, false, &[0x89], r, rm),
            K::I32 | K::F32 => self.op(None, false, false, &[0x89], r, rm),
            K::I64 | K::F64 => self.op(None, true, false, &[0x89], r, rm),
        }
    }

    const fn sse(k: K) -> u8 {
        if matches!(k, K::F32) { 0xf3 } else { 0xf2 }
    }

    fn load_fp(&mut self, x: u32, v: V, k: K) {
        match v {
            V::I(bits) => {
                self.mov_imm(RAX, bits as u64);
                // movq / movd xmm, rax
                self.op(Some(0x66), k == K::F64, false, &[0x0f, 0x6e], x, Rm::R(RAX));
            }
            V::M(m) => {
                let rm = self.mem(m, R10);
                self.op(Some(Self::sse(k)), false, false, &[0x0f, 0x10], x, rm);
            }
        }
    }

    fn store_fp(&mut self, x: u32, m: Mem, k: K) {
        let rm = self.mem(m, R11);
        self.op(Some(Self::sse(k)), false, false, &[0x0f, 0x11], x, rm);
    }

    fn lea(&mut self, r: u32, m: Mem) {
        let rm = self.mem(m, r);
        self.op(None, true, false, &[0x8d], r, rm);
    }

    fn jmp(&mut self, l: Label) {
        self.b(0xe9);
        self.fixes.push((self.code.len(), l));
        self.d32(0);
    }

    fn jcc(&mut self, cc: u8, l: Label) {
        self.bytes(&[0x0f, 0x80 + cc]);
        self.fixes.push((self.code.len(), l));
        self.d32(0);
    }

    /// A forward `jcc` to a not yet known spot: its rel32's position.
    fn jcc_fwd(&mut self, cc: u8) -> usize {
        self.bytes(&[0x0f, 0x80 + cc]);
        self.d32(0);
        self.code.len() - 4
    }

    fn jmp_fwd(&mut self) -> usize {
        self.b(0xe9);
        self.d32(0);
        self.code.len() - 4
    }

    /// Point the rel32 at `at` here.
    fn here(&mut self, at: usize) {
        let d = (self.code.len() - (at + 4)) as i32;
        self.code[at..at + 4].copy_from_slice(&d.to_le_bytes());
    }

    /// `setcc al; movzx eax, al`.
    fn setcc(&mut self, cc: u8) {
        self.bytes(&[0x0f, 0x90 + cc, 0xc0, 0x0f, 0xb6, 0xc0]);
    }

    fn alu(&mut self, opc: u8, w: bool, dst: u32, src: u32) {
        self.op(None, w, false, &[opc], src, Rm::R(dst));
    }

    fn prologue(&mut self) {
        self.bytes(&[0x55, 0x48, 0x89, 0xe5]); // push rbp; mov rbp, rsp
        let n = self.frame;
        let pages = n / PAGE;
        if pages > 8 {
            self.mov_imm(R11, u64::from(pages));
            let top = self.code.len();
            self.bytes(&[0x48, 0x81, 0xec]); // sub rsp, imm32
            self.d32(PAGE as i32);
            self.bytes(&[0x48, 0x83, 0x0c, 0x24, 0x00]); // or qword [rsp], 0
            self.bytes(&[0x49, 0xff, 0xcb]); // dec r11
            self.bytes(&[0x0f, 0x85]); // jnz top
            let d = top as i32 - (self.code.len() as i32 + 4);
            self.d32(d);
        } else {
            for _ in 0..pages {
                self.bytes(&[0x48, 0x81, 0xec]);
                self.d32(PAGE as i32);
                self.bytes(&[0x48, 0x83, 0x0c, 0x24, 0x00]);
            }
        }
        let rest = n % PAGE;
        if rest != 0 {
            self.bytes(&[0x48, 0x81, 0xec]);
            self.d32(rest as i32);
        }
    }

    fn epilogue(&mut self) {
        self.bytes(&[0x48, 0x89, 0xec, 0x5d, 0xc3]); // mov rsp, rbp; pop rbp; ret
    }

    fn copy(&mut self, dst: Mem, src: Mem, size: u32, zero: bool) {
        if size > 128 {
            if !zero {
                self.lea(RSI, src);
            }
            self.lea(RDI, dst);
            self.mov_imm(RCX, u64::from(size));
            if zero {
                self.bytes(&[0x31, 0xc0, 0xf3, 0xaa]); // xor eax, eax; rep stosb
            } else {
                self.bytes(&[0xf3, 0xa4]); // rep movsb
            }
            return;
        }
        if !zero {
            self.lea(R10, src);
        }
        self.lea(R11, dst);
        if zero {
            self.bytes(&[0x31, 0xc0]);
        }
        self.copy_words(size, zero);
    }

    /// `[r11 + i] = [r10 + i]` (or zero) for `size` bytes.
    fn copy_words(&mut self, size: u32, zero: bool) {
        let mut off = 0i32;
        let mut rest = size;
        for (n, k) in [(8u32, K::I64), (4, K::I32), (2, K::I16), (1, K::I8)] {
            while rest >= n {
                if !zero {
                    let rm = Rm::M(R10, off);
                    match k {
                        K::I64 => self.op(None, true, false, &[0x8b], RAX, rm),
                        K::I32 => self.op(None, false, false, &[0x8b], RAX, rm),
                        K::I16 => self.op(None, false, false, &[0x0f, 0xb7], RAX, rm),
                        _ => self.op(None, false, false, &[0x0f, 0xb6], RAX, rm),
                    }
                }
                let rm = Rm::M(R11, off);
                match k {
                    K::I64 => self.op(None, true, false, &[0x89], RAX, rm),
                    K::I32 => self.op(None, false, false, &[0x89], RAX, rm),
                    K::I16 => self.op(Some(0x66), false, false, &[0x89], RAX, rm),
                    _ => self.op(None, false, true, &[0x88], RAX, rm),
                }
                rest -= n;
                off += n as i32;
            }
        }
    }

    fn bin_int(&mut self, op: Bin, k: K, signed: bool) {
        // rax = rax op rcx
        let w = k == K::I64;
        match op {
            Bin::Add => self.alu(0x01, w, RAX, RCX),
            Bin::Sub => self.alu(0x29, w, RAX, RCX),
            Bin::And => self.alu(0x21, w, RAX, RCX),
            Bin::Or => self.alu(0x09, w, RAX, RCX),
            Bin::Xor => self.alu(0x31, w, RAX, RCX),
            Bin::Mul => self.op(None, w, false, &[0x0f, 0xaf], RAX, Rm::R(RCX)),
            Bin::Div | Bin::Rem => {
                if signed {
                    // cqo / cdq; idiv rcx
                    if w {
                        self.bytes(&[0x48, 0x99]);
                    } else {
                        self.b(0x99);
                    }
                    self.op(None, w, false, &[0xf7], 7, Rm::R(RCX));
                } else {
                    self.bytes(&[0x31, 0xd2]); // xor edx, edx
                    self.op(None, w, false, &[0xf7], 6, Rm::R(RCX));
                }
                if op == Bin::Rem {
                    self.op(None, true, false, &[0x89], RDX, Rm::R(RAX));
                }
            }
            Bin::Shl => self.op(None, w, false, &[0xd3], 4, Rm::R(RAX)),
            Bin::Shr => self.op(
                None,
                w,
                false,
                &[0xd3],
                if signed { 7 } else { 5 },
                Rm::R(RAX),
            ),
        }
    }

    fn inst(&mut self, i: &Inst, next: Option<&Inst>) {
        match i {
            Inst::Label(l) => self.labels[*l as usize] = Some(self.code.len()),
            Inst::Jmp(l) => {
                if !matches!(next, Some(Inst::Label(n)) if n == l) {
                    self.jmp(*l);
                }
            }
            Inst::Br { c, t, f } => {
                if let V::I(v) = c {
                    self.jmp(if *v & 0xff != 0 { *t } else { *f });
                    return;
                }
                self.load(RAX, *c, K::I8, false);
                self.bytes(&[0x85, 0xc0]); // test eax, eax
                self.jcc(CC_NE, *t);
                if !matches!(next, Some(Inst::Label(n)) if n == f) {
                    self.jmp(*f);
                }
            }
            Inst::Mov { k, dst, src } => {
                self.load(RAX, *src, *k, false);
                self.store(RAX, *dst, *k);
            }
            Inst::Copy { dst, src, size } => self.copy(*dst, *src, *size, false),
            Inst::Zero { dst, size } => self.copy(*dst, *dst, *size, true),
            Inst::Addr { dst, src } => {
                self.lea(RAX, *src);
                self.store(RAX, *dst, K::I64);
            }
            Inst::Sym { dst, sym, got } => {
                if *got {
                    self.op_rip(None, true, &[0x8b], RAX, RelKind::X86GotLoad, *sym);
                } else {
                    self.op_rip(None, true, &[0x8d], RAX, RelKind::X86Pc32, *sym);
                }
                self.store(RAX, *dst, K::I64);
            }
            Inst::Tls { dst, sym } => {
                if self.obj.elf {
                    // Initial exec: the offset from the thread pointer.
                    self.op_rip(None, true, &[0x8b], RAX, RelKind::X86Tls, *sym);
                    // mov rcx, fs:[0]; add rax, rcx
                    self.bytes(&[0x64, 0x48, 0x8b, 0x0c, 0x25, 0, 0, 0, 0]);
                    self.alu(0x01, true, RAX, RCX);
                } else {
                    // Mach-O: the descriptor's getter, address in rax.
                    self.op_rip(None, true, &[0x8b], RDI, RelKind::X86Tls, *sym);
                    self.bytes(&[0xff, 0x17]); // call [rdi]
                }
                self.store(RAX, *dst, K::I64);
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
                    self.load_fp(XMM1, *b, *k);
                    self.load_fp(XMM0, *a, *k);
                    let opc = match op {
                        Bin::Add => 0x58,
                        Bin::Sub => 0x5c,
                        Bin::Mul => 0x59,
                        _ => 0x5e,
                    };
                    self.op(
                        Some(Self::sse(*k)),
                        false,
                        false,
                        &[0x0f, opc],
                        XMM0,
                        Rm::R(XMM1),
                    );
                    self.store_fp(XMM0, *dst, *k);
                    return;
                }
                self.load(RCX, *b, *k, *signed);
                self.load(RAX, *a, *k, *signed);
                self.bin_int(*op, *k, *signed);
                self.store(RAX, *dst, *k);
            }
            Inst::Ovf {
                op,
                k,
                signed,
                dst,
                a,
                b,
                fail,
            } => {
                self.load(RCX, *b, *k, *signed);
                self.load(RAX, *a, *k, *signed);
                match k {
                    K::I64 | K::I32 => {
                        let w = *k == K::I64;
                        match op {
                            Bin::Add => self.alu(0x01, w, RAX, RCX),
                            Bin::Sub => self.alu(0x29, w, RAX, RCX),
                            _ if *signed => self.op(None, w, false, &[0x0f, 0xaf], RAX, Rm::R(RCX)),
                            // mul rcx: rdx:rax; OF / CF when the high half is used.
                            _ => self.op(None, w, false, &[0xf7], 4, Rm::R(RCX)),
                        }
                        let cc = match (op, signed) {
                            (_, true) | (Bin::Mul, false) => CC_O,
                            _ => CC_B,
                        };
                        self.jcc(cc, *fail);
                    }
                    _ => {
                        // 8 / 16 bits in 32: the result must equal its
                        // own extension.
                        self.bin_int(*op, K::I32, *signed);
                        let opc = match (k, signed) {
                            (K::I8, true) => [0x0f, 0xbe],
                            (K::I8, false) => [0x0f, 0xb6],
                            (_, true) => [0x0f, 0xbf],
                            _ => [0x0f, 0xb7],
                        };
                        self.op(None, false, false, &opc, RCX, Rm::R(RAX));
                        self.alu(0x39, false, RAX, RCX);
                        self.jcc(CC_NE, *fail);
                    }
                }
                self.store(RAX, *dst, *k);
            }
            Inst::Un { op, k, dst, a } => self.un(*op, *k, *dst, *a),
            Inst::Cmp {
                cc,
                k,
                signed,
                dst,
                a,
                b,
            } => {
                if k.is_float() {
                    self.load_fp(XMM0, *a, *k);
                    self.load_fp(XMM1, *b, *k);
                    let pre = if *k == K::F64 { Some(0x66) } else { None };
                    let ucomi = |s: &mut Self, x: u32, y: u32| {
                        s.op(pre, false, false, &[0x0f, 0x2e], x, Rm::R(y));
                    };
                    match cc {
                        Cc::Eq | Cc::Ne => {
                            ucomi(self, XMM0, XMM1);
                            let (c1, c2, comb) = if *cc == Cc::Eq {
                                (CC_E, CC_NP, 0x21)
                            } else {
                                (CC_NE, CC_P, 0x09)
                            };
                            self.bytes(&[0x0f, 0x90 + c1, 0xc0]); // setcc al
                            self.bytes(&[0x0f, 0x90 + c2, 0xc1]); // setcc cl
                            self.bytes(&[comb - 1, 0xc8]); // and / or al, cl
                            self.bytes(&[0x0f, 0xb6, 0xc0]);
                        }
                        Cc::Lt | Cc::Le => {
                            ucomi(self, XMM1, XMM0);
                            self.setcc(if *cc == Cc::Lt { CC_A } else { CC_AE });
                        }
                        Cc::Gt | Cc::Ge => {
                            ucomi(self, XMM0, XMM1);
                            self.setcc(if *cc == Cc::Gt { CC_A } else { CC_AE });
                        }
                    }
                    self.store(RAX, *dst, K::I8);
                    return;
                }
                self.load(RAX, *a, *k, *signed);
                self.load(RCX, *b, *k, *signed);
                self.alu(0x39, true, RAX, RCX);
                let c = match (cc, signed) {
                    (Cc::Eq, _) => CC_E,
                    (Cc::Ne, _) => CC_NE,
                    (Cc::Lt, true) => CC_L,
                    (Cc::Lt, false) => CC_B,
                    (Cc::Le, true) => CC_LE,
                    (Cc::Le, false) => CC_BE,
                    (Cc::Gt, true) => CC_G,
                    (Cc::Gt, false) => CC_A,
                    (Cc::Ge, true) => CC_GE,
                    (Cc::Ge, false) => CC_AE,
                };
                self.setcc(c);
                self.store(RAX, *dst, K::I8);
            }
            Inst::Conv {
                conv,
                from,
                to,
                dst,
                a,
            } => self.conv(*conv, *from, *to, *dst, *a),
            Inst::AtomicLoad { k, dst, ptr } => {
                self.lea(R10, *ptr);
                self.sized_load(*k, RAX, Rm::M(R10, 0));
                self.store(RAX, *dst, *k);
            }
            Inst::AtomicStore { k, ptr, src } => {
                self.load(RAX, *src, *k, false);
                self.lea(R10, *ptr);
                self.xchg(*k);
            }
            Inst::AtomicRmw {
                op,
                k,
                dst,
                ptr,
                val,
            } => {
                self.load(RCX, *val, *k, false);
                self.lea(R10, *ptr);
                match op {
                    Rmw::Xchg => {
                        self.op(None, true, false, &[0x89], RCX, Rm::R(RAX));
                        self.xchg(*k);
                    }
                    Rmw::Add | Rmw::Sub => {
                        if *op == Rmw::Sub {
                            self.op(None, true, false, &[0xf7], 3, Rm::R(RCX)); // neg rcx
                        }
                        self.b(0xf0); // lock xadd [r10], rcx
                        self.sized(*k, &[0x0f, 0xc1], &[0x0f, 0xc0], RCX, Rm::M(R10, 0));
                        self.op(None, true, false, &[0x89], RCX, Rm::R(RAX));
                    }
                    Rmw::And | Rmw::Or | Rmw::Xor => {
                        // A compare-and-swap loop: rax = old, rdx = new.
                        self.sized_load(*k, RAX, Rm::M(R10, 0));
                        let top = self.code.len();
                        self.op(None, true, false, &[0x89], RAX, Rm::R(RDX));
                        let opc = match op {
                            Rmw::And => 0x21,
                            Rmw::Or => 0x09,
                            _ => 0x31,
                        };
                        self.alu(opc, true, RDX, RCX);
                        self.b(0xf0);
                        self.sized(*k, &[0x0f, 0xb1], &[0x0f, 0xb0], RDX, Rm::M(R10, 0));
                        self.bytes(&[0x0f, 0x85]);
                        let d = top as i32 - (self.code.len() as i32 + 4);
                        self.d32(d);
                    }
                }
                self.store(RAX, *dst, *k);
            }
            Inst::Cas {
                k,
                dst,
                ptr,
                expected,
                new,
            } => {
                self.load(RAX, *expected, *k, false);
                self.load(RCX, *new, *k, false);
                self.lea(R10, *ptr);
                self.b(0xf0);
                self.sized(*k, &[0x0f, 0xb1], &[0x0f, 0xb0], RCX, Rm::M(R10, 0));
                self.store(RAX, *dst, *k);
            }
            Inst::Call {
                callee,
                args,
                rets,
                sret,
                variadic,
            } => self.call(callee, args, rets, *sret, *variadic),
            Inst::Param { part, dst } => match part.loc {
                Loc::Int(r) => self.store(ARGS[r as usize], *dst, part.k),
                Loc::Fp(r) => self.store_fp(u32::from(r), *dst, part.k),
                Loc::Stack(o) => {
                    let rm = Rm::M(RBP, 16 + o as i32);
                    self.op(None, true, false, &[0x8b], RAX, rm);
                    self.store(RAX, *dst, part.k);
                }
                Loc::Sret => self.store(RDI, *dst, K::I64),
            },
            Inst::Ret { vals } => {
                // x87 results: the last pushed first, so `st0` is the
                // first.
                let x87 = [3, 2]
                    .into_iter()
                    .filter_map(|n| vals.iter().find(|(p, _)| p.loc == Loc::Fp(n)));
                for (p, v) in x87 {
                    let rm = match v {
                        V::M(m) => self.mem(*m, R10),
                        V::I(bits) => {
                            self.mov_imm(RAX, *bits as u64);
                            self.op(None, true, false, &[0x89], RAX, Rm::M(RSP, -8));
                            Rm::M(RSP, -8)
                        }
                    };
                    // fld dword / qword
                    let opc = if p.k == K::F32 { 0xd9 } else { 0xdd };
                    self.op(None, false, false, &[opc], 0, rm);
                }
                // Floats first: a float constant passes through rax.
                for (p, v) in vals {
                    if let Loc::Fp(r @ 0..2) = p.loc {
                        self.load_fp(u32::from(r), *v, p.k);
                    }
                }
                for (p, v) in vals {
                    if let Loc::Int(r) = p.loc {
                        self.load(RETS[r as usize], *v, p.k, p.signed);
                    }
                }
                self.epilogue();
            }
            Inst::Trap => self.bytes(&[0x0f, 0x0b]), // ud2
            Inst::Line(line, col, scope) => {
                let at = self.code.len() as u32;
                self.lines.push((at, *line, *col, *scope));
            }
        }
    }

    /// `opc` (16 / 32 / 64-bit) or `byte_opc` by `k`, `reg`, `rm`.
    fn sized(&mut self, k: K, opc: &[u8], byte_opc: &[u8], reg: u32, rm: Rm) {
        match k {
            K::I8 => self.op(None, false, true, byte_opc, reg, rm),
            K::I16 => self.op(Some(0x66), false, false, opc, reg, rm),
            K::I32 | K::F32 => self.op(None, false, false, opc, reg, rm),
            K::I64 | K::F64 => self.op(None, true, false, opc, reg, rm),
        }
    }

    fn sized_load(&mut self, k: K, r: u32, rm: Rm) {
        match k {
            K::I8 => self.op(None, false, false, &[0x0f, 0xb6], r, rm),
            K::I16 => self.op(None, false, false, &[0x0f, 0xb7], r, rm),
            K::I32 | K::F32 => self.op(None, false, false, &[0x8b], r, rm),
            K::I64 | K::F64 => self.op(None, true, false, &[0x8b], r, rm),
        }
    }

    /// `xchg [r10], rax` (sequentially consistent store); the old value
    /// in rax.
    fn xchg(&mut self, k: K) {
        self.sized(k, &[0x87], &[0x86], RAX, Rm::M(R10, 0));
    }

    fn call(
        &mut self,
        callee: &Callee,
        args: &[(crate::lir::Part, V)],
        rets: &[(crate::lir::Part, Mem)],
        sret: Option<Mem>,
        variadic: bool,
    ) {
        for (p, v) in args {
            if let Loc::Stack(o) = p.loc {
                self.load(RAX, *v, p.k, p.signed);
                self.op(None, true, false, &[0x89], RAX, Rm::M(RSP, o as i32));
            }
        }
        let mut fps = 0;
        for (p, v) in args {
            match p.loc {
                Loc::Int(r) => self.load(ARGS[r as usize], *v, p.k, p.signed),
                Loc::Fp(r) => {
                    self.load_fp(u32::from(r), *v, p.k);
                    fps = fps.max(r + 1);
                }
                _ => {}
            }
        }
        if let Some(m) = sret {
            self.lea(RDI, m);
        }
        if variadic {
            self.mov_imm(RAX, u64::from(fps));
        }
        match callee {
            Callee::Sym(s) => {
                self.b(0xe8);
                let off = self.start + self.code.len() as u32;
                self.relocs.push((off, RelKind::X86Call, *s));
                self.d32(0);
            }
            Callee::Ptr(m) => {
                let rm = self.mem(*m, R10);
                self.op(None, true, false, &[0x8b], R11, rm);
                self.op(None, false, false, &[0xff], 2, Rm::R(R11)); // call r11
            }
        }
        // x87 results (`st0`, then `st1`), popped in order.
        let x87: Vec<_> = [2, 3]
            .into_iter()
            .filter_map(|n| rets.iter().find(|(p, _)| p.loc == Loc::Fp(n)))
            .collect();
        for (p, m) in rets {
            match p.loc {
                Loc::Int(r) => self.store(RETS[r as usize], *m, p.k),
                Loc::Fp(r) if r < 2 => self.store_fp(u32::from(r), *m, p.k),
                _ => {}
            }
        }
        for (p, m) in x87 {
            let rm = self.mem(*m, R11);
            // fstp dword / qword
            let opc = if p.k == K::F32 { 0xd9 } else { 0xdd };
            self.op(None, false, false, &[opc], 3, rm);
        }
    }

    fn un(&mut self, op: Un, k: K, dst: Mem, a: V) {
        let w = k == K::I64;
        let bits = k.bits();
        match op {
            Un::Sqrt => {
                self.load_fp(XMM0, a, k);
                self.op(
                    Some(Self::sse(k)),
                    false,
                    false,
                    &[0x0f, 0x51],
                    XMM0,
                    Rm::R(XMM0),
                );
                self.store_fp(XMM0, dst, k);
                return;
            }
            Un::Neg if k.is_float() => {
                // Flip the sign bit.
                self.load(RAX, a, k, false);
                if k == K::F64 {
                    self.mov_imm(RCX, 1 << 63);
                    self.alu(0x31, true, RAX, RCX);
                } else {
                    self.b(0x35); // xor eax, imm32
                    self.d32(i32::MIN);
                }
            }
            Un::Neg => {
                self.load(RAX, a, k, true);
                self.op(None, w, false, &[0xf7], 3, Rm::R(RAX));
            }
            Un::Not => {
                self.load(RAX, a, k, false);
                self.op(None, w, false, &[0xf7], 2, Rm::R(RAX));
            }
            Un::Popcnt => {
                self.load(RAX, a, k, false);
                // The classic bit-slicing count, 64-bit.
                let step = |s: &mut Self, sh: u8, mask: u64| {
                    s.op(None, true, false, &[0x89], RAX, Rm::R(RCX)); // rcx = x
                    s.op(None, true, false, &[0xc1], 5, Rm::R(RCX)); // shr rcx, sh
                    s.b(sh);
                    s.mov_imm(RDX, mask);
                    s.alu(0x21, true, RCX, RDX);
                    s.alu(0x21, true, RAX, RDX);
                };
                // x -= (x >> 1) & 0x55..
                self.op(None, true, false, &[0x89], RAX, Rm::R(RCX));
                self.op(None, true, false, &[0xd1], 5, Rm::R(RCX)); // shr rcx, 1
                self.mov_imm(RDX, 0x5555_5555_5555_5555);
                self.alu(0x21, true, RCX, RDX);
                self.alu(0x29, true, RAX, RCX);
                // x = (x & 0x33..) + ((x >> 2) & 0x33..)
                step(self, 2, 0x3333_3333_3333_3333);
                self.alu(0x01, true, RAX, RCX);
                // x = (x + (x >> 4)) & 0x0f..
                self.op(None, true, false, &[0x89], RAX, Rm::R(RCX));
                self.op(None, true, false, &[0xc1], 5, Rm::R(RCX));
                self.b(4);
                self.alu(0x01, true, RAX, RCX);
                self.mov_imm(RDX, 0x0f0f_0f0f_0f0f_0f0f);
                self.alu(0x21, true, RAX, RDX);
                // x = (x * 0x0101..) >> 56
                self.mov_imm(RDX, 0x0101_0101_0101_0101);
                self.op(None, true, false, &[0x0f, 0xaf], RAX, Rm::R(RDX));
                self.op(None, true, false, &[0xc1], 5, Rm::R(RAX));
                self.b(56);
            }
            Un::Clz | Un::Ctz => {
                self.load(RAX, a, k, false);
                self.alu(0x85, true, RAX, RAX); // test rax, rax
                let zero = self.jcc_fwd(CC_E);
                if op == Un::Clz {
                    self.op(None, true, false, &[0x0f, 0xbd], RAX, Rm::R(RAX)); // bsr
                    self.mov_imm(RCX, u64::from(bits - 1));
                    self.alu(0x29, true, RCX, RAX);
                    self.op(None, true, false, &[0x89], RCX, Rm::R(RAX));
                } else {
                    self.op(None, true, false, &[0x0f, 0xbc], RAX, Rm::R(RAX)); // bsf
                }
                let done = self.jmp_fwd();
                self.here(zero);
                self.mov_imm(RAX, u64::from(bits));
                self.here(done);
            }
            Un::Bswap => {
                self.load(RAX, a, k, false);
                match k {
                    K::I16 => self.bytes(&[0x66, 0xc1, 0xc0, 0x08]), // rol ax, 8
                    K::I32 => self.bytes(&[0x0f, 0xc8]),
                    K::I64 => self.bytes(&[0x48, 0x0f, 0xc8]),
                    _ => {}
                }
            }
        }
        self.store(RAX, dst, k);
    }

    fn conv(&mut self, conv: Conv, from: K, to: K, dst: Mem, a: V) {
        match conv {
            Conv::Int { signed } => {
                self.load(RAX, a, from, signed);
                self.store(RAX, dst, to);
            }
            Conv::ToBool => {
                self.load(RAX, a, from, false);
                self.alu(0x85, true, RAX, RAX);
                self.setcc(CC_NE);
                self.store(RAX, dst, K::I8);
            }
            Conv::IToF { signed } => {
                self.load(RAX, a, from, signed);
                let cvt = |s: &mut Self, r: u32| {
                    s.op(
                        Some(Self::sse(to)),
                        true,
                        false,
                        &[0x0f, 0x2a],
                        XMM0,
                        Rm::R(r),
                    );
                };
                if !signed && from == K::I64 {
                    // u64 ≥ 2^63: halve (keeping the low bit), convert,
                    // double.
                    self.alu(0x85, true, RAX, RAX);
                    let big = self.jcc_fwd(CC_S);
                    cvt(self, RAX);
                    let done = self.jmp_fwd();
                    self.here(big);
                    self.op(None, true, false, &[0x89], RAX, Rm::R(RCX));
                    self.op(None, true, false, &[0xd1], 5, Rm::R(RCX)); // shr rcx, 1
                    self.bytes(&[0x83, 0xe0, 0x01]); // and eax, 1
                    self.alu(0x09, true, RCX, RAX);
                    cvt(self, RCX);
                    self.op(
                        Some(Self::sse(to)),
                        false,
                        false,
                        &[0x0f, 0x58],
                        XMM0,
                        Rm::R(XMM0),
                    );
                    self.here(done);
                } else {
                    cvt(self, RAX);
                }
                self.store_fp(XMM0, dst, to);
            }
            Conv::FToI { signed, bits } => self.f_to_i(from, to, dst, a, signed, bits),
            Conv::FToF => {
                self.load_fp(XMM0, a, from);
                self.op(
                    Some(Self::sse(from)),
                    false,
                    false,
                    &[0x0f, 0x5a],
                    XMM0,
                    Rm::R(XMM0),
                );
                self.store_fp(XMM0, dst, to);
            }
            Conv::Bits => {
                self.load(RAX, a, from, false);
                self.store(RAX, dst, to);
            }
        }
    }

    /// Float → integer, saturating, NaN to 0 (`bits` of the destination
    /// are the integer's).
    fn f_to_i(&mut self, from: K, to: K, dst: Mem, a: V, signed: bool, bits: u32) {
        let pre = Self::sse(from);
        let ucomi_pre = if from == K::F64 { Some(0x66) } else { None };
        // xmm1 = 2^63 (as `from`).
        let two63 = if from == K::F64 {
            (63f64.exp2()).to_bits()
        } else {
            u64::from(63f32.exp2().to_bits())
        };
        self.load_fp(XMM0, a, from);
        self.mov_imm(RAX, two63);
        self.op(
            Some(0x66),
            from == K::F64,
            false,
            &[0x0f, 0x6e],
            XMM1,
            Rm::R(RAX),
        );
        let cvtt = |s: &mut Self| s.op(Some(pre), true, false, &[0x0f, 0x2c], RAX, Rm::R(XMM0));
        let ucomi = |s: &mut Self, x: u32, y: u32| {
            s.op(ucomi_pre, false, false, &[0x0f, 0x2e], x, Rm::R(y));
        };
        let mut ends = Vec::new();
        // NaN (and, unsigned, negative): 0.
        ucomi(self, XMM0, XMM0);
        let mut zeros = vec![self.jcc_fwd(CC_P)];
        if signed {
            ucomi(self, XMM0, XMM1);
            let big = self.jcc_fwd(CC_AE);
            cvtt(self); // too negative: i64::MIN
            ends.push(self.jmp_fwd());
            self.here(big);
            self.mov_imm(RAX, i64::MAX as u64);
        } else {
            // ≥ 2^64: max; ≥ 2^63: through the sign bit.
            self.bytes(&[0x0f, 0x57, 0xd2]); // xorps xmm2, xmm2
            ucomi(self, XMM0, 2);
            zeros.push(self.jcc_fwd(CC_B));
            ucomi(self, XMM0, XMM1);
            let high = self.jcc_fwd(CC_AE);
            cvtt(self);
            ends.push(self.jmp_fwd());
            self.here(high);
            self.op(Some(pre), false, false, &[0x0f, 0x5c], XMM0, Rm::R(XMM1)); // sub 2^63
            ucomi(self, XMM0, XMM1);
            let huge = self.jcc_fwd(CC_AE);
            cvtt(self);
            self.mov_imm(RCX, 1 << 63);
            self.alu(0x31, true, RAX, RCX);
            ends.push(self.jmp_fwd());
            self.here(huge);
            self.mov_imm(RAX, u64::MAX);
        }
        ends.push(self.jmp_fwd());
        for z in zeros {
            self.here(z);
        }
        self.bytes(&[0x31, 0xc0]); // xor eax, eax
        for e in ends {
            self.here(e);
        }
        if bits < 64 {
            let (max, min) = if signed {
                ((1i64 << (bits - 1)) - 1, -(1i64 << (bits - 1)))
            } else {
                ((1i64 << bits) - 1, 0)
            };
            self.mov_imm(RCX, max as u64);
            self.alu(0x39, true, RAX, RCX);
            // cmovg / cmova rax, rcx
            let cc = if signed { CC_G } else { CC_A };
            self.op(None, true, false, &[0x0f, 0x40 + cc], RAX, Rm::R(RCX));
            if signed {
                self.mov_imm(RCX, min as u64);
                self.alu(0x39, true, RAX, RCX);
                self.op(None, true, false, &[0x0f, 0x40 + CC_L], RAX, Rm::R(RCX));
            }
        }
        self.store(RAX, dst, to);
    }
}

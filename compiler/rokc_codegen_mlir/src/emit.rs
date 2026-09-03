//! Standard-MLIR text emission.
//!
//! Output format follows upstream MLIR exactly. SSA value numbering is
//! local to each `func.func`. The pipeline stops here; downstream tools
//! (`mlir-opt`, `mlir-translate`, `clang`/`lld`) handle the rest.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use rokc_ir_common::{ConstVal, FunctionId, LocalId, PrimOp, PrimTy};
use rokc_mir::{
    BasicBlock, MirFunction, MirModule, MirTy, Operand, RValue, Statement, Terminator,
};

pub struct Emitter {
    out: String,
    pointer_width: u32,
    // Interned string-literal globals: content → symbol name. Emitted at
    // module top so all functions can reference them by `addressof`.
    str_globals: std::collections::BTreeMap<String, String>,
    next_str_id: u32,
}

impl Emitter {
    #[must_use]
    pub fn new(pointer_width: u32) -> Self {
        Self {
            out: String::new(),
            pointer_width,
            str_globals: std::collections::BTreeMap::new(),
            next_str_id: 0,
        }
    }

    pub fn emit_module(&mut self, module: &MirModule) {
        // The user's `fn main` is renamed to `rok_user_main`; the real
        // C entry point is a synthetic wrapper that brackets the user
        // body with runtime init / shutdown calls.
        let user_main_ret_ty = module
            .functions
            .iter()
            .find(|f| f.name == "main")
            .map(|f| f.ret_ty.clone());

        let mut fn_names: HashMap<FunctionId, String> = HashMap::new();
        for f in &module.functions {
            let mlir_name = if f.name == "main" {
                "rok_user_main".to_owned()
            } else {
                // MLIR / LLVM symbols can't carry `::`; module path
                // separators get rewritten to `__`. Same convention as
                // impl-method mangling, so the namespaces compose without
                // collision risk in the small.
                f.name.replace("::", "__")
            };
            fn_names.insert(f.id, mlir_name);
        }

        self.out.push_str("module {\n");
        for f in &module.functions {
            let symbol = fn_names.get(&f.id).cloned().unwrap_or_else(|| f.name.clone());
            self.emit_function(f, &symbol, &fn_names);
        }
        if let Some(ret_ty) = user_main_ret_ty {
            self.emit_main_wrapper(&ret_ty);
        }
        self.emit_string_globals();
        self.emit_static_globals(module);
        self.out.push_str("}\n");
    }

    fn emit_static_globals(&mut self, module: &MirModule) {
        for s in &module.statics {
            let ty_str = mlir_type(&s.ty, self.pointer_width);
            let constness = if s.is_mut { "" } else { "constant " };
            let init = format_const_attr(&s.init, &s.ty);
            let _ = writeln!(
                self.out,
                "  llvm.mlir.global internal {constness}@{name}({init}) {{addr_space = 0 : i32}} : {ty_str}",
                name = s.name
            );
        }
    }

    // Emit one `llvm.mlir.global` per interned string literal. The
    // literals are stored as `internal constant` byte arrays with a
    // trailing NUL so they can be passed to C-string-expecting APIs.
    fn emit_string_globals(&mut self) {
        let entries: Vec<(String, String)> = self
            .str_globals
            .iter()
            .map(|(content, sym)| (content.clone(), sym.clone()))
            .collect();
        for (content, sym) in entries {
            let bytes = content.as_bytes();
            let mut escaped = String::new();
            for &b in bytes {
                if b == b'\\' || b == b'"' {
                    escaped.push('\\');
                    escaped.push(b as char);
                } else if (0x20..0x7f).contains(&b) {
                    escaped.push(b as char);
                } else {
                    let _ = write!(escaped, "\\{:02X}", b);
                }
            }
            // `\00` terminator so `puts` / `printf` see a C string.
            let len = bytes.len() + 1;
            let _ = writeln!(
                self.out,
                "  llvm.mlir.global internal constant @{sym}(\"{escaped}\\00\") {{addr_space = 0 : i32}} : !llvm.array<{len} x i8>"
            );
        }
    }

    fn emit_function(
        &mut self,
        f: &MirFunction,
        symbol: &str,
        fn_names: &HashMap<FunctionId, String>,
    ) {
        // Empty-body functions become external declarations — no body
        // braces, just a signature with `private` linkage.
        let is_decl = f.blocks.is_empty();
        if is_decl {
            self.out.push_str("  func.func private @");
        } else {
            self.out.push_str("  func.func @");
        }
        self.out.push_str(symbol);
        self.out.push('(');
        for (i, _p) in f.params.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            let ty = f.param_tys.get(i).cloned().unwrap_or(MirTy::Any);
            let _ = write!(
                self.out,
                "%arg{i}: {}",
                mlir_type(&ty, self.pointer_width)
            );
        }
        self.out.push(')');
        if !matches!(f.ret_ty, MirTy::Unit) {
            let _ = write!(self.out, " -> {}", mlir_type(&f.ret_ty, self.pointer_width));
        }
        if is_decl {
            self.out.push('\n');
            return;
        }
        self.out.push_str(" {\n");

        let mut emit = FnEmit::new(f, self.pointer_width, fn_names, self.next_str_id);
        emit.emit_prelude();
        for b in &f.blocks {
            emit.emit_block(b);
        }
        // Hoist any string globals that this function discovered.
        for (content, sym) in std::mem::take(&mut emit.str_globals) {
            self.str_globals.insert(content, sym);
        }
        self.next_str_id += emit.next_str_id;
        self.out.push_str(&emit.finish());

        self.out.push_str("  }\n");
    }

    // Synthetic `main` wrapping the user's body with runtime calls.
    // Both runtime functions are forward-declared as private extern.
    fn emit_main_wrapper(&mut self, user_ret_ty: &MirTy) {
        let pw = self.pointer_width;
        self.out.push_str(
            "  func.func private @rok_runtime_init() -> ()\n  func.func private @rok_runtime_shutdown() -> ()\n",
        );
        self.out.push_str("  func.func @main() -> i32 {\n");
        self.out.push_str("    func.call @rok_runtime_init() : () -> ()\n");
        match user_ret_ty {
            MirTy::Unit => {
                self.out.push_str("    func.call @rok_user_main() : () -> ()\n");
                self.out.push_str("    func.call @rok_runtime_shutdown() : () -> ()\n");
                self.out.push_str("    %0 = arith.constant 0 : i32\n");
                self.out.push_str("    func.return %0 : i32\n");
            }
            other => {
                let ret = mlir_type(other, pw);
                let _ = writeln!(
                    self.out,
                    "    %0 = func.call @rok_user_main() : () -> {ret}"
                );
                self.out.push_str("    func.call @rok_runtime_shutdown() : () -> ()\n");
                // OS expects an i32 exit code; widen / narrow as needed.
                let _ = if matches!(other, MirTy::Prim(PrimTy::I32)) {
                    writeln!(self.out, "    func.return %0 : i32")
                } else {
                    let _ = writeln!(
                        self.out,
                        "    %1 = arith.trunci %0 : {ret} to i32"
                    );
                    writeln!(self.out, "    func.return %1 : i32")
                };
            }
        }
        self.out.push_str("  }\n");
    }

    #[must_use]
    pub fn finish(self) -> String {
        self.out
    }

    #[must_use]
    pub const fn pointer_width(&self) -> u32 {
        self.pointer_width
    }
}

struct FnEmit<'a> {
    f: &'a MirFunction,
    pointer_width: u32,
    body: String,
    /// SSA name for each local: function/block params hold their MLIR SSA
    /// directly; stack-slotted locals hold the memref ptr value here as a
    /// fallback if a load is requested before the slot is initialised.
    local_names: Vec<Option<String>>,
    /// `Some(slot_ssa)` for stack-slotted locals; `None` for params.
    slot_names: Vec<Option<String>>,
    /// Locals whose slot is allocated via `llvm.alloca` rather than
    /// `memref.alloca` — needed for aggregate types that the memref
    /// dialect can't hold (`!llvm.struct<...>`, `!llvm.ptr`).
    llvm_slot: HashSet<u32>,
    /// Set of locals that are block parameters (consumed as SSA values
    /// rather than stack-slotted).
    block_param_set: HashSet<u32>,
    next_ssa: u32,
    fn_names: &'a HashMap<FunctionId, String>,
    /// String literals discovered in this function (content → symbol).
    /// Merged into the parent emitter so module-level globals are
    /// emitted once for the whole TU.
    str_globals: std::collections::BTreeMap<String, String>,
    next_str_id: u32,
    str_id_base: u32,
}

impl<'a> FnEmit<'a> {
    fn new(
        f: &'a MirFunction,
        pointer_width: u32,
        fn_names: &'a HashMap<FunctionId, String>,
        str_id_base: u32,
    ) -> Self {
        // Block params are SSA values; everything else gets a stack slot.
        let mut block_param_set: HashSet<u32> = HashSet::new();
        for b in &f.blocks {
            for p in &b.params {
                block_param_set.insert(p.0);
            }
        }
        let mut local_names = vec![None; f.locals.len()];
        for (i, p) in f.params.iter().enumerate() {
            local_names[p.0 as usize] = Some(format!("%arg{i}"));
        }
        Self {
            f,
            pointer_width,
            body: String::new(),
            local_names,
            slot_names: vec![None; f.locals.len()],
            llvm_slot: HashSet::new(),
            block_param_set,
            next_ssa: 0,
            fn_names,
            str_globals: std::collections::BTreeMap::new(),
            next_str_id: 0,
            str_id_base,
        }
    }

    fn intern_string(&mut self, s: &str) -> String {
        if let Some(name) = self.str_globals.get(s) {
            return name.clone();
        }
        let name = format!("rok.str{}", self.str_id_base + self.next_str_id);
        self.next_str_id += 1;
        self.str_globals.insert(s.to_owned(), name.clone());
        name
    }

    fn is_block_param(&self, id: LocalId) -> bool {
        self.block_param_set.contains(&id.0)
    }

    /// Emit `memref.alloca` slots for every reassignable local, then
    /// store function args into their slots so subsequent loads see the
    /// initial value. Called once at the start of the entry block.
    fn emit_prelude(&mut self) {
        // `llvm.alloca` needs a size operand. Materialize a single
        // `i32 1` once and reuse it across the prelude.
        let mut alloca_size: Option<String> = None;
        for local in &self.f.locals {
            if self.is_block_param(local.id) {
                continue;
            }
            // `[T; N]` arrays use an `llvm.alloca` of `!llvm.array<N x T>`
            // uniformly. The `memref` dialect only accepts a narrow set
            // of element types, but the LLVM dialect accepts anything,
            // including nested arrays and aggregates.
            if let MirTy::Array(elem, n) = &local.ty {
                let slot = format!("%p{}", local.id.0);
                self.slot_names[local.id.0 as usize] = Some(slot.clone());
                let elem_ty = mlir_type(elem, self.pointer_width);
                let size = if let Some(s) = &alloca_size {
                    s.clone()
                } else {
                    let s = self.fresh_value();
                    let _ = writeln!(self.body, "    {s} = llvm.mlir.constant(1 : i32) : i32");
                    alloca_size = Some(s.clone());
                    s
                };
                self.llvm_slot.insert(local.id.0);
                let _ = writeln!(
                    self.body,
                    "    {slot} = llvm.alloca {size} x !llvm.array<{n} x {elem_ty}> : (i32) -> !llvm.ptr"
                );
                continue;
            }
            if is_memref_storable(&local.ty) {
                let ty = mlir_type(&local.ty, self.pointer_width);
                let slot = format!("%p{}", local.id.0);
                self.slot_names[local.id.0 as usize] = Some(slot.clone());
                let _ = writeln!(self.body, "    {slot} = memref.alloca() : memref<{ty}>");
                continue;
            }
            // Aggregates and pointer-shaped values get an LLVM-dialect
            // slot so they can survive across loop back-edges.
            if is_llvm_storable(&local.ty) {
                let ty = mlir_type(&local.ty, self.pointer_width);
                let slot = format!("%p{}", local.id.0);
                let size = if let Some(s) = &alloca_size {
                    s.clone()
                } else {
                    let s = self.fresh_value();
                    let _ = writeln!(self.body, "    {s} = llvm.mlir.constant(1 : i32) : i32");
                    alloca_size = Some(s.clone());
                    s
                };
                self.slot_names[local.id.0 as usize] = Some(slot.clone());
                self.llvm_slot.insert(local.id.0);
                let _ = writeln!(
                    self.body,
                    "    {slot} = llvm.alloca {size} x {ty} : (i32) -> !llvm.ptr"
                );
            }
        }
        // Seed each function-arg slot with the incoming SSA arg.
        for (i, p) in self.f.params.iter().enumerate() {
            let Some(slot) = self.slot_names.get(p.0 as usize).and_then(Option::as_ref).cloned()
            else {
                continue;
            };
            let ty = mlir_type(&self.f.locals[p.0 as usize].ty, self.pointer_width);
            if self.llvm_slot.contains(&p.0) {
                let _ = writeln!(
                    self.body,
                    "    llvm.store %arg{i}, {slot} : {ty}, !llvm.ptr"
                );
            } else {
                let _ = writeln!(
                    self.body,
                    "    memref.store %arg{i}, {slot}[] : memref<{ty}>"
                );
            }
        }
    }

    // Read a local. Block params and non-slotted locals return their SSA
    // name directly; memref-slotted locals get `memref.load`; llvm-slotted
    // locals get `llvm.load`.
    fn read_local(&mut self, id: LocalId) -> String {
        if self.is_block_param(id) || self.slot_names[id.0 as usize].is_none() {
            return self
                .local_names
                .get(id.0 as usize)
                .and_then(Option::as_ref)
                .cloned()
                .unwrap_or_else(|| {
                    // Truly unknown — emit a typed zero so callers stay valid.
                    let v = self.fresh_value();
                    let ty = mlir_type(&self.local_ty(id), self.pointer_width);
                    let _ = writeln!(self.body, "    {v} = arith.constant 0 : {ty}");
                    v
                });
        }
        let slot = self.slot_names[id.0 as usize].clone().unwrap();
        let v = self.fresh_value();
        let ty = mlir_type(&self.local_ty(id), self.pointer_width);
        if self.llvm_slot.contains(&id.0) {
            let _ = writeln!(self.body, "    {v} = llvm.load {slot} : !llvm.ptr -> {ty}");
        } else {
            let _ = writeln!(self.body, "    {v} = memref.load {slot}[] : memref<{ty}>");
        }
        v
    }

    fn write_local(&mut self, id: LocalId, value: &str) {
        if self.is_block_param(id) {
            return;
        }
        // Non-slotted locals: just remap the SSA name.
        if self.slot_names[id.0 as usize].is_none() {
            self.local_names[id.0 as usize] = Some(value.to_owned());
            return;
        }
        let slot = self.slot_names[id.0 as usize].clone().unwrap();
        let ty = mlir_type(&self.local_ty(id), self.pointer_width);
        if self.llvm_slot.contains(&id.0) {
            let _ = writeln!(self.body, "    llvm.store {value}, {slot} : {ty}, !llvm.ptr");
        } else {
            let _ = writeln!(self.body, "    memref.store {value}, {slot}[] : memref<{ty}>");
        }
    }

    fn finish(self) -> String {
        self.body
    }

    fn fresh_value(&mut self) -> String {
        let n = self.next_ssa;
        self.next_ssa += 1;
        format!("%{n}")
    }

    fn emit_block(&mut self, b: &BasicBlock) {
        // Multi-block functions need labels; the entry block is unlabeled
        // per MLIR convention. Block parameters appear in the header.
        if b.id.0 != 0 {
            // Allocate SSA names for block params.
            let mut header_args: Vec<String> = Vec::new();
            for p in &b.params {
                let name = self.fresh_value();
                let ty = self.local_ty(*p);
                header_args.push(format!("{name}: {}", mlir_type(&ty, self.pointer_width)));
                self.local_names[p.0 as usize] = Some(name);
            }
            if header_args.is_empty() {
                let _ = writeln!(self.body, "  ^bb{}:", b.id.0);
            } else {
                let _ = writeln!(
                    self.body,
                    "  ^bb{}({}):",
                    b.id.0,
                    header_args.join(", ")
                );
            }
        }
        for s in &b.stmts {
            self.emit_stmt(s);
        }
        self.emit_terminator(&b.terminator);
    }

    fn emit_stmt(&mut self, s: &Statement) {
        match s {
            Statement::Assign { target, rvalue } => {
                // `[a, b, c]` writes directly into the target's
                // memref slot — no intermediate SSA value.
                if let RValue::ArrayInit { elem_ty, elements } = rvalue {
                    self.emit_array_init(*target, elem_ty, elements);
                    return;
                }
                let ty = self.local_ty(*target);
                let val = self.compute_rvalue(&ty, rvalue);
                self.write_local(*target, &val);
            }
            Statement::ArrayWrite { array, index, value, elem_ty, len } => {
                self.emit_array_write(*array, index, value, elem_ty, *len);
            }
            Statement::StaticStore { name, value, ty } => {
                let val = self.materialize_operand(value, ty);
                let ty_str = mlir_type(ty, self.pointer_width);
                let addr = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {addr} = llvm.mlir.addressof @{name} : !llvm.ptr"
                );
                let _ = writeln!(
                    self.body,
                    "    llvm.store {val}, {addr} : {ty_str}, !llvm.ptr"
                );
            }
        }
    }

    fn emit_array_write(
        &mut self,
        array: LocalId,
        index: &Operand,
        value: &Operand,
        elem_ty: &MirTy,
        len: u32,
    ) {
        let Some(slot) = self.slot_names[array.0 as usize].clone() else {
            return;
        };
        let val = self.materialize_operand(value, elem_ty);
        let elem_str = mlir_type(elem_ty, self.pointer_width);
        if self.llvm_slot.contains(&array.0) {
            // GEP into the LLVM array slot for aggregate elements.
            let idx_i32 = self.materialize_index_as_i32(index);
            let ptr = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {ptr} = llvm.getelementptr {slot}[0, {idx_i32}] : (!llvm.ptr, i32) -> !llvm.ptr, !llvm.array<{len} x {elem_str}>"
            );
            let _ = writeln!(
                self.body,
                "    llvm.store {val}, {ptr} : {elem_str}, !llvm.ptr"
            );
            return;
        }
        let (idx_int, idx_int_ty) = match index {
            Operand::Copy(id) => {
                let ty = self.local_ty(*id);
                (self.materialize_operand(index, &ty), ty)
            }
            Operand::Const(c) => {
                let ty = const_ty(c).unwrap_or(MirTy::Prim(PrimTy::I32));
                (self.materialize_operand(index, &ty), ty)
            }
        };
        let from_str = mlir_type(&idx_int_ty, self.pointer_width);
        let idx_index = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {idx_index} = arith.index_cast {idx_int} : {from_str} to index"
        );
        let _ = writeln!(
            self.body,
            "    memref.store {val}, {slot}[{idx_index}] : memref<{len} x {elem_str}>"
        );
    }

    fn emit_array_init(&mut self, target: LocalId, elem_ty: &MirTy, elements: &[Operand]) {
        let Some(slot) = self.slot_names[target.0 as usize].clone() else {
            return;
        };
        let len = elements.len();
        let elem_str = mlir_type(elem_ty, self.pointer_width);
        let llvm_path = self.llvm_slot.contains(&target.0);
        for (i, e) in elements.iter().enumerate() {
            let v = self.materialize_operand(e, elem_ty);
            if llvm_path {
                let ptr = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {ptr} = llvm.getelementptr {slot}[0, {i}] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<{len} x {elem_str}>"
                );
                let _ = writeln!(
                    self.body,
                    "    llvm.store {v}, {ptr} : {elem_str}, !llvm.ptr"
                );
            } else {
                let idx = self.fresh_value();
                let _ = writeln!(self.body, "    {idx} = arith.constant {i} : index");
                let _ = writeln!(
                    self.body,
                    "    memref.store {v}, {slot}[{idx}] : memref<{len} x {elem_str}>"
                );
            }
        }
    }

    // Coerce an operand to an `i32` SSA name suitable as the index in
    // `llvm.getelementptr`. Constants are emitted directly as i32; copies
    // are loaded at their declared type and then sign-extended/truncated
    // to i32 if necessary.
    fn materialize_index_as_i32(&mut self, index: &Operand) -> String {
        match index {
            Operand::Const(c) => match c {
                ConstVal::Int { value, .. } => {
                    let v = self.fresh_value();
                    let _ = writeln!(
                        self.body,
                        "    {v} = llvm.mlir.constant({} : i32) : i32",
                        *value
                    );
                    v
                }
                ConstVal::UInt { value, .. } => {
                    let v = self.fresh_value();
                    let _ = writeln!(
                        self.body,
                        "    {v} = llvm.mlir.constant({} : i32) : i32",
                        *value
                    );
                    v
                }
                _ => self.materialize_operand(index, &MirTy::Prim(PrimTy::I32)),
            },
            Operand::Copy(id) => {
                let ty = self.local_ty(*id);
                let val = self.materialize_operand(index, &ty);
                let from_str = mlir_type(&ty, self.pointer_width);
                if from_str == "i32" {
                    val
                } else if let MirTy::Prim(p) = &ty {
                    let dst = self.fresh_value();
                    let from_w = p.bit_width(self.pointer_width);
                    if from_w > 32 {
                        let _ = writeln!(
                            self.body,
                            "    {dst} = arith.trunci {val} : {from_str} to i32"
                        );
                    } else {
                        let mn = if p.is_signed_int() {
                            "arith.extsi"
                        } else {
                            "arith.extui"
                        };
                        let _ = writeln!(
                            self.body,
                            "    {dst} = {mn} {val} : {from_str} to i32"
                        );
                    }
                    dst
                } else {
                    val
                }
            }
        }
    }

    // Materialise an rvalue into a single SSA name and return it.
    fn compute_rvalue(&mut self, dst_ty: &MirTy, r: &RValue) -> String {
        match r {
            RValue::Use(op) => self.materialize_operand(op, dst_ty),
            RValue::BinOp { op, op_ty, lhs, rhs } => {
                let dst = self.fresh_value();
                self.emit_bin_op(&dst, dst_ty, *op, op_ty, lhs, rhs);
                dst
            }
            RValue::UnaryOp { op, op_ty, operand } => {
                let dst = self.fresh_value();
                self.emit_unary_op(&dst, dst_ty, *op, op_ty, operand);
                dst
            }
            RValue::Call { callee, args, ret_ty } => {
                let dst = self.fresh_value();
                self.emit_call(&dst, *callee, args, ret_ty);
                dst
            }
            RValue::StructInit { ty, fields } => self.emit_struct_init(ty, fields),
            RValue::FieldRead { target, index, field_ty } => {
                self.emit_field_read(target, *index, field_ty, dst_ty)
            }
            RValue::Cast { source, from_ty, to_ty } => {
                self.emit_cast(source, from_ty, to_ty)
            }
            RValue::WithField { source, struct_ty, index, value } => {
                self.emit_with_field(source, struct_ty, *index, value)
            }
            RValue::ArrayInit { .. } => {
                // Array init doesn't return an SSA value; it stores
                // into the destination slot. Routed via emit_stmt.
                self.fresh_value()
            }
            RValue::ArrayIndex { array, index, elem_ty, len } => {
                self.emit_array_index(*array, index, elem_ty, *len)
            }
            RValue::FnAddr { callee, fn_ty } => self.emit_fn_addr(*callee, fn_ty),
            RValue::CallIndirect { callee, args, arg_tys, ret_ty } => {
                self.emit_call_indirect(callee, args, arg_tys, ret_ty)
            }
            RValue::StaticLoad { name, ty } => {
                let ty_str = mlir_type(ty, self.pointer_width);
                let addr = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {addr} = llvm.mlir.addressof @{name} : !llvm.ptr"
                );
                let dst = self.fresh_value();
                let _ = writeln!(
                    self.body,
                    "    {dst} = llvm.load {addr} : !llvm.ptr -> {ty_str}"
                );
                dst
            }
        }
    }

    fn emit_fn_addr(&mut self, callee: FunctionId, fn_ty: &MirTy) -> String {
        let name = self
            .fn_names
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| format!("fn{}", callee.0));
        let MirTy::Fn(args, ret) = fn_ty else {
            // Fall back: just emit unrealized cast.
            let dst = self.fresh_value();
            let _ = writeln!(self.body, "    {dst} = arith.constant 0 : i64");
            return dst;
        };
        // `func.constant` accepts a `func.func` symbol; bridge to
        // `!llvm.ptr` so it can flow through closure structs and
        // llvm-dialect call sites.
        let typed = self.fresh_value();
        let sig = mlir_fn_signature(args, ret, self.pointer_width);
        let _ = writeln!(
            self.body,
            "    {typed} = func.constant @{name} : {sig}"
        );
        let dst = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {dst} = builtin.unrealized_conversion_cast {typed} : {sig} to !llvm.ptr"
        );
        dst
    }

    fn emit_call_indirect(
        &mut self,
        callee: &Operand,
        args: &[Operand],
        arg_tys: &[MirTy],
        ret_ty: &MirTy,
    ) -> String {
        let fn_ty = MirTy::Fn(arg_tys.to_vec(), Box::new(ret_ty.clone()));
        let callee_v = self.materialize_operand(callee, &fn_ty);
        let arg_vals: Vec<String> = args
            .iter()
            .zip(arg_tys.iter())
            .map(|(op, t)| self.materialize_operand(op, t))
            .collect();
        let arg_ty_list = arg_tys
            .iter()
            .map(|t| mlir_type(t, self.pointer_width))
            .collect::<Vec<_>>()
            .join(", ");
        let arg_list = arg_vals.join(", ");
        let ret = if matches!(ret_ty, MirTy::Unit) {
            "()".to_owned()
        } else {
            mlir_type(ret_ty, self.pointer_width)
        };
        if matches!(ret_ty, MirTy::Unit) {
            let _ = writeln!(
                self.body,
                "    llvm.call {callee_v}({arg_list}) vararg(!llvm.func<void ({arg_ty_list})>) : !llvm.ptr, ({arg_ty_list}) -> ()"
            );
            let dst = self.fresh_value();
            let _ = writeln!(self.body, "    {dst} = arith.constant 0 : i1");
            dst
        } else {
            let dst = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {dst} = llvm.call {callee_v}({arg_list}) : !llvm.ptr, ({arg_ty_list}) -> {ret}"
            );
            dst
        }
    }

    fn emit_array_index(
        &mut self,
        array: LocalId,
        index: &Operand,
        elem_ty: &MirTy,
        len: u32,
    ) -> String {
        let slot = self
            .slot_names
            .get(array.0 as usize)
            .and_then(Option::as_ref)
            .cloned()
            .unwrap_or_default();
        let elem_str = mlir_type(elem_ty, self.pointer_width);
        if self.llvm_slot.contains(&array.0) {
            let idx_i32 = self.materialize_index_as_i32(index);
            let ptr = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {ptr} = llvm.getelementptr {slot}[0, {idx_i32}] : (!llvm.ptr, i32) -> !llvm.ptr, !llvm.array<{len} x {elem_str}>"
            );
            let dst = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {dst} = llvm.load {ptr} : !llvm.ptr -> {elem_str}"
            );
            return dst;
        }
        let (idx_int, idx_int_ty) = match index {
            Operand::Copy(id) => {
                let ty = self.local_ty(*id);
                (self.materialize_operand(index, &ty), ty)
            }
            Operand::Const(c) => {
                let ty = const_ty(c).unwrap_or(MirTy::Prim(PrimTy::I32));
                (self.materialize_operand(index, &ty), ty)
            }
        };
        let from_str = mlir_type(&idx_int_ty, self.pointer_width);
        let idx_index = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {idx_index} = arith.index_cast {idx_int} : {from_str} to index"
        );
        let dst = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {dst} = memref.load {slot}[{idx_index}] : memref<{len} x {elem_str}>"
        );
        dst
    }

    // `llvm.insertvalue` writes one element of an aggregate, returning
    // a new aggregate value (no in-place mutation).
    fn emit_with_field(
        &mut self,
        source: &Operand,
        struct_ty: &MirTy,
        index: u32,
        value: &Operand,
    ) -> String {
        let src_v = self.materialize_operand(source, struct_ty);
        let field_tys = struct_field_tys(struct_ty);
        let val_ty = field_tys
            .get(index as usize)
            .cloned()
            .unwrap_or(MirTy::Any);
        let v = self.materialize_operand(value, &val_ty);
        let ty_str = mlir_type(struct_ty, self.pointer_width);
        let dst = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {dst} = llvm.insertvalue {v}, {src_v}[{index}] : {ty_str}"
        );
        dst
    }

    // Integer width adjust. Wider via signed/unsigned extend, narrower
    // via truncate. Same-size acts as a no-op alias.
    fn emit_cast(&mut self, source: &Operand, from_ty: &MirTy, to_ty: &MirTy) -> String {
        let v = self.materialize_operand(source, from_ty);
        let from = mlir_type(from_ty, self.pointer_width);
        let to = mlir_type(to_ty, self.pointer_width);
        if from == to {
            return v;
        }
        let (MirTy::Prim(fp), MirTy::Prim(tp)) = (from_ty, to_ty) else {
            // Non-int casts aren't part of this slice; emit a placeholder.
            let dst = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {dst} = builtin.unrealized_conversion_cast {v} : {from} to {to}"
            );
            return dst;
        };
        let dst = self.fresh_value();
        // Bool participates in cast logic as a 1-bit unsigned int. The
        // is_int helpers don't include it (operator dispatch wants Bool
        // separate), so widen the int classification locally.
        let from_int_like = fp.is_int() || matches!(fp, PrimTy::Bool);
        let to_int_like = tp.is_int() || matches!(tp, PrimTy::Bool);
        // Pick the right arith op for each four-way (int/float) combination.
        match (from_int_like, to_int_like, fp.is_float(), tp.is_float()) {
            (true, true, _, _) => {
                // `bit_width` for bool reports 8 because it represents
                // storage size, but the codegen type is i1. Use 1
                // explicitly here so the ext/trunc decision is right.
                let bool_aware = |p: PrimTy| -> u32 {
                    if matches!(p, PrimTy::Bool) { 1 } else { p.bit_width(self.pointer_width) }
                };
                let from_w = bool_aware(*fp);
                let to_w = bool_aware(*tp);
                if to_w > from_w {
                    // i1 / u-types zero-extend; signed-int sign-extend.
                    let mn = if matches!(fp, PrimTy::Bool) || !fp.is_signed_int() {
                        "arith.extui"
                    } else {
                        "arith.extsi"
                    };
                    let _ = writeln!(self.body, "    {dst} = {mn} {v} : {from} to {to}");
                } else if to_w < from_w {
                    if matches!(tp, PrimTy::Bool) {
                        // Truncating to i1 — use a comparison with 0
                        // since `arith.trunci ... to i1` is supported
                        // but `cmpi ne` is more explicit about intent.
                        let zero = self.fresh_value();
                        let _ = writeln!(
                            self.body,
                            "    {zero} = arith.constant 0 : {from}"
                        );
                        let _ = writeln!(
                            self.body,
                            "    {dst} = arith.cmpi ne, {v}, {zero} : {from}"
                        );
                    } else {
                        let _ =
                            writeln!(self.body, "    {dst} = arith.trunci {v} : {from} to {to}");
                    }
                } else {
                    let _ = writeln!(
                        self.body,
                        "    {dst} = builtin.unrealized_conversion_cast {v} : {from} to {to}"
                    );
                }
            }
            (false, true, true, false) => {
                // float → int.
                let mn = if tp.is_signed_int() {
                    "arith.fptosi"
                } else {
                    "arith.fptoui"
                };
                let _ = writeln!(self.body, "    {dst} = {mn} {v} : {from} to {to}");
            }
            (true, false, false, true) => {
                // int → float.
                let mn = if fp.is_signed_int() {
                    "arith.sitofp"
                } else {
                    "arith.uitofp"
                };
                let _ = writeln!(self.body, "    {dst} = {mn} {v} : {from} to {to}");
            }
            (false, false, true, true) => {
                // float → float.
                let from_w = fp.bit_width(self.pointer_width);
                let to_w = tp.bit_width(self.pointer_width);
                if to_w > from_w {
                    let _ = writeln!(self.body, "    {dst} = arith.extf {v} : {from} to {to}");
                } else if to_w < from_w {
                    let _ = writeln!(self.body, "    {dst} = arith.truncf {v} : {from} to {to}");
                } else {
                    let _ = writeln!(
                        self.body,
                        "    {dst} = builtin.unrealized_conversion_cast {v} : {from} to {to}"
                    );
                }
            }
            _ => {
                let _ = writeln!(
                    self.body,
                    "    {dst} = builtin.unrealized_conversion_cast {v} : {from} to {to}"
                );
            }
        }
        dst
    }

    // Build a struct value by chaining `llvm.insertvalue` from `undef`.
    fn emit_struct_init(&mut self, ty: &MirTy, fields: &[Operand]) -> String {
        let ty_str = mlir_type(ty, self.pointer_width);
        let acc0 = self.fresh_value();
        let _ = writeln!(self.body, "    {acc0} = llvm.mlir.undef : {ty_str}");
        let field_tys = struct_field_tys(ty);
        let mut acc = acc0;
        for (i, f) in fields.iter().enumerate() {
            let f_ty = field_tys
                .get(i)
                .cloned()
                .unwrap_or_else(|| match f {
                    Operand::Copy(id) => self.local_ty(*id),
                    Operand::Const(c) => const_ty(c).unwrap_or(MirTy::Any),
                });
            let v = self.materialize_operand(f, &f_ty);
            let next = self.fresh_value();
            let _ = writeln!(
                self.body,
                "    {next} = llvm.insertvalue {v}, {acc}[{i}] : {ty_str}"
            );
            acc = next;
        }
        acc
    }

    fn emit_field_read(
        &mut self,
        target: &Operand,
        index: u32,
        field_ty: &MirTy,
        _dst_ty: &MirTy,
    ) -> String {
        let target_ty = match target {
            Operand::Copy(id) => self.local_ty(*id),
            Operand::Const(c) => const_ty(c).unwrap_or(MirTy::Any),
        };
        let target_v = self.materialize_operand(target, &target_ty);
        let target_ty_str = mlir_type(&target_ty, self.pointer_width);
        let dst = self.fresh_value();
        let _ = writeln!(
            self.body,
            "    {dst} = llvm.extractvalue {target_v}[{index}] : {target_ty_str}"
        );
        let _ = field_ty;
        dst
    }

    fn emit_call(&mut self, dst: &str, callee: FunctionId, args: &[Operand], ret_ty: &MirTy) {
        // Materialize each argument with its declared type so the
        // `func.call` operand list is well-typed.
        let arg_tys: Vec<MirTy> = args
            .iter()
            .map(|op| match op {
                Operand::Copy(id) => self.local_ty(*id),
                Operand::Const(c) => const_ty(c).unwrap_or(MirTy::Any),
            })
            .collect();
        let arg_vals: Vec<String> = args
            .iter()
            .zip(arg_tys.iter())
            .map(|(op, ty)| self.materialize_operand(op, ty))
            .collect();

        let name = self
            .fn_names
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| format!("fn{}", callee.0));
        let arg_list = arg_vals.join(", ");
        let arg_ty_list = arg_tys
            .iter()
            .map(|t| mlir_type(t, self.pointer_width))
            .collect::<Vec<_>>()
            .join(", ");
        let ret = mlir_type(ret_ty, self.pointer_width);

        if matches!(ret_ty, MirTy::Unit) {
            // Unit-returning calls produce no SSA value; emit the call
            // and bind `dst` to a dummy zero so downstream code keeps
            // the slot wired up.
            let _ = writeln!(
                self.body,
                "    func.call @{name}({arg_list}) : ({arg_ty_list}) -> ()"
            );
            let _ = writeln!(self.body, "    {dst} = arith.constant 0 : i1");
        } else {
            let _ = writeln!(
                self.body,
                "    {dst} = func.call @{name}({arg_list}) : ({arg_ty_list}) -> {ret}"
            );
        }
    }

    fn emit_bin_op(
        &mut self,
        dst: &str,
        _dst_ty: &MirTy,
        op: PrimOp,
        op_ty: &MirTy,
        lhs: &Operand,
        rhs: &Operand,
    ) {
        let lhs_v = self.materialize_operand(lhs, op_ty);
        let rhs_v = self.materialize_operand(rhs, op_ty);
        let ty = mlir_type(op_ty, self.pointer_width);
        let MirTy::Prim(prim) = op_ty else {
            let _ = writeln!(
                self.body,
                "    {dst} = builtin.unrealized_conversion_cast : () to {ty}"
            );
            return;
        };
        if let Some(line) = arith_binop(op, *prim, dst, &lhs_v, &rhs_v, &ty) {
            self.body.push_str(&line);
            return;
        }
        let _ = writeln!(
            self.body,
            "    {dst} = builtin.unrealized_conversion_cast : () to {ty}"
        );
    }

    fn emit_unary_op(
        &mut self,
        dst: &str,
        dst_ty: &MirTy,
        op: PrimOp,
        op_ty: &MirTy,
        operand: &Operand,
    ) {
        let v = self.materialize_operand(operand, op_ty);
        let ty = mlir_type(op_ty, self.pointer_width);
        let MirTy::Prim(prim) = op_ty else {
            let _ = writeln!(
                self.body,
                "    {dst} = builtin.unrealized_conversion_cast : () to {}",
                mlir_type(dst_ty, self.pointer_width)
            );
            return;
        };
        match (op, prim) {
            (PrimOp::Neg, p) if p.is_signed_int() => {
                // arith has no `negi`; lower to `0 - x`.
                let zero = self.fresh_value();
                let _ = writeln!(self.body, "    {zero} = arith.constant 0 : {ty}");
                let _ = writeln!(self.body, "    {dst} = arith.subi {zero}, {v} : {ty}");
            }
            (PrimOp::Neg, p) if p.is_float() => {
                let _ = writeln!(self.body, "    {dst} = arith.negf {v} : {ty}");
            }
            (PrimOp::Not, p) if p.is_int() => {
                // Bitwise NOT = xor with all-ones.
                let ones = self.fresh_value();
                let _ = writeln!(self.body, "    {ones} = arith.constant -1 : {ty}");
                let _ = writeln!(self.body, "    {dst} = arith.xori {v}, {ones} : {ty}");
            }
            (PrimOp::LogicalNot, PrimTy::Bool) => {
                let one = self.fresh_value();
                let _ = writeln!(self.body, "    {one} = arith.constant 1 : i1");
                let _ = writeln!(self.body, "    {dst} = arith.xori {v}, {one} : i1");
            }
            _ => {
                let _ = writeln!(
                    self.body,
                    "    {dst} = builtin.unrealized_conversion_cast : () to {ty}"
                );
            }
        }
    }

    fn emit_const_assign(&mut self, dst: &str, dst_ty: &MirTy, c: &ConstVal) {
        let ty = mlir_type(dst_ty, self.pointer_width);
        match c {
            ConstVal::Int { value, ty: prim } => {
                let _ = writeln!(
                    self.body,
                    "    {dst} = arith.constant {value} : {}",
                    mlir_prim(*prim, self.pointer_width)
                );
            }
            ConstVal::UInt { value, ty: prim } => {
                let _ = writeln!(
                    self.body,
                    "    {dst} = arith.constant {value} : {}",
                    mlir_prim(*prim, self.pointer_width)
                );
            }
            ConstVal::Bool(b) => {
                let _ = writeln!(
                    self.body,
                    "    {dst} = arith.constant {} : i1",
                    u32::from(*b)
                );
            }
            ConstVal::Float { bits, ty: prim } => {
                let lit = format_float(*bits, *prim);
                let _ = writeln!(
                    self.body,
                    "    {dst} = arith.constant {lit} : {}",
                    mlir_prim(*prim, self.pointer_width)
                );
            }
            ConstVal::Unit | ConstVal::None => {
                // For aggregate destinations, materialize an `undef`
                // value; for primitives, a zero constant. Unit really
                // shouldn't reach codegen but a placeholder keeps the
                // pipeline well-typed.
                if matches!(
                    dst_ty,
                    MirTy::Struct(_, _) | MirTy::Tuple(_) | MirTy::Sum(_) | MirTy::Array(_, _)
                ) {
                    let _ = writeln!(self.body, "    {dst} = llvm.mlir.undef : {ty}");
                } else if matches!(dst_ty, MirTy::Fn(_, _)) {
                    let _ = writeln!(self.body, "    {dst} = llvm.mlir.zero : !llvm.ptr");
                } else {
                    let _ = writeln!(self.body, "    {dst} = arith.constant 0 : {ty}");
                }
            }
            ConstVal::Char(c) => {
                let _ = writeln!(self.body, "    {dst} = arith.constant {c} : {ty}");
            }
            ConstVal::Str(s) => {
                // Look up (or intern) the string and take its address.
                let sym = self.intern_string(s);
                let _ = writeln!(self.body, "    {dst} = llvm.mlir.addressof @{sym} : !llvm.ptr");
            }
        }
    }

    fn emit_terminator(&mut self, t: &Terminator) {
        match t {
            Terminator::Return(None) => {
                self.body.push_str("    func.return\n");
            }
            Terminator::Return(Some(op)) => {
                let val = self.materialize_operand(op, &self.f.ret_ty.clone());
                let ty = mlir_type(&self.f.ret_ty, self.pointer_width);
                let _ = writeln!(self.body, "    func.return {val} : {ty}");
            }
            Terminator::Goto { target, args } => {
                self.emit_branch("    cf.br", target.0, args, None);
            }
            Terminator::If { cond, then_bb, then_args, else_bb, else_args } => {
                let v = self.materialize_operand(cond, &MirTy::Prim(PrimTy::Bool));
                let then_part = self.format_block_target(then_bb.0, then_args);
                let else_part = self.format_block_target(else_bb.0, else_args);
                let _ = writeln!(
                    self.body,
                    "    cf.cond_br {v}, {then_part}, {else_part}"
                );
            }
            Terminator::Unreachable => {
                self.body.push_str("    llvm.unreachable\n");
            }
        }
    }

    fn emit_branch(&mut self, op: &str, target: u32, args: &[Operand], _label: Option<&str>) {
        if args.is_empty() {
            let _ = writeln!(self.body, "{op} ^bb{target}");
            return;
        }
        let parts: Vec<(String, String)> = args
            .iter()
            .map(|a| {
                let ty = match a {
                    Operand::Copy(id) => self.local_ty(*id),
                    Operand::Const(c) => const_ty(c).unwrap_or(MirTy::Any),
                };
                let v = self.materialize_operand(a, &ty);
                (v, mlir_type(&ty, self.pointer_width))
            })
            .collect();
        let vals: Vec<String> = parts.iter().map(|(v, _)| v.clone()).collect();
        let tys: Vec<String> = parts.iter().map(|(_, t)| t.clone()).collect();
        let _ = writeln!(
            self.body,
            "{op} ^bb{target}({} : {})",
            vals.join(", "),
            tys.join(", ")
        );
    }

    fn format_block_target(&mut self, target: u32, args: &[Operand]) -> String {
        if args.is_empty() {
            return format!("^bb{target}");
        }
        let parts: Vec<(String, String)> = args
            .iter()
            .map(|a| {
                let ty = match a {
                    Operand::Copy(id) => self.local_ty(*id),
                    Operand::Const(c) => const_ty(c).unwrap_or(MirTy::Any),
                };
                let v = self.materialize_operand(a, &ty);
                (v, mlir_type(&ty, self.pointer_width))
            })
            .collect();
        let vals: Vec<String> = parts.iter().map(|(v, _)| v.clone()).collect();
        let tys: Vec<String> = parts.iter().map(|(_, t)| t.clone()).collect();
        format!("^bb{target}({} : {})", vals.join(", "), tys.join(", "))
    }

    fn materialize_operand(&mut self, op: &Operand, ty: &MirTy) -> String {
        match op {
            Operand::Copy(id) => self.read_local(*id),
            Operand::Const(c) => {
                let v = self.fresh_value();
                self.emit_const_assign(&v, ty, c);
                v
            }
        }
    }

    fn local_ty(&self, id: rokc_ir_common::LocalId) -> MirTy {
        self.f
            .locals
            .get(id.0 as usize)
            .map_or(MirTy::Any, |l| l.ty.clone())
    }
}

fn mlir_type(ty: &MirTy, pointer_width: u32) -> String {
    match ty {
        MirTy::Unit => "()".to_owned(),
        MirTy::Prim(p) => mlir_prim(*p, pointer_width),
        MirTy::Any => format!("i{pointer_width}"),
        MirTy::Sum(parts) => {
            let _ = parts;
            "!llvm.struct<(i32, i64)>".to_owned()
        }
        MirTy::Tuple(parts) | MirTy::Struct(_, parts) => {
            let inner: Vec<String> =
                parts.iter().map(|t| mlir_type(t, pointer_width)).collect();
            format!("!llvm.struct<({})>", inner.join(", "))
        }
        MirTy::Array(elem, n) => {
            format!("!llvm.array<{n} x {}>", mlir_type(elem, pointer_width))
        }
        // Function values flow as opaque pointers so they can live
        // alongside other fields inside `!llvm.struct`. The full
        // `(args) -> ret` shape is supplied at each call site.
        MirTy::Fn(_, _) => "!llvm.ptr".to_owned(),
    }
}

// `(args) -> ret` rendering for func.constant / call sites.
fn mlir_fn_signature(args: &[MirTy], ret: &MirTy, pointer_width: u32) -> String {
    let arg_list = args
        .iter()
        .map(|t| mlir_type(t, pointer_width))
        .collect::<Vec<_>>()
        .join(", ");
    let ret_str = if matches!(ret, MirTy::Unit) {
        "()".to_owned()
    } else {
        mlir_type(ret, pointer_width)
    };
    format!("({arg_list}) -> {ret_str}")
}

fn mlir_prim(p: PrimTy, pointer_width: u32) -> String {
    match p {
        PrimTy::I8 | PrimTy::U8 | PrimTy::CChar => "i8".to_owned(),
        PrimTy::I16 | PrimTy::U16 => "i16".to_owned(),
        PrimTy::I32 | PrimTy::U32 => "i32".to_owned(),
        PrimTy::I64 | PrimTy::U64 => "i64".to_owned(),
        PrimTy::Isize | PrimTy::Usize => format!("i{pointer_width}"),
        PrimTy::F32 => "f32".to_owned(),
        PrimTy::F64 => "f64".to_owned(),
        PrimTy::Bool => "i1".to_owned(),
        // FFI-friendly form: opaque pointer to a NUL-terminated byte
        // sequence. The spec's `(ptr, len)` view is kept as a future
        // refinement under a separate stdlib type.
        PrimTy::Str => "!llvm.ptr".to_owned(),
    }
}

/// Build a single MLIR line for a primitive binary op. Returns `None` if
/// the (op, prim) combo is not handled.
fn arith_binop(
    op: PrimOp,
    prim: PrimTy,
    dst: &str,
    lhs: &str,
    rhs: &str,
    ty: &str,
) -> Option<String> {
    let int = prim.is_int();
    let signed = prim.is_signed_int();
    let float = prim.is_float();
    let bool_ = matches!(prim, PrimTy::Bool);

    let mnemonic: Option<String> = match op {
        PrimOp::Add if int => Some("arith.addi".into()),
        PrimOp::Add if float => Some("arith.addf".into()),
        PrimOp::Sub if int => Some("arith.subi".into()),
        PrimOp::Sub if float => Some("arith.subf".into()),
        PrimOp::Mul if int => Some("arith.muli".into()),
        PrimOp::Mul if float => Some("arith.mulf".into()),
        PrimOp::Div if signed => Some("arith.divsi".into()),
        PrimOp::Div if int => Some("arith.divui".into()),
        PrimOp::Div if float => Some("arith.divf".into()),
        PrimOp::Rem if signed => Some("arith.remsi".into()),
        PrimOp::Rem if int => Some("arith.remui".into()),
        PrimOp::Rem if float => Some("arith.remf".into()),
        PrimOp::BitAnd if int || bool_ => Some("arith.andi".into()),
        PrimOp::BitOr if int || bool_ => Some("arith.ori".into()),
        PrimOp::BitXor if int || bool_ => Some("arith.xori".into()),
        PrimOp::LogicalAnd if bool_ => Some("arith.andi".into()),
        PrimOp::LogicalOr if bool_ => Some("arith.ori".into()),
        PrimOp::Shl if int => Some("arith.shli".into()),
        PrimOp::Shr if signed => Some("arith.shrsi".into()),
        PrimOp::Shr if int => Some("arith.shrui".into()),
        _ => None,
    };
    if let Some(m) = mnemonic {
        return Some(format!("    {dst} = {m} {lhs}, {rhs} : {ty}\n"));
    }

    // Comparisons return i1; the predicate selector encodes signed-ness.
    let pred = match (op, prim) {
        (PrimOp::Eq, p) if p.is_int() || matches!(p, PrimTy::Bool) => Some(("arith.cmpi", "eq")),
        (PrimOp::Ne, p) if p.is_int() || matches!(p, PrimTy::Bool) => Some(("arith.cmpi", "ne")),
        (PrimOp::Lt, p) if p.is_signed_int() => Some(("arith.cmpi", "slt")),
        (PrimOp::Le, p) if p.is_signed_int() => Some(("arith.cmpi", "sle")),
        (PrimOp::Gt, p) if p.is_signed_int() => Some(("arith.cmpi", "sgt")),
        (PrimOp::Ge, p) if p.is_signed_int() => Some(("arith.cmpi", "sge")),
        (PrimOp::Lt, p) if p.is_int() => Some(("arith.cmpi", "ult")),
        (PrimOp::Le, p) if p.is_int() => Some(("arith.cmpi", "ule")),
        (PrimOp::Gt, p) if p.is_int() => Some(("arith.cmpi", "ugt")),
        (PrimOp::Ge, p) if p.is_int() => Some(("arith.cmpi", "uge")),
        (PrimOp::Eq, p) if p.is_float() => Some(("arith.cmpf", "oeq")),
        (PrimOp::Ne, p) if p.is_float() => Some(("arith.cmpf", "one")),
        (PrimOp::Lt, p) if p.is_float() => Some(("arith.cmpf", "olt")),
        (PrimOp::Le, p) if p.is_float() => Some(("arith.cmpf", "ole")),
        (PrimOp::Gt, p) if p.is_float() => Some(("arith.cmpf", "ogt")),
        (PrimOp::Ge, p) if p.is_float() => Some(("arith.cmpf", "oge")),
        _ => None,
    };
    if let Some((mn, pred)) = pred {
        return Some(format!("    {dst} = {mn} {pred}, {lhs}, {rhs} : {ty}\n"));
    }
    None
}

// Struct / tuple / pointer values live in SSA — `memref` can't hold an
// arbitrary `!llvm.struct` or `!llvm.ptr`, so they aren't stack-slotted.
// Arrays go through memref directly (`memref<N x T>`) for dynamic
// indexing — handled separately from primitive slots.
/// Types stored via `memref.alloca`. Limited to plain primitives that
/// the memref dialect understands. Aggregates and pointer-shaped values
/// (including nested arrays) take the `llvm.alloca` path instead.
fn is_memref_storable(ty: &MirTy) -> bool {
    matches!(ty, MirTy::Prim(p) if !matches!(p, PrimTy::Str))
}

/// Types stored via `llvm.alloca` — aggregates and pointer-shaped
/// values that flow through the LLVM dialect.
fn is_llvm_storable(ty: &MirTy) -> bool {
    matches!(
        ty,
        MirTy::Struct(_, _)
            | MirTy::Tuple(_)
            | MirTy::Sum(_)
            | MirTy::Prim(PrimTy::Str)
            | MirTy::Fn(_, _)
    )
}

fn struct_field_tys(ty: &MirTy) -> Vec<MirTy> {
    match ty {
        MirTy::Struct(_, fs) | MirTy::Tuple(fs) => fs.clone(),
        _ => Vec::new(),
    }
}

/// Best-effort type for a `ConstVal`. Used at call sites where we have a
/// raw const operand and need to pick an MLIR type for it.
fn const_ty(c: &ConstVal) -> Option<MirTy> {
    match c {
        ConstVal::Int { ty, .. } | ConstVal::UInt { ty, .. } | ConstVal::Float { ty, .. } => {
            Some(MirTy::Prim(*ty))
        }
        ConstVal::Bool(_) => Some(MirTy::Prim(PrimTy::Bool)),
        ConstVal::Str(_) => Some(MirTy::Prim(PrimTy::Str)),
        ConstVal::Char(_) => Some(MirTy::Prim(PrimTy::CChar)),
        ConstVal::Unit | ConstVal::None => Some(MirTy::Unit),
    }
}

fn format_float(bits: u64, prim: PrimTy) -> String {
    match prim {
        PrimTy::F32 => {
            let v = f32::from_bits(bits as u32);
            if v.is_nan() {
                "0x7FC00000".to_owned()
            } else {
                format_float_decimal(f64::from(v))
            }
        }
        _ => {
            let v = f64::from_bits(bits);
            if v.is_nan() {
                "0x7FF8000000000000".to_owned()
            } else {
                format_float_decimal(v)
            }
        }
    }
}

// MLIR's float literal grammar requires a decimal point — `3e0` is
// rejected. `{:?}` on `f64` always emits at least `3.0`, which works.
fn format_float_decimal(v: f64) -> String {
    if v.is_infinite() {
        if v.is_sign_negative() {
            "0xFFF0000000000000".to_owned()
        } else {
            "0x7FF0000000000000".to_owned()
        }
    } else {
        format!("{v:?}")
    }
}

/// Render a `ConstVal` as the attribute body of an `llvm.mlir.global`.
/// Only literal-shaped values are valid here — anything else degrades
/// to a zero-init.
fn format_const_attr(v: &ConstVal, ty: &MirTy) -> String {
    let ty_str = mlir_type(ty, 64);
    match v {
        ConstVal::Int { value, .. } => format!("{value} : {ty_str}"),
        ConstVal::Bool(b) => format!("{} : i1", if *b { 1 } else { 0 }),
        ConstVal::Unit | ConstVal::None => "0 : i32".to_owned(),
        ConstVal::Char(c) => format!("{c} : i32"),
        ConstVal::Str(_) | ConstVal::UInt { .. } | ConstVal::Float { .. } => {
            // String / float / unsigned static initialisers aren't part
            // of this slice — emit a zero-init placeholder.
            format!("0 : {ty_str}")
        }
    }
}


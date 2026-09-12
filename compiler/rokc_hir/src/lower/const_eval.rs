//! Compile-time evaluation (spec 5.2, 6.5.8): an interpreter over
//! lowered HIR.
//!
//! Const items, array lengths, const generic arguments, static
//! initializers and `const fn` literal handlers all run through `Interp`.
//! Callee bodies come from a `Bodies` provider: with a lowering context
//! they are lowered on demand (`CtxBodies`); the pre-pass front-end
//! (`syntactic_int`, item signatures before any body exists) has none.
//!
//! Integers are `i128` tagged with their primitive; every result is
//! range-checked, so overflow, division by zero, bad shifts and failed
//! float-to-int casts are errors, never wrapped (the `wrapping_*`
//! intrinsics wrap). Loops and calls are bounded by `STEP_LIMIT` and
//! `DEPTH_LIMIT`.
//!
//! A user function must be a `const fn` to be entered; standard library
//! (`rok::*`) bodies are entered as long as they stay evaluable, since
//! the library does not mark its pure functions `const` yet.

// `a` / `b` operands, `p` their primitive, `f` the frame, `v` a value.
#![allow(clippy::many_single_char_names)]

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rokc_diagnostic::Span;

#[allow(clippy::wildcard_imports)]
use super::*;

const STEP_LIMIT: u64 = 4_000_000;
const DEPTH_LIMIT: u32 = 128;
const POINTER_WIDTH: u32 = 64;

#[derive(Clone, Debug)]
pub(super) enum Value {
    Unit,
    Bool(bool),
    Int(i128, PrimTy),
    /// `f32` values are kept rounded to `f32`.
    Float(f64, PrimTy),
    /// `char` / `c_char` code point.
    Char(u32),
    Str(Rc<str>),
    None,
    Tuple(Vec<Value>),
    Array(Vec<Value>),
    Struct(StructId, Vec<Value>),
    Enum(EnumId, u32, Vec<Value>),
    Sum(u32, Option<Box<Value>>),
    /// A `GcBuf`: shared, mutable; never embedded.
    Buf(Rc<RefCell<Vec<Value>>>),
    Fn(FunctionId),
    Closure(FunctionId, Box<Value>),
    /// A union's storage: the value last written; reads reinterpret it.
    Union(Box<Value>),
}

/// Why evaluation stopped: an error, or a control transfer in flight.
pub(super) enum Stop {
    /// Needs a run-time value or operation.
    Runtime(Span, String),
    /// The evaluation itself failed (panic, overflow, limits).
    Fail(Span, String),
    /// Ran into code that already has errors; nothing more to report.
    Poisoned,
    Break(Option<String>, Value),
    Continue(Option<String>),
    Return(Value),
}

type R<T> = Result<T, Stop>;

pub(super) enum Callee {
    /// The body, and whether it is standard library code.
    Body(Rc<HirFunction>, bool),
    Extern(String),
    /// Not callable at compile time: the reason.
    Refused(String),
    Poisoned,
}

pub(super) trait Bodies {
    fn callee(&mut self, id: FunctionId) -> Callee;
}

/// No bodies at all (pre-pass).
struct NoBodies;

impl Bodies for NoBodies {
    fn callee(&mut self, _: FunctionId) -> Callee {
        Callee::Refused("calls a function".to_owned())
    }
}

type Frame = HashMap<LocalId, Value>;

pub(super) struct Interp<'b> {
    bodies: &'b mut dyn Bodies,
    steps: u64,
    depth: u32,
}

const fn int_range(p: PrimTy) -> (i128, i128) {
    let bits = p.bit_width(POINTER_WIDTH);
    if p.is_signed_int() {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    } else {
        (0, (1i128 << bits) - 1)
    }
}

/// Two's-complement wrap of `v` into `p`.
const fn wrap(v: i128, p: PrimTy) -> i128 {
    let bits = p.bit_width(POINTER_WIDTH);
    let mask = (1u128 << bits) - 1;
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]
    let low = (v as u128) & mask;
    #[allow(clippy::cast_possible_wrap)]
    if p.is_signed_int() && low >> (bits - 1) == 1 {
        (low as i128) - (1i128 << bits)
    } else {
        low as i128
    }
}

#[allow(clippy::cast_possible_truncation)]
fn round(v: f64, p: PrimTy) -> f64 {
    if p == PrimTy::F32 {
        f64::from(v as f32)
    } else {
        v
    }
}

const fn prim_of(ty: &HirTy) -> Option<PrimTy> {
    match ty {
        HirTy::Prim(p) => Some(*p),
        _ => None,
    }
}

fn from_const(c: &ConstVal, ty: &HirTy) -> Value {
    match c {
        ConstVal::Unit => Value::Unit,
        ConstVal::Bool(b) => Value::Bool(*b),
        ConstVal::Int { value, ty: p } => Value::Int(*value, prim_of(ty).unwrap_or(*p)),
        #[allow(clippy::cast_possible_wrap)]
        ConstVal::UInt { value, ty: p } => Value::Int(*value as i128, prim_of(ty).unwrap_or(*p)),
        ConstVal::Float { bits, ty: p } => {
            #[allow(clippy::cast_possible_truncation)]
            let v = if *p == PrimTy::F32 {
                f64::from(f32::from_bits(*bits as u32))
            } else {
                f64::from_bits(*bits)
            };
            let p = prim_of(ty).filter(|t| t.is_float()).unwrap_or(*p);
            Value::Float(round(v, p), p)
        }
        ConstVal::Char(c) => Value::Char(*c),
        ConstVal::Str(s) => Value::Str(s.as_str().into()),
        ConstVal::None => Value::None,
    }
}

/// `v` as a constant expression of type `ty`; `None` when it holds
/// something only a run-time value can be (a buffer, a function).
pub(super) fn embed(ctx: &LowerCtx<'_>, v: &Value, ty: &HirTy, span: Span) -> Option<HirExpr> {
    let konst = |c: ConstVal| HirExpr {
        kind: HirExprKind::Const(c),
        ty: ty.clone(),
        span,
    };
    let kind = match v {
        Value::Unit => return Some(konst(ConstVal::Unit)),
        Value::Bool(b) => return Some(konst(ConstVal::Bool(*b))),
        Value::Int(i, p) => {
            return Some(konst(ConstVal::Int {
                value: *i,
                ty: prim_of(ty).unwrap_or(*p),
            }));
        }
        Value::Float(f, p) => {
            let p = prim_of(ty).unwrap_or(*p);
            #[allow(clippy::cast_possible_truncation)]
            let bits = if p == PrimTy::F32 {
                u64::from((*f as f32).to_bits())
            } else {
                f.to_bits()
            };
            return Some(konst(ConstVal::Float { bits, ty: p }));
        }
        Value::Char(c) => return Some(konst(ConstVal::Char(*c))),
        Value::Str(s) => return Some(konst(ConstVal::Str(s.to_string()))),
        Value::None => return Some(konst(ConstVal::None)),
        Value::Tuple(vs) => {
            let tys: Vec<HirTy> = match ty {
                HirTy::Tuple(ts) => ts.clone(),
                // A `throws` carrier: `(is_err, ok, err)`, no unit `ok`.
                HirTy::Throws { ok, err } if **ok == HirTy::Unit => {
                    vec![HirTy::Prim(PrimTy::Bool), (**err).clone()]
                }
                HirTy::Throws { ok, err } => {
                    vec![HirTy::Prim(PrimTy::Bool), (**ok).clone(), (**err).clone()]
                }
                _ => return None,
            };
            if tys.len() != vs.len() {
                return None;
            }
            let fields = vs
                .iter()
                .zip(&tys)
                .map(|(v, t)| embed(ctx, v, t, span))
                .collect::<Option<Vec<_>>>()?;
            HirExprKind::Tuple { fields }
        }
        Value::Array(vs) => {
            let HirTy::Array(elem, _) = ty else {
                return None;
            };
            let elements = vs
                .iter()
                .map(|v| embed(ctx, v, elem, span))
                .collect::<Option<Vec<_>>>()?;
            HirExprKind::ArrayInit {
                elem_ty: (**elem).clone(),
                elements,
            }
        }
        Value::Struct(id, vs) => {
            let def = ctx.struct_def(*id);
            if def.union_kind.is_some() || def.fields.len() != vs.len() {
                return None;
            }
            let fields = vs
                .iter()
                .zip(&def.fields)
                .map(|(v, f)| embed(ctx, v, &f.ty, span))
                .collect::<Option<Vec<_>>>()?;
            HirExprKind::StructInit {
                struct_id: *id,
                fields,
            }
        }
        Value::Enum(id, idx, vs) => {
            let def = ctx.enum_def(*id);
            let var = def.variants.get(*idx as usize)?;
            let tys: Vec<HirTy> = match (&var.payload_ty, var.arity) {
                (_, 0) => Vec::new(),
                (Some(t), 1) => vec![t.clone()],
                (Some(HirTy::Tuple(ts)), _) => ts.clone(),
                _ => return None,
            };
            if tys.len() != vs.len() {
                return None;
            }
            let args = vs
                .iter()
                .zip(&tys)
                .map(|(v, t)| embed(ctx, v, t, span))
                .collect::<Option<Vec<_>>>()?;
            HirExprKind::EnumVariantInit {
                enum_id: *id,
                variant_index: *idx,
                args,
            }
        }
        Value::Sum(idx, payload) => {
            let HirTy::Sum(members) = ty else {
                return None;
            };
            let member = members.get(*idx as usize)?;
            let value = match payload {
                Some(p) => Some(Box::new(embed(ctx, p, member, span)?)),
                None => None,
            };
            HirExprKind::SumWrap {
                sum_ty: ty.clone(),
                variant_index: *idx,
                value,
            }
        }
        Value::Buf(_) | Value::Fn(_) | Value::Closure(..) | Value::Union(_) => return None,
    };
    Some(HirExpr {
        kind,
        ty: ty.clone(),
        span,
    })
}

fn describe(v: &Value) -> String {
    match v {
        Value::Str(s) => format!("{s:?}"),
        Value::Int(i, _) => i.to_string(),
        Value::Float(f, _) => f.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Char(c) => char::from_u32(*c).map_or_else(|| c.to_string(), |c| format!("{c:?}")),
        Value::Struct(_, fs) | Value::Enum(_, _, fs) | Value::Tuple(fs)
            if fs.len() == 1 && matches!(fs[0], Value::Str(_)) =>
        {
            describe(&fs[0])
        }
        Value::Sum(_, Some(p)) => describe(p),
        _ => "a value".to_owned(),
    }
}

impl<'b> Interp<'b> {
    pub(super) fn new(bodies: &'b mut dyn Bodies) -> Self {
        Self {
            bodies,
            steps: 0,
            depth: 0,
        }
    }

    pub(super) fn eval(&mut self, e: &HirExpr) -> R<Value> {
        self.expr(e, &mut Frame::new())
    }

    fn step(&mut self, span: Span) -> R<()> {
        self.steps += 1;
        if self.steps > STEP_LIMIT {
            return Err(Stop::Fail(
                span,
                format!("evaluation exceeds the step limit ({STEP_LIMIT})"),
            ));
        }
        Ok(())
    }

    fn block(&mut self, b: &HirBlock, f: &mut Frame) -> R<Value> {
        let r = self.block_inner(b, f);
        match (r, &b.label) {
            (Err(Stop::Break(Some(l), v)), Some(own)) if l == *own => Ok(v),
            (r, _) => r,
        }
    }

    fn block_inner(&mut self, b: &HirBlock, f: &mut Frame) -> R<Value> {
        for s in &b.stmts {
            self.stmt(s, f)?;
        }
        match &b.trailing {
            Some(e) => self.expr(e, f),
            None => Ok(Value::Unit),
        }
    }

    fn stmt(&mut self, s: &HirStmt, f: &mut Frame) -> R<()> {
        match s {
            HirStmt::Let { local, init } | HirStmt::Assign { local, value: init } => {
                let v = self.expr(init, f)?;
                f.insert(*local, v);
            }
            HirStmt::ArrayAssign {
                array_local,
                index,
                value,
                ..
            } => {
                let i = self.expr(index, f)?;
                let v = self.expr(value, f)?;
                let span = index.span;
                let Some(Value::Array(items)) = f.get_mut(array_local) else {
                    return Err(Stop::Runtime(span, "writes a run-time array".to_owned()));
                };
                let len = items.len();
                let slot = index_of(&i, len, span)?;
                items[slot] = v;
            }
            HirStmt::StaticAssign { name, value } => {
                return Err(Stop::Runtime(
                    value.span,
                    format!("writes the static `{}`", leaf_name(name)),
                ));
            }
            HirStmt::Expr(e) => {
                self.expr(e, f)?;
            }
            HirStmt::Return(v) => {
                let v = match v {
                    Some(e) => self.expr(e, f)?,
                    None => Value::Unit,
                };
                return Err(Stop::Return(v));
            }
            HirStmt::Break { label, value } => {
                let v = match value {
                    Some(e) => self.expr(e, f)?,
                    None => Value::Unit,
                };
                return Err(Stop::Break(label.clone(), v));
            }
            HirStmt::Continue { label } => return Err(Stop::Continue(label.clone())),
            HirStmt::Panic(e) => {
                self.expr(e, f)?;
                return Err(Stop::Fail(e.span, "panicked".to_owned()));
            }
        }
        Ok(())
    }

    /// One loop iteration's outcome: `Ok(None)` to go on, `Ok(Some(v))`
    /// when a `break` left this loop.
    fn iteration(r: R<Value>, label: Option<&String>) -> R<Option<Value>> {
        let ours = |l: &Option<String>| l.is_none() || l.as_ref() == label;
        match r {
            Ok(_) => Ok(None),
            Err(Stop::Break(l, v)) if ours(&l) => Ok(Some(v)),
            Err(Stop::Continue(l)) if ours(&l) => Ok(None),
            Err(e) => Err(e),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn expr(&mut self, e: &HirExpr, f: &mut Frame) -> R<Value> {
        use HirExprKind as K;
        self.step(e.span)?;
        let span = e.span;
        let runtime = |what: &str| Err(Stop::Runtime(span, what.to_owned()));
        match &e.kind {
            K::Const(c) => Ok(from_const(c, &e.ty)),
            K::Local(id) => match f.get(id) {
                Some(v) => Ok(v.clone()),
                None => runtime("reads a run-time variable"),
            },
            K::Block(b) => self.block(b, f),
            K::StaticRef(name) => Err(Stop::Runtime(
                span,
                format!("reads the static `{}`", leaf_name(name)),
            )),
            K::UnresolvedPath(_) => Err(Stop::Poisoned),
            K::PrimBinOp { op, lhs, rhs } => {
                let l = self.expr(lhs, f)?;
                match (op, &l) {
                    (PrimOp::LogicalAnd, Value::Bool(false)) => return Ok(Value::Bool(false)),
                    (PrimOp::LogicalOr, Value::Bool(true)) => return Ok(Value::Bool(true)),
                    _ => {}
                }
                let r = self.expr(rhs, f)?;
                binop(*op, l, r, span)
            }
            K::PrimUnaryOp { op, operand } => {
                let v = self.expr(operand, f)?;
                unop(*op, v, span)
            }
            K::Call { callee, args } => {
                let args = self.exprs(args, f)?;
                self.call(*callee, args, span)
            }
            K::FnRef(id) => Ok(Value::Fn(*id)),
            K::CallIndirect { callee, args, .. }
            | K::CallClosure {
                closure: callee,
                args,
                ..
            } => {
                let c = self.expr(callee, f)?;
                let mut args = self.exprs(args, f)?;
                match c {
                    Value::Fn(id) => self.call(id, args, span),
                    Value::Closure(id, env) => {
                        args.insert(0, *env);
                        self.call(id, args, span)
                    }
                    _ => runtime("calls a run-time function value"),
                }
            }
            K::Cast {
                operand,
                from_ty,
                to_ty,
            } => {
                let v = self.expr(operand, f)?;
                cast(v, from_ty, to_ty, span)
            }
            K::ClosureValue { fn_id, env, .. } => {
                let env = self.expr(env, f)?;
                Ok(Value::Closure(*fn_id, Box::new(env)))
            }
            K::If {
                cond,
                then_block,
                else_branch,
            } => {
                if self.cond(cond, f)? {
                    self.block(then_block, f)
                } else if let Some(x) = else_branch {
                    self.expr(x, f)
                } else {
                    Ok(Value::Unit)
                }
            }
            K::While { label, cond, body } => {
                while self.cond(cond, f)? {
                    let r = self.block(body, f);
                    if Self::iteration(r, label.as_ref())?.is_some() {
                        break;
                    }
                }
                Ok(Value::Unit)
            }
            K::Loop { label, body, .. } => loop {
                let r = self.block(body, f);
                if let Some(v) = Self::iteration(r, label.as_ref())? {
                    return Ok(v);
                }
                self.step(span)?;
            },
            K::Match { scrutinee, arms } => {
                let v = self.expr(scrutinee, f)?;
                for arm in arms {
                    if !self.pattern(&arm.pat, &v, f, span)? {
                        continue;
                    }
                    if let Some(g) = &arm.guard {
                        if !self.cond(g, f)? {
                            continue;
                        }
                    }
                    return self.expr(&arm.body, f);
                }
                Err(Stop::Fail(span, "no `match` arm matched".to_owned()))
            }
            K::StructInit { struct_id, fields } => {
                Ok(Value::Struct(*struct_id, self.exprs(fields, f)?))
            }
            K::FieldRead {
                target,
                field_index,
                ..
            } => match self.expr(target, f)? {
                Value::Struct(_, mut fs) if (*field_index as usize) < fs.len() => {
                    Ok(fs.swap_remove(*field_index as usize))
                }
                _ => runtime("reads a field of a run-time value"),
            },
            K::WithField {
                target,
                field_index,
                value,
                ..
            } => {
                let t = self.expr(target, f)?;
                let v = self.expr(value, f)?;
                match t {
                    Value::Struct(id, mut fs) if (*field_index as usize) < fs.len() => {
                        fs[*field_index as usize] = v;
                        Ok(Value::Struct(id, fs))
                    }
                    _ => runtime("writes a field of a run-time value"),
                }
            }
            K::EnumVariantInit {
                enum_id,
                variant_index,
                args,
            } => Ok(Value::Enum(*enum_id, *variant_index, self.exprs(args, f)?)),
            K::SumWrap {
                variant_index,
                value,
                ..
            } => {
                let v = match value {
                    Some(x) => Some(Box::new(self.expr(x, f)?)),
                    None => None,
                };
                Ok(Value::Sum(*variant_index, v))
            }
            K::Tuple { fields } => Ok(Value::Tuple(self.exprs(fields, f)?)),
            K::TupleField { target, index, .. } => match self.expr(target, f)? {
                Value::Tuple(mut fs) if (*index as usize) < fs.len() => {
                    Ok(fs.swap_remove(*index as usize))
                }
                _ => runtime("reads a field of a run-time value"),
            },
            K::ArrayInit { elements, .. } => Ok(Value::Array(self.exprs(elements, f)?)),
            K::ArrayRepeat { value, len, .. } => {
                let v = self.expr(value, f)?;
                self.steps += u64::from(*len);
                self.step(span)?;
                Ok(Value::Array(vec![v; *len as usize]))
            }
            K::ArrayIndex { array, index, .. } => {
                let a = self.expr(array, f)?;
                let i = self.expr(index, f)?;
                match a {
                    Value::Array(mut items) => {
                        let slot = index_of(&i, items.len(), span)?;
                        Ok(items.swap_remove(slot))
                    }
                    _ => runtime("indexes a run-time array"),
                }
            }
            K::BufNew { elem, len } => {
                let n = self.expr(len, f)?;
                let Value::Int(n, _) = n else {
                    return runtime("allocates a run-time sized buffer");
                };
                let n = usize::try_from(n)
                    .map_err(|_| Stop::Fail(span, format!("buffer length {n} is out of range")))?;
                self.steps += n as u64;
                self.step(span)?;
                Ok(Value::Buf(Rc::new(RefCell::new(vec![zero(elem); n]))))
            }
            K::BufGet { buf, index, .. } => {
                let b = self.expr(buf, f)?;
                let i = self.expr(index, f)?;
                let Value::Buf(b) = b else {
                    return runtime("reads a run-time buffer");
                };
                let items = b.borrow();
                let slot = index_of(&i, items.len(), span)?;
                Ok(items[slot].clone())
            }
            K::BufSet {
                buf, index, value, ..
            } => {
                let b = self.expr(buf, f)?;
                let i = self.expr(index, f)?;
                let v = self.expr(value, f)?;
                let Value::Buf(b) = b else {
                    return runtime("writes a run-time buffer");
                };
                let mut items = b.borrow_mut();
                let slot = index_of(&i, items.len(), span)?;
                items[slot] = v;
                Ok(Value::Unit)
            }
            K::BufAtomic { .. } => runtime("performs an atomic operation"),
            K::RawRead { .. } | K::RawWrite { .. } => runtime("accesses raw memory"),
            K::SizeOf { .. } => runtime("asks for a type layout"),
            K::MlirOp { .. } => runtime("runs an MLIR operation"),
            K::UnionWrite { value, .. } => Ok(Value::Union(Box::new(self.expr(value, f)?))),
            K::UnionRead {
                target, field_ty, ..
            } => match self.expr(target, f)? {
                Value::Struct(_, fs) => match fs.into_iter().next() {
                    Some(Value::Union(v)) => reinterpret(*v, field_ty)
                        .ok_or_else(|| Stop::Runtime(span, "reinterprets a union".to_owned())),
                    _ => Err(Stop::Poisoned),
                },
                _ => runtime("reads a run-time union"),
            },
            K::Suspend { .. } | K::CoroNew { .. } => runtime("runs a coroutine"),
        }
    }

    fn exprs(&mut self, es: &[HirExpr], f: &mut Frame) -> R<Vec<Value>> {
        es.iter().map(|e| self.expr(e, f)).collect()
    }

    fn cond(&mut self, e: &HirExpr, f: &mut Frame) -> R<bool> {
        match self.expr(e, f)? {
            Value::Bool(b) => Ok(b),
            _ => Err(Stop::Poisoned),
        }
    }

    fn call(&mut self, id: FunctionId, args: Vec<Value>, span: Span) -> R<Value> {
        let (func, std) = match self.bodies.callee(id) {
            Callee::Body(func, std) => (func, std),
            Callee::Extern(name) if name.starts_with("rok_panic") => {
                let msg = args.first().map_or_else(String::new, |a| match a {
                    Value::Str(s) => format!(": {s}"),
                    _ => String::new(),
                });
                return Err(Stop::Fail(span, format!("panicked{msg}")));
            }
            Callee::Extern(name) => {
                return pure_extern(&name, &args).ok_or_else(|| {
                    Stop::Runtime(span, format!("calls the extern function `{name}`"))
                });
            }
            Callee::Refused(why) => return Err(Stop::Runtime(span, why)),
            Callee::Poisoned => return Err(Stop::Poisoned),
        };
        let Some(body) = &func.body else {
            return Err(Stop::Runtime(
                span,
                format!("calls `{}`, whose body is not available", func.name),
            ));
        };
        if self.depth >= DEPTH_LIMIT {
            return Err(Stop::Fail(
                span,
                format!("evaluation exceeds the call depth limit ({DEPTH_LIMIT})"),
            ));
        }
        if func.params.len() != args.len() {
            return Err(Stop::Poisoned);
        }
        let mut frame: Frame = func.params.iter().map(|p| p.local).zip(args).collect();
        self.depth += 1;
        let r = self.block(body, &mut frame);
        self.depth -= 1;
        match r {
            Ok(v) | Err(Stop::Return(v)) => Ok(v),
            // Inside a body every operation must be evaluable. A failure
            // inside the library is shown at the call that reached it.
            Err(Stop::Runtime(s, m) | Stop::Fail(s, m)) => {
                Err(Stop::Fail(if std { span } else { s }, m))
            }
            Err(Stop::Break(..) | Stop::Continue(_)) => Err(Stop::Poisoned),
            Err(e) => Err(e),
        }
    }

    fn pattern(&mut self, p: &HirPattern, v: &Value, f: &mut Frame, span: Span) -> R<bool> {
        Ok(match (p, v) {
            (HirPattern::Wildcard, _) => true,
            (HirPattern::Binding { local, .. }, _) => {
                f.insert(*local, v.clone());
                true
            }
            (HirPattern::At { local, sub, .. }, _) => {
                let hit = self.pattern(sub, v, f, span)?;
                if hit {
                    f.insert(*local, v.clone());
                }
                hit
            }
            (HirPattern::Literal { value, .. }, _) => {
                let c = from_const(value, &HirTy::Unknown);
                matches!(binop(PrimOp::Eq, v.clone(), c, span)?, Value::Bool(true))
            }
            (HirPattern::Or(alts), _) => {
                for a in alts {
                    if self.pattern(a, v, f, span)? {
                        return Ok(true);
                    }
                }
                false
            }
            (HirPattern::Tuple(ps), Value::Tuple(vs)) => self.all(ps.iter().zip(vs), f, span)?,
            (HirPattern::Struct { fields, .. }, Value::Struct(_, vs)) => {
                let pairs: Option<Vec<_>> = fields
                    .iter()
                    .map(|(i, p)| vs.get(*i as usize).map(|v| (p, v)))
                    .collect();
                let Some(pairs) = pairs else {
                    return Err(Stop::Poisoned);
                };
                self.all(pairs.into_iter(), f, span)?
            }
            (
                HirPattern::Range {
                    start,
                    end,
                    inclusive,
                    ..
                },
                _,
            ) => {
                let le = |a: Value, b: Value| -> R<bool> {
                    Ok(matches!(binop(PrimOp::Le, a, b, span)?, Value::Bool(true)))
                };
                let lt = |a: Value, b: Value| -> R<bool> {
                    Ok(matches!(binop(PrimOp::Lt, a, b, span)?, Value::Bool(true)))
                };
                let lo = match start {
                    Some(s) => le(from_const(s, &HirTy::Unknown), v.clone())?,
                    None => true,
                };
                let hi = match end {
                    Some(e) if *inclusive => le(v.clone(), from_const(e, &HirTy::Unknown))?,
                    Some(e) => lt(v.clone(), from_const(e, &HirTy::Unknown))?,
                    None => true,
                };
                lo && hi
            }
            (
                HirPattern::EnumVariant {
                    variant_index,
                    args,
                    ..
                },
                Value::Enum(_, idx, vs),
            ) => *variant_index == *idx && self.all(args.iter().zip(vs), f, span)?,
            (
                HirPattern::SumVariant {
                    variant_index,
                    binder,
                    ..
                },
                Value::Sum(idx, payload),
            ) => {
                if *variant_index != *idx {
                    return Ok(false);
                }
                if let Some(b) = binder {
                    f.insert(*b, payload.as_deref().cloned().unwrap_or(Value::None));
                }
                true
            }
            (
                HirPattern::SumMember {
                    variant_index, sub, ..
                },
                Value::Sum(idx, Some(payload)),
            ) => *variant_index == *idx && self.pattern(sub, payload, f, span)?,
            _ => false,
        })
    }

    fn all<'p>(
        &mut self,
        pairs: impl Iterator<Item = (&'p HirPattern, &'p Value)>,
        f: &mut Frame,
        span: Span,
    ) -> R<bool> {
        for (p, v) in pairs {
            if !self.pattern(p, v, f, span)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// The runtime's pure `str` functions (`rok::core::str` is built on
/// them), computed here exactly as `rokr` does.
fn pure_extern(name: &str, args: &[Value]) -> Option<Value> {
    let int = |v: &Value| match v {
        Value::Int(i, _) => usize::try_from(*i).ok(),
        _ => None,
    };
    let usize_value = |n: usize| Value::Int(n as i128, PrimTy::Usize);
    Some(match (name, args) {
        ("rok_str_len", [Value::Str(s)]) => usize_value(s.len()),
        ("rok_str_char_count", [Value::Str(s)]) => usize_value(s.chars().count()),
        ("rok_str_byte", [Value::Str(s), i]) => Value::Int(
            i128::from(s.as_bytes().get(int(i)?).copied().unwrap_or(0)),
            PrimTy::U8,
        ),
        ("rok_str_cmp", [Value::Str(a), Value::Str(b)]) => {
            Value::Int(a.as_bytes().cmp(b.as_bytes()) as i128, PrimTy::I32)
        }
        ("rok_str_concat", [Value::Str(a), Value::Str(b)]) => Value::Str(format!("{a}{b}").into()),
        ("rok_str_from_char", [c]) => {
            let c = match c {
                Value::Int(c, _) => u32::try_from(*c).ok()?,
                Value::Char(c) => *c,
                _ => return None,
            };
            Value::Str(char::from_u32(c)?.to_string().into())
        }
        ("rok_bytes_slice", [Value::Str(s), a, b]) => {
            let end = int(b)?.min(s.len());
            let start = int(a)?.min(end);
            // A cut inside a char is not a `str` this evaluator holds.
            Value::Str(s.get(start..end)?.into())
        }
        _ => return None,
    })
}

/// A primitive's bits read back as primitive `to` (a union read).
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn reinterpret(v: Value, to: &HirTy) -> Option<Value> {
    let tp = prim_of(to)?;
    let bits: u64 = match v {
        Value::Int(i, p) => (i as u64) & (u64::MAX >> (64 - p.bit_width(POINTER_WIDTH))),
        Value::Char(c) => u64::from(c),
        Value::Bool(b) => u64::from(b),
        Value::Float(x, PrimTy::F32) => u64::from((x as f32).to_bits()),
        Value::Float(x, _) => x.to_bits(),
        _ => return None,
    };
    Some(match tp {
        PrimTy::Bool => Value::Bool(bits & 1 == 1),
        PrimTy::Char | PrimTy::CChar => Value::Char(bits as u32),
        PrimTy::F32 => Value::Float(f64::from(f32::from_bits(bits as u32)), tp),
        PrimTy::F64 => Value::Float(f64::from_bits(bits), tp),
        p if p.is_int() => Value::Int(wrap(i128::from(bits), p), p),
        _ => return None,
    })
}

/// The zeroed element of a fresh buffer.
const fn zero(ty: &HirTy) -> Value {
    match ty {
        HirTy::Prim(PrimTy::Bool) => Value::Bool(false),
        HirTy::Prim(p) if p.is_float() => Value::Float(0.0, *p),
        HirTy::Prim(PrimTy::Char | PrimTy::CChar) => Value::Char(0),
        HirTy::Prim(p) if p.is_int() => Value::Int(0, *p),
        _ => Value::Unit,
    }
}

fn index_of(i: &Value, len: usize, span: Span) -> R<usize> {
    let Value::Int(i, _) = i else {
        return Err(Stop::Poisoned);
    };
    match usize::try_from(*i) {
        Ok(slot) if slot < len => Ok(slot),
        _ => Err(Stop::Fail(
            span,
            format!("index out of bounds: the len is {len} but the index is {i}"),
        )),
    }
}

fn checked(v: Option<i128>, p: PrimTy, what: &str, span: Span) -> R<Value> {
    let (lo, hi) = int_range(p);
    match v {
        Some(v) if (lo..=hi).contains(&v) => Ok(Value::Int(v, p)),
        _ => Err(Stop::Fail(span, format!("attempt to {what} with overflow"))),
    }
}

fn shift_amount(r: i128, p: PrimTy, span: Span, dir: &str) -> R<u32> {
    let bits = p.bit_width(POINTER_WIDTH);
    match u32::try_from(r) {
        Ok(n) if n < bits => Ok(n),
        _ => Err(Stop::Fail(
            span,
            format!("attempt to shift {dir} with overflow"),
        )),
    }
}

#[allow(clippy::too_many_lines, clippy::float_cmp)]
fn binop(op: PrimOp, l: Value, r: Value, span: Span) -> R<Value> {
    use PrimOp as O;
    let cmp = |o: std::cmp::Ordering| -> Value {
        Value::Bool(match op {
            O::Eq => o.is_eq(),
            O::Ne => o.is_ne(),
            O::Lt => o.is_lt(),
            O::Le => o.is_le(),
            O::Gt => o.is_gt(),
            _ => o.is_ge(),
        })
    };
    let is_cmp = matches!(op, O::Eq | O::Ne | O::Lt | O::Le | O::Gt | O::Ge);
    match (l, r) {
        (Value::Int(a, p), Value::Int(b, _)) => {
            if is_cmp {
                return Ok(cmp(a.cmp(&b)));
            }
            #[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]
            match op {
                O::Add => checked(a.checked_add(b), p, "add", span),
                O::Sub => checked(a.checked_sub(b), p, "subtract", span),
                O::Mul => checked(a.checked_mul(b), p, "multiply", span),
                O::Div | O::Rem => {
                    let div = op == O::Div;
                    if b == 0 {
                        return Err(Stop::Fail(
                            span,
                            if div {
                                "attempt to divide by zero"
                            } else {
                                "attempt to calculate the remainder with a divisor of zero"
                            }
                            .to_owned(),
                        ));
                    }
                    let what = if div {
                        "divide"
                    } else {
                        "calculate the remainder"
                    };
                    if p.is_signed_int() && b == -1 && a == int_range(p).0 {
                        return Err(Stop::Fail(span, format!("attempt to {what} with overflow")));
                    }
                    Ok(Value::Int(if div { a / b } else { a % b }, p))
                }
                O::BitAnd => Ok(Value::Int(a & b, p)),
                O::BitOr => Ok(Value::Int(a | b, p)),
                O::BitXor => Ok(Value::Int(a ^ b, p)),
                O::Shl => {
                    let n = shift_amount(b, p, span, "left")?;
                    Ok(Value::Int(wrap(((a as u128) << n) as i128, p), p))
                }
                O::Shr => {
                    let n = shift_amount(b, p, span, "right")?;
                    Ok(Value::Int(a >> n, p))
                }
                O::WrappingAdd => Ok(Value::Int(wrap(a.wrapping_add(b), p), p)),
                O::WrappingSub => Ok(Value::Int(wrap(a.wrapping_sub(b), p), p)),
                O::WrappingMul => Ok(Value::Int(wrap(a.wrapping_mul(b), p), p)),
                _ => Err(Stop::Poisoned),
            }
        }
        (Value::Float(a, p), Value::Float(b, _)) => {
            if is_cmp {
                return Ok(match a.partial_cmp(&b) {
                    Some(o) => cmp(o),
                    None => Value::Bool(op == O::Ne),
                });
            }
            let v = match op {
                O::Add => a + b,
                O::Sub => a - b,
                O::Mul => a * b,
                O::Div => a / b,
                O::Rem => a % b,
                _ => return Err(Stop::Poisoned),
            };
            // `f32` arithmetic on `f32`-exact operands, rounded once:
            // the same as computing in `f32`.
            Ok(Value::Float(round(v, p), p))
        }
        (Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(match op {
            O::BitAnd | O::LogicalAnd => a & b,
            O::BitOr | O::LogicalOr => a | b,
            O::BitXor => a ^ b,
            _ if is_cmp => return Ok(cmp(a.cmp(&b))),
            _ => return Err(Stop::Poisoned),
        })),
        (Value::Char(a), Value::Char(b)) if is_cmp => Ok(cmp(a.cmp(&b))),
        (Value::Str(a), Value::Str(b)) if is_cmp => Ok(cmp(a.as_bytes().cmp(b.as_bytes()))),
        (Value::Unit, Value::Unit) | (Value::None, Value::None) if is_cmp => {
            Ok(cmp(std::cmp::Ordering::Equal))
        }
        _ => Err(Stop::Poisoned),
    }
}

fn unop(op: PrimOp, v: Value, span: Span) -> R<Value> {
    let bits_of = |p: PrimTy| p.bit_width(POINTER_WIDTH);
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)]
    let raw = |a: i128, p: PrimTy| (a as u128) & ((1u128 << bits_of(p)) - 1);
    match (op, v) {
        (PrimOp::Neg, Value::Int(a, p)) => checked(0i128.checked_sub(a), p, "negate", span),
        (PrimOp::Neg, Value::Float(a, p)) => Ok(Value::Float(-a, p)),
        (PrimOp::Not | PrimOp::LogicalNot, Value::Bool(b)) => Ok(Value::Bool(!b)),
        (PrimOp::Not, Value::Int(a, p)) => Ok(Value::Int(wrap(!a, p), p)),
        (PrimOp::Sqrt, Value::Float(a, p)) => {
            #[allow(clippy::cast_possible_truncation)]
            let r = if p == PrimTy::F32 {
                f64::from((a as f32).sqrt())
            } else {
                a.sqrt()
            };
            Ok(Value::Float(r, p))
        }
        (PrimOp::CountOnes, Value::Int(a, p)) => {
            Ok(Value::Int(i128::from(raw(a, p).count_ones()), p))
        }
        (PrimOp::LeadingZeros, Value::Int(a, p)) => Ok(Value::Int(
            i128::from(raw(a, p).leading_zeros() - (128 - bits_of(p))),
            p,
        )),
        (PrimOp::TrailingZeros, Value::Int(a, p)) => {
            let r = raw(a, p);
            let n = if r == 0 {
                bits_of(p)
            } else {
                r.trailing_zeros()
            };
            Ok(Value::Int(i128::from(n), p))
        }
        #[allow(clippy::cast_possible_wrap)]
        (PrimOp::SwapBytes, Value::Int(a, p)) => {
            let swapped = raw(a, p).swap_bytes() >> (128 - bits_of(p));
            Ok(Value::Int(wrap(swapped as i128, p), p))
        }
        _ => Err(Stop::Poisoned),
    }
}

#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss
)]
fn cast(v: Value, from: &HirTy, to: &HirTy, span: Span) -> R<Value> {
    let Some(tp) = prim_of(to) else {
        return if from == to {
            Ok(v)
        } else {
            Err(Stop::Runtime(
                span,
                "casts a non-primitive value".to_owned(),
            ))
        };
    };
    let int_value = match &v {
        Value::Int(a, _) => Some(*a),
        Value::Bool(b) => Some(i128::from(*b)),
        Value::Char(c) => Some(i128::from(*c)),
        _ => None,
    };
    match (int_value, &v) {
        (Some(a), _) if tp == PrimTy::Bool => Ok(Value::Bool(a != 0)),
        (Some(a), _) if matches!(tp, PrimTy::Char | PrimTy::CChar) => {
            Ok(Value::Char(wrap(a, PrimTy::U32) as u32))
        }
        (Some(a), _) if tp.is_int() => Ok(Value::Int(wrap(a, tp), tp)),
        (Some(a), _) if tp == PrimTy::F32 => Ok(Value::Float(f64::from(a as f32), tp)),
        (Some(a), _) if tp == PrimTy::F64 => Ok(Value::Float(a as f64, tp)),
        (None, Value::Float(x, _)) if tp.is_float() => Ok(Value::Float(round(*x, tp), tp)),
        (None, Value::Float(x, _)) if tp.is_int() => {
            let t = x.trunc();
            let (lo, hi) = int_range(tp);
            // `fptosi` / `fptoui` of a value out of range is poison.
            if t.is_nan() || t < lo as f64 || t > hi as f64 || t as i128 > hi {
                return Err(Stop::Fail(
                    span,
                    format!("`{x}` does not fit in `{}`", tp.name()),
                ));
            }
            Ok(Value::Int(t as i128, tp))
        }
        (None, Value::Str(_)) if tp == PrimTy::Str => Ok(v),
        _ => Err(Stop::Runtime(span, "casts a run-time value".to_owned())),
    }
}

/// Bodies for an evaluation inside lowering: lowered extras as they are,
/// other declarations lowered on demand.
pub(super) struct CtxBodies<'c, 'a> {
    ctx: &'c LowerCtx<'a>,
    cache: HashMap<FunctionId, (Rc<HirFunction>, bool)>,
}

impl<'c, 'a> CtxBodies<'c, 'a> {
    pub(super) fn new(ctx: &'c LowerCtx<'a>) -> Self {
        Self {
            ctx,
            cache: HashMap::new(),
        }
    }
}

/// `rok::*`: the standard library.
fn is_std(module: &str) -> bool {
    module == "rok" || module.starts_with("rok::")
}

impl Bodies for CtxBodies<'_, '_> {
    fn callee(&mut self, id: FunctionId) -> Callee {
        if let Some((f, std)) = self.cache.get(&id) {
            return Callee::Body(Rc::clone(f), *std);
        }
        let env = self.ctx.env;
        let name = |f: &str| leaf_name(f).to_owned();
        let found = env
            .sink
            .extras
            .borrow()
            .iter()
            .find(|f| f.id == id)
            .cloned();
        let (func, std) = if let Some(f) = found {
            // Lifted closures / thunks have no origin and belong to
            // their (const) definer.
            let origin = env.sink.fn_origin.borrow().get(&id).copied();
            if origin == Some((false, false)) {
                return Callee::Refused(not_const(&name(&f.name)));
            }
            (f, origin.is_some_and(|(_, std)| std))
        } else if let Some(decl) = env.decls.get(id.0 as usize) {
            let (MethodOrFn::Fn(def) | MethodOrFn::Method { fn_def: def, .. }) = decl;
            if env.extern_fn_ids.contains(&id) || env.rok_externs.contains(&id) {
                return Callee::Extern(def.name.clone());
            }
            let module = match decl {
                MethodOrFn::Fn(f) => module_of(&f.name),
                MethodOrFn::Method { module, .. } => module.clone(),
            };
            let is_const = def
                .attrs
                .iter()
                .any(|a| a.path == [rokc_ast::CONST_FN_ATTR]);
            if !is_const && !is_std(&module) {
                return Callee::Refused(not_const(&name(&def.name)));
            }
            if def.body.is_none() {
                return Callee::Refused(format!(
                    "calls `{}`, whose body is not available",
                    name(&def.name)
                ));
            }
            if !env.sink.const_lowering.borrow_mut().insert(id) {
                return Callee::Refused(format!("`{}` depends on itself", name(&def.name)));
            }
            let f = super::collect::lower_decl(env, id.0 as usize, false);
            env.sink.const_lowering.borrow_mut().remove(&id);
            (f, is_std(&module))
        } else {
            return Callee::Refused("calls a function that is still being compiled".to_owned());
        };
        if func
            .body
            .as_ref()
            .is_some_and(super::collect::hir_block_has_unknown)
        {
            return Callee::Poisoned;
        }
        let func = Rc::new(func);
        self.cache.insert(id, (Rc::clone(&func), std));
        Callee::Body(func, std)
    }
}

fn not_const(name: &str) -> String {
    format!("calls `{name}`, which is not a `const fn` (spec 5.2.5)")
}

/// Evaluate a lowered expression in `ctx`.
pub(super) fn eval_in(ctx: &LowerCtx<'_>, e: &HirExpr) -> R<Value> {
    if super::collect::hir_expr_has_unknown(e) {
        return Err(Stop::Poisoned);
    }
    let mut bodies = CtxBodies::new(ctx);
    Interp::new(&mut bodies).eval(e)
}

fn report(ctx: &LowerCtx<'_>, at: Span, what: &str, op: Span, why: &str) {
    let mut d = rokc_diagnostic::RokDiagnostic::error(
        rokc_diagnostic::ErrorKind::Type,
        format!("{what} cannot be evaluated at compile time: {why}"),
    )
    .with_span(at, "");
    if op != at && !op.is_dummy() {
        d = d.with_secondary(op, "here");
    }
    ctx.env.sink.diagnostics.borrow_mut().push(d);
}

/// Lower const `name`'s value with `lower`, unless it is already being
/// lowered: a const defined through itself is an error (`None`).
pub(super) fn guard(
    ctx: &mut LowerCtx<'_>,
    name: &str,
    span: Span,
    lower: impl FnOnce(&mut LowerCtx<'_>) -> HirExpr,
) -> Option<HirExpr> {
    let stack = &ctx.env.sink.const_stack;
    if stack.borrow().iter().any(|n| n == name) {
        let d = rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            format!("const `{}` is defined in terms of itself", leaf_name(name)),
        )
        .with_span(span, "");
        ctx.env.sink.diagnostics.borrow_mut().push(d);
        return None;
    }
    stack.borrow_mut().push(name.to_owned());
    let v = lower(ctx);
    ctx.env.sink.const_stack.borrow_mut().pop();
    Some(v)
}

/// A const item's value at a use (spec 5.2): evaluated, and embedded
/// as a constant when it is plain data. Not evaluable is an error.
pub(super) fn const_item(ctx: &LowerCtx<'_>, name: &str, v: HirExpr) -> HirExpr {
    let what = format!("const `{}`", leaf_name(name));
    match eval_in(ctx, &v) {
        Ok(val) => embed(ctx, &val, &v.ty, v.span).unwrap_or(v),
        Err(Stop::Runtime(op, why) | Stop::Fail(op, why)) => {
            report(ctx, v.span, &what, op, &why);
            poison(v.span)
        }
        Err(_) => v,
    }
}

/// A `#[literal]` handler call (spec 6.5.8): the outermost call to a
/// `const fn` in `h` runs now when its arguments are constants. A
/// failure inside the handler (a panic, a `throw`) is a compile error
/// at the literal.
pub(super) fn fold_literal(ctx: &LowerCtx<'_>, h: &mut HirExpr, at: Span) {
    if let HirExprKind::Call { callee, .. } = &h.kind {
        if is_const_fn(ctx, *callee) {
            fold_call(ctx, h, at);
            return;
        }
    }
    match &mut h.kind {
        HirExprKind::Block(b) => {
            for s in &mut b.stmts {
                if let HirStmt::Let { init: e, .. } | HirStmt::Expr(e) = s {
                    fold_literal(ctx, e, at);
                }
            }
            if let Some(t) = &mut b.trailing {
                fold_literal(ctx, t, at);
            }
        }
        HirExprKind::SumWrap { value: Some(e), .. }
        | HirExprKind::Cast { operand: e, .. }
        | HirExprKind::TupleField { target: e, .. } => fold_literal(ctx, e, at),
        _ => {}
    }
}

fn is_const_fn(ctx: &LowerCtx<'_>, id: FunctionId) -> bool {
    let env = ctx.env;
    if let Some(&(is_const, _)) = env.sink.fn_origin.borrow().get(&id) {
        return is_const;
    }
    env.decls.get(id.0 as usize).is_some_and(|d| {
        let (MethodOrFn::Fn(def) | MethodOrFn::Method { fn_def: def, .. }) = d;
        def.attrs
            .iter()
            .any(|a| a.path == [rokc_ast::CONST_FN_ATTR])
    })
}

fn fold_call(ctx: &LowerCtx<'_>, h: &mut HirExpr, at: Span) {
    match eval_in(ctx, h) {
        Ok(val) => {
            // A handler that threw: its carrier says so.
            if let (HirTy::Throws { .. }, Value::Tuple(fs)) = (&h.ty, &val) {
                if let (Some(Value::Bool(true)), Some(err)) = (fs.first(), fs.last()) {
                    report(
                        ctx,
                        at,
                        "literal",
                        at,
                        &format!("the handler threw {}", describe(err)),
                    );
                    return;
                }
            }
            if let Some(c) = embed(ctx, &val, &h.ty, h.span) {
                *h = c;
            }
        }
        Err(Stop::Fail(op, why)) => report(ctx, at, "literal", op, &why),
        // Run-time arguments: the call stays.
        Err(_) => {}
    }
}

/// An integer in a type position (array length, const generic argument)
/// lowered in `ctx` and evaluated.
pub(super) fn eval_int(ctx: &LowerCtx<'_>, e: &Expr) -> Result<i128, String> {
    let mut cx = ctx.clone();
    // A const parameter bound without its type reads as a `usize`.
    for (n, t) in ctx.ty_subst {
        if let Some((v, None)) = crate::ty::as_const(t) {
            cx.splices
                .insert(n.clone(), hir_int(v, PrimTy::Usize, e.span));
        }
    }
    let mark = cx.probe_mark();
    let h = lower_expected(&mut cx, e, HirTy::Unknown);
    let lowering_error = cx
        .env
        .sink
        .diagnostics
        .borrow()
        .get(mark.diagnostics)
        .map(|d| d.message.clone());
    let r = match lowering_error {
        Some(why) => Err(why),
        None => match eval_in(&cx, &h) {
            Ok(Value::Int(v, _)) => Ok(v),
            Ok(Value::Bool(b)) => Ok(i128::from(b)),
            Ok(_) => Err("not an integer".to_owned()),
            Err(Stop::Runtime(_, why) | Stop::Fail(_, why)) => Err(why),
            Err(_) => Err("not a constant".to_owned()),
        },
    };
    cx.rollback_all(&mark);
    r
}

/// Evaluate every const item of the user's package once (spec 5.2.7),
/// so an unused one is checked too.
pub(super) fn check_user_consts(env: &Env<'_>) {
    let no_subst = HashMap::new();
    let mut keys: Vec<&String> = env
        .consts
        .keys()
        .filter(|k| package_of(&module_of(k)).is_empty())
        .collect();
    keys.sort();
    for key in keys {
        let span = env.consts[key].1.span;
        let outer = rokc_diagnostic::set_current_span(span);
        let mut ctx = LowerCtx::new(env, &no_subst, None);
        let module = module_of(key);
        // Impl consts (`S::N`) are checked where they are read.
        let segs: Vec<&str> = module.split("::").collect();
        if !module.is_empty() && ctx.canon_type(&segs).as_deref() == Some(module.as_str()) {
            rokc_diagnostic::set_current_span(outer);
            continue;
        }
        ctx.current_module = module;
        let path = rokc_ast::Path {
            segments: vec![rokc_ast::PathSegment {
                name: leaf_name(key).to_owned(),
                generics: Vec::new(),
            }],
            span,
        };
        super::expr::lower_path(&mut ctx, &path, span);
        rokc_diagnostic::set_current_span(outer);
    }
}

/// A static's initializer function, run now (spec 5.3.1): its value
/// when it is a primitive constant; `None` keeps the lazy initializer.
pub(super) fn static_init(env: &Env<'_>, init_fn: &HirFunction) -> Option<ConstVal> {
    let no_subst = HashMap::new();
    let ctx = LowerCtx::new(env, &no_subst, None);
    let body = init_fn.body.as_ref()?;
    if super::collect::hir_block_has_unknown(body) {
        return None;
    }
    let mut bodies = CtxBodies::new(&ctx);
    let mut interp = Interp::new(&mut bodies);
    let (Ok(v) | Err(Stop::Return(v))) = interp.block(body, &mut Frame::new()) else {
        return None;
    };
    match embed(&ctx, &v, &init_fn.ret_ty, init_fn.span)?.kind {
        HirExprKind::Const(c) => Some(c),
        _ => None,
    }
}

/// Pre-pass integer constant (item signatures, before any body is
/// lowered): literals, names `lookup` knows, unary `-` and `+ - * / %
/// << >> & | ^` over them, as `i64` on the same evaluator.
pub fn syntactic_int(
    c: &rokc_ast::ConstExpr,
    lookup: &dyn Fn(&str) -> Option<i128>,
) -> Option<i128> {
    fn lower(e: &Expr, lookup: &dyn Fn(&str) -> Option<i128>) -> Option<HirExpr> {
        let int = |v: i128| hir_int(v, PrimTy::I64, e.span);
        let kind = match &e.kind {
            ExprKind::Literal(AstLit::Int(s)) => return parse_int_literal(s).map(|(v, _)| int(v)),
            ExprKind::Path(p) if p.segments.len() == 1 => {
                return lookup(&p.segments[0].name).map(int);
            }
            ExprKind::OpPrefix { op, operand } if op == "-" => HirExprKind::PrimUnaryOp {
                op: PrimOp::Neg,
                operand: Box::new(lower(operand, lookup)?),
            },
            ExprKind::OpInfix { op, lhs, rhs } => HirExprKind::PrimBinOp {
                op: match op.as_str() {
                    "+" => PrimOp::Add,
                    "-" => PrimOp::Sub,
                    "*" => PrimOp::Mul,
                    "/" => PrimOp::Div,
                    "%" => PrimOp::Rem,
                    "<<" => PrimOp::Shl,
                    ">>" => PrimOp::Shr,
                    "&" => PrimOp::BitAnd,
                    "|" => PrimOp::BitOr,
                    "^" => PrimOp::BitXor,
                    _ => return None,
                },
                lhs: Box::new(lower(lhs, lookup)?),
                rhs: Box::new(lower(rhs, lookup)?),
            },
            _ => return None,
        };
        Some(HirExpr {
            kind,
            ty: HirTy::Prim(PrimTy::I64),
            span: e.span,
        })
    }
    let h = match c {
        rokc_ast::ConstExpr::Literal(AstLit::Int(s)) => {
            return parse_int_literal(s).map(|(v, _)| v);
        }
        rokc_ast::ConstExpr::Path(p) if p.segments.len() == 1 => {
            return lookup(&p.segments[0].name);
        }
        rokc_ast::ConstExpr::Literal(_) | rokc_ast::ConstExpr::Path(_) => return None,
        rokc_ast::ConstExpr::Expr(e) => lower(e, lookup)?,
    };
    match Interp::new(&mut NoBodies).eval(&h) {
        Ok(Value::Int(v, _)) => Some(v),
        _ => None,
    }
}

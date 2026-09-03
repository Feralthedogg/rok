//! One exhaustive pre-order AST walker for the lowering pre-passes
//! (generic-instantiation discovery, closure capture analysis). Every
//! match is exhaustive so a new AST node kind is a compile error here
//! instead of a silently skipped subtree.

use rokc_ast::{
    AccessTail, Block, CallArg, EnumVariantKind, Expr, ExprKind, FnDef, ImplItem, Item, Pattern,
    PatternKind, Stmt, StmtKind, StructKind, TraitItem, Ty, TyKind,
};

/// Callbacks for `walk_*`. Scope events (`push_scope` / `bind` /
/// `pop_scope`) follow the language's lexical rules: a `let` binds after
/// its initializer, match / for / closure binders are scoped to their
/// body.
pub(crate) trait AstVisitor {
    fn expr(&mut self, _e: &Expr) {}
    fn ty(&mut self, _t: &Ty) {}
    fn bind(&mut self, _name: &str) {}
    fn push_scope(&mut self) {}
    fn pop_scope(&mut self) {}
}

pub(crate) fn walk_item(v: &mut impl AstVisitor, item: &Item) {
    match item {
        Item::Fn(f) => walk_fn(v, f),
        Item::Struct(s) => match &s.kind {
            StructKind::Named(fields) => {
                for f in fields {
                    walk_ty(v, &f.ty);
                    if let Some(d) = &f.default {
                        walk_expr(v, d);
                    }
                }
            }
            StructKind::Tuple(fields) => {
                for f in fields {
                    walk_ty(v, &f.ty);
                }
            }
            StructKind::Unit => {}
        },
        Item::Enum(e) => {
            for var in &e.variants {
                match &var.kind {
                    EnumVariantKind::Unit => {}
                    EnumVariantKind::Tuple(tys) => {
                        for t in tys {
                            walk_ty(v, t);
                        }
                    }
                    EnumVariantKind::Named(fields) => {
                        for f in fields {
                            walk_ty(v, &f.ty);
                        }
                    }
                    EnumVariantKind::Value(e) => walk_expr(v, e),
                }
            }
        }
        Item::Union(u) => {
            for f in &u.fields {
                walk_ty(v, &f.ty);
            }
        }
        Item::Impl(impl_def) => {
            walk_ty(v, &impl_def.self_ty);
            for ii in &impl_def.items {
                match ii {
                    ImplItem::Method(m) => walk_fn(v, m),
                    ImplItem::AssocType { ty, .. } => walk_ty(v, ty),
                    ImplItem::Const(c) => {
                        walk_ty(v, &c.ty);
                        walk_expr(v, &c.value);
                    }
                }
            }
        }
        Item::Trait(t) => {
            for ti in &t.items {
                match ti {
                    TraitItem::Method(m) => walk_fn(v, m),
                    TraitItem::AssocType { .. } => {}
                    TraitItem::Const(c) => {
                        walk_ty(v, &c.ty);
                        walk_expr(v, &c.value);
                    }
                }
            }
        }
        Item::Const(c) => {
            walk_ty(v, &c.ty);
            walk_expr(v, &c.value);
        }
        Item::Static(s) => {
            walk_ty(v, &s.ty);
            if let Some(e) = &s.value {
                walk_expr(v, e);
            }
        }
        Item::TypeAlias(a) => walk_ty(v, &a.ty),
        Item::Extern(blk) => {
            for ei in &blk.items {
                if let rokc_ast::ExternItem::Fn(f) = ei {
                    walk_fn(v, f);
                }
            }
        }
        Item::Use(_) | Item::Mod(_) => {}
    }
}

pub(crate) fn walk_fn(v: &mut impl AstVisitor, f: &FnDef) {
    v.push_scope();
    for p in &f.params {
        if let Some(t) = &p.ty {
            walk_ty(v, t);
        }
        if let Some(d) = &p.default {
            walk_expr(v, d);
        }
        v.bind(&p.name);
    }
    if let Some(t) = &f.ret_ty {
        walk_ty(v, t);
    }
    if let Some(body) = &f.body {
        walk_block(v, body);
    }
    v.pop_scope();
}

pub(crate) fn walk_block(v: &mut impl AstVisitor, b: &Block) {
    v.push_scope();
    for s in &b.stmts {
        walk_stmt(v, s);
    }
    if let Some(t) = &b.trailing {
        walk_expr(v, t);
    }
    v.pop_scope();
}

pub(crate) fn walk_stmt(v: &mut impl AstVisitor, s: &Stmt) {
    match &s.kind {
        StmtKind::Let { name, ty, init } => {
            walk_expr(v, init);
            if let Some(t) = ty {
                walk_ty(v, t);
            }
            v.bind(name);
        }
        StmtKind::LetTuple { names, rest, ty, init } => {
            walk_expr(v, init);
            if let Some(t) = ty {
                walk_ty(v, t);
            }
            for n in names.iter().filter(|n| *n != "_") {
                v.bind(n);
            }
            if let Some((_, Some(r))) = rest {
                v.bind(r);
            }
        }
        StmtKind::LetStruct { path, fields, ty, init, .. } => {
            walk_expr(v, init);
            if let Some(t) = ty {
                walk_ty(v, t);
            }
            walk_path_generics(v, path);
            for (_, bind) in fields {
                v.bind(bind);
            }
        }
        StmtKind::Assign(a, b) => {
            walk_expr(v, a);
            walk_expr(v, b);
        }
        StmtKind::CompoundAssign { target, value, .. } => {
            walk_expr(v, target);
            walk_expr(v, value);
        }
        // Nested items have their own scopes; their bodies can't see the
        // enclosing function's locals.
        StmtKind::Item(_) => {}
        StmtKind::Expr(e) | StmtKind::Trailing(e) | StmtKind::Throw(e) => walk_expr(v, e),
        StmtKind::Return(e) | StmtKind::Break { value: e, .. } => {
            if let Some(e) = e {
                walk_expr(v, e);
            }
        }
        StmtKind::Continue { .. } => {}
    }
}

fn walk_args(v: &mut impl AstVisitor, args: &[CallArg]) {
    for a in args {
        match a {
            CallArg::Positional(e) | CallArg::Spread(e) | CallArg::Named { value: e, .. } => {
                walk_expr(v, e);
            }
        }
    }
}

fn walk_path_generics(v: &mut impl AstVisitor, p: &rokc_ast::Path) {
    for seg in &p.segments {
        for g in &seg.generics {
            walk_ty(v, g);
        }
    }
}

pub(crate) fn walk_expr(v: &mut impl AstVisitor, e: &Expr) {
    v.expr(e);
    match &e.kind {
        ExprKind::Literal(_) | ExprKind::SelfLower | ExprKind::SelfUpper => {}
        ExprKind::Path(p) => walk_path_generics(v, p),
        ExprKind::Tuple(items) | ExprKind::List(items) | ExprKind::Set(items) => {
            for i in items {
                walk_expr(v, i);
            }
        }
        ExprKind::Dict(pairs) => {
            for (k, val) in pairs {
                walk_expr(v, k);
                walk_expr(v, val);
            }
        }
        ExprKind::Block(b)
        | ExprKind::AsyncBlock(b)
        | ExprKind::YieldBlock(b)
        | ExprKind::AsyncYieldBlock(b) => walk_block(v, b),
        ExprKind::If { cond, then_branch, else_branch } => {
            walk_expr(v, cond);
            walk_block(v, then_branch);
            if let Some(eb) = else_branch {
                walk_expr(v, eb);
            }
        }
        ExprKind::Match { scrutinee, arms } => {
            walk_expr(v, scrutinee);
            for arm in arms {
                v.push_scope();
                walk_pat(v, &arm.pat);
                if let Some(g) = &arm.guard {
                    walk_expr(v, g);
                }
                walk_expr(v, &arm.body);
                v.pop_scope();
            }
        }
        ExprKind::Loop { body, .. } => walk_block(v, body),
        ExprKind::While { cond, body, .. } => {
            walk_expr(v, cond);
            walk_block(v, body);
        }
        ExprKind::For { pat, iter, body, .. } => {
            walk_expr(v, iter);
            v.push_scope();
            walk_pat(v, pat);
            walk_block(v, body);
            v.pop_scope();
        }
        ExprKind::Try { body, catches, finally } => {
            walk_block(v, body);
            for c in catches {
                v.push_scope();
                walk_pat(v, &c.pat);
                walk_block(v, &c.body);
                v.pop_scope();
            }
            if let Some(f) = finally {
                walk_block(v, f);
            }
        }
        ExprKind::LetElse { pat, ty, init, else_body } => {
            walk_expr(v, init);
            if let Some(t) = ty {
                walk_ty(v, t);
            }
            walk_block(v, else_body);
            walk_pat(v, pat);
        }
        ExprKind::OpInfix { lhs, rhs, .. } | ExprKind::NullishCoalesce(lhs, rhs) => {
            walk_expr(v, lhs);
            walk_expr(v, rhs);
        }
        ExprKind::Index(lhs, rhs) => {
            walk_expr(v, lhs);
            walk_expr(v, rhs);
        }
        ExprKind::OpPrefix { operand, .. } | ExprKind::OpPostfix { operand, .. } => {
            walk_expr(v, operand);
        }
        ExprKind::Cast(inner, ty) => {
            walk_expr(v, inner);
            walk_ty(v, ty);
        }
        ExprKind::Is(inner, pat) => {
            walk_expr(v, inner);
            walk_pat(v, pat);
        }
        ExprKind::Field(t, _) | ExprKind::TupleField(t, _) => walk_expr(v, t),
        ExprKind::MethodCall { receiver, type_args, args, trailing_closure, .. } => {
            walk_expr(v, receiver);
            for t in type_args {
                walk_ty(v, t);
            }
            walk_args(v, args);
            if let Some(tc) = trailing_closure {
                walk_expr(v, tc);
            }
        }
        ExprKind::Call { callee, args, trailing_closure } => {
            walk_expr(v, callee);
            walk_args(v, args);
            if let Some(tc) = trailing_closure {
                walk_expr(v, tc);
            }
        }
        ExprKind::Slice { target, start, end, step } => {
            walk_expr(v, target);
            for x in [start, end, step].into_iter().flatten() {
                walk_expr(v, x);
            }
        }
        ExprKind::Range { start, end, .. } => {
            for x in [start, end].into_iter().flatten() {
                walk_expr(v, x);
            }
        }
        ExprKind::QuestionDot(t, tail) => {
            walk_expr(v, t);
            match tail {
                AccessTail::Field(_) | AccessTail::TupleField(_) => {}
                AccessTail::Method { type_args, args, .. } => {
                    for t in type_args {
                        walk_ty(v, t);
                    }
                    walk_args(v, args);
                }
                AccessTail::Index(i) => walk_expr(v, i),
            }
        }
        ExprKind::TryQ(inner)
        | ExprKind::Await(inner)
        | ExprKind::Spread(inner)
        | ExprKind::Discard(inner) => walk_expr(v, inner),
        ExprKind::Yield(inner) => {
            if let Some(i) = inner {
                walk_expr(v, i);
            }
        }
        ExprKind::Closure { params, ret_ty, body, .. } => {
            v.push_scope();
            for p in params {
                if let Some(t) = &p.ty {
                    walk_ty(v, t);
                }
                v.bind(&p.name);
            }
            if let Some(t) = ret_ty {
                walk_ty(v, t);
            }
            walk_expr(v, body);
            v.pop_scope();
        }
        ExprKind::StructInit { path, fields, spread } => {
            walk_path_generics(v, path);
            for (_, f) in fields {
                walk_expr(v, f);
            }
            if let Some(s) = spread {
                walk_expr(v, s);
            }
        }
    }
}

/// Visits a pattern's types and binds its names into the current scope.
pub(crate) fn walk_pat(v: &mut impl AstVisitor, p: &Pattern) {
    match &p.kind {
        PatternKind::Wildcard | PatternKind::Literal(_) | PatternKind::Range { .. } => {}
        PatternKind::Binding { name, sub } => {
            if let Some(s) = sub {
                walk_pat(v, s);
            }
            if name != "_" {
                v.bind(name);
            }
        }
        PatternKind::TypeCheck { binder, ty } => {
            walk_ty(v, ty);
            if let Some(b) = binder {
                v.bind(b);
            }
        }
        PatternKind::Tuple(parts) => {
            for x in parts {
                walk_pat(v, x);
            }
        }
        // Spec 3.11.4: every alternative binds the same names.
        PatternKind::Or(alts) => {
            for x in alts {
                walk_pat(v, x);
            }
        }
        PatternKind::Rest(name) => {
            if let Some(n) = name {
                v.bind(n);
            }
        }
        PatternKind::Struct { path, fields, .. } => {
            walk_path_generics(v, path);
            for fp in fields {
                match &fp.pat {
                    Some(x) => walk_pat(v, x),
                    None => v.bind(&fp.name),
                }
            }
        }
        PatternKind::EnumVariant { path, args } => {
            walk_path_generics(v, path);
            for a in args {
                walk_pat(v, a);
            }
        }
    }
}

pub(crate) fn walk_ty(v: &mut impl AstVisitor, t: &Ty) {
    v.ty(t);
    match &t.kind {
        TyKind::Path(p) => walk_path_generics(v, p),
        TyKind::Sum(parts) | TyKind::Tuple(parts) => {
            for p in parts {
                walk_ty(v, p);
            }
        }
        TyKind::Array(elem, _) => walk_ty(v, elem),
        TyKind::Fn(args, ret) => {
            for a in args {
                walk_ty(v, a);
            }
            walk_ty(v, ret);
        }
        TyKind::Any | TyKind::None | TyKind::SelfUpper => {}
    }
}

/// Names a closure body references but doesn't bind, in first-use
/// order. Includes globals (the caller keeps only outer locals).
pub(crate) fn free_names(params: &[rokc_ast::Param], body: &Expr) -> Vec<String> {
    struct Free {
        scopes: Vec<Vec<String>>,
        out: Vec<String>,
    }
    impl AstVisitor for Free {
        fn expr(&mut self, e: &Expr) {
            let name = match &e.kind {
                ExprKind::Path(p) => match p.segments.as_slice() {
                    [seg] => seg.name.as_str(),
                    _ => return,
                },
                // A method body's closure captures the receiver.
                ExprKind::SelfLower => "self",
                _ => return,
            };
            let bound = self.scopes.iter().any(|s| s.iter().any(|b| b == name));
            if !bound && !self.out.iter().any(|o| o == name) {
                self.out.push(name.to_owned());
            }
        }
        fn bind(&mut self, name: &str) {
            if let Some(s) = self.scopes.last_mut() {
                s.push(name.to_owned());
            }
        }
        fn push_scope(&mut self) {
            self.scopes.push(Vec::new());
        }
        fn pop_scope(&mut self) {
            self.scopes.pop();
        }
    }
    let mut f = Free { scopes: vec![params.iter().map(|p| p.name.clone()).collect()], out: Vec::new() };
    walk_expr(&mut f, body);
    f.out
}

/// Calls `f` on every AST type in `item` (signatures, fields, bodies).
pub(crate) fn for_each_ty(item: &Item, f: &mut dyn FnMut(&Ty)) {
    struct Tys<'f>(&'f mut dyn FnMut(&Ty));
    impl AstVisitor for Tys<'_> {
        fn ty(&mut self, t: &Ty) {
            (self.0)(t);
        }
        fn expr(&mut self, e: &Expr) {
            // `Pair<i32> { ... }` / `Box::<T>` carry type uses on paths.
            let path = match &e.kind {
                ExprKind::StructInit { path, .. } | ExprKind::Path(path) => path,
                _ => return,
            };
            if path.segments.last().is_some_and(|s| !s.generics.is_empty()) {
                (self.0)(&Ty { kind: TyKind::Path(path.clone()), span: path.span });
            }
        }
    }
    walk_item(&mut Tys(f), item);
}

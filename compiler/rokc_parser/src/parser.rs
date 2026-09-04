//! Parser entry point. Recursive descent with Pratt-style operator
//! parsing driven by a `PrecTable`.
//!
//! Only enough of the grammar is implemented here to drive the rest of
//! the pipeline end-to-end on tiny programs (`fn main` returning an int).
//! Each block of the grammar is added incrementally.

use rokc_ast::{
    AccessTail, AttrArg, AttrBody, Attribute, Block, CallArg, CatchArm, ConstExpr, EnumDef,
    EnumVariant, EnumVariantKind, Expr, ExprKind, ExternBlock, ExternItem, FieldPattern, FnDef,
    Generics, ImplDef, ImplItem, Item, Literal, MatchArm, ModDef, NamedField, Param, Path,
    PathSegment, Pattern, PatternKind, Program, Stmt, StmtKind, StructDef, StructKind, ThrowsKind,
    TraitDef, TraitItem, Ty, TyKind, UnionDef,
};
use rokc_core::Visibility;
use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};
use rokc_lexer::{Token, TokenKind};

use crate::prec::{Assoc, Fixity, PrecTable};

/// `rest` of a `let (..)` tuple pattern: splice index + optional name.
type LetTupleRest = (usize, Option<String>);

#[allow(clippy::struct_excessive_bools)] // independent context flags, not a state machine
pub struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    file: String,
    diagnostics: Vec<RokDiagnostic>,
    prec: &'a PrecTable,
    /// Whether `Path { ... }` is a struct initializer at this point. We
    /// disable it inside `if`/`while`/`for` conditions so the trailing
    /// `{` is treated as the body brace, not a struct body.
    struct_expr_allowed: bool,
    /// `|` mid-type expands to sum-type alternation. Inside closure
    /// parameter lists the closing `|` must end the list instead.
    type_sum_allowed: bool,
    /// Remainder of a `>`-prefixed token that was split to close a
    /// generic list (`>>` → `>` + pending `>`, `>=` → `>` + pending `=`,
    /// `>>=` → `>` + pending `>=`). `peek`/`bump` serve it before the
    /// next real token.
    pending: Option<TokenKind>,
    /// Parsing the target type of `expr as T`: a `<` after the type path
    /// only opens generic args when a matching `>` follows (otherwise
    /// `x as i64 < y` is a comparison).
    in_cast_type: bool,
    /// Current expr/type/pattern/block nesting; capped at `MAX_DEPTH`
    /// so hostile input gets a diagnostic instead of a stack overflow.
    depth: u32,
    depth_reported: bool,
    /// Statements queued by a parsing site that emits more than one
    /// statement at a time (currently nested-tuple destructure
    /// `let ((a, b), c) = ...;` — spec 3.15.4). `parse_block` drains
    /// this after every successful `parse_stmt` so the synthesized
    /// follow-up stmts land in the same enclosing scope.
    pending_stmts: Vec<Stmt>,
    /// Counter for generating unique temp names across nested-tuple
    /// destructures within a single parse session.
    next_destructure_temp: u32,
}

/// Nesting limit for expressions, types, patterns and blocks.
const MAX_DEPTH: u32 = 256;
const PARSER_STACK: usize = 128 << 20;

pub fn parse_program(
    tokens: &[Token],
    prec: &PrecTable,
    file: impl Into<String>,
) -> (Program, Vec<RokDiagnostic>) {
    let file = file.into();
    let run = move || {
        let mut p = Parser::new(tokens, prec, file);
        let program = p.parse_program();
        (program, p.diagnostics)
    };
    // Recursive descent: `MAX_DEPTH` levels of debug-build frames need
    // more than a default 2-8 MiB stack, so parse on a dedicated thread
    // whose stack is sized for the cap (address space only until used).
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(PARSER_STACK)
            .spawn_scoped(s, run)
            .expect("spawn parser thread")
            .join()
            .unwrap_or_else(|e| std::panic::resume_unwind(e))
    })
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [Token], prec: &'a PrecTable, file: impl Into<String>) -> Self {
        Self {
            tokens,
            pos: 0,
            file: file.into(),
            diagnostics: Vec::new(),
            prec,
            struct_expr_allowed: true,
            type_sum_allowed: true,
            pending: None,
            in_cast_type: false,
            depth: 0,
            depth_reported: false,
            pending_stmts: Vec::new(),
            next_destructure_temp: 0,
        }
    }

    /// Run `f` with `struct_expr_allowed` set to `allowed`, restoring the
    /// previous value afterwards — also when `f` bails out early with
    /// `None`, so error paths cannot leak the flag.
    fn with_struct_expr<T>(&mut self, allowed: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        let prev = std::mem::replace(&mut self.struct_expr_allowed, allowed);
        let r = f(self);
        self.struct_expr_allowed = prev;
        r
    }

    /// Same as `with_struct_expr` for `type_sum_allowed`.
    fn with_type_sum<T>(&mut self, allowed: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        let prev = std::mem::replace(&mut self.type_sum_allowed, allowed);
        let r = f(self);
        self.type_sum_allowed = prev;
        r
    }

    /// Rebuild an assignment target so that every sub-expression with
    /// possible side effects is evaluated once, into `let` temps pushed
    /// on `temps`. Variables, `self`, literals and field chains on them
    /// stay as written (spec 3.4.3).
    fn hoist_place(&mut self, e: Expr, temps: &mut Vec<Stmt>) -> Expr {
        let span = e.span;
        let kind = match e.kind {
            ExprKind::Path(_)
            | ExprKind::SelfLower
            | ExprKind::SelfUpper
            | ExprKind::Literal(_) => e.kind,
            ExprKind::Field(base, name) => {
                ExprKind::Field(Box::new(self.hoist_place(*base, temps)), name)
            }
            ExprKind::TupleField(base, i) => {
                ExprKind::TupleField(Box::new(self.hoist_place(*base, temps)), i)
            }
            ExprKind::Index(base, idx) => {
                let base = self.hoist_place(*base, temps);
                let idx = self.hoist_place(*idx, temps);
                ExprKind::Index(Box::new(base), Box::new(idx))
            }
            other => {
                let name = self.fresh_destructure_temp();
                temps.push(Stmt {
                    kind: StmtKind::Let {
                        name: name.clone(),
                        ty: None,
                        init: Expr { kind: other, span },
                    },
                    span,
                });
                ExprKind::Path(Path {
                    segments: vec![PathSegment {
                        name,
                        generics: Vec::new(),
                    }],
                    span,
                })
            }
        };
        Expr { kind, span }
    }

    /// Error recovery after a failed item / statement that started at
    /// token `from`: skip to the next synchronisation point instead of
    /// one token, so one mistake yields one diagnostic. Braces opened
    /// since `from` are closed first (parens/brackets are not trusted:
    /// the error is often an unclosed one); then stop after `;`, before an
    /// item (or statement) keyword, or at the enclosing `}` — which is
    /// consumed only at top level, or when it closes the failed item.
    fn recover(&mut self, from: usize, ctx: Recover) {
        self.pending = None;
        let opened: i32 = self.tokens[from.min(self.pos)..self.pos]
            .iter()
            .map(|t| match t.kind {
                TokenKind::LBrace => 1,
                TokenKind::RBrace => -1,
                _ => 0,
            })
            .sum();
        let mut depth = opened.max(0);
        if self.pos == from {
            // Failed on its first token: make progress.
            match self.bump().kind {
                TokenKind::LBrace => depth += 1,
                TokenKind::Semi | TokenKind::RBrace if depth == 0 => return,
                _ => {}
            }
        }
        loop {
            let kind = self.peek();
            match kind {
                TokenKind::Eof => return,
                TokenKind::LBrace => depth += 1,
                TokenKind::RBrace if depth == 0 => {
                    if ctx == Recover::TopItem {
                        self.bump();
                    }
                    return;
                }
                TokenKind::RBrace => {
                    depth -= 1;
                    if depth == 0 && ctx != Recover::Stmt {
                        self.bump();
                        return;
                    }
                }
                TokenKind::Semi if depth == 0 => {
                    self.bump();
                    return;
                }
                _ if depth == 0 && ctx != Recover::Stmt && starts_item(kind) => return,
                _ if depth == 0 && ctx == Recover::Stmt && starts_stmt(kind) => return,
                _ => {}
            }
            self.bump();
        }
    }

    /// Run a recursive production one nesting level deeper, or report
    /// (once) and fail when `MAX_DEPTH` is reached.
    fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> Option<T>) -> Option<T> {
        if self.depth >= MAX_DEPTH {
            if !self.depth_reported {
                self.depth_reported = true;
                let span = self.peek_span();
                self.error(span, format!("nesting too deep (limit {MAX_DEPTH})"));
            }
            return None;
        }
        self.depth += 1;
        let r = f(self);
        self.depth -= 1;
        r
    }

    fn fresh_destructure_temp(&mut self) -> String {
        let n = self.next_destructure_temp;
        self.next_destructure_temp = self.next_destructure_temp.wrapping_add(1);
        format!("__destruct{n}")
    }

    /// Close a generic list: consume a `>`, splitting `>>`, `>=`, `>>=`
    /// and leaving the remainder pending. Emits an error and returns
    /// false when no `>` is present.
    fn expect_closing_gt(&mut self) -> bool {
        let rest = match self.peek() {
            TokenKind::Gt => None,
            TokenKind::Shr => Some(TokenKind::Gt),
            TokenKind::GtEq => Some(TokenKind::Eq),
            TokenKind::ShrEq => Some(TokenKind::GtEq),
            other => {
                let msg = format!("expected `>` to close generic arguments, found {other:?}");
                let span = self.peek_span();
                self.error(span, msg);
                return false;
            }
        };
        self.bump();
        self.pending = rest;
        true
    }

    fn peek(&self) -> &TokenKind {
        if let Some(k) = &self.pending {
            return k;
        }
        self.tokens
            .get(self.pos)
            .map_or(&TokenKind::Eof, |t| &t.kind)
    }

    fn peek_span(&self) -> Span {
        self.tokens.get(self.pos).map_or(Span::DUMMY, |t| t.span)
    }

    fn bump(&mut self) -> Token {
        if let Some(kind) = self.pending.take() {
            // Remainder of a split token; span of the token it came from.
            let span = self
                .tokens
                .get(self.pos.saturating_sub(1))
                .map_or(Span::DUMMY, |t| t.span);
            return Token { kind, span };
        }
        // Past EOF: hand back a synthetic Eof token instead of panicking.
        // Recovery paths can call `bump()` past the last real token while
        // skipping malformed input; previously this indexed out of bounds.
        let Some(t) = self.tokens.get(self.pos).cloned() else {
            return Token {
                kind: TokenKind::Eof,
                span: Span::DUMMY,
            };
        };
        self.pos += 1;
        t
    }

    fn eat(&mut self, kind: &TokenKind) -> bool {
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(kind) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: &TokenKind, what: &str) -> Option<Token> {
        if std::mem::discriminant(self.peek()) == std::mem::discriminant(kind) {
            Some(self.bump())
        } else {
            let span = self.peek_span();
            self.error(span, format!("expected {what}, found {:?}", self.peek()));
            None
        }
    }

    fn unsupported(&mut self, span: Span, msg: impl Into<String>) {
        self.diagnostics.push(
            RokDiagnostic::error(ErrorKind::Unsupported, msg)
                .with_file(self.file.clone())
                .with_span(span, ""),
        );
    }

    fn error(&mut self, span: Span, msg: impl Into<String>) {
        self.diagnostics.push(
            RokDiagnostic::error(ErrorKind::Parse, msg)
                .with_file(self.file.clone())
                .with_span(span, ""),
        );
    }

    pub fn parse_program(&mut self) -> Program {
        let mut items = Vec::new();
        let mut stmts = Vec::new();
        let attrs = self.parse_inner_attrs();
        while !matches!(self.peek(), TokenKind::Eof) {
            let from = self.pos;
            if self.at_item_start() {
                if let Some(item) = self.parse_item() {
                    items.push(item);
                } else {
                    self.recover(from, Recover::TopItem);
                }
            } else if let Some(stmt) = self.parse_top_stmt() {
                stmts.push(stmt);
                while let Some(extra) = self.pending_stmts.pop() {
                    stmts.push(extra);
                }
            } else {
                self.pending_stmts.clear();
                self.recover(from, Recover::Stmt);
            }
        }
        Program {
            attrs,
            items,
            stmts,
        }
    }

    /// Whether the next tokens begin an item rather than a top-level
    /// statement. `unsafe` / `async` start an item only when `fn` follows
    /// (`unsafe { .. }` / `async { .. }` are expressions).
    fn at_item_start(&self) -> bool {
        match self.peek() {
            TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield => matches!(
                self.peek_next(),
                Some(TokenKind::Fn | TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield)
            ),
            k => starts_item(k),
        }
    }

    /// Top-level statement of the entry file (spec 4.16.1:
    /// `top_stmt ::= let_stmt | let_else_stmt | expr ";"`). Block-like
    /// expressions (`if`, `for`, ...) need no `;`; there is no tail
    /// expression and no top-level `return` (4.16.4).
    fn parse_top_stmt(&mut self) -> Option<Stmt> {
        let span = self.peek_span();
        let (stmt, _) = self.parse_stmt()?;
        match stmt.kind {
            StmtKind::Return(_) => {
                self.error(
                    span,
                    "top-level `return` is not allowed (spec 4.16.4); use `env::exit(code)` \
                     or an explicit `fn main() -> i32`",
                );
                None
            }
            StmtKind::Trailing(expr) if !is_block_like(&expr) => {
                self.error(span, "expected `;` after top-level expression");
                None
            }
            StmtKind::Trailing(expr) => Some(Stmt {
                kind: StmtKind::Expr(expr),
                span: stmt.span,
            }),
            _ => Some(stmt),
        }
    }

    fn parse_inner_attrs(&mut self) -> Vec<Attribute> {
        let mut attrs = Vec::new();
        while matches!(self.peek(), TokenKind::HashBangLBracket) {
            if let Some(attr) = self.parse_attr(true) {
                attrs.push(attr);
            }
        }
        attrs
    }

    fn parse_outer_attrs(&mut self) -> Vec<Attribute> {
        let mut attrs = Vec::new();
        while matches!(self.peek(), TokenKind::HashLBracket) {
            if let Some(attr) = self.parse_attr(false) {
                attrs.push(attr);
            }
        }
        attrs
    }

    fn parse_attr(&mut self, inner: bool) -> Option<Attribute> {
        let start = self.peek_span();
        self.bump(); // `#[` or `#![`
        let path = self.parse_attr_path()?;
        let body = self.parse_attr_body();
        self.expect(&TokenKind::RBracket, "`]`");
        Some(Attribute {
            path,
            body,
            inner,
            span: start,
        })
    }

    /// Path inside an attribute body: `name` or `a::b::c`.
    fn parse_attr_path(&mut self) -> Option<Vec<String>> {
        let mut segments = Vec::new();
        loop {
            let name = match self.peek().clone() {
                TokenKind::Ident(n) => n,
                // `any` is a reserved keyword but valid here as a
                // contextual identifier (`#[cfg(any(...))]`).
                TokenKind::Any => "any".to_owned(),
                other => {
                    let s = self.peek_span();
                    self.error(s, format!("attribute name expected, found {other:?}"));
                    return None;
                }
            };
            self.bump();
            segments.push(name);
            if !self.eat(&TokenKind::ColonColon) {
                break;
            }
        }
        Some(segments)
    }

    fn parse_attr_body(&mut self) -> AttrBody {
        match self.peek() {
            TokenKind::LParen => {
                self.bump();
                let mut args = Vec::new();
                while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
                    if let Some(arg) = self.parse_attr_arg() {
                        args.push(arg);
                    } else {
                        // recover until `,` or `)`
                        while !matches!(
                            self.peek(),
                            TokenKind::Comma | TokenKind::RParen | TokenKind::Eof
                        ) {
                            self.bump();
                        }
                    }
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen, "`)`");
                AttrBody::Args(args)
            }
            TokenKind::Eq => {
                self.bump();
                self.parse_attr_literal()
                    .map_or(AttrBody::Empty, AttrBody::Value)
            }
            _ => AttrBody::Empty,
        }
    }

    fn parse_attr_arg(&mut self) -> Option<AttrArg> {
        // `any` is a reserved type-keyword but in attribute args it has
        // contextual meaning (`#[cfg(any(...))]`). Treat it as a Word.
        let ident_name = match self.peek().clone() {
            TokenKind::Ident(n) => Some(n),
            TokenKind::Any => Some("any".to_owned()),
            _ => None,
        };
        if let Some(name) = ident_name {
            // `key = value` form when an identifier is followed by `=`.
            if matches!(self.peek_next(), Some(TokenKind::Eq)) {
                self.bump(); // ident
                self.bump(); // `=`
                let lit = self.parse_attr_literal()?;
                return Some(AttrArg::KeyValue(name, lit));
            }
            if matches!(
                self.peek_next(),
                Some(TokenKind::LParen | TokenKind::ColonColon)
            ) {
                let path = self.parse_attr_path()?;
                let body = self.parse_attr_body();
                return Some(AttrArg::Nested {
                    path,
                    body: Box::new(body),
                });
            }
            // Plain identifier (no `=`, no `(`): treat as a Word arg.
            self.bump();
            return Some(AttrArg::Word(name));
        }
        if let Some(lit) = self.try_parse_attr_literal() {
            return Some(AttrArg::Lit(lit));
        }
        let s = self.peek_span();
        self.error(
            s,
            format!("unexpected token in attribute args: {:?}", self.peek()),
        );
        None
    }

    fn parse_attr_literal(&mut self) -> Option<Literal> {
        self.try_parse_attr_literal().or_else(|| {
            let s = self.peek_span();
            self.error(s, "literal expected");
            None
        })
    }

    fn try_parse_attr_literal(&mut self) -> Option<Literal> {
        // `-1` style negative numeric literals are accepted as a single
        // literal token-pair (Rust attribute compatibility).
        let neg = self.eat(&TokenKind::Minus);
        let lit = match self.peek().clone() {
            TokenKind::IntLit(s) => {
                self.bump();
                Literal::Int(if neg { format!("-{s}") } else { s })
            }
            TokenKind::FloatLit(s) => {
                self.bump();
                Literal::Float(if neg { format!("-{s}") } else { s })
            }
            TokenKind::StrLit(s) => {
                self.bump();
                Literal::Str(s)
            }
            TokenKind::RawStrLit(s) => {
                self.bump();
                Literal::RawStr(s)
            }
            TokenKind::CharLit(s) => {
                self.bump();
                Literal::Char(s)
            }
            TokenKind::CCharLit(s) => {
                self.bump();
                Literal::CChar(s)
            }
            TokenKind::True => {
                self.bump();
                Literal::Bool(true)
            }
            TokenKind::False => {
                self.bump();
                Literal::Bool(false)
            }
            TokenKind::None => {
                self.bump();
                Literal::None
            }
            _ => return None,
        };
        Some(lit)
    }

    fn peek_next(&self) -> Option<TokenKind> {
        self.tokens.get(self.pos + 1).map(|t| t.kind.clone())
    }

    fn parse_item(&mut self) -> Option<Item> {
        let attrs = self.parse_outer_attrs();
        let vis = self.parse_visibility();
        // Spec 6.8: user meta blocks
        //   #[impl_derive(...)] / #[impl_attribute(...)] /
        //   #[impl_derive_attribute(...)]   pub? @derive|@attribute { ... }
        //
        // Stage-1 has no template-token expander, so we recognise the form
        // and reject explicitly. Without this the `@derive` token would
        // surface as a confusing "expected an item" parse error and the
        // attribute would silently bind to nothing.
        let is_meta_attr = attrs.iter().any(|a| {
            matches!(
                a.name(),
                "impl_derive" | "impl_attribute" | "impl_derive_attribute"
            )
        });
        if is_meta_attr {
            return self.skip_meta_block(vis, attrs);
        }
        match self.peek() {
            TokenKind::Fn | TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield => {
                self.parse_fn(vis, attrs).map(Item::Fn)
            }
            TokenKind::Trait => self.parse_trait(vis, attrs).map(Item::Trait),
            TokenKind::Struct => self.parse_struct(vis, attrs).map(Item::Struct),
            TokenKind::Union => self.parse_union(vis, attrs).map(Item::Union),
            TokenKind::Enum => self.parse_enum(vis, attrs).map(Item::Enum),
            TokenKind::Impl => self.parse_impl(vis, attrs).map(Item::Impl),
            TokenKind::Extern => self.parse_extern_block(attrs).map(Item::Extern),
            TokenKind::Mod => self.parse_mod(vis, attrs).map(Item::Mod),
            TokenKind::Use => self.parse_use(vis, attrs).map(Item::Use),
            // Spec 5.2 / variant 663: `const fn name(...) -> R { ... }` —
            // a compile-time-evaluable function. Distinguish from a
            // `const NAME: T = ...;` item by peeking past `const`.
            TokenKind::Const => {
                if matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(TokenKind::Fn)
                ) {
                    self.bump(); // `const`
                    // Stage-1: accept `const fn` as a regular fn. CTE
                    // (compile-time evaluation) lowering is a separate
                    // milestone; the body still runs at runtime.
                    return self.parse_fn(vis, attrs).map(Item::Fn);
                }
                self.parse_const(vis, attrs).map(Item::Const)
            }
            TokenKind::Static => self.parse_static(vis, attrs).map(Item::Static),
            TokenKind::Type => self.parse_type_alias(vis, attrs).map(Item::TypeAlias),
            _ => {
                let span = self.peek_span();
                self.error(span, "expected an item");
                None
            }
        }
    }

    /// Skip the body of a `pub? @derive { ... }` / `@attribute { ... }`
    /// meta block (spec 6.8) and emit a single "not yet implemented"
    /// diagnostic. Recognising the shape here keeps the rest of the
    /// item-parsing loop from reporting a stream of confusing errors.
    fn skip_meta_block(
        &mut self,
        _vis: rokc_core::Visibility,
        _attrs: Vec<Attribute>,
    ) -> Option<Item> {
        let span = self.peek_span();
        self.error(
            span,
            "user meta blocks (#[impl_derive] / #[impl_attribute] / \
             #[impl_derive_attribute]) are not yet implemented \
             (spec 6.8, stage-1 unimpl)",
        );
        // Best-effort: consume `@derive | @attribute` then a balanced { ... }.
        if matches!(self.peek(), TokenKind::At) {
            self.bump();
            if matches!(self.peek(), TokenKind::Ident(_)) {
                self.bump();
            }
        }
        if matches!(self.peek(), TokenKind::LBrace) {
            self.bump();
            let mut depth = 1usize;
            while depth > 0 && !matches!(self.peek(), TokenKind::Eof) {
                match self.peek() {
                    TokenKind::LBrace => {
                        depth += 1;
                        self.bump();
                    }
                    TokenKind::RBrace => {
                        depth -= 1;
                        self.bump();
                    }
                    _ => {
                        self.bump();
                    }
                }
            }
        }
        None
    }

    /// `type NAME[<G>] = ty;`
    fn parse_type_alias(
        &mut self,
        vis: Visibility,
        attrs: Vec<Attribute>,
    ) -> Option<rokc_ast::TypeAliasDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Type, "`type`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "type alias name expected");
            return None;
        };
        let generics = self.parse_generic_params();
        self.expect(&TokenKind::Eq, "`=`")?;
        let ty = self.parse_type()?;
        self.expect(&TokenKind::Semi, "`;`")?;
        Some(rokc_ast::TypeAliasDef {
            vis,
            attrs,
            name,
            generics,
            ty,
            span: start,
        })
    }

    /// `const NAME: T = expr;`
    fn parse_const(
        &mut self,
        vis: Visibility,
        attrs: Vec<Attribute>,
    ) -> Option<rokc_ast::ConstDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Const, "`const`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "const name expected");
            return None;
        };
        self.expect(&TokenKind::Colon, "`:`")?;
        let ty = self.parse_type()?;
        self.expect(&TokenKind::Eq, "`=`")?;
        let value = self.parse_expr()?;
        self.expect(&TokenKind::Semi, "`;`")?;
        Some(rokc_ast::ConstDef {
            vis,
            attrs,
            name,
            ty,
            value,
            span: start,
        })
    }

    /// `static [mut] NAME: T = expr;` — module-level binding.
    /// Currently treated like `const` (the initializer is inlined at
    /// each use). A future stage will give `static` its own `mlir.global`
    /// storage and honour `mut`.
    fn parse_static(
        &mut self,
        vis: Visibility,
        attrs: Vec<Attribute>,
    ) -> Option<rokc_ast::StaticDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Static, "`static`")?;
        let is_mut = self.eat(&TokenKind::Mut);
        // Spec 5.3 / variant 656: `static mut` is permitted only inside
        // an `extern "C" { ... }` block (FFI). The regular item path
        // (this function) is not the FFI path, so reject.
        if is_mut {
            let mut_span = self.peek_span();
            self.error(
                mut_span,
                "`static mut` is only allowed inside `extern \"C\" { ... }` (FFI). \
                 General code should use `Atomic`/`Mutex`/`Cell` (spec 5.3)",
            );
        }
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "static name expected");
            return None;
        };
        self.expect(&TokenKind::Colon, "`:`")?;
        let ty = self.parse_type()?;
        let value = if self.eat(&TokenKind::Eq) {
            Some(self.parse_expr()?)
        } else {
            None
        };
        self.expect(&TokenKind::Semi, "`;`")?;
        Some(rokc_ast::StaticDef {
            vis,
            attrs,
            name,
            ty,
            value,
            is_mut,
            span: start,
        })
    }

    fn parse_struct(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<StructDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Struct, "`struct`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "struct name expected");
            return None;
        };
        let generics = if matches!(self.peek(), TokenKind::Lt) {
            self.parse_generic_params()
        } else {
            Generics::default()
        };

        let kind = match self.peek().clone() {
            TokenKind::Semi => {
                self.bump();
                StructKind::Unit
            }
            TokenKind::LParen => {
                // Tuple struct accepted but not yet lowered past parsing.
                self.bump();
                let mut fields = Vec::new();
                while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
                    let f_attrs = self.parse_outer_attrs();
                    let f_vis = self.parse_visibility();
                    let span = self.peek_span();
                    let ty = self.parse_type()?;
                    fields.push(rokc_ast::TupleField {
                        vis: f_vis,
                        attrs: f_attrs,
                        ty,
                        span,
                    });
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen, "`)`")?;
                self.expect(&TokenKind::Semi, "`;`")?;
                StructKind::Tuple(fields)
            }
            _ => {
                let fields = self.parse_named_fields(true)?;
                StructKind::Named(fields)
            }
        };

        Some(StructDef {
            vis,
            attrs,
            name,
            generics,
            kind,
            span: start,
        })
    }

    /// `union Name<G> { f: T; g: U; }` — fields share storage.
    /// Parsed only at this stage; the layout pass will treat unions as
    /// the largest field's MIR type (future work).
    fn parse_union(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<UnionDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Union, "`union`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "union name expected");
            return None;
        };
        let generics = if matches!(self.peek(), TokenKind::Lt) {
            self.parse_generic_params()
        } else {
            Generics::default()
        };
        let fields = self.parse_named_fields(false)?;
        Some(UnionDef {
            vis,
            attrs,
            name,
            generics,
            fields,
            span: start,
        })
    }

    /// `{ [attrs] [vis] name: T [= default]; ... }` — struct, union and
    /// enum-variant bodies. Defaults only where `allow_default`.
    fn parse_named_fields(&mut self, allow_default: bool) -> Option<Vec<NamedField>> {
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let attrs = self.parse_outer_attrs();
            let vis = self.parse_visibility();
            let span = self.peek_span();
            let TokenKind::Ident(name) = self.peek().clone() else {
                self.error(
                    span,
                    format!("field name expected, found {:?}", self.peek()),
                );
                return None;
            };
            self.bump();
            self.expect(&TokenKind::Colon, "`:`")?;
            let ty = self.parse_type()?;
            let default = if allow_default && self.eat(&TokenKind::Eq) {
                Some(self.parse_expr()?)
            } else {
                None
            };
            fields.push(NamedField {
                vis,
                attrs,
                name,
                ty,
                default,
                span,
            });
            if !self.eat(&TokenKind::Semi) {
                break;
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(fields)
    }

    // Spec 2.4: `enum Name { Variant, Variant(T), Variant { x: T }, ... }`.
    // Current slice only emits unit variants — tuple / named / value
    // variants parse but lower to placeholders.
    // Both inherent and trait impl. For `impl Trait for Type` the
    // trait_path is captured but isn't yet used for trait checking;
    // the methods are registered on the target type directly.
    fn parse_impl(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<ImplDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Impl, "`impl`")?;
        let generics = self.parse_generic_params();
        let first_ty = self.parse_type()?;
        let (trait_path, self_ty) = if self.eat(&TokenKind::For) {
            // `impl TRAIT for SELF` — the first parsed type was the trait.
            let trait_path = match &first_ty.kind {
                TyKind::Path(p) => Some(p.clone()),
                _ => None,
            };
            let self_ty = self.parse_type()?;
            (trait_path, self_ty)
        } else {
            (None, first_ty)
        };
        let where_clause = self.parse_where_clause();
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut items = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let item_attrs = self.parse_outer_attrs();
            let item_vis = self.parse_visibility();
            match self.peek() {
                TokenKind::Fn | TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield => {
                    let from = self.pos;
                    if let Some(f) = self.parse_fn(item_vis, item_attrs) {
                        items.push(ImplItem::Method(f));
                    } else {
                        self.recover(from, Recover::NestedItem);
                    }
                }
                // Spec 2.9.1: `impl_item ::= fn_decl | "type" ident "=" ty ";" | const_decl`.
                // Associated-type concrete binding: `type Output = V;`.
                TokenKind::Type => {
                    let _ = (item_vis, item_attrs);
                    self.bump();
                    let assoc_name = if let TokenKind::Ident(n) = self.peek().clone() {
                        self.bump();
                        n
                    } else {
                        let s = self.peek_span();
                        self.error(s, "associated-type name expected");
                        String::new()
                    };
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let aty = self.parse_type()?;
                    self.expect(&TokenKind::Semi, "`;`")?;
                    items.push(ImplItem::AssocType {
                        name: assoc_name,
                        ty: aty,
                    });
                }
                // ponytail: parsed-but-ignored would be worse than a
                // clear refusal — HIR has no lowering for these yet.
                TokenKind::Const => {
                    let s = self.peek_span();
                    self.unsupported(
                        s,
                        "associated `const` in `impl` (spec 2.9.1) is not yet supported",
                    );
                    let from = self.pos;
                    self.recover(from, Recover::NestedItem);
                }
                _ => {
                    let s = self.peek_span();
                    self.error(s, format!("expected impl item, found {:?}", self.peek()));
                    let from = self.pos;
                    self.recover(from, Recover::NestedItem);
                }
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(ImplDef {
            vis,
            attrs,
            generics,
            trait_path,
            self_ty,
            where_clause,
            items,
            span: start,
        })
    }

    fn parse_enum(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<EnumDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Enum, "`enum`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "enum name expected");
            return None;
        };
        let generics = if matches!(self.peek(), TokenKind::Lt) {
            self.parse_generic_params()
        } else {
            Generics::default()
        };
        self.expect(&TokenKind::LBrace, "`{`")?;

        let mut variants = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let v_attrs = self.parse_outer_attrs();
            let v_span = self.peek_span();
            let v_name = if let TokenKind::Ident(n) = self.peek().clone() {
                self.bump();
                n
            } else {
                let s = self.peek_span();
                self.error(s, "variant name expected");
                return None;
            };
            let kind = match self.peek() {
                TokenKind::LParen => {
                    self.bump();
                    let mut tys = Vec::new();
                    while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
                        if let Some(t) = self.parse_type() {
                            tys.push(t);
                        }
                        if !self.eat(&TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&TokenKind::RParen, "`)`")?;
                    EnumVariantKind::Tuple(tys)
                }
                TokenKind::LBrace => {
                    let fields = self.parse_named_fields(false)?;
                    EnumVariantKind::Named(fields)
                }
                TokenKind::Eq => {
                    self.bump();
                    let value = self.parse_expr()?;
                    EnumVariantKind::Value(value)
                }
                _ => EnumVariantKind::Unit,
            };
            variants.push(EnumVariant {
                attrs: v_attrs,
                name: v_name,
                kind,
                span: v_span,
            });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;

        Some(EnumDef {
            vis,
            attrs,
            name,
            generics,
            variants,
            span: start,
        })
    }

    // `extern "ABI" { fn name(args) -> ret; ... }`. ABI defaults to "C".
    fn parse_extern_block(&mut self, attrs: Vec<Attribute>) -> Option<ExternBlock> {
        let start = self.peek_span();
        self.expect(&TokenKind::Extern, "`extern`")?;
        let abi = match self.peek().clone() {
            TokenKind::StrLit(s) => {
                self.bump();
                s
            }
            _ => "C".to_owned(),
        };
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut items = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let item_attrs = self.parse_outer_attrs();
            let item_vis = self.parse_visibility();
            match self.peek() {
                TokenKind::Fn | TokenKind::Unsafe => {
                    let from = self.pos;
                    if let Some(f) = self.parse_fn(item_vis, item_attrs) {
                        items.push(ExternItem::Fn(f));
                    } else {
                        self.recover(from, Recover::NestedItem);
                    }
                }
                TokenKind::Static => {
                    let s = self.peek_span();
                    self.unsupported(
                        s,
                        "`static` in `extern` blocks (spec 5.3) is not yet supported",
                    );
                    let from = self.pos;
                    self.recover(from, Recover::NestedItem);
                }
                _ => {
                    let s = self.peek_span();
                    self.error(s, format!("expected extern item, found {:?}", self.peek()));
                    let from = self.pos;
                    self.recover(from, Recover::NestedItem);
                }
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(ExternBlock {
            attrs,
            abi,
            items,
            span: start,
        })
    }

    fn parse_mod(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<ModDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Mod, "`mod`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "module name expected");
            return None;
        };
        let items = if matches!(self.peek(), TokenKind::LBrace) {
            self.bump();
            let mut items = Vec::new();
            while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                let from = self.pos;
                if let Some(item) = self.parse_item() {
                    items.push(item);
                } else {
                    self.recover(from, Recover::NestedItem);
                }
            }
            self.expect(&TokenKind::RBrace, "`}`")?;
            Some(items)
        } else {
            self.expect(&TokenKind::Semi, "`;` or `{` after module name")?;
            None
        };
        Some(ModDef {
            vis,
            attrs,
            name,
            items,
            span: start,
        })
    }

    /// `use path[::name | ::* | ::** | ::{ ... } | as alias];`
    fn parse_use(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<rokc_ast::UseDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Use, "`use`")?;
        let tree = self.parse_use_tree()?;
        self.expect(&TokenKind::Semi, "`;`")?;
        Some(rokc_ast::UseDef {
            vis,
            attrs,
            tree,
            span: start,
        })
    }

    fn parse_use_tree(&mut self) -> Option<rokc_ast::UseTree> {
        // Path prefix — every form starts with at least one segment.
        let prefix_start = self.peek_span();
        let mut segments: Vec<PathSegment> = Vec::new();
        loop {
            // Path roots in `use`: bare identifier (absolute), or the
            // contextual roots `pkg::` (package root) and `sup::`
            // (parent module). `self::` is intentionally not a `use`
            // root — same-module children resolve via the lookup-time
            // ancestors walk without an explicit prefix.
            let seg_name = if let TokenKind::Ident(n) = self.peek().clone() {
                self.bump();
                n
            } else {
                let s = self.peek_span();
                self.error(s, "expected an import path");
                return None;
            };
            segments.push(PathSegment {
                name: seg_name,
                generics: Vec::new(),
            });
            if !matches!(self.peek(), TokenKind::ColonColon) {
                break;
            }
            // Lookahead one token — if it's `*`, `{`, or another path
            // segment we commit; otherwise the `::` belongs to the
            // calling context.
            let after_colons = self.peek_next();
            match after_colons {
                Some(TokenKind::Star | TokenKind::LBrace | TokenKind::Ident(_)) => {
                    self.bump(); // consume `::`
                    if matches!(self.peek(), TokenKind::Star | TokenKind::LBrace) {
                        break;
                    }
                }
                _ => break,
            }
        }
        let prefix = Path {
            segments,
            span: prefix_start,
        };
        // Disambiguate the trailing form.
        let kind = match self.peek().clone() {
            TokenKind::Star => {
                self.bump();
                // `**` is two consecutive Stars — the second `*` follows
                // immediately when there's no space.
                if matches!(self.peek(), TokenKind::Star) {
                    self.bump();
                    rokc_ast::UseTreeKind::GlobRecursive
                } else {
                    rokc_ast::UseTreeKind::Glob
                }
            }
            TokenKind::LBrace => {
                self.bump();
                let mut children = Vec::new();
                while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                    let child = self.parse_use_tree()?;
                    children.push(child);
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokenKind::RBrace, "`}`")?;
                rokc_ast::UseTreeKind::Group(children)
            }
            TokenKind::As => {
                self.bump();
                let alias = if let TokenKind::Ident(n) = self.peek().clone() {
                    self.bump();
                    n
                } else {
                    let s = self.peek_span();
                    self.error(s, "alias name expected after `as`");
                    return None;
                };
                rokc_ast::UseTreeKind::Simple(Some(alias))
            }
            _ => rokc_ast::UseTreeKind::Simple(None),
        };
        Some(rokc_ast::UseTree { prefix, kind })
    }

    fn parse_trait(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<TraitDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Trait, "`trait`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "trait name expected");
            return None;
        };
        let generics = self.parse_generic_params();
        let supertraits = if self.eat(&TokenKind::Colon) {
            self.parse_bounds()
        } else {
            Vec::new()
        };
        let where_clause = self.parse_where_clause();
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut items = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let from = self.pos;
            if let Some(item) = self.parse_trait_item() {
                items.push(item);
            } else {
                self.recover(from, Recover::NestedItem);
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(TraitDef {
            vis,
            attrs,
            name,
            generics,
            supertraits,
            items,
            where_clause,
            span: start,
        })
    }

    fn parse_trait_item(&mut self) -> Option<TraitItem> {
        let attrs = self.parse_outer_attrs();
        let vis = self.parse_visibility();
        match self.peek() {
            TokenKind::Fn | TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield => {
                let f = self.parse_fn(vis, attrs)?;
                Some(TraitItem::Method(f))
            }
            TokenKind::Type => {
                self.bump();
                let name = if let TokenKind::Ident(n) = self.peek().clone() {
                    self.bump();
                    n
                } else {
                    let s = self.peek_span();
                    self.error(s, "associated type name expected");
                    return None;
                };
                // Optional bounds (`: A + B`) and default (`= T`) — skip
                // until the terminating `;`.
                while !matches!(self.peek(), TokenKind::Semi | TokenKind::Eof) {
                    self.bump();
                }
                self.expect(&TokenKind::Semi, "`;`")?;
                let _ = attrs;
                Some(TraitItem::AssocType {
                    name,
                    bounds: Vec::new(),
                    default: None,
                })
            }
            _ => {
                let s = self.peek_span();
                self.error(s, format!("expected trait item, found {:?}", self.peek()));
                None
            }
        }
    }

    /// Parse `(elem, elem, ...)` for `let` destructure. Each `elem` is
    /// either an identifier (binding name), `..` / `..ident` (rest), or
    /// a nested `(...)` group (spec 3.15.4). Nested groups are desugared
    /// into a fresh temp binding plus a follow-up `LetTuple` queued on
    /// `pending_stmts`. Caller has already verified `peek() == LParen`.
    fn parse_let_tuple_pattern(
        &mut self,
        outer_span: Span,
    ) -> Option<(Vec<String>, Option<LetTupleRest>)> {
        self.expect(&TokenKind::LParen, "`(`")?;
        let mut names: Vec<String> = Vec::new();
        let mut rest: Option<LetTupleRest> = None;
        while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
            if matches!(self.peek(), TokenKind::DotDot) {
                self.bump();
                if rest.is_some() {
                    let s = self.peek_span();
                    self.error(
                        s,
                        "tuple destructure: only one `..` rest pattern allowed (spec 3.15.3)",
                    );
                    return None;
                }
                let name = match self.peek().clone() {
                    TokenKind::Ident(n) => {
                        self.bump();
                        Some(n)
                    }
                    _ => None,
                };
                rest = Some((names.len(), name));
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
                continue;
            }
            // Nested destructure `((a, b), c)` — recurse into the
            // sub-pattern, allocate a temp, and queue a follow-up
            // `let (sub_names) = __destructN;` so the inner names land
            // in the surrounding scope (spec 3.15.4).
            if matches!(self.peek(), TokenKind::LParen) {
                let inner_span = self.peek_span();
                let (inner_names, inner_rest) = self.parse_let_tuple_pattern(inner_span)?;
                let temp_name = self.fresh_destructure_temp();
                names.push(temp_name.clone());
                let init = Expr {
                    span: inner_span,
                    kind: ExprKind::Path(Path {
                        segments: vec![PathSegment {
                            name: temp_name,
                            generics: Vec::new(),
                        }],
                        span: inner_span,
                    }),
                };
                self.pending_stmts.push(Stmt {
                    kind: StmtKind::LetTuple {
                        names: inner_names,
                        rest: inner_rest,
                        ty: None,
                        init,
                    },
                    span: outer_span,
                });
            } else {
                let n = if let TokenKind::Ident(n) = self.peek().clone() {
                    self.bump();
                    n
                } else {
                    let s = self.peek_span();
                    self.error(s, "binding name expected");
                    return None;
                };
                names.push(n);
            }
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&TokenKind::RParen, "`)`")?;
        Some((names, rest))
    }

    fn parse_visibility(&mut self) -> Visibility {
        if !self.eat(&TokenKind::Pub) {
            return Visibility::Private;
        }
        if !self.eat(&TokenKind::LParen) {
            return Visibility::Pub;
        }
        // `pub(reach)`. Contextual identifier; only valid inside `pub(...)`.
        let v = if let TokenKind::Ident(name) = self.peek().clone() {
            match name.as_str() {
                "pkg" => Visibility::Pkg,
                "sub" => Visibility::Sub,
                _ => {
                    let s = self.peek_span();
                    self.error(s, "expected `pkg` or `sub`");
                    Visibility::Pub
                }
            }
        } else {
            let s = self.peek_span();
            self.error(s, "expected `pkg` or `sub`");
            Visibility::Pub
        };
        self.bump();
        self.expect(&TokenKind::RParen, "`)`");
        v
    }

    fn parse_fn(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<FnDef> {
        let mut is_async = false;
        let mut is_generator = false;
        let start = self.peek_span();
        // Modifiers in fixed order `unsafe async yield` (spec 4.1.11).
        // ponytail: `unsafe` is accepted but not recorded — no
        // unsafe-call check exists yet (spec 4.15).
        self.eat(&TokenKind::Unsafe);
        if matches!(self.peek(), TokenKind::Async) {
            is_async = true;
            self.bump();
        }
        if matches!(self.peek(), TokenKind::Yield) {
            is_generator = true;
            self.bump();
        }
        self.expect(&TokenKind::Fn, "`fn`")?;
        let name = if let TokenKind::Ident(n) = self.peek() {
            n.clone()
        } else {
            let s = self.peek_span();
            self.error(s, "function name expected");
            return None;
        };
        self.bump();
        // Optional generic parameters.
        let generics = if matches!(self.peek(), TokenKind::Lt) {
            self.parse_generic_params()
        } else {
            Generics::default()
        };
        self.expect(&TokenKind::LParen, "`(`")?;
        let mut params = Vec::new();
        while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
            params.push(self.parse_param()?);
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&TokenKind::RParen, "`)`")?;

        let throws = self.parse_throws();
        let ret_ty = if self.eat(&TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let where_clause = self.parse_where_clause();

        let body = if matches!(self.peek(), TokenKind::LBrace) {
            Some(self.parse_block()?)
        } else {
            self.expect(&TokenKind::Semi, "`;` or function body")?;
            None
        };

        Some(FnDef {
            vis,
            attrs,
            name,
            generics,
            params,
            ret_ty,
            body,
            is_async,
            is_generator,
            throws,
            where_clause,
            span: start,
        })
    }

    /// Parse an optional `<T: Bound = Default, const N: usize>` generic
    /// parameter list. Returns empty generics when not at `<`.
    fn parse_generic_params(&mut self) -> Generics {
        let mut params: Vec<rokc_ast::GenericParam> = Vec::new();
        if !self.eat(&TokenKind::Lt) {
            return Generics { params };
        }
        while !matches!(self.peek(), TokenKind::Gt | TokenKind::Eof) {
            if self.eat(&TokenKind::Const) {
                let TokenKind::Ident(name) = self.peek().clone() else {
                    let s = self.peek_span();
                    self.error(s, "const-generic name expected");
                    break;
                };
                self.bump();
                self.expect(&TokenKind::Colon, "`:`");
                if let Some(ty) = self.parse_type() {
                    params.push(rokc_ast::GenericParam::Const { name, ty });
                }
                // Spec 2.10: optional `= const_expr` default (not modelled).
                if self.eat(&TokenKind::Eq) {
                    let _ = self.parse_expr_bp(0);
                }
            } else {
                let TokenKind::Ident(name) = self.peek().clone() else {
                    let s = self.peek_span();
                    self.error(s, "generic param name expected");
                    break;
                };
                self.bump();
                let bounds = if self.eat(&TokenKind::Colon) {
                    self.parse_bounds()
                } else {
                    Vec::new()
                };
                // Spec 2.10.5: optional default `= T2`.
                let default = if self.eat(&TokenKind::Eq) {
                    self.parse_type()
                } else {
                    None
                };
                params.push(rokc_ast::GenericParam::Type {
                    name,
                    bounds,
                    default,
                });
            }
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect_closing_gt();
        Generics { params }
    }

    /// `Bound (+ Bound)*`.
    fn parse_bounds(&mut self) -> Vec<Ty> {
        let mut bounds = Vec::new();
        loop {
            if let Some(t) = self.parse_type() {
                bounds.push(t);
            }
            if !self.eat(&TokenKind::Plus) {
                return bounds;
            }
        }
    }

    /// Optional `where T: A + B, U::Out: C` (spec 2.10.4).
    fn parse_where_clause(&mut self) -> Vec<rokc_ast::WherePred> {
        let mut preds = Vec::new();
        if !self.eat(&TokenKind::Where) {
            return preds;
        }
        while !matches!(
            self.peek(),
            TokenKind::LBrace | TokenKind::Semi | TokenKind::Eof
        ) {
            let Some(ty) = self.parse_type() else { break };
            if self
                .expect(&TokenKind::Colon, "`:` in where clause")
                .is_none()
            {
                break;
            }
            let bounds = self.parse_bounds();
            preds.push(rokc_ast::WherePred { ty, bounds });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        preds
    }

    fn parse_throws(&mut self) -> ThrowsKind {
        if !self.eat(&TokenKind::Throws) {
            return ThrowsKind::None;
        }
        if !self.eat(&TokenKind::LParen) {
            return ThrowsKind::Untyped;
        }
        let mut tys = Vec::new();
        while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
            if let Some(ty) = self.parse_type() {
                tys.push(ty);
            }
            if !self.eat(&TokenKind::Pipe) {
                break;
            }
        }
        self.expect(&TokenKind::RParen, "`)`");
        ThrowsKind::Typed(tys)
    }

    fn parse_param(&mut self) -> Option<Param> {
        let start = self.peek_span();
        let by_ref = self.eat(&TokenKind::Ref);

        // `self` (or `ref self`) is the implicit-`Self` receiver. The
        // `Self` type is filled in later when the method is associated
        // with its containing trait or impl.
        if matches!(self.peek(), TokenKind::SelfLower) {
            self.bump();
            return Some(Param {
                name: "self".to_owned(),
                ty: None,
                by_ref,
                default: None,
                variadic: false,
                span: start,
            });
        }

        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(s, "parameter name expected");
            return None;
        };
        // Spec 4.1 / variant 833: `xs: ...T` variadic — `...` precedes the
        // element type. Stage-1 stores the element type plain and marks
        // the param `variadic`; lowering still needs to wrap the call's
        // trailing args into a Slice<T>, which is a separate milestone.
        let (ty, variadic) = if self.eat(&TokenKind::Colon) {
            if self.eat(&TokenKind::DotDot) && self.eat(&TokenKind::Dot) {
                // `...T` — three dots. Lexed as `..` then `.`.
                let elem = self.parse_type()?;
                (Some(elem), true)
            } else {
                (Some(self.parse_type()?), false)
            }
        } else {
            (None, false)
        };
        let default = if self.eat(&TokenKind::Eq) {
            let value = self.with_struct_expr(true, Self::parse_expr)?;
            Some(value)
        } else {
            None
        };
        Some(Param {
            name,
            ty,
            by_ref,
            default,
            variadic,
            span: start,
        })
    }

    /// Type expression. `|` (sum) binds weakest (spec 2.1.10); it is
    /// disabled inside closure parameter lists and cast targets, where a
    /// bare `|` ends the type.
    fn parse_type(&mut self) -> Option<Ty> {
        let start = self.peek_span();
        let first = self.parse_type_atom()?;
        if !(self.type_sum_allowed && matches!(self.peek(), TokenKind::Pipe)) {
            return Some(first);
        }
        let mut variants = vec![first];
        while self.eat(&TokenKind::Pipe) {
            variants.push(self.parse_type_atom()?);
        }
        Some(Ty {
            kind: TyKind::Sum(variants),
            span: start,
        })
    }

    /// Everything but `|`: paths, `fn(..) -> R`, tuples / grouping,
    /// arrays, `any`, `none`, `Self`.
    fn parse_type_atom(&mut self) -> Option<Ty> {
        self.nested(Self::parse_type_atom_inner)
    }

    fn parse_type_atom_inner(&mut self) -> Option<Ty> {
        let start = self.peek_span();
        let kind = match self.peek().clone() {
            TokenKind::Any => {
                self.bump();
                TyKind::Any
            }
            TokenKind::None => {
                self.bump();
                TyKind::None
            }
            TokenKind::SelfUpper => {
                self.bump();
                TyKind::SelfUpper
            }
            TokenKind::Ident(_) => TyKind::Path(self.parse_type_path()?),
            TokenKind::Fn => {
                self.bump();
                self.expect(&TokenKind::LParen, "`(`")?;
                let args = self.nested_type_list(TokenKind::RParen)?;
                self.expect(&TokenKind::RParen, "`)`")?;
                // `fn(..) -> R` binds tighter than `|` (spec 2.1.10):
                // `fn() -> A | B` is `(fn() -> A) | B`.
                let ret = if self.eat(&TokenKind::Arrow) {
                    self.parse_type_atom()?
                } else {
                    Ty {
                        kind: TyKind::Tuple(Vec::new()),
                        span: start,
                    }
                };
                TyKind::Fn(args, Box::new(ret))
            }
            TokenKind::LParen => {
                // `()` unit, `(T)` grouping, `(T,)` / `(A, B)` tuple
                // (spec 2.1.7).
                self.bump();
                let mut tys = Vec::new();
                let mut trailing_comma = false;
                let ok = self.with_type_sum(true, |p| {
                    let prev_cast = std::mem::replace(&mut p.in_cast_type, false);
                    let mut ok = true;
                    while !matches!(p.peek(), TokenKind::RParen | TokenKind::Eof) {
                        let Some(t) = p.parse_type() else {
                            ok = false;
                            break;
                        };
                        tys.push(t);
                        trailing_comma = p.eat(&TokenKind::Comma);
                        if !trailing_comma {
                            break;
                        }
                    }
                    p.in_cast_type = prev_cast;
                    ok
                });
                if !ok {
                    return None;
                }
                self.expect(&TokenKind::RParen, "`)`")?;
                if tys.len() == 1 && !trailing_comma {
                    return tys.pop();
                }
                TyKind::Tuple(tys)
            }
            // `[T; N]` fixed-size array.
            TokenKind::LBracket => {
                self.bump();
                let elem = self.with_type_sum(true, Self::parse_type)?;
                self.expect(&TokenKind::Semi, "`;`")?;
                // For now: only literal integer length.
                let len = if let TokenKind::IntLit(s) = self.peek().clone() {
                    self.bump();
                    ConstExpr::Literal(Literal::Int(s))
                } else {
                    let s = self.peek_span();
                    self.error(s, "array length literal expected");
                    ConstExpr::Literal(Literal::Int("0".into()))
                };
                self.expect(&TokenKind::RBracket, "`]`")?;
                TyKind::Array(Box::new(elem), len)
            }
            other => {
                self.error(start, format!("type expected, found {other:?}"));
                return None;
            }
        };
        Some(Ty { kind, span: start })
    }

    /// Comma-separated types up to (not including) `close`. Sum types are
    /// allowed inside the brackets even where a bare `|` would end a type.
    fn nested_type_list(&mut self, close: TokenKind) -> Option<Vec<Ty>> {
        self.with_type_sum(true, |p| {
            let prev_cast = std::mem::replace(&mut p.in_cast_type, false);
            let mut tys = Vec::new();
            let mut ok = true;
            while std::mem::discriminant(p.peek()) != std::mem::discriminant(&close)
                && !matches!(
                    p.peek(),
                    TokenKind::Eof | TokenKind::Shr | TokenKind::GtEq | TokenKind::ShrEq
                )
            {
                let Some(t) = p.parse_type() else {
                    ok = false;
                    break;
                };
                tys.push(t);
                if !p.eat(&TokenKind::Comma) {
                    break;
                }
            }
            p.in_cast_type = prev_cast;
            ok.then_some(tys)
        })
    }

    /// Target type of `expr as T`: no bare `|` sum, and `<` only opens
    /// generic args when a matching `>` follows.
    fn parse_cast_type(&mut self) -> Option<Ty> {
        let prev = std::mem::replace(&mut self.in_cast_type, true);
        let ty = self.with_type_sum(false, Self::parse_type);
        self.in_cast_type = prev;
        ty
    }

    /// Lookahead from a `<`: does a matching `>` follow, with only
    /// type-shaped tokens in between?
    fn generic_close_ahead(&self) -> bool {
        let mut angle = 0i32;
        let mut nest = 0i32;
        for t in self.tokens.iter().skip(self.pos) {
            match &t.kind {
                TokenKind::Lt => angle += 1,
                TokenKind::Gt => angle -= 1,
                TokenKind::Shr => angle -= 2,
                TokenKind::LParen | TokenKind::LBracket => nest += 1,
                TokenKind::RParen | TokenKind::RBracket => {
                    nest -= 1;
                    if nest < 0 {
                        return false;
                    }
                }
                TokenKind::Semi if nest > 0 => {}
                TokenKind::Ident(_)
                | TokenKind::ColonColon
                | TokenKind::Comma
                | TokenKind::IntLit(_)
                | TokenKind::Fn
                | TokenKind::Arrow
                | TokenKind::Any
                | TokenKind::None
                | TokenKind::SelfUpper
                | TokenKind::Pipe => {}
                _ => return false,
            }
            if angle <= 0 {
                return nest == 0;
            }
        }
        false
    }

    fn parse_path(&mut self) -> Option<Path> {
        self.parse_path_inner(false)
    }

    fn parse_type_path(&mut self) -> Option<Path> {
        self.parse_path_inner(true)
    }

    fn parse_path_inner(&mut self, allow_generics: bool) -> Option<Path> {
        let start = self.peek_span();
        let mut segments = Vec::new();
        loop {
            let TokenKind::Ident(name) = self.peek().clone() else {
                let s = self.peek_span();
                self.error(s, "path segment expected");
                return None;
            };
            self.bump();
            // `Name<T1, T2>` — generic arguments accepted only when the
            // caller is parsing a type. In expression position the `<`
            // is ambiguous with comparison.
            let mut generics: Vec<Ty> = Vec::new();
            if allow_generics
                && matches!(self.peek(), TokenKind::Lt)
                && (!self.in_cast_type || self.generic_close_ahead())
            {
                self.bump();
                generics = self.nested_type_list(TokenKind::Gt)?;
                if !self.expect_closing_gt() {
                    return None;
                }
            }
            segments.push(PathSegment { name, generics });
            if !self.eat(&TokenKind::ColonColon) {
                break;
            }
        }
        Some(Path {
            segments,
            span: start,
        })
    }

    /// `{ stmts }`. Inside braces a struct literal is always allowed
    /// again, even when the block itself sits in an `if`/`while` head.
    /// Match arm body. `return` / `break` / `continue` / `throw` are
    /// statements, so `none => return 0,` (spec 3.12) wraps one in a block.
    fn parse_arm_body(&mut self) -> Option<Expr> {
        let span = self.peek_span();
        let label = |p: &mut Self| {
            if let TokenKind::Label(name) = p.peek().clone() {
                p.bump();
                Some(name)
            } else {
                None
            }
        };
        let value = |p: &mut Self| {
            if matches!(p.peek(), TokenKind::Comma | TokenKind::RBrace) {
                Some(None)
            } else {
                p.parse_expr().map(Some)
            }
        };
        let kind = match self.peek() {
            TokenKind::Return => {
                self.bump();
                StmtKind::Return(value(self)?)
            }
            TokenKind::Break => {
                self.bump();
                let label = label(self);
                StmtKind::Break {
                    label,
                    value: value(self)?,
                }
            }
            TokenKind::Continue => {
                self.bump();
                StmtKind::Continue { label: label(self) }
            }
            TokenKind::Throw => {
                self.bump();
                StmtKind::Throw(self.parse_expr()?)
            }
            _ => return self.parse_expr(),
        };
        Some(Expr {
            kind: ExprKind::Block(Block {
                stmts: vec![Stmt { kind, span }],
                trailing: None,
                span,
                label: None,
            }),
            span,
        })
    }

    fn parse_block(&mut self) -> Option<Block> {
        self.nested(|p| p.with_struct_expr(true, Self::parse_block_inner))
    }

    fn parse_block_inner(&mut self) -> Option<Block> {
        let start = self.peek_span();
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut stmts = Vec::new();
        let mut trailing: Option<Box<Expr>> = None;
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let from = self.pos;
            if let Some((stmt, is_trailing)) = self.parse_stmt() {
                if is_trailing && matches!(self.peek(), TokenKind::RBrace) {
                    if let StmtKind::Trailing(expr) = stmt.kind {
                        trailing = Some(Box::new(expr));
                    } else {
                        stmts.push(stmt);
                    }
                } else {
                    stmts.push(stmt);
                }
                // Drain follow-up stmts queued by the most recent parse
                // (e.g. nested-tuple destructure: spec 3.15.4 desugars
                // `let ((a, b), c) = …;` to a chain of LetTuple stmts).
                while let Some(extra) = self.pending_stmts.pop() {
                    stmts.push(extra);
                }
            } else {
                self.pending_stmts.clear();
                self.recover(from, Recover::Stmt);
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(Block {
            stmts,
            trailing,
            span: start,
            label: None,
        })
    }

    /// Returns `(stmt, is_trailing_eligible)`. The block-builder decides
    /// whether a trailing expression is actually a trailing value or a
    /// statement.
    #[allow(clippy::cognitive_complexity)] // one arm per statement form
    fn parse_stmt(&mut self) -> Option<(Stmt, bool)> {
        let start = self.peek_span();
        match self.peek() {
            TokenKind::Use => {
                let vis = Visibility::Private;
                let attrs = Vec::new();
                let use_def = self.parse_use(vis, attrs)?;
                Some((
                    Stmt {
                        kind: StmtKind::Item(Item::Use(use_def)),
                        span: start,
                    },
                    false,
                ))
            }
            TokenKind::Let => {
                self.bump();
                // Struct destructure: `let Point { x, y, .. } [: ty] = init;`.
                // Decided purely by syntax: `let Path {` cannot start a
                // plain binding (`let name [: ty] = ...`), so any path
                // followed by `{` is a struct pattern — no capitalisation
                // or pre-scanned type-name table involved.
                if self.peek_path_then_lbrace() {
                    let path = self.parse_path()?;
                    self.expect(&TokenKind::LBrace, "`{`")?;
                    let mut fields: Vec<(String, String)> = Vec::new();
                    let mut rest = false;
                    while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                        if matches!(self.peek(), TokenKind::DotDot) {
                            self.bump();
                            rest = true;
                            break;
                        }
                        let field_name = if let TokenKind::Ident(n) = self.peek().clone() {
                            self.bump();
                            n
                        } else {
                            let s = self.peek_span();
                            self.error(s, "field name expected");
                            return None;
                        };
                        let bind_name = if self.eat(&TokenKind::Colon) {
                            if let TokenKind::Ident(n) = self.peek().clone() {
                                self.bump();
                                n
                            } else {
                                let s = self.peek_span();
                                self.error(s, "rebind name expected");
                                return None;
                            }
                        } else {
                            field_name.clone()
                        };
                        fields.push((field_name, bind_name));
                        if !self.eat(&TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(&TokenKind::RBrace, "`}`")?;
                    let ty = if self.eat(&TokenKind::Colon) {
                        Some(self.parse_type()?)
                    } else {
                        None
                    };
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let init = self.parse_expr()?;
                    self.expect(&TokenKind::Semi, "`;`")?;
                    return Some((
                        Stmt {
                            kind: StmtKind::LetStruct {
                                path,
                                fields,
                                rest,
                                ty,
                                init,
                            },
                            span: start,
                        },
                        false,
                    ));
                }
                // Tuple destructure: `let (a, b) = ...;`. Spec 3.15.4
                // allows nested patterns `let ((a, b), c) = ...;`. We
                // desugar nested groups into a chain of plain LetTuple
                // statements, queuing follow-ups onto `pending_stmts`.
                if matches!(self.peek(), TokenKind::LParen) {
                    let (names, rest) = self.parse_let_tuple_pattern(start)?;
                    let ty = if self.eat(&TokenKind::Colon) {
                        Some(self.parse_type()?)
                    } else {
                        None
                    };
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let init = self.parse_expr()?;
                    self.expect(&TokenKind::Semi, "`;`")?;
                    return Some((
                        Stmt {
                            kind: StmtKind::LetTuple {
                                names,
                                rest,
                                ty,
                                init,
                            },
                            span: start,
                        },
                        false,
                    ));
                }
                let name = if let TokenKind::Ident(n) = self.peek() {
                    n.clone()
                } else {
                    let s = self.peek_span();
                    self.error(s, "binding name expected");
                    return None;
                };
                self.bump();
                let ty = if self.eat(&TokenKind::Colon) {
                    Some(self.parse_type()?)
                } else {
                    None
                };
                self.expect(&TokenKind::Eq, "`=`")?;
                let init = self.parse_expr()?;
                // `let name [: T] = expr else { ... };` — let-else.
                // Desugar to `let name [: T] = match expr { v: T => v, _ => { else_body } };`
                // where the wildcard arm runs the divergent else block.
                if matches!(self.peek(), TokenKind::Else) {
                    self.bump();
                    let else_block = self.parse_block()?;
                    self.expect(&TokenKind::Semi, "`;`")?;
                    let init_span = init.span;
                    let bk_span = else_block.span;
                    let binder = "__letelse_v".to_string();
                    let success_pat = if let Some(t) = &ty {
                        Pattern {
                            kind: PatternKind::TypeCheck {
                                binder: Some(binder.clone()),
                                ty: t.clone(),
                            },
                            span: init_span,
                        }
                    } else {
                        Pattern {
                            kind: PatternKind::Binding {
                                name: binder.clone(),
                                sub: None,
                            },
                            span: init_span,
                        }
                    };
                    let success_body = Expr {
                        kind: ExprKind::Path(Path {
                            segments: vec![PathSegment {
                                name: binder,
                                generics: vec![],
                            }],
                            span: init_span,
                        }),
                        span: init_span,
                    };
                    let else_expr = Expr {
                        kind: ExprKind::Block(else_block),
                        span: bk_span,
                    };
                    let arms = vec![
                        MatchArm {
                            pat: success_pat,
                            guard: None,
                            body: success_body,
                        },
                        MatchArm {
                            pat: Pattern {
                                kind: PatternKind::Wildcard,
                                span: bk_span,
                            },
                            guard: None,
                            body: else_expr,
                        },
                    ];
                    let match_expr = Expr {
                        kind: ExprKind::Match {
                            scrutinee: Box::new(init),
                            arms,
                        },
                        span: init_span,
                    };
                    return Some((
                        Stmt {
                            kind: StmtKind::Let {
                                name,
                                ty,
                                init: match_expr,
                            },
                            span: start,
                        },
                        false,
                    ));
                }
                self.expect(&TokenKind::Semi, "`;`")?;
                Some((
                    Stmt {
                        kind: StmtKind::Let { name, ty, init },
                        span: start,
                    },
                    false,
                ))
            }
            TokenKind::Return => {
                self.bump();
                let value = if matches!(self.peek(), TokenKind::Semi) {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                self.expect(&TokenKind::Semi, "`;`")?;
                Some((
                    Stmt {
                        kind: StmtKind::Return(value),
                        span: start,
                    },
                    false,
                ))
            }
            TokenKind::Break => {
                self.bump();
                // Optional `'label` after `break`.
                let label = if let TokenKind::Label(name) = self.peek().clone() {
                    self.bump();
                    Some(name)
                } else {
                    None
                };
                let value = if matches!(self.peek(), TokenKind::Semi) {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                self.expect(&TokenKind::Semi, "`;`")?;
                Some((
                    Stmt {
                        kind: StmtKind::Break { label, value },
                        span: start,
                    },
                    false,
                ))
            }
            TokenKind::Continue => {
                self.bump();
                let label = if let TokenKind::Label(name) = self.peek().clone() {
                    self.bump();
                    Some(name)
                } else {
                    None
                };
                self.expect(&TokenKind::Semi, "`;`")?;
                Some((
                    Stmt {
                        kind: StmtKind::Continue { label },
                        span: start,
                    },
                    false,
                ))
            }
            TokenKind::Throw => {
                self.bump();
                let value = self.parse_expr()?;
                self.expect(&TokenKind::Semi, "`;`")?;
                Some((
                    Stmt {
                        kind: StmtKind::Throw(value),
                        span: start,
                    },
                    false,
                ))
            }
            _ => {
                let expr = self.parse_expr()?;
                if matches!(self.peek(), TokenKind::Eq) {
                    self.bump();
                    let value = self.parse_expr()?;
                    // Spec 4.6.2's example `|| { count = count + 1 }` writes the
                    // assignment without a trailing `;` in the block. Strict
                    // 3.9.1 demands the `;`; we accept the `;`-less form when
                    // it sits in trailing position (`}` follows) so the spec
                    // example parses while still requiring `;` between
                    // statements in the middle of a block.
                    if matches!(self.peek(), TokenKind::RBrace) {
                        let _ = self.eat(&TokenKind::Semi);
                    } else {
                        self.expect(&TokenKind::Semi, "`;`")?;
                    }
                    return Some((
                        Stmt {
                            kind: StmtKind::Assign(expr, value),
                            span: start,
                        },
                        false,
                    ));
                }
                // Compound assignment `target op= value;` desugars to
                // `target = OpInfix(op, target, value);`. Spec 3.4.3: the
                // target must be evaluated once — index / receiver
                // sub-expressions that are not plain variables or
                // literals are hoisted into temps first:
                // `a[f()] += 1` → `{ let t = f(); a[t] = a[t] + 1; }`.
                if let Some(op) = compound_assign_op(self.peek()) {
                    self.bump();
                    let value = self.parse_expr()?;
                    self.expect(&TokenKind::Semi, "`;`")?;
                    let mut stmts = Vec::new();
                    let target = self.hoist_place(expr, &mut stmts);
                    let span = target.span;
                    let combined = Expr {
                        span,
                        kind: ExprKind::OpInfix {
                            op: op.to_owned(),
                            lhs: Box::new(target.clone()),
                            rhs: Box::new(value),
                        },
                    };
                    let assign = Stmt {
                        kind: StmtKind::Assign(target, combined),
                        span: start,
                    };
                    if stmts.is_empty() {
                        return Some((assign, false));
                    }
                    stmts.push(assign);
                    let block = Block {
                        stmts,
                        trailing: None,
                        span: start,
                        label: None,
                    };
                    return Some((
                        Stmt {
                            kind: StmtKind::Expr(Expr {
                                kind: ExprKind::Block(block),
                                span: start,
                            }),
                            span: start,
                        },
                        false,
                    ));
                }
                if self.eat(&TokenKind::Semi) {
                    Some((
                        Stmt {
                            kind: StmtKind::Expr(expr),
                            span: start,
                        },
                        false,
                    ))
                } else {
                    Some((
                        Stmt {
                            kind: StmtKind::Trailing(expr),
                            span: start,
                        },
                        true,
                    ))
                }
            }
        }
    }

    /// Expression including ranges (spec 3.7): `a..b`, `a..=b`, `..b`,
    /// `a..`, `..`. Ranges bind weakest (prec 0) and do not chain.
    fn parse_expr(&mut self) -> Option<Expr> {
        let span = self.peek_span();
        let start = if matches!(self.peek(), TokenKind::DotDot | TokenKind::DotDotEq) {
            None
        } else {
            Some(Box::new(self.parse_expr_bp(0)?))
        };
        let inclusive = match self.peek() {
            TokenKind::DotDot => false,
            TokenKind::DotDotEq => true,
            _ => return start.map(|e| *e),
        };
        self.bump();
        let end = if !inclusive && !self.can_start_range_end() {
            None
        } else {
            Some(Box::new(self.parse_expr_bp(0)?))
        };
        if matches!(self.peek(), TokenKind::DotDot | TokenKind::DotDotEq) {
            let s = self.peek_span();
            self.error(s, "range operators cannot be chained (spec 3.7.3)");
        }
        Some(Expr {
            span,
            kind: ExprKind::Range {
                start,
                end,
                inclusive,
            },
        })
    }

    /// After `..`: does an end operand follow (vs. `a..` / `..`)?
    fn can_start_range_end(&self) -> bool {
        match self.peek() {
            TokenKind::RParen
            | TokenKind::RBracket
            | TokenKind::RBrace
            | TokenKind::Comma
            | TokenKind::Semi
            | TokenKind::FatArrow
            | TokenKind::Eq
            | TokenKind::Eof => false,
            TokenKind::LBrace => self.struct_expr_allowed,
            _ => true,
        }
    }

    /// Pratt loop. `min_bp` is the minimum binding power that the next
    /// infix/postfix operator must exceed for the loop to consume it.
    fn parse_expr_bp(&mut self, min_bp: u32) -> Option<Expr> {
        self.nested(|p| p.parse_expr_bp_inner(min_bp))
    }

    fn parse_expr_bp_inner(&mut self, min_bp: u32) -> Option<Expr> {
        let mut lhs = if let Some((sym, span)) = self.peek_op_symbol(Fixity::Prefix) {
            let Some(entry) = self.prec.lookup(&sym, Fixity::Prefix).cloned() else {
                self.error(
                    span,
                    format!("prefix operator `{sym}` is not defined (no `#[prefix]` registration)"),
                );
                return None;
            };
            self.bump();
            let rhs = self.parse_expr_bp(entry.prec)?;
            Expr {
                kind: ExprKind::OpPrefix {
                    op: entry.symbol,
                    operand: Box::new(rhs),
                },
                span,
            }
        } else {
            self.parse_primary()?
        };

        // Tracks the precedence of the most recently consumed non-associative
        // op so we can reject chains like `a < b < c` (spec 3.2.5).
        let mut last_none_prec: Option<u32> = None;

        loop {
            // Postfix binds tightest after the primary.
            if let Some((sym, _)) = self.peek_op_symbol(Fixity::Postfix) {
                if let Some(entry) = self.prec.lookup(&sym, Fixity::Postfix).cloned() {
                    if entry.prec >= min_bp {
                        let span = lhs.span;
                        self.bump();
                        lhs = Expr {
                            kind: ExprKind::OpPostfix {
                                op: entry.symbol,
                                operand: Box::new(lhs),
                            },
                            span,
                        };
                        continue;
                    }
                }
            }

            let Some((sym, _)) = self.peek_op_symbol(Fixity::Infix) else {
                break;
            };
            // `??` is a language-level operator, not a stdlib trait dispatch.
            // Hardcode a precedence just below `||` so chains read naturally.
            if sym == "??" {
                let prec_bp = 1u32;
                if prec_bp + 1 < min_bp {
                    break;
                }
                self.bump();
                let rhs = self.parse_expr_bp(prec_bp)?;
                let span = lhs.span;
                lhs = Expr {
                    kind: ExprKind::NullishCoalesce(Box::new(lhs), Box::new(rhs)),
                    span,
                };
                continue;
            }
            let Some(entry) = self.prec.lookup(&sym, Fixity::Infix).cloned() else {
                break;
            };
            let (left_bp, right_bp) = match entry.assoc {
                Assoc::Left | Assoc::None => (entry.prec, entry.prec + 1),
                Assoc::Right => (entry.prec + 1, entry.prec),
            };
            if left_bp < min_bp {
                break;
            }
            // Spec 3.2.5: non-associative ops cannot chain. The Pratt loop
            // already prevents `a < b < c` parsing as `a < (b < c)`, but
            // the *outer* iteration would still consume the second `<`,
            // building `(a < b) < c`. Track the last non-assoc prec we
            // consumed and refuse another op at the same prec.
            if let Some(prev) = last_none_prec {
                if prev == entry.prec {
                    let span = self.peek_span();
                    self.error(
                        span,
                        format!(
                            "non-associative operator `{}` cannot be chained \
                             (parenthesise to disambiguate)",
                            entry.symbol
                        ),
                    );
                }
            }
            self.bump();
            let rhs = self.parse_expr_bp(right_bp)?;
            let span = lhs.span;
            lhs = Expr {
                kind: ExprKind::OpInfix {
                    op: entry.symbol,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
            last_none_prec = matches!(entry.assoc, Assoc::None).then_some(entry.prec);
        }

        Some(lhs)
    }

    /// Peek the current token and convert it to an operator-symbol string
    /// if it is a candidate for the given fixity. Tokens that are also
    /// language syntax (e.g. `|` in lambda parameters, `<` in generic
    /// arguments) are filtered by the caller's context — here we only
    /// expose tokens that have an unambiguous lexical operator meaning.
    fn peek_op_symbol(&self, fixity: Fixity) -> Option<(String, Span)> {
        let tok = self.tokens.get(self.pos)?;
        let sym = match (&tok.kind, fixity) {
            // Infix-only tokens.
            (TokenKind::Plus, Fixity::Infix) => "+".into(),
            (TokenKind::Minus, Fixity::Infix | Fixity::Prefix) => "-".into(),
            (TokenKind::Star, Fixity::Infix) => "*".into(),
            (TokenKind::Slash, Fixity::Infix) => "/".into(),
            (TokenKind::Percent, Fixity::Infix) => "%".into(),
            (TokenKind::PercentPercent, Fixity::Infix) => "%%".into(),
            (TokenKind::DotPercentPercent, Fixity::Infix) => ".%%".into(),
            (TokenKind::DotAmpAmp, Fixity::Infix) => ".&&".into(),
            (TokenKind::DotPipePipe, Fixity::Infix) => ".||".into(),
            (TokenKind::EqEq, Fixity::Infix) => "==".into(),
            (TokenKind::NotEq, Fixity::Infix) => "!=".into(),
            (TokenKind::Lt, Fixity::Infix) => "<".into(),
            (TokenKind::Gt, Fixity::Infix) => ">".into(),
            (TokenKind::LtEq, Fixity::Infix) => "<=".into(),
            (TokenKind::GtEq, Fixity::Infix) => ">=".into(),
            (TokenKind::AmpAmp, Fixity::Infix) => "&&".into(),
            (TokenKind::PipePipe, Fixity::Infix) => "||".into(),
            (TokenKind::QuestionQuestion, Fixity::Infix) => "??".into(),
            (TokenKind::Amp, Fixity::Infix) => "&".into(),
            (TokenKind::Pipe, Fixity::Infix) => "|".into(),
            (TokenKind::Caret, Fixity::Infix) => "^".into(),
            (TokenKind::Shl, Fixity::Infix) => "<<".into(),
            (TokenKind::Shr, Fixity::Infix) => ">>".into(),
            (TokenKind::DotPlus, Fixity::Infix) => ".+".into(),
            (TokenKind::DotMinus, Fixity::Infix) => ".-".into(),
            (TokenKind::DotStar, Fixity::Infix) => ".*".into(),
            (TokenKind::DotSlash, Fixity::Infix) => "./".into(),
            (TokenKind::DotPercent, Fixity::Infix) => ".%".into(),
            (TokenKind::DotEqEq, Fixity::Infix) => ".==".into(),
            (TokenKind::DotNotEq, Fixity::Infix) => ".!=".into(),
            (TokenKind::DotLt, Fixity::Infix) => ".<".into(),
            (TokenKind::DotGt, Fixity::Infix) => ".>".into(),
            (TokenKind::DotLtEq, Fixity::Infix) => ".<=".into(),
            (TokenKind::DotGtEq, Fixity::Infix) => ".>=".into(),
            (TokenKind::DotAmp, Fixity::Infix) => ".&".into(),
            (TokenKind::DotPipe, Fixity::Infix) => ".|".into(),
            (TokenKind::DotCaret, Fixity::Infix) => ".^".into(),
            (TokenKind::DotShl, Fixity::Infix) => ".<<".into(),
            (TokenKind::DotShr, Fixity::Infix) => ".>>".into(),
            // Prefix-only tokens.
            (TokenKind::Bang, Fixity::Prefix) => "!".into(),
            (TokenKind::Tilde, Fixity::Prefix) => "~".into(),
            _ => return None,
        };
        Some((sym, tok.span))
    }

    #[allow(clippy::cognitive_complexity)] // one arm per primary-expression token
    fn parse_primary(&mut self) -> Option<Expr> {
        let start = self.peek_span();
        let kind = match self.peek().clone() {
            // Spec 2.13: `<Type as Trait>::method(...)` fully-qualified
            // path. At the start of a primary, `<` cannot begin a
            // comparison, so it unambiguously opens a UFCS form.
            // Stage-1 lowers it to `Type::method(...)` — the trait
            // qualifier is informational until multi-impl resolution
            // lands.
            TokenKind::Lt => {
                self.bump();
                let ty_path = self.parse_type_path()?;
                self.expect(&TokenKind::As, "`as`")?;
                let _trait_path = self.parse_type_path()?;
                if !self.expect_closing_gt() {
                    return None;
                }
                self.expect(&TokenKind::ColonColon, "`::`")?;
                let method_name = if let TokenKind::Ident(n) = self.peek().clone() {
                    self.bump();
                    n
                } else {
                    let s = self.peek_span();
                    self.error(s, "method name expected after `<T as Trait>::`");
                    return None;
                };
                let mut segments = ty_path.segments;
                segments.push(PathSegment {
                    name: method_name,
                    generics: Vec::new(),
                });
                ExprKind::Path(Path {
                    segments,
                    span: start,
                })
            }
            TokenKind::IntLit(s) => {
                self.bump();
                ExprKind::Literal(Literal::Int(s))
            }
            TokenKind::FloatLit(s) => {
                self.bump();
                ExprKind::Literal(Literal::Float(s))
            }
            TokenKind::StrLit(s) => {
                self.bump();
                ExprKind::Literal(Literal::Str(s))
            }
            TokenKind::RawStrLit(s) => {
                self.bump();
                ExprKind::Literal(Literal::RawStr(s))
            }
            TokenKind::FStrLit(s) => {
                // ponytail: f-strings need Display dispatch + string
                // concatenation, which HIR/runtime don't provide yet.
                self.unsupported(
                    start,
                    "f-string literals (spec 1.7.3) are not yet supported",
                );
                self.bump();
                ExprKind::Literal(Literal::FStr(s))
            }
            TokenKind::Unsafe => {
                // Spec 4.15 `unsafe { ... }`. ponytail: parsed as a plain
                // block — the unsafe-call check (spec 4.15.2) is not
                // implemented, so the marker carries no meaning yet.
                self.bump();
                if !matches!(self.peek(), TokenKind::LBrace) {
                    self.error(start, "expected `{` after `unsafe`");
                    return None;
                }
                ExprKind::Block(self.parse_block()?)
            }
            TokenKind::Using => {
                self.unsupported(
                    start,
                    "`using` expressions (spec 3.17) are not yet supported",
                );
                return None;
            }
            TokenKind::True => {
                self.bump();
                ExprKind::Literal(Literal::Bool(true))
            }
            TokenKind::False => {
                self.bump();
                ExprKind::Literal(Literal::Bool(false))
            }
            TokenKind::None => {
                self.bump();
                ExprKind::Literal(Literal::None)
            }
            TokenKind::CharLit(s) => {
                self.bump();
                ExprKind::Literal(Literal::Char(s))
            }
            TokenKind::CCharLit(s) => {
                self.bump();
                ExprKind::Literal(Literal::CChar(s))
            }
            TokenKind::LParen => {
                self.bump();
                // `()` unit, `(e)` grouping, `(e,)` / `(a, b)` tuple.
                let (mut items, trailing_comma) =
                    self.with_struct_expr(true, |p| p.expr_list(&TokenKind::RParen))?;
                self.expect(&TokenKind::RParen, "`)`")?;
                if items.len() == 1 && !trailing_comma {
                    items.pop()?.kind
                } else {
                    ExprKind::Tuple(items)
                }
            }
            TokenKind::Pipe | TokenKind::PipePipe => self.parse_closure_expr()?,
            TokenKind::LBrace => {
                let block = self.parse_block()?;
                ExprKind::Block(block)
            }
            TokenKind::Label(name) => {
                // `'label: loop`, `'label: while`, `'label: for`,
                // `'label: { ... }`. Parse the labelled construct and
                // attach the label.
                let label_name = name;
                self.bump();
                self.expect(&TokenKind::Colon, "`:` after label")?;
                match self.peek().clone() {
                    TokenKind::Loop => {
                        self.bump();
                        let body = self.parse_block()?;
                        ExprKind::Loop {
                            label: Some(label_name),
                            body,
                        }
                    }
                    TokenKind::While => {
                        self.bump();
                        let cond = self.with_struct_expr(false, Self::parse_expr)?;
                        let body = self.parse_block()?;
                        ExprKind::While {
                            label: Some(label_name),
                            cond: Box::new(cond),
                            body,
                        }
                    }
                    TokenKind::For => {
                        self.bump();
                        let pat = self.parse_pattern()?;
                        self.expect(&TokenKind::In, "`in`")?;
                        let iter = self.with_struct_expr(false, Self::parse_expr)?;
                        let body = self.parse_block()?;
                        ExprKind::For {
                            label: Some(label_name),
                            pat,
                            iter: Box::new(iter),
                            body,
                        }
                    }
                    TokenKind::LBrace => {
                        let mut block = self.parse_block()?;
                        block.label = Some(label_name);
                        ExprKind::Block(block)
                    }
                    _ => {
                        let s = self.peek_span();
                        self.error(s, "expected `loop`, `while`, `for`, or `{` after label");
                        return None;
                    }
                }
            }
            TokenKind::Loop => {
                self.bump();
                let body = self.parse_block()?;
                ExprKind::Loop { label: None, body }
            }
            TokenKind::For => {
                self.bump();
                let pat = self.parse_pattern()?;
                self.expect(&TokenKind::In, "`in`")?;
                let iter = self.with_struct_expr(false, Self::parse_expr)?;
                let body = self.parse_block()?;
                ExprKind::For {
                    label: None,
                    pat,
                    iter: Box::new(iter),
                    body,
                }
            }
            TokenKind::Match => {
                self.bump();
                let scrutinee = self.with_struct_expr(false, Self::parse_expr)?;
                self.expect(&TokenKind::LBrace, "`{`")?;
                let arms = self.with_struct_expr(true, |p| {
                    let mut arms = Vec::new();
                    while !matches!(p.peek(), TokenKind::RBrace | TokenKind::Eof) {
                        let pat = p.parse_pattern()?;
                        let guard = if p.eat(&TokenKind::If) {
                            Some(p.parse_expr()?)
                        } else {
                            None
                        };
                        p.expect(&TokenKind::FatArrow, "`=>`")?;
                        let body = p.parse_arm_body()?;
                        p.eat(&TokenKind::Comma);
                        arms.push(MatchArm { pat, guard, body });
                    }
                    Some(arms)
                })?;
                self.expect(&TokenKind::RBrace, "`}`")?;
                ExprKind::Match {
                    scrutinee: Box::new(scrutinee),
                    arms,
                }
            }
            TokenKind::Try => {
                // `try { body } (catch pat { handler })* (finally { ... })?`
                self.bump();
                let body = self.parse_block()?;
                let mut catches: Vec<CatchArm> = Vec::new();
                while matches!(self.peek(), TokenKind::Catch) {
                    self.bump();
                    let pat = self.with_struct_expr(false, Self::parse_pattern)?;
                    let arm_body = self.parse_block()?;
                    catches.push(CatchArm {
                        pat,
                        body: arm_body,
                    });
                }
                let finally = if matches!(self.peek(), TokenKind::Finally) {
                    self.bump();
                    Some(self.parse_block()?)
                } else {
                    None
                };
                ExprKind::Try {
                    body,
                    catches,
                    finally,
                }
            }
            TokenKind::While => {
                self.bump();
                // `while let pat = expr { body }` desugars to
                // `loop { match expr { pat => body, _ => break } }`.
                if self.eat(&TokenKind::Let) {
                    let pat = self.parse_pattern()?;
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let scrutinee = self.with_struct_expr(false, Self::parse_expr)?;
                    let body_block = self.parse_block()?;
                    let body_span = body_block.span;
                    let then_body = Expr {
                        span: body_span,
                        kind: ExprKind::Block(body_block),
                    };
                    let break_expr = Expr {
                        span: start,
                        kind: ExprKind::Tuple(Vec::new()),
                    };
                    let break_block = Block {
                        stmts: vec![Stmt {
                            kind: StmtKind::Break {
                                label: None,
                                value: None,
                            },
                            span: start,
                        }],
                        trailing: None,
                        span: start,
                        label: None,
                    };
                    let break_arm_body = Expr {
                        span: start,
                        kind: ExprKind::Block(break_block),
                    };
                    let _ = break_expr;
                    let wildcard = Pattern {
                        kind: PatternKind::Wildcard,
                        span: start,
                    };
                    let match_expr = Expr {
                        span: start,
                        kind: ExprKind::Match {
                            scrutinee: Box::new(scrutinee),
                            arms: vec![
                                MatchArm {
                                    pat,
                                    guard: None,
                                    body: then_body,
                                },
                                MatchArm {
                                    pat: wildcard,
                                    guard: None,
                                    body: break_arm_body,
                                },
                            ],
                        },
                    };
                    let loop_body = Block {
                        stmts: vec![Stmt {
                            kind: StmtKind::Expr(match_expr),
                            span: start,
                        }],
                        trailing: None,
                        span: start,
                        label: None,
                    };
                    ExprKind::Loop {
                        label: None,
                        body: loop_body,
                    }
                } else {
                    let cond = self.with_struct_expr(false, Self::parse_expr)?;
                    let body = self.parse_block()?;
                    ExprKind::While {
                        label: None,
                        cond: Box::new(cond),
                        body,
                    }
                }
            }
            TokenKind::If => {
                self.bump();
                // `if let pat = expr block else?` desugars to a `match`
                // with the pattern's arm and a wildcard fallback.
                if self.eat(&TokenKind::Let) {
                    let pat = self.parse_pattern()?;
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let scrutinee = self.with_struct_expr(false, Self::parse_expr)?;
                    let then_block = self.parse_block()?;
                    let then_span = then_block.span;
                    let then_body = Expr {
                        span: then_span,
                        kind: ExprKind::Block(then_block),
                    };
                    let else_body = if self.eat(&TokenKind::Else) {
                        if matches!(self.peek(), TokenKind::If) {
                            self.parse_primary()?
                        } else {
                            let block = self.parse_block()?;
                            let s = block.span;
                            Expr {
                                span: s,
                                kind: ExprKind::Block(block),
                            }
                        }
                    } else {
                        Expr {
                            span: start,
                            kind: ExprKind::Tuple(Vec::new()),
                        }
                    };
                    let wildcard = Pattern {
                        kind: PatternKind::Wildcard,
                        span: start,
                    };
                    ExprKind::Match {
                        scrutinee: Box::new(scrutinee),
                        arms: vec![
                            MatchArm {
                                pat,
                                guard: None,
                                body: then_body,
                            },
                            MatchArm {
                                pat: wildcard,
                                guard: None,
                                body: else_body,
                            },
                        ],
                    }
                } else {
                    let cond = self.with_struct_expr(false, Self::parse_expr)?;
                    let then_branch = self.parse_block()?;
                    let else_branch = if self.eat(&TokenKind::Else) {
                        if matches!(self.peek(), TokenKind::If) {
                            // Chained `else if`: recurse into another primary.
                            Some(Box::new(self.parse_primary()?))
                        } else {
                            let block = self.parse_block()?;
                            let span = block.span;
                            Some(Box::new(Expr {
                                span,
                                kind: ExprKind::Block(block),
                            }))
                        }
                    } else {
                        None
                    };
                    ExprKind::If {
                        cond: Box::new(cond),
                        then_branch,
                        else_branch,
                    }
                }
            }
            TokenKind::Ident(_) => {
                let mut path = self.parse_path()?;
                // Spec 2.10: explicit generic instantiation in struct
                // literal — `Pair<i32, i32> { a: 5, b: 7 }`. The `<` at
                // expression position is normally a comparison, so we
                // only accept generics when a balanced `>` is followed
                // by `{` or `(` (turbofish-style heuristic). The args
                // attach to the last path segment.
                if matches!(self.peek(), TokenKind::Lt) && self.peek_struct_or_call_after_generics()
                {
                    self.bump(); // `<`
                    let generics = self.nested_type_list(TokenKind::Gt)?;
                    if !self.expect_closing_gt() {
                        return None;
                    }
                    if let Some(last) = path.segments.last_mut() {
                        last.generics = generics;
                    }
                }
                if self.struct_expr_allowed && matches!(self.peek(), TokenKind::LBrace) {
                    // Spec 2.3 vs 4.8.1: `Path { ... }` is either a struct
                    // init (`Point { x: 1 }`) or a 0-arg trailing closure
                    // (`run { body }`). We disambiguate with lookahead at
                    // the body's first token:
                    //   `}`                     → empty struct init
                    //   `..rest`                → struct init (rest)
                    //   `ident ":"|","|"}"`     → struct init / shorthand
                    //   anything else           → 0-arg trailing closure
                    if self.peek_struct_init_body() {
                        self.parse_struct_init_body(path)?
                    } else {
                        // `path { body }` → call with 0-arg trailing closure.
                        let body_span = self.peek_span();
                        let block = self.parse_block()?;
                        let body = Expr {
                            span: body_span,
                            kind: ExprKind::Block(block),
                        };
                        let closure = Expr {
                            span: body_span,
                            kind: ExprKind::Closure {
                                captures: Vec::new(),
                                params: Vec::new(),
                                ret_ty: None,
                                body: Box::new(body),
                                is_async: false,
                                is_generator: false,
                            },
                        };
                        let path_span = start;
                        ExprKind::Call {
                            callee: Box::new(Expr {
                                span: path_span,
                                kind: ExprKind::Path(path),
                            }),
                            args: Vec::new(),
                            trailing_closure: Some(Box::new(closure)),
                        }
                    }
                } else {
                    ExprKind::Path(path)
                }
            }
            TokenKind::SelfLower => {
                self.bump();
                ExprKind::SelfLower
            }
            TokenKind::SelfUpper => {
                self.bump();
                ExprKind::SelfUpper
            }
            // `[a, b, c]` array literal — OR closure capture-list
            // `[ref x, ref y] || ...` (spec 4.6.2). We disambiguate by
            // lookahead: a `ref` keyword inside `[...]` is unambiguous —
            // arrays of variables don't take `ref`, capture lists do.
            TokenKind::LBracket
                if matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(TokenKind::Ref)
                ) =>
            {
                self.bump(); // `[`
                let mut captures: Vec<rokc_ast::CaptureSpec> = Vec::new();
                while !matches!(self.peek(), TokenKind::RBracket | TokenKind::Eof) {
                    if self.eat(&TokenKind::Ref) {
                        let name = if let TokenKind::Ident(n) = self.peek().clone() {
                            self.bump();
                            n
                        } else {
                            let s = self.peek_span();
                            self.error(s, "capture name expected after `ref`");
                            return None;
                        };
                        captures.push(rokc_ast::CaptureSpec::Ref(name));
                    } else if let TokenKind::Ident(n) = self.peek().clone() {
                        self.bump();
                        captures.push(rokc_ast::CaptureSpec::Value(n));
                    } else {
                        let s = self.peek_span();
                        self.error(s, "capture-list item expected");
                        return None;
                    }
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                self.expect(&TokenKind::RBracket, "`]`")?;
                if !matches!(self.peek(), TokenKind::Pipe | TokenKind::PipePipe) {
                    let s = self.peek_span();
                    self.error(s, "`|` or `||` expected after capture list");
                    return None;
                }
                let mut closure_kind = self.parse_closure_expr()?;
                if let ExprKind::Closure { captures: c, .. } = &mut closure_kind {
                    *c = captures;
                }
                closure_kind
            }
            TokenKind::LBracket => {
                self.bump();
                let (items, _) =
                    self.with_struct_expr(true, |p| p.expr_list(&TokenKind::RBracket))?;
                self.expect(&TokenKind::RBracket, "`]`")?;
                ExprKind::List(items)
            }
            TokenKind::Await => {
                // Spec 4.12: `await expr` extracts the result of a Future.
                // Stage-1 has no scheduler/Future story, so HIR lowers
                // this as passthrough — the parsed AST keeps `Await` so
                // the future scheduler implementation has a hook.
                self.bump();
                let inner = self.parse_expr_bp(0)?;
                ExprKind::Await(Box::new(inner))
            }
            TokenKind::Yield => {
                // Spec 4.11: `yield N` inside a generator function. The
                // parser accepts the form so generator bodies tokenise
                // cleanly; HIR emits an explicit refusal until the
                // coroutine runtime lands (no nullptr stub miscompile).
                self.bump();
                let value = if matches!(
                    self.peek(),
                    TokenKind::Semi | TokenKind::RBrace | TokenKind::Comma | TokenKind::RParen
                ) {
                    None
                } else {
                    Some(Box::new(self.parse_expr_bp(0)?))
                };
                ExprKind::Yield(value)
            }
            other => {
                self.error(start, format!("expression expected, found {other:?}"));
                return None;
            }
        };
        let mut expr = Expr { kind, span: start };

        // Postfix chain: `(...)`, `.field`, `.method(...)`. Indexing and
        // optional-chaining come later.
        loop {
            match self.peek() {
                TokenKind::LParen => {
                    self.bump();
                    let args = self.parse_call_args()?;
                    self.expect(&TokenKind::RParen, "`)`")?;
                    // Spec 4.8: trailing closure after a call. A `{` or
                    // closure-shape (`||` / `|x|`) immediately after the
                    // closing `)` attaches as the call's last argument.
                    let trailing_closure = self.try_parse_trailing_closure()?;
                    expr = Expr {
                        span: expr.span,
                        kind: ExprKind::Call {
                            callee: Box::new(expr),
                            args,
                            trailing_closure,
                        },
                    };
                }
                TokenKind::Dot => {
                    self.bump();
                    let name = match self.peek().clone() {
                        TokenKind::Ident(n) => {
                            self.bump();
                            n
                        }
                        TokenKind::IntLit(s) | TokenKind::FloatLit(s) => {
                            // Tuple field: `expr.0`, `expr.1`, ... A float
                            // token `0.1` in `t.0.1` is two accesses.
                            let span = self.peek_span();
                            self.bump();
                            for part in s.split('.') {
                                let idx = self.tuple_index(part, span)?;
                                expr = Expr {
                                    span: expr.span,
                                    kind: ExprKind::TupleField(Box::new(expr), idx),
                                };
                            }
                            continue;
                        }
                        _ => {
                            let s = self.peek_span();
                            self.error(s, "field or method name expected after `.`");
                            return None;
                        }
                    };
                    if matches!(self.peek(), TokenKind::LParen) {
                        self.bump();
                        let args = self.parse_call_args()?;
                        self.expect(&TokenKind::RParen, "`)`")?;
                        // Spec 4.8: trailing closure on a method call —
                        // `v.apply() |x| { x*2 }` / `v.apply() { body }`.
                        // Same disambig as Call: `{` only consumed when
                        // `struct_expr_allowed`, `|`/`||` always consumed.
                        let trailing_closure = self.try_parse_trailing_closure()?;
                        expr = Expr {
                            span: expr.span,
                            kind: ExprKind::MethodCall {
                                receiver: Box::new(expr),
                                method: name,
                                type_args: Vec::new(),
                                args,
                                trailing_closure,
                            },
                        };
                    } else {
                        expr = Expr {
                            span: expr.span,
                            kind: ExprKind::Field(Box::new(expr), name),
                        };
                    }
                }
                TokenKind::LBracket => {
                    self.bump();
                    let (indices, _) =
                        self.with_struct_expr(true, |p| p.expr_list(&TokenKind::RBracket))?;
                    if indices.is_empty() {
                        let s = self.peek_span();
                        self.error(s, "index expression expected");
                    }
                    self.expect(&TokenKind::RBracket, "`]`")?;
                    // Spec 3.6.1: `m[i, j]` lowers to `m[i][j]`. Until
                    // `Index<(I, J)>` trait dispatch lands the sugar maps
                    // straight to chained primitive indexing — which is
                    // the right semantic for fixed-size 2D arrays.
                    let span = expr.span;
                    for idx in indices {
                        expr = Expr {
                            span,
                            kind: ExprKind::Index(Box::new(expr), Box::new(idx)),
                        };
                    }
                }
                TokenKind::As => {
                    self.bump();
                    let ty = self.parse_cast_type()?;
                    expr = Expr {
                        span: expr.span,
                        kind: ExprKind::Cast(Box::new(expr), ty),
                    };
                }
                TokenKind::Question => {
                    self.bump();
                    expr = Expr {
                        span: expr.span,
                        kind: ExprKind::TryQ(Box::new(expr)),
                    };
                }
                TokenKind::QuestionDot => {
                    self.bump();
                    let name = match self.peek().clone() {
                        TokenKind::Ident(n) => {
                            self.bump();
                            n
                        }
                        TokenKind::IntLit(s) => {
                            let span = self.peek_span();
                            self.bump();
                            let idx = self.tuple_index(&s, span)?;
                            expr = Expr {
                                span: expr.span,
                                kind: ExprKind::QuestionDot(
                                    Box::new(expr),
                                    AccessTail::TupleField(idx),
                                ),
                            };
                            continue;
                        }
                        _ => {
                            let s = self.peek_span();
                            self.error(s, "field or method name expected after `?.`");
                            return None;
                        }
                    };
                    let tail = if matches!(self.peek(), TokenKind::LParen) {
                        self.bump();
                        let args = self.parse_call_args()?;
                        self.expect(&TokenKind::RParen, "`)`")?;
                        AccessTail::Method {
                            method: name,
                            type_args: Vec::new(),
                            args,
                        }
                    } else {
                        AccessTail::Field(name)
                    };
                    expr = Expr {
                        span: expr.span,
                        kind: ExprKind::QuestionDot(Box::new(expr), tail),
                    };
                }
                _ => break,
            }
        }
        Some(expr)
    }

    /// Tuple field index after `.`: plain decimal digits only — no
    /// suffix, radix prefix, `_` or leading zero (`t.1u8`, `t.0x1` are
    /// errors, not `t.0`).
    fn tuple_index(&mut self, text: &str, span: Span) -> Option<u32> {
        let plain = !text.is_empty()
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text == "0" || !text.starts_with('0'));
        match text.parse::<u32>() {
            Ok(i) if plain => Some(i),
            _ => {
                self.error(span, format!("invalid tuple field index `{text}`"));
                None
            }
        }
    }

    /// `e, e, ...` up to (not consuming) `close`. Returns the items and
    /// whether the list ended with a trailing comma.
    fn expr_list(&mut self, close: &TokenKind) -> Option<(Vec<Expr>, bool)> {
        let mut items = Vec::new();
        let mut trailing_comma = false;
        while std::mem::discriminant(self.peek()) != std::mem::discriminant(close)
            && !matches!(self.peek(), TokenKind::Eof)
        {
            items.push(self.parse_expr()?);
            trailing_comma = self.eat(&TokenKind::Comma);
            if !trailing_comma {
                break;
            }
        }
        Some((items, trailing_comma))
    }

    /// Spec 4.8: trailing closure attached to a call. A `||`, `|...|`, or
    /// `{ ... }` immediately after the closing `)` of the call becomes
    /// the last argument. Returns `None` when no trailing closure is
    /// present.
    ///
    /// `{ ... }` is gated on `self.struct_expr_allowed`: inside a
    /// control-flow head (`if`, `while`, `for`, `match` condition) the
    /// brace is reserved for the construct body, not a 0-arg closure.
    /// The flag is reused (not duplicated) because both situations share
    /// the same disambiguation question.
    #[allow(clippy::option_option)] // outer None = parse error (for `?`), inner None = no closure
    fn try_parse_trailing_closure(&mut self) -> Option<Option<Box<Expr>>> {
        match self.peek() {
            TokenKind::LBrace if self.struct_expr_allowed => {
                let span = self.peek_span();
                let block = self.parse_block()?;
                let body = Expr {
                    span,
                    kind: ExprKind::Block(block),
                };
                let closure = Expr {
                    span,
                    kind: ExprKind::Closure {
                        captures: Vec::new(),
                        params: Vec::new(),
                        ret_ty: None,
                        body: Box::new(body),
                        is_async: false,
                        is_generator: false,
                    },
                };
                Some(Some(Box::new(closure)))
            }
            TokenKind::PipePipe | TokenKind::Pipe => {
                let span = self.peek_span();
                let kind = self.parse_closure_expr()?;
                Some(Some(Box::new(Expr { span, kind })))
            }
            _ => Some(None),
        }
    }

    /// Parse `|args| body` or `|args| -> R body` (or `|| body`).
    /// Captures aren't supported yet — the body must reference only its
    /// parameters or globally visible items.
    fn parse_closure_expr(&mut self) -> Option<ExprKind> {
        let mut params: Vec<Param> = Vec::new();
        if self.eat(&TokenKind::PipePipe) {
            // Empty param list `||`.
        } else {
            self.expect(&TokenKind::Pipe, "`|`")?;
            params = self.with_type_sum(false, |p| {
                let mut params = Vec::new();
                while !matches!(p.peek(), TokenKind::Pipe | TokenKind::Eof) {
                    params.push(p.parse_param()?);
                    if !p.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                Some(params)
            })?;
            self.expect(&TokenKind::Pipe, "`|`")?;
        }
        let ret_ty = if self.eat(&TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let body = self.parse_expr()?;
        Some(ExprKind::Closure {
            captures: Vec::new(),
            params,
            ret_ty,
            body: Box::new(body),
            is_async: false,
            is_generator: false,
        })
    }

    /// Parse `{ field: expr, ..., ..base? }` after a leading path. The
    /// caller already has the path; we consume from the opening `{`.
    /// Disambiguate `Path { ... }`: struct init vs 0-arg trailing closure.
    /// Looks two tokens past the `{` without consuming.
    ///   `{ }`              → struct init (empty/unit)
    ///   `{ .. }`           → struct init (rest)
    ///   `{ ident : ... }`  → struct init (named field)
    ///   `{ ident , ... }`  → struct init (shorthand)
    ///   `{ ident } `       → struct init (single shorthand)
    ///   anything else      → trailing closure body
    /// Heuristic for `Path<...>` in expression position. Walks forward
    /// from the `<` token, balancing nested angle brackets. Returns
    /// true when a matched `>` is followed by `{` or `(` — the only
    /// shapes for an explicit generic instantiation that immediately
    /// constructs (struct init) or calls (turbofish). Stops scanning
    /// at tokens that can't appear inside a generic-arg list (block
    /// braces, semicolons, etc.) to keep the lookahead short and
    /// rule out comparisons.
    fn peek_struct_or_call_after_generics(&self) -> bool {
        // Caller has already confirmed `peek() == Lt`.
        let mut depth: i32 = 0;
        let mut i = self.pos;
        let max = i.saturating_add(64).min(self.tokens.len());
        while i < max {
            let kind = match self.tokens.get(i) {
                Some(t) => &t.kind,
                None => return false,
            };
            match kind {
                TokenKind::Lt => depth += 1,
                TokenKind::Shl => depth += 2,
                TokenKind::Gt => {
                    depth -= 1;
                    if depth == 0 {
                        let next = self.tokens.get(i + 1).map(|t| &t.kind);
                        return matches!(next, Some(TokenKind::LBrace | TokenKind::LParen));
                    }
                }
                TokenKind::Shr => {
                    depth -= 2;
                    if depth <= 0 {
                        let next = self.tokens.get(i + 1).map(|t| &t.kind);
                        return matches!(next, Some(TokenKind::LBrace | TokenKind::LParen));
                    }
                }
                // Tokens that may appear inside a generic-arg type list.
                TokenKind::Ident(_)
                | TokenKind::Comma
                | TokenKind::ColonColon
                | TokenKind::Amp
                | TokenKind::Star
                | TokenKind::LBracket
                | TokenKind::RBracket
                | TokenKind::LParen
                | TokenKind::RParen
                | TokenKind::Semi
                | TokenKind::IntLit(_) => {}
                _ => return false,
            }
            i += 1;
        }
        false
    }

    /// `Ident (:: Ident)* {` lookahead (no tokens consumed).
    fn peek_path_then_lbrace(&self) -> bool {
        let mut i = self.pos;
        loop {
            if !matches!(
                self.tokens.get(i).map(|t| &t.kind),
                Some(TokenKind::Ident(_))
            ) {
                return false;
            }
            match self.tokens.get(i + 1).map(|t| &t.kind) {
                Some(TokenKind::ColonColon) => i += 2,
                Some(TokenKind::LBrace) => return true,
                _ => return false,
            }
        }
    }

    fn peek_struct_init_body(&self) -> bool {
        // Caller has just confirmed `peek() == LBrace`.
        let after_brace = self.tokens.get(self.pos + 1).map(|t| &t.kind);
        match after_brace {
            Some(TokenKind::RBrace | TokenKind::DotDot) => true,
            Some(TokenKind::Ident(_)) => {
                let third = self.tokens.get(self.pos + 2).map(|t| &t.kind);
                matches!(
                    third,
                    Some(TokenKind::Colon | TokenKind::Comma | TokenKind::RBrace)
                )
            }
            _ => false,
        }
    }

    fn parse_struct_init_body(&mut self, path: Path) -> Option<ExprKind> {
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut fields = Vec::new();
        let mut spread: Option<Box<Expr>> = None;
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            if self.eat(&TokenKind::DotDot) {
                let base = self.with_struct_expr(true, Self::parse_expr)?;
                spread = Some(Box::new(base));
                break;
            }
            let name = if let TokenKind::Ident(n) = self.peek().clone() {
                self.bump();
                n
            } else {
                let s = self.peek_span();
                self.error(s, "field name expected");
                return None;
            };
            // Shorthand `Foo { x }` (using a local named `x`) is allowed
            // when the next token is not `:`.
            let value = if self.eat(&TokenKind::Colon) {
                self.with_struct_expr(true, Self::parse_expr)?
            } else {
                Expr {
                    span: self.peek_span(),
                    kind: ExprKind::Path(Path {
                        segments: vec![PathSegment {
                            name: name.clone(),
                            generics: Vec::new(),
                        }],
                        span: self.peek_span(),
                    }),
                }
            };
            fields.push((name, value));
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(ExprKind::StructInit {
            path,
            fields,
            spread,
        })
    }

    /// If a literal pattern is followed by `..` or `..=`, extend it into
    /// a range pattern. The end is optional: `0..` is open-ended.
    fn maybe_extend_range(&mut self, span: Span, start: Literal) -> Pattern {
        let inclusive = match self.peek() {
            TokenKind::DotDotEq => true,
            TokenKind::DotDot => false,
            _ => {
                return Pattern {
                    kind: PatternKind::Literal(start),
                    span,
                };
            }
        };
        self.bump();
        let end = match self.peek().clone() {
            TokenKind::IntLit(s) => {
                self.bump();
                Some(Literal::Int(s))
            }
            TokenKind::FloatLit(s) => {
                self.bump();
                Some(Literal::Float(s))
            }
            TokenKind::Minus => {
                self.bump();
                match self.peek().clone() {
                    TokenKind::IntLit(s) => {
                        self.bump();
                        Some(Literal::Int(format!("-{s}")))
                    }
                    TokenKind::FloatLit(s) => {
                        self.bump();
                        Some(Literal::Float(format!("-{s}")))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        Pattern {
            kind: PatternKind::Range {
                start: Some(start),
                end,
                inclusive,
            },
            span,
        }
    }

    fn parse_struct_pattern_body(&mut self, path: Path) -> Option<PatternKind> {
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut fields = Vec::new();
        let mut rest = false;
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            if self.eat(&TokenKind::DotDot) {
                rest = true;
                break;
            }
            let name = if let TokenKind::Ident(n) = self.peek().clone() {
                self.bump();
                n
            } else {
                let s = self.peek_span();
                self.error(s, "field name expected");
                return None;
            };
            // `Foo { x: pat }` or shorthand `Foo { x }` (binds `x`).
            let pat = if self.eat(&TokenKind::Colon) {
                Some(self.parse_pattern()?)
            } else {
                None
            };
            fields.push(FieldPattern { name, pat });
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(PatternKind::Struct { path, fields, rest })
    }

    fn parse_pattern(&mut self) -> Option<Pattern> {
        let first = self.parse_pattern_atom()?;
        if !matches!(self.peek(), TokenKind::Pipe) {
            return Some(first);
        }
        let span = first.span;
        let mut alts = vec![first];
        while self.eat(&TokenKind::Pipe) {
            alts.push(self.parse_pattern_atom()?);
        }
        Some(Pattern {
            kind: PatternKind::Or(alts),
            span,
        })
    }

    fn parse_pattern_atom(&mut self) -> Option<Pattern> {
        self.nested(Self::parse_pattern_atom_inner)
    }

    fn parse_pattern_atom_inner(&mut self) -> Option<Pattern> {
        let span = self.peek_span();
        // Negative numeric literal: `-NUM`.
        if matches!(self.peek(), TokenKind::Minus) {
            self.bump();
            let lit = match self.peek().clone() {
                TokenKind::IntLit(s) => {
                    self.bump();
                    Literal::Int(format!("-{s}"))
                }
                TokenKind::FloatLit(s) => {
                    self.bump();
                    Literal::Float(format!("-{s}"))
                }
                _ => {
                    let s = self.peek_span();
                    self.error(s, "literal expected after `-`");
                    return None;
                }
            };
            return Some(self.maybe_extend_range(span, lit));
        }
        let kind = match self.peek().clone() {
            TokenKind::IntLit(s) => {
                self.bump();
                return Some(self.maybe_extend_range(span, Literal::Int(s)));
            }
            TokenKind::FloatLit(s) => {
                self.bump();
                return Some(self.maybe_extend_range(span, Literal::Float(s)));
            }
            TokenKind::StrLit(s) => {
                self.bump();
                PatternKind::Literal(Literal::Str(s))
            }
            TokenKind::RawStrLit(s) => {
                self.bump();
                PatternKind::Literal(Literal::RawStr(s))
            }
            TokenKind::CharLit(s) => {
                self.bump();
                return Some(self.maybe_extend_range(span, Literal::Char(s)));
            }
            TokenKind::CCharLit(s) => {
                self.bump();
                return Some(self.maybe_extend_range(span, Literal::CChar(s)));
            }
            TokenKind::True => {
                self.bump();
                PatternKind::Literal(Literal::Bool(true))
            }
            TokenKind::False => {
                self.bump();
                PatternKind::Literal(Literal::Bool(false))
            }
            TokenKind::None => {
                self.bump();
                PatternKind::Literal(Literal::None)
            }
            TokenKind::Ident(name) if name == "_" => {
                self.bump();
                PatternKind::Wildcard
            }
            TokenKind::LParen => {
                self.bump();
                let mut subs: Vec<Pattern> = Vec::new();
                if !matches!(self.peek(), TokenKind::RParen) {
                    loop {
                        subs.push(self.parse_pattern()?);
                        if !self.eat(&TokenKind::Comma) {
                            break;
                        }
                        if matches!(self.peek(), TokenKind::RParen) {
                            break;
                        }
                    }
                }
                self.expect(&TokenKind::RParen, "`)`")?;
                PatternKind::Tuple(subs)
            }
            TokenKind::Ident(_) => {
                // Multi-segment path → enum variant pattern.
                if matches!(self.peek_next(), Some(TokenKind::ColonColon)) {
                    let path = self.parse_path()?;
                    if matches!(self.peek(), TokenKind::LBrace) {
                        self.parse_struct_pattern_body(path)?
                    } else {
                        let args = if self.eat(&TokenKind::LParen) {
                            let mut sub = Vec::new();
                            while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
                                sub.push(self.parse_pattern()?);
                                if !self.eat(&TokenKind::Comma) {
                                    break;
                                }
                            }
                            self.expect(&TokenKind::RParen, "`)`")?;
                            sub
                        } else {
                            Vec::new()
                        };
                        PatternKind::EnumVariant { path, args }
                    }
                } else if self.struct_expr_allowed
                    && matches!(self.peek_next(), Some(TokenKind::LBrace))
                {
                    // `Name { .. }` struct pattern. Disabled where a block
                    // follows the pattern (`catch e { body }`).
                    let path = self.parse_path()?;
                    self.parse_struct_pattern_body(path)?
                } else if matches!(self.peek_next(), Some(TokenKind::Colon)) {
                    // `name: T` — type-narrow pattern (sum-type slot).
                    let TokenKind::Ident(name) = self.peek().clone() else {
                        unreachable!()
                    };
                    self.bump(); // ident
                    self.bump(); // ':'
                    let ty = self.parse_type()?;
                    PatternKind::TypeCheck {
                        binder: Some(name),
                        ty,
                    }
                } else {
                    let TokenKind::Ident(name) = self.peek().clone() else {
                        unreachable!()
                    };
                    self.bump();
                    PatternKind::Binding { name, sub: None }
                }
            }
            other => {
                self.error(span, format!("pattern expected, found {other:?}"));
                return None;
            }
        };
        Some(Pattern { kind, span })
    }

    fn parse_call_args(&mut self) -> Option<Vec<CallArg>> {
        let mut args = Vec::new();
        while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
            // `name: expr` is a named argument; otherwise positional.
            if let TokenKind::Ident(name) = self.peek().clone() {
                if matches!(self.peek_next(), Some(TokenKind::Colon)) {
                    self.bump(); // ident
                    self.bump(); // `:`
                    let value = self.parse_expr()?;
                    args.push(CallArg::Named { name, value });
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                    continue;
                }
            }
            // `..expr` is a spread argument.
            if matches!(self.peek(), TokenKind::DotDot) {
                self.bump();
                let value = self.parse_expr()?;
                args.push(CallArg::Spread(value));
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
                continue;
            }
            let value = self.parse_expr()?;
            args.push(CallArg::Positional(value));
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        Some(args)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Recover {
    /// Program level: a stray `}` is consumed.
    TopItem,
    /// Inside `impl` / `trait` / `mod` / `extern` braces.
    NestedItem,
    /// Inside a block.
    Stmt,
}

const fn starts_item(k: &TokenKind) -> bool {
    use TokenKind as T;
    matches!(
        k,
        T::Fn
            | T::Struct
            | T::Enum
            | T::Union
            | T::Trait
            | T::Impl
            | T::Extern
            | T::Mod
            | T::Use
            | T::Const
            | T::Static
            | T::Type
            | T::Pub
            | T::HashLBracket
            | T::Unsafe
            | T::Async
    )
}

const fn is_block_like(e: &Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::Block(_)
            | ExprKind::If { .. }
            | ExprKind::Match { .. }
            | ExprKind::Loop { .. }
            | ExprKind::While { .. }
            | ExprKind::For { .. }
            | ExprKind::Try { .. }
    )
}

const fn starts_stmt(k: &TokenKind) -> bool {
    use TokenKind as T;
    matches!(
        k,
        T::Let | T::Return | T::Break | T::Continue | T::Throw | T::Use
    )
}

// Map a compound-assign token to its base operator symbol.
const fn compound_assign_op(tok: &rokc_lexer::TokenKind) -> Option<&'static str> {
    use rokc_lexer::TokenKind as T;
    Some(match tok {
        T::PlusEq => "+",
        T::MinusEq => "-",
        T::StarEq => "*",
        T::SlashEq => "/",
        T::PercentEq => "%",
        T::PercentPercentEq => "%%",
        T::AmpEq => "&",
        T::PipeEq => "|",
        T::CaretEq => "^",
        T::ShlEq => "<<",
        T::ShrEq => ">>",
        _ => return None,
    })
}

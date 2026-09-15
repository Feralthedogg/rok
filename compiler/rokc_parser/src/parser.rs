//! Parser entry point. Recursive descent with Pratt-style operator
//! parsing over the fixed precedence table (spec 3.2.3).

use rokc_ast::{
    AccessTail, AttrArg, AttrBody, Attribute, Block, CallArg, CatchArm, ConstExpr, EnumDef,
    EnumVariant, EnumVariantKind, Expr, ExprKind, ExternBlock, ExternItem, FieldPattern, FnDef,
    Generics, ImplDef, ImplItem, Item, Literal, MatchArm, ModDef, NamedField, Param, Path,
    PathSegment, Pattern, PatternKind, Program, Stmt, StmtKind, StructDef, StructKind, ThrowsKind,
    TraitDef, TraitItem, TryKind, Ty, TyKind, UnionDef,
};
use rokc_core::Visibility;
use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};
use rokc_lexer::token::keyword_str;
use rokc_lexer::{Token, TokenKind};

use crate::prec::{Assoc, CAST_PREC, COALESCE_PREC, ExtOps, Fixity};

#[path = "fstring.rs"]
mod fstring;
#[path = "literal.rs"]
pub mod literal;
#[path = "meta.rs"]
pub mod meta;

/// `rest` of a `let (..)` tuple pattern: splice index + optional name.
type LetTupleRest = (usize, Option<String>);

#[allow(clippy::struct_excessive_bools)] // independent context flags, not a state machine
pub struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    file: String,
    pub(crate) diagnostics: Vec<RokDiagnostic>,
    /// Whether `Path { .. }` is a struct literal here; off in `if` /
    /// `while` / `for` heads so the `{` opens the body.
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
    /// Links on the operator / postfix chains enclosing this point.
    chain: u32,
    /// Extra statements from a site that emits several (nested tuple
    /// destructure `let ((a, b), c) = ..;`, spec 3.15.4). `parse_block`
    /// drains it after each statement, so they land in the same scope.
    pending_stmts: Vec<Stmt>,
    /// Counter for unique temp names of nested tuple destructures.
    next_destructure_temp: u32,
    /// Spans of untyped `throws` in fn types not (yet) claimed by a
    /// `rethrows` signature; reported at the end of the parse.
    untyped_throws: Vec<Span>,
    /// Registered extension operators (spec 1.10.4) and their levels.
    ext: ExtOps,
    /// Items `#[derive(..)]` generated for the last item parsed.
    pending_items: Vec<Item>,
    /// User meta blocks (spec 6.8), gathered by the driver's pre-pass.
    meta: std::sync::Arc<meta::MetaTable>,
    /// The build's cfg (spec 6.3): resolves `#[cfg_attr]` and `cfg!(..)`
    /// before meta expansion. `None` outside a build (tools, pre-pass).
    cfg: Option<crate::cfg::CfgEnv>,
    /// Meta expansions in progress (cycle detection, 6.8.8).
    meta_stack: Vec<String>,
    /// Source text of the meta expansions so far (`Program::expanded`).
    expanded: Vec<String>,
    /// `#[literal]` registrations (spec 6.5), gathered by the pre-pass.
    literals: std::sync::Arc<literal::LiteralTable>,
    /// The last `parse_item` consumed an item that expanded to nothing.
    vanished: bool,
    /// Nested `fn`s (spec 4.10), lifted to module items once the
    /// enclosing item is parsed.
    lifted: Vec<FnDef>,
    /// Names of the `fn`s being parsed, outermost first (`Type.m` for
    /// a method).
    fn_names: Vec<String>,
    /// The impl target's or trait's name while parsing its items.
    fn_owner: Option<String>,
    /// Lifted names given out so far.
    lifted_names: std::collections::HashSet<String>,
    /// The next primary starts a statement: if it is block-like, `(` / `[`
    /// after it begin a new statement (`while c {} (a, b)`), not a call.
    stmt_head: bool,
}

/// Nesting limit for expressions, types, patterns and blocks.
const MAX_DEPTH: u32 = 256;
/// Links in one left-nested operator / postfix chain.
const MAX_CHAIN: u32 = 4096;
/// The path of the type a variadic `xs: ...T` parameter has in the body
/// (`Slice<T>`, spec 4.2.5).
pub const VARIADIC_SLICE: [&str; 5] = ["rok", "core", "collections", "slice", "Slice"];

/// `Slice<elem>`: a variadic `...elem` parameter's type.
#[must_use]
pub fn variadic_slice_ty(elem: Ty) -> Ty {
    let span = elem.span;
    let n = VARIADIC_SLICE.len();
    Ty {
        kind: TyKind::Path(Path {
            segments: VARIADIC_SLICE
                .iter()
                .enumerate()
                .map(|(k, name)| PathSegment {
                    name: (*name).to_owned(),
                    generics: if k + 1 == n {
                        vec![elem.clone()]
                    } else {
                        Vec::new()
                    },
                })
                .collect(),
            span,
        }),
        span,
    }
}
/// `MAX_DEPTH` levels need ~5 MiB (the dev profile builds the parser at
/// opt-level 1; ~4 MiB at opt-level 3: `Expr` values are large).
const PARSER_STACK: usize = 16 << 20;

pub fn parse_program(tokens: &[Token], file: impl Into<String>) -> (Program, Vec<RokDiagnostic>) {
    parse_program_ext(tokens, file, &ExtOps::default())
}

/// `parse_program` that also knows registered extension operators.
pub fn parse_program_ext(
    tokens: &[Token],
    file: impl Into<String>,
    ext: &ExtOps,
) -> (Program, Vec<RokDiagnostic>) {
    parse_program_meta(
        tokens,
        file,
        ext,
        &std::sync::Arc::default(),
        &std::sync::Arc::default(),
        None,
    )
}

/// `parse_program_ext` that also expands user meta blocks (spec 6.8)
/// and matches `#[literal]` patterns (spec 6.5).
pub fn parse_program_meta(
    tokens: &[Token],
    file: impl Into<String>,
    ext: &ExtOps,
    metas: &std::sync::Arc<meta::MetaTable>,
    literals: &std::sync::Arc<literal::LiteralTable>,
    cfg: Option<&crate::cfg::CfgEnv>,
) -> (Program, Vec<RokDiagnostic>) {
    let file = file.into();
    let ext = ext.clone();
    let metas = std::sync::Arc::clone(metas);
    let literals = std::sync::Arc::clone(literals);
    let cfg = cfg.cloned();
    let run = move || {
        let mut p = Parser::new(tokens, file);
        p.ext = ext;
        p.meta = metas;
        p.literals = literals;
        p.cfg = cfg;
        let program = p.parse_program();
        (program, p.diagnostics)
    };
    on_parser_stack(run)
}

/// A file that is one expression and nothing else (a `.rokon` file: the package
/// manifest): parse it without top-level statement rules (no `;`).
pub fn parse_expr_file(
    tokens: &[Token],
    file: impl Into<String>,
) -> (Option<Expr>, Vec<RokDiagnostic>) {
    let file = file.into();
    on_parser_stack(move || {
        let mut p = Parser::new(tokens, file);
        let e = p.parse_expr();
        if e.is_some() && !matches!(p.peek(), TokenKind::Eof) {
            let span = p.peek_span();
            p.error(span, "expected the end of the file after the expression");
        }
        (e, p.diagnostics)
    })
}

/// Recursive descent: `MAX_DEPTH` levels need more than a default 1-2 MiB
/// (Windows main, spawned threads) stack, so parse on a dedicated thread
/// whose stack is sized for the cap (address space only until used).
fn on_parser_stack<T: Send>(run: impl FnOnce() -> T + Send) -> T {
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
    pub fn new(tokens: &'a [Token], file: impl Into<String>) -> Self {
        Self {
            tokens,
            pos: 0,
            file: file.into(),
            diagnostics: Vec::new(),
            struct_expr_allowed: true,
            stmt_head: false,
            type_sum_allowed: true,
            pending: None,
            in_cast_type: false,
            depth: 0,
            depth_reported: false,
            chain: 0,
            pending_stmts: Vec::new(),
            next_destructure_temp: 0,
            untyped_throws: Vec::new(),
            ext: ExtOps::default(),
            pending_items: Vec::new(),
            meta: std::sync::Arc::default(),
            cfg: None,
            meta_stack: Vec::new(),
            expanded: Vec::new(),
            literals: std::sync::Arc::default(),
            vanished: false,
            lifted: Vec::new(),
            fn_names: Vec::new(),
            fn_owner: None,
            lifted_names: std::collections::HashSet::new(),
        }
    }

    /// Does `f` fail here? Always rewinds: position, diagnostics and
    /// queued statements are as before.
    fn backtracks<T>(&mut self, f: impl FnOnce(&mut Self) -> Option<T>) -> bool {
        let (pos, n_diags, n_pending, n_lifted) = (
            self.pos,
            self.diagnostics.len(),
            self.pending_stmts.len(),
            self.lifted.len(),
        );
        let failed = f(self).is_none();
        self.pos = pos;
        self.diagnostics.truncate(n_diags);
        self.pending_stmts.truncate(n_pending);
        self.lifted.truncate(n_lifted);
        failed
    }

    pub(crate) fn at_eof(&self) -> bool {
        matches!(self.peek(), TokenKind::Eof)
    }

    pub(crate) const fn position(&self) -> usize {
        self.pos
    }

    pub(crate) fn parse_item_pub(&mut self) -> Option<Item> {
        self.parse_item()
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

    /// One more operator / postfix link on a left-nested chain (`1 + 1 +
    /// ..`, `a.f().g()..`): the tree deepens without `nested`, so the
    /// links of all enclosing chains share their own cap.
    fn chain_link(&mut self) -> Option<()> {
        self.chain += 1;
        if self.chain <= MAX_CHAIN {
            return Some(());
        }
        if !self.depth_reported {
            self.depth_reported = true;
            let span = self.peek_span();
            self.error(
                span,
                format!("expression chain too long (limit {MAX_CHAIN})"),
            );
        }
        None
    }

    /// From a path (`a::E`) at the cursor: is its `{ .. }` group followed
    /// by another `{`?
    fn braces_then_block(&self) -> bool {
        let mut i = self.pos;
        let kind = |i: usize| self.tokens.get(i).map(|t| &t.kind);
        while matches!(kind(i), Some(TokenKind::Ident(_) | TokenKind::ColonColon)) {
            i += 1;
        }
        if i == self.pos || !matches!(kind(i), Some(TokenKind::LBrace)) {
            return false;
        }
        let mut depth = 0u32;
        while let Some(k) = kind(i) {
            match k {
                TokenKind::LBrace => depth += 1,
                TokenKind::RBrace => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(kind(i + 1), Some(TokenKind::LBrace));
                    }
                }
                _ => {}
            }
            i += 1;
        }
        false
    }

    fn fresh_destructure_temp(&mut self) -> String {
        let n = self.next_destructure_temp;
        self.next_destructure_temp = self.next_destructure_temp.wrapping_add(1);
        format!("__destruct{n}")
    }

    /// The pattern of `if let` / `while let`, with an optional `: T`
    /// (spec 3.10.5). `(a, b): T` matches a `__destructN: T` and
    /// destructures it in the body: the returned statement.
    fn parse_let_cond_pattern(&mut self) -> Option<(Pattern, Option<Stmt>)> {
        let pat = self.parse_pattern()?;
        if !self.eat(&TokenKind::Colon) {
            return Some((pat, None));
        }
        let ty = self.parse_type()?;
        let span = pat.span;
        let typed = |binder| Pattern {
            kind: PatternKind::TypeCheck { binder, ty },
            span,
        };
        if matches!(pat.kind, PatternKind::Wildcard) {
            return Some((typed(None), None));
        }
        let tmp = self.fresh_destructure_temp();
        let init = Expr {
            span,
            kind: ExprKind::Path(Path {
                segments: vec![PathSegment {
                    name: tmp.clone(),
                    generics: Vec::new(),
                }],
                span,
            }),
        };
        let stmt = Stmt {
            kind: StmtKind::LetPattern {
                pat,
                ty: None,
                init,
            },
            span,
        };
        Some((typed(Some(tmp)), Some(stmt)))
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
                let msg = format!(
                    "expected `>` to close generic arguments, found {}",
                    other.describe()
                );
                let span = self.peek_span();
                self.error(span, msg);
                return false;
            }
        };
        self.bump();
        self.pending = rest;
        true
    }

    /// Open a generic list or `<T as Tr>`: consume a `<`, splitting `<<`
    /// (`Tag<<A as P>::X>`) and leaving the second pending.
    fn eat_opening_lt(&mut self) -> bool {
        match self.peek() {
            TokenKind::Lt => {
                self.bump();
            }
            TokenKind::Shl => {
                self.bump();
                self.pending = Some(TokenKind::Lt);
            }
            _ => return false,
        }
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
            return Token::new(kind, span);
        }
        // Recovery can bump past the last token: hand back a synthetic Eof.
        let Some(t) = self.tokens.get(self.pos).cloned() else {
            return Token::new(TokenKind::Eof, Span::DUMMY);
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
            let d = self.expected(kind, what);
            self.diagnostics.push(d);
            None
        }
    }

    /// "expected X, found Y" with hints for common slips: a missing `;`
    /// (pointed at the end of the line), an unclosed delimiter (its
    /// opening location), `->` / `=>` mixups.
    fn expected(&self, kind: &TokenKind, what: &str) -> RokDiagnostic {
        let found = self.peek();
        let here = self.peek_span();
        let d = RokDiagnostic::error(
            ErrorKind::Parse,
            format!("expected {what}, found {}", found.describe()),
        )
        .with_file(self.file.clone());
        let prev = self.prev_span();
        match kind {
            TokenKind::Semi if prev.is_some_and(|p| p.line < here.line || here.is_dummy()) => {
                let at = self.after_prev();
                return d
                    .with_span(at, "expected `;`")
                    .with_help("add `;` at the end of the statement");
            }
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                if let Some(open) = self.unclosed_opener(kind) {
                    return d
                        .with_span(here, format!("expected {what}"))
                        .with_secondary(open, "unclosed delimiter");
                }
            }
            TokenKind::FatArrow if matches!(found, TokenKind::Arrow) => {
                return d
                    .with_span(here, "")
                    .with_help("match arms are written `pattern => value`");
            }
            _ if matches!(found, TokenKind::FatArrow)
                && self.prev_kind() == Some(&TokenKind::RParen) =>
            {
                return d
                    .with_span(here, "")
                    .with_help("a return type is written `-> Type`");
            }
            _ => {}
        }
        // `fucn main`, `retrun x`: an identifier that reads as a
        // misspelled keyword, followed by another word.
        if let Some(TokenKind::Ident(word)) = self.prev_kind() {
            if matches!(found, TokenKind::Ident(_)) || keyword_alias(word).is_some() {
                if let Some(k) = keyword_hint(word) {
                    let at = self.prev_span().unwrap_or(here);
                    return d
                        .with_span(here, "")
                        .with_secondary(at, "not a keyword")
                        .with_help(format!("did you mean `{k}`?"));
                }
            }
        }
        d.with_span(here, "")
    }

    fn prev_span(&self) -> Option<Span> {
        self.tokens.get(self.pos.checked_sub(1)?).map(|t| t.span)
    }

    /// `span` widened to the end of the previous token: a compound
    /// expression covers all its tokens.
    fn to_prev(&self, mut span: Span) -> Span {
        if let Some(p) = self.prev_span() {
            if p.file == span.file && p.end > span.end {
                span.end = p.end;
            }
        }
        span
    }

    fn prev_kind(&self) -> Option<&TokenKind> {
        self.tokens.get(self.pos.checked_sub(1)?).map(|t| &t.kind)
    }

    /// Zero-width span just after the previous token.
    fn after_prev(&self) -> Span {
        let Some(t) = self.pos.checked_sub(1).and_then(|i| self.tokens.get(i)) else {
            return self.peek_span();
        };
        let len = u32::try_from(t.kind.text().chars().count()).unwrap_or(1);
        Span {
            start: t.span.end,
            end: t.span.end,
            line: t.span.line,
            col: t.span.col + len.max(1),
            file: t.span.file,
        }
    }

    /// The innermost delimiter still open before the current token
    /// that `close` would close.
    fn unclosed_opener(&self, close: &TokenKind) -> Option<Span> {
        let mut stack: Vec<(&TokenKind, Span)> = Vec::new();
        for t in self.tokens.get(..self.pos)? {
            match &t.kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => {
                    stack.push((&t.kind, t.span));
                }
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                    stack.pop();
                }
                _ => {}
            }
        }
        let open = match close {
            TokenKind::RParen => TokenKind::LParen,
            TokenKind::RBracket => TokenKind::LBracket,
            _ => TokenKind::LBrace,
        };
        stack
            .iter()
            .rev()
            .find(|(k, _)| **k == open)
            .map(|(_, s)| *s)
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
        let mut tops = Vec::new();
        let attrs = self.parse_inner_attrs();
        while !matches!(self.peek(), TokenKind::Eof) {
            let from = self.pos;
            if self.meta_block().is_some() || self.eat(&TokenKind::Semi) {
                continue;
            }
            tops.push((self.peek_span().start, self.at_item_start()));
            if self.at_item_start() {
                if let Some(item) = self.parse_item() {
                    items.push(item);
                    items.append(&mut self.pending_items);
                } else if !std::mem::take(&mut self.vanished) {
                    self.recover(from, Recover::TopItem);
                }
            } else if let Some(stmt) = self.parse_top_stmt() {
                stmts.push(stmt);
                while let Some(extra) = self.pending_stmts.pop() {
                    stmts.push(extra);
                }
                items.extend(self.lifted.drain(..).map(Item::Fn));
            } else {
                self.pending_stmts.clear();
                self.recover(from, Recover::Stmt);
            }
        }
        // Untyped `throws` in fn types that no `rethrows` claimed keep the
        // marker; HIR reads it as `any Error` (spec 4.14).
        self.untyped_throws.clear();
        Program {
            attrs,
            items,
            stmts,
            expanded: std::mem::take(&mut self.expanded),
            tops,
        }
    }

    /// Whether the next tokens begin an item rather than a top-level
    /// statement. `unsafe` / `async` start an item only when `fn` follows
    /// (`unsafe { .. }` / `async { .. }` are expressions).
    fn at_item_start(&self) -> bool {
        match self.peek() {
            TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield => matches!(
                self.peek_next(),
                Some(
                    TokenKind::Fn
                        | TokenKind::Impl
                        | TokenKind::Unsafe
                        | TokenKind::Async
                        | TokenKind::Yield
                )
            ),
            _ if self.at_union_item() || self.at_ctx_item() => true,
            k => starts_item(k),
        }
    }

    /// `extern "C" {` / `extern {`, `const NAME` / `const fn`,
    /// `static [mut] NAME`, `type Name`: contextual at item start.
    fn at_ctx_item(&self) -> bool {
        let next = self.peek_next();
        let TokenKind::Ident(k) = self.peek() else {
            return false;
        };
        match k.as_str() {
            "extern" => matches!(next, Some(TokenKind::StrLit(_) | TokenKind::LBrace)),
            "const" => matches!(next, Some(TokenKind::Ident(_) | TokenKind::Fn)),
            "static" | "type" => matches!(next, Some(TokenKind::Ident(_))),
            _ => false,
        }
    }

    /// Spec 1.5.4: `union` is a contextual keyword — an item only as
    /// `union Name` at item start; elsewhere it is an identifier
    /// (`Set::union`, `a.union(b)`).
    fn at_union_item(&self) -> bool {
        matches!(self.peek(), TokenKind::Ident(n) if n == "union")
            && matches!(self.peek_next(), Some(TokenKind::Ident(_)))
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
            StmtKind::Trailing(expr) if !ends_stmt(&expr) => {
                let d = self.expected(&TokenKind::Semi, "`;` after top-level expression");
                self.diagnostics.push(d);
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
        loop {
            self.doc_attrs(true, &mut attrs);
            if !matches!(self.peek(), TokenKind::HashBangLBracket) {
                return attrs;
            }
            if let Some(attr) = self.parse_attr(true) {
                match &self.cfg {
                    Some(env) => crate::cfg::expand_cfg_attr(env, attr, &mut attrs),
                    None => attrs.push(attr),
                }
            }
        }
    }

    fn parse_outer_attrs(&mut self) -> Vec<Attribute> {
        let mut attrs = Vec::new();
        loop {
            self.doc_attrs(false, &mut attrs);
            if !matches!(self.peek(), TokenKind::HashLBracket) {
                return attrs;
            }
            if let Some(attr) = self.parse_attr(false) {
                match &self.cfg {
                    Some(env) => crate::cfg::expand_cfg_attr(env, attr, &mut attrs),
                    None => attrs.push(attr),
                }
            }
        }
    }

    /// The next token's `///` (or `//!`) lines as `#[doc = ".."]`
    /// attributes (the text escaped, as a string literal holds it). Doc
    /// comments where no attribute can go are dropped.
    fn doc_attrs(&self, inner: bool, out: &mut Vec<Attribute>) {
        if self.pending.is_some() {
            return;
        }
        let Some(t) = self.tokens.get(self.pos) else {
            return;
        };
        out.extend(
            t.docs
                .iter()
                .filter(|d| d.inner == inner)
                .map(|d| Attribute {
                    path: vec!["doc".to_owned()],
                    body: AttrBody::Value(Literal::Str(
                        d.text.replace('\\', "\\\\").replace('"', "\\\""),
                    )),
                    inner,
                    span: Span {
                        file: t.span.file,
                        ..d.span
                    },
                }),
        );
    }

    fn parse_attr(&mut self, inner: bool) -> Option<Attribute> {
        let start = self.peek_span();
        self.bump(); // `#[` or `#![`
        let path = self.parse_attr_path()?;
        let body = if path == ["literal"] && matches!(self.peek(), TokenKind::LParen) {
            self.parse_literal_attr_body()
        } else {
            self.parse_attr_body()
        };
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
                other => {
                    let s = self.peek_span();
                    self.error(
                        s,
                        format!("expected attribute name, found {}", other.describe()),
                    );
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

    /// One argument, or a range of two (`a..=b`, `..b`, `a..`).
    fn parse_attr_arg(&mut self) -> Option<AttrArg> {
        let is_range = |k: &TokenKind| matches!(k, TokenKind::DotDot | TokenKind::DotDotEq);
        let lo = if is_range(self.peek()) {
            None
        } else {
            Some(self.parse_attr_atom()?)
        };
        if !is_range(self.peek()) {
            return lo;
        }
        let inclusive = matches!(self.peek(), TokenKind::DotDotEq);
        self.bump();
        let hi = if matches!(self.peek(), TokenKind::Comma | TokenKind::RParen) {
            None
        } else {
            Some(Box::new(self.parse_attr_atom()?))
        };
        Some(AttrArg::Range {
            lo: lo.map(Box::new),
            hi,
            inclusive,
        })
    }

    fn parse_attr_atom(&mut self) -> Option<AttrArg> {
        let ident_name = match self.peek().clone() {
            TokenKind::Ident(n) => Some(n),
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
            format!(
                "unexpected {} in attribute arguments",
                self.peek().describe()
            ),
        );
        None
    }

    fn parse_attr_literal(&mut self) -> Option<Literal> {
        self.try_parse_attr_literal().or_else(|| {
            let s = self.peek_span();
            self.error(
                s,
                format!("expected literal, found {}", self.peek().describe()),
            );
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

    /// A `fn` type behind `unsafe` (calling it needs an unsafe scope,
    /// 4.15) and / or `extern "C"` (a C function pointer, 5.9.4).
    fn parse_marked_fn_type(&mut self, start: Span) -> Option<TyKind> {
        let unsafe_fn = self.eat(&TokenKind::Unsafe);
        if !unsafe_fn {
            self.bump(); // `extern`
            if let TokenKind::StrLit(abi) = self.peek().clone() {
                if abi != "C" {
                    self.error(start, format!("unsupported ABI `\"{abi}\"` (only \"C\")"));
                }
            }
            self.bump(); // ABI string
        }
        let mut t = self.parse_type_atom_inner()?;
        if let TyKind::Fn(_, _, bounds) = &mut t.kind {
            if unsafe_fn {
                bounds.unsafe_fn = true;
            } else {
                bounds.c_abi = true;
            }
        }
        Some(t.kind)
    }

    /// `extern "<abi>" fn` starting `k` tokens ahead (a C fn pointer type).
    fn at_c_fn_type(&self, k: usize) -> bool {
        let at = |i: usize| self.tokens.get(self.pos + k + i).map(|t| &t.kind);
        matches!(at(0), Some(TokenKind::Ident(n)) if n == "extern")
            && matches!(at(1), Some(TokenKind::StrLit(_)))
            && matches!(at(2), Some(TokenKind::Fn))
    }

    /// The current token is the contextual keyword `w` (an identifier
    /// token; spec 1.5).
    fn at_kw(&self, w: &str) -> bool {
        matches!(self.peek(), TokenKind::Ident(n) if n == w)
    }

    fn eat_kw(&mut self, w: &str) -> bool {
        let hit = self.at_kw(w);
        if hit {
            self.bump();
        }
        hit
    }

    fn expect_kw(&mut self, w: &str) -> Option<()> {
        if self.eat_kw(w) {
            return Some(());
        }
        let s = self.peek_span();
        self.error(
            s,
            format!("expected `{w}`, found {}", self.peek().describe()),
        );
        None
    }

    /// A member / field / argument-label name: an identifier or any
    /// reserved keyword but `self` (`p.type`, `f(match: 1)`).
    fn peek_name(&self) -> Option<String> {
        match self.peek() {
            TokenKind::Ident(n) => Some(n.clone()),
            k => keyword_str(k).filter(|w| *w != "self").map(str::to_owned),
        }
    }

    fn peek_next(&self) -> Option<TokenKind> {
        self.tokens.get(self.pos + 1).map(|t| t.kind.clone())
    }

    fn parse_item(&mut self) -> Option<Item> {
        let lifted = self.lifted.len();
        let item = self.parse_item_lifting();
        let nested: Vec<Item> = self.lifted.drain(lifted..).map(Item::Fn).collect();
        self.pending_items.extend(nested);
        item
    }

    fn parse_item_lifting(&mut self) -> Option<Item> {
        let span = self.peek_span();
        let from = self.pos;
        let item = self.parse_item_inner()?;
        // `pkg` / `sup` / `rok` are path roots and `any` is the any
        // type, so no module or type may take those names.
        let name = match &item {
            Item::Struct(d) => Some(&d.name),
            Item::Enum(d) => Some(&d.name),
            Item::Union(d) => Some(&d.name),
            Item::Trait(d) => Some(&d.name),
            Item::TypeAlias(d) => Some(&d.name),
            Item::Mod(d) => Some(&d.name),
            _ => None,
        };
        if let Some(n) = name.filter(|n| matches!(n.as_str(), "pkg" | "sup" | "rok" | "any")) {
            let what = if matches!(item, Item::Mod(_)) {
                "module"
            } else {
                "type"
            };
            self.error(
                span,
                format!("`{n}` cannot name a {what}: it is reserved as a path root / type keyword"),
            );
        }
        if !self.meta.is_empty() {
            // Spec 6.8.3: a user attribute replaces the item with its
            // expansion (which expands again — 6.8.8).
            if let Some(items) = self.expand_user_attribute(&item, from) {
                let mut it = items.into_iter();
                let first = it.next();
                self.pending_items.extend(it);
                self.vanished = first.is_none();
                return first;
            }
        }
        let (item, user_derived) = if self.meta.is_empty() {
            (item, Vec::new())
        } else {
            self.expand_user_derives(item, from)
        };
        let (derived, diags) = crate::derive::derive_items(&item, &self.file);
        self.pending_items.extend(derived);
        self.pending_items.extend(user_derived);
        self.diagnostics.extend(diags);
        Some(item)
    }

    fn parse_item_inner(&mut self) -> Option<Item> {
        let attrs = self.parse_outer_attrs();
        let vis = self.parse_visibility();
        if self.at_union_item() {
            return self.parse_union(vis, attrs).map(Item::Union);
        }
        // Contextual item keywords: `extern "C"`, `const NAME` /
        // `const fn`, `static [mut] NAME`, `type Name`.
        if self.at_kw("extern") {
            // `extern "C" fn f(..) { .. }` (spec 5.9.10): a rok function
            // with the C ABI, marked for HIR's checks.
            let after_abi = self.tokens.get(self.pos + 2).map(|t| &t.kind);
            if matches!(self.peek_next(), Some(TokenKind::StrLit(_)))
                && matches!(after_abi, Some(TokenKind::Fn | TokenKind::Unsafe))
            {
                let span = self.peek_span();
                self.bump(); // `extern`
                self.bump(); // ABI string
                let mut attrs = attrs;
                attrs.push(Attribute {
                    path: vec![rokc_ast::EXTERN_C_FN_ATTR.to_owned()],
                    body: rokc_ast::AttrBody::Empty,
                    inner: false,
                    span,
                });
                return self.parse_fn(vis, attrs).map(Item::Fn);
            }
            return self.parse_extern_block(attrs).map(Item::Extern);
        }
        if self.at_kw("const") {
            if matches!(self.peek_next(), Some(TokenKind::Fn)) {
                return self.parse_const_fn(vis, attrs).map(Item::Fn);
            }
            return self.parse_const(vis, attrs).map(Item::Const);
        }
        if self.at_kw("static") {
            return self.parse_static(vis, attrs).map(Item::Static);
        }
        if self.at_kw("type") {
            return self.parse_type_alias(vis, attrs).map(Item::TypeAlias);
        }
        match self.peek() {
            TokenKind::Unsafe if self.peek_next() == Some(TokenKind::Impl) => {
                self.bump();
                self.parse_impl(vis, attrs).map(|i| {
                    Item::Impl(ImplDef {
                        is_unsafe: true,
                        ..i
                    })
                })
            }
            TokenKind::Fn | TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield => {
                self.parse_fn(vis, attrs).map(Item::Fn)
            }
            TokenKind::Trait => self.parse_trait(vis, attrs).map(Item::Trait),
            TokenKind::Struct => self.parse_struct(vis, attrs).map(Item::Struct),
            TokenKind::Enum => self.parse_enum(vis, attrs).map(Item::Enum),
            TokenKind::Impl => self.parse_impl(vis, attrs).map(Item::Impl),
            TokenKind::Mod => self.parse_mod(vis, attrs).map(Item::Mod),
            TokenKind::Use => self.parse_use(vis, attrs).map(Item::Use),
            _ => {
                let span = self.peek_span();
                self.error(span, "expected an item");
                None
            }
        }
    }

    /// `type NAME[<G>] = ty;`
    fn parse_type_alias(
        &mut self,
        vis: Visibility,
        attrs: Vec<Attribute>,
    ) -> Option<rokc_ast::TypeAliasDef> {
        let start = self.peek_span();
        self.bump(); // contextual `type`
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(
                s,
                format!("expected type alias name, found {}", self.peek().describe()),
            );
            return None;
        };
        let generics = self.parse_generic_params();
        let mut where_clause = self.parse_where_clause();
        self.expect(&TokenKind::Eq, "`=`")?;
        let ty = self.parse_type()?;
        // `type A<T> = B<T> where T: X;` reads the same.
        where_clause.extend(self.parse_where_clause());
        self.expect(&TokenKind::Semi, "`;`")?;
        Some(rokc_ast::TypeAliasDef {
            vis,
            attrs,
            name,
            generics,
            ty,
            where_clause,
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
        self.bump(); // contextual `const`
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(
                s,
                format!("expected const name, found {}", self.peek().describe()),
            );
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

    /// `static [mut] NAME: T = expr;` — a module-level global.
    fn parse_static(
        &mut self,
        vis: Visibility,
        attrs: Vec<Attribute>,
    ) -> Option<rokc_ast::StaticDef> {
        let start = self.peek_span();
        self.bump(); // contextual `static`
        let is_mut = matches!(self.peek_next(), Some(TokenKind::Ident(_))) && self.eat_kw("mut");
        // Spec 5.3: `static mut` only inside `extern "C" { .. }` (FFI),
        // which doesn't come through here.
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
            self.error(
                s,
                format!("expected static name, found {}", self.peek().describe()),
            );
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
            self.error(
                s,
                format!("expected struct name, found {}", self.peek().describe()),
            );
            return None;
        };
        let generics = if matches!(self.peek(), TokenKind::Lt) {
            self.parse_generic_params()
        } else {
            Generics::default()
        };
        let mut where_clause = self.parse_where_clause();

        let kind = match self.peek().clone() {
            TokenKind::Semi => {
                self.bump();
                StructKind::Unit
            }
            TokenKind::LParen => {
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
                // `struct P<T>(T) where T: X;` reads the same.
                where_clause.extend(self.parse_where_clause());
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
            where_clause,
            span: start,
        })
    }

    /// `union Name<G> { f: T; g: U; }` — fields share storage.
    fn parse_union(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<UnionDef> {
        let start = self.peek_span();
        self.bump(); // contextual `union`
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(
                s,
                format!("expected union name, found {}", self.peek().describe()),
            );
            return None;
        };
        let generics = if matches!(self.peek(), TokenKind::Lt) {
            self.parse_generic_params()
        } else {
            Generics::default()
        };
        let where_clause = self.parse_where_clause();
        let fields = self.parse_named_fields(false)?;
        Some(UnionDef {
            vis,
            attrs,
            name,
            generics,
            fields,
            where_clause,
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
            let Some(name) = self.peek_name() else {
                self.error(
                    span,
                    format!("expected field name, found {}", self.peek().describe()),
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

    /// `impl [Trait for] Type { .. }`: an inherent or trait impl.
    fn parse_impl(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<ImplDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Impl, "`impl`")?;
        let generics = self.parse_generic_params();
        // `impl !Send for T {}` — auto-trait opt-out.
        let negative = self.eat(&TokenKind::Bang);
        let first_ty = self.parse_type()?;
        if negative && !matches!(self.peek(), TokenKind::For) {
            let s = self.peek_span();
            self.error(s, "`impl !Trait` needs `for Type`");
        }
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
        let owner = match &self_ty.kind {
            TyKind::Path(p) => p.segments.last().map(|s| s.name.clone()),
            _ => None,
        };
        let outer_owner = std::mem::replace(&mut self.fn_owner, owner);
        let items = self.parse_impl_items();
        self.fn_owner = outer_owner;
        let items = items?;
        Some(ImplDef {
            vis,
            attrs,
            generics,
            trait_path,
            is_unsafe: false,
            negative,
            self_ty,
            where_clause,
            items,
            module: String::new(),
            span: start,
        })
    }

    /// An impl's items through its `}`.
    fn parse_impl_items(&mut self) -> Option<Vec<ImplItem>> {
        let mut items = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let attrs_from = self.pos;
            let item_attrs = self.parse_outer_attrs();
            let item_vis = self.parse_visibility();
            match self.peek() {
                TokenKind::Fn | TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield => {
                    let from = self.pos;
                    if let Some(f) = self.parse_fn(item_vis, item_attrs) {
                        let fs = self.expand_method(f, attrs_from);
                        items.extend(fs.into_iter().map(ImplItem::Method));
                    } else {
                        self.recover(from, Recover::NestedItem);
                    }
                }
                // Spec 2.9.1: `impl_item ::= fn_decl | "type" ident "=" ty ";" | const_decl`.
                // Associated-type concrete binding: `type Output = V;`.
                TokenKind::Ident(k) if k == "type" => {
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
                TokenKind::Ident(k)
                    if k == "const" && matches!(self.peek_next(), Some(TokenKind::Fn)) =>
                {
                    let from = self.pos;
                    if let Some(f) = self.parse_const_fn(item_vis, item_attrs) {
                        let fs = self.expand_method(f, attrs_from);
                        items.extend(fs.into_iter().map(ImplItem::Method));
                    } else {
                        self.recover(from, Recover::NestedItem);
                    }
                }
                // Spec 2.9.1 `impl_item ::= .. | const_decl`.
                TokenKind::Ident(k) if k == "const" => {
                    let from = self.pos;
                    match self.parse_const(item_vis, item_attrs) {
                        Some(c) => items.push(ImplItem::Const(c)),
                        None => self.recover(from, Recover::NestedItem),
                    }
                }
                _ => {
                    let s = self.peek_span();
                    self.error(
                        s,
                        format!("expected impl item, found {}", self.peek().describe()),
                    );
                    let from = self.pos;
                    self.recover(from, Recover::NestedItem);
                }
            }
        }
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(items)
    }

    /// A method (impl or trait) with a user attribute (spec 6.9.5:
    /// `@accept(fn)` takes methods too) becomes its expansion, which must
    /// be methods.
    fn expand_method(&mut self, f: FnDef, from: usize) -> Vec<FnDef> {
        if self.meta.is_empty() {
            return vec![f];
        }
        let span = f.span;
        let item = Item::Fn(f);
        let Some(items) = self.expand_user_attribute(&item, from) else {
            let Item::Fn(f) = item else { unreachable!() };
            return vec![f];
        };
        let mut out = Vec::new();
        for i in items {
            match i {
                Item::Fn(f) => out.push(f),
                _ => self.error(
                    span,
                    "an attribute on a method must expand to methods only (spec 6.9.5)",
                ),
            }
        }
        out
    }

    /// `enum Name { V, V(T), V { x: T }, .. }` (spec 2.4).
    fn parse_enum(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<EnumDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Enum, "`enum`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(
                s,
                format!("expected enum name, found {}", self.peek().describe()),
            );
            return None;
        };
        let generics = if matches!(self.peek(), TokenKind::Lt) {
            self.parse_generic_params()
        } else {
            Generics::default()
        };
        let where_clause = self.parse_where_clause();
        self.expect(&TokenKind::LBrace, "`{`")?;

        let mut variants = Vec::new();
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let v_attrs = self.parse_outer_attrs();
            // Spec 5.6.9: variants take the enum's visibility.
            if matches!(self.peek(), TokenKind::Pub) {
                let s = self.peek_span();
                self.error(
                    s,
                    "enum variants take the enum's visibility; remove the visibility \
                     keyword (spec 5.6.9)",
                );
                self.parse_visibility();
            }
            let v_span = self.peek_span();
            let v_name = if let TokenKind::Ident(n) = self.peek().clone() {
                self.bump();
                n
            } else {
                let s = self.peek_span();
                self.error(
                    s,
                    format!("expected variant name, found {}", self.peek().describe()),
                );
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
            where_clause,
            span: start,
        })
    }

    // `extern "ABI" { fn name(args) -> ret; ... }`. ABI defaults to "C".
    fn parse_extern_block(&mut self, attrs: Vec<Attribute>) -> Option<ExternBlock> {
        let start = self.peek_span();
        self.bump(); // contextual `extern`
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
                // Spec 5.9.3: `static mut? name: T;` defined outside.
                TokenKind::Ident(k) if k == "static" => {
                    let from = self.pos;
                    let span = self.peek_span();
                    self.bump();
                    let is_mut =
                        matches!(self.peek_next(), Some(TokenKind::Ident(_))) && self.eat_kw("mut");
                    let name = match self.peek().clone() {
                        TokenKind::Ident(n) => {
                            self.bump();
                            Some(n)
                        }
                        _ => None,
                    };
                    let ty = name.as_ref().and_then(|_| {
                        self.expect(&TokenKind::Colon, "`:`")?;
                        let ty = self.parse_type()?;
                        self.expect(&TokenKind::Semi, "`;`")?;
                        Some(ty)
                    });
                    if let (Some(name), Some(ty)) = (name, ty) {
                        items.push(ExternItem::Static(rokc_ast::StaticDef {
                            vis: item_vis,
                            attrs: item_attrs,
                            name,
                            ty,
                            value: None,
                            is_mut,
                            span,
                        }));
                    } else {
                        self.error(span, "expected `static name: Type;` in `extern` block");
                        self.recover(from, Recover::NestedItem);
                    }
                }
                _ => {
                    let s = self.peek_span();
                    self.error(
                        s,
                        format!("expected extern item, found {}", self.peek().describe()),
                    );
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

    fn parse_mod(&mut self, vis: Visibility, mut attrs: Vec<Attribute>) -> Option<ModDef> {
        let start = self.peek_span();
        self.expect(&TokenKind::Mod, "`mod`")?;
        let name = if let TokenKind::Ident(n) = self.peek().clone() {
            self.bump();
            n
        } else {
            let s = self.peek_span();
            self.error(
                s,
                format!("expected module name, found {}", self.peek().describe()),
            );
            return None;
        };
        let items = if matches!(self.peek(), TokenKind::LBrace) {
            self.bump();
            // `#![..]` / `//!` at the body's head are the module's (6.2.8).
            attrs.extend(self.parse_inner_attrs());
            let mut items = Vec::new();
            while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
                let from = self.pos;
                if self.meta_block().is_some() {
                    continue;
                }
                if !self.at_item_start() {
                    let span = self.peek_span();
                    self.error(
                        span,
                        format!(
                            "expected an item in `mod {name}`: module bodies are \
                             definitions-only; statements belong in `main.rok` (spec 4.16.6)"
                        ),
                    );
                    self.recover(from, Recover::NestedItem);
                } else if let Some(item) = self.parse_item() {
                    items.push(item);
                    items.append(&mut self.pending_items);
                } else if !std::mem::take(&mut self.vanished) {
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
            // `use` roots: a bare identifier (absolute), `pkg::` (package
            // root) or `sup::` (parent). No `self::`: same-module children
            // resolve through the ancestor walk.
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
                    self.error(
                        s,
                        format!(
                            "expected alias name after `as`, found {}",
                            self.peek().describe()
                        ),
                    );
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
            self.error(
                s,
                format!("expected trait name, found {}", self.peek().describe()),
            );
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
        let outer_owner = self.fn_owner.replace(name.clone());
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let from = self.pos;
            if let Some(item) = self.parse_trait_item() {
                match item {
                    TraitItem::Method(f) => {
                        let fs = self.expand_method(f, from);
                        items.extend(fs.into_iter().map(TraitItem::Method));
                    }
                    item => items.push(item),
                }
            } else {
                self.recover(from, Recover::NestedItem);
            }
        }
        self.fn_owner = outer_owner;
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
            TokenKind::Ident(k)
                if k == "const" && matches!(self.peek_next(), Some(TokenKind::Fn)) =>
            {
                self.parse_const_fn(vis, attrs).map(TraitItem::Method)
            }
            TokenKind::Ident(k) if k == "const" => {
                self.bump();
                let TokenKind::Ident(name) = self.peek().clone() else {
                    let s = self.peek_span();
                    self.error(
                        s,
                        format!(
                            "expected associated const name, found {}",
                            self.peek().describe()
                        ),
                    );
                    return None;
                };
                self.bump();
                self.expect(&TokenKind::Colon, "`:`")?;
                let ty = self.parse_type()?;
                let default = if self.eat(&TokenKind::Eq) {
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                self.expect(&TokenKind::Semi, "`;`")?;
                Some(TraitItem::Const { name, ty, default })
            }
            TokenKind::Ident(k) if k == "type" => {
                self.bump();
                let name = if let TokenKind::Ident(n) = self.peek().clone() {
                    self.bump();
                    n
                } else {
                    let s = self.peek_span();
                    self.error(
                        s,
                        format!(
                            "expected associated type name, found {}",
                            self.peek().describe()
                        ),
                    );
                    return None;
                };
                // Optional bounds (`: A + B`) and default (`= T`).
                let bounds = if self.eat(&TokenKind::Colon) {
                    self.parse_bounds()
                } else {
                    Vec::new()
                };
                let default = if self.eat(&TokenKind::Eq) {
                    self.parse_type()
                } else {
                    None
                };
                self.expect(&TokenKind::Semi, "`;`")?;
                let _ = attrs;
                Some(TraitItem::AssocType {
                    name,
                    bounds,
                    default,
                })
            }
            _ => {
                let s = self.peek_span();
                self.error(
                    s,
                    format!("expected trait item, found {}", self.peek().describe()),
                );
                None
            }
        }
    }

    /// Parse `(elem, elem, ...)` for `let` destructure. Each `elem` is
    /// either an identifier (binding name), `..` / `..ident` (rest), or
    /// a nested `(...)` group (spec 3.15.4). Nested groups are desugared
    /// into a fresh temp binding plus a follow-up `LetTuple` queued on
    /// `pending_stmts`. Caller has already verified `peek() == LParen`.
    /// The last tuple's flag is whether it ended in `,` (so `(a)` is a
    /// grouping and `(a,)` a 1-tuple).
    fn parse_let_tuple_pattern(
        &mut self,
        outer_span: Span,
    ) -> Option<(Vec<String>, Option<LetTupleRest>, bool)> {
        self.expect(&TokenKind::LParen, "`(`")?;
        let mut names: Vec<String> = Vec::new();
        let mut rest: Option<LetTupleRest> = None;
        let mut trailing_comma = false;
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
                let (mut inner_names, inner_rest, inner_comma) =
                    self.parse_let_tuple_pattern(inner_span)?;
                // `((a), b)`: the inner parens only group.
                if inner_names.len() == 1 && inner_rest.is_none() && !inner_comma {
                    names.extend(inner_names.pop());
                    trailing_comma = self.eat(&TokenKind::Comma);
                    if !trailing_comma {
                        break;
                    }
                    continue;
                }
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
                    self.error(
                        s,
                        format!("expected binding name, found {}", self.peek().describe()),
                    );
                    return None;
                };
                // `n @ (x, y)`: bind `n`, then destructure it.
                if self.eat(&TokenKind::At) {
                    let inner_span = self.peek_span();
                    let sub = self.parse_let_sub_pattern(&n, inner_span)?;
                    self.pending_stmts.push(sub);
                }
                names.push(n);
            }
            trailing_comma = self.eat(&TokenKind::Comma);
            if !trailing_comma {
                break;
            }
        }
        self.expect(&TokenKind::RParen, "`)`")?;
        Some((names, rest, trailing_comma))
    }

    /// The pattern after `let name @`: an irrefutable destructure of
    /// `name` (spec 3.11 binding pattern), checked in HIR.
    fn parse_let_sub_pattern(&mut self, name: &str, span: Span) -> Option<Stmt> {
        let init = Expr {
            span,
            kind: ExprKind::Path(Path {
                segments: vec![PathSegment {
                    name: name.to_owned(),
                    generics: Vec::new(),
                }],
                span,
            }),
        };
        let pat = self.with_struct_expr(true, Self::parse_pattern_atom)?;
        Some(Stmt {
            kind: StmtKind::LetPattern {
                pat,
                ty: None,
                init,
            },
            span,
        })
    }

    /// `Path { f, g: alias, .. }` of a `let` struct destructure:
    /// the path, `(field, binding)` pairs, and whether `..` ends it.
    #[allow(clippy::type_complexity)]
    fn parse_let_struct_fields(&mut self) -> Option<(Path, Vec<(String, String)>, bool)> {
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
            let field_name = if let Some(n) = self.peek_name() {
                self.bump();
                n
            } else {
                let s = self.peek_span();
                self.error(s, "expected field name");
                return None;
            };
            let bind_name = if self.eat(&TokenKind::Colon) {
                if let TokenKind::Ident(n) = self.peek().clone() {
                    self.bump();
                    n
                } else {
                    let s = self.peek_span();
                    self.error(
                        s,
                        format!("expected rebind name, found {}", self.peek().describe()),
                    );
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
        Some((path, fields, rest))
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

    /// A function's name. Contextual keywords lex as identifiers,
    /// so `fn union` (`Set::union`) and `fn any` (`Iterator::any`) work.
    fn fn_name(&mut self) -> Option<String> {
        let TokenKind::Ident(name) = self.peek().clone() else {
            let s = self.peek_span();
            self.error(
                s,
                format!("expected function name, found {}", self.peek().describe()),
            );
            return None;
        };
        self.bump();
        Some(name)
    }

    /// `const fn` (spec 5.2.5): a plain fn carrying `CONST_FN_ATTR`.
    fn parse_const_fn(&mut self, vis: Visibility, mut attrs: Vec<Attribute>) -> Option<FnDef> {
        let span = self.peek_span();
        self.bump(); // `const`
        attrs.push(Attribute {
            path: vec![rokc_ast::CONST_FN_ATTR.to_owned()],
            body: rokc_ast::AttrBody::Empty,
            inner: false,
            span,
        });
        self.parse_fn(vis, attrs)
    }

    fn parse_fn(&mut self, vis: Visibility, attrs: Vec<Attribute>) -> Option<FnDef> {
        let mut is_async = false;
        let mut is_generator = false;
        let start = self.peek_span();
        // Modifiers in fixed order `unsafe async yield` (spec 4.1.11).
        let is_unsafe = self.eat(&TokenKind::Unsafe);
        if matches!(self.peek(), TokenKind::Async) {
            is_async = true;
            self.bump();
        }
        if matches!(self.peek(), TokenKind::Yield) {
            is_generator = true;
            self.bump();
        }
        self.expect(&TokenKind::Fn, "`fn`")?;
        let name = self.fn_name()?;
        // Optional generic parameters.
        let generics = if matches!(self.peek(), TokenKind::Lt) {
            self.parse_generic_params()
        } else {
            Generics::default()
        };
        self.expect(&TokenKind::LParen, "`(`")?;
        let untyped_mark = self.untyped_throws.len();
        let mut params = Vec::new();
        let mut attrs = attrs;
        while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
            if self.eat_c_variadic(&mut attrs) {
                break;
            }
            params.push(self.parse_param()?);
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(&TokenKind::RParen, "`)`")?;

        let mut generics = generics;
        self.desugar_variadic(&mut params);
        let throws = if matches!(self.peek(), TokenKind::Ident(n) if n == "rethrows") {
            let span = self.peek_span();
            self.bump();
            self.untyped_throws.truncate(untyped_mark);
            let errs = desugar_rethrows(&mut params, &mut generics);
            if errs.is_empty() {
                self.error(
                    span,
                    "`rethrows` needs a parameter of throwing function type \
                     (`f: fn(T) throws -> U`) (spec 4.14)",
                );
            }
            ThrowsKind::Typed(errs)
        } else {
            match self.parse_throws() {
                ThrowsKind::Untyped => ThrowsKind::Typed(vec![rokc_ast::untyped_throws_ty(start)]),
                t => t,
            }
        };
        let ret_ty = if self.eat(&TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        let where_clause = self.parse_where_clause();

        let body = if matches!(self.peek(), TokenKind::LBrace) {
            let owned = match (&self.fn_owner, self.fn_names.is_empty()) {
                (Some(o), true) => format!("{o}.{name}"),
                _ => name.clone(),
            };
            self.fn_names.push(owned);
            let b = self.parse_block();
            self.fn_names.pop();
            Some(b?)
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
            is_unsafe,
            throws,
            where_clause,
            span: start,
        })
    }

    /// `fn printf(fmt: str, ...)`: a C variadic marker (spec 8.6.10),
    /// recorded as an attribute; only last, and only in an `extern`
    /// block (checked by HIR).
    fn eat_c_variadic(&mut self, attrs: &mut Vec<Attribute>) -> bool {
        if !(matches!(self.peek(), TokenKind::DotDot)
            && matches!(self.peek_next(), Some(TokenKind::Dot)))
        {
            return false;
        }
        let span = self.peek_span();
        self.bump();
        self.bump();
        attrs.push(Attribute {
            path: vec![rokc_ast::C_VARIADIC_ATTR.to_owned()],
            body: rokc_ast::AttrBody::Empty,
            inner: false,
            span,
        });
        self.eat(&TokenKind::Comma);
        if !matches!(self.peek(), TokenKind::RParen) {
            self.error(span, "`...` must be the last parameter (spec 8.6.10)");
        }
        true
    }

    /// Spec 4.2.5: `xs: ...T` is a read-only view of the call's trailing
    /// arguments — `xs: Slice<T>` (the call site builds it), so a
    /// variadic function is not instantiated per argument count. Only
    /// the last parameter can be variadic.
    fn desugar_variadic(&mut self, params: &mut [Param]) {
        let last = params.len().saturating_sub(1);
        for (i, p) in params.iter_mut().enumerate() {
            if !p.variadic {
                continue;
            }
            if i != last {
                self.error(
                    p.span,
                    "only the last parameter can be variadic `...T` (spec 4.2.5)",
                );
                continue;
            }
            let Some(elem) = p.ty.take() else { continue };
            p.ty = Some(variadic_slice_ty(elem));
        }
    }

    /// Parse an optional `<T: Bound = Default, const N: usize>` generic
    /// parameter list. Returns empty generics when not at `<`.
    fn parse_generic_params(&mut self) -> Generics {
        let mut params: Vec<rokc_ast::GenericParam> = Vec::new();
        if !self.eat(&TokenKind::Lt) {
            return Generics { params };
        }
        while !matches!(self.peek(), TokenKind::Gt | TokenKind::Eof) {
            if matches!(self.peek_next(), Some(TokenKind::Ident(_))) && self.eat_kw("const") {
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
                    self.error(
                        s,
                        format!(
                            "expected generic param name, found {}",
                            self.peek().describe()
                        ),
                    );
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

    /// The `N` of `[T; N]` / `[v; N]`: a const expression (`3`, `N`,
    /// `M * N`, spec 2.11.5).
    fn parse_const_len(&mut self) -> Option<ConstExpr> {
        Some(match (self.peek().clone(), self.peek_next()) {
            (TokenKind::IntLit(s), Some(TokenKind::RBracket)) => {
                self.bump();
                ConstExpr::Literal(Literal::Int(s))
            }
            _ => ConstExpr::Expr(Box::new(self.with_struct_expr(false, Self::parse_expr)?)),
        })
    }

    /// Optional `where T: A + B, U::Out: C` (spec 2.10.4).
    fn parse_where_clause(&mut self) -> Vec<rokc_ast::WherePred> {
        let mut preds = Vec::new();
        if !self.eat_kw("where") {
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
        if !self.eat_kw("throws") {
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
            self.error(
                s,
                format!("expected parameter name, found {}", self.peek().describe()),
            );
            return None;
        };
        // Spec 4.2.5: `xs: ...T` — `...` precedes the element type; the
        // param is marked `variadic` (its type becomes `Slice<T>`).
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
    /// arrays, `any`, `none`, `Self`, and their `T?`.
    fn parse_type_atom(&mut self) -> Option<Ty> {
        let mut t = self.nested(Self::parse_type_atom_inner)?;
        // `T?` (spec 2.6.5): postfix, tighter than `|`. A `?` right after
        // `x as T` / `x is T` belongs to the type (propagate with
        // `(x as T)?`), but `??` there stays coalescing.
        loop {
            let layers = match self.peek() {
                TokenKind::Question => 1,
                TokenKind::QuestionQuestion if !self.in_cast_type => 2,
                _ => break,
            };
            self.bump();
            for _ in 0..layers {
                t = optional_ty(t);
            }
        }
        Some(t)
    }

    fn parse_type_atom_inner(&mut self) -> Option<Ty> {
        let start = self.peek_span();
        let kind = match self.peek().clone() {
            // `any` | `any Tr` | `any (A + B)`. The bound binds
            // tighter than `|`: `any Error | none` is `(any Error) | none`.
            TokenKind::Ident(k)
                if k == "any" && !matches!(self.peek_next(), Some(TokenKind::ColonColon)) =>
            {
                self.bump();
                match self.peek() {
                    TokenKind::Ident(_) => TyKind::AnyTrait(vec![self.parse_type_path()?]),
                    TokenKind::LParen => {
                        self.bump();
                        let mut bounds = vec![self.parse_type_path()?];
                        while self.eat(&TokenKind::Plus) {
                            bounds.push(self.parse_type_path()?);
                        }
                        self.expect(&TokenKind::RParen, "`)`")?;
                        TyKind::AnyTrait(bounds)
                    }
                    _ => TyKind::Any,
                }
            }
            TokenKind::None => {
                self.bump();
                TyKind::None
            }
            // `Self::Item`: an associated type of the impl / trait.
            TokenKind::SelfUpper if self.peek_next() == Some(TokenKind::ColonColon) => {
                self.bump();
                self.bump();
                let mut p = self.parse_type_path()?;
                p.segments.insert(
                    0,
                    PathSegment {
                        name: "Self".to_owned(),
                        generics: Vec::new(),
                    },
                );
                p.span = start;
                TyKind::Path(p)
            }
            TokenKind::SelfUpper => {
                self.bump();
                TyKind::SelfUpper
            }
            TokenKind::Bang => {
                self.bump();
                TyKind::Never
            }
            TokenKind::Unsafe
                if self.peek_next() == Some(TokenKind::Fn) || self.at_c_fn_type(1) =>
            {
                self.parse_marked_fn_type(start)?
            }
            TokenKind::Ident(_) if self.at_c_fn_type(0) => self.parse_marked_fn_type(start)?,
            TokenKind::Ident(_) => TyKind::Path(self.parse_type_path()?),
            // `<T as Tr>::X` (spec 2.13.4).
            TokenKind::Lt | TokenKind::Shl => TyKind::QPath(Box::new(self.parse_qpath()?)),
            TokenKind::Fn => {
                self.bump();
                self.expect(&TokenKind::LParen, "`(`")?;
                let args = self.nested_type_list(TokenKind::RParen)?;
                self.expect(&TokenKind::RParen, "`)`")?;
                let throws_span = self.peek_span();
                let throws = self.parse_throws();
                // `fn(..) -> R` binds tighter than `|` (spec 2.1.10):
                // `fn() -> A | B` is `(fn() -> A) | B`.
                let mut ret = if self.eat(&TokenKind::Arrow) {
                    self.parse_type_atom()?
                } else {
                    Ty {
                        kind: TyKind::Tuple(Vec::new()),
                        span: start,
                    }
                };
                let err = match throws {
                    ThrowsKind::None => None,
                    // Claimed by an enclosing `rethrows` signature, else
                    // reported at the end of the parse.
                    ThrowsKind::Untyped => {
                        self.untyped_throws.push(throws_span);
                        Some(rokc_ast::untyped_throws_ty(throws_span))
                    }
                    ThrowsKind::Typed(mut tys) if tys.len() == 1 => tys.pop(),
                    ThrowsKind::Typed(tys) => Some(Ty {
                        kind: TyKind::Sum(tys),
                        span: throws_span,
                    }),
                };
                if let Some(err) = err {
                    let span = ret.span;
                    ret = Ty {
                        kind: TyKind::Throws {
                            ok: Box::new(ret),
                            err: Box::new(err),
                        },
                        span,
                    };
                }
                // `fn(..) -> R + Send + Sync` — auto-trait bounds.
                let mut bounds = rokc_ast::FnTyBounds::default();
                while self.eat(&TokenKind::Plus) {
                    bounds.auto.push(self.parse_type_path()?);
                }
                TyKind::Fn(args, Box::new(ret), bounds)
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
                let len = self.parse_const_len()?;
                self.expect(&TokenKind::RBracket, "`]`")?;
                TyKind::Array(Box::new(elem), len)
            }
            other => {
                self.error(start, format!("expected type, found {}", other.describe()));
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
                // Spec 2.11.4: a const argument — a literal, `-lit`, or a
                // braced expression `{ M * N }`; a string names an MLIR op
                // (`__mlir_op::<"arith.addi", i32>`, bare 1.9).
                if matches!(
                    p.peek(),
                    TokenKind::IntLit(_)
                        | TokenKind::CharLit(_)
                        | TokenKind::StrLit(_)
                        | TokenKind::Minus
                        | TokenKind::True
                        | TokenKind::False
                        | TokenKind::LBrace
                ) {
                    let span = p.peek_span();
                    let e = if p.eat(&TokenKind::LBrace) {
                        let e = p.with_struct_expr(true, Self::parse_expr);
                        p.expect(&TokenKind::RBrace, "`}`")?;
                        e
                    } else {
                        p.parse_expr_bp(12)
                    };
                    let Some(e) = e else {
                        ok = false;
                        break;
                    };
                    tys.push(Ty {
                        kind: TyKind::Const(ConstExpr::Expr(Box::new(e))),
                        span,
                    });
                    if !p.eat(&TokenKind::Comma) {
                        break;
                    }
                    continue;
                }
                // `Name = Ty`: an associated-type binding (spec 2.1).
                let binding = match (p.peek().clone(), p.tokens.get(p.pos + 1).map(|t| &t.kind)) {
                    (TokenKind::Ident(name), Some(TokenKind::Eq)) => {
                        p.bump();
                        p.bump();
                        Some(name)
                    }
                    _ => None,
                };
                let Some(t) = p.parse_type() else {
                    ok = false;
                    break;
                };
                tys.push(match binding {
                    Some(name) => Ty {
                        span: t.span,
                        kind: TyKind::Binding(name, Box::new(t)),
                    },
                    None => t,
                });
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
                | TokenKind::CharLit(_)
                | TokenKind::Fn
                | TokenKind::Arrow
                | TokenKind::None
                | TokenKind::SelfUpper
                | TokenKind::Pipe
                | TokenKind::Question
                | TokenKind::QuestionQuestion => {}
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

    /// `<T as Tr>::item` (spec 2.13.4).
    fn parse_qpath(&mut self) -> Option<rokc_ast::QPath> {
        if !self.eat_opening_lt() {
            self.expect(&TokenKind::Lt, "`<`")?;
        }
        let self_ty = self.with_type_sum(false, Self::parse_type_atom)?;
        self.expect(&TokenKind::As, "`as`")?;
        let tr = self.parse_type_path()?;
        if !self.expect_closing_gt() {
            return None;
        }
        self.expect(&TokenKind::ColonColon, "`::`")?;
        let TokenKind::Ident(name) = self.peek().clone() else {
            let s = self.peek_span();
            self.error(
                s,
                format!(
                    "expected associated item name after `<.. as ..>::`, found {}",
                    self.peek().describe()
                ),
            );
            return None;
        };
        self.bump();
        Some(rokc_ast::QPath {
            self_ty,
            trait_path: tr,
            item: name,
        })
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
                self.error(
                    s,
                    format!("expected path segment, found {}", self.peek().describe()),
                );
                return None;
            };
            self.bump();
            // `Name<T1, T2>` — generic arguments accepted only when the
            // caller is parsing a type. In expression position the `<`
            // is ambiguous with comparison.
            let mut generics: Vec<Ty> = Vec::new();
            if allow_generics
                && (matches!(self.peek(), TokenKind::Shl) && !self.in_cast_type
                    || matches!(self.peek(), TokenKind::Lt)
                        && (!self.in_cast_type || self.generic_close_ahead()))
            {
                self.eat_opening_lt();
                generics = self.nested_type_list(TokenKind::Gt)?;
                if !self.expect_closing_gt() {
                    return None;
                }
            }
            segments.push(PathSegment { name, generics });
            if !self.eat(&TokenKind::ColonColon) {
                break;
            }
            // `f::<T, 3>(..)` — explicit generic arguments in an
            // expression path (spec 2.11.4); a type path takes the same
            // spelling (`__mlir_type::<"index">`, bare 1.9).
            if matches!(self.peek(), TokenKind::Lt) {
                self.bump();
                let args = self.nested_type_list(TokenKind::Gt)?;
                if !self.expect_closing_gt() {
                    return None;
                }
                if let Some(last) = segments.last_mut() {
                    last.generics = args;
                }
                if !self.eat(&TokenKind::ColonColon) {
                    break;
                }
            }
        }
        Some(Path {
            segments,
            span: start,
        })
    }

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

    /// `{ stmts }`. Inside braces a struct literal is always allowed
    /// again, even when the block itself sits in an `if`/`while` head.
    /// `let PAT [: T] = init else { .. };` (spec 3.16.4) →
    /// `let (b1, .., bn,) = match init { PAT => (b1, .., bn,), _ => else };`
    /// (one binder: a plain `let`, none: an expression statement).
    fn let_else_pattern(
        &mut self,
        pat: Pattern,
        ty: Option<Ty>,
        init: Expr,
        else_block: Block,
        start: Span,
    ) -> Stmt {
        fn binders(p: &Pattern, out: &mut Vec<String>) {
            match &p.kind {
                PatternKind::Binding { name, sub } => {
                    out.push(name.clone());
                    if let Some(s) = sub {
                        binders(s, out);
                    }
                }
                PatternKind::TypeCheck {
                    binder: Some(n), ..
                }
                | PatternKind::Rest(Some(n)) => out.push(n.clone()),
                PatternKind::Tuple(ps) | PatternKind::EnumVariant { args: ps, .. } => {
                    ps.iter().for_each(|p| binders(p, out));
                }
                PatternKind::Or(ps) => {
                    if let Some(p) = ps.first() {
                        binders(p, out);
                    }
                }
                PatternKind::Struct { fields, .. } => {
                    for f in fields {
                        match &f.pat {
                            Some(p) => binders(p, out),
                            None => out.push(f.name.clone()),
                        }
                    }
                }
                _ => {}
            }
        }
        let span = init.span;
        let path = |name: &str| Expr {
            kind: ExprKind::Path(Path {
                segments: vec![PathSegment {
                    name: name.to_string(),
                    generics: vec![],
                }],
                span,
            }),
            span,
        };
        let mut names = Vec::new();
        binders(&pat, &mut names);
        let body = match names.as_slice() {
            [one] => path(one),
            _ => Expr {
                kind: ExprKind::Tuple(names.iter().map(|n| path(n)).collect()),
                span,
            },
        };
        let scrutinee = match ty {
            Some(ty) => Expr {
                kind: ExprKind::Block(Block {
                    stmts: vec![Stmt {
                        kind: StmtKind::Let {
                            name: "__letelse_s".to_string(),
                            ty: Some(ty),
                            init,
                        },
                        span,
                    }],
                    trailing: Some(Box::new(path("__letelse_s"))),
                    span,
                    label: None,
                }),
                span,
            },
            None => init,
        };
        let else_span = else_block.span;
        let m = Expr {
            kind: ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms: vec![
                    MatchArm {
                        pat,
                        guard: None,
                        body,
                    },
                    MatchArm {
                        pat: Pattern {
                            kind: PatternKind::Wildcard,
                            span: else_span,
                        },
                        guard: None,
                        body: Expr {
                            kind: ExprKind::Block(else_block),
                            span: else_span,
                        },
                    },
                ],
            },
            span,
        };
        let kind = match names.len() {
            0 => StmtKind::Expr(m),
            1 => StmtKind::Let {
                name: names.pop().unwrap_or_default(),
                ty: None,
                init: m,
            },
            _ => {
                self.pending_stmts.push(Stmt {
                    kind: StmtKind::LetTuple {
                        names,
                        rest: None,
                        ty: None,
                        init: path("__letelse_t"),
                    },
                    span: start,
                });
                StmtKind::Let {
                    name: "__letelse_t".to_string(),
                    ty: None,
                    init: m,
                }
            }
        };
        Stmt { kind, span: start }
    }

    fn parse_block(&mut self) -> Option<Block> {
        self.nested(|p| p.with_struct_expr(true, Self::parse_block_inner))
    }

    fn parse_block_inner(&mut self) -> Option<Block> {
        let lifted = self.lifted.len();
        let block = self.parse_block_stmts()?;
        // Spec 4.10.5: a nested fn is visible in its whole block — in
        // the bodies of the fns lifted from inside it too.
        let markers: Vec<Stmt> = block
            .stmts
            .iter()
            .filter_map(|s| match &s.kind {
                StmtKind::Item(Item::Fn(f)) => {
                    rokc_ast::nested_marker_of(f).map(|(lifted, _)| Stmt {
                        kind: StmtKind::Item(Item::Fn(nested_marker(f, lifted, true))),
                        span: s.span,
                    })
                }
                _ => None,
            })
            .collect();
        if !markers.is_empty() {
            for f in &mut self.lifted[lifted..] {
                if let Some(b) = &mut f.body {
                    b.stmts.splice(0..0, markers.iter().cloned());
                }
            }
        }
        Some(block)
    }

    /// `fn name(..) { .. }` as a statement (spec 4.10): lifted to a
    /// module item `outer/name` (`outer/name/2` .. for a repeated name;
    /// `/` is in no other item name), leaving a marker statement.
    fn parse_nested_fn(&mut self) -> Option<Stmt> {
        let start = self.peek_span();
        if self.parse_visibility() != Visibility::Private {
            self.error(
                start,
                "`pub` is meaningless on a nested function: it is visible only in its block \
                 (spec 4.10.7)",
            );
        }
        let mut def = self.parse_fn(Visibility::Private, Vec::new())?;
        let outer = if self.fn_names.is_empty() {
            "main".to_owned()
        } else {
            self.fn_names.join("/")
        };
        let base = format!("{outer}/{}", def.name);
        let mut lifted = base.clone();
        let mut n = 1;
        while !self.lifted_names.insert(lifted.clone()) {
            n += 1;
            lifted = format!("{base}/{n}");
        }
        let marker = nested_marker(&def, &lifted, false);
        def.name = lifted;
        self.lifted.push(def);
        Some(Stmt {
            kind: StmtKind::Item(Item::Fn(marker)),
            span: start,
        })
    }

    /// Does a nested `fn` (`pub`, `unsafe` / `async` / `yield`) start here?
    fn at_nested_fn(&self) -> bool {
        let mut i = self.pos;
        let kind = |i: usize| self.tokens.get(i).map(|t| &t.kind);
        if matches!(kind(i), Some(TokenKind::Pub)) {
            i += 1;
            if matches!(kind(i), Some(TokenKind::LParen)) {
                i += 3;
            }
        }
        while matches!(
            kind(i),
            Some(TokenKind::Unsafe | TokenKind::Async | TokenKind::Yield)
        ) {
            i += 1;
        }
        matches!(kind(i), Some(TokenKind::Fn)) && matches!(kind(i + 1), Some(TokenKind::Ident(_)))
    }

    fn parse_block_stmts(&mut self) -> Option<Block> {
        let start = self.peek_span();
        self.expect(&TokenKind::LBrace, "`{`")?;
        let mut stmts = Vec::new();
        let mut trailing: Option<Box<Expr>> = None;
        while !matches!(self.peek(), TokenKind::RBrace | TokenKind::Eof) {
            let from = self.pos;
            // An empty statement (`;;`).
            if self.eat(&TokenKind::Semi) {
                continue;
            }
            if let Some((stmt, is_trailing)) = self.parse_stmt() {
                if is_trailing && matches!(self.peek(), TokenKind::RBrace) {
                    if let StmtKind::Trailing(expr) = stmt.kind {
                        trailing = Some(Box::new(expr));
                    } else {
                        stmts.push(stmt);
                    }
                } else {
                    if let StmtKind::Trailing(e) = &stmt.kind {
                        if !ends_stmt(e) {
                            let d =
                                self.expected(&TokenKind::Semi, "`;` after expression statement");
                            self.diagnostics.push(d);
                        }
                    }
                    stmts.push(stmt);
                }
                // Follow-ups queued by the statement (nested tuple
                // destructure, spec 3.15.4).
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
        if self.at_nested_fn() {
            return Some((self.parse_nested_fn()?, false));
        }
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
                // The flat forms below (`Point { x, y: b }`, `(a, ..rest)`,
                // `name`) have their own statements; any other irrefutable
                // pattern (`Pair(a, b)`, `Line { a: Point { x, .. }, .. }`,
                // `(n, P { x, .. })`) is a `LetPattern` (spec 3.15).
                let general = match self.peek() {
                    TokenKind::Ident(_) => {
                        matches!(
                            self.peek_next(),
                            Some(TokenKind::LParen | TokenKind::ColonColon)
                        ) && !self.peek_path_then_lbrace()
                    }
                    TokenKind::LParen => self.backtracks(|p| p.parse_let_tuple_pattern(start)),
                    _ => false,
                } || (self.peek_path_then_lbrace()
                    && self.backtracks(|p| {
                        p.parse_let_struct_fields()
                            .filter(|_| matches!(p.peek(), TokenKind::Colon | TokenKind::Eq))
                    }));
                if general {
                    let pat = self.with_struct_expr(true, Self::parse_pattern_atom)?;
                    let ty = if self.eat(&TokenKind::Colon) {
                        Some(self.parse_type()?)
                    } else {
                        None
                    };
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let init = self.parse_expr()?;
                    if self.eat(&TokenKind::Else) {
                        let else_block = self.parse_block()?;
                        self.expect(&TokenKind::Semi, "`;`")?;
                        return Some((
                            self.let_else_pattern(pat, ty, init, else_block, start),
                            false,
                        ));
                    }
                    self.expect(&TokenKind::Semi, "`;`")?;
                    return Some((
                        Stmt {
                            kind: StmtKind::LetPattern { pat, ty, init },
                            span: start,
                        },
                        false,
                    ));
                }
                // `let Point { x, y, .. } [: ty] = init;`: `let Path {`
                // can't start a plain binding, so it is a struct pattern.
                if self.peek_path_then_lbrace() {
                    let (path, fields, rest) = self.parse_let_struct_fields()?;
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
                // `let (a, b) = ..;`. Nested groups (spec 3.15.4) become
                // a chain of `LetTuple`s queued on `pending_stmts`.
                if matches!(self.peek(), TokenKind::LParen) {
                    let (mut names, rest, trailing_comma) = self.parse_let_tuple_pattern(start)?;
                    let ty = if self.eat(&TokenKind::Colon) {
                        Some(self.parse_type()?)
                    } else {
                        None
                    };
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let init = self.parse_expr()?;
                    self.expect(&TokenKind::Semi, "`;`")?;
                    // `let (a) = ..` only groups; `let (a,) = ..` is a 1-tuple.
                    let kind = if names.len() == 1 && rest.is_none() && !trailing_comma {
                        StmtKind::Let {
                            name: names.pop()?,
                            ty,
                            init,
                        }
                    } else {
                        StmtKind::LetTuple {
                            names,
                            rest,
                            ty,
                            init,
                        }
                    };
                    return Some((Stmt { kind, span: start }, false));
                }
                let name = if let TokenKind::Ident(n) = self.peek() {
                    n.clone()
                } else {
                    let s = self.peek_span();
                    self.error(
                        s,
                        format!("expected binding name, found {}", self.peek().describe()),
                    );
                    return None;
                };
                self.bump();
                // `let whole @ (a, b) = init;` → `let whole = init;` then
                // a destructure of `whole`.
                let sub = if self.eat(&TokenKind::At) {
                    let s = self.peek_span();
                    Some(self.parse_let_sub_pattern(&name, s)?)
                } else {
                    None
                };
                let ty = if self.eat(&TokenKind::Colon) {
                    Some(self.parse_type()?)
                } else {
                    None
                };
                self.expect(&TokenKind::Eq, "`=`")?;
                let init = self.parse_expr()?;
                if let Some(sub) = sub {
                    self.expect(&TokenKind::Semi, "`;`")?;
                    self.pending_stmts.push(sub);
                    return Some((
                        Stmt {
                            kind: StmtKind::Let { name, ty, init },
                            span: start,
                        },
                        false,
                    ));
                }
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
            // Spec 3.9 (Rust rule): a block-like expression in statement
            // position ends the statement — no `;` needed, and a following
            // operator starts a new statement (`if c {} -1` is two). Only
            // the postfix chain (`.m()`, `?`) continues it.
            TokenKind::If
            | TokenKind::Match
            | TokenKind::Loop
            | TokenKind::While
            | TokenKind::For
            | TokenKind::LBrace
            | TokenKind::Label(_) => {
                self.stmt_head = true;
                let expr = self.parse_expr_bp(u32::MAX)?;
                let ends = is_block_like(&expr) || matches!(self.peek(), TokenKind::RBrace);
                if !ends || self.eat(&TokenKind::Semi) {
                    if !ends {
                        self.expect(&TokenKind::Semi, "`;`")?;
                    }
                    return Some((
                        Stmt {
                            kind: StmtKind::Expr(expr),
                            span: start,
                        },
                        false,
                    ));
                }
                Some((
                    Stmt {
                        kind: StmtKind::Trailing(expr),
                        span: start,
                    },
                    true,
                ))
            }
            _ => {
                let expr = self.parse_expr()?;
                if matches!(self.peek(), TokenKind::Eq) {
                    self.bump();
                    let value = self.parse_expr()?;
                    // Spec 4.6.2 writes `|| { count = count + 1 }`: a
                    // trailing assignment (`}` follows) may omit its `;`
                    // (3.9.1 otherwise requires it).
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
                // Compound assignment `target op= value;` (HIR: the
                // `*Assign` trait's method, else `target = target op
                // value`). Spec 3.4.3: the target must be evaluated once —
                // index / receiver sub-expressions that are not plain
                // variables or literals are hoisted into temps first:
                // `a[f()] += 1` → `{ let t = f(); a[t] += 1; }`.
                if let Some(op) = compound_assign_op(self.peek()) {
                    self.bump();
                    let value = self.parse_expr()?;
                    self.expect(&TokenKind::Semi, "`;`")?;
                    let mut stmts = Vec::new();
                    let target = self.hoist_place(expr, &mut stmts);
                    let assign = Stmt {
                        kind: StmtKind::CompoundAssign {
                            target,
                            op: format!("{op}="),
                            value,
                        },
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
            let e = self.parse_expr_bp(0)?;
            Some(Box::new(self.parse_catch_tail(e)?))
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
            span: self.to_prev(span),
            kind: ExprKind::Range {
                start,
                end,
                inclusive,
            },
        })
    }

    /// Postfix `catch pat? { .. }` arms and `finally { .. }` around `body`
    /// (spec 4.14). They bind loosest, so `try a() + b() catch _ { 0 }`
    /// handles both calls.
    fn parse_catch_tail(&mut self, body: Expr) -> Option<Expr> {
        if !(self.at_kw("catch") || self.at_kw("finally")) {
            return Some(body);
        }
        let mut catches: Vec<CatchArm> = Vec::new();
        while self.at_kw("catch") {
            let span = self.peek_span();
            self.bump();
            let pat = if matches!(self.peek(), TokenKind::LBrace) {
                Pattern {
                    kind: PatternKind::Wildcard,
                    span,
                }
            } else {
                // `catch E { code, .. } { body }`: a struct pattern when a
                // second block follows the first.
                let struct_pat = self.braces_then_block();
                self.with_struct_expr(struct_pat, Self::parse_pattern)?
            };
            let arm_body = self.parse_block()?;
            catches.push(CatchArm {
                pat,
                body: arm_body,
            });
        }
        let finally = if self.eat_kw("finally") {
            Some(self.parse_block()?)
        } else {
            None
        };
        Some(Expr {
            span: self.to_prev(body.span),
            kind: ExprKind::Catch {
                body: Box::new(body),
                catches,
                finally,
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
        let chain = self.chain;
        let r = self.nested(|p| p.parse_expr_bp_inner(min_bp));
        self.chain = chain;
        r
    }

    fn parse_expr_bp_inner(&mut self, min_bp: u32) -> Option<Expr> {
        let mut lhs = if let Some((sym, span)) = self.peek_op_symbol(Fixity::Prefix) {
            let (prec, _) = self.ext.level(&sym, Fixity::Prefix)?;
            self.bump();
            let rhs = self.parse_expr_bp(prec)?;
            Expr {
                kind: ExprKind::OpPrefix {
                    op: sym,
                    operand: Box::new(rhs),
                },
                span: self.to_prev(span),
            }
        } else {
            self.parse_primary()?
        };

        // Tracks the precedence of the most recently consumed non-associative
        // op so we can reject chains like `a < b < c` (spec 3.2.5).
        let mut last_none_prec: Option<u32> = None;

        loop {
            self.chain_link()?;
            // Spec 3.2.3: `as` / `is` sit at level 11, left-assoc — below
            // prefix unary (`-x as i64` is `(-x) as i64`), above arithmetic.
            if matches!(self.peek(), TokenKind::As | TokenKind::Is) {
                if CAST_PREC < min_bp {
                    break;
                }
                let is_cast = matches!(self.peek(), TokenKind::As);
                self.bump();
                let ty_span = self.peek_span();
                let ty = self.parse_cast_type()?;
                let span = lhs.span;
                let kind = if is_cast {
                    ExprKind::Cast(Box::new(lhs), ty)
                } else {
                    // Spec 2.2.5: `v is T` — runtime type test.
                    ExprKind::Is(
                        Box::new(lhs),
                        rokc_ast::Pattern {
                            kind: rokc_ast::PatternKind::TypeCheck { binder: None, ty },
                            span: ty_span,
                        },
                    )
                };
                lhs = Expr {
                    kind,
                    span: self.to_prev(span),
                };
                continue;
            }

            let Some((sym, _)) = self.peek_op_symbol(Fixity::Infix) else {
                break;
            };
            // `??` is a language-level desugar (spec 3.8.4), level 1,
            // right-assoc.
            if sym == "??" {
                if COALESCE_PREC < min_bp {
                    break;
                }
                self.bump();
                let rhs = self.parse_expr_bp(COALESCE_PREC)?;
                let span = self.to_prev(lhs.span);
                lhs = Expr {
                    kind: ExprKind::NullishCoalesce(Box::new(lhs), Box::new(rhs)),
                    span,
                };
                continue;
            }
            let Some((prec, assoc)) = self.ext.level(&sym, Fixity::Infix) else {
                break;
            };
            let (left_bp, right_bp) = match assoc {
                Assoc::Left | Assoc::None => (prec, prec + 1),
                Assoc::Right => (prec + 1, prec),
            };
            if left_bp < min_bp {
                break;
            }
            // Spec 3.2.5: non-associative ops don't chain. Without this
            // the loop would build `(a < b) < c`.
            if last_none_prec == Some(prec) {
                let span = self.peek_span();
                self.error(
                    span,
                    format!(
                        "non-associative operator `{sym}` cannot be chained \
                         (parenthesise to disambiguate)"
                    ),
                );
            }
            self.bump();
            let rhs = self.parse_expr_bp(right_bp)?;
            let span = self.to_prev(lhs.span);
            lhs = Expr {
                kind: ExprKind::OpInfix {
                    op: sym,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
            last_none_prec = matches!(assoc, Assoc::None).then_some(prec);
        }

        Some(lhs)
    }

    /// The current token as an operator symbol for `fixity`. Tokens that
    /// are also syntax (`|` in closure params, `<` in generic args) are
    /// the caller's to filter.
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
            (TokenKind::MathOp('√'), Fixity::Prefix) => "√".into(),
            (TokenKind::MathOp(c), Fixity::Infix) if *c != '√' => c.to_string(),
            (TokenKind::ExtOp(s), f) if self.ext.levels.contains_key(&(s.clone(), f)) => s.clone(),
            _ => return None,
        };
        Some((sym, tok.span))
    }

    /// `cfg!(pred)` (spec 6.3.5): a `bool` literal, folded here. Without
    /// a build's cfg (tools) it reads as the empty environment.
    fn cfg_macro(&mut self) -> Option<Expr> {
        let start = self.peek_span();
        let at = |k: usize| self.tokens.get(self.pos + k).map(|t| &t.kind);
        if self.pending.is_some()
            || !matches!(at(0), Some(TokenKind::Ident(n)) if n == "cfg")
            || at(1) != Some(&TokenKind::Bang)
            || at(2) != Some(&TokenKind::LParen)
        {
            return None;
        }
        self.bump();
        self.bump();
        let body = self.parse_attr_body();
        let value = match &body {
            AttrBody::Args(args) if args.len() == 1 => {
                if let Some(why) = crate::cfg::check_pred(&args[0]) {
                    self.error(start, why);
                }
                self.cfg.as_ref().is_some_and(|env| env.eval(&args[0]))
            }
            _ => {
                self.error(start, "`cfg!` takes exactly one predicate".to_owned());
                false
            }
        };
        Some(Expr {
            kind: ExprKind::Literal(Literal::Bool(value)),
            span: start,
        })
    }

    #[allow(clippy::cognitive_complexity)] // one arm per primary-expression token
    fn parse_primary(&mut self) -> Option<Expr> {
        let stmt_head = std::mem::take(&mut self.stmt_head);
        if let Some(e) = self.try_magic_literal().or_else(|| self.cfg_macro()) {
            return Some(e);
        }
        let start = self.peek_span();
        let kind = match self.peek().clone() {
            // Spec 2.13.4: `<Type as Trait>::method(...)`. At the start of
            // a primary, `<` cannot begin a comparison.
            TokenKind::Lt => ExprKind::QPath(Box::new(self.parse_qpath()?)),
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
            TokenKind::FStrStart(_) => self.parse_fstring(),
            TokenKind::Unsafe => {
                // Spec 4.15.2 `unsafe { ... }`.
                self.bump();
                if !matches!(self.peek(), TokenKind::LBrace) {
                    self.error(start, "expected `{` after `unsafe`");
                    return None;
                }
                ExprKind::Unsafe(self.parse_block()?)
            }
            // Spec 3.17: `using a = e, b = f { body }` is
            // `{ let a = e; { let b = f; { body } finally { b.drop(); } }
            // finally { a.drop(); } }` — resources drop in reverse order on
            // every way out of the block.
            TokenKind::Using => {
                self.bump();
                // Spec 3.17.1 `using_binding ::= pattern "=" expr`: a name,
                // or any irrefutable pattern over a temp that is dropped.
                let mut bindings: Vec<(String, Span, Expr, Option<Pattern>)> = Vec::new();
                loop {
                    let span = self.peek_span();
                    let (name, pat) = match self.peek().clone() {
                        TokenKind::Ident(name) if self.peek_next() == Some(TokenKind::Eq) => {
                            self.bump();
                            (name, None)
                        }
                        _ => {
                            let pat = self.with_struct_expr(true, Self::parse_pattern_atom)?;
                            (format!("#using{}", self.pos), Some(pat))
                        }
                    };
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let init = self.with_struct_expr(false, Self::parse_expr)?;
                    bindings.push((name, span, init, pat));
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
                let mut body = self.parse_block()?;
                // The patterns bind in source order, before the body.
                let lets: Vec<Stmt> = bindings
                    .iter()
                    .filter_map(|(name, span, _, pat)| {
                        Some(Stmt {
                            kind: StmtKind::LetPattern {
                                pat: pat.clone()?,
                                ty: None,
                                init: Expr {
                                    span: *span,
                                    kind: ExprKind::Path(Path {
                                        segments: vec![PathSegment {
                                            name: name.clone(),
                                            generics: Vec::new(),
                                        }],
                                        span: *span,
                                    }),
                                },
                            },
                            span: *span,
                        })
                    })
                    .collect();
                body.stmts.splice(0..0, lets);
                let mut inner = Expr {
                    span: start,
                    kind: ExprKind::Block(body),
                };
                for (name, span, init, _) in bindings.into_iter().rev() {
                    let path = |name: &str| Expr {
                        span,
                        kind: ExprKind::Path(Path {
                            segments: vec![PathSegment {
                                name: name.to_owned(),
                                generics: Vec::new(),
                            }],
                            span,
                        }),
                    };
                    let drop_call = Stmt {
                        kind: StmtKind::Expr(Expr {
                            span,
                            kind: ExprKind::MethodCall {
                                receiver: Box::new(path(&name)),
                                method: rokc_ast::USING_DROP_METHOD.to_owned(),
                                type_args: Vec::new(),
                                args: Vec::new(),
                                trailing_closure: None,
                            },
                        }),
                        span,
                    };
                    let guarded = Expr {
                        span: start,
                        kind: ExprKind::Catch {
                            body: Box::new(inner),
                            catches: Vec::new(),
                            finally: Some(Block {
                                stmts: vec![drop_call],
                                trailing: None,
                                span,
                                label: None,
                            }),
                        },
                    };
                    inner = Expr {
                        span: start,
                        kind: ExprKind::Block(Block {
                            stmts: vec![Stmt {
                                kind: StmtKind::Let {
                                    name,
                                    ty: None,
                                    init,
                                },
                                span,
                            }],
                            trailing: Some(Box::new(guarded)),
                            span: start,
                            label: None,
                        }),
                    };
                }
                inner.kind
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
                if let Some(lit) = self.try_set_or_dict() {
                    lit
                } else {
                    ExprKind::Block(self.parse_block()?)
                }
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
                        let is_await = self.eat(&TokenKind::Await);
                        let pat = self.parse_pattern()?;
                        self.expect_kw("in")?;
                        let iter = self.with_struct_expr(false, Self::parse_expr)?;
                        let body = self.parse_block()?;
                        ExprKind::For {
                            label: Some(label_name),
                            pat,
                            iter: Box::new(iter),
                            body,
                            is_await,
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
                // Spec 4.13.5: `for await pat in stream`.
                let is_await = self.eat(&TokenKind::Await);
                let pat = self.parse_pattern()?;
                self.expect_kw("in")?;
                let iter = self.with_struct_expr(false, Self::parse_expr)?;
                let body = self.parse_block()?;
                ExprKind::For {
                    label: None,
                    pat,
                    iter: Box::new(iter),
                    body,
                    is_await,
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
                // `try e` / `try? e` / `try! e` covers the whole expression
                // to its right, up to a `catch` / `finally` (attached
                // around the result by `parse_catch_tail`).
                let try_end = self.peek_span().end;
                self.bump();
                // `try!` is one word: `try !x` tries the negation.
                let glued = self.peek_span().start == try_end;
                let kind = if self.eat(&TokenKind::Question) {
                    TryKind::Optional
                } else if glued && self.eat(&TokenKind::Bang) {
                    TryKind::Force
                } else {
                    TryKind::Plain
                };
                let operand = self.parse_expr_bp(0)?;
                ExprKind::Try {
                    kind,
                    operand: Box::new(operand),
                }
            }
            TokenKind::While => {
                self.bump();
                // `while let pat = expr { body }` desugars to
                // `loop { match expr { pat => body, _ => break } }`.
                if self.eat(&TokenKind::Let) {
                    let (pat, destructure) = self.parse_let_cond_pattern()?;
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let scrutinee = self.with_struct_expr(false, Self::parse_expr)?;
                    let mut body_block = self.parse_block()?;
                    body_block.stmts.splice(0..0, destructure);
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
                    let (pat, destructure) = self.parse_let_cond_pattern()?;
                    self.expect(&TokenKind::Eq, "`=`")?;
                    let scrutinee = self.with_struct_expr(false, Self::parse_expr)?;
                    let mut then_block = self.parse_block()?;
                    then_block.stmts.splice(0..0, destructure);
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
                // Spec 2.10: `Pair<i32, i32> { a: 5, b: 7 }`. `<` is a
                // comparison unless a balanced `>` is followed by `{` or
                // `(`. The args attach to the last path segment.
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
                } else if let Some(closure) = self.paren_less_trailing_closure() {
                    // `f |x| { .. }` → `f(|x| { .. })` (spec 4.8.1).
                    ExprKind::Call {
                        callee: Box::new(Expr {
                            span: start,
                            kind: ExprKind::Path(path),
                        }),
                        args: Vec::new(),
                        trailing_closure: Some(closure),
                    }
                } else {
                    ExprKind::Path(path)
                }
            }
            TokenKind::SelfLower => {
                self.bump();
                ExprKind::SelfLower
            }
            // `Self::NAME` / `Self::f(..)` inside an impl.
            TokenKind::SelfUpper if matches!(self.peek_next(), Some(TokenKind::ColonColon)) => {
                self.bump();
                self.bump();
                let mut rest = self.parse_path()?;
                rest.segments.insert(
                    0,
                    PathSegment {
                        name: "Self".to_owned(),
                        generics: Vec::new(),
                    },
                );
                rest.span = start;
                ExprKind::Path(rest)
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
                self.parse_capture_closure()?
            }
            TokenKind::LBracket => {
                self.bump();
                let (mut items, trailing_comma) =
                    self.with_struct_expr(true, |p| p.expr_list(&TokenKind::RBracket))?;
                // `[v; N]` repeat literal (spec 2.11).
                if items.len() == 1 && !trailing_comma && self.eat(&TokenKind::Semi) {
                    let len = self.parse_const_len()?;
                    self.expect(&TokenKind::RBracket, "`]`")?;
                    ExprKind::ArrayRepeat {
                        value: Box::new(items.pop()?),
                        len,
                    }
                } else {
                    self.expect(&TokenKind::RBracket, "`]`")?;
                    ExprKind::List(items)
                }
            }
            // Spec 4.12.1 / 4.13.1: `async { }`, `async yield { }`, and
            // the closure modifiers `async ||` / `async yield ||`.
            TokenKind::Async => {
                self.bump();
                let is_generator = self.eat(&TokenKind::Yield);
                match self.peek() {
                    TokenKind::LBrace => {
                        let b = self.parse_block()?;
                        if is_generator {
                            ExprKind::AsyncYieldBlock(b)
                        } else {
                            ExprKind::AsyncBlock(b)
                        }
                    }
                    TokenKind::Pipe | TokenKind::PipePipe | TokenKind::LBracket => {
                        self.coro_closure(true, is_generator)?
                    }
                    _ => {
                        self.error(start, "expected `{`, `|` or `fn` after `async`");
                        return None;
                    }
                }
            }
            TokenKind::Await => {
                // Spec 4.12.2: prefix `await expr`.
                self.bump();
                let inner = self.parse_expr_bp(0)?;
                ExprKind::Await(Box::new(inner))
            }
            // Spec 4.11.7: `yield {` is a generator block, `yield |` a
            // generator closure, anything else the `yield` statement.
            TokenKind::Yield if matches!(self.peek_next(), Some(TokenKind::LBrace)) => {
                self.bump();
                ExprKind::YieldBlock(self.parse_block()?)
            }
            TokenKind::Yield
                if matches!(
                    self.peek_next(),
                    Some(TokenKind::Pipe | TokenKind::PipePipe)
                ) || (matches!(self.peek_next(), Some(TokenKind::LBracket))
                    && matches!(
                        self.tokens.get(self.pos + 2).map(|t| &t.kind),
                        Some(TokenKind::Ref)
                    )) =>
            {
                self.bump();
                self.coro_closure(false, true)?
            }
            TokenKind::Yield => {
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
                self.error(
                    start,
                    format!("expected expression, found {}", other.describe()),
                );
                return None;
            }
        };
        let mut expr = Expr {
            kind,
            span: self.to_prev(start),
        };

        // Postfix chain: calls, members, indexing, `?`, `?.`. After a
        // `?.`, member / index links join its tail (spec 3.8.8).
        let mut chain_open = false;
        loop {
            expr.span = self.to_prev(expr.span);
            if chain_open {
                match fold_chain(expr) {
                    Ok(e) => expr = e,
                    Err(e) => {
                        expr = e;
                        chain_open = false;
                    }
                }
            }
            self.chain_link()?;
            match self.peek() {
                TokenKind::LParen | TokenKind::LBracket if stmt_head && is_block_like(&expr) => {
                    break;
                }
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
                TokenKind::Dot if self.peek_next() == Some(TokenKind::LParen) => {
                    // `f.(xs)`: function broadcast (spec 3.3.3).
                    self.bump();
                    self.bump();
                    let args = self.parse_call_args()?;
                    self.expect(&TokenKind::RParen, "`)`")?;
                    expr = Expr {
                        span: expr.span,
                        kind: ExprKind::Broadcast {
                            callee: Box::new(expr),
                            args,
                        },
                    };
                }
                TokenKind::Dot => {
                    self.bump();
                    let name = match self.peek().clone() {
                        _ if self.peek_name().is_some() => {
                            let n = self.peek_name().unwrap_or_default();
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
                            self.error(
                                s,
                                format!(
                                    "expected field or method name after `.`, found {}",
                                    self.peek().describe()
                                ),
                            );
                            return None;
                        }
                    };
                    // `x.m::<T>(..)`: explicit generic arguments (spec 3.5).
                    let mut type_args = Vec::new();
                    if matches!(self.peek(), TokenKind::ColonColon)
                        && self.peek_next() == Some(TokenKind::Lt)
                    {
                        self.bump();
                        self.bump();
                        type_args = self.nested_type_list(TokenKind::Gt)?;
                        if !self.expect_closing_gt() {
                            return None;
                        }
                        if !matches!(self.peek(), TokenKind::LParen) {
                            let s = self.peek_span();
                            self.error(s, "expected `(` after a method's `::<..>`");
                            return None;
                        }
                    }
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
                                type_args,
                                args,
                                trailing_closure,
                            },
                        };
                    } else if let Some(closure) = self.paren_less_trailing_closure() {
                        // `xs.map |x| { .. }` (spec 4.8.1).
                        expr = Expr {
                            span: expr.span,
                            kind: ExprKind::MethodCall {
                                receiver: Box::new(expr),
                                method: name,
                                type_args,
                                args: Vec::new(),
                                trailing_closure: Some(closure),
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
                    // Spec 3.6.2 slicing: `a[start? : end? (: step?)?]`.
                    if let Some(slice) = self.with_struct_expr(true, |p| p.parse_slice(&expr)) {
                        expr = slice?;
                        continue;
                    }
                    let (indices, _) =
                        self.with_struct_expr(true, |p| p.expr_list(&TokenKind::RBracket))?;
                    if matches!(self.peek(), TokenKind::Colon | TokenKind::ColonColon) {
                        self.mixed_index_error();
                        return None;
                    }
                    if indices.is_empty() {
                        let s = self.peek_span();
                        self.error(s, "expected index expression");
                    }
                    self.expect(&TokenKind::RBracket, "`]`")?;
                    // Spec 3.6.1: `m[i, j]` is `m[(i, j)]` (`Index<(I, J)>`).
                    let span = expr.span;
                    let idx = if indices.len() == 1 {
                        indices.into_iter().next()?
                    } else {
                        let at = indices.first().map_or(span, |e| e.span);
                        Expr {
                            span: at,
                            kind: ExprKind::Tuple(indices),
                        }
                    };
                    expr = Expr {
                        span,
                        kind: ExprKind::Index(Box::new(expr), Box::new(idx)),
                    };
                }
                TokenKind::Question => {
                    self.bump();
                    expr = Expr {
                        span: expr.span,
                        kind: ExprKind::TryQ(Box::new(expr)),
                    };
                }
                // A registered postfix extension token (`x°`): the postfix
                // row (level 13) with `?` and member access (spec 6.7.1).
                TokenKind::ExtOp(sym)
                    if self
                        .ext
                        .levels
                        .contains_key(&(sym.clone(), Fixity::Postfix)) =>
                {
                    let op = sym.clone();
                    self.bump();
                    expr = Expr {
                        span: expr.span,
                        kind: ExprKind::OpPostfix {
                            op,
                            operand: Box::new(expr),
                        },
                    };
                }
                TokenKind::QuestionDot => {
                    self.bump();
                    let name = match self.peek().clone() {
                        _ if self.peek_name().is_some() => {
                            let n = self.peek_name().unwrap_or_default();
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
                                    vec![AccessTail::TupleField(idx)],
                                ),
                            };
                            chain_open = true;
                            continue;
                        }
                        _ => {
                            let s = self.peek_span();
                            self.error(
                                s,
                                format!(
                                    "expected field or method name after `?.`, found {}",
                                    self.peek().describe()
                                ),
                            );
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
                        kind: ExprKind::QuestionDot(Box::new(expr), vec![tail]),
                    };
                    chain_open = true;
                }
                _ => break,
            }
        }
        if chain_open {
            expr = fold_chain(expr).unwrap_or_else(|e| e);
        }
        expr.span = self.to_prev(expr.span);
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

    /// Spec 6.5.6: `{ k: v, .. }` is a dict, `{ a, b, .. }` a set (two
    /// or more items, or a trailing comma); anything else (`{}`, `{ e }`,
    /// statements) is a block. Decided by parsing the first expression
    /// speculatively and looking at the token after it.
    fn try_set_or_dict(&mut self) -> Option<ExprKind> {
        let (pos, pending, n_diags) = (self.pos, self.pending.clone(), self.diagnostics.len());
        let n_lifted = self.lifted.len();
        let rewind = |p: &mut Self| {
            p.pos = pos;
            p.pending.clone_from(&pending);
            p.diagnostics.truncate(n_diags);
            p.lifted.truncate(n_lifted);
        };
        self.bump(); // `{`
        // Only a simple-looking first item is tried, so nested blocks
        // (`{ if .. { .. } }`) aren't re-parsed exponentially; a set /
        // dict whose first item starts with a keyword parses as a block.
        let first = if matches!(
            self.peek(),
            TokenKind::IntLit(_)
                | TokenKind::FloatLit(_)
                | TokenKind::CharLit(_)
                | TokenKind::StrLit(_)
                | TokenKind::RawStrLit(_)
                | TokenKind::Ident(_)
                | TokenKind::True
                | TokenKind::False
                | TokenKind::Minus
                | TokenKind::LParen
                | TokenKind::LBracket
        ) {
            self.with_struct_expr(true, Self::parse_expr)
        } else {
            None
        };
        let kind = match (first, self.peek()) {
            (Some(k), TokenKind::Colon) => {
                self.bump();
                let mut pairs = Vec::new();
                let mut key = k;
                loop {
                    let v = self.with_struct_expr(true, Self::parse_expr)?;
                    pairs.push((key, v));
                    if !self.eat(&TokenKind::Comma) || matches!(self.peek(), TokenKind::RBrace) {
                        break;
                    }
                    key = self.with_struct_expr(true, Self::parse_expr)?;
                    self.expect(&TokenKind::Colon, "`:` in a dict literal")?;
                }
                ExprKind::Dict(pairs)
            }
            (Some(first), TokenKind::Comma) => {
                self.bump();
                let (mut rest, _) =
                    self.with_struct_expr(true, |p| p.expr_list(&TokenKind::RBrace))?;
                rest.insert(0, first);
                ExprKind::Set(rest)
            }
            _ => {
                rewind(self);
                return None;
            }
        };
        self.expect(&TokenKind::RBrace, "`}`")?;
        Some(kind)
    }

    /// After `[`: a slice `start? : end? (: step?)? ]` on `target`, or
    /// `None` (nothing consumed) when the brackets hold a plain index.
    #[allow(clippy::option_option)] // outer: is a slice; inner: parsed ok
    fn parse_slice(&mut self, target: &Expr) -> Option<Option<Expr>> {
        let save = self.pos;
        let colon = |p: &Self| matches!(p.peek(), TokenKind::Colon | TokenKind::ColonColon);
        let start = if colon(self) {
            None
        } else {
            let (saved_diags, n_lifted) = (self.diagnostics.len(), self.lifted.len());
            let e = self.parse_expr();
            if e.is_none() || !colon(self) {
                self.pos = save;
                self.diagnostics.truncate(saved_diags);
                self.lifted.truncate(n_lifted);
                return None;
            }
            e.map(Box::new)
        };
        let opt = |p: &mut Self| {
            if matches!(p.peek(), TokenKind::Colon | TokenKind::RBracket) {
                Some(None)
            } else {
                p.parse_expr().map(|e| Some(Box::new(e)))
            }
        };
        // `a::k` lexes `::` as one token: no end, then the step.
        let (end, has_step) = if self.eat(&TokenKind::ColonColon) {
            (None, true)
        } else {
            self.bump(); // `:`
            let Some(end) = opt(self) else {
                return Some(None);
            };
            (end, self.eat(&TokenKind::Colon))
        };
        let step = if has_step {
            let Some(step) = opt(self) else {
                return Some(None);
            };
            step
        } else {
            None
        };
        if matches!(self.peek(), TokenKind::Comma) {
            self.mixed_index_error();
            return Some(None);
        }
        if self.expect(&TokenKind::RBracket, "`]`").is_none() {
            return Some(None);
        }
        Some(Some(Expr {
            span: target.span,
            kind: ExprKind::Slice {
                target: Box::new(target.clone()),
                start,
                end,
                step,
            },
        }))
    }

    /// Spec 3.6.3: one bracket either indexes (`,`) or slices (`:`).
    fn mixed_index_error(&mut self) {
        let s = self.peek_span();
        self.error(
            s,
            "one `[..]` cannot both index with `,` and slice with `:` (spec 3.6.3); \
             slice and index in separate brackets (`m[a:b][c]`)",
        );
    }

    /// `e, e, ...` up to (not consuming) `close`. Returns the items and
    /// whether the list ended with a trailing comma.
    fn expr_list(&mut self, close: &TokenKind) -> Option<(Vec<Expr>, bool)> {
        let mut items = Vec::new();
        let mut trailing_comma = false;
        while std::mem::discriminant(self.peek()) != std::mem::discriminant(close)
            && !matches!(self.peek(), TokenKind::Eof)
        {
            if *close == TokenKind::RBracket
                && matches!(self.peek(), TokenKind::Colon | TokenKind::ColonColon)
            {
                break;
            }
            items.push(self.parse_expr()?);
            trailing_comma = self.eat(&TokenKind::Comma);
            if !trailing_comma {
                break;
            }
        }
        Some((items, trailing_comma))
    }

    /// Spec 4.8: trailing closure attached to a call. A `|...|` or
    /// `{ ... }` immediately after the closing `)` of the call becomes
    /// the last argument (408.6); a 0-arg trailing closure is spelled
    /// `{ ... }`, so `||` there is the logical-or operator. Returns
    /// `None` when no trailing closure is present.
    ///
    /// `{ ... }` is gated on `struct_expr_allowed`: in a control-flow
    /// head the brace is the construct's body, not a 0-arg closure.
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
            TokenKind::Pipe => {
                let span = self.peek_span();
                let kind = self.parse_closure_expr()?;
                Some(Some(Box::new(Expr { span, kind })))
            }
            _ => Some(None),
        }
    }

    /// `[ref x, y] |..| body` — a closure with a capture list (spec 4.6.2).
    fn parse_capture_closure(&mut self) -> Option<ExprKind> {
        self.bump(); // `[`
        let mut captures: Vec<rokc_ast::CaptureSpec> = Vec::new();
        while !matches!(self.peek(), TokenKind::RBracket | TokenKind::Eof) {
            if self.eat(&TokenKind::Ref) {
                let name = if let TokenKind::Ident(n) = self.peek().clone() {
                    self.bump();
                    n
                } else {
                    let s = self.peek_span();
                    self.error(
                        s,
                        format!(
                            "expected capture name after `ref`, found {}",
                            self.peek().describe()
                        ),
                    );
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
        Some(closure_kind)
    }

    /// `async ||` / `yield ||` / `async yield ||` closure.
    fn coro_closure(&mut self, is_async: bool, is_generator: bool) -> Option<ExprKind> {
        let mut k = if matches!(self.peek(), TokenKind::LBracket) {
            self.parse_capture_closure()?
        } else {
            self.parse_closure_expr()?
        };
        if let ExprKind::Closure {
            is_async: a,
            is_generator: g,
            ..
        } = &mut k
        {
            *a = is_async;
            *g = is_generator;
        }
        Some(k)
    }

    /// `|args| body`, `|args| -> R body` or `|| body`.
    fn parse_closure_expr(&mut self) -> Option<ExprKind> {
        let (params, ret_ty) = self.parse_closure_head()?;
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

    /// Spec 4.8.1 `primary trailing_closure` without the call's `( )`:
    /// `xs.map |x| { .. }` / `f |x| { .. }`. A `|` after a callee is the
    /// closure only when `|params| (-> R)? {` follows — the trailing body
    /// is always a block — else it stays the `|` operator. `||` stays
    /// logical-or (the 0-parameter form is `f { .. }`). Off in a
    /// control-flow head, like the `{ .. }` form.
    fn paren_less_trailing_closure(&mut self) -> Option<Box<Expr>> {
        if !self.struct_expr_allowed || !matches!(self.peek(), TokenKind::Pipe) {
            return None;
        }
        let not_closure = self.backtracks(|p| {
            p.parse_closure_head()?;
            matches!(p.peek(), TokenKind::LBrace).then_some(())
        });
        if not_closure {
            return None;
        }
        let span = self.peek_span();
        let (params, ret_ty) = self.parse_closure_head()?;
        let body_span = self.peek_span();
        let block = self.parse_block()?;
        Some(Box::new(Expr {
            span,
            kind: ExprKind::Closure {
                captures: Vec::new(),
                params,
                ret_ty,
                body: Box::new(Expr {
                    span: body_span,
                    kind: ExprKind::Block(block),
                }),
                is_async: false,
                is_generator: false,
            },
        }))
    }

    /// `|params|` / `||`, then an optional `-> R`.
    fn parse_closure_head(&mut self) -> Option<(Vec<Param>, Option<Ty>)> {
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
        Some((params, ret_ty))
    }

    /// `Path<...>` in expression position: true when a balanced `>` is
    /// followed by `{` or `(` (a struct literal or turbofish call).
    /// Stops at tokens a generic-arg list can't hold, which rules out
    /// comparisons and keeps the lookahead short.
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

    /// `Path { .. }`: struct literal or 0-arg trailing closure? Looks two
    /// tokens past the `{` without consuming.
    ///   `{ }`              → struct init (empty/unit)
    ///   `{ .. }`           → struct init (rest)
    ///   `{ ident : ... }`  → struct init (named field)
    ///   `{ ident , ... }`  → struct init (shorthand)
    ///   `{ ident } `       → struct init (single shorthand)
    ///   anything else      → trailing closure body
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

    /// `{ field: expr, .., ..base? }` after a path, from the `{`.
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
            let name = if let Some(n) = self.peek_name() {
                self.bump();
                n
            } else {
                let s = self.peek_span();
                self.error(s, "expected field name");
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
            TokenKind::CharLit(s) => {
                self.bump();
                Some(Literal::Char(s))
            }
            TokenKind::CCharLit(s) => {
                self.bump();
                Some(Literal::CChar(s))
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

    /// `(p, .., q)` after a variant path (empty without parentheses).
    /// `..` stands for the fields not written.
    fn parse_variant_pattern_args(&mut self) -> Option<Vec<Pattern>> {
        Some(if self.eat(&TokenKind::LParen) {
            let mut sub = Vec::new();
            while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
                // `V(a, ..)`: the remaining fields, any value.
                if matches!(self.peek(), TokenKind::DotDot) {
                    let span = self.peek_span();
                    self.bump();
                    sub.push(Pattern {
                        kind: PatternKind::Rest(None),
                        span,
                    });
                } else {
                    sub.push(self.parse_pattern()?);
                }
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(&TokenKind::RParen, "`)`")?;
            sub
        } else {
            Vec::new()
        })
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
            let name = if let Some(n) = self.peek_name() {
                self.bump();
                n
            } else {
                let s = self.peek_span();
                self.error(s, "expected field name");
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

    /// After a binding's name: `name` or `name @ pat` (spec 3.11 binds
    /// the whole value matched by `pat`).
    fn parse_binding_rest(&mut self, name: String) -> Option<PatternKind> {
        let sub = if self.eat(&TokenKind::At) {
            Some(Box::new(self.parse_pattern_atom()?))
        } else {
            None
        };
        Some(PatternKind::Binding { name, sub })
    }

    fn parse_pattern_atom(&mut self) -> Option<Pattern> {
        self.nested(Self::parse_pattern_atom_inner)
    }

    fn parse_pattern_atom_inner(&mut self) -> Option<Pattern> {
        let span = self.peek_span();
        let num = match self.peek() {
            TokenKind::Minus => self.tokens.get(self.pos + 1).map(|t| &t.kind),
            k => Some(k),
        };
        if let Some(TokenKind::IntLit(t) | TokenKind::FloatLit(t)) = num {
            if let Some(sfx) = literal::user_suffix(t) {
                self.error(
                    span,
                    format!(
                        "a `{sfx}` suffix literal is a `#[literal]` handler call and can't be a \
                         pattern (spec 6.5)"
                    ),
                );
                return None;
            }
        }
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
                    self.error(
                        s,
                        format!(
                            "expected literal after `-`, found {}",
                            self.peek().describe()
                        ),
                    );
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
                // `_: T` — type-check pattern without a binding (3.11.4).
                if self.eat(&TokenKind::Colon) {
                    let ty = self.parse_type()?;
                    PatternKind::TypeCheck { binder: None, ty }
                } else {
                    PatternKind::Wildcard
                }
            }
            TokenKind::LParen => {
                self.bump();
                let mut subs: Vec<Pattern> = Vec::new();
                let mut trailing_comma = false;
                if !matches!(self.peek(), TokenKind::RParen) {
                    loop {
                        subs.push(self.parse_pattern()?);
                        trailing_comma = self.eat(&TokenKind::Comma);
                        if !trailing_comma || matches!(self.peek(), TokenKind::RParen) {
                            break;
                        }
                    }
                }
                self.expect(&TokenKind::RParen, "`)`")?;
                // `(p)` groups; a 1-tuple pattern is `(p,)`.
                if subs.len() == 1 && !trailing_comma {
                    return subs.pop();
                }
                PatternKind::Tuple(subs)
            }
            TokenKind::Ident(_) => {
                // Multi-segment path, or `Name(..)` (an imported variant
                // such as `Ok(v)`) → enum variant pattern.
                if matches!(
                    self.peek_next(),
                    Some(TokenKind::ColonColon | TokenKind::LParen)
                ) {
                    let path = self.parse_path()?;
                    // Not where a block follows (`catch E::V { body }`).
                    if self.struct_expr_allowed && matches!(self.peek(), TokenKind::LBrace) {
                        self.parse_struct_pattern_body(path)?
                    } else {
                        let args = self.parse_variant_pattern_args()?;
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
                    self.parse_binding_rest(name)?
                }
            }
            other => {
                self.error(
                    span,
                    format!("expected pattern, found {}", other.describe()),
                );
                return None;
            }
        };
        Some(Pattern { kind, span })
    }

    /// Arguments are inside `( )`, so a condition's struct-literal
    /// restriction does not reach them (`if f(S { a: 1 }) { .. }`).
    fn parse_call_args(&mut self) -> Option<Vec<CallArg>> {
        self.with_struct_expr(true, Self::parse_call_args_inner)
    }

    fn parse_call_args_inner(&mut self) -> Option<Vec<CallArg>> {
        let mut args = Vec::new();
        while !matches!(self.peek(), TokenKind::RParen | TokenKind::Eof) {
            // `name: expr` is a named argument; otherwise positional.
            // `__mlir_op`'s `attributes = {..}` / `regions = [..]` are
            // too (bare 1.9).
            if let Some(name) = self.peek_name() {
                if matches!(self.peek_next(), Some(TokenKind::Colon))
                    || (matches!(name.as_str(), "attributes" | "regions")
                        && matches!(self.peek_next(), Some(TokenKind::Eq)))
                {
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
            // `ref x` passes the binding by reference (spec 4.7.3).
            if matches!(self.peek(), TokenKind::Ref) {
                self.bump();
                let value = self.parse_expr()?;
                args.push(CallArg::Ref(value));
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
                continue;
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
            | T::Trait
            | T::Impl
            | T::Mod
            | T::Use
            | T::Pub
            | T::HashLBracket
            | T::Unsafe
            | T::Async
    )
}

/// A statement that may omit its `;`: a block-like expression (spec
/// 1.3.4), or a call whose trailing closure has a block body
/// (`with_lock(m) { .. }`, `xs.each |x| { .. }` — spec 4.8.8 writes them
/// keyword-like, without `;`). The call's value is discarded like `;`.
const fn ends_stmt(e: &Expr) -> bool {
    let (ExprKind::Call {
        trailing_closure: Some(c),
        ..
    }
    | ExprKind::MethodCall {
        trailing_closure: Some(c),
        ..
    }) = &e.kind
    else {
        return is_block_like(e);
    };
    matches!(&c.kind, ExprKind::Closure { body, .. } if matches!(body.kind, ExprKind::Block(_)))
}

const fn is_block_like(e: &Expr) -> bool {
    // `try for x in g { .. }` (a throwing iterator) ends like its loop.
    if let ExprKind::Try { operand, .. } = &e.kind {
        return matches!(operand.kind, ExprKind::For { .. });
    }
    matches!(
        e.kind,
        ExprKind::Block(_)
            | ExprKind::Unsafe(_)
            | ExprKind::If { .. }
            | ExprKind::Match { .. }
            | ExprKind::Loop { .. }
            | ExprKind::While { .. }
            | ExprKind::For { .. }
            | ExprKind::Catch { .. }
    )
}

/// `T?` = `Nest(T) | none`: like `Maybe<T>` (`type Maybe<T> = T |
/// none`), `T` is a generic member, so `(i32 | none)?` keeps two layers
/// while `i32?` is `i32 | none` (spec 2.6.4).
fn optional_ty(t: Ty) -> Ty {
    let span = t.span;
    let nest = Ty {
        kind: TyKind::Nest(Box::new(t)),
        span,
    };
    let none = Ty {
        kind: TyKind::None,
        span,
    };
    Ty {
        kind: TyKind::Sum(vec![nest, none]),
        span,
    }
}

fn path_ty(name: &str, span: Span) -> Ty {
    Ty {
        kind: TyKind::Path(Path {
            segments: vec![PathSegment {
                name: name.to_owned(),
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    }
}

/// `fn f(g: fn(T) throws -> U) rethrows -> R` → `fn f<#E0>(g: fn(T)
/// throws (#E0) -> U) throws (#E0) -> R`. Monomorphization binds `#E0`
/// to the argument's error type, or to "no error" for a non-throwing
/// argument, whose instance then doesn't throw. Returns the error types.
fn desugar_rethrows(params: &mut [Param], generics: &mut Generics) -> Vec<Ty> {
    fn walk(ty: &mut Ty, generics: &mut Generics, errs: &mut Vec<Ty>) {
        if rokc_ast::is_untyped_throws(ty) {
            let name = format!("#E{}", errs.len());
            *ty = path_ty(&name, ty.span);
            generics.params.push(rokc_ast::GenericParam::Type {
                name,
                bounds: Vec::new(),
                default: None,
            });
            errs.push(ty.clone());
            return;
        }
        match &mut ty.kind {
            TyKind::Path(p) => {
                for seg in &mut p.segments {
                    for g in &mut seg.generics {
                        walk(g, generics, errs);
                    }
                }
            }
            TyKind::QPath(q) => walk(&mut q.self_ty, generics, errs),
            TyKind::Sum(ts) | TyKind::Tuple(ts) => {
                for t in ts {
                    walk(t, generics, errs);
                }
            }
            TyKind::Fn(args, ret, _) => {
                for t in args {
                    walk(t, generics, errs);
                }
                walk(ret, generics, errs);
            }
            TyKind::Throws { ok, err } => {
                walk(ok, generics, errs);
                walk(err, generics, errs);
            }
            TyKind::Array(t, _) | TyKind::Nest(t) | TyKind::Binding(_, t) => {
                walk(t, generics, errs);
            }
            TyKind::Const(_)
            | TyKind::AnyTrait(_)
            | TyKind::Any
            | TyKind::None
            | TyKind::SelfUpper
            | TyKind::Never => {}
        }
    }
    let mut errs = Vec::new();
    for p in params {
        if let Some(t) = &mut p.ty {
            walk(t, generics, &mut errs);
        }
    }
    errs
}

const fn starts_stmt(k: &TokenKind) -> bool {
    use TokenKind as T;
    matches!(
        k,
        T::Let | T::Return | T::Break | T::Continue | T::Throw | T::Use
    )
}

/// The base operator symbol of a compound-assign token.
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

/// Keywords of other languages and their rok spelling.
fn keyword_alias(word: &str) -> Option<&'static str> {
    Some(match word {
        "func" | "fun" | "function" | "def" | "fucn" | "fnc" => "fn",
        "elif" | "elsif" | "elseif" => "else if",
        "switch" => "match",
        "var" | "val" => "let",
        "null" | "nil" | "None" | "NULL" => "none",
        "class" => "struct",
        "interface" | "protocol" => "trait",
        "import" | "include" | "require" => "use",
        "module" | "namespace" | "package" => "mod",
        "raise" => "throw",
        "except" => "catch",
        _ => return None,
    })
}

/// The keyword `word` most likely meant: a known alias, else the
/// closest reserved or contextual keyword.
pub(crate) fn keyword_hint(word: &str) -> Option<&'static str> {
    const CONTEXTUAL: &[&str] = &[
        "type", "any", "in", "where", "throws", "rethrows", "catch", "finally", "const", "static",
        "extern", "mut", "union",
    ];
    keyword_alias(word).or_else(|| {
        rokc_diagnostic::suggest(
            word,
            rokc_lexer::token::RESERVED
                .iter()
                .chain(CONTEXTUAL)
                .copied(),
        )
    })
}

/// The marker statement's fn of a nested fn `f` lifted as `lifted`.
fn nested_marker(f: &FnDef, lifted: &str, inherited: bool) -> FnDef {
    let mut args = vec![rokc_ast::AttrArg::Lit(Literal::Str(lifted.to_owned()))];
    if inherited {
        args.push(rokc_ast::AttrArg::Lit(Literal::Bool(true)));
    }
    FnDef {
        vis: Visibility::Private,
        attrs: vec![Attribute {
            path: vec![rokc_ast::NESTED_FN_ATTR.to_owned()],
            body: rokc_ast::AttrBody::Args(args),
            inner: false,
            span: f.span,
        }],
        name: f.name.clone(),
        generics: Generics::default(),
        params: Vec::new(),
        ret_ty: None,
        body: None,
        is_async: false,
        is_generator: false,
        is_unsafe: false,
        throws: f.throws.clone(),
        where_clause: Vec::new(),
        span: f.span,
    }
}

/// `x?.a` followed by a member / index link: the link joins the `?.`
/// tail; anything else (`Err`) ends the optional chain.
fn fold_chain(e: Expr) -> Result<Expr, Expr> {
    let span = e.span;
    let (recv, tail) = match e.kind {
        ExprKind::QuestionDot(..) => return Ok(e),
        ExprKind::Field(r, name) if matches!(r.kind, ExprKind::QuestionDot(..)) => {
            (r, AccessTail::Field(name))
        }
        ExprKind::TupleField(r, i) if matches!(r.kind, ExprKind::QuestionDot(..)) => {
            (r, AccessTail::TupleField(i))
        }
        ExprKind::Index(r, i) if matches!(r.kind, ExprKind::QuestionDot(..)) => {
            (r, AccessTail::Index(i))
        }
        ExprKind::MethodCall {
            receiver,
            method,
            type_args,
            mut args,
            trailing_closure,
        } if matches!(receiver.kind, ExprKind::QuestionDot(..)) => {
            args.extend(trailing_closure.map(|c| CallArg::Positional(*c)));
            (
                receiver,
                AccessTail::Method {
                    method,
                    type_args,
                    args,
                },
            )
        }
        kind => return Err(Expr { kind, span }),
    };
    let ExprKind::QuestionDot(x, mut tails) = recv.kind else {
        unreachable!("checked above")
    };
    tails.push(tail);
    Ok(Expr {
        kind: ExprKind::QuestionDot(x, tails),
        span,
    })
}

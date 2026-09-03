//! Lexer driver. Handles whitespace, comments, identifiers, numeric and
//! string literals, and the fixed punctuation/operator table.

use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};
use rokc_scanner::ScannerTables;

use crate::token::{Token, TokenKind, keyword_kind};

pub struct Lexer<'src, 't> {
    src: &'src str,
    bytes: &'src [u8],
    tables: &'t ScannerTables,
    file: String,
    pos: usize,
    line: u32,
    col: u32,
    diagnostics: Vec<RokDiagnostic>,
}

impl<'src, 't> Lexer<'src, 't> {
    #[must_use]
    pub fn new(src: &'src str, tables: &'t ScannerTables, file: impl Into<String>) -> Self {
        Self {
            src,
            bytes: src.as_bytes(),
            tables,
            file: file.into(),
            pos: 0,
            line: 1,
            col: 1,
            diagnostics: Vec::new(),
        }
    }

    pub fn lex_all(mut self) -> (Vec<Token>, Vec<RokDiagnostic>) {
        let mut tokens = Vec::new();
        loop {
            self.skip_trivia();
            if self.pos >= self.bytes.len() {
                tokens.push(Token::new(TokenKind::Eof, self.span_here()));
                break;
            }
            match self.next_token() {
                Some(tok) => tokens.push(tok),
                None => break,
            }
        }
        (tokens, self.diagnostics)
    }

    fn next_token(&mut self) -> Option<Token> {
        let start = self.pos;
        let line = self.line;
        let col = self.col;

        let b = *self.bytes.get(start)?;
        let kind = match b {
            b'#' => self.lex_hash(),
            b'(' => {
                self.advance(1);
                TokenKind::LParen
            }
            b')' => {
                self.advance(1);
                TokenKind::RParen
            }
            b'[' => {
                self.advance(1);
                TokenKind::LBracket
            }
            b']' => {
                self.advance(1);
                TokenKind::RBracket
            }
            b'{' => {
                self.advance(1);
                TokenKind::LBrace
            }
            b'}' => {
                self.advance(1);
                TokenKind::RBrace
            }
            b',' => {
                self.advance(1);
                TokenKind::Comma
            }
            b';' => {
                self.advance(1);
                TokenKind::Semi
            }
            b'@' => {
                self.advance(1);
                TokenKind::At
            }
            b'~' => {
                self.advance(1);
                TokenKind::Tilde
            }
            b'+' => self.lex_op2(b'=', TokenKind::PlusEq, TokenKind::Plus),
            b'-' => self.lex_minus(),
            b'*' => self.lex_op2(b'=', TokenKind::StarEq, TokenKind::Star),
            b'/' => self.lex_slash(),
            b'%' => self.lex_op2(b'=', TokenKind::PercentEq, TokenKind::Percent),
            b'^' => self.lex_op2(b'=', TokenKind::CaretEq, TokenKind::Caret),
            b'=' => self.lex_eq(),
            b'!' => self.lex_op2(b'=', TokenKind::NotEq, TokenKind::Bang),
            b'<' => self.lex_lt(),
            b'>' => self.lex_gt(),
            b'&' => self.lex_amp(),
            b'|' => self.lex_pipe(),
            b'.' => self.lex_dot(),
            b':' => self.lex_colon(),
            b'?' => self.lex_question(),
            b'\'' => self.lex_quote_or_label(),
            b'"' => self.lex_str_lit(false),
            b'r' if self.bytes.get(start + 1) == Some(&b'"')
                || self.bytes.get(start + 1) == Some(&b'#') =>
            {
                self.lex_raw_str_lit()
            }
            b'f' if self.bytes.get(start + 1) == Some(&b'"') => self.lex_str_lit(true),
            b'c' if self.bytes.get(start + 1) == Some(&b'\'') => self.lex_char_lit(true),
            d if d.is_ascii_digit() => self.lex_number(),
            _ => {
                if is_ident_start(b) {
                    self.lex_ident()
                } else {
                    let span = self.make_span(start, start + 1, line, col);
                    self.error(span, format!("unexpected byte '{}'", b.escape_ascii()));
                    self.advance(1);
                    return self.next_token();
                }
            }
        };

        let span = self.make_span(start, self.pos, line, col);
        Some(Token::new(kind, span))
    }

    fn lex_hash(&mut self) -> TokenKind {
        // `#[` and `#![` are single tokens; bare `#` is invalid here.
        if self.bytes.get(self.pos + 1) == Some(&b'[') {
            self.advance(2);
            TokenKind::HashLBracket
        } else if self.bytes.get(self.pos + 1) == Some(&b'!')
            && self.bytes.get(self.pos + 2) == Some(&b'[')
        {
            self.advance(3);
            TokenKind::HashBangLBracket
        } else {
            let span = self.span_here();
            self.error(span, "stray `#` (expected `#[` or `#![`)");
            self.advance(1);
            TokenKind::Bang
        }
    }

    fn lex_minus(&mut self) -> TokenKind {
        if self.bytes.get(self.pos + 1) == Some(&b'>') {
            self.advance(2);
            TokenKind::Arrow
        } else if self.bytes.get(self.pos + 1) == Some(&b'=') {
            self.advance(2);
            TokenKind::MinusEq
        } else {
            self.advance(1);
            TokenKind::Minus
        }
    }

    fn lex_slash(&mut self) -> TokenKind {
        // Comments are handled in skip_trivia; here we only see `/` operators.
        if self.bytes.get(self.pos + 1) == Some(&b'=') {
            self.advance(2);
            TokenKind::SlashEq
        } else {
            self.advance(1);
            TokenKind::Slash
        }
    }

    fn lex_eq(&mut self) -> TokenKind {
        match self.bytes.get(self.pos + 1) {
            Some(b'=') => {
                self.advance(2);
                TokenKind::EqEq
            }
            Some(b'>') => {
                self.advance(2);
                TokenKind::FatArrow
            }
            _ => {
                self.advance(1);
                TokenKind::Eq
            }
        }
    }

    fn lex_lt(&mut self) -> TokenKind {
        match self.bytes.get(self.pos + 1) {
            Some(b'=') => {
                self.advance(2);
                TokenKind::LtEq
            }
            Some(b'<') => {
                if self.bytes.get(self.pos + 2) == Some(&b'=') {
                    self.advance(3);
                    TokenKind::ShlEq
                } else {
                    self.advance(2);
                    TokenKind::Shl
                }
            }
            _ => {
                self.advance(1);
                TokenKind::Lt
            }
        }
    }

    fn lex_gt(&mut self) -> TokenKind {
        match self.bytes.get(self.pos + 1) {
            Some(b'=') => {
                self.advance(2);
                TokenKind::GtEq
            }
            Some(b'>') => {
                if self.bytes.get(self.pos + 2) == Some(&b'=') {
                    self.advance(3);
                    TokenKind::ShrEq
                } else {
                    self.advance(2);
                    TokenKind::Shr
                }
            }
            _ => {
                self.advance(1);
                TokenKind::Gt
            }
        }
    }

    fn lex_amp(&mut self) -> TokenKind {
        match self.bytes.get(self.pos + 1) {
            Some(b'&') => {
                self.advance(2);
                TokenKind::AmpAmp
            }
            Some(b'=') => {
                self.advance(2);
                TokenKind::AmpEq
            }
            _ => {
                self.advance(1);
                TokenKind::Amp
            }
        }
    }

    fn lex_pipe(&mut self) -> TokenKind {
        match self.bytes.get(self.pos + 1) {
            Some(b'|') => {
                self.advance(2);
                TokenKind::PipePipe
            }
            Some(b'=') => {
                self.advance(2);
                TokenKind::PipeEq
            }
            _ => {
                self.advance(1);
                TokenKind::Pipe
            }
        }
    }

    fn lex_dot(&mut self) -> TokenKind {
        // `..=`, `..`, broadcast operators, plain `.`.
        if self.bytes.get(self.pos + 1) == Some(&b'.') {
            if self.bytes.get(self.pos + 2) == Some(&b'=') {
                self.advance(3);
                return TokenKind::DotDotEq;
            }
            self.advance(2);
            return TokenKind::DotDot;
        }

        if let Some(kind) = self.try_broadcast() {
            return kind;
        }

        self.advance(1);
        TokenKind::Dot
    }

    fn try_broadcast(&mut self) -> Option<TokenKind> {
        // `.+` `.-` `.*` `./` `.%` `.&` `.|` `.^` `.<<` `.>>`
        // `.==` `.!=` `.<` `.>` `.<=` `.>=`
        let p = self.pos + 1;
        let b1 = *self.bytes.get(p)?;
        let b2 = self.bytes.get(p + 1).copied();

        let (len, kind) = match (b1, b2) {
            (b'<', Some(b'<')) => (3, TokenKind::DotShl),
            (b'>', Some(b'>')) => (3, TokenKind::DotShr),
            (b'<', Some(b'=')) => (3, TokenKind::DotLtEq),
            (b'>', Some(b'=')) => (3, TokenKind::DotGtEq),
            (b'=', Some(b'=')) => (3, TokenKind::DotEqEq),
            (b'!', Some(b'=')) => (3, TokenKind::DotNotEq),
            (b'+', _) => (2, TokenKind::DotPlus),
            (b'-', _) => (2, TokenKind::DotMinus),
            (b'*', _) => (2, TokenKind::DotStar),
            (b'/', _) => (2, TokenKind::DotSlash),
            (b'%', _) => (2, TokenKind::DotPercent),
            (b'&', _) => (2, TokenKind::DotAmp),
            (b'|', _) => (2, TokenKind::DotPipe),
            (b'^', _) => (2, TokenKind::DotCaret),
            (b'<', _) => (2, TokenKind::DotLt),
            (b'>', _) => (2, TokenKind::DotGt),
            _ => return None,
        };
        self.advance(len);
        Some(kind)
    }

    fn lex_colon(&mut self) -> TokenKind {
        if self.bytes.get(self.pos + 1) == Some(&b':') {
            self.advance(2);
            TokenKind::ColonColon
        } else {
            self.advance(1);
            TokenKind::Colon
        }
    }

    fn lex_question(&mut self) -> TokenKind {
        match self.bytes.get(self.pos + 1) {
            Some(b'.') => {
                self.advance(2);
                TokenKind::QuestionDot
            }
            Some(b'?') => {
                self.advance(2);
                TokenKind::QuestionQuestion
            }
            _ => {
                self.advance(1);
                TokenKind::Question
            }
        }
    }

    fn lex_op2(&mut self, second: u8, two: TokenKind, one: TokenKind) -> TokenKind {
        if self.bytes.get(self.pos + 1) == Some(&second) {
            self.advance(2);
            two
        } else {
            self.advance(1);
            one
        }
    }

    fn lex_ident(&mut self) -> TokenKind {
        let start = self.pos;
        // First char: this entry was reached because `is_ident_start_byte`
        // matched. The byte test admits any `b >= 0x80` (Unicode lead),
        // but `is_ident_continue` is char-level and rejects e.g. `≡` (Sm).
        // Without consuming the first char unconditionally we'd produce
        // an empty lexeme and never advance — infinite loop.
        if let Some(c) = self.peek_char() {
            self.advance(c.len_utf8());
        }
        while let Some(c) = self.peek_char() {
            if is_ident_continue(c) {
                self.advance(c.len_utf8());
            } else {
                break;
            }
        }
        let lexeme = &self.src[start..self.pos];

        // Non-ASCII single char that isn't `is_ident_continue` is treated
        // as a stray operator-shaped char rather than an identifier.
        // Stage-1 emits a diagnostic and produces an `Ident(<char>)`
        // token so downstream parsing produces a clear "unexpected token"
        // error instead of silently miscompiling.
        if let Some(first_char) = lexeme.chars().next() {
            if !first_char.is_ascii() && !is_ident_continue(first_char) {
                let span = self.span_here();
                self.error(
                    span,
                    format!(
                        "unexpected character `{first_char}` (extension \
                         operator tokens via `#[infix]` are not yet \
                         lexed — spec 1.10.4)"
                    ),
                );
            }
        }

        if let Some(kw) = keyword_kind(lexeme) {
            return kw;
        }
        if self.tables.is_user_keyword(lexeme) {
            return TokenKind::UserKeyword(lexeme.to_owned());
        }
        if self.tables.is_type_ident(lexeme) {
            return TokenKind::TypeIdent(lexeme.to_owned());
        }
        TokenKind::Ident(lexeme.to_owned())
    }

    fn lex_number(&mut self) -> TokenKind {
        let start = self.pos;
        let first = self.bytes[start];

        // Radix prefixes: 0x.., 0b.., 0o..
        if first == b'0' && self.pos + 1 < self.bytes.len() {
            match self.bytes[self.pos + 1] {
                b'x' | b'X' => {
                    self.advance(2);
                    self.eat_digits(16);
                    self.eat_int_suffix();
                    return TokenKind::IntLit(self.src[start..self.pos].to_owned());
                }
                b'b' | b'B' => {
                    self.advance(2);
                    self.eat_digits(2);
                    self.eat_int_suffix();
                    return TokenKind::IntLit(self.src[start..self.pos].to_owned());
                }
                b'o' | b'O' => {
                    self.advance(2);
                    self.eat_digits(8);
                    self.eat_int_suffix();
                    return TokenKind::IntLit(self.src[start..self.pos].to_owned());
                }
                _ => {}
            }
        }

        // Decimal integer or float.
        self.eat_digits(10);
        let mut is_float = false;

        // `.` followed by a digit is part of the float; otherwise leave it
        // for the dot/range/broadcast lexer.
        if self.bytes.get(self.pos) == Some(&b'.')
            && self.bytes.get(self.pos + 1).is_some_and(u8::is_ascii_digit)
        {
            is_float = true;
            self.advance(1);
            self.eat_digits(10);
        } else if self.bytes.get(self.pos) == Some(&b'.')
            && !self
                .bytes
                .get(self.pos + 1)
                .is_some_and(|c| *c == b'.' || is_ident_start_byte(*c))
        {
            // Trailing dot float: `1.`.
            is_float = true;
            self.advance(1);
        }

        // Exponent.
        if matches!(self.bytes.get(self.pos), Some(b'e' | b'E')) {
            is_float = true;
            self.advance(1);
            if matches!(self.bytes.get(self.pos), Some(b'+' | b'-')) {
                self.advance(1);
            }
            self.eat_digits(10);
        }

        if is_float {
            self.eat_float_suffix();
            TokenKind::FloatLit(self.src[start..self.pos].to_owned())
        } else {
            self.eat_int_suffix();
            TokenKind::IntLit(self.src[start..self.pos].to_owned())
        }
    }

    fn eat_digits(&mut self, radix: u32) {
        while let Some(&b) = self.bytes.get(self.pos) {
            if b == b'_' {
                self.advance(1);
            } else if (b as char).is_digit(radix) {
                self.advance(1);
            } else {
                break;
            }
        }
    }

    fn eat_int_suffix(&mut self) {
        // i8, i16, i32, i64, isize, u8, u16, u32, u64, usize, c_char.
        let candidates: &[&str] =
            &["isize", "usize", "i128", "u128", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8", "c_char"];
        for cand in candidates {
            if self.src[self.pos..].starts_with(cand) {
                self.advance(cand.len());
                return;
            }
        }
    }

    fn eat_float_suffix(&mut self) {
        for cand in &["f32", "f64"] {
            if self.src[self.pos..].starts_with(cand) {
                self.advance(cand.len());
                return;
            }
        }
    }

    /// Disambiguate `'…` between a char literal and a label. Char form is
    /// `'X'` or `'\X'` (single character + closing quote, optionally with
    /// escape). Label form is `'ident` (apostrophe + identifier, no
    /// closing quote). The choice is made by scanning ahead a few bytes:
    /// if we see `'<ident>` followed by something other than `'`, it's a
    /// label.
    fn lex_quote_or_label(&mut self) -> TokenKind {
        let after = self.bytes.get(self.pos + 1).copied();
        // Empty `''` or escape: definitely char literal.
        if matches!(after, Some(b'\\')) {
            return self.lex_char_lit(false);
        }
        // Look at the byte right after the candidate identifier start.
        // If the second byte is `'`, this is a single-char literal `'X'`.
        // Otherwise (alpha/digit/_/end), treat as a label.
        if let Some(c1) = after {
            if c1.is_ascii_alphabetic() || c1 == b'_' {
                if matches!(self.bytes.get(self.pos + 2), Some(&b'\'')) {
                    return self.lex_char_lit(false);
                }
                return self.lex_label();
            }
        }
        self.lex_char_lit(false)
    }

    fn lex_label(&mut self) -> TokenKind {
        // self.pos sits on the `'`. Skip it, then read the identifier.
        self.advance(1);
        let start = self.pos;
        while let Some(&b) = self.bytes.get(self.pos) {
            if b.is_ascii_alphanumeric() || b == b'_' {
                self.advance(1);
            } else {
                break;
            }
        }
        let name = self.src[start..self.pos].to_owned();
        TokenKind::Label(name)
    }

    fn lex_char_lit(&mut self, c_char: bool) -> TokenKind {
        let prefix_len = usize::from(c_char);
        self.advance(prefix_len + 1); // skip optional `c` and the opening `'`
        let start = self.pos;
        while let Some(&b) = self.bytes.get(self.pos) {
            if b == b'\\' {
                self.advance(2);
                continue;
            }
            if b == b'\'' {
                let body = self.src[start..self.pos].to_owned();
                self.advance(1);
                return if c_char {
                    TokenKind::CCharLit(body)
                } else {
                    TokenKind::CharLit(body)
                };
            }
            if b == b'\n' {
                let span = self.span_here();
                self.error(span, "unterminated char literal");
                break;
            }
            self.advance(1);
        }
        let span = self.span_here();
        self.error(span, "unterminated char literal");
        TokenKind::CharLit(String::new())
    }

    fn lex_str_lit(&mut self, f_string: bool) -> TokenKind {
        let prefix_len = usize::from(f_string);
        self.advance(prefix_len + 1); // skip optional `f` and the opening `"`
        let start = self.pos;
        while let Some(&b) = self.bytes.get(self.pos) {
            if b == b'\\' {
                self.advance(2);
                continue;
            }
            if b == b'"' {
                let body = self.src[start..self.pos].to_owned();
                self.advance(1);
                return if f_string {
                    TokenKind::FStrLit(body)
                } else {
                    TokenKind::StrLit(body)
                };
            }
            self.advance(1);
        }
        let span = self.span_here();
        self.error(span, "unterminated string literal");
        TokenKind::StrLit(String::new())
    }

    fn lex_raw_str_lit(&mut self) -> TokenKind {
        // r"..." or r#"..."# / r##"..."##.
        self.advance(1); // `r`
        let mut hash_count = 0usize;
        while self.bytes.get(self.pos) == Some(&b'#') {
            hash_count += 1;
            self.advance(1);
        }
        if self.bytes.get(self.pos) != Some(&b'"') {
            let span = self.span_here();
            self.error(span, "expected `\"` after raw-string prefix");
            return TokenKind::RawStrLit(String::new());
        }
        self.advance(1);
        let start = self.pos;
        loop {
            match self.bytes.get(self.pos) {
                None => {
                    let span = self.span_here();
                    self.error(span, "unterminated raw string");
                    return TokenKind::RawStrLit(String::new());
                }
                Some(&b'"') => {
                    let body_end = self.pos;
                    let mut k = 0;
                    while self.bytes.get(self.pos + 1 + k) == Some(&b'#') && k < hash_count {
                        k += 1;
                    }
                    if k == hash_count {
                        let body = self.src[start..body_end].to_owned();
                        self.advance(1 + hash_count);
                        return TokenKind::RawStrLit(body);
                    }
                    self.advance(1);
                }
                _ => self.advance(1),
            }
        }
    }

    fn skip_trivia(&mut self) {
        while self.pos < self.bytes.len() {
            match self.bytes[self.pos] {
                b' ' | b'\t' | b'\r' => self.advance(1),
                b'\n' => {
                    self.pos += 1;
                    self.line += 1;
                    self.col = 1;
                }
                b'/' if self.bytes.get(self.pos + 1) == Some(&b'/') => self.skip_line_comment(),
                b'/' if self.bytes.get(self.pos + 1) == Some(&b'*') => self.skip_block_comment(),
                _ => break,
            }
        }
    }

    fn skip_line_comment(&mut self) {
        while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
            self.pos += 1;
            self.col += 1;
        }
    }

    fn skip_block_comment(&mut self) {
        self.advance(2);
        let mut depth = 1usize;
        while self.pos < self.bytes.len() && depth > 0 {
            if self.bytes.get(self.pos) == Some(&b'/') && self.bytes.get(self.pos + 1) == Some(&b'*')
            {
                self.advance(2);
                depth += 1;
            } else if self.bytes.get(self.pos) == Some(&b'*')
                && self.bytes.get(self.pos + 1) == Some(&b'/')
            {
                self.advance(2);
                depth -= 1;
            } else if self.bytes[self.pos] == b'\n' {
                self.pos += 1;
                self.line += 1;
                self.col = 1;
            } else {
                self.advance(1);
            }
        }
    }

    fn advance(&mut self, n: usize) {
        let end = (self.pos + n).min(self.bytes.len());
        for &b in &self.bytes[self.pos..end] {
            if b == b'\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
        self.pos = end;
    }

    fn peek_char(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn span_here(&self) -> Span {
        let start = u32::try_from(self.pos).unwrap_or(u32::MAX);
        Span::new(start, start, self.line, self.col)
    }

    fn make_span(&self, start: usize, end: usize, line: u32, col: u32) -> Span {
        Span::new(
            u32::try_from(start).unwrap_or(u32::MAX),
            u32::try_from(end).unwrap_or(u32::MAX),
            line,
            col,
        )
    }

    fn error(&mut self, span: Span, msg: impl Into<String>) {
        self.diagnostics.push(
            RokDiagnostic::error(ErrorKind::Lexical, msg)
                .with_file(self.file.clone())
                .with_span(span, ""),
        );
    }
}

fn is_ident_start_byte(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || (b >= 0x80)
}

fn is_ident_start(b: u8) -> bool {
    is_ident_start_byte(b)
}

fn is_ident_continue(c: char) -> bool {
    // ASCII fast path; otherwise accept any char with a letter/digit category.
    if c.is_ascii() {
        c.is_ascii_alphanumeric() || c == '_'
    } else {
        c.is_alphanumeric() || matches!(c, '_')
    }
}

//! `f"..."` (refs-lang 1.7.3) split into literal runs and holes
//! (`ExprKind::FString`). The parser only finds the holes, parses their
//! expressions and splits each spec into text and `${..}` pieces; HIR
//! reads the spec and formats by the hole's type (stdlib 2.10).

use rokc_ast::{Expr, ExprKind, FStringPart, SpecPiece};
use rokc_diagnostic::Span;
use rokc_lexer::{Lexer, TokenKind};

use super::Parser;

/// One `{...}`: its expression text (with offset into the body) and spec.
struct Hole<'a> {
    expr: &'a str,
    offset: usize,
    spec: &'a str,
    spec_offset: usize,
}

/// Split the body into literal runs (escapes kept, `{{` / `}}` folded)
/// and holes. The lexer already checked brace balance.
fn split(body: &str) -> Vec<Result<String, Hole<'_>>> {
    let b = body.as_bytes();
    let mut out = Vec::new();
    let mut lit = String::new();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'{' if b.get(i + 1) == Some(&b'{') => {
                lit.push('{');
                i += 2;
            }
            b'}' if b.get(i + 1) == Some(&b'}') => {
                lit.push('}');
                i += 2;
            }
            b'\\' => {
                let n = body[i + 1..].chars().next().map_or(0, char::len_utf8);
                lit.push_str(&body[i..=i + n]);
                i += 1 + n;
            }
            b'{' => {
                if !lit.is_empty() {
                    out.push(Ok(std::mem::take(&mut lit)));
                }
                let start = i + 1;
                let (mut depth, mut j, mut colon) = (0usize, start, None);
                while j < b.len() {
                    match b[j] {
                        b'"' => {
                            j += 1;
                            while j < b.len() && b[j] != b'"' {
                                j += if b[j] == b'\\' { 2 } else { 1 };
                            }
                        }
                        b'(' | b'[' | b'{' => depth += 1,
                        b')' | b']' => depth = depth.saturating_sub(1),
                        b'}' if depth == 0 => break,
                        b'}' => depth -= 1,
                        b':' if depth == 0 && colon.is_none() => {
                            if b.get(j + 1) == Some(&b':') {
                                j += 1; // `::` path separator
                            } else {
                                colon = Some(j);
                            }
                        }
                        _ => {}
                    }
                    j += 1;
                }
                let end = j.min(b.len());
                let (expr, spec, spec_offset) = match colon {
                    Some(c) => (&body[start..c], &body[c + 1..end], c + 1),
                    None => (&body[start..end], "", end),
                };
                out.push(Err(Hole {
                    expr,
                    offset: start,
                    spec,
                    spec_offset,
                }));
                i = end + 1;
            }
            _ => {
                let n = body[i..].chars().next().map_or(1, char::len_utf8);
                lit.push_str(&body[i..i + n]);
                i += n;
            }
        }
    }
    if !lit.is_empty() {
        out.push(Ok(lit));
    }
    out
}

impl Parser<'_> {
    /// The parts of `f"..."` from its body (raw source between the
    /// quotes; the token's span starts at the `f`).
    pub(super) fn parse_fstring(&mut self, body: &str, span: Span) -> ExprKind {
        let mut parts = Vec::new();
        for part in split(body) {
            match part {
                Ok(lit) => parts.push(FStringPart::Lit(lit)),
                Err(hole) => {
                    let Some(expr) = self.parse_hole(hole.expr, &body[..hole.offset], span) else {
                        continue;
                    };
                    let spec = self.spec_pieces(body, hole.spec_offset, hole.spec, span);
                    parts.push(FStringPart::Hole { expr, spec });
                }
            }
        }
        ExprKind::FString(parts)
    }

    /// `text` (at `offset` in `body`) as text and `${expr}` pieces; `$$`
    /// is a literal `$` (refs-lang 1.7.3).
    fn spec_pieces(&mut self, body: &str, offset: usize, text: &str, span: Span) -> Vec<SpecPiece> {
        let mut out = Vec::new();
        let mut lit = String::new();
        let mut rest = text;
        while let Some(i) = rest.find('$') {
            lit.push_str(&rest[..i]);
            let after = &rest[i + 1..];
            if let Some(tail) = after.strip_prefix('$') {
                lit.push('$');
                rest = tail;
            } else if after.starts_with('{') {
                // The hole splitter balanced the braces.
                let mut depth = 0usize;
                let close = after
                    .char_indices()
                    .find(|&(_, c)| {
                        match c {
                            '{' => depth += 1,
                            '}' => depth -= 1,
                            _ => {}
                        }
                        depth == 0
                    })
                    .map_or(after.len(), |(j, _)| j);
                let inner = &after[1..close.max(1)];
                let at = offset + (text.len() - rest.len()) + i + 2;
                if !lit.is_empty() {
                    out.push(SpecPiece::Text(std::mem::take(&mut lit)));
                }
                if let Some(e) = self.parse_hole(inner, &body[..at], span) {
                    out.push(SpecPiece::Expr(e));
                }
                rest = after.get(close + 1..).unwrap_or("");
            } else {
                lit.push('$');
                rest = after;
            }
        }
        lit.push_str(rest);
        if !lit.is_empty() {
            out.push(SpecPiece::Text(lit));
        }
        out
    }

    /// Parse one hole's expression. `before` is the f-string body up to
    /// the hole, so token and lexer-error spans land on the hole's own
    /// line / column.
    fn parse_hole(&mut self, text: &str, before: &str, span: Span) -> Option<Expr> {
        if text.trim().is_empty() {
            self.error(span, "empty `{}` in f-string");
            return None;
        }
        let (mut tokens, mut diags) = Lexer::new(text, self.file.clone())
            .with_ext_ops(self.ext.symbols())
            .lex_all();
        let to_u32 = |n: usize| u32::try_from(n).unwrap_or(u32::MAX);
        let base = to_u32(span.start as usize + 2 + before.len()); // skip `f"`
        let remap = |s: &mut Span| {
            let upto = (s.start as usize).min(text.len());
            let prefix = format!("{before}{}", &text[..upto]);
            let (line, col) = match prefix.rfind('\n') {
                Some(nl) => (
                    span.line + to_u32(prefix.matches('\n').count()),
                    1 + to_u32(prefix[nl + 1..].chars().count()),
                ),
                None => (span.line, span.col + 2 + to_u32(prefix.chars().count())),
            };
            *s = Span {
                start: s.start.saturating_add(base),
                end: s.end.saturating_add(base),
                line,
                col,
                file: span.file,
            };
        };
        for t in &mut tokens {
            remap(&mut t.span);
        }
        for d in &mut diags {
            if let Some(l) = d.primary.as_mut() {
                remap(&mut l.span);
            }
        }
        self.diagnostics.extend(diags);
        let mut sub = Parser::new(&tokens, self.file.clone());
        sub.ext = self.ext.clone();
        sub.literals = std::sync::Arc::clone(&self.literals);
        let e = sub.parse_expr();
        if !matches!(sub.peek(), TokenKind::Eof) {
            sub.error(span, format!("unexpected tokens in f-string hole `{text}`"));
        }
        self.diagnostics.append(&mut sub.diagnostics);
        e
    }
}

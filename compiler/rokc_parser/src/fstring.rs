//! `f"..."` (refs-lang 1.7.3) desugared to plain expressions:
//!
//! ```text
//! f"x = {x}, y = {y:>8.2}"
//!   ==>  "x = " + x.display() + ", y = "
//!        + rok::core::fmt::fstr_pad(rok::core::fmt::fstr_fixed(y as f64, 2), 8, ' ', '>', 0)
//! ```
//!
//! `+` on `str` concatenates (`core::str`). `{x:?}` calls `debug()`;
//! `b` / `o` / `x` / `X` go through `fstr_radix(x as u64, ..)`;
//! precision through `fstr_fixed(x as f64, ..)` (stdlib 2.10).
//!
//! ponytail: the spec is parsed here, before types are known, so an
//! alignment-less width pads on the right for every type (the spec's
//! numbers-right default needs the type) and `e` / `E` / `${..}` are
//! rejected.

use rokc_ast::{CallArg, Expr, ExprKind, Literal, Path, PathSegment, Ty, TyKind};
use rokc_diagnostic::Span;
use rokc_lexer::{Lexer, TokenKind};

use super::Parser;

/// Parsed `[[fill]align][sign]['#']['0'][width]['.' precision][type]`.
#[derive(Default)]
struct Spec {
    fill: Option<char>,
    align: Option<char>,
    plus: bool,
    alt: bool,
    zero: bool,
    width: Option<usize>,
    precision: Option<usize>,
    ty: Option<char>,
}

fn parse_spec(text: &str) -> Result<Spec, String> {
    if text.contains('$') {
        return Err("dynamic format specs (`${..}`) are not supported yet".to_owned());
    }
    let mut spec = Spec::default();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    let is_align = |c: char| matches!(c, '<' | '>' | '^' | '=');
    if chars.len() >= 2 && is_align(chars[1]) {
        spec.fill = Some(chars[0]);
        spec.align = Some(chars[1]);
        i = 2;
    } else if chars.first().copied().is_some_and(is_align) {
        spec.align = Some(chars[0]);
        i = 1;
    }
    if chars.get(i) == Some(&'+') {
        spec.plus = true;
        i += 1;
    } else if chars.get(i) == Some(&'-') {
        i += 1;
    }
    if chars.get(i) == Some(&'#') {
        spec.alt = true;
        i += 1;
    }
    if chars.get(i) == Some(&'0') {
        spec.zero = true;
        i += 1;
    }
    let digits = |i: &mut usize| {
        let start = *i;
        while chars.get(*i).is_some_and(char::is_ascii_digit) {
            *i += 1;
        }
        (start < *i).then(|| chars[start..*i].iter().collect::<String>().parse().ok())
    };
    spec.width = digits(&mut i).flatten();
    if chars.get(i) == Some(&'.') {
        i += 1;
        spec.precision = digits(&mut i).flatten();
        if spec.precision.is_none() {
            return Err(format!(
                "format spec `{text}`: precision expected after `.`"
            ));
        }
    }
    if let Some(&c) = chars.get(i) {
        if !matches!(c, 'd' | 'b' | 'o' | 'x' | 'X' | 'f' | 'g' | 's' | '?') {
            return Err(format!("format spec `{text}`: unsupported type `{c}`"));
        }
        spec.ty = Some(c);
        i += 1;
    }
    if i != chars.len() {
        return Err(format!("format spec `{text}` is malformed"));
    }
    Ok(spec)
}

/// One `{...}`: its expression text (with offset into the body) and spec.
struct Hole<'a> {
    expr: &'a str,
    offset: usize,
    spec: &'a str,
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
                let (expr, spec) = match colon {
                    Some(c) => (&body[start..c], &body[c + 1..end]),
                    None => (&body[start..end], ""),
                };
                out.push(Err(Hole {
                    expr,
                    offset: start,
                    spec,
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

const fn mk(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}

fn path(names: &[&str], span: Span) -> Path {
    Path {
        segments: names
            .iter()
            .map(|n| PathSegment {
                name: (*n).to_owned(),
                generics: Vec::new(),
            })
            .collect(),
        span,
    }
}

const fn int(text: String, span: Span) -> Expr {
    mk(ExprKind::Literal(Literal::Int(text)), span)
}

fn call_fmt(name: &str, args: Vec<Expr>, span: Span) -> Expr {
    mk(
        ExprKind::Call {
            callee: Box::new(mk(
                ExprKind::Path(path(&["rok", "core", "fmt", name], span)),
                span,
            )),
            args: args.into_iter().map(CallArg::Positional).collect(),
            trailing_closure: None,
        },
        span,
    )
}

fn method(recv: Expr, name: &str, span: Span) -> Expr {
    mk(
        ExprKind::MethodCall {
            receiver: Box::new(recv),
            method: name.to_owned(),
            type_args: Vec::new(),
            args: Vec::new(),
            trailing_closure: None,
        },
        span,
    )
}

fn cast(e: Expr, ty: &str, span: Span) -> Expr {
    let ty = Ty {
        kind: TyKind::Path(path(&[ty], span)),
        span,
    };
    mk(ExprKind::Cast(Box::new(e), ty), span)
}

/// The formatted `str` for one hole.
fn format_value(e: Expr, spec: &Spec, span: Span) -> Expr {
    let base = match (spec.ty, spec.precision) {
        (Some('?'), _) => method(e, "debug", span),
        (Some(c @ ('b' | 'o' | 'x' | 'X')), _) => {
            let radix = match c {
                'b' => 2,
                'o' => 8,
                _ => 16,
            };
            let flags = u32::from(c == 'X') | (u32::from(spec.alt) << 1);
            call_fmt(
                "fstr_radix",
                vec![
                    cast(e, "u64", span),
                    int(format!("{radix}u32"), span),
                    int(format!("{flags}u32"), span),
                ],
                span,
            )
        }
        (Some('f'), p) | (_, p @ Some(_)) => call_fmt(
            "fstr_fixed",
            vec![
                cast(e, "f64", span),
                int(format!("{}i32", p.unwrap_or(6)), span),
            ],
            span,
        ),
        _ => method(e, "display", span),
    };
    if spec.width.is_none() && !spec.plus {
        return base;
    }
    let flags = u32::from(spec.plus) | (u32::from(spec.zero) << 1);
    call_fmt(
        "fstr_pad",
        vec![
            base,
            int(format!("{}usize", spec.width.unwrap_or(0)), span),
            int(format!("{}u32", u32::from(spec.fill.unwrap_or(' '))), span),
            int(format!("{}u32", spec.align.map_or(0, u32::from)), span),
            int(format!("{flags}u32"), span),
        ],
        span,
    )
}

impl Parser<'_> {
    /// Desugar the body of `f"..."` (raw source between the quotes; the
    /// token's span starts at the `f`).
    pub(super) fn desugar_fstring(&mut self, body: &str, span: Span) -> ExprKind {
        let mut acc: Option<Expr> = None;
        for part in split(body) {
            let piece = match part {
                Ok(lit) => mk(ExprKind::Literal(Literal::Str(lit)), span),
                Err(hole) => {
                    let spec = match parse_spec(hole.spec) {
                        Ok(s) => s,
                        Err(msg) => {
                            self.error(span, msg);
                            Spec::default()
                        }
                    };
                    let Some(e) =
                        self.parse_hole(hole.expr, span.start as usize + 2 + hole.offset, span)
                    else {
                        continue;
                    };
                    format_value(e, &spec, span)
                }
            };
            acc = Some(match acc {
                None => piece,
                Some(lhs) => mk(
                    ExprKind::OpInfix {
                        op: "+".to_owned(),
                        lhs: Box::new(lhs),
                        rhs: Box::new(piece),
                    },
                    span,
                ),
            });
        }
        // Every piece is a `str` already (`display()` & co. return one).
        acc.map_or(ExprKind::Literal(Literal::Str(String::new())), |e| e.kind)
    }

    /// Parse one hole's expression; diagnostics land on the f-string.
    fn parse_hole(&mut self, text: &str, abs_offset: usize, span: Span) -> Option<Expr> {
        if text.trim().is_empty() {
            self.error(span, "empty `{}` in f-string");
            return None;
        }
        let (mut tokens, diags) = Lexer::new(text, self.file.clone()).lex_all();
        for t in &mut tokens {
            // Byte offsets into the file; line / column of the literal.
            let off = u32::try_from(abs_offset).unwrap_or(u32::MAX);
            t.span = Span {
                start: t.span.start.saturating_add(off),
                end: t.span.end.saturating_add(off),
                line: span.line,
                col: span.col,
            };
        }
        self.diagnostics.extend(diags);
        let mut sub = Parser::new(&tokens, self.file.clone());
        let e = sub.parse_expr();
        if !matches!(sub.peek(), TokenKind::Eof) {
            sub.error(span, format!("unexpected tokens in f-string hole `{text}`"));
        }
        self.diagnostics.append(&mut sub.diagnostics);
        e
    }
}

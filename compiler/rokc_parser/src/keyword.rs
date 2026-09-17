//! `#[keyword("name")]` (refs-lang 6.6): a function registers `name` as
//! a keyword of its package.
//!
//! The driver's pre-pass gathers the registrations (`collect_keywords`)
//! before the real lex of the package; `apply_keywords` then turns every
//! `name` token of that package into the handler's absolute path, so
//! `with(m) { .. }` is the call `pkg::with_handler(m) { .. }` (trailing
//! closure) and `name` in a declaration / member position is an error.
//!
//! The handler is a free `fn` named by path; its signature is the
//! library's (6.6.8), so the call shape is the use site's.
//!
//! On a `struct` (stdlib spec 2.1.2 / 2.1.3: `#[keyword("int")] struct
//! Int`) the keyword is a type name: every `name` token becomes the
//! struct's path, `name::item` included (`int::from_i64`). A standard
//! library type keyword applies to every package (the driver's
//! `keyword_tables`), like the built-in type names.

use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};
use rokc_lexer::token::{RESERVED, keyword_kind};
use rokc_lexer::{Token, TokenKind};

#[derive(Clone, Debug)]
pub struct KeywordDef {
    pub name: String,
    /// The handler function's path in its file (`f`, `inner::f`), or the
    /// struct's name for a type keyword.
    pub handler: String,
    /// On a `struct`: a type name, not a call.
    pub ty: bool,
    pub file: String,
    /// The `#[keyword(..)]` attribute.
    pub span: Span,
}

/// Identifiers the language already gives meaning to in fixed positions
/// (contextual keywords, path roots).
const CONTEXTUAL: &[&str] = &[
    "type", "any", "in", "where", "throws", "rethrows", "catch", "finally", "const", "static",
    "extern", "mut", "union", "pkg", "sub", "sup", "rok",
];

/// Every `#[keyword("..")] .. fn handler` in `tokens` (a whole file).
#[must_use]
pub fn collect_keywords(tokens: &[Token], file: &str) -> Vec<KeywordDef> {
    let mut out = Vec::new();
    for (k, w) in tokens.windows(6).enumerate() {
        let [h, n, lp, s, rp, rb] = w else { continue };
        let (
            TokenKind::HashLBracket,
            TokenKind::Ident(attr),
            TokenKind::LParen,
            TokenKind::StrLit(name),
            TokenKind::RParen,
            TokenKind::RBracket,
        ) = (&h.kind, &n.kind, &lp.kind, &s.kind, &rp.kind, &rb.kind)
        else {
            continue;
        };
        if attr != "keyword" {
            continue;
        }
        // The fn (or struct) this attribute and any following ones sit on.
        let item = tokens[k + 6..]
            .windows(2)
            .find(|p| matches!(p[0].kind, TokenKind::Fn | TokenKind::Struct));
        let ty = item.is_some_and(|p| p[0].kind == TokenKind::Struct);
        let handler = if ty {
            item.and_then(|p| match &p[1].kind {
                TokenKind::Ident(f) => Some(f.clone()),
                _ => None,
            })
            .unwrap_or_default()
        } else {
            handler_at(tokens, k, k + 6)
        };
        out.push(KeywordDef {
            name: name.clone(),
            handler,
            ty,
            file: file.to_owned(),
            span: h.span,
        });
    }
    out
}

/// The function an attribute at `attr` sits on (the first `fn` from
/// `after`), as a path in its file: `f`, or `a::b::f` inside inline
/// `mod a { mod b { .. } }`. Empty when no `fn` follows.
pub(crate) fn handler_at(tokens: &[Token], attr: usize, after: usize) -> String {
    let Some(name) = tokens[after.min(tokens.len())..]
        .windows(2)
        .find(|p| p[0].kind == TokenKind::Fn)
        .and_then(|p| match &p[1].kind {
            TokenKind::Ident(f) => Some(f.clone()),
            _ => None,
        })
    else {
        return String::new();
    };
    // Inline `mod m {` still open at the attribute (brace depth).
    let mut mods: Vec<(String, usize)> = Vec::new();
    let mut depth = 0usize;
    for (i, t) in tokens[..attr].iter().enumerate() {
        match &t.kind {
            TokenKind::LBrace => {
                depth += 1;
                if let (Some(TokenKind::Mod), Some(TokenKind::Ident(m))) = (
                    i.checked_sub(2).map(|j| &tokens[j].kind),
                    i.checked_sub(1).map(|j| &tokens[j].kind),
                ) {
                    mods.push((m.clone(), depth));
                }
            }
            TokenKind::RBrace => {
                if mods.last().is_some_and(|(_, d)| *d == depth) {
                    mods.pop();
                }
                depth = depth.saturating_sub(1);
            }
            _ => {}
        }
    }
    let mut path: Vec<String> = mods.into_iter().map(|(m, _)| m).collect();
    path.push(name);
    path.join("::")
}

/// 6.6.4: a reserved / contextual keyword can't be registered, nor can
/// a name that is not an identifier.
#[must_use]
pub fn check_keyword(def: &KeywordDef) -> Option<RokDiagnostic> {
    let err = |m: String| Some(RokDiagnostic::error(ErrorKind::Meta, def.span, m));
    let n = def.name.as_str();
    if RESERVED.contains(&n) || keyword_kind(n).is_some() || CONTEXTUAL.contains(&n) {
        return err(format!(
            "`#[keyword(\"{n}\")]`: `{n}` is already a keyword (spec 6.6.4)"
        ));
    }
    let ident = n
        .chars()
        .next()
        .is_some_and(|c| c.is_alphabetic() || c == '_')
        && n.chars().all(|c| c.is_alphanumeric() || c == '_');
    if !ident {
        return err(format!(
            "`#[keyword(\"{n}\")]`: a keyword must be an identifier (spec 6.6.2)"
        ));
    }
    if def.handler.is_empty() {
        return err(format!(
            "`#[keyword(\"{n}\")]` must be on a function — its handler (spec 6.6.2)"
        ));
    }
    None
}

/// A package's keywords: name, the handler's (or type's) absolute
/// path, and whether it is a type keyword.
pub type KeywordTable = Vec<(String, Vec<String>, bool)>;

/// Rewrite the package's registered keywords (`name` → handler path).
pub fn apply_keywords(tokens: &mut Vec<Token>, kws: &KeywordTable, diags: &mut Vec<RokDiagnostic>) {
    if kws.is_empty() {
        return;
    }
    let mut out = Vec::with_capacity(tokens.len());
    for (k, t) in tokens.iter().enumerate() {
        let TokenKind::Ident(n) = &t.kind else {
            out.push(t.clone());
            continue;
        };
        let Some((_, path, ty)) = kws.iter().find(|(kw, ..)| kw == n) else {
            out.push(t.clone());
            continue;
        };
        let prev = k.checked_sub(1).map(|p| &tokens[p].kind);
        let next = tokens.get(k + 1).map(|t| &t.kind);
        // A keyword can't name anything (6.6.3).
        let names = matches!(
            prev,
            Some(
                TokenKind::Let
                    | TokenKind::Fn
                    | TokenKind::Struct
                    | TokenKind::Enum
                    | TokenKind::Trait
                    | TokenKind::Mod
                    | TokenKind::Dot
                    | TokenKind::ColonColon
                    | TokenKind::For
            )
        ) || matches!(next, Some(TokenKind::Colon))
            || (!ty && matches!(next, Some(TokenKind::ColonColon)));
        if names {
            diags.push(
                RokDiagnostic::error(
                    ErrorKind::Parse, t.span,
                    format!(
                        "`{n}` is a keyword registered with `#[keyword(\"{n}\")]` and can't be used as a name (spec 6.6.3)"
                    ),
                ),
            );
            out.push(t.clone());
            continue;
        }
        for (i, seg) in path.iter().enumerate() {
            if i > 0 {
                out.push(Token::new(TokenKind::ColonColon, t.span));
            }
            out.push(Token::new(TokenKind::Ident(seg.clone()), t.span));
        }
    }
    *tokens = out;
}

rokc_core::codec_struct!(KeywordDef {
    name,
    handler,
    ty,
    file,
    span
});

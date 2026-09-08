//! `#[keyword("name")]` (refs-lang 6.6): a function registers `name` as
//! a keyword of its package.
//!
//! The driver's pre-pass gathers the registrations (`collect_keywords`)
//! before the real lex of the package; `apply_keywords` then turns every
//! `name` token of that package into the handler's absolute path, so
//! `with(m) { .. }` is the call `pkg::with_handler(m) { .. }` (trailing
//! closure) and `name` in a declaration / member position is an error.
//!
//! ponytail: the handler is a free `fn` named by path; 6.6.8 leaves its
//! signature to the library, so the call shape is the use site's.

use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};
use rokc_lexer::token::{RESERVED, keyword_kind};
use rokc_lexer::{Token, TokenKind};

#[derive(Clone, Debug)]
pub struct KeywordDef {
    pub name: String,
    /// The handler function's name (leaf).
    pub handler: String,
    pub file: String,
    /// The `#[keyword(..)]` attribute.
    pub span: Span,
}

/// Identifiers the language already gives meaning to in fixed positions
/// (E8 contextual keywords, path roots).
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
        // The function the attribute (and any after it) sits on.
        let handler = tokens[k + 6..]
            .windows(2)
            .find(|p| p[0].kind == TokenKind::Fn)
            .and_then(|p| match &p[1].kind {
                TokenKind::Ident(f) => Some(f.clone()),
                _ => None,
            })
            .unwrap_or_default();
        out.push(KeywordDef {
            name: name.clone(),
            handler,
            file: file.to_owned(),
            span: h.span,
        });
    }
    out
}

/// 6.6.4: a reserved / contextual keyword can't be registered, nor can
/// a name that is not an identifier.
#[must_use]
pub fn check_keyword(def: &KeywordDef) -> Option<RokDiagnostic> {
    let err = |m: String| Some(RokDiagnostic::error(ErrorKind::Meta, m).with_span(def.span, ""));
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

/// Rewrite the package's registered keywords (`name` → handler path).
pub fn apply_keywords(
    tokens: &mut Vec<Token>,
    kws: &[(String, Vec<String>)],
    diags: &mut Vec<RokDiagnostic>,
) {
    if kws.is_empty() {
        return;
    }
    let mut out = Vec::with_capacity(tokens.len());
    for (k, t) in tokens.iter().enumerate() {
        if let TokenKind::FStrLit(text) = &t.kind {
            let text = fstr_keywords(text, kws);
            out.push(Token::new(TokenKind::FStrLit(text), t.span));
            continue;
        }
        let TokenKind::Ident(n) = &t.kind else {
            out.push(t.clone());
            continue;
        };
        let Some((_, path)) = kws.iter().find(|(kw, _)| kw == n) else {
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
        ) || matches!(next, Some(TokenKind::Colon | TokenKind::ColonColon));
        if names {
            diags.push(
                RokDiagnostic::error(
                    ErrorKind::Parse,
                    format!(
                        "`{n}` is a keyword registered with `#[keyword(\"{n}\")]` and can't be used as a name (spec 6.6.3)"
                    ),
                )
                .with_span(t.span, ""),
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

/// The keywords inside an f-string's `{..}` holes (re-lexed later).
fn fstr_keywords(text: &str, kws: &[(String, Vec<String>)]) -> String {
    let chars: Vec<char> = text.chars().collect();
    let (mut out, mut depth, mut i) = (String::new(), 0u32, 0);
    while i < chars.len() {
        let c = chars[i];
        if depth == 0 && c == '{' && chars.get(i + 1) == Some(&'{') {
            out.push_str("{{");
            i += 2;
            continue;
        }
        match c {
            '{' => depth += 1,
            '}' => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth > 0 && (c.is_alphabetic() || c == '_') {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            let member = start > 0 && matches!(chars[start - 1], '.' | ':');
            match kws.iter().find(|(k, _)| *k == word).filter(|_| !member) {
                Some((_, path)) => out.push_str(&path.join("::")),
                None => out.push_str(&word),
            }
            continue;
        }
        out.push(c);
        i += 1;
    }
    out
}

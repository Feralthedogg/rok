//! Layout-preserving edits (`rok add` / `remove`, `env import`): set or
//! remove one entry of a struct / dict / list, splicing text between
//! tokens so that comments and layout stay as written.
//!
//! ```text
//! // `Package { deps: { .. } }`: set `deps["json"]`, adding `deps` if missing.
//! let t = edit::set(text, &[Step::Field("deps"), Step::Key("json")], "Dep::path(\"x\")")?;
//! ```

use rokc_lexer::{Token, TokenKind};

use crate::{Error, Kind, Value};

/// One step of a path into a value.
#[derive(Clone, Copy, Debug)]
pub enum Step<'a> {
    /// A struct field (or a `T::V { .. }` field): `name: ..`.
    Field(&'a str),
    /// A dict entry with a string key: `"key": ..`.
    Key(&'a str),
    /// A list (or tuple) element.
    Index(usize),
}

/// `text` with the entry at `path` set to `value` (ROKON text): replaced
/// in place, or added at the end of its container. Missing containers on
/// the way are added as `{}` (a field or string key only).
pub fn set(text: &str, path: &[Step<'_>], value: &str) -> Result<String, Error> {
    let Some((last, outer)) = path.split_last() else {
        return Ok(value.to_owned());
    };
    let tokens = crate::lex(text)?;
    let root = crate::parse_tokens(&tokens)?;
    let mut v = &root;
    for step in outer {
        let Some(i) = find(v, *step)? else {
            // Add the missing container, then set in the new text.
            let with = insert(text, &tokens, v, *step, "{}")?;
            return set(&with, path, value);
        };
        v = child(v, i);
    }
    let list = list_of(&tokens, v)?;
    match find(v, *last)? {
        Some(i) => {
            let e = &list.entries[i];
            let at = match last {
                Step::Index(_) => e.start,
                _ => e.value.map_or(e.end, |t| tokens[t].span.start as usize),
            };
            Ok(splice(text, vec![(at, e.end, value.to_owned())]))
        }
        None => insert(text, &tokens, v, *last, value),
    }
}

/// `text` without the entry at `path`, or `None` when there is none.
/// The entry's whole lines go (with a trailing `//` comment) when it has
/// them to itself.
pub fn remove(text: &str, path: &[Step<'_>]) -> Result<Option<String>, Error> {
    let Some((last, outer)) = path.split_last() else {
        return Ok(None);
    };
    let tokens = crate::lex(text)?;
    let root = crate::parse_tokens(&tokens)?;
    let mut v = &root;
    for step in outer {
        match find(v, *step)? {
            Some(i) => v = child(v, i),
            None => return Ok(None),
        }
    }
    let Some(i) = find(v, *last)? else {
        return Ok(None);
    };
    let list = list_of(&tokens, v)?;
    Ok(Some(delete(text, &list.entries[i])))
}

/// The index of `step`'s entry in container `v`.
fn find(v: &Value, step: Step<'_>) -> Result<Option<usize>, Error> {
    let not = |what: &str| {
        Err(Error::new(
            v.span,
            format!("expected {what}, found {}", v.describe()),
        ))
    };
    Ok(match (&v.kind, step) {
        (
            Kind::Struct { fields, .. }
            | Kind::Variant {
                named: fields,
                braces: true,
                ..
            },
            Step::Field(n),
        ) => fields.iter().position(|f| f.name == n),
        (Kind::Dict(ps), Step::Key(k)) => ps
            .iter()
            .position(|(key, _)| matches!(&key.kind, Kind::Str(s) if s == k)),
        // `{}` is an empty struct as well as an empty dict.
        (Kind::Dict(ps), Step::Field(_)) if ps.is_empty() => None,
        (Kind::List(vs) | Kind::Tuple(vs), Step::Index(i)) => (i < vs.len()).then_some(i),
        (_, Step::Field(_)) => return not("a struct"),
        (_, Step::Key(_)) => return not("a dict"),
        (_, Step::Index(_)) => return not("a list"),
    })
}

fn child(v: &Value, i: usize) -> &Value {
    match &v.kind {
        Kind::Struct { fields, .. } | Kind::Variant { named: fields, .. } => &fields[i].value,
        Kind::Dict(ps) => &ps[i].1,
        Kind::List(vs) | Kind::Tuple(vs) => &vs[i],
        _ => unreachable!("`find` found an entry"),
    }
}

/// `text` with a `step: value` entry added at the end of container `v`.
fn insert(
    text: &str,
    tokens: &[Token],
    v: &Value,
    step: Step<'_>,
    value: &str,
) -> Result<String, Error> {
    let entry = match step {
        Step::Field(n) => format!("{n}: {value}"),
        Step::Key(k) => format!("{}: {value}", crate::quote(k)),
        Step::Index(i) => match &v.kind {
            Kind::List(vs) if i == vs.len() => value.to_owned(),
            _ => return Err(Error::new(v.span, format!("no element {i} to set"))),
        },
    };
    Ok(append(text, &list_of(tokens, v)?, &entry))
}

/// One comma-separated entry of a bracketed list, as byte offsets.
struct Entry {
    start: usize,
    end: usize,
    /// Token index of the value after the first top-level `:`.
    value: Option<usize>,
    /// End of the comma after the entry, if any.
    comma_end: Option<usize>,
}

struct List {
    open: usize,
    close: usize,
    entries: Vec<Entry>,
}

/// The bracketed list of container `v` (its first `{` / `[` / `(`).
fn list_of(tokens: &[Token], v: &Value) -> Result<List, Error> {
    let open = tokens
        .iter()
        .position(|t| {
            t.span.start >= v.span.start
                && matches!(
                    t.kind,
                    TokenKind::LBrace | TokenKind::LBracket | TokenKind::LParen
                )
        })
        .ok_or_else(|| Error::new(v.span, "expected a bracketed value"))?;
    Ok(list_at(tokens, open))
}

/// The list opened at token `i`.
fn list_at(tokens: &[Token], i: usize) -> List {
    let mut entries: Vec<Entry> = Vec::new();
    let mut depth = 0usize;
    let mut cur: Option<Entry> = None;
    let mut close = tokens[i].span.end as usize;
    for (j, t) in tokens.iter().enumerate().skip(i + 1) {
        let (s, e) = (t.span.start as usize, t.span.end as usize);
        match &t.kind {
            TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket if depth == 0 => {
                close = s;
                break;
            }
            TokenKind::Comma if depth == 0 => {
                if let Some(mut c) = cur.take() {
                    c.comma_end = Some(e);
                    entries.push(c);
                }
                continue;
            }
            TokenKind::Eof => break,
            _ => {}
        }
        match &t.kind {
            TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => depth += 1,
            TokenKind::RBrace | TokenKind::RParen | TokenKind::RBracket => depth -= 1,
            _ => {}
        }
        let c = cur.get_or_insert(Entry {
            start: s,
            end: e,
            value: None,
            comma_end: None,
        });
        c.end = e;
        if depth == 0 && c.value.is_none() && matches!(t.kind, TokenKind::Colon) {
            c.value = Some(j + 1);
        }
    }
    entries.extend(cur);
    List {
        open: tokens[i].span.start as usize,
        close,
        entries,
    }
}

/// Splice `edits` (`(start, end, text)`, non-overlapping) into `text`.
fn splice(text: &str, mut edits: Vec<(usize, usize, String)>) -> String {
    edits.sort_by_key(|e| std::cmp::Reverse(e.0));
    let mut out = text.to_owned();
    for (s, e, with) in edits {
        out.replace_range(s..e, &with);
    }
    out
}

fn line_start(text: &str, at: usize) -> usize {
    text[..at].rfind('\n').map_or(0, |i| i + 1)
}

/// `text` with `entry` added at the end of `list`, in its layout: one
/// more line in a multi-line list, `, entry` in a one-line list, and an
/// empty list opened onto lines.
fn append(text: &str, list: &List, entry: &str) -> String {
    let ls = line_start(text, list.open);
    let base = &text[ls..ls + text[ls..].len() - text[ls..].trim_start_matches([' ', '\t']).len()];
    let (open, close) = (&text[list.open..=list.open], &text[list.close..=list.close]);
    let mut edits = Vec::new();
    if text[list.open..list.close].contains('\n') {
        if let Some(last) = list.entries.last().filter(|l| l.comma_end.is_none()) {
            edits.push((last.end, last.end, ",".to_owned()));
        }
        let cl = line_start(text, list.close);
        if text[cl..list.close].trim().is_empty() {
            edits.push((cl, cl, format!("{base}    {entry},\n")));
        } else {
            edits.push((
                list.close,
                list.close,
                format!("\n{base}    {entry},\n{base}"),
            ));
        }
    } else if let Some(last) = list.entries.last() {
        edits.push((last.end, last.end, format!(", {entry}")));
    } else {
        edits.push((
            list.open,
            list.close + 1,
            format!("{open}\n{base}    {entry},\n{base}{close}"),
        ));
    }
    splice(text, edits)
}

/// `text` without entry `e` (its whole lines, with a trailing `//`
/// comment, when it has them to itself).
fn delete(text: &str, e: &Entry) -> String {
    let end = e.comma_end.unwrap_or(e.end);
    let ls = line_start(text, e.start);
    let le = text[end..].find('\n').map_or(text.len(), |i| end + i + 1);
    let rest = text[end..le].trim();
    if text[ls..e.start].trim().is_empty() && (rest.is_empty() || rest.starts_with("//")) {
        return splice(text, vec![(ls, le, String::new())]);
    }
    let after = text[end..].len() - text[end..].trim_start_matches(' ').len();
    splice(text, vec![(e.start, end + after, String::new())])
}

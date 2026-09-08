//! TOML 1.0 (<https://toml.io/en/v1.0.0>), by hand: the workspace takes
//! no external crates. `parse` gives a value tree whose every key and
//! value carries its byte span (for diagnostics), and `Document` edits
//! the source text in place — setting or removing one key keeps every
//! other byte (comments, order, spacing) as written.

mod edit;
mod parse;

pub use edit::{Document, format_key, format_value};
pub use parse::parse;

/// Byte range into the source.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    /// Offset / local date-time, local date or local time, validated and
    /// kept as written.
    Datetime(String),
    Array(Vec<Item>),
    Table(Table),
}

impl Value {
    pub const fn type_name(&self) -> &'static str {
        match self {
            Self::String(_) => "string",
            Self::Integer(_) => "integer",
            Self::Float(_) => "float",
            Self::Boolean(_) => "boolean",
            Self::Datetime(_) => "datetime",
            Self::Array(_) => "array",
            Self::Table(_) => "table",
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }

    pub const fn as_table(&self) -> Option<&Table> {
        match self {
            Self::Table(t) => Some(t),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Item]> {
        match self {
            Self::Array(a) => Some(a),
            _ => None,
        }
    }
}

/// A value and where it was written (for a table made by a header or
/// dotted keys: its first key).
#[derive(Clone, Debug, PartialEq)]
pub struct Item {
    pub value: Value,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Key {
    pub name: String,
    pub span: Span,
}

/// How a table came to be; decides what may still extend it (TOML 1.0
/// "Table" / "Inline Table" / "Array of Tables").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// Created as the parent of a header (`[a.b]` makes `a`).
    Implicit,
    /// Defined by a `[header]` (or an `[[array]]` element).
    Header,
    /// Created by a dotted key (`a.b = 1` makes `a`).
    Dotted,
    /// An inline table `{ .. }`: closed.
    Inline,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Table {
    // ponytail: linear key lookup; manifests are small. A map index if
    // big documents ever matter.
    entries: Vec<(Key, Item)>,
    pub(crate) kind: Kind,
    /// An array made by `[[header]]` (only those take more elements).
    pub(crate) aot: Vec<String>,
}

impl Table {
    pub(crate) const fn new(kind: Kind) -> Self {
        Self {
            entries: Vec::new(),
            kind,
            aot: Vec::new(),
        }
    }

    pub fn get(&self, key: &str) -> Option<&Item> {
        self.entries
            .iter()
            .find(|(k, _)| k.name == key)
            .map(|(_, v)| v)
    }

    pub(crate) fn get_mut(&mut self, key: &str) -> Option<&mut Item> {
        self.entries
            .iter_mut()
            .find(|(k, _)| k.name == key)
            .map(|(_, v)| v)
    }

    pub fn key(&self, key: &str) -> Option<&Key> {
        self.entries
            .iter()
            .find(|(k, _)| k.name == key)
            .map(|(k, _)| k)
    }

    /// Entries in source order.
    pub fn iter(&self) -> impl Iterator<Item = (&Key, &Item)> {
        self.entries.iter().map(|(k, v)| (k, v))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn insert(&mut self, key: Key, item: Item) -> &mut Item {
        self.entries.push((key, item));
        &mut self.entries.last_mut().unwrap().1
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub message: String,
    pub span: Span,
}

impl Error {
    pub(crate) fn new(message: impl Into<String>, start: usize, end: usize) -> Self {
        Self {
            message: message.into(),
            span: Span { start, end },
        }
    }

    /// `file:line:col: error: message`, the source line and a caret.
    pub fn render(&self, src: &str, file: &str) -> String {
        render(src, file, self.span, &self.message)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// 1-based `(line, column)` of byte `offset` (columns count chars).
pub fn line_col(src: &str, offset: usize) -> (usize, usize) {
    let offset = offset.min(src.len());
    let before = &src[..offset];
    let line = before.matches('\n').count() + 1;
    let start = before.rfind('\n').map_or(0, |i| i + 1);
    (line, before[start..].chars().count() + 1)
}

/// A diagnostic at `span` of `src`: `file:line:col: error: message`, then
/// the line and `^^^` under the span.
pub fn render(src: &str, file: &str, span: Span, message: &str) -> String {
    let (line, col) = line_col(src, span.start);
    let text = src.lines().nth(line - 1).unwrap_or("");
    let width = src
        .get(span.start..span.end.max(span.start))
        .map_or(1, |s| s.lines().next().unwrap_or("").chars().count().max(1));
    format!(
        "{file}:{line}:{col}: error: {message}\n{line:>4} | {text}\n     | {}{}",
        " ".repeat(col - 1),
        "^".repeat(width)
    )
}

#[cfg(test)]
mod tests;

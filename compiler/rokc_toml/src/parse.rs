//! The TOML 1.0 parser: one pass over the bytes, building the value tree
//! and (for `Document`) where each header and key/value line sits.

use crate::{Error, Item, Key, Kind, Span, Table, Value};

/// Parse a whole document into its root table.
pub fn parse(src: &str) -> Result<Table, Error> {
    parse_layout(src).map(|(t, _)| t)
}

/// A `[header]` / `[[header]]` (or the root, `path` empty) and the end of
/// its header line.
pub struct Section {
    pub path: Vec<String>,
    pub array: bool,
    pub line_end: usize,
}

/// A `key = value` line of section `section`.
pub struct Entry {
    pub section: usize,
    pub keys: Vec<String>,
    /// From the line start through its newline.
    pub line: Span,
    pub value: Span,
}

#[derive(Default)]
pub struct Layout {
    pub sections: Vec<Section>,
    pub entries: Vec<Entry>,
}

pub fn parse_layout(src: &str) -> Result<(Table, Layout), Error> {
    let mut p = Parser {
        src,
        b: src.as_bytes(),
        pos: 0,
    };
    let mut root = Table::new(Kind::Header);
    let mut layout = Layout::default();
    layout.sections.push(Section {
        path: Vec::new(),
        array: false,
        line_end: 0,
    });
    // The current header's path (`true`: an array-of-tables element).
    let mut cur: Vec<(String, bool)> = Vec::new();
    loop {
        let line_start = p.pos;
        p.ws();
        match p.peek() {
            None => break,
            Some(b'#') => p.comment()?,
            Some(b'\n') => p.pos += 1,
            Some(b'\r') => p.newline()?,
            Some(b'[') => {
                let array = p.b.get(p.pos + 1) == Some(&b'[');
                let start = p.pos;
                p.pos += if array { 2 } else { 1 };
                p.ws();
                let keys = p.key_path()?;
                p.ws();
                let close: &[u8] = if array { b"]]" } else { b"]" };
                if !p.b[p.pos..].starts_with(close) {
                    return Err(p.err_here(format!(
                        "expected `{}` to close the table header",
                        std::str::from_utf8(close).unwrap()
                    )));
                }
                p.pos += close.len();
                let span = Span { start, end: p.pos };
                p.line_end()?;
                define_header(&mut root, &keys, array, span)?;
                cur = keys
                    .iter()
                    .enumerate()
                    .map(|(i, k)| (k.name.clone(), array && i + 1 == keys.len()))
                    .collect();
                layout.sections.push(Section {
                    path: keys.into_iter().map(|k| k.name).collect(),
                    array,
                    line_end: p.pos,
                });
            }
            Some(_) => {
                let keys = p.key_path()?;
                p.ws();
                p.expect(b'=', "expected `=` after a key")?;
                p.ws();
                let item = p.value()?;
                let value = item.span;
                p.line_end()?;
                let table = navigate(&mut root, &cur);
                insert_dotted(table, &keys, item, Kind::Dotted)?;
                layout.entries.push(Entry {
                    section: layout.sections.len() - 1,
                    keys: keys.into_iter().map(|k| k.name).collect(),
                    line: Span {
                        start: line_start,
                        end: p.pos,
                    },
                    value,
                });
            }
        }
    }
    Ok((root, layout))
}

/// The table the current header names (the last element of each
/// array of tables on the way). Headers were checked when defined.
fn navigate<'a>(mut t: &'a mut Table, path: &[(String, bool)]) -> &'a mut Table {
    for (k, _) in path {
        let item = t.get_mut(k).expect("header defined");
        t = match &mut item.value {
            Value::Table(sub) => sub,
            Value::Array(a) => match &mut a.last_mut().expect("array of tables").value {
                Value::Table(sub) => sub,
                _ => unreachable!("array of tables holds tables"),
            },
            _ => unreachable!("header names a table"),
        };
    }
    t
}

fn dotted(keys: &[Key]) -> String {
    keys.iter()
        .map(|k| crate::format_key(&k.name))
        .collect::<Vec<_>>()
        .join(".")
}

/// `[a.b.c]` / `[[a.b.c]]`.
fn define_header(root: &mut Table, keys: &[Key], array: bool, span: Span) -> Result<(), Error> {
    let mut t = root;
    let (last, parents) = keys.split_last().expect("key path is non-empty");
    for (i, k) in parents.iter().enumerate() {
        if t.get(&k.name).is_none() {
            t.insert(
                k.clone(),
                Item {
                    value: Value::Table(Table::new(Kind::Implicit)),
                    span: k.span,
                },
            );
        }
        let is_aot = t.aot.contains(&k.name);
        let problem = match &t.get(&k.name).unwrap().value {
            Value::Table(sub) if sub.kind == Kind::Inline => Some(format!(
                "`{}` is an inline table; it cannot be extended",
                dotted(&keys[..=i])
            )),
            Value::Table(_) => None,
            Value::Array(_) if is_aot => None,
            v => Some(format!(
                "`{}` is already a {}, not a table",
                dotted(&keys[..=i]),
                v.type_name()
            )),
        };
        if let Some(msg) = problem {
            return Err(Error::new(msg, k.span.start, k.span.end));
        }
        t = match &mut t.get_mut(&k.name).unwrap().value {
            Value::Table(sub) => sub,
            Value::Array(a) => match &mut a.last_mut().unwrap().value {
                Value::Table(sub) => sub,
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
    }
    let name = dotted(keys);
    let is_aot = t.aot.contains(&last.name);
    let fresh = Item {
        value: Value::Table(Table::new(Kind::Header)),
        span: last.span,
    };
    match t.get_mut(&last.name) {
        None if array => {
            t.aot.push(last.name.clone());
            t.insert(
                last.clone(),
                Item {
                    value: Value::Array(vec![fresh]),
                    span: last.span,
                },
            );
        }
        None => {
            t.insert(last.clone(), fresh);
        }
        Some(Item {
            value: Value::Array(a),
            ..
        }) if array && is_aot => a.push(fresh),
        Some(Item {
            value: Value::Table(sub),
            ..
        }) if !array && sub.kind == Kind::Implicit => sub.kind = Kind::Header,
        Some(item) => {
            let what = match &item.value {
                Value::Array(_) if is_aot => "an array of tables",
                Value::Array(_) => "a static array",
                Value::Table(_) => "a table",
                _ => "a value",
            };
            return Err(Error::new(
                format!("`{name}` is already defined as {what}"),
                span.start,
                span.end,
            ));
        }
    }
    Ok(())
}

/// `a.b.c = v` inside `t`: `a` and `a.b` are made (or must be) tables of
/// `kind` (dotted keys may only extend what dotted keys made).
fn insert_dotted(t: &mut Table, keys: &[Key], item: Item, kind: Kind) -> Result<(), Error> {
    let mut t = t;
    let (last, parents) = keys.split_last().expect("key path is non-empty");
    for (i, k) in parents.iter().enumerate() {
        if t.get(&k.name).is_none() {
            t.insert(
                k.clone(),
                Item {
                    value: Value::Table(Table::new(kind)),
                    span: k.span,
                },
            );
        }
        let problem = match &t.get(&k.name).unwrap().value {
            Value::Table(sub) if sub.kind == kind => None,
            Value::Table(_) => Some(format!(
                "table `{}` is defined elsewhere; dotted keys cannot add to it",
                dotted(&keys[..=i])
            )),
            v => Some(format!(
                "`{}` is already a {}, not a table",
                dotted(&keys[..=i]),
                v.type_name()
            )),
        };
        if let Some(msg) = problem {
            return Err(Error::new(msg, k.span.start, k.span.end));
        }
        let Value::Table(sub) = &mut t.get_mut(&k.name).unwrap().value else {
            unreachable!()
        };
        t = sub;
    }
    if t.get(&last.name).is_some() {
        return Err(Error::new(
            format!("duplicate key `{}`", dotted(keys)),
            last.span.start,
            last.span.end,
        ));
    }
    t.insert(last.clone(), item);
    Ok(())
}

/// Close an inline table and every table its dotted keys made.
fn freeze(t: &mut Table) {
    t.kind = Kind::Inline;
    for (_, item) in &mut t.entries {
        if let Value::Table(sub) = &mut item.value {
            if sub.kind == Kind::Dotted {
                freeze(sub);
            }
        }
    }
}

struct Parser<'a> {
    src: &'a str,
    b: &'a [u8],
    pos: usize,
}

const fn is_bare(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c == b'-'
}

impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.pos).copied()
    }

    fn err_here(&self, msg: impl Into<String>) -> Error {
        let end = self.src[self.pos..]
            .chars()
            .next()
            .map_or(self.pos, |c| self.pos + c.len_utf8());
        Error::new(msg, self.pos, end)
    }

    fn expect(&mut self, c: u8, msg: &str) -> Result<(), Error> {
        if self.peek() == Some(c) {
            self.pos += 1;
            Ok(())
        } else {
            Err(self.err_here(msg))
        }
    }

    /// Spaces and tabs.
    fn ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t')) {
            self.pos += 1;
        }
    }

    /// `\n` or `\r\n`.
    fn newline(&mut self) -> Result<(), Error> {
        match self.peek() {
            Some(b'\n') => self.pos += 1,
            Some(b'\r') if self.b.get(self.pos + 1) == Some(&b'\n') => self.pos += 2,
            _ => return Err(self.err_here("expected a newline")),
        }
        Ok(())
    }

    /// `# ...` up to (not including) the newline.
    fn comment(&mut self) -> Result<(), Error> {
        self.pos += 1;
        while let Some(c) = self.peek() {
            match c {
                b'\n' => break,
                b'\r' if self.b.get(self.pos + 1) == Some(&b'\n') => break,
                b'\t' => {}
                c if c < 0x20 || c == 0x7f => {
                    return Err(self.err_here("control character in a comment"));
                }
                _ => {}
            }
            self.pos += 1;
        }
        Ok(())
    }

    /// After a header or key/value: spaces, an optional comment, then a
    /// newline or the end.
    fn line_end(&mut self) -> Result<(), Error> {
        self.ws();
        if self.peek() == Some(b'#') {
            self.comment()?;
        }
        if self.peek().is_none() {
            return Ok(());
        }
        self.newline()
            .map_err(|_| self.err_here("expected the end of the line"))
    }

    /// Whitespace, newlines and comments (inside arrays).
    fn ws_nl(&mut self) -> Result<(), Error> {
        loop {
            self.ws();
            match self.peek() {
                Some(b'#') => self.comment()?,
                Some(b'\n' | b'\r') => self.newline()?,
                _ => return Ok(()),
            }
        }
    }

    /// `a.b."c"` — at least one key.
    fn key_path(&mut self) -> Result<Vec<Key>, Error> {
        let mut keys = vec![self.key()?];
        loop {
            let save = self.pos;
            self.ws();
            if self.peek() != Some(b'.') {
                self.pos = save;
                return Ok(keys);
            }
            self.pos += 1;
            self.ws();
            keys.push(self.key()?);
        }
    }

    fn key(&mut self) -> Result<Key, Error> {
        let start = self.pos;
        let name = match self.peek() {
            Some(b'"') => {
                if self.b[self.pos..].starts_with(b"\"\"\"") {
                    return Err(self.err_here("a key cannot be a multi-line string"));
                }
                self.basic_string()?
            }
            Some(b'\'') => {
                if self.b[self.pos..].starts_with(b"'''") {
                    return Err(self.err_here("a key cannot be a multi-line string"));
                }
                self.literal_string()?
            }
            Some(c) if is_bare(c) => {
                while self.peek().is_some_and(is_bare) {
                    self.pos += 1;
                }
                self.src[start..self.pos].to_owned()
            }
            _ => return Err(self.err_here("expected a key")),
        };
        Ok(Key {
            name,
            span: Span {
                start,
                end: self.pos,
            },
        })
    }

    fn value(&mut self) -> Result<Item, Error> {
        let start = self.pos;
        let value = match self.peek() {
            Some(b'"') if self.b[self.pos..].starts_with(b"\"\"\"") => {
                Value::String(self.ml_basic_string()?)
            }
            Some(b'"') => Value::String(self.basic_string()?),
            Some(b'\'') if self.b[self.pos..].starts_with(b"'''") => {
                Value::String(self.ml_literal_string()?)
            }
            Some(b'\'') => Value::String(self.literal_string()?),
            Some(b'[') => self.array()?,
            Some(b'{') => self.inline_table()?,
            Some(_) => self.scalar()?,
            None => return Err(self.err_here("expected a value")),
        };
        Ok(Item {
            value,
            span: Span {
                start,
                end: self.pos,
            },
        })
    }

    fn array(&mut self) -> Result<Value, Error> {
        self.pos += 1;
        let mut items = Vec::new();
        loop {
            self.ws_nl()?;
            if self.peek() == Some(b']') {
                self.pos += 1;
                return Ok(Value::Array(items));
            }
            items.push(self.value()?);
            self.ws_nl()?;
            match self.peek() {
                Some(b',') => self.pos += 1,
                Some(b']') => {}
                _ => return Err(self.err_here("expected `,` or `]` in an array")),
            }
        }
    }

    fn inline_table(&mut self) -> Result<Value, Error> {
        self.pos += 1;
        let mut t = Table::new(Kind::Inline);
        self.ws();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            return Ok(Value::Table(t));
        }
        loop {
            self.ws();
            let keys = self.key_path()?;
            self.ws();
            self.expect(b'=', "expected `=` after a key")?;
            self.ws();
            let item = self.value()?;
            insert_dotted(&mut t, &keys, item, Kind::Dotted)?;
            self.ws();
            match self.peek() {
                Some(b',') => {
                    self.pos += 1;
                    self.ws();
                    if matches!(self.peek(), Some(b'\n' | b'\r')) {
                        return Err(self.err_here("an inline table must be on one line"));
                    }
                    if self.peek() == Some(b'}') {
                        return Err(
                            self.err_here("trailing comma in an inline table (not allowed)")
                        );
                    }
                }
                Some(b'}') => {
                    self.pos += 1;
                    freeze(&mut t);
                    return Ok(Value::Table(t));
                }
                Some(b'\n' | b'\r') => {
                    return Err(self.err_here("an inline table must be on one line"));
                }
                _ => return Err(self.err_here("expected `,` or `}` in an inline table")),
            }
        }
    }

    /// One char of string content, checking for control characters.
    fn content_char(&mut self, multiline: bool) -> Result<char, Error> {
        let c = self.src[self.pos..].chars().next().unwrap();
        let ok = match c {
            '\t' => true,
            '\n' => multiline,
            '\r' => multiline && self.b.get(self.pos + 1) == Some(&b'\n'),
            c => !c.is_control() || (c as u32) > 0x9f,
        };
        if !ok {
            return Err(self.err_here(if c == '\n' || c == '\r' {
                "newline in a single-line string"
            } else {
                "control character in a string (escape it)"
            }));
        }
        self.pos += c.len_utf8();
        Ok(c)
    }

    fn escape(&mut self, out: &mut String) -> Result<(), Error> {
        let start = self.pos;
        self.pos += 1;
        let c = self
            .peek()
            .ok_or_else(|| self.err_here("unterminated string"))?;
        self.pos += 1;
        let ch = match c {
            b'b' => '\u{8}',
            b't' => '\t',
            b'n' => '\n',
            b'f' => '\u{c}',
            b'r' => '\r',
            b'"' => '"',
            b'\\' => '\\',
            b'u' | b'U' => {
                let n = if c == b'u' { 4 } else { 8 };
                let hex = self
                    .src
                    .get(self.pos..self.pos + n)
                    .filter(|h| h.bytes().all(|b| b.is_ascii_hexdigit()))
                    .ok_or_else(|| {
                        Error::new(
                            format!("`\\{}` needs {n} hex digits", c as char),
                            start,
                            self.pos,
                        )
                    })?;
                self.pos += n;
                let code = u32::from_str_radix(hex, 16).unwrap();
                char::from_u32(code).ok_or_else(|| {
                    Error::new(
                        format!("`\\{}{hex}` is not a Unicode scalar value", c as char),
                        start,
                        self.pos,
                    )
                })?
            }
            _ => {
                return Err(Error::new(
                    format!("unknown escape `\\{}`", c as char),
                    start,
                    self.pos,
                ));
            }
        };
        out.push(ch);
        Ok(())
    }

    fn basic_string(&mut self) -> Result<String, Error> {
        let start = self.pos;
        self.pos += 1;
        let mut out = String::new();
        loop {
            match self.peek() {
                None => return Err(Error::new("unterminated string", start, self.pos)),
                Some(b'"') => {
                    self.pos += 1;
                    return Ok(out);
                }
                Some(b'\\') => self.escape(&mut out)?,
                Some(_) => out.push(self.content_char(false)?),
            }
        }
    }

    fn literal_string(&mut self) -> Result<String, Error> {
        let start = self.pos;
        self.pos += 1;
        let mut out = String::new();
        loop {
            match self.peek() {
                None => return Err(Error::new("unterminated string", start, self.pos)),
                Some(b'\'') => {
                    self.pos += 1;
                    return Ok(out);
                }
                Some(_) => out.push(self.content_char(false)?),
            }
        }
    }

    /// At `q q q`: the closing delimiter when 3–5 quotes run here (up to
    /// two belong to the content). Returns how many quotes are content.
    fn ml_close(&self, q: u8) -> Result<Option<usize>, Error> {
        let n = self.b[self.pos..].iter().take_while(|&&c| c == q).count();
        match n {
            0..=2 => Ok(None),
            3..=5 => Ok(Some(n - 3)),
            _ => Err(Error::new(
                "too many quotes at the end of a multi-line string",
                self.pos,
                self.pos + n,
            )),
        }
    }

    /// Skip the newline right after an opening `"""` / `'''`.
    fn skip_first_newline(&mut self) {
        if self.b[self.pos..].starts_with(b"\n") {
            self.pos += 1;
        } else if self.b[self.pos..].starts_with(b"\r\n") {
            self.pos += 2;
        }
    }

    fn ml_basic_string(&mut self) -> Result<String, Error> {
        let start = self.pos;
        self.pos += 3;
        self.skip_first_newline();
        let mut out = String::new();
        loop {
            match self.peek() {
                None => return Err(Error::new("unterminated string", start, start + 3)),
                Some(b'"') => {
                    if let Some(extra) = self.ml_close(b'"')? {
                        out.push_str(&"\"".repeat(extra));
                        self.pos += extra + 3;
                        return Ok(out);
                    }
                    out.push('"');
                    self.pos += 1;
                }
                Some(b'\\') => {
                    // Line-ending backslash: drop whitespace and newlines
                    // up to the next non-space.
                    let mut j = self.pos + 1;
                    while matches!(self.b.get(j), Some(b' ' | b'\t')) {
                        j += 1;
                    }
                    if matches!(self.b.get(j), Some(b'\n' | b'\r')) {
                        self.pos = j;
                        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
                            if self.peek() == Some(b'\r') {
                                self.newline()?;
                            } else {
                                self.pos += 1;
                            }
                        }
                    } else {
                        self.escape(&mut out)?;
                    }
                }
                Some(_) => {
                    let c = self.content_char(true)?;
                    if c != '\r' {
                        out.push(c);
                    }
                }
            }
        }
    }

    fn ml_literal_string(&mut self) -> Result<String, Error> {
        let start = self.pos;
        self.pos += 3;
        self.skip_first_newline();
        let mut out = String::new();
        loop {
            match self.peek() {
                None => return Err(Error::new("unterminated string", start, start + 3)),
                Some(b'\'') => {
                    if let Some(extra) = self.ml_close(b'\'')? {
                        out.push_str(&"'".repeat(extra));
                        self.pos += extra + 3;
                        return Ok(out);
                    }
                    out.push('\'');
                    self.pos += 1;
                }
                Some(_) => {
                    let c = self.content_char(true)?;
                    if c != '\r' {
                        out.push(c);
                    }
                }
            }
        }
    }

    /// Boolean, number or date/time: the run of characters up to a
    /// delimiter (a date-time may hold one space before its time).
    fn scalar(&mut self) -> Result<Value, Error> {
        let start = self.pos;
        let stop = |c: u8| matches!(c, b' ' | b'\t' | b'\n' | b'\r' | b',' | b']' | b'}' | b'#');
        while self.peek().is_some_and(|c| !stop(c)) {
            self.pos += 1;
        }
        // `1979-05-27 07:32:00`: a full date, a space, then `HH:`.
        let is_date = |s: &[u8]| {
            s.len() == 10
                && s.iter().enumerate().all(|(i, c)| {
                    if i == 4 || i == 7 {
                        *c == b'-'
                    } else {
                        c.is_ascii_digit()
                    }
                })
        };
        if is_date(&self.b[start..self.pos])
            && self.peek() == Some(b' ')
            && self
                .b
                .get(self.pos + 1..self.pos + 4)
                .is_some_and(|t| t[0].is_ascii_digit() && t[1].is_ascii_digit() && t[2] == b':')
        {
            self.pos += 1;
            while self.peek().is_some_and(|c| !stop(c)) {
                self.pos += 1;
            }
        }
        let text = &self.src[start..self.pos];
        let err = |msg: &str| Error::new(format!("{msg} `{text}`"), start, start + text.len());
        if text.is_empty() {
            return Err(self.err_here("expected a value"));
        }
        match text {
            "true" => return Ok(Value::Boolean(true)),
            "false" => return Ok(Value::Boolean(false)),
            "inf" | "+inf" => return Ok(Value::Float(f64::INFINITY)),
            "-inf" => return Ok(Value::Float(f64::NEG_INFINITY)),
            "nan" | "+nan" | "-nan" => return Ok(Value::Float(f64::NAN)),
            _ => {}
        }
        if is_date(&self.b[start..(start + 10).min(self.pos)])
            || (text.len() >= 3 && text.as_bytes()[2] == b':')
        {
            return datetime(text)
                .then(|| Value::Datetime(text.to_owned()))
                .ok_or_else(|| err("invalid date/time"));
        }
        number(text).ok_or_else(|| {
            if text.bytes().all(is_bare) && !text.as_bytes()[0].is_ascii_digit() {
                err("expected a value (strings need quotes), found")
            } else {
                err("invalid number")
            }
        })
    }
}

/// Digits (of `radix`) with `_` only between two digits.
fn digits(s: &str, radix: u32) -> Option<String> {
    let b = s.as_bytes();
    if b.is_empty() || b[0] == b'_' || b[b.len() - 1] == b'_' || s.contains("__") {
        return None;
    }
    let clean: String = s.chars().filter(|&c| c != '_').collect();
    clean.chars().all(|c| c.is_digit(radix)).then_some(clean)
}

fn number(text: &str) -> Option<Value> {
    for (prefix, radix) in [("0x", 16), ("0o", 8), ("0b", 2)] {
        if let Some(rest) = text.strip_prefix(prefix) {
            let d = digits(rest, radix)?;
            return i64::from_str_radix(&d, radix).ok().map(Value::Integer);
        }
    }
    let (sign, body) = match text.as_bytes()[0] {
        b'+' | b'-' => (&text[..1], &text[1..]),
        _ => ("", text),
    };
    // Integer part: no leading zeros.
    let int_end = body.find(['.', 'e', 'E']).unwrap_or(body.len());
    let int = digits(&body[..int_end], 10)?;
    if int.len() > 1 && int.starts_with('0') {
        return None;
    }
    if int_end == body.len() {
        return format!("{sign}{int}").parse().ok().map(Value::Integer);
    }
    let mut rest = &body[int_end..];
    let mut float = format!("{sign}{int}");
    if let Some(r) = rest.strip_prefix('.') {
        let end = r.find(['e', 'E']).unwrap_or(r.len());
        float.push('.');
        float.push_str(&digits(&r[..end], 10)?);
        rest = &r[end..];
    }
    if let Some(r) = rest.strip_prefix(['e', 'E']) {
        let (s, d) = match r.as_bytes().first() {
            Some(b'+' | b'-') => (&r[..1], &r[1..]),
            _ => ("", r),
        };
        float.push('e');
        float.push_str(s);
        float.push_str(&digits(d, 10)?);
        rest = "";
    }
    if !rest.is_empty() {
        return None;
    }
    float.parse().ok().map(Value::Float)
}

/// `YYYY-MM-DD`, `HH:MM:SS[.frac]`, or a date `T`/` ` a time with an
/// optional `Z` / `±HH:MM` offset (TOML 1.0 / RFC 3339).
fn datetime(text: &str) -> bool {
    fn num(s: &str, lo: u32, hi: u32) -> Option<u32> {
        (s.len() == 2 || s.len() == 4)
            .then_some(())
            .filter(|()| s.bytes().all(|b| b.is_ascii_digit()))?;
        let n: u32 = s.parse().ok()?;
        (lo..=hi).contains(&n).then_some(n)
    }
    fn date(s: &str) -> Option<()> {
        let (y, m, d) = (s.get(0..4)?, s.get(5..7)?, s.get(8..10)?);
        if s.len() != 10 || &s[4..5] != "-" || &s[7..8] != "-" {
            return None;
        }
        let (y, m) = (num(y, 0, 9999)?, num(m, 1, 12)?);
        let leap = y % 4 == 0 && (y % 100 != 0 || y % 400 == 0);
        let days = match m {
            2 if leap => 29,
            2 => 28,
            4 | 6 | 9 | 11 => 30,
            _ => 31,
        };
        num(d, 1, days).map(|_| ())
    }
    fn time(s: &str) -> Option<()> {
        let (hms, frac) = s.split_once('.').map_or((s, None), |(a, b)| (a, Some(b)));
        if hms.len() != 8 || &hms[2..3] != ":" || &hms[5..6] != ":" {
            return None;
        }
        num(&hms[0..2], 0, 23)?;
        num(&hms[3..5], 0, 59)?;
        num(&hms[6..8], 0, 60)?;
        match frac {
            Some(f) if f.is_empty() || !f.bytes().all(|b| b.is_ascii_digit()) => None,
            _ => Some(()),
        }
    }
    fn offset_time(s: &str) -> Option<()> {
        if let Some(t) = s.strip_suffix(['Z', 'z']) {
            return time(t);
        }
        if s.len() > 6 {
            let (t, off) = s.split_at(s.len() - 6);
            if matches!(&off[..1], "+" | "-") && off.len() == 6 && &off[3..4] == ":" {
                num(&off[1..3], 0, 23)?;
                num(&off[4..6], 0, 59)?;
                return time(t);
            }
        }
        time(s)
    }
    let ok = if text.as_bytes().get(2) == Some(&b':') {
        time(text)
    } else if text.len() == 10 {
        date(text)
    } else if text.len() > 11 && matches!(&text[10..11], "T" | "t" | " ") {
        date(&text[..10]).and_then(|()| offset_time(&text[11..]))
    } else {
        None
    };
    ok.is_some()
}

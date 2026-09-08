//! Format-preserving edits: a `Document` is the source text plus where
//! its headers and key/value lines are. An edit splices text and parses
//! again, so the result is always valid TOML and every untouched byte
//! (comments, blank lines, order, spacing) stays as written.

use crate::parse::{Layout, parse_layout};
use crate::{Error, Table, Value};

pub struct Document {
    text: String,
    table: Table,
    layout: Layout,
}

impl Document {
    pub fn parse(text: &str) -> Result<Self, Error> {
        let (table, layout) = parse_layout(text)?;
        Ok(Self {
            text: text.to_owned(),
            table,
            layout,
        })
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub const fn table(&self) -> &Table {
        &self.table
    }

    fn splice(&mut self, start: usize, end: usize, with: &str) -> Result<(), Error> {
        let mut text = self.text.clone();
        text.replace_range(start..end, with);
        *self = Self::parse(&text)?;
        Ok(())
    }

    /// The key/value line for `table.key`: in the `[table]` section, or
    /// written dotted from an enclosing section (`table.key = ..` at
    /// the root, `key = ..` with `table` empty).
    fn find(&self, table: &[&str], key: &str) -> Option<usize> {
        self.layout.entries.iter().position(|e| {
            let sec = &self.layout.sections[e.section];
            if sec.array {
                return false;
            }
            let full: Vec<&str> = sec.path.iter().chain(&e.keys).map(String::as_str).collect();
            full.len() == table.len() + 1
                && full[..table.len()] == *table
                && full[table.len()] == key
        })
    }

    /// Set `table.key` to the TOML value text `value` (e.g. from
    /// `format_value`): replace the value in place, else add a line at the
    /// end of the `[table]` section, else append a new `[table]` section.
    /// Fails when the result is not valid TOML (say, `table` is an
    /// inline table or a value).
    pub fn set(&mut self, table: &[&str], key: &str, value: &str) -> Result<(), Error> {
        if let Some(i) = self.find(table, key) {
            let span = self.layout.entries[i].value;
            return self.splice(span.start, span.end, value);
        }
        let line = format!("{} = {value}\n", format_key(key));
        let section =
            self.layout.sections.iter().position(|s| {
                !s.array && s.path.iter().map(String::as_str).eq(table.iter().copied())
            });
        let Some(s) = section else {
            let mut text = self.text.clone();
            if !text.is_empty() && !text.ends_with('\n') {
                text.push('\n');
            }
            if !text.trim().is_empty() {
                text.push('\n');
            }
            if !table.is_empty() {
                let header: Vec<String> = table.iter().map(|k| format_key(k)).collect();
                text.push_str(&format!("[{}]\n", header.join(".")));
            }
            text.push_str(&line);
            *self = Self::parse(&text)?;
            return Ok(());
        };
        let at = self
            .layout
            .entries
            .iter()
            .filter(|e| e.section == s)
            .map(|e| e.line.end)
            .last()
            .unwrap_or_else(|| {
                // An empty section: after the comment lines right below
                // its header (they describe what goes there).
                let mut at = self.layout.sections[s].line_end;
                while let Some(line) = self.text[at..].split_inclusive('\n').next() {
                    if !line.trim_start().starts_with('#') {
                        break;
                    }
                    at += line.len();
                }
                at
            });
        // A last line without its newline gets one first.
        let needs_nl = at > 0 && !self.text[..at].ends_with('\n');
        let insert = if needs_nl { format!("\n{line}") } else { line };
        self.splice(at, at, &insert)
    }

    /// Remove the line defining `table.key`. `false` when there is none.
    pub fn remove(&mut self, table: &[&str], key: &str) -> Result<bool, Error> {
        let Some(i) = self.find(table, key) else {
            return Ok(false);
        };
        let span = self.layout.entries[i].line;
        self.splice(span.start, span.end, "")?;
        Ok(true)
    }
}

/// A key as written: bare when it can be, else a basic string.
pub fn format_key(key: &str) -> String {
    if !key.is_empty()
        && key
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || c == b'_' || c == b'-')
    {
        key.to_owned()
    } else {
        quote(key)
    }
}

fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            c if c.is_control() => out.push_str(&format!("\\u{:04X}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A value as one-line TOML text (tables inline).
pub fn format_value(v: &Value) -> String {
    match v {
        Value::String(s) => quote(s),
        Value::Integer(i) => i.to_string(),
        Value::Float(f) if f.is_nan() => "nan".to_owned(),
        Value::Float(f) if f.is_infinite() => if *f > 0.0 { "inf" } else { "-inf" }.to_owned(),
        Value::Float(f) if f.fract() == 0.0 && f.abs() < 1e16 => format!("{f:.1}"),
        Value::Float(f) => f.to_string(),
        Value::Boolean(b) => b.to_string(),
        Value::Datetime(d) => d.clone(),
        Value::Array(a) => {
            let items: Vec<String> = a.iter().map(|i| format_value(&i.value)).collect();
            format!("[{}]", items.join(", "))
        }
        Value::Table(t) if t.is_empty() => "{}".to_owned(),
        Value::Table(t) => {
            let items: Vec<String> = t
                .iter()
                .map(|(k, v)| format!("{} = {}", format_key(&k.name), format_value(&v.value)))
                .collect();
            format!("{{ {} }}", items.join(", "))
        }
    }
}

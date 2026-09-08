//! Diagnostics shared across compiler stages.

use std::cell::Cell;
use std::fmt;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU8, Ordering};

/// Source location as byte offsets plus 1-based line/column. `file` is
/// a `register_file` id (0 = unknown).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub col: u32,
    pub file: u32,
}

impl Span {
    pub const DUMMY: Self = Self {
        start: 0,
        end: 0,
        line: 0,
        col: 0,
        file: 0,
    };

    #[must_use]
    pub const fn new(start: u32, end: u32, line: u32, col: u32) -> Self {
        Self {
            start,
            end,
            line,
            col,
            file: 0,
        }
    }

    #[must_use]
    pub const fn is_dummy(&self) -> bool {
        self.start == 0 && self.end == 0 && self.line == 0 && self.col == 0
    }
}

/// Source files by id (`Span::file` - 1): path and text, for locations
/// and the caret line under a diagnostic.
static FILES: Mutex<Vec<(String, String)>> = Mutex::new(Vec::new());

/// Register a source file; its id goes into the `file` of its spans.
pub fn register_file(path: String, source: String) -> u32 {
    let mut files = FILES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    files.push((path, source));
    u32::try_from(files.len()).unwrap_or(0)
}

/// Every registered source file `(path, text)`, in registration order.
pub fn registered_files() -> Vec<(String, String)> {
    FILES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone()
}

fn file_by_id(id: u32) -> Option<(String, String)> {
    let files = FILES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    files
        .get(usize::try_from(id).ok()?.checked_sub(1)?)
        .cloned()
}

fn source_by_path(path: &str) -> Option<String> {
    let files = FILES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    files
        .iter()
        .find(|(p, _)| p == path)
        .map(|(_, s)| s.clone())
}

thread_local! {
    static CURRENT_SPAN: Cell<Span> = const { Cell::new(Span::DUMMY) };
}

/// The location new diagnostics default to.
#[must_use]
pub fn current_span() -> Span {
    CURRENT_SPAN.with(Cell::get)
}

/// Set the location new diagnostics default to (what a later pass is
/// working on, e.g. the expression HIR is lowering); returns the old
/// one to restore.
pub fn set_current_span(span: Span) -> Span {
    CURRENT_SPAN.with(|c| c.replace(span))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Severity {
    /// Compile fails but later passes still collect diagnostics.
    Error,
    /// Compiler cannot proceed (OOM, stack overflow, ICE).
    Fatal,
    /// Build still passes.
    Warning,
    /// Supplementary hint attached to another diagnostic.
    Note,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => f.write_str("error"),
            Self::Fatal => f.write_str("fatal"),
            Self::Warning => f.write_str("warning"),
            Self::Note => f.write_str("note"),
        }
    }
}

/// Coarse error category.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    Lexical,
    Parse,
    Resolve,
    Type,
    Visibility,
    Module,
    Pattern,
    Meta,
    Lowering,
    Codegen,
    Linkage,
    Unsupported,
    Internal,
    Other,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Lexical => "lexical",
            Self::Parse => "parse",
            Self::Resolve => "resolve",
            Self::Type => "type",
            Self::Visibility => "visibility",
            Self::Module => "module",
            Self::Pattern => "pattern",
            Self::Meta => "meta",
            Self::Lowering => "lowering",
            Self::Codegen => "codegen",
            Self::Linkage => "linkage",
            Self::Unsupported => "unsupported",
            Self::Internal => "internal",
            Self::Other => "other",
        };
        f.write_str(s)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RokDiagnostic {
    pub severity: Severity,
    pub kind: ErrorKind,
    pub message: String,
    pub file: Option<String>,
    /// Boxed to keep `RokDiagnostic` small as a `Result` error type.
    pub primary: Option<Box<Label>>,
    pub secondary: Vec<Label>,
    pub notes: Vec<String>,
}

impl RokDiagnostic {
    #[must_use]
    pub fn error(kind: ErrorKind, message: impl Into<String>) -> Self {
        let here = CURRENT_SPAN.with(Cell::get);
        Self {
            severity: Severity::Error,
            kind,
            message: message.into(),
            file: None,
            primary: (!here.is_dummy()).then(|| {
                Box::new(Label {
                    span: here,
                    message: String::new(),
                })
            }),
            secondary: Vec::new(),
            notes: Vec::new(),
        }
    }

    #[must_use]
    pub fn fatal(kind: ErrorKind, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Fatal,
            ..Self::error(kind, message)
        }
    }

    #[must_use]
    pub fn warning(kind: ErrorKind, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warning,
            ..Self::error(kind, message)
        }
    }

    #[must_use]
    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    #[must_use]
    pub fn with_span(mut self, span: Span, message: impl Into<String>) -> Self {
        self.primary = Some(Box::new(Label {
            span,
            message: message.into(),
        }));
        self
    }

    #[must_use]
    pub fn with_secondary(mut self, span: Span, message: impl Into<String>) -> Self {
        self.secondary.push(Label {
            span,
            message: message.into(),
        });
        self
    }

    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    #[must_use]
    pub const fn is_error(&self) -> bool {
        matches!(self.severity, Severity::Error | Severity::Fatal)
    }
}

impl RokDiagnostic {
    /// The file path: explicit, else from the primary span's file id.
    fn path(&self) -> Option<String> {
        self.file.clone().or_else(|| {
            let span = self.primary.as_ref()?.span;
            Some(file_by_id(span.file)?.0)
        })
    }

    /// `  N | <source line>` and a caret under the primary column.
    fn snippet(&self) -> Option<String> {
        let span = self.primary.as_ref()?.span;
        let source = file_by_id(span.file)
            .map(|(_, s)| s)
            .or_else(|| source_by_path(self.file.as_deref()?))?;
        let line = source
            .lines()
            .nth(usize::try_from(span.line).ok()?.checked_sub(1)?)?;
        let n = span.line.to_string();
        let pad = " ".repeat(n.len());
        let col = usize::try_from(span.col).ok()?.saturating_sub(1);
        // Keep tabs so the caret lines up under them.
        let lead: String = line
            .chars()
            .take(col)
            .map(|c| if c == '\t' { '\t' } else { ' ' })
            .collect();
        Some(format!("{pad} |\n{n} | {line}\n{pad} | {lead}^"))
    }
}

impl fmt::Display for RokDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.path() {
            Some(file) => {
                let span = self.primary.as_ref().map(|l| l.span).unwrap_or_default();
                write!(
                    f,
                    "{}: [{}] {}:{}:{}: {}",
                    self.severity, self.kind, file, span.line, span.col, self.message
                )
            }
            None => write!(f, "{}: [{}] {}", self.severity, self.kind, self.message),
        }
    }
}

/// How `report` prints (spec 901.8 / 909.4); set once by the CLI.
static STYLE: AtomicU8 = AtomicU8::new(0);
const STYLE_COLOR: u8 = 1;
const STYLE_JSON: u8 = 2;

/// `json`: one JSON object per line on stdout (`--message-format=json`);
/// otherwise human text on stderr, ANSI-colored when `color`.
pub fn set_report_style(json: bool, color: bool) {
    let style = if json {
        STYLE_JSON
    } else if color {
        STYLE_COLOR
    } else {
        0
    };
    STYLE.store(style, Ordering::Relaxed);
}

impl ErrorKind {
    /// Spec 909.4 code ranges: E0xx lexical / syntax, E1xx names /
    /// visibility, E2xx types, E3xx meta, E4xx build / link, E5xx other.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Lexical => "E001",
            Self::Parse => "E002",
            Self::Resolve => "E100",
            Self::Visibility => "E101",
            Self::Module => "E102",
            Self::Type => "E200",
            Self::Pattern => "E201",
            Self::Meta => "E300",
            Self::Lowering => "E400",
            Self::Codegen => "E401",
            Self::Linkage => "E402",
            Self::Unsupported => "E500",
            Self::Internal => "E501",
            Self::Other => "E502",
        }
    }
}

/// A JSON string literal.
#[must_use]
pub fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

impl RokDiagnostic {
    /// One-line JSON (spec 909.4):
    /// `{"type","code","kind","message","spans":[..],"notes":[..]}`.
    #[must_use]
    pub fn to_json(&self) -> String {
        let span_json = |l: &Label, primary: bool, file: Option<String>| {
            let file = file.or_else(|| Some(file_by_id(l.span.file)?.0));
            format!(
                "{{\"file_name\":{},\"line_start\":{},\"col_start\":{},\"byte_start\":{},\
                 \"byte_end\":{},\"is_primary\":{primary},\"label\":{}}}",
                file.as_deref().map_or_else(|| "null".to_owned(), json_str),
                l.span.line,
                l.span.col,
                l.span.start,
                l.span.end,
                json_str(&l.message),
            )
        };
        let mut spans: Vec<String> = Vec::new();
        if let Some(p) = &self.primary {
            spans.push(span_json(p, true, self.path()));
        } else if let Some(file) = self.path() {
            spans.push(format!(
                "{{\"file_name\":{},\"is_primary\":true}}",
                json_str(&file)
            ));
        }
        spans.extend(self.secondary.iter().map(|l| span_json(l, false, None)));
        let notes: Vec<String> = self.notes.iter().map(|n| json_str(n)).collect();
        format!(
            "{{\"type\":\"{}\",\"code\":\"{}\",\"kind\":\"{}\",\"message\":{},\"spans\":[{}],\
             \"notes\":[{}]}}",
            self.severity,
            self.kind.code(),
            self.kind,
            json_str(&self.message),
            spans.join(","),
            notes.join(",")
        )
    }
}

/// Print one diagnostic: human text on stderr, or a JSON line on stdout
/// (see `set_report_style`).
pub fn report(diag: &RokDiagnostic) {
    let style = STYLE.load(Ordering::Relaxed);
    if style == STYLE_JSON {
        println!("{}", diag.to_json());
        return;
    }
    let paint = |code: &str, text: &str| {
        if style == STYLE_COLOR {
            format!("\x1b[{code}m{text}\x1b[0m")
        } else {
            text.to_owned()
        }
    };
    let color = match diag.severity {
        Severity::Error | Severity::Fatal => "1;31",
        Severity::Warning => "1;33",
        Severity::Note => "1;36",
    };
    let head = diag.to_string();
    let sev = diag.severity.to_string();
    eprintln!("{}{}", paint(color, &sev), &head[sev.len()..]);
    if let Some(s) = diag.snippet() {
        // The caret ends the snippet.
        match s.strip_suffix('^') {
            Some(body) => eprintln!("{body}{}", paint(color, "^")),
            None => eprintln!("{s}"),
        }
    }
    for label in &diag.secondary {
        // A label in another file (a meta block's template) names it.
        let path = file_by_id(label.span.file)
            .map(|(p, _)| format!("{p}:"))
            .unwrap_or_default();
        eprintln!(
            "  {} ({path}{}:{}): {}",
            paint("1;36", "note"),
            label.span.line,
            label.span.col,
            label.message
        );
    }
    for note in &diag.notes {
        eprintln!("  {}: {note}", paint("1;36", "note"));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_line_escapes_and_codes() {
        let d = RokDiagnostic::error(ErrorKind::Type, "bad \"x\"\n")
            .with_file("a.rok")
            .with_note("n");
        assert_eq!(
            d.to_json(),
            r#"{"type":"error","code":"E200","kind":"type","message":"bad \"x\"\n","spans":[{"file_name":"a.rok","is_primary":true}],"notes":["n"]}"#
        );
    }
}

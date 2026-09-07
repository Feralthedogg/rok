//! Diagnostics shared across compiler stages.

use std::cell::Cell;
use std::fmt;
use std::sync::Mutex;

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

/// Print one diagnostic to stderr.
pub fn report(diag: &RokDiagnostic) {
    eprintln!("{diag}");
    if let Some(s) = diag.snippet() {
        eprintln!("{s}");
    }
    for label in &diag.secondary {
        eprintln!(
            "  note ({}:{}): {}",
            label.span.line, label.span.col, label.message
        );
    }
    for note in &diag.notes {
        eprintln!("  note: {note}");
    }
}

//! Diagnostics shared across compiler stages.

use std::fmt;

/// Source location as byte offsets plus 1-based line/column.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub col: u32,
}

impl Span {
    pub const DUMMY: Self = Self {
        start: 0,
        end: 0,
        line: 0,
        col: 0,
    };

    #[must_use]
    pub const fn new(start: u32, end: u32, line: u32, col: u32) -> Self {
        Self {
            start,
            end,
            line,
            col,
        }
    }

    #[must_use]
    pub const fn is_dummy(&self) -> bool {
        self.start == 0 && self.end == 0 && self.line == 0 && self.col == 0
    }
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
        Self {
            severity: Severity::Error,
            kind,
            message: message.into(),
            file: None,
            primary: None,
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

impl fmt::Display for RokDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.file {
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

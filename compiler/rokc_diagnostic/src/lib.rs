//! Diagnostics shared across compiler stages.

mod json;

pub use json::Json;

use std::fmt;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU8, Ordering};

/// Source location as byte offsets plus 1-based line/column. `file` is
/// a `SourceMap` id (0 = unknown).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash, PartialOrd, Ord)]
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

/// `ROK_TIME_PASSES=1`: each compiler pass's wall time on stderr.
#[must_use]
pub fn time_passes() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| rokc_core::env_flag("ROK_TIME_PASSES"))
}

/// Run `f` as pass `what`, timed under `ROK_TIME_PASSES`.
pub fn time<T>(what: &str, f: impl FnOnce() -> T) -> T {
    if !time_passes() {
        return f();
    }
    let t = std::time::Instant::now();
    let r = f();
    eprintln!("time: {:>9.1}ms  {what}", t.elapsed().as_secs_f64() * 1e3);
    r
}

/// The source files of one compile, by id (`Span::file` - 1): path and
/// text, for locations and the caret line under a diagnostic. The
/// driver fills it; whoever renders the compile's diagnostics reads it.
#[derive(Clone, Debug, Default)]
pub struct SourceMap {
    files: Vec<(String, String)>,
    views: Vec<View>,
}

/// A stretch of a file `location` shows as another file: a REPL cell
/// inside its generated session source reads as `<repl>:1:1`, a program
/// loaded into a session (`repl <path>`) as the program's own lines.
#[derive(Clone, Debug)]
struct View {
    id: u32,
    path: String,
    /// First line and column of the stretch in file `id`.
    from: (u32, u32),
    /// Its last line.
    last: u32,
    /// Where `from` shows; later lines keep their columns.
    at: (u32, u32),
}

impl SourceMap {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            files: Vec::new(),
            views: Vec::new(),
        }
    }

    /// Add a source file; its id goes into the `file` of its spans. A
    /// file already added with the same text keeps its id.
    pub fn add(&mut self, path: String, source: String) -> u32 {
        let i = self
            .files
            .iter()
            .position(|(p, s)| *p == path && *s == source)
            .unwrap_or_else(|| {
                self.files.push((path, source));
                self.files.len() - 1
            });
        u32::try_from(i + 1).unwrap_or(0)
    }

    /// How many files there are (the next one's id is this plus 1).
    #[must_use]
    pub fn len(&self) -> usize {
        self.files.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    /// Every file `(path, text)`, by id.
    #[must_use]
    pub fn files(&self) -> &[(String, String)] {
        &self.files
    }

    /// Path and text of file `id` (a span's `file`).
    #[must_use]
    pub fn file(&self, id: u32) -> Option<&(String, String)> {
        self.files.get(usize::try_from(id).ok()?.checked_sub(1)?)
    }

    /// The path of file `id`.
    #[must_use]
    pub fn path(&self, id: u32) -> Option<&str> {
        self.file(id).map(|(p, _)| p.as_str())
    }

    /// The id of the last file added at `path`.
    #[must_use]
    pub fn id_of(&self, path: &str) -> Option<u32> {
        let i = self.files.iter().rposition(|(p, _)| p == path)?;
        u32::try_from(i + 1).ok()
    }

    fn source_by_path(&self, path: &str) -> Option<&str> {
        self.files
            .iter()
            .find(|(p, _)| p == path)
            .map(|(_, s)| s.as_str())
    }

    /// Make `location` show lines `from.0..=last` of file `id` as `path`.
    ///
    /// `from` (line, column) shows as `at`. A span of `id` outside every
    /// such stretch shows as the first one's `path`, without a position.
    pub fn view(&mut self, id: u32, path: String, from: (u32, u32), last: u32, at: (u32, u32)) {
        self.views.push(View {
            id,
            path,
            from,
            last,
            at,
        });
    }

    /// `path:line:col` of `span`, as a panic reports it; `<unknown>` for
    /// a span without a source position.
    #[must_use]
    pub fn location(&self, span: Span) -> String {
        let mut of_file = self.views.iter().filter(|v| v.id == span.file).peekable();
        if let Some(first) = of_file.peek() {
            let path = first.path.clone();
            let inside = |v: &&View| (v.from.0..=v.last).contains(&span.line);
            return match of_file.find(inside) {
                Some(v) if span.line == v.from.0 => {
                    let col = (span.col + v.at.1).saturating_sub(v.from.1).max(1);
                    format!("{}:{}:{col}", v.path, v.at.0)
                }
                Some(v) => format!(
                    "{}:{}:{}",
                    v.path,
                    span.line - v.from.0 + v.at.0,
                    span.col.max(1)
                ),
                None => path,
            };
        }
        match self.path(span.file) {
            Some(p) if span.line != 0 => format!("{p}:{}:{}", span.line, span.col.max(1)),
            _ => "<unknown>".to_owned(),
        }
    }

    /// The file path of `diag`: explicit, else its primary span's file.
    fn diag_path(&self, diag: &RokDiagnostic) -> Option<String> {
        diag.file.clone().or_else(|| {
            let span = diag.primary.as_ref()?.span;
            Some(self.path(span.file)?.to_owned())
        })
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
    /// A value used after another owner took it (stdlib 2.13.9).
    Handoff,
    Meta,
    Lowering,
    Codegen,
    Linkage,
    Unsupported,
    Internal,
    Other,
    /// A `rokc lint` finding (its lint name is in a note).
    Lint,
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
            Self::Handoff => "handoff",
            Self::Meta => "meta",
            Self::Lowering => "lowering",
            Self::Codegen => "codegen",
            Self::Linkage => "linkage",
            Self::Unsupported => "unsupported",
            Self::Internal => "internal",
            Self::Other => "other",
            Self::Lint => "lint",
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
    /// An error at `here` (`Span::DUMMY`: no location).
    #[must_use]
    pub fn error(kind: ErrorKind, here: Span, message: impl Into<String>) -> Self {
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
    pub fn fatal(kind: ErrorKind, here: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Fatal,
            ..Self::error(kind, here, message)
        }
    }

    #[must_use]
    pub fn warning(kind: ErrorKind, here: Span, message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Warning,
            ..Self::error(kind, here, message)
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
    /// A `help:` note, printed as `= help: ..`.
    #[must_use]
    pub fn with_help(self, help: impl Into<String>) -> Self {
        self.with_note(format!("help: {}", help.into()))
    }
}

/// `message` about the name `leaf` defined at both `a` and `b`.
///
/// One name, one item: no overloading. Points at both, the later as
/// the error; `callable`: the help names default parameters, the way
/// to take different argument counts (spec 4.2.3).
#[must_use]
pub fn duplicate(
    kind: ErrorKind,
    message: impl Into<String>,
    leaf: &str,
    a: Span,
    b: Option<Span>,
    callable: bool,
) -> RokDiagnostic {
    let (here, first) = match b.filter(|b| !b.is_dummy() && *b != a) {
        Some(b) if (b.file, b.start) > (a.file, a.start) => (b, Some(a)),
        b => (a, b),
    };
    let leaf = leaf.rsplit("::").next().unwrap_or(leaf);
    let mut d = RokDiagnostic::error(kind, here, message);
    if !here.is_dummy() {
        d = d.with_span(here, "defined again here");
    }
    if let Some(first) = first {
        d = d.with_secondary(first, "first defined here");
    }
    let rename = format!("rename one of them, e.g. `{leaf}2`");
    d.with_help(if callable {
        format!(
            "{rename}; there is no overloading, so to take fewer arguments keep one and give \
             its last parameters defaults, as in `b: i32 = 0` (spec 4.2.3)"
        )
    } else {
        rename
    })
}

impl SourceMap {
    /// `diag` on one line: `error[E200]: path:line:col: message`.
    #[must_use]
    pub fn line(&self, diag: &RokDiagnostic) -> String {
        let mut out = format!("{}[{}]: ", diag.severity, diag.kind.code());
        if let Some(file) = self.diag_path(diag) {
            match diag.primary.as_ref().map(|l| l.span) {
                Some(s) if s.line != 0 => {
                    out.push_str(&format!("{file}:{}:{}: ", s.line, s.col.max(1)));
                }
                _ => out.push_str(&format!("{file}: ")),
            }
        }
        out.push_str(&diag.message);
        out
    }
}

/// Closest candidate to `name` by edit distance, for a "did you mean".
///
/// Within about a third of the name's length (names under three chars
/// only match by case), ties to the first. Exact matches and internal
/// names (`__x`, `#x`, a nested fn's `f/x`) give nothing.
#[must_use]
pub fn suggest<'a, I>(name: &str, candidates: I) -> Option<&'a str>
where
    I: IntoIterator<Item = &'a str>,
{
    let len = name.chars().count();
    let limit = if len < 3 { 0 } else { (len + 2) / 3 };
    let mut best: Option<(usize, &str)> = None;
    for c in candidates {
        if c == name || c.is_empty() || c.starts_with("__") || c.contains(['#', '/']) {
            continue;
        }
        let d = edit_distance(name, c);
        // A case-only difference is always worth naming.
        let d = if c.eq_ignore_ascii_case(name) { 0 } else { d };
        if d <= limit && best.is_none_or(|(b, _)| d < b) {
            best = Some((d, c));
        }
    }
    best.map(|(_, c)| c)
}

/// Levenshtein distance over chars, with adjacent transpositions
/// counted as one edit.
#[must_use]
pub fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev2: Vec<usize> = vec![0; b.len() + 1];
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    for i in 1..=a.len() {
        let mut cur = vec![i; b.len() + 1];
        for j in 1..=b.len() {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                cur[j] = cur[j].min(prev2[j - 2] + 1);
            }
        }
        prev2 = std::mem::replace(&mut prev, cur);
    }
    prev[b.len()]
}

/// One underlined source line of a snippet.
struct Mark<'a> {
    line: u32,
    text: &'a str,
    lead: String,
    width: usize,
    primary: bool,
    label: &'a str,
}

/// Underline of `span` within its source line `text`: (leading blanks,
/// width). Tabs are kept so the marks line up under them.
fn underline(text: &str, span: Span, source: &str) -> (String, usize) {
    let col = usize::try_from(span.col).unwrap_or(1).saturating_sub(1);
    let lead: String = text
        .chars()
        .take(col)
        .map(|c| if c == '\t' { '\t' } else { ' ' })
        .collect();
    let avail = text.chars().count().saturating_sub(col).max(1);
    let width = usize::try_from(span.start)
        .ok()
        .zip(usize::try_from(span.end).ok())
        .and_then(|(s, e)| source.get(s..e))
        .map_or(1, |s| s.split('\n').next().unwrap_or("").chars().count())
        .clamp(1, avail);
    (lead, width)
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
            Self::Handoff => "E202",
            Self::Meta => "E300",
            Self::Lowering => "E400",
            Self::Codegen => "E401",
            Self::Linkage => "E402",
            Self::Unsupported => "E500",
            Self::Internal => "E501",
            Self::Other => "E502",
            Self::Lint => "E503",
        }
    }
}

impl SourceMap {
    /// `diag` as one-line JSON (spec 909.4):
    /// `{"type","code","kind","message","spans":[..],"notes":[..]}`.
    #[must_use]
    pub fn json(&self, diag: &RokDiagnostic) -> String {
        let span_json = |l: &Label, primary: bool, file: Option<String>| {
            let file = file.or_else(|| Some(self.path(l.span.file)?.to_owned()));
            Json::obj([
                ("file_name", file.map_or(Json::Null, Json::Str)),
                ("line_start", Json::num(l.span.line)),
                ("col_start", Json::num(l.span.col)),
                ("byte_start", Json::num(l.span.start)),
                ("byte_end", Json::num(l.span.end)),
                ("is_primary", Json::Bool(primary)),
                ("label", Json::str(&l.message)),
            ])
        };
        let mut spans = Vec::new();
        if let Some(p) = &diag.primary {
            spans.push(span_json(p, true, self.diag_path(diag)));
        } else if let Some(file) = self.diag_path(diag) {
            spans.push(Json::obj([
                ("file_name", Json::Str(file)),
                ("is_primary", Json::Bool(true)),
            ]));
        }
        spans.extend(diag.secondary.iter().map(|l| span_json(l, false, None)));
        Json::obj([
            ("type", Json::str(diag.severity.to_string())),
            ("code", Json::str(diag.kind.code())),
            ("kind", Json::str(diag.kind.to_string())),
            ("message", Json::str(&diag.message)),
            ("spans", Json::Arr(spans)),
            (
                "notes",
                Json::Arr(diag.notes.iter().map(Json::str).collect()),
            ),
        ])
        .to_string()
    }
}

/// The report style in effect (part of a build key whose warnings are
/// replayed as rendered).
#[must_use]
pub fn report_style() -> u8 {
    STYLE.load(Ordering::Relaxed)
}

/// Warnings `report`ed inside `capture_warnings`, rendered.
static CAPTURED: Mutex<Option<String>> = Mutex::new(None);

impl SourceMap {
    /// Print one diagnostic: human text on stderr, or a JSON line on
    /// stdout (see `set_report_style`).
    pub fn report(&self, diag: &RokDiagnostic) {
        let text = self.render(diag);
        if !diag.is_error() {
            if let Some(c) = CAPTURED
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .as_mut()
            {
                c.push_str(&text);
            }
        }
        print_rendered(&text);
    }
}

/// Run `f`; also what it reported as warnings (on any thread), rendered,
/// for a build record to replay.
pub fn capture_warnings<T>(f: impl FnOnce() -> T) -> (T, String) {
    *CAPTURED
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(String::new());
    let r = f();
    let text = CAPTURED
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .take()
        .unwrap_or_default();
    (r, text)
}

/// From a panic hook: end the process quietly if `output_closed`.
///
/// As a C program does: killed by SIGPIPE, saying nothing (Windows:
/// exit 1, though std drops writes to a pipe whose reader left, so it
/// hardly gets here). Other pipes and sockets keep reporting `EPIPE`, so SIGPIPE
/// stays ignored until now.
pub fn end_if_output_closed(info: &std::panic::PanicHookInfo<'_>) {
    if !output_closed(info) {
        return;
    }
    #[cfg(unix)]
    {
        const SIGPIPE: i32 = 13;
        unsafe extern "C" {
            fn signal(sig: i32, handler: usize) -> usize;
            fn raise(sig: i32) -> i32;
        }
        // SAFETY: SIG_DFL (0) for SIGPIPE, then raise it on this thread.
        unsafe {
            signal(SIGPIPE, 0);
            raise(SIGPIPE);
        }
    }
    std::process::exit(1);
}

/// Whether a panic is std's `print!` / `eprint!` failing on a stdout
/// or stderr whose reader is gone (`rokc .. | head`): no compiler error.
#[must_use]
pub fn output_closed(info: &std::panic::PanicHookInfo<'_>) -> bool {
    let p = info.payload();
    let msg = p
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| p.downcast_ref::<&str>().copied())
        .unwrap_or("");
    // "failed printing to stdout: Broken pipe (os error 32)"
    msg.strip_prefix("failed printing to std")
        .and_then(|m| {
            m.rsplit_once("(os error ")?
                .1
                .strip_suffix(')')?
                .parse()
                .ok()
        })
        .is_some_and(|code| {
            std::io::Error::from_raw_os_error(code).kind() == std::io::ErrorKind::BrokenPipe
        })
}

/// Print text from `render` where `report` would.
pub fn print_rendered(text: &str) {
    if report_style() == STYLE_JSON {
        print!("{text}");
    } else {
        eprint!("{text}");
    }
}

impl SourceMap {
    /// `diag` as `report` prints it, newline-terminated (spec 9.1.8):
    ///
    /// ```text
    /// error[E100]: cannot find value `count` in this scope
    ///   --> src/main.rok:5:10
    ///    |
    ///  5 |     let x = count + 1;
    ///    |             ^^^^^ not found in this scope
    ///    |
    ///    = help: a local with a similar name exists: `counter`
    /// ```
    #[must_use]
    pub fn render(&self, diag: &RokDiagnostic) -> String {
        let style = report_style();
        if style == STYLE_JSON {
            return format!("{}\n", self.json(diag));
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
        let mut out = format!(
            "{}{}\n",
            paint(color, &format!("{}[{}]", diag.severity, diag.kind.code())),
            paint("1", &format!(": {}", diag.message))
        );
        let path = self.diag_path(diag);
        let primary = diag.primary.as_deref();
        let source = primary.and_then(|l| {
            self.file(l.span.file)
                .map(|(_, s)| s.as_str())
                .or_else(|| self.source_by_path(path.as_deref()?))
        });
        // Labels in the primary's file go under its snippet; others are
        // listed by location.
        let mut marks: Vec<Mark<'_>> = Vec::new();
        let mut elsewhere: Vec<&Label> = Vec::new();
        let mut place = |l: &'_ Label, is_primary: bool| -> bool {
            let (Some(p), Some(src)) = (primary, source) else {
                return false;
            };
            if !is_primary && l.span.file != p.span.file && l.span.file != 0 {
                return false;
            }
            let idx = usize::try_from(l.span.line)
                .ok()
                .and_then(|n| n.checked_sub(1));
            // The line after the last one: end of file.
            let eof = |i: usize| (i == src.lines().count()).then_some("");
            let Some(text) = idx.and_then(|i| src.lines().nth(i).or_else(|| eof(i))) else {
                return false;
            };
            let (lead, width) = underline(text, l.span, src);
            marks.push(Mark {
                line: l.span.line,
                text,
                lead,
                width,
                primary: is_primary,
                label: "",
            });
            true
        };
        let mut labels: Vec<(usize, &str)> = Vec::new();
        if let Some(p) = primary {
            if place(p, true) {
                labels.push((0, &p.message));
            }
        }
        for l in &diag.secondary {
            if place(l, false) {
                labels.push((labels.len(), &l.message));
            } else {
                elsewhere.push(l);
            }
        }
        for (i, label) in labels {
            marks[i].label = label;
        }
        marks.sort_by_key(|m| (m.line, m.lead.len()));
        let width = marks
            .iter()
            .map(|m| m.line)
            .max()
            .map_or(1, |n| n.to_string().len());
        let pad = " ".repeat(width + 1);
        let bar = paint("1;34", "|");
        if let Some(file) = &path {
            let loc = match primary.map(|l| l.span) {
                Some(s) if s.line != 0 => format!("{file}:{}:{}", s.line, s.col.max(1)),
                _ => file.clone(),
            };
            out.push_str(&format!("{pad}{} {loc}\n", paint("1;34", "-->")));
        }
        if !marks.is_empty() {
            out.push_str(&format!("{pad} {bar}\n"));
            let mut last: Option<u32> = None;
            for m in &marks {
                if last != Some(m.line) {
                    if last.is_some_and(|l| m.line > l + 1) {
                        out.push_str(&format!(" {}\n", paint("1;34", "...")));
                    }
                    let n = format!("{:>width$}", m.line);
                    out.push_str(&format!(" {} {bar} {}\n", paint("1;34", &n), m.text));
                }
                last = Some(m.line);
                let (ch, c) = if m.primary {
                    ('^', color)
                } else {
                    ('-', "1;34")
                };
                let mut under: String = std::iter::repeat_n(ch, m.width).collect();
                if !m.label.is_empty() {
                    under = format!("{under} {}", m.label);
                }
                out.push_str(&format!("{pad} {bar} {}{}\n", m.lead, paint(c, &under)));
            }
        }
        for l in elsewhere {
            // A label in another file (a meta block's template) names it.
            let loc = match self.path(l.span.file) {
                Some(p) => format!("{p}:{}:{}", l.span.line, l.span.col.max(1)),
                None => format!("{}:{}", l.span.line, l.span.col.max(1)),
            };
            out.push_str(&format!(
                "{pad}{} {loc}: {}\n",
                paint("1;34", ":::"),
                l.message
            ));
        }
        if !diag.notes.is_empty() && !marks.is_empty() {
            out.push_str(&format!("{pad} {bar}\n"));
        }
        for note in &diag.notes {
            let (kind, text) = match note.strip_prefix("help: ") {
                Some(h) => ("help", h),
                None => ("note", note.as_str()),
            };
            out.push_str(&format!(
                "{pad} {} {}: {text}\n",
                paint("1;34", "="),
                paint("1", kind)
            ));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_line_escapes_and_codes() {
        let d = RokDiagnostic::error(ErrorKind::Type, Span::DUMMY, "bad \"x\"\n")
            .with_file("a.rok")
            .with_note("n");
        assert_eq!(
            SourceMap::new().json(&d),
            r#"{"type":"error","code":"E200","kind":"type","message":"bad \"x\"\n","spans":[{"file_name":"a.rok","is_primary":true}],"notes":["n"]}"#
        );
    }
}

impl rokc_core::codec::Codec for Span {
    fn enc(&self, e: &mut rokc_core::codec::Enc) {
        if e.spans {
            if self.file != 0 && !e.files.contains(&self.file) {
                e.files.push(self.file);
            }
            if let Some((f, a, b)) = e.home {
                let inside = self.file == f && self.start >= a && self.end <= b;
                if self.file != 0 && !inside {
                    match e.foreign.iter_mut().find(|(f, _)| *f == self.file) {
                        Some((_, end)) => *end = (*end).max(self.end),
                        None => e.foreign.push((self.file, self.end)),
                    }
                }
            }
            e.u(u64::from(self.file));
            e.u(u64::from(self.start));
            e.u(u64::from(self.end.wrapping_sub(self.start)));
            e.u(u64::from(self.line));
            e.u(u64::from(self.col));
        }
    }
    fn dec(d: &mut rokc_core::codec::Dec<'_>) -> Option<Self> {
        let old = u32::try_from(d.u()?).ok()?;
        let file = d.file(old)?;
        let start = u32::try_from(d.u()?).ok()?;
        let len = u32::try_from(d.u()?).ok()?;
        Some(Self {
            start,
            end: start.wrapping_add(len),
            line: u32::try_from(d.u()?).ok()?,
            col: u32::try_from(d.u()?).ok()?,
            file,
        })
    }
}

rokc_core::codec_enum!(Severity {
    Error,
    Fatal,
    Warning,
    Note
});
rokc_core::codec_enum!(ErrorKind {
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
    Lint,
    Handoff,
});
rokc_core::codec_struct!(Label { span, message });
rokc_core::codec_struct!(RokDiagnostic {
    severity,
    kind,
    message,
    file,
    primary,
    secondary,
    notes,
});

//! Token definitions.

use rokc_diagnostic::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    #[must_use]
    pub const fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}

/// Token kinds. Strings carry the lexeme as written; the parser owns
/// any further interpretation (suffix splitting, escape decoding, ...).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    // Literals.
    /// Integer literal; value+suffix kept as written, e.g. `42i32`, `0xFFu8`.
    IntLit(String),
    /// Float literal; e.g. `3.14`, `1.5e-3f32`.
    FloatLit(String),
    /// `'A'` (stdlib `char`).
    CharLit(String),
    /// `c'A'` (primitive `c_char`).
    CCharLit(String),
    /// `"hello"`.
    StrLit(String),
    /// `r"raw"` or `r#"raw"#`.
    RawStrLit(String),
    /// `f"x = {x}"`. Body is kept raw; format-spec parsing is later.
    FStrLit(String),

    // Identifiers and contextual promotions.
    Ident(String),
    /// `'name` — loop / block label. Distinguished from char literals
    /// at lex time: `'X'` is a char, `'name` (without closing quote) is
    /// a label.
    Label(String),

    // Declaration / variable keywords.
    Let,
    Fn,
    Struct,
    Enum,
    Trait,
    Impl,
    Pub,
    Mod,
    Use,
    As,
    Ref,
    Unsafe,

    // Control flow keywords.
    If,
    Else,
    Match,
    While,
    Loop,
    For,
    Break,
    Continue,
    Return,
    Is,
    Using,
    Try,
    Throw,

    // Async / generator keywords.
    Async,
    Await,
    Yield,

    // Self keywords. `pkg` and `sup` are contextual identifiers, not
    // tokens — they only carry path-root meaning when followed by `::`,
    // so they remain ordinary identifiers in other positions
    // (consistent with `pub(pkg)` / `pub(sub)`).
    SelfLower,
    SelfUpper,

    // Sentinels.
    True,
    False,
    None,

    // Arithmetic / comparison / logical.
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    /// `%%` Euclidean modulo (spec 1.10.3).
    PercentPercent,
    EqEq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    AmpAmp,
    PipePipe,
    Bang,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Shl,
    Shr,
    /// Unicode math operator (spec 1.10.3): `× ⋅ ∘ √ ∈ ∉ ⊂ ⊆ ∪ ∩`.
    /// `÷ ≡ ≠ ≤ ≥` lex as their ASCII synonyms (`Slash`, `EqEq`, ...).
    MathOp(char),
    /// Registered extension operator token (spec 1.10.4, `like = ..`).
    ExtOp(String),

    // Broadcast (`.` prefix).
    DotPlus,
    DotMinus,
    DotStar,
    DotSlash,
    DotPercent,
    DotPercentPercent,
    DotEqEq,
    DotNotEq,
    DotLt,
    DotGt,
    DotLtEq,
    DotGtEq,
    DotAmp,
    DotPipe,
    DotAmpAmp,
    DotPipePipe,
    DotCaret,
    DotShl,
    DotShr,

    // Assignment / compound assignment.
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    PercentPercentEq,
    AmpEq,
    PipeEq,
    CaretEq,
    ShlEq,
    ShrEq,

    // Range / slice.
    DotDot,
    DotDotEq,
    Colon,
    ColonColon,

    // Dot / question.
    Dot,
    QuestionDot,
    QuestionQuestion,
    Question,

    // Lambda / arrow.
    Arrow,
    FatArrow,

    // Punctuation.
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semi,
    At,

    // Attribute introducers (no space allowed between `#` and `[`).
    HashLBracket,
    HashBangLBracket,

    Eof,
}

impl TokenKind {
    /// Statement terminator token.
    #[must_use]
    pub const fn is_semi(&self) -> bool {
        matches!(self, Self::Semi)
    }
}

/// Reserved keywords (spec 1.5, E8).
///
/// `type`, `any`, `in`, `where`,
/// `throws`, `rethrows`, `catch`, `finally`, `const`, `static`,
/// `extern`, `mut`, `union`, `pkg`, `sub`, `sup` and `rok` are contextual:
/// they lex as identifiers and the parser recognizes them in place.
pub const RESERVED: &[&str] = &[
    "let", "fn", "if", "else", "match", "while", "loop", "for", "return", "break", "continue",
    "try", "throw", "async", "await", "yield", "unsafe", "using", "struct", "enum", "trait",
    "impl", "pub", "mod", "use", "as", "is", "ref", "true", "false", "none", "self", "Self",
];

/// The spelling of a reserved-keyword token (`TokenKind::Match` →
/// `"match"`), for positions where any keyword is a name (after `.`,
/// field declarations, argument labels).
#[must_use]
pub fn keyword_str(kind: &TokenKind) -> Option<&'static str> {
    RESERVED
        .iter()
        .copied()
        .find(|w| keyword_kind(w).as_ref() == Some(kind))
}

/// Match a keyword string against the reserved table.
#[must_use]
pub fn keyword_kind(ident: &str) -> Option<TokenKind> {
    Some(match ident {
        "let" => TokenKind::Let,
        "fn" => TokenKind::Fn,
        "struct" => TokenKind::Struct,
        "enum" => TokenKind::Enum,
        "trait" => TokenKind::Trait,
        "impl" => TokenKind::Impl,
        "pub" => TokenKind::Pub,
        "mod" => TokenKind::Mod,
        "use" => TokenKind::Use,
        "as" => TokenKind::As,
        "ref" => TokenKind::Ref,
        "unsafe" => TokenKind::Unsafe,
        "if" => TokenKind::If,
        "else" => TokenKind::Else,
        "match" => TokenKind::Match,
        "while" => TokenKind::While,
        "loop" => TokenKind::Loop,
        "for" => TokenKind::For,
        "break" => TokenKind::Break,
        "continue" => TokenKind::Continue,
        "return" => TokenKind::Return,
        "is" => TokenKind::Is,
        "using" => TokenKind::Using,
        "try" => TokenKind::Try,
        "throw" => TokenKind::Throw,
        "async" => TokenKind::Async,
        "await" => TokenKind::Await,
        "yield" => TokenKind::Yield,
        "self" => TokenKind::SelfLower,
        "Self" => TokenKind::SelfUpper,
        "true" => TokenKind::True,
        "false" => TokenKind::False,
        "none" => TokenKind::None,
        _ => return None,
    })
}

//! Abstract syntax tree.
//!
//! Operators are not built into the language. The parser only records
//! their token symbol; trait dispatch (`#[infix]` / `#[prefix]` /
//! `#[postfix]` on stdlib trait methods) happens later.

mod codec;
pub mod defs;
pub mod escape;
pub mod print;

pub use defs::*;

use rokc_diagnostic::Span;

#[derive(Clone, Debug, Default)]
pub struct Program {
    pub attrs: Vec<Attribute>,
    pub items: Vec<Item>,
    /// Top-level statements in source order (spec 4.16.1). Only the entry
    /// file `main.rok` may have them; they become the implicit `main`.
    pub stmts: Vec<Stmt>,
    /// Source text of each meta expansion (spec 6.9.9, `--emit=expanded`).
    pub expanded: Vec<String>,
    /// Where each top-level item / statement of the file starts (its
    /// first token, attributes included), in order: (byte offset,
    /// whether it is an item). A REPL session splits a program by it.
    pub tops: Vec<(u32, bool)>,
}

/// Parsed attribute. Spec 6.1 grammar:
/// `attr_body ::= path attr_args?`,
/// `attr_args ::= "(" arg ("," arg)* ","? ")" | "=" literal`,
/// `arg ::= literal | identifier | attr_body | identifier "=" literal`.
#[derive(Clone, Debug)]
pub struct Attribute {
    pub path: Vec<String>,
    pub body: AttrBody,
    pub inner: bool,
    pub span: Span,
}

#[derive(Clone, Debug, Default)]
pub enum AttrBody {
    /// `#[name]` — flag only.
    #[default]
    Empty,
    /// `#[name(arg, arg, ...)]`.
    Args(Vec<AttrArg>),
    /// `#[name = literal]`.
    Value(Literal),
}

#[derive(Clone, Debug)]
pub enum AttrArg {
    Lit(Literal),
    Word(String),
    KeyValue(String, Literal),
    /// Nested `name(args)` or `name = literal` inside an arg list.
    Nested {
        path: Vec<String>,
        body: Box<AttrBody>,
    },
    /// `lo..hi` / `lo..=hi`, either end optional (`#[niche(I32_MIN..=-1)]`).
    Range {
        lo: Option<Box<AttrArg>>,
        hi: Option<Box<AttrArg>>,
        inclusive: bool,
    },
}

impl Attribute {
    /// Convenience: `name` of a single-segment attribute path. Returns
    /// `""` for multi-segment paths so callers can fall back to `path`.
    #[must_use]
    pub fn name(&self) -> &str {
        if self.path.len() == 1 {
            &self.path[0]
        } else {
            ""
        }
    }
}

#[derive(Clone, Debug)]
pub enum Literal {
    /// Integer text + optional suffix as written.
    Int(String),
    /// Float text + optional suffix.
    Float(String),
    Bool(bool),
    Str(String),
    RawStr(String),
    /// `b"..."`: the body as written.
    ByteStr(String),
    Char(String),
    CChar(String),
    None,
}

#[derive(Clone, Debug)]
pub enum Item {
    Fn(FnDef),
    Struct(StructDef),
    Enum(EnumDef),
    Union(UnionDef),
    Trait(TraitDef),
    Impl(ImplDef),
    Const(ConstDef),
    Static(StaticDef),
    TypeAlias(TypeAliasDef),
    Mod(ModDef),
    Use(UseDef),
    Extern(ExternBlock),
}

impl Item {
    #[must_use]
    pub const fn span(&self) -> rokc_diagnostic::Span {
        match self {
            Self::Fn(x) => x.span,
            Self::Struct(x) => x.span,
            Self::Enum(x) => x.span,
            Self::Union(x) => x.span,
            Self::Trait(x) => x.span,
            Self::Impl(x) => x.span,
            Self::Const(x) => x.span,
            Self::Static(x) => x.span,
            Self::TypeAlias(x) => x.span,
            Self::Mod(x) => x.span,
            Self::Use(x) => x.span,
            Self::Extern(x) => x.span,
        }
    }
}

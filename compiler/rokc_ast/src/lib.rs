//! Abstract syntax tree.
//!
//! Operators are not built into the language. The parser only records
//! their token symbol; trait dispatch (`#[infix]` / `#[prefix]` /
//! `#[postfix]` on stdlib trait methods) happens later.

pub mod defs;

pub use defs::*;

use rokc_diagnostic::Span;

#[derive(Clone, Debug)]
pub struct Program {
    pub attrs: Vec<Attribute>,
    pub items: Vec<Item>,
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
    FStr(String),
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

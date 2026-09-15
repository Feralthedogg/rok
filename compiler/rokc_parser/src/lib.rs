//! Parser. Tokens in, AST out.
//!
//! Operator precedence is fixed by the language (spec 3.2.3, `prec.rs`).
//! stdlib's `#[infix]` / `#[prefix]` / `#[postfix]` attributes only bind
//! tokens to trait methods (`PrecTable`, consumed by HIR).

pub mod cfg;
pub mod derive;
pub mod keyword;
pub mod lang;
pub mod parser;
pub mod prec;

#[cfg(test)]
mod tests;

pub use cfg::CfgEnv;
pub use keyword::{KeywordDef, KeywordTable, apply_keywords, check_keyword, collect_keywords};
pub use lang::{LangEntry, LangItemKind, LangTable, collect_lang_table};
pub use parser::literal::{
    ArgKind, LitRule, LiteralDef, LiteralTable, PatElem, PatKind, Pattern, Shape, collect_literals,
    parse_pattern,
};
pub use parser::meta::{MetaDef, MetaKind, MetaTable, collect_meta_blocks};
pub use parser::{
    Parser, VARIADIC_SLICE, parse_expr_file, parse_program, parse_program_ext, parse_program_meta,
};
pub use prec::{Assoc, ExtOps, Fixity, OpEntry, PrecTable, collect_prec_table};

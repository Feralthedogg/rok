//! Parser. Tokens in, AST out.
//!
//! Operator precedence is supplied externally (a `PrecTable` built from
//! stdlib's `#[infix]` / `#[prefix]` / `#[postfix]` attributes). The
//! parser knows the lexical operator tokens but not their semantics.

pub mod lang;
pub mod parser;
pub mod prec;

#[cfg(test)]
mod tests;

pub use lang::{LangEntry, LangItemKind, LangTable, collect_lang_table};
pub use parser::{Parser, parse_program};
pub use prec::{Assoc, Fixity, OpEntry, PrecTable, collect_prec_table};

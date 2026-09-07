//! Parser. Tokens in, AST out.
//!
//! Operator precedence is fixed by the language (spec 3.2.3, `prec.rs`).
//! stdlib's `#[infix]` / `#[prefix]` / `#[postfix]` attributes only bind
//! tokens to trait methods (`PrecTable`, consumed by HIR).

pub mod lang;
pub mod parser;
pub mod prec;

#[cfg(test)]
mod tests;

pub use lang::{LangEntry, LangItemKind, LangTable, collect_lang_table};
pub use parser::{Parser, parse_program};
pub use prec::{Assoc, Fixity, OpEntry, PrecTable, collect_prec_table};

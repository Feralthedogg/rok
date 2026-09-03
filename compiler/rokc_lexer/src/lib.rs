//! Lexer.
//!
//! Input:  source string + optional `ScannerTables`.
//! Output: a `Vec<Token>`.

pub mod lexer;
pub mod token;

pub use lexer::Lexer;
pub use token::{Token, TokenKind};

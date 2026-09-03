//! Lexer.
//!
//! Input:  source string.
//! Output: a `Vec<Token>`.

pub mod lexer;
pub mod token;

pub use lexer::Lexer;
pub use token::{Token, TokenKind};

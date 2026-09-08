//! Interactive tooling on top of the compiler front end: the language
//! server (`lsp`) and the REPL (`repl`). Both take their configuration
//! as arguments, so any CLI front (`rokc lsp`, which `rok lsp` / `rokls` run)
//! can host them.

mod analysis;
mod json;
pub mod lsp;
pub mod repl;

#[cfg(test)]
mod lsp_tests;

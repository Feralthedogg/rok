//! Tooling on top of the compiler front end: the language server
//! (`lsp`), the REPL (`repl`) and its Jupyter kernel (`jupyter`), the
//! linter (`lint`) and the documentation generator (`doc`). Each takes
//! its configuration
//! as arguments, so any CLI front (`rokc lsp`, which `rok lsp` / `rokls` run)
//! can host them.

mod analysis;
pub mod doc;
pub mod json;
pub mod jupyter;
pub mod lint;
pub mod lsp;
pub mod repl;

#[cfg(test)]
mod lsp_tests;

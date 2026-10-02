//! Tooling on top of the compiler front end: the language server
//! (`lsp`), the REPL (`repl`) and its Jupyter kernel (`jupyter`), the
//! linter (`lint`), the documentation generator (`doc`) and the C
//! binding generator (`bindgen`). Each takes
//! its configuration as arguments, so any CLI front (`rokc lsp`, which
//! `rok lsp` / `rokls` run) can host them.

pub mod analysis;
pub mod bindgen;
mod copy_write;
pub mod doc;
pub mod jupyter;
mod line_edit;
pub mod lint;
pub mod lsp;
pub mod repl;

#[cfg(test)]
mod lsp_tests;

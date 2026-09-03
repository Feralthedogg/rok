//! Scanner: shallow first pass that gathers type identifiers and
//! user-registered keywords (`#[keyword(name)]`) so the lexer can promote
//! `Ident` tokens to `TypeIdent` / `UserKeyword`.

use std::collections::HashSet;

#[derive(Clone, Debug, Default)]
pub struct ScannerTables {
    type_idents: HashSet<String>,
    user_keywords: HashSet<String>,
}

impl ScannerTables {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_type_ident(&mut self, name: impl Into<String>) {
        self.type_idents.insert(name.into());
    }

    pub fn add_user_keyword(&mut self, name: impl Into<String>) {
        self.user_keywords.insert(name.into());
    }

    #[must_use]
    pub fn is_type_ident(&self, name: &str) -> bool {
        self.type_idents.contains(name)
    }

    #[must_use]
    pub fn is_user_keyword(&self, name: &str) -> bool {
        self.user_keywords.contains(name)
    }

    pub fn type_idents(&self) -> impl Iterator<Item = &str> {
        self.type_idents.iter().map(String::as_str)
    }

    pub fn user_keywords(&self) -> impl Iterator<Item = &str> {
        self.user_keywords.iter().map(String::as_str)
    }
}

/// Heuristic first pass: register the identifier following `struct`, `enum`,
/// `union`, `trait`, `type` keywords as a type ident.
#[must_use]
pub fn scan_source(source: &str) -> ScannerTables {
    let mut tables = ScannerTables::new();

    let bytes = source.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_')
            {
                i += 1;
            }
            let word = &source[start..i];
            if matches!(word, "struct" | "enum" | "union" | "trait" | "type") {
                while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
                let name_start = i;
                while i < bytes.len()
                    && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_')
                {
                    i += 1;
                }
                if i > name_start {
                    tables.add_type_ident(&source[name_start..i]);
                }
            }
        } else {
            i += 1;
        }
    }

    tables
}

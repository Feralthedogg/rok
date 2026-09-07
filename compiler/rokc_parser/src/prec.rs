//! Operator precedence (spec 3.2.3) is fixed by the language.
//!
//! `fixed_prec` is the whole table. `#[infix]` / `#[prefix]` / `#[postfix]` only bind
//! a token to a trait method (spec 6.7); `PrecTable` records those
//! bindings for operator dispatch in HIR.

use std::collections::HashMap;

use rokc_ast::{AttrArg, AttrBody, Attribute, Item, Literal, Program, TraitItem};
use rokc_diagnostic::{ErrorKind, RokDiagnostic};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Fixity {
    Infix,
    Prefix,
    Postfix,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Assoc {
    Left,
    Right,
    /// Non-associative; chaining must be parenthesized.
    None,
}

/// Binding power of `as` / `is` (spec 3.2.3 level 11, left-assoc).
pub const CAST_PREC: u32 = 11;
/// Binding power of `??` (level 1, right-assoc).
pub const COALESCE_PREC: u32 = 1;

/// Spec 3.2.3: the language-fixed precedence of a built-in operator.
///
/// Dot-prefixed (broadcast) tokens share their scalar sibling's
/// row. `÷ ≡ ≠ ≤ ≥` are lexed as `/ == != <= >=`. `None` for tokens
/// outside the table.
#[must_use]
pub fn fixed_prec(symbol: &str, fixity: Fixity) -> Option<(u32, Assoc)> {
    let base = match symbol {
        "./" => "/",
        s if s.len() > 1 && s.starts_with('.') => &s[1..],
        s => s,
    };
    match fixity {
        Fixity::Prefix => matches!(symbol, "-" | "!" | "~" | "√").then_some((12, Assoc::Right)),
        // Level 13: the postfix row (`?`, member access). `?` itself is
        // language syntax; it is here only as a `like` target (spec 6.7.1).
        Fixity::Postfix => (symbol == "?").then_some((13, Assoc::Left)),
        Fixity::Infix => Some(match base {
            "<<" | ">>" => (10, Assoc::Left),
            "∘" => (9, Assoc::Left),
            "*" | "/" | "%" | "%%" | "×" | "⋅" | "÷" | "∩" => (8, Assoc::Left),
            "+" | "-" | "∪" => (7, Assoc::Left),
            "&" | "^" => (6, Assoc::Left),
            "|" => (5, Assoc::Left),
            "==" | "!=" | "<" | ">" | "<=" | ">=" | "≡" | "≠" | "≤" | "≥" | "∈" | "∉" | "⊂"
            | "⊆" => (4, Assoc::None),
            "&&" => (3, Assoc::Left),
            "||" => (2, Assoc::Left),
            _ => return None,
        }),
    }
}

#[derive(Clone, Debug)]
pub struct OpEntry {
    pub symbol: String,
    pub fixity: Fixity,
    // Trait method name this operator dispatches to (e.g. "add" for "+").
    pub method_name: String,
    // Trait declaring that method (e.g. "Add"). Only an impl of this trait
    // makes a user type support the operator (spec 0.4 / 6.4).
    pub trait_name: String,
    /// `#[infix("∈", swap)]`: `a ∈ s` calls `s.contains(a)` (spec 6.7.2).
    pub swap: bool,
    /// Binding level: the table's, or `like`'s for an extension token.
    pub level: (u32, Assoc),
    /// Registered by a standard-library root (only `rok::…` traits
    /// count); user registrations bind the user trait itself.
    pub from_lib: bool,
}

/// Registered extension operator tokens: what the lexer must recognize
/// and the level the parser gives them.
#[derive(Clone, Debug, Default)]
pub struct ExtOps {
    pub levels: HashMap<(String, Fixity), (u32, Assoc)>,
}

impl ExtOps {
    /// Distinct symbols, longest first (the lexer's longest match).
    #[must_use]
    pub fn symbols(&self) -> Vec<String> {
        let mut v: Vec<String> = self.levels.keys().map(|k| k.0.clone()).collect();
        v.sort_by_key(|s| std::cmp::Reverse(s.len()));
        v.dedup();
        v
    }

    /// Level of `symbol` at `fixity`: the fixed table, else a registration.
    #[must_use]
    pub fn level(&self, symbol: &str, fixity: Fixity) -> Option<(u32, Assoc)> {
        fixed_prec(symbol, fixity)
            .or_else(|| self.levels.get(&(symbol.to_owned(), fixity)).copied())
    }
}

/// Operator bindings: `(symbol, fixity) -> trait method`.
#[derive(Clone, Debug, Default)]
pub struct PrecTable {
    by_key: HashMap<(String, Fixity), OpEntry>,
}

impl PrecTable {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, entry: OpEntry) {
        self.by_key
            .insert((entry.symbol.clone(), entry.fixity), entry);
    }

    #[must_use]
    pub fn lookup(&self, symbol: &str, fixity: Fixity) -> Option<&OpEntry> {
        self.by_key.get(&(symbol.to_owned(), fixity))
    }

    pub fn entries(&self) -> impl Iterator<Item = &OpEntry> {
        self.by_key.values()
    }

    /// Extension tokens (spec 1.10.4): registered symbols outside the
    /// fixed table, with the level they took from `like`.
    #[must_use]
    pub fn ext_ops(&self) -> ExtOps {
        ExtOps {
            levels: self
                .by_key
                .values()
                .filter(|e| fixed_prec(&e.symbol, e.fixity).is_none())
                .map(|e| ((e.symbol.clone(), e.fixity), e.level))
                .collect(),
        }
    }

    /// Insert `entry`; an error if the token is already bound to a
    /// different trait method.
    pub fn merge(&mut self, entry: OpEntry) -> Option<RokDiagnostic> {
        if let Some(e) = self.lookup(&entry.symbol, entry.fixity) {
            if e.trait_name != entry.trait_name || e.method_name != entry.method_name {
                return Some(RokDiagnostic::error(
                    ErrorKind::Meta,
                    format!(
                        "operator `{}` is bound twice (`{}::{}` and `{}::{}`)",
                        entry.symbol,
                        e.trait_name,
                        e.method_name,
                        entry.trait_name,
                        entry.method_name
                    ),
                ));
            }
        }
        self.insert(entry);
        None
    }
}

/// Walk a program and collect every `#[infix]` / `#[prefix]` / `#[postfix]`
/// attribute attached to a trait method into a `PrecTable`.
///
/// Errors: a precedence/associativity argument (spec 6.7.2), `like` on a
/// table token, a token outside the table without `like`, aliases of one
/// method on different levels (6.7.12), and one token bound to two
/// different methods.
pub fn collect_prec_table(program: &Program) -> (PrecTable, Vec<RokDiagnostic>) {
    let mut table = PrecTable::new();
    let mut diags = Vec::new();
    for item in &program.items {
        let Item::Trait(t) = item else { continue };
        for ti in &t.items {
            let TraitItem::Method(m) = ti else { continue };
            let mut level: Option<(u32, Assoc)> = None;
            for attr in &m.attrs {
                let Some((fixity, symbol, lv, swap)) = collect_attr(attr, &mut diags) else {
                    continue;
                };
                if level.is_some_and(|l| l != lv) {
                    diags.push(meta_err(
                        attr,
                        format!(
                            "operator aliases of `{}` must share one precedence level (spec 6.7.12)",
                            m.name
                        ),
                    ));
                    continue;
                }
                level = Some(lv);
                let entry = OpEntry {
                    symbol,
                    fixity,
                    swap,
                    level: lv,
                    from_lib: false,
                    method_name: m.name.clone(),
                    trait_name: t.name.clone(),
                };
                if let Some(e) = table.merge(entry) {
                    diags.push(e.with_span(attr.span, ""));
                }
            }
        }
    }
    (table, diags)
}

fn meta_err(attr: &Attribute, msg: String) -> RokDiagnostic {
    RokDiagnostic::error(ErrorKind::Meta, msg).with_span(attr.span, "")
}

fn collect_attr(
    attr: &Attribute,
    diags: &mut Vec<RokDiagnostic>,
) -> Option<(Fixity, String, (u32, Assoc), bool)> {
    let fixity = match attr.name() {
        "infix" => Fixity::Infix,
        "prefix" => Fixity::Prefix,
        "postfix" => Fixity::Postfix,
        _ => return None,
    };
    let name = attr.name();
    let AttrBody::Args(args) = &attr.body else {
        diags.push(meta_err(
            attr,
            format!("`#[{name}]` needs an operator token"),
        ));
        return None;
    };
    let mut symbol: Option<String> = None;
    let mut like: Option<String> = None;
    let mut swap = false;
    for a in args {
        match a {
            AttrArg::Lit(Literal::Str(s)) if symbol.is_none() => symbol = Some(s.clone()),
            AttrArg::Word(w) if w == "swap" && fixity == Fixity::Infix && !swap => swap = true,
            AttrArg::KeyValue(k, Literal::Str(v)) if k == "like" && like.is_none() => {
                like = Some(v.clone());
            }
            _ => {
                diags.push(meta_err(
                    attr,
                    format!(
                        "`#[{name}]` takes only an operator token, `like = \"..\"` and `swap`: \
                         precedence and associativity are fixed by the language (spec 3.2.3)"
                    ),
                ));
                return None;
            }
        }
    }
    let Some(symbol) = symbol else {
        diags.push(meta_err(
            attr,
            format!("`#[{name}]` needs an operator token"),
        ));
        return None;
    };
    if symbol == "?" {
        diags.push(meta_err(
            attr,
            "`?` is language syntax (error propagation), not an operator token".to_owned(),
        ));
        return None;
    }
    let level = match (fixed_prec(&symbol, fixity), like) {
        (Some(lv), None) => lv,
        (Some(_), Some(_)) => {
            diags.push(meta_err(
                attr,
                format!(
                    "`{symbol}` has a fixed precedence (spec 3.2.3); `like` is only for new tokens"
                ),
            ));
            return None;
        }
        (None, Some(l)) => {
            let Some(lv) = fixed_prec(&l, fixity) else {
                diags.push(meta_err(
                    attr,
                    format!("`like = \"{l}\"` must name a {name} operator of the spec 3.2 table"),
                ));
                return None;
            };
            lv
        }
        (None, None) => {
            diags.push(meta_err(
                attr,
                format!(
                    "`{symbol}` is not a {name} operator of the spec 3.2 table; a new token \
                     needs `like = \"<existing token>\"`"
                ),
            ));
            return None;
        }
    };
    Some((fixity, symbol, level, swap))
}

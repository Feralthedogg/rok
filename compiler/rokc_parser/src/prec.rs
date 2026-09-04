//! Operator precedence table built from stdlib `#[infix]` / `#[prefix]` /
//! `#[postfix]` attributes. The language has no operator semantics of its
//! own; this table is the contract used during parsing.

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

#[derive(Clone, Debug)]
pub struct OpEntry {
    pub symbol: String,
    pub fixity: Fixity,
    pub prec: u32,
    pub assoc: Assoc,
    // Trait method name this operator dispatches to (e.g. "add" for "+").
    pub method_name: String,
    // Trait declaring that method (e.g. "Add"). Only an impl of this trait
    // makes a user type support the operator (spec 0.4 / 6.4).
    pub trait_name: String,
}

/// Operator lookup: `(symbol, fixity) -> entry`.
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
}

/// Walk a program and collect every `#[infix]` / `#[prefix]` / `#[postfix]`
/// attribute attached to a trait method into a `PrecTable`.
///
/// Conflicts (same `(symbol, fixity)` registered with mismatched
/// precedence or associativity) produce diagnostics.
pub fn collect_prec_table(program: &Program) -> (PrecTable, Vec<RokDiagnostic>) {
    let mut table = PrecTable::new();
    let mut diags = Vec::new();
    for item in &program.items {
        if let Item::Trait(t) = item {
            for ti in &t.items {
                if let TraitItem::Method(m) = ti {
                    for attr in &m.attrs {
                        collect_attr(attr, &t.name, &m.name, &mut table, &mut diags);
                    }
                }
            }
        }
    }
    (table, diags)
}

fn collect_attr(
    attr: &Attribute,
    trait_name: &str,
    method_name: &str,
    table: &mut PrecTable,
    diags: &mut Vec<RokDiagnostic>,
) {
    let fixity = match attr.name() {
        "infix" => Fixity::Infix,
        "prefix" => Fixity::Prefix,
        "postfix" => Fixity::Postfix,
        _ => return,
    };
    let AttrBody::Args(args) = &attr.body else {
        diags.push(
            RokDiagnostic::error(
                ErrorKind::Meta,
                format!("{} requires arguments", attr.name()),
            )
            .with_span(attr.span, ""),
        );
        return;
    };

    let mut symbol: Option<String> = None;
    let mut prec: Option<u32> = None;
    let mut assoc: Option<Assoc> = None;
    for a in args {
        match a {
            AttrArg::Lit(Literal::Str(s)) if symbol.is_none() => symbol = Some(s.clone()),
            AttrArg::KeyValue(k, Literal::Int(v)) if k == "prec" => {
                prec = parse_uint(v);
            }
            AttrArg::Word(w) => {
                assoc = match w.as_str() {
                    "left" => Some(Assoc::Left),
                    "right" => Some(Assoc::Right),
                    "none" => Some(Assoc::None),
                    _ => assoc,
                };
            }
            _ => {}
        }
    }

    let (Some(symbol), Some(prec)) = (symbol, prec) else {
        diags.push(
            RokDiagnostic::error(
                ErrorKind::Meta,
                format!("{} needs a symbol and `prec = N`", attr.name()),
            )
            .with_span(attr.span, ""),
        );
        return;
    };
    let assoc = match (fixity, assoc) {
        (Fixity::Infix, Some(a)) => a,
        (Fixity::Infix, None) => Assoc::None,
        // prefix / postfix are unary; associativity is meaningless.
        _ => Assoc::Right,
    };

    if let Some(existing) = table.lookup(&symbol, fixity) {
        if existing.prec != prec || existing.assoc != assoc {
            diags.push(
                RokDiagnostic::error(
                    ErrorKind::Meta,
                    format!(
                        "operator `{symbol}` registered twice with different precedence/associativity"
                    ),
                )
                .with_span(attr.span, ""),
            );
            return;
        }
    }

    table.insert(OpEntry {
        symbol,
        fixity,
        prec,
        assoc,
        method_name: method_name.to_owned(),
        trait_name: trait_name.to_owned(),
    });
}

fn parse_uint(s: &str) -> Option<u32> {
    let cleaned: String = s.chars().filter(|c| *c != '_').collect();
    cleaned.parse::<u32>().ok()
}

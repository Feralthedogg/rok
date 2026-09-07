//! Lang-slot table built from `#[lang(...)]` attributes (spec 6.4).
//!
//! `#[lang("slot_name")]` connects a stdlib item (trait, type, fn, const,
//! static) to a compiler-known slot. The compiler uses these slots to
//! desugar tokens (e.g. `+` → `add_trait::add`), pick the type of
//! built-in literals (`none` → `none_type`), and so on.
//!
//! This module just collects the registrations. Consumers (HIR, codegen)
//! look up slots through `LangTable`. Slot names are a closed set
//! (`KNOWN_SLOTS`, stdlib spec 0.4); an unknown name is a compile error
//! (spec 6.4.8).

use std::collections::HashMap;

use rokc_ast::{AttrArg, AttrBody, Attribute, Item, Literal, Program};
use rokc_diagnostic::{ErrorKind, RokDiagnostic};

/// Every slot name the compiler accepts (spec 6.4.8). Source of truth:
/// stdlib spec `000-meta/004-lang-slot-table.md`; change that table first.
pub const KNOWN_SLOTS: &[&str] = &[
    // 0.4.2 type slots
    "i32_type",
    "i64_type",
    "f32_type",
    "f64_type",
    "usize_type",
    "isize_type",
    "bool_type",
    "cchar_type",
    "str_type",
    "none_type",
    "int_type",
    "float_type",
    "char_type",
    "range_type",
    // 0.4.3 trait slots
    "iterator_trait",
    "into_iterator_trait",
    "index_trait",
    "index_set_trait",
    "slice_trait",
    "display_trait",
    "debug_trait",
    "future_trait",
    // operator / comparison trait slots (0.4.3; `library/core/ops.rok`, `marker.rok`)
    "add_trait",
    "sub_trait",
    "mul_trait",
    "div_trait",
    "rem_trait",
    "neg_trait",
    "not_trait",
    "bitnot_trait",
    "bitand_trait",
    "bitor_trait",
    "bitxor_trait",
    "shl_trait",
    "shr_trait",
    "eq_trait",
    "cmp_trait",
    "ord_trait",
    "hash_trait",
    "clone_trait",
    // auto (structural) marker traits (E3; `marker.rok`)
    "send_trait",
    "sync_trait",
    "logical_and_trait",
    "logical_or_trait",
    // 0.4.4 fn slots
    "panic_fn",
    "oom_fn",
    "unreachable_fn",
    // 0.4.5 method slots
    "drop_method",
];

/// What kind of item the `#[lang]` attribute is attached to. Consumers
/// can use this to validate slots that demand a specific shape (e.g.
/// `none_type` must be a type, `add_trait` must be a trait).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LangItemKind {
    Trait,
    Struct,
    Enum,
    Fn,
    Const,
    Static,
    TypeAlias,
}

#[derive(Clone, Debug)]
pub struct LangEntry {
    pub slot: String,
    pub item_name: String,
    pub kind: LangItemKind,
}

#[derive(Clone, Debug, Default)]
pub struct LangTable {
    by_slot: HashMap<String, LangEntry>,
}

impl LangTable {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn lookup(&self, slot: &str) -> Option<&LangEntry> {
        self.by_slot.get(slot)
    }

    pub fn entries(&self) -> impl Iterator<Item = &LangEntry> {
        self.by_slot.values()
    }

    /// Append a pre-validated entry. Caller is responsible for spec
    /// 6.4.6 duplicate detection — this just stores. Used by the driver
    /// to merge per-module tables.
    pub fn insert_entry(&mut self, entry: LangEntry) {
        self.by_slot.insert(entry.slot.clone(), entry);
    }
}

/// Walk a program and collect every `#[lang("...")]` attribute attached
/// to a top-level item. Spec 6.4.6: same slot name on two items is a
/// compile error.
pub fn collect_lang_table(program: &Program) -> (LangTable, Vec<RokDiagnostic>) {
    let mut table = LangTable::default();
    let mut diags = Vec::new();
    for item in &program.items {
        let (attrs, name, kind, span) = match item {
            Item::Trait(t) => (&t.attrs, &t.name, LangItemKind::Trait, t.span),
            Item::Struct(s) => (&s.attrs, &s.name, LangItemKind::Struct, s.span),
            Item::Enum(e) => (&e.attrs, &e.name, LangItemKind::Enum, e.span),
            Item::Fn(f) => (&f.attrs, &f.name, LangItemKind::Fn, f.span),
            Item::Const(c) => (&c.attrs, &c.name, LangItemKind::Const, c.span),
            Item::Static(s) => (&s.attrs, &s.name, LangItemKind::Static, s.span),
            Item::TypeAlias(a) => (&a.attrs, &a.name, LangItemKind::TypeAlias, a.span),
            _ => continue,
        };
        for attr in attrs {
            collect_attr(attr, name, kind, span, &mut table, &mut diags);
        }
        // Method slots (`drop_method`) sit on trait methods.
        if let Item::Trait(t) = item {
            for ti in &t.items {
                if let rokc_ast::TraitItem::Method(f) = ti {
                    let qualified = format!("{}::{}", t.name, f.name);
                    for attr in &f.attrs {
                        collect_attr(
                            attr,
                            &qualified,
                            LangItemKind::Fn,
                            f.span,
                            &mut table,
                            &mut diags,
                        );
                    }
                }
            }
        }
    }
    (table, diags)
}

fn collect_attr(
    attr: &Attribute,
    item_name: &str,
    kind: LangItemKind,
    item_span: rokc_diagnostic::Span,
    table: &mut LangTable,
    diags: &mut Vec<RokDiagnostic>,
) {
    if attr.name() != "lang" {
        return;
    }
    let AttrBody::Args(args) = &attr.body else {
        diags.push(
            RokDiagnostic::error(
                ErrorKind::Meta,
                "`#[lang(...)]` requires a single string-literal slot name (spec 6.4.2)".to_owned(),
            )
            .with_span(attr.span, ""),
        );
        return;
    };
    let mut slot: Option<String> = None;
    for a in args {
        match a {
            AttrArg::Lit(Literal::Str(s)) if slot.is_none() => slot = Some(s.clone()),
            _ => {}
        }
    }
    let Some(slot) = slot else {
        diags.push(
            RokDiagnostic::error(
                ErrorKind::Meta,
                "`#[lang(...)]` requires a single string-literal slot name (spec 6.4.2)".to_owned(),
            )
            .with_span(attr.span, ""),
        );
        return;
    };
    // Spec 6.4.8: unknown slot name → error.
    if !KNOWN_SLOTS.contains(&slot.as_str()) {
        diags.push(
            RokDiagnostic::error(
                ErrorKind::Meta,
                format!("unknown lang slot `{slot}` on `{item_name}` (spec 6.4.8)"),
            )
            .with_span(attr.span, ""),
        );
        return;
    }
    // Spec 6.4.6: same slot on two items → error.
    if let Some(prev) = table.by_slot.get(&slot) {
        diags.push(
            RokDiagnostic::error(
                ErrorKind::Meta,
                format!(
                    "lang slot `{slot}` is already bound to `{}` — cannot also bind to \
                     `{item_name}` (spec 6.4.6)",
                    prev.item_name
                ),
            )
            .with_span(item_span, ""),
        );
        return;
    }
    table.by_slot.insert(
        slot.clone(),
        LangEntry {
            slot,
            item_name: item_name.to_owned(),
            kind,
        },
    );
}

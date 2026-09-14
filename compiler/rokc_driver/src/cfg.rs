//! `#[cfg(...)]` predicate evaluation and item filtering.
//!
//! The cfg environment is the `--cfg` flags plus the target's keys
//! (`target_os`, `target_arch`, `target_pointer_width`, `target_family`,
//! `target_endian`); an item whose `#[cfg(p)]` is false is dropped, an
//! excluded inline `mod` with its whole subtree.

use rokc_ast::{Attribute, Item};

pub use rokc_parser::CfgEnv;

/// The target's cfg keys (spec 6.3.2).
pub fn add_target(env: &mut CfgEnv, target: &rokc_mir::Target) {
    let endian = if matches!(
        target.arch.as_str(),
        "powerpc" | "powerpc64" | "mips" | "sparc"
    ) {
        "big"
    } else {
        "little"
    };
    env.add_pair("target_os", &target.os);
    env.add_pair("target_arch", &target.arch);
    env.add_pair("target_pointer_width", &target.pointer_width.to_string());
    env.add_pair("target_family", target.family());
    env.add_pair("target_endian", endian);
    let host = if target.os == "linux" { "gnu" } else { "" };
    let last = target
        .triple
        .as_deref()
        .map_or(host, |t| t.rsplit('-').next().unwrap_or(""));
    if let Some(e) = ["gnu", "musl", "msvc"]
        .iter()
        .find(|k| last.starts_with(*k))
    {
        env.add_pair("target_env", e);
    }
}

/// Filter a list of items, dropping those whose `#[cfg(...)]` predicate
/// evaluates to false. Inline modules recurse so excluded subtrees are
/// fully pruned; their non-`Mod` children also get the same filter.
#[must_use]
pub fn filter_items(items: Vec<Item>, env: &CfgEnv) -> Vec<Item> {
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        if !item_passes(&item, env) {
            continue;
        }
        let item = match item {
            Item::Mod(mut m) => {
                if let Some(inner) = m.items.take() {
                    m.items = Some(filter_items(inner, env));
                }
                Item::Mod(m)
            }
            other => other,
        };
        out.push(item);
    }
    out
}

fn item_passes(item: &Item, env: &CfgEnv) -> bool {
    let attrs = item_attrs(item);
    // Spec 6.2.5: `#[test]` implies `#[cfg(test)]`; so does `#[bench]`
    // (a bench build is a test build, as with cargo).
    (env.has_flag("test")
        || !(crate::harness::is_test(attrs) || crate::harness::has_attr(attrs, "bench")))
        && attrs_pass(attrs, env)
}

/// Whether every `#[cfg(..)]` among `attrs` holds.
pub fn attrs_pass(attrs: &[Attribute], env: &CfgEnv) -> bool {
    env.attrs_pass(attrs)
}

fn item_attrs(item: &Item) -> &[Attribute] {
    match item {
        Item::Fn(f) => &f.attrs,
        Item::Struct(s) => &s.attrs,
        Item::Enum(e) => &e.attrs,
        Item::Union(u) => &u.attrs,
        Item::Trait(t) => &t.attrs,
        Item::Impl(i) => &i.attrs,
        Item::Const(c) => &c.attrs,
        Item::Static(s) => &s.attrs,
        Item::TypeAlias(a) => &a.attrs,
        Item::Mod(m) => &m.attrs,
        Item::Use(u) => &u.attrs,
        Item::Extern(e) => &e.attrs,
    }
}

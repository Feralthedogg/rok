//! `#[cfg(...)]` predicate evaluation and item filtering.
//!
//! The cfg environment is the `--cfg` flags plus the target's keys
//! (`target_os`, `target_arch`, `target_pointer_width`, `target_family`,
//! `target_endian`, `target_env`); an item whose `#[cfg(p)]` is false
//! is dropped, an excluded inline `mod` with its whole subtree. Members
//! and statements are dropped by the parser as they are read.

use rokc_ast::{Attribute, Item};

pub use rokc_parser::CfgEnv;

/// The value of a `--cfg feature=<f>` flag (quotes optional).
#[must_use]
pub fn feature_of(flag: &str) -> Option<&str> {
    let (k, v) = flag.split_once('=')?;
    (k.trim() == "feature").then(|| v.trim().trim_matches('"'))
}

/// The target's cfg keys (spec 6.3.2); `target_family` / `target_env`
/// only when the target has one.
pub fn add_target(env: &mut CfgEnv, target: &rokc_mir::Target) {
    env.add_pair("target_os", &target.os);
    env.add_pair("target_arch", &target.arch);
    env.add_pair("target_pointer_width", &target.pointer_width.to_string());
    env.add_pair("target_endian", &target.endian);
    for (k, v) in [
        ("target_family", &target.family),
        ("target_env", &target.env),
    ] {
        if !v.is_empty() {
            env.add_pair(k, v);
        }
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
    let attrs = item.attrs();
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

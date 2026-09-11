//! `#[cfg(...)]` predicate evaluation and item filtering.
//!
//! The cfg environment is the `--cfg` flags plus the target's keys
//! (`target_os`, `target_arch`, `target_pointer_width`, `target_family`,
//! `target_endian`); an item whose `#[cfg(p)]` is false is dropped, an
//! excluded inline `mod` with its whole subtree.

use std::collections::HashSet;

use rokc_ast::{AttrArg, AttrBody, Attribute, Item, Literal};

/// Resolved cfg environment. Contains the set of bare flags
/// (`{"test", "debug_assertions"}`) and key→value pairs
/// (`{"target_os": "macos", "target_pointer_width": "64"}`).
#[derive(Clone, Debug, Default)]
pub struct CfgEnv {
    flags: HashSet<String>,
    pairs: HashSet<(String, String)>,
}

impl CfgEnv {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add `--cfg` argument. Either `"flag"` or `"key=value"`.
    pub fn add(&mut self, raw: &str) {
        match raw.split_once('=') {
            Some((key, value)) => {
                self.pairs
                    .insert((key.trim().to_owned(), value.trim().to_owned()));
            }
            None => {
                self.flags.insert(raw.trim().to_owned());
            }
        }
    }

    /// The target's cfg keys (spec 6.3.2).
    pub fn add_target(&mut self, target: &rokc_mir::Target) {
        let endian = if matches!(
            target.arch.as_str(),
            "powerpc" | "powerpc64" | "mips" | "sparc"
        ) {
            "big"
        } else {
            "little"
        };
        for (k, v) in [
            ("target_os", target.os.as_str()),
            ("target_arch", target.arch.as_str()),
            ("target_pointer_width", &target.pointer_width.to_string()),
            ("target_family", target.family()),
            ("target_endian", endian),
        ] {
            self.pairs.insert((k.to_owned(), v.to_owned()));
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
    let attrs = item_attrs(item);
    // Spec 6.2.5: `#[test]` implies `#[cfg(test)]`; so does `#[bench]`
    // (a bench build is a test build, as with cargo).
    (env.flags.contains("test")
        || !(crate::harness::is_test(attrs) || crate::harness::has_attr(attrs, "bench")))
        && attrs_pass(attrs, env)
}

/// Whether every `#[cfg(..)]` among `attrs` holds.
pub fn attrs_pass(attrs: &[Attribute], env: &CfgEnv) -> bool {
    attrs.iter().all(|a| !is_cfg(a) || eval_cfg_attr(a, env))
}

fn is_cfg(a: &Attribute) -> bool {
    a.path.len() == 1 && a.path[0] == "cfg"
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

fn eval_cfg_attr(a: &Attribute, env: &CfgEnv) -> bool {
    match &a.body {
        AttrBody::Args(args) if args.len() == 1 => eval_arg(&args[0], env),
        // `#[cfg]` with no body or with the wrong shape is treated as
        // "always-on" so attribute typos don't silently strip code.
        _ => true,
    }
}

fn eval_arg(arg: &AttrArg, env: &CfgEnv) -> bool {
    match arg {
        AttrArg::Word(name) => env.flags.contains(name),
        AttrArg::KeyValue(key, lit) => {
            let Some(value) = lit_to_string(lit) else {
                return false;
            };
            env.pairs.contains(&(key.clone(), value))
        }
        AttrArg::Nested { path, body } => {
            if path.len() != 1 {
                return true;
            }
            match (path[0].as_str(), body.as_ref()) {
                ("all", AttrBody::Args(inner)) => inner.iter().all(|a| eval_arg(a, env)),
                ("any", AttrBody::Args(inner)) => inner.iter().any(|a| eval_arg(a, env)),
                ("not", AttrBody::Args(inner)) if inner.len() == 1 => !eval_arg(&inner[0], env),
                _ => true,
            }
        }
        AttrArg::Lit(_) | AttrArg::Range { .. } => false,
    }
}

fn lit_to_string(lit: &Literal) -> Option<String> {
    match lit {
        Literal::Str(s) | Literal::RawStr(s) => Some(s.clone()),
        _ => None,
    }
}

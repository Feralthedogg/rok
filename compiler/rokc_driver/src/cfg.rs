//! `#[cfg(...)]` predicate evaluation and item filtering.
//!
//! Two responsibilities:
//! 1. Build a `CfgEnv` from the CLI's `--cfg` flags + a few automatic
//!    keys (`target_os`, `target_arch`, `target_pointer_width`,
//!    `target_family`, `target_endian`).
//! 2. Walk the parsed item list and drop any item whose `#[cfg(p)]`
//!    predicate `p` evaluates to false. Drops are recursive — an
//!    excluded inline `mod` removes its whole subtree.

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
                self.pairs.insert((key.trim().to_owned(), value.trim().to_owned()));
            }
            None => {
                self.flags.insert(raw.trim().to_owned());
            }
        }
    }

    /// Default cfg keys derived from the host build target. The full
    /// matrix is in spec 6.3.2; we cover the common ones.
    pub fn populate_target_defaults(&mut self) {
        let os = if cfg!(target_os = "macos") {
            "macos"
        } else if cfg!(target_os = "linux") {
            "linux"
        } else if cfg!(target_os = "windows") {
            "windows"
        } else {
            "unknown"
        };
        self.pairs
            .insert(("target_os".into(), os.into()));

        let arch = if cfg!(target_arch = "x86_64") {
            "x86_64"
        } else if cfg!(target_arch = "aarch64") {
            "aarch64"
        } else {
            "unknown"
        };
        self.pairs
            .insert(("target_arch".into(), arch.into()));

        let pw = if cfg!(target_pointer_width = "64") {
            "64"
        } else {
            "32"
        };
        self.pairs
            .insert(("target_pointer_width".into(), pw.into()));

        let family = if cfg!(target_family = "windows") {
            "windows"
        } else if cfg!(target_family = "wasm") {
            "wasm"
        } else {
            "unix"
        };
        self.pairs
            .insert(("target_family".into(), family.into()));

        // Endianness — most modern targets are little-endian.
        self.pairs.insert((
            "target_endian".into(),
            if cfg!(target_endian = "big") { "big" } else { "little" }.into(),
        ));
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
    item_attrs(item)
        .iter()
        .all(|a| !is_cfg(a) || eval_cfg_attr(a, env))
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
            let Some(value) = lit_to_string(lit) else { return false };
            env.pairs.contains(&(key.clone(), value))
        }
        AttrArg::Nested { path, body } => {
            if path.len() != 1 {
                return true;
            }
            match (path[0].as_str(), body.as_ref()) {
                ("all", AttrBody::Args(inner)) => inner.iter().all(|a| eval_arg(a, env)),
                ("any", AttrBody::Args(inner)) => inner.iter().any(|a| eval_arg(a, env)),
                ("not", AttrBody::Args(inner)) if inner.len() == 1 => {
                    !eval_arg(&inner[0], env)
                }
                _ => true,
            }
        }
        AttrArg::Lit(_) => false,
    }
}

fn lit_to_string(lit: &Literal) -> Option<String> {
    match lit {
        Literal::Str(s) | Literal::RawStr(s) => Some(s.clone()),
        _ => None,
    }
}

//! `use` declarations as a name-resolution table.
//!
//! The driver hands HIR a list of `(module_path, UseTree)` pairs — one
//! entry per `use` statement encountered, tagged with the module the
//! statement appeared in. We flatten those trees into per-module
//! `UseEntry` lists. Lower-time name resolution consults the entries
//! whenever a bare name fails to resolve through the local scopes and
//! module-path ancestors.

use std::collections::HashMap;

use rokc_ast::{UseTree, UseTreeKind};
use rokc_core::Visibility;
use rokc_diagnostic::{ErrorKind, RokDiagnostic};

/// One resolved `use` entry. All paths are stored fully qualified (no
/// `crate::` / `super::` / `self::` left in the strings) so the lookup
/// loop can do plain string concatenation.
#[derive(Clone, Debug)]
pub enum UseEntry {
    /// `use foo::bar;` or `use foo::bar as baz;`
    /// — the local name `local` resolves to `full`.
    Single { local: String, full: String },
    /// `use foo::*;` — bare name `name` is tried as `prefix::name`.
    Glob { prefix: String },
    /// `use foo::**;` — bare name `name` is tried as `prefix::name` and,
    /// recursively, in any descendant of `prefix`.
    GlobDeep { prefix: String },
}

/// Per-module use list, keyed by the module path the `use` appeared in.
/// Empty key = root module.
pub type UseTable = HashMap<String, Vec<UseEntry>>;

/// `pub use mod_path::name as alias;` — re-export. The lower pass
/// installs each entry as an fn-table alias so callers can reach the
/// item via `module_path::short_name` instead of its original path.
#[derive(Clone, Debug)]
pub struct ReExport {
    pub module_path: String,
    pub short_name: String,
    pub full_path: String,
    pub vis: Visibility,
}

/// Build the per-module use table plus the re-export list from
/// `(module_path, vis, UseTree)` triples. Group trees (`use foo::{a, b}`)
/// expand into multiple entries with the prefix prepended. Each `pub use`
/// (or `pub(...) use`) Single contributes both a use-table entry (so the
/// declaring module can use the short name itself) and a re-export the
/// lower pass installs as an fn-table alias. Returns diagnostics for any
/// `use` conflict (5.5.12: same short name imported from different full
/// paths inside one module).
#[must_use]
pub fn build_use_table(
    raw: &[(String, Visibility, UseTree)],
) -> (UseTable, Vec<ReExport>, Vec<RokDiagnostic>) {
    let mut table: UseTable = HashMap::new();
    let mut reexports: Vec<ReExport> = Vec::new();
    let mut diags: Vec<RokDiagnostic> = Vec::new();
    for (module_path, vis, tree) in raw {
        let mut entries = Vec::new();
        flatten_tree(tree, &[], module_path, &mut entries);
        // 5.5.12 duplicate-name detection. Compare each fresh single
        // import against earlier singles in the same module — duplicate
        // local with a different full path is an error; same full path
        // is silently allowed (5.5.11).
        let existing = table.entry(module_path.clone()).or_default();
        for entry in entries {
            if let UseEntry::Single { local, full } = &entry {
                if let Some(prev) = existing.iter().find_map(|e| match e {
                    UseEntry::Single { local: l, full: f } if l == local => Some(f.clone()),
                    _ => None,
                }) {
                    if &prev != full {
                        diags.push(RokDiagnostic::error(
                            ErrorKind::Module,
                            format!(
                                "name `{local}` imported twice with different targets: \
                                 `{prev}` and `{full}` in module `{}`",
                                if module_path.is_empty() { "<root>" } else { module_path },
                            ),
                        ));
                        continue;
                    }
                }
                // `pub use` with a Single entry yields a re-export.
                if *vis != Visibility::Private {
                    reexports.push(ReExport {
                        module_path: module_path.clone(),
                        short_name: local.clone(),
                        full_path: full.clone(),
                        vis: *vis,
                    });
                }
            }
            existing.push(entry);
        }
    }
    (table, reexports, diags)
}

/// Public alias of `flatten_tree` for the lower pass to expand a
/// function-local `use` into entries against the function's module.
pub fn flatten_tree_for_local(
    tree: &UseTree,
    accumulated: &[String],
    module_path: &str,
    out: &mut Vec<UseEntry>,
) {
    flatten_tree(tree, accumulated, module_path, out);
}

/// Walk a `UseTree`, accumulating segments through `Group` nesting.
/// Each leaf produces one `UseEntry`. The current `module_path` is
/// used to resolve `pkg::` / `sup::` roots. (`self::` is intentionally
/// not a `use` root — same-module children are reachable through the
/// lookup-time ancestors walk.)
fn flatten_tree(
    tree: &UseTree,
    accumulated: &[String],
    module_path: &str,
    out: &mut Vec<UseEntry>,
) {
    let mut prefix_segs: Vec<String> = accumulated.to_vec();
    let raw_segs: Vec<String> = tree.prefix.segments.iter().map(|s| s.name.clone()).collect();
    // Resolve the root segment if it's `crate` / `super` / `self`.
    let resolved = resolve_root(&raw_segs, module_path);
    prefix_segs.extend(resolved);

    match &tree.kind {
        UseTreeKind::Simple(alias) => {
            // `use a::b::c` → local `c` (or alias) → full `a::b::c`.
            let Some(leaf) = prefix_segs.last().cloned() else { return };
            let full = prefix_segs.join("::");
            let local = alias.clone().unwrap_or(leaf);
            out.push(UseEntry::Single { local, full });
        }
        UseTreeKind::Glob => {
            out.push(UseEntry::Glob {
                prefix: prefix_segs.join("::"),
            });
        }
        UseTreeKind::GlobRecursive => {
            out.push(UseEntry::GlobDeep {
                prefix: prefix_segs.join("::"),
            });
        }
        UseTreeKind::Group(children) => {
            for child in children {
                flatten_tree(child, &prefix_segs, module_path, out);
            }
        }
    }
}

/// Convert `pkg::a::b` / `sup::a` into an absolute `module_path`-rooted
/// segment list. Bare-ident roots (`a::b`) are taken as absolute already.
fn resolve_root(segs: &[String], module_path: &str) -> Vec<String> {
    if segs.is_empty() {
        return Vec::new();
    }
    match segs[0].as_str() {
        "pkg" => segs[1..].to_vec(),
        "sup" => {
            let mut parts: Vec<String> = if module_path.is_empty() {
                Vec::new()
            } else {
                module_path.split("::").map(str::to_owned).collect()
            };
            // Each leading `sup` pops one ancestor.
            let mut i = 0;
            while i < segs.len() && segs[i] == "sup" {
                if !parts.is_empty() {
                    parts.pop();
                }
                i += 1;
            }
            parts.extend(segs[i..].iter().cloned());
            parts
        }
        _ => segs.to_vec(),
    }
}

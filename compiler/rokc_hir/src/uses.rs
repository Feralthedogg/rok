//! `use` declarations as a name-resolution table.
//!
//! Each `use` tree, tagged with its module, is flattened into per-module
//! `UseEntry` lists. Name resolution consults them when a bare name
//! misses the local scopes and module ancestors.

use std::collections::HashMap;

use rokc_ast::{UseTree, UseTreeKind};
use rokc_core::Visibility;
use rokc_diagnostic::{ErrorKind, RokDiagnostic};

/// One resolved `use` entry. Paths are fully qualified (no `pkg::` /
/// `sup::` left), so lookup is plain concatenation.
#[derive(Clone, Debug)]
pub enum UseEntry {
    /// `use foo::bar [as baz];`: `local` resolves to `full`.
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

/// `pub use mod_path::name as alias;`, installed as an fn-table alias
/// at `module_path::short_name`.
#[derive(Clone, Debug)]
pub struct ReExport {
    pub module_path: String,
    pub short_name: String,
    pub full_path: String,
    pub vis: Visibility,
}

/// Build the per-module use table plus the re-export list from
/// `(module_path, vis, UseTree)` triples.
///
/// A `pub use` single yields both a use entry (for the declaring module)
/// and a re-export. Diagnoses one short name imported from two different
/// paths in one module (spec 5.5.12).
#[must_use]
pub fn build_use_table(
    raw: &[(String, Visibility, UseTree)],
) -> (UseTable, Vec<ReExport>, Vec<RokDiagnostic>) {
    let mut table: UseTable = HashMap::new();
    let mut reexports: Vec<ReExport> = Vec::new();
    let mut diags: Vec<RokDiagnostic> = Vec::new();
    for (module_path, vis, tree) in raw {
        let mut entries = Vec::new();
        let existing = table.entry(module_path.clone()).or_default();
        flatten_tree(tree, &[], module_path, existing, &mut entries);
        // The same full path imported twice is fine (spec 5.5.11).
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
                                if module_path.is_empty() {
                                    "<root>"
                                } else {
                                    module_path
                                },
                            ),
                        ));
                        continue;
                    }
                }
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
    flatten_tree(tree, accumulated, module_path, &[], out);
}

/// One `UseEntry` per leaf of `tree`; `module_path` resolves `pkg::` /
/// `sup::` roots. `self::` is not a root: lookup already walks the
/// module's ancestors.
fn flatten_tree(
    tree: &UseTree,
    accumulated: &[String],
    module_path: &str,
    earlier: &[UseEntry],
    out: &mut Vec<UseEntry>,
) {
    let mut prefix_segs: Vec<String> = accumulated.to_vec();
    let raw_segs: Vec<String> = tree
        .prefix
        .segments
        .iter()
        .map(|s| s.name.clone())
        .collect();
    // Only the first segment of the whole path is a root (`pkg`, `sup`,
    // `rok`, an earlier import, or a child module); group members extend
    // their prefix as written.
    if accumulated.is_empty() {
        prefix_segs.extend(resolve_root(&raw_segs, module_path, earlier));
    } else {
        prefix_segs.extend(raw_segs);
    }

    match &tree.kind {
        UseTreeKind::Simple(alias) => {
            // `use a::b::c` → local `c` (or alias) → full `a::b::c`.
            let Some(leaf) = prefix_segs.last().cloned() else {
                return;
            };
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
                flatten_tree(child, &prefix_segs, module_path, earlier, out);
            }
        }
    }
}

/// Convert `pkg::a::b` / `sup::a` into an absolute `module_path`-rooted
/// segment list. Bare-ident roots (`a::b`) are relative to the module.
fn resolve_root(segs: &[String], module_path: &str, earlier: &[UseEntry]) -> Vec<String> {
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
        // Spec 5.7: a bare root names something in the current module
        // (a child module); `rok::` is the virtual stdlib root.
        "rok" => segs.to_vec(),
        // Spec 5.5: a name an earlier `use` of this module brought in
        // (`use a::b; use b::c;`).
        first
            if earlier
                .iter()
                .any(|e| matches!(e, UseEntry::Single { local, .. } if local == first)) =>
        {
            let full = earlier
                .iter()
                .find_map(|e| match e {
                    UseEntry::Single { local, full } if local == first => Some(full.clone()),
                    _ => None,
                })
                .unwrap_or_default();
            full.split("::")
                .map(str::to_owned)
                .chain(segs[1..].iter().cloned())
                .collect()
        }
        _ if module_path.is_empty() => segs.to_vec(),
        _ => module_path
            .split("::")
            .map(str::to_owned)
            .chain(segs.iter().cloned())
            .collect(),
    }
}

//! `use` declarations as a name-resolution table.
//!
//! Each `use` tree, tagged with its module, is flattened into per-module
//! `UseEntry` lists. Name resolution consults them when a bare name
//! misses the local scopes and module ancestors.

use std::collections::{HashMap, HashSet};

use rokc_ast::{UseTree, UseTreeKind};
use rokc_core::Visibility;
use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};

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
/// `(module_path, vis, UseTree)` triples; `packages`: the dependencies'
/// top-level names (`HirInput::packages`).
///
/// A `pub use` single yields both a use entry (for the declaring module)
/// and a re-export. Diagnoses one short name imported from two different
/// paths in one module (spec 5.5.12).
#[must_use]
pub fn build_use_table(
    raw: &[(String, Visibility, UseTree)],
    packages: &[String],
) -> (UseTable, Vec<ReExport>, Vec<RokDiagnostic>) {
    crate::lower::set_packages(packages.to_vec());
    let mut table: UseTable = HashMap::new();
    let mut reexports: Vec<ReExport> = Vec::new();
    let mut diags: Vec<RokDiagnostic> = Vec::new();
    for (module_path, vis, tree) in raw {
        let mut entries = Vec::new();
        let existing = table.entry(module_path.clone()).or_default();
        flatten_tree(tree, None, module_path, existing, &mut entries);
        // The same full path imported twice is fine (spec 5.5.11).
        let existing = table.entry(module_path.clone()).or_default();
        for (entry, span) in entries {
            if let UseEntry::Single { local, full } = &entry {
                if let Some(prev) = existing.iter().find_map(|e| match e {
                    UseEntry::Single { local: l, full: f } if l == local => Some(f.clone()),
                    _ => None,
                }) {
                    if &prev != full {
                        diags.push(RokDiagnostic::error(
                            ErrorKind::Module,
                            span,
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

/// Unresolved module-level imports, reported at the leaf's path.
///
/// A leaf must name an item, an enum variant, a module, or a re-export. A
/// path rooted at a bare name (not `pkg` / `sup` / `rok`) may also start
/// with a name the module sees through one of its globs or the implicit
/// `use rok::core::**` (`use Result::*`).
#[must_use]
pub fn check_use_targets(
    raw: &[(String, Visibility, UseTree)],
    items: &[rokc_ast::Item],
    table: &UseTable,
    reexports: &[ReExport],
) -> Vec<RokDiagnostic> {
    use rokc_ast::{ExternItem, ImplItem, Item};
    let mut known: HashSet<String> = HashSet::new();
    for item in items {
        match item {
            Item::Fn(f) => drop(known.insert(f.name.clone())),
            Item::Struct(s) => drop(known.insert(s.name.clone())),
            Item::Union(u) => drop(known.insert(u.name.clone())),
            Item::Trait(t) => drop(known.insert(t.name.clone())),
            Item::Const(c) => drop(known.insert(c.name.clone())),
            Item::Static(s) => drop(known.insert(s.name.clone())),
            Item::TypeAlias(a) => drop(known.insert(a.name.clone())),
            Item::Enum(e) => {
                known.insert(e.name.clone());
                known.extend(e.variants.iter().map(|v| format!("{}::{}", e.name, v.name)));
            }
            // Methods carry only their module (`a::get`).
            Item::Impl(i) => known.extend(i.items.iter().filter_map(|m| match m {
                ImplItem::Method(f) => f.name.rsplit_once("::").map(|(m, _)| m.to_owned()),
                _ => None,
            })),
            Item::Extern(b) => known.extend(b.items.iter().map(|x| match x {
                ExternItem::Fn(f) => f.name.clone(),
                ExternItem::Static(s) => s.name.clone(),
            })),
            Item::Mod(_) | Item::Use(_) => {}
        }
    }
    known.extend(raw.iter().map(|(m, _, _)| m.clone()));
    known.extend(reexports.iter().map(|r| {
        if r.module_path.is_empty() {
            r.short_name.clone()
        } else {
            format!("{}::{}", r.module_path, r.short_name)
        }
    }));
    // Every ancestor of a known path is a module (or an enum).
    let modules: Vec<String> = known
        .iter()
        .flat_map(|k| k.match_indices("::").map(|(i, _)| k[..i].to_owned()))
        .collect();
    known.extend(modules);
    let mod_vis = crate::lower::module_visibility(items);
    let item_vis: HashMap<&str, Visibility> = items
        .iter()
        .filter_map(|i| match i {
            Item::Fn(f) => Some((f.name.as_str(), f.vis)),
            Item::Struct(s) => Some((s.name.as_str(), s.vis)),
            Item::Union(u) => Some((u.name.as_str(), u.vis)),
            Item::Trait(t) => Some((t.name.as_str(), t.vis)),
            Item::Const(c) => Some((c.name.as_str(), c.vis)),
            Item::Static(s) => Some((s.name.as_str(), s.vis)),
            Item::TypeAlias(a) => Some((a.name.as_str(), a.vis)),
            Item::Enum(e) => Some((e.name.as_str(), e.vis)),
            Item::Mod(m) => Some((m.name.as_str(), m.vis)),
            _ => None,
        })
        .collect();
    let mut diags = Vec::new();
    for (module_path, use_vis, tree) in raw {
        let bare = tree
            .prefix
            .segments
            .first()
            .is_some_and(|s| !matches!(s.name.as_str(), "pkg" | "sup" | "rok"));
        let earlier = table.get(module_path).map_or(&[][..], Vec::as_slice);
        let mut leaves = Vec::new();
        flatten_tree(tree, None, module_path, earlier, &mut leaves);
        for (entry, span) in leaves {
            let path = match &entry {
                UseEntry::Single { full, .. } => full,
                UseEntry::Glob { prefix } | UseEntry::GlobDeep { prefix } => prefix,
            };
            if let UseEntry::Single { full, .. } = &entry {
                if let Some(m) = crate::lower::hidden_module(&mod_vis, module_path, full) {
                    diags.push(RokDiagnostic::error(
                        ErrorKind::Module,
                        span,
                        crate::lower::hidden_module_msg(full, &m, module_path),
                    ));
                    continue;
                }
                // Spec 5.8.4: a named re-export reaches no further than
                // its item.
                if let Some(&vis) = item_vis.get(full.as_str()) {
                    let rank = crate::lower::visibility_rank;
                    if *use_vis != Visibility::Private && rank(*use_vis) > rank(vis) {
                        diags.push(RokDiagnostic::error(
                            ErrorKind::Module,
                            span,
                            format!(
                                "`{full}` is {} but re-exported as {} — a re-export can't \
                                 be wider than its item (spec 5.8.4)",
                                vis_word(vis),
                                vis_word(*use_vis)
                            ),
                        ));
                        continue;
                    }
                }
            }
            if path.is_empty() || known.contains(path) {
                continue;
            }
            // Spec 5.7.1: a bare root may also be a name this module sees
            // through a glob of its own or the implicit `use rok::core::**`.
            if bare {
                let written = path
                    .strip_prefix(module_path.as_str())
                    .and_then(|r| r.strip_prefix("::"))
                    .unwrap_or(path);
                let tail = format!("::{written}");
                let under = |prefix: &str| {
                    let prefix = format!("{prefix}::");
                    known
                        .iter()
                        .any(|k| k.starts_with(&prefix) && k.ends_with(&tail))
                };
                let globbed = earlier.iter().any(|e| match e {
                    UseEntry::Glob { prefix } => known.contains(&format!("{prefix}{tail}")),
                    UseEntry::GlobDeep { prefix } => under(prefix),
                    UseEntry::Single { .. } => false,
                });
                if globbed || under(crate::lower::CORE_PREFIX) {
                    continue;
                }
            }
            diags.push(RokDiagnostic::error(
                ErrorKind::Module,
                span,
                format!("unresolved import: `{path}` does not exist"),
            ));
        }
    }
    diags
}

const fn vis_word(v: Visibility) -> &'static str {
    match v {
        Visibility::Pub => "`pub`",
        Visibility::Pkg => "`pub(pkg)`",
        Visibility::Sub => "`pub(sub)`",
        Visibility::Private => "private",
    }
}

/// Public alias of `flatten_tree` for the lower pass to expand a
/// function-local `use` into entries against the function's module.
pub fn flatten_tree_for_local(tree: &UseTree, module_path: &str, out: &mut Vec<UseEntry>) {
    let mut leaves = Vec::new();
    flatten_tree(tree, None, module_path, &[], &mut leaves);
    out.extend(leaves.into_iter().map(|(e, _)| e));
}

/// One `UseEntry` per leaf of `tree`; `module_path` resolves `pkg::` /
/// `sup::` roots. `self::` is not a root: lookup already walks the
/// module's ancestors. `parent` is the resolved prefix of the enclosing
/// group, `None` at the top of the tree.
fn flatten_tree(
    tree: &UseTree,
    parent: Option<&[String]>,
    module_path: &str,
    earlier: &[UseEntry],
    out: &mut Vec<(UseEntry, Span)>,
) {
    let span = tree.prefix.span;
    let raw_segs: Vec<String> = tree
        .prefix
        .segments
        .iter()
        .map(|s| s.name.clone())
        .collect();
    // Only the first segment of the whole path is a root (`pkg`, `sup`,
    // `rok`, an earlier import, or a child module); group members extend
    // their prefix as written. A resolved parent may be empty
    // (`pkg::{..}` at the package root), so presence, not length, decides.
    let prefix_segs: Vec<String> = match parent {
        None => resolve_root(&raw_segs, module_path, earlier),
        Some(p) => p.iter().cloned().chain(raw_segs).collect(),
    };

    match &tree.kind {
        UseTreeKind::Simple(alias) => {
            // `use a::b::c` → local `c` (or alias) → full `a::b::c`.
            let Some(leaf) = prefix_segs.last().cloned() else {
                return;
            };
            let full = prefix_segs.join("::");
            let local = alias.clone().unwrap_or(leaf);
            out.push((UseEntry::Single { local, full }, span));
        }
        UseTreeKind::Glob => {
            out.push((
                UseEntry::Glob {
                    prefix: prefix_segs.join("::"),
                },
                span,
            ));
        }
        UseTreeKind::GlobRecursive => {
            out.push((
                UseEntry::GlobDeep {
                    prefix: prefix_segs.join("::"),
                },
                span,
            ));
        }
        UseTreeKind::Group(children) => {
            for child in children {
                flatten_tree(child, Some(&prefix_segs), module_path, earlier, out);
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
    let strs: Vec<&str> = segs.iter().map(String::as_str).collect();
    if let Some(rooted) = crate::lower::root_path(&strs, module_path) {
        return rooted;
    }
    match segs[0].as_str() {
        // A dependency's name is a top-level name in every module (902.3).
        first if crate::lower::is_dependency(first) => segs.to_vec(),
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

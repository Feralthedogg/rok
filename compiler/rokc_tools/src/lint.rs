//! `rokc lint` (spec 901 `rokc lint`, 6.2.9): style and common-mistake
//! checks over a package that type-checked (front end through HIR, no
//! codegen).
//!
//! Most lints walk the user package's AST as parsed (`SourceFile`s, kept
//! by the driver); `redundant_cast` / `redundant_clone` read HIR types.
//! Levels: each lint's default, then the command line (`-A/-W/-D name`,
//! later wins; `rok` turns `rok.rokon` `lints` into leading flags), then
//! `#[allow/warn/deny(name)]` on an enclosing item, `mod`, or `#![..]`
//! at the top of a file (innermost wins).
//!
//! Items have only start spans, so an item's attribute scope runs to the next sibling item's start. Name-based lints (`dead_code`,
//! `unused_imports`, `deprecated`, `unused_must_use`) match by the last
//! path segment, so a same-named item elsewhere hides a finding (never
//! the reverse). Names starting with an uppercase letter are not tracked
//! as locals (a pattern `Foo` may name a constant).

use std::collections::{HashMap, HashSet};

use rokc_ast::{
    AccessTail, AttrArg, AttrBody, Attribute, Block, CallArg, Expr, ExprKind, FnDef, ImplItem,
    Item, Literal, Pattern, PatternKind, Stmt, StmtKind, TraitItem, TryKind, Ty, TyKind, UseTree,
    UseTreeKind,
};
use rokc_core::Visibility;
use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};
use rokc_hir::walk::{AstVisitor, walk_fn, walk_item, walk_stmt};
use rokc_hir::{HirExprKind, HirTy};
use rokc_interface::{CompileResult, SourceFile};

use crate::analysis::{each_block, short_name};

pub use rokc_core::lint::Level;

pub struct Lint {
    pub name: &'static str,
    pub default: Level,
    pub desc: &'static str,
}

const fn warn(name: &'static str, desc: &'static str) -> Lint {
    Lint {
        name,
        default: Level::Warn,
        desc,
    }
}

/// Every lint, with its default level.
pub const LINTS: &[Lint] = &[
    warn(
        "unused_variables",
        "a local or parameter that is never read",
    ),
    warn(
        "unused_imports",
        "a `use` whose name the module never mentions",
    ),
    warn("dead_code", "a non-`pub` function nothing calls"),
    warn(
        "unreachable_code",
        "statements after `return` / `break` / `continue` / `throw` / `panic`",
    ),
    warn(
        "unused_must_use",
        "the result of a `#[must_use]` function is discarded",
    ),
    warn(
        "ignored_error",
        "a `try? f();` statement silently drops the error",
    ),
    warn(
        "shadowed_loop_var",
        "a `let` in a `for` body re-binds the loop variable",
    ),
    warn(
        "nan_comparison",
        "comparing with NaN is always false (`!=`: true)",
    ),
    warn("none_comparison", "`x == none` instead of `x is none`"),
    warn(
        "bool_comparison",
        "comparing a `bool` with `true` / `false`",
    ),
    warn("self_assignment", "`x = x;`"),
    warn("while_true", "`while true` instead of `loop`"),
    warn("redundant_cast", "`x as T` where `x` already has type `T`"),
    warn("redundant_clone", "`.clone()` of a primitive value"),
    warn(
        "non_snake_case",
        "functions, locals, parameters and modules are snake_case",
    ),
    warn(
        "non_camel_case_types",
        "types, traits and variants are UpperCamelCase",
    ),
    warn(
        "non_upper_case_globals",
        "`const` / `static` names are UPPER_SNAKE_CASE",
    ),
    warn(
        "confusable_idents",
        "identifiers that look alike (spec 1.4.3)",
    ),
    warn("deprecated", "use of a `#[deprecated]` function"),
    warn(
        "unclosed_resource",
        "a local holding a `Drop` resource (file, socket, child) that is never closed",
    ),
];

/// Lint groups usable wherever a lint name is (`all`: every lint).
const GROUPS: &[(&str, &[&str])] = &[
    (
        "unused",
        &[
            "unused_variables",
            "unused_imports",
            "dead_code",
            "unreachable_code",
            "unused_must_use",
        ],
    ),
    (
        "nonstandard_style",
        &[
            "non_snake_case",
            "non_camel_case_types",
            "non_upper_case_globals",
        ],
    ),
];

/// The lints `name` stands for (a lint, a group, `all`), or `None`.
#[must_use]
pub fn expand(name: &str) -> Option<Vec<&'static str>> {
    if name == "all" {
        return Some(LINTS.iter().map(|l| l.name).collect());
    }
    if let Some(l) = LINTS.iter().find(|l| l.name == name) {
        return Some(vec![l.name]);
    }
    GROUPS
        .iter()
        .find(|(g, _)| *g == name)
        .map(|(_, ls)| ls.to_vec())
}

/// `rokc lint --list` text.
#[must_use]
pub fn list() -> String {
    let mut s = String::from("lints (default level):\n");
    for l in LINTS {
        s.push_str(&format!(
            "  {:<24} {:<5} {}\n",
            l.name,
            l.default.name(),
            l.desc
        ));
    }
    s.push_str("groups: all");
    for (g, ls) in GROUPS {
        s.push_str(&format!(", {g} ({})", ls.join(", ")));
    }
    s.push('\n');
    s
}

/// A lint hit before its level is known.
struct Finding {
    lint: &'static str,
    span: Span,
    msg: String,
    notes: Vec<String>,
    secondary: Option<(Span, String)>,
}

/// An attribute scope: `[start, end)` of file `file`, with the levels its
/// `#[allow/warn/deny]` attributes set.
struct Region {
    file: u32,
    start: u32,
    end: u32,
    levels: Vec<(Level, &'static str, Span)>,
}

/// Lint a front-end result (`Session::set_keep_ast`).
///
/// `cli` is the command line's `-A/-W/-D` in order. Returns what to report: the
/// compile warnings (confusable-identifier ones become the
/// `confusable_idents` lint), then the findings, as warnings or (deny)
/// errors.
#[must_use]
pub fn run(result: &CompileResult, cli: &[(Level, String)]) -> Vec<RokDiagnostic> {
    let mut out = Vec::new();
    let mut base: HashMap<&'static str, (Level, Option<String>)> =
        LINTS.iter().map(|l| (l.name, (l.default, None))).collect();
    for (lvl, name) in cli {
        match expand(name) {
            Some(ls) => {
                for l in ls {
                    base.insert(l, (*lvl, Some(format!("{} {name}", lvl.flag()))));
                }
            }
            None => out.push(RokDiagnostic::warning(
                ErrorKind::Lint,
                format!("unknown lint `{name}` on the command line"),
            )),
        }
    }

    let texts = rokc_diagnostic::registered_files();
    let user: Vec<&SourceFile> = result
        .sources
        .iter()
        .filter(|f| f.package.is_empty())
        .collect();
    let mut cx = Cx::new(&result.sources, &texts);
    let mut regions = Vec::new();
    for f in &user {
        regions.extend(file_regions(f, &user, &mut out));
        cx.file(f);
    }
    cx.dead_code(&user);
    if let Some(m) = result.modules.first() {
        cx.hir(&m.hir, &user);
    }
    for w in &result.warnings {
        let confusable = w.kind == ErrorKind::Lexical
            && (w.message.contains("confusable") || w.message.contains("mixes Cyrillic"));
        match (confusable, &w.primary) {
            (true, Some(p)) => cx.findings.push(Finding {
                lint: "confusable_idents",
                span: p.span,
                msg: w.message.clone(),
                notes: Vec::new(),
                secondary: None,
            }),
            _ => out.push(w.clone()),
        }
    }

    let mut findings = cx.findings;
    findings.sort_by_key(|f| (f.span.file, f.span.start, f.lint));
    findings.dedup_by(|a, b| a.lint == b.lint && a.span == b.span);
    for f in findings {
        let generated = text_at(&texts, f.span).is_some_and(|t| t.starts_with('#'));
        if generated {
            continue;
        }
        let (mut level, mut from) = base[f.lint].clone();
        let mut at = None;
        for r in &regions {
            if r.file == f.span.file && r.start <= f.span.start && f.span.start < r.end {
                for &(lvl, name, span) in &r.levels {
                    if name == f.lint {
                        level = lvl;
                        at = Some((span, lvl));
                        from = None;
                    }
                }
            }
        }
        if level == Level::Allow {
            continue;
        }
        let mut d = if level == Level::Deny {
            RokDiagnostic::error(ErrorKind::Lint, f.msg)
        } else {
            RokDiagnostic::warning(ErrorKind::Lint, f.msg)
        }
        .with_span(f.span, "");
        if let Some((span, msg)) = f.secondary {
            d = d.with_secondary(span, msg);
        }
        for n in f.notes {
            d = d.with_note(n);
        }
        d = match (at, from) {
            (Some((span, lvl)), _) => {
                d.with_secondary(span, format!("`#[{}({})]` set here", lvl.name(), f.lint))
            }
            (None, Some(flag)) => d.with_note(format!("`{flag}` on the command line")),
            (None, None) => d.with_note(format!("`#[{}({})]` on by default", level.name(), f.lint)),
        };
        out.push(d);
    }
    out
}

/// The source text from `span` to the end of its line.
fn text_at(texts: &[(String, String)], span: Span) -> Option<&str> {
    let (_, text) = texts.get(usize::try_from(span.file).ok()?.checked_sub(1)?)?;
    let rest = text.get(usize::try_from(span.start).ok()?..)?;
    Some(rest.split('\n').next().unwrap_or(rest))
}

/// `(level, lint, attribute span)` for each lint an `allow` / `warn` /
/// `deny` attribute names; unknown names are reported to `out`.
fn levels_of(
    attrs: &[Attribute],
    out: &mut Vec<RokDiagnostic>,
) -> Vec<(Level, &'static str, Span)> {
    let mut levels = Vec::new();
    for a in attrs {
        let Some(lvl) = Level::parse(a.name()) else {
            continue;
        };
        let AttrBody::Args(args) = &a.body else {
            continue;
        };
        for arg in args {
            let name = match arg {
                AttrArg::Word(w) => w.as_str(),
                AttrArg::Nested { path, .. } => path.last().map_or("", String::as_str),
                _ => "",
            };
            match expand(name) {
                Some(ls) => levels.extend(ls.into_iter().map(|l| (lvl, l, a.span))),
                None => out.push(
                    RokDiagnostic::warning(ErrorKind::Lint, format!("unknown lint `{name}`"))
                        .with_span(a.span, ""),
                ),
            }
        }
    }
    levels
}

fn item_attrs(item: &Item) -> &[Attribute] {
    match item {
        Item::Fn(x) => &x.attrs,
        Item::Struct(x) => &x.attrs,
        Item::Enum(x) => &x.attrs,
        Item::Union(x) => &x.attrs,
        Item::Trait(x) => &x.attrs,
        Item::Impl(x) => &x.attrs,
        Item::Const(x) => &x.attrs,
        Item::Static(x) => &x.attrs,
        Item::TypeAlias(x) => &x.attrs,
        Item::Mod(x) => &x.attrs,
        Item::Use(x) => &x.attrs,
        Item::Extern(x) => &x.attrs,
    }
}

/// Where an item's text starts: its first attribute or its first token.
fn item_start(attrs: &[Attribute], span: Span) -> u32 {
    attrs
        .iter()
        .map(|a| a.span.start)
        .chain([span.start])
        .min()
        .unwrap_or(span.start)
}

/// Attribute scopes of one file, outermost first: the file (its `mod`
/// declarations' attributes up the module path, then its `#![..]`),
/// then each item down the tree.
fn file_regions(f: &SourceFile, user: &[&SourceFile], out: &mut Vec<RokDiagnostic>) -> Vec<Region> {
    let mut attrs: Vec<Attribute> = Vec::new();
    // `#[allow(x)] mod m;` in the parent file covers all of `m.rok`.
    for depth in 1..=f.module.len() {
        let (parent, name) = (&f.module[..depth - 1], &f.module[depth - 1]);
        for p in user.iter().filter(|p| p.module == parent) {
            for item in &p.items {
                if let Item::Mod(m) = item {
                    if m.name == *name && m.items.is_none() {
                        attrs.extend(m.attrs.iter().cloned());
                    }
                }
            }
        }
    }
    attrs.extend(f.attrs.iter().cloned());
    let mut regions = vec![Region {
        file: f.file_id,
        start: 0,
        end: u32::MAX,
        levels: levels_of(&attrs, out),
    }];
    let spans: Vec<(u32, &[Attribute])> = f
        .items
        .iter()
        .map(|i| (item_start(item_attrs(i), i.span()), item_attrs(i)))
        .collect();
    item_regions(f.file_id, &f.items, &spans, u32::MAX, &mut regions, out);
    regions
}

fn item_regions(
    file: u32,
    items: &[Item],
    starts: &[(u32, &[Attribute])],
    end: u32,
    regions: &mut Vec<Region>,
    out: &mut Vec<RokDiagnostic>,
) {
    for (i, item) in items.iter().enumerate() {
        let (start, attrs) = starts[i];
        let next = starts
            .iter()
            .map(|(s, _)| *s)
            .filter(|s| *s > start)
            .min()
            .unwrap_or(end)
            .min(end);
        let levels = levels_of(attrs, out);
        if !levels.is_empty() {
            regions.push(Region {
                file,
                start,
                end: next,
                levels,
            });
        }
        let fns: Vec<&FnDef> = match item {
            Item::Impl(im) => im
                .items
                .iter()
                .filter_map(|ii| match ii {
                    ImplItem::Method(m) => Some(m),
                    _ => None,
                })
                .collect(),
            Item::Trait(t) => t
                .items
                .iter()
                .filter_map(|ti| match ti {
                    TraitItem::Method(m) => Some(m),
                    _ => None,
                })
                .collect(),
            Item::Mod(m) => {
                if let Some(inner) = &m.items {
                    let s: Vec<(u32, &[Attribute])> = inner
                        .iter()
                        .map(|i| (item_start(item_attrs(i), i.span()), item_attrs(i)))
                        .collect();
                    item_regions(file, inner, &s, next, regions, out);
                }
                Vec::new()
            }
            _ => Vec::new(),
        };
        let starts: Vec<u32> = fns.iter().map(|m| item_start(&m.attrs, m.span)).collect();
        for (k, m) in fns.iter().enumerate() {
            let levels = levels_of(&m.attrs, out);
            if levels.is_empty() {
                continue;
            }
            let mend = starts
                .iter()
                .copied()
                .filter(|s| *s > starts[k])
                .min()
                .unwrap_or(next)
                .min(next);
            regions.push(Region {
                file,
                start: starts[k],
                end: mend,
                levels,
            });
        }
    }
}

/// `#[name]` / `#[name = "msg"]` / `#[name("msg")]`: its message (empty
/// when it has none), or `None` without the attribute.
fn attr_msg(attrs: &[Attribute], name: &str) -> Option<String> {
    let a = attrs.iter().find(|a| a.name() == name)?;
    let lit = match &a.body {
        AttrBody::Value(l) => Some(l),
        AttrBody::Args(args) => args.iter().find_map(|x| match x {
            AttrArg::Lit(l) => Some(l),
            _ => None,
        }),
        AttrBody::Empty => None,
    };
    Some(match lit {
        Some(Literal::Str(s) | Literal::RawStr(s)) => s.trim_matches('"').to_owned(),
        _ => String::new(),
    })
}

fn has_attr(attrs: &[Attribute], names: &[&str]) -> bool {
    attrs
        .iter()
        .any(|a| names.contains(&a.name()) || a.path.first().is_some_and(|p| p.starts_with('#')))
}

/// Every function in `items`, impl / trait methods and inline modules
/// included.
fn each_fn(items: &[Item], visit: &mut dyn FnMut(&FnDef)) {
    for i in items {
        match i {
            Item::Fn(f) => visit(f),
            Item::Impl(im) => im.items.iter().for_each(|ii| {
                if let ImplItem::Method(m) = ii {
                    visit(m);
                }
            }),
            Item::Trait(t) => t.items.iter().for_each(|ti| {
                if let TraitItem::Method(m) = ti {
                    visit(m);
                }
            }),
            Item::Mod(m) => each_fn(m.items.as_deref().unwrap_or(&[]), visit),
            _ => {}
        }
    }
}

/// Trait names declared in `items`.
fn collect_traits(items: &[Item], out: &mut HashSet<String>) {
    for i in items {
        match i {
            Item::Trait(t) => {
                out.insert(t.name.clone());
            }
            Item::Mod(m) => collect_traits(m.items.as_deref().unwrap_or(&[]), out),
            _ => {}
        }
    }
}

/// Every function of `files` (impl / trait methods too), by short name:
/// the message of the `attr` attribute, for names no function without it
/// shares.
fn marked_fns(files: &[SourceFile], attr: &str) -> HashMap<String, String> {
    let mut marked: HashMap<String, String> = HashMap::new();
    let mut plain: HashSet<String> = HashSet::new();
    let mut visit = |f: &FnDef| match attr_msg(&f.attrs, attr) {
        Some(m) => {
            marked.insert(f.name.clone(), m);
        }
        None => {
            plain.insert(f.name.clone());
        }
    };
    for f in files {
        each_fn(&f.items, &mut visit);
    }
    marked.retain(|n, _| !plain.contains(n));
    marked
}

fn is_snake(n: &str) -> bool {
    !n.chars().any(|c| c.is_ascii_uppercase())
}

fn is_camel(n: &str) -> bool {
    let t = n.trim_start_matches('_');
    !t.starts_with(|c: char| c.is_ascii_lowercase()) && !t.contains('_')
}

fn is_upper(n: &str) -> bool {
    !n.chars().any(|c| c.is_ascii_lowercase())
}

fn to_snake(n: &str) -> String {
    let mut s = String::new();
    for (i, c) in n.char_indices() {
        if c.is_ascii_uppercase() {
            if i > 0 && !s.ends_with('_') {
                s.push('_');
            }
            s.push(c.to_ascii_lowercase());
        } else {
            s.push(c);
        }
    }
    s
}

fn to_camel(n: &str) -> String {
    n.split('_')
        .filter(|p| !p.is_empty())
        .map(|p| {
            let mut cs = p.chars();
            cs.next()
                .map(|c| c.to_ascii_uppercase().to_string() + cs.as_str())
                .unwrap_or_default()
        })
        .collect()
}

struct Binding {
    name: String,
    span: Span,
    used: bool,
    is_loop: bool,
}

struct Scope {
    bindings: Vec<Binding>,
    /// Parameters fixed by a trait or with no body: never "unused".
    exempt: bool,
}

/// The AST pass: one visitor over every user file.
struct Cx<'a> {
    texts: &'a [(String, String)],
    findings: Vec<Finding>,
    scopes: Vec<Scope>,
    exempt_next: bool,
    /// Plain-assignment targets (`x = ..`): not reads.
    assign_targets: HashSet<(u32, u32)>,
    /// Spans of `for` patterns and their parts.
    loop_pats: HashSet<(u32, u32)>,
    /// Names mentioned in the current file / any user file.
    file_names: HashSet<String>,
    all_names: HashSet<String>,
    /// `(file, start)` of user-written casts (`x as T`; f-strings
    /// desugar to casts too).
    casts: HashSet<(u32, u32)>,
    must_use: HashMap<String, String>,
    deprecated: HashMap<String, String>,
    traits: HashSet<String>,
}

const fn key(s: Span) -> (u32, u32) {
    (s.file, s.start)
}

impl<'a> Cx<'a> {
    fn new(all: &[SourceFile], texts: &'a [(String, String)]) -> Self {
        let mut traits = HashSet::new();
        for f in all {
            collect_traits(&f.items, &mut traits);
        }
        Self {
            texts,
            findings: Vec::new(),
            scopes: Vec::new(),
            exempt_next: false,
            assign_targets: HashSet::new(),
            loop_pats: HashSet::new(),
            file_names: HashSet::new(),
            all_names: HashSet::new(),
            casts: HashSet::new(),
            must_use: marked_fns(all, "must_use"),
            deprecated: marked_fns(all, "deprecated"),
            traits,
        }
    }

    fn hit(&mut self, lint: &'static str, span: Span, msg: String) {
        self.findings.push(Finding {
            lint,
            span,
            msg,
            notes: Vec::new(),
            secondary: None,
        });
    }

    fn name_lint(&mut self, what: &str, name: &str, span: Span, kind: u8) {
        let (ok, lint, fixed, style) = match kind {
            0 => (
                is_snake(name),
                "non_snake_case",
                to_snake(name),
                "a snake case",
            ),
            1 => (
                is_camel(name),
                "non_camel_case_types",
                to_camel(name),
                "an upper camel case",
            ),
            _ => (
                is_upper(name),
                "non_upper_case_globals",
                to_snake(name).to_ascii_uppercase(),
                "an upper case",
            ),
        };
        if !ok {
            self.findings.push(Finding {
                lint,
                span,
                msg: format!("{what} `{name}` should have {style} name"),
                notes: vec![format!("rename it to `{fixed}`")],
                secondary: None,
            });
        }
    }

    fn file(&mut self, f: &SourceFile) {
        self.file_names.clear();
        for a in &f.attrs {
            self.attr_names(a);
        }
        for item in &f.items {
            self.item(item);
        }
        if !f.stmts.is_empty() {
            self.unreachable(&f.stmts, None);
            self.push_scope();
            for s in &f.stmts {
                walk_stmt(self, s);
            }
            self.pop_scope();
        }
        self.unused_imports(&f.items);
        let names = std::mem::take(&mut self.file_names);
        self.all_names.extend(names);
    }

    fn attr_names(&mut self, a: &Attribute) {
        self.file_names.extend(a.path.iter().cloned());
        if let AttrBody::Args(args) = &a.body {
            for x in args {
                if let AttrArg::Word(w) = x {
                    self.file_names.insert(w.clone());
                }
            }
        }
    }

    fn item(&mut self, item: &Item) {
        for a in item_attrs(item) {
            self.attr_names(a);
        }
        match item {
            Item::Fn(f) => {
                if !has_attr(&f.attrs, &["no_mangle", "export_name"]) {
                    self.name_lint("function", &f.name, f.span, 0);
                }
                self.func(f, false);
            }
            Item::Struct(s) => {
                self.name_lint("type", &s.name, s.span, 1);
                walk_item(self, item);
            }
            Item::Union(u) => {
                self.name_lint("type", &u.name, u.span, 1);
                walk_item(self, item);
            }
            Item::TypeAlias(t) => {
                self.name_lint("type", &t.name, t.span, 1);
                walk_item(self, item);
            }
            Item::Enum(e) => {
                self.name_lint("type", &e.name, e.span, 1);
                for v in &e.variants {
                    self.name_lint("variant", &v.name, v.span, 1);
                }
                walk_item(self, item);
            }
            Item::Trait(t) => {
                self.name_lint("trait", &t.name, t.span, 1);
                for ti in &t.items {
                    if let TraitItem::Method(m) = ti {
                        self.name_lint("method", &m.name, m.span, 0);
                        self.func(m, true);
                    }
                }
            }
            Item::Impl(im) => {
                self.ty_names(&im.self_ty);
                if let Some(p) = &im.trait_path {
                    self.file_names
                        .extend(p.segments.iter().map(|s| s.name.clone()));
                }
                for ii in &im.items {
                    match ii {
                        ImplItem::Method(m) => {
                            if im.trait_path.is_none() {
                                self.name_lint("method", &m.name, m.span, 0);
                            }
                            self.func(m, im.trait_path.is_some());
                        }
                        ImplItem::Const(c) => {
                            self.name_lint("constant", &c.name, c.span, 2);
                            self.scoped(|cx| rokc_hir::walk::walk_expr(cx, &c.value));
                        }
                        ImplItem::AssocType { ty, .. } => self.ty_names(ty),
                    }
                }
            }
            Item::Const(c) => {
                self.name_lint("constant", &c.name, c.span, 2);
                self.scoped(|cx| walk_item(cx, item));
            }
            Item::Static(s) => {
                self.name_lint("static", &s.name, s.span, 2);
                self.scoped(|cx| walk_item(cx, item));
            }
            Item::Mod(m) => {
                self.name_lint("module", &m.name, m.span, 0);
                for i in m.items.as_deref().unwrap_or(&[]) {
                    self.item(i);
                }
            }
            // C names are not ours to style.
            Item::Use(_) | Item::Extern(_) => {}
        }
    }

    fn ty_names(&mut self, t: &Ty) {
        rokc_hir::walk::walk_ty(self, t);
    }

    fn scoped(&mut self, f: impl FnOnce(&mut Self)) {
        self.push_scope();
        f(self);
        self.pop_scope();
    }

    /// A function body; `fixed`: its signature comes from a trait.
    fn func(&mut self, f: &FnDef, fixed: bool) {
        self.exempt_next = fixed || f.body.is_none();
        walk_fn(self, f);
        if let Some(b) = &f.body {
            self.unreachable(&b.stmts, b.trailing.as_deref());
        }
    }

    /// `unreachable_code` in one statement list.
    fn unreachable(&mut self, stmts: &[Stmt], trailing: Option<&Expr>) {
        let Some(i) = stmts.iter().position(diverges) else {
            return;
        };
        let next = stmts
            .get(i + 1)
            .map(|s| s.span)
            .or_else(|| trailing.map(|e| e.span));
        if let Some(span) = next {
            self.findings.push(Finding {
                lint: "unreachable_code",
                span,
                msg: "unreachable statement".to_owned(),
                notes: Vec::new(),
                secondary: Some((
                    stmts[i].span,
                    "any code following this statement is unreachable".to_owned(),
                )),
            });
        }
    }

    fn block(&mut self, b: &Block) {
        self.unreachable(&b.stmts, b.trailing.as_deref());
    }

    fn unused_imports(&mut self, items: &[Item]) {
        // `use a::inner; use inner::f;` — a path's first segment may be an
        // earlier import (spec 5.5).
        for item in items {
            if let Item::Use(u) = item {
                if let Some(first) = u.tree.prefix.segments.first() {
                    self.file_names.insert(first.name.clone());
                }
            }
        }
        for item in items {
            match item {
                Item::Use(u) if u.vis == Visibility::Private => {
                    let mut leaves = Vec::new();
                    use_leaves(&u.tree, &mut Vec::new(), &mut leaves);
                    for (name, path, span) in leaves {
                        if !self.file_names.contains(&name) && !self.traits.contains(&name) {
                            let span = if span.is_dummy() { u.span } else { span };
                            self.hit("unused_imports", span, format!("unused import `{path}`"));
                        }
                    }
                }
                Item::Mod(m) => self.unused_imports(m.items.as_deref().unwrap_or(&[])),
                _ => {}
            }
        }
    }

    /// `dead_code`: non-`pub` free functions and inherent methods whose
    /// name no user file mentions.
    fn dead_code(&mut self, user: &[&SourceFile]) {
        fn walk(cx: &mut Cx<'_>, items: &[Item]) {
            for item in items {
                match item {
                    Item::Fn(f) => cx.dead_fn(f),
                    Item::Impl(im) if im.trait_path.is_none() => {
                        for ii in &im.items {
                            if let ImplItem::Method(m) = ii {
                                cx.dead_fn(m);
                            }
                        }
                    }
                    Item::Mod(m) => walk(cx, m.items.as_deref().unwrap_or(&[])),
                    _ => {}
                }
            }
        }
        for f in user {
            walk(self, &f.items);
        }
    }

    fn dead_fn(&mut self, f: &FnDef) {
        const ROOTS: &[&str] = &[
            "test",
            "bench",
            "export_name",
            "no_mangle",
            "lang",
            "intrinsic",
            "infix",
            "prefix",
            "postfix",
            "literal",
            "keyword",
        ];
        if f.vis != Visibility::Pub
            && f.name != "main"
            && !f.name.starts_with('_')
            && !has_attr(&f.attrs, ROOTS)
            && !self.all_names.contains(&f.name)
        {
            self.hit(
                "dead_code",
                f.span,
                format!("function `{}` is never used", f.name),
            );
        }
    }

    /// `redundant_cast` / `redundant_clone` from typed HIR. Generic
    /// instances (`__mono__`) are skipped: a cast to `T` is not
    /// redundant just because one instance has `T = i32`.
    fn hir(&mut self, hir: &rokc_hir::HirModule, user: &[&SourceFile]) {
        let files: HashSet<u32> = user.iter().map(|f| f.file_id).collect();
        let names: HashMap<_, &str> = hir
            .functions
            .iter()
            .map(|f| (f.id, f.name.as_str()))
            .collect();
        let mut hits: Vec<(&'static str, Span, String)> = Vec::new();
        for f in hir
            .functions
            .iter()
            .filter(|f| !f.name.contains("__mono__"))
        {
            let Some(body) = &f.body else { continue };
            each_block(body, &mut |e| {
                if !files.contains(&e.span.file) {
                    return;
                }
                match &e.kind {
                    HirExprKind::Cast { from_ty, to_ty, .. }
                        if from_ty == to_ty && self.casts.contains(&key(e.span)) =>
                    {
                        hits.push((
                            "redundant_cast",
                            e.span,
                            format!("casting to the same type `{}`", hir_ty(to_ty)),
                        ));
                    }
                    HirExprKind::Call { callee, args }
                        if args.len() == 1
                            && names.get(callee).is_some_and(|n| short_name(n) == "clone")
                            && matches!(args[0].ty, HirTy::Prim(_)) =>
                    {
                        hits.push((
                            "redundant_clone",
                            e.span,
                            format!(
                                "redundant `.clone()` of a `{}`: the value is copied anyway",
                                hir_ty(&args[0].ty)
                            ),
                        ));
                    }
                    _ => {}
                }
            });
        }
        for f in hir
            .functions
            .iter()
            .filter(|f| !f.name.contains("__mono__"))
        {
            unclosed(hir, f, &files, &mut hits);
        }
        for (lint, span, msg) in hits {
            self.hit(lint, span, msg);
        }
    }

    fn mark_used(&mut self, name: &str) {
        for s in self.scopes.iter_mut().rev() {
            if let Some(b) = s.bindings.iter_mut().rev().find(|b| b.name == name) {
                b.used = true;
                return;
            }
        }
    }

    /// `==` / `!=` / ordering comparisons with a NaN, `none`, or a `bool`
    /// literal.
    fn comparison(&mut self, e: &Expr, op: &str, lhs: &Expr, rhs: &Expr) {
        if !matches!(op, "==" | "!=" | "<" | "<=" | ">" | ">=") {
            return;
        }
        let nan = |x: &Expr| match &x.kind {
            ExprKind::Path(p) => p.segments.last().is_some_and(|s| s.name == "NAN"),
            ExprKind::Call { callee, args, .. } if args.is_empty() => matches!(
                &callee.kind,
                ExprKind::Path(p) if p.segments.len() == 2
                    && matches!(p.segments[0].name.as_str(), "f32" | "f64")
                    && p.segments[1].name == "nan"
            ),
            _ => false,
        };
        if nan(lhs) || nan(rhs) {
            self.hit(
                "nan_comparison",
                e.span,
                format!(
                    "comparison with NaN is always {}; use `.is_nan()`",
                    if op == "!=" { "true" } else { "false" }
                ),
            );
            return;
        }
        if !matches!(op, "==" | "!=") {
            return;
        }
        let lit = |x: &Expr| match &x.kind {
            ExprKind::Literal(l) => Some(l.clone()),
            _ => None,
        };
        match (lit(lhs), lit(rhs)) {
            (Some(Literal::None), _) | (_, Some(Literal::None)) => {
                let fix = if op == "==" {
                    "x is none"
                } else {
                    "!(x is none)"
                };
                self.hit(
                    "none_comparison",
                    e.span,
                    format!("comparing with `none` using `{op}`; write `{fix}`"),
                );
            }
            (Some(Literal::Bool(b)), _) | (_, Some(Literal::Bool(b))) => {
                let same = (op == "==") == b;
                self.hit(
                    "bool_comparison",
                    e.span,
                    format!(
                        "comparison with `{b}`; use the operand {}",
                        if same { "directly" } else { "negated (`!x`)" }
                    ),
                );
            }
            _ => {}
        }
    }

    /// Statement-position calls: `unused_must_use`, `ignored_error`.
    fn discarded(&mut self, e: &Expr) {
        let mut inner = e;
        if let ExprKind::Try { kind, operand } = &e.kind {
            if *kind == TryKind::Optional {
                self.hit(
                    "ignored_error",
                    e.span,
                    "`try?` result discarded: the error is silently ignored".to_owned(),
                );
            }
            inner = operand;
        }
        let name = match &inner.kind {
            ExprKind::Call { callee, .. } => match &callee.kind {
                ExprKind::Path(p) => p.segments.last().map(|s| s.name.as_str()),
                _ => None,
            },
            ExprKind::MethodCall { method, .. } => Some(method.as_str()),
            _ => None,
        };
        if let Some(msg) = name.and_then(|n| self.must_use.get(n).cloned()) {
            let mut f = Finding {
                lint: "unused_must_use",
                span: e.span,
                msg: format!(
                    "unused result of `{}`, which is `#[must_use]`",
                    name.unwrap_or("")
                ),
                notes: Vec::new(),
                secondary: None,
            };
            f.notes.extend(Some(msg).filter(|m| !m.is_empty()));
            self.findings.push(f);
        }
    }

    fn deprecated_use(&mut self, name: &str, span: Span) {
        if let Some(msg) = self.deprecated.get(name).cloned() {
            self.findings.push(Finding {
                lint: "deprecated",
                span,
                msg: format!("use of deprecated function `{name}`"),
                notes: Some(msg).filter(|m| !m.is_empty()).into_iter().collect(),
                secondary: None,
            });
        }
    }
}

/// `unclosed_resource`: a named local of a type with a `Drop` impl whose
/// every use is a call of its own non-closing methods. The GC never
/// closes it (stdlib 2.13), so the descriptor leaks. Any other use
/// (passed on, returned, stored, captured, `using`) counts as handled.
fn unclosed(
    hir: &rokc_hir::HirModule,
    f: &rokc_hir::HirFunction,
    files: &HashSet<u32>,
    hits: &mut Vec<(&'static str, Span, String)>,
) {
    const CLOSERS: &[&str] = &["close", "drop", "wait", "wait_with_output"];
    // The std descriptor holders; any other type whose `drop` the
    // program reaches counts too.
    const RESOURCES: &[&str] = &[
        "rok::std::fs::File",
        "rok::std::fs::Dir",
        "rok::std::fs::ReadDir",
        "rok::std::net::TcpStream",
        "rok::std::net::TcpListener",
        "rok::std::net::UdpSocket",
        "rok::std::process::Child",
    ];
    let Some(body) = &f.body else { return };
    let params: HashSet<_> = f.params.iter().map(|p| p.local).collect();
    // Methods are named `Struct<id>__<method>`.
    let resource = |t: &HirTy| match t {
        HirTy::Struct(id) => {
            let own = format!("Struct{}", id.0);
            let drop = format!("{own}__drop");
            hir.structs
                .iter()
                .find(|s| s.id == *id)
                .map(|s| s.name.as_str())
                .filter(|n| RESOURCES.contains(n) || hir.functions.iter().any(|g| g.name == drop))
                .map(|n| (n, own))
        }
        _ => None,
    };
    let names: HashMap<_, &str> = hir
        .functions
        .iter()
        .map(|g| (g.id, g.name.as_str()))
        .collect();
    for l in &f.locals {
        let Some(name) = l.name.as_deref().filter(|n| !n.starts_with(['#', '_'])) else {
            continue;
        };
        let Some((ty, own)) = resource(&l.ty).filter(|_| !params.contains(&l.id)) else {
            continue;
        };
        let is_l = |e: &rokc_hir::HirExpr| matches!(e.kind, HirExprKind::Local(x) if x == l.id);
        let (mut uses, mut kept, mut first) = (0, 0, None);
        each_block(body, &mut |e| {
            if is_l(e) {
                uses += 1;
                first = first.or(Some(e.span));
            }
            if let HirExprKind::Call { callee, args } = &e.kind {
                let own = names
                    .get(callee)
                    .and_then(|n| n.strip_prefix(own.as_str()))
                    .filter(|m| m.starts_with("__") || m.starts_with('.'))
                    .and_then(|m| m.rsplit("__").next());
                if args.first().is_some_and(is_l)
                    && own.is_some_and(|m| !CLOSERS.contains(&m) && !m.starts_with("into_"))
                {
                    kept += 1;
                }
            }
        });
        if let Some(span) = first.filter(|s| uses == kept && files.contains(&s.file)) {
            hits.push((
                "unclosed_resource",
                span,
                format!(
                    "`{name}` holds a `{}` that is never closed — bind it with `using` or \
                     call `close()`; the GC does not close it (stdlib 2.13)",
                    short_name(ty)
                ),
            ));
        }
    }
}

fn hir_ty(t: &HirTy) -> String {
    match t {
        HirTy::Prim(p) => p.name().to_owned(),
        other => format!("{other:?}"),
    }
}

/// Whether control never continues past `s`.
fn diverges(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Return(_)
        | StmtKind::Break { .. }
        | StmtKind::Continue { .. }
        | StmtKind::Throw(_) => true,
        StmtKind::Expr(e) => matches!(
            &e.kind,
            ExprKind::Call { callee, .. } if matches!(
                &callee.kind,
                ExprKind::Path(p) if p.segments.last().is_some_and(|s| matches!(
                    s.name.as_str(), "panic" | "exit" | "unreachable" | "todo"
                ))
            )
        ),
        _ => false,
    }
}

/// `(bound name, written path, span)` for each non-glob leaf of a `use`.
fn use_leaves(t: &UseTree, prefix: &mut Vec<String>, out: &mut Vec<(String, String, Span)>) {
    let n = prefix.len();
    prefix.extend(t.prefix.segments.iter().map(|s| s.name.clone()));
    match &t.kind {
        UseTreeKind::Simple(alias) => {
            let last = match prefix.last().map(String::as_str) {
                Some("self") => prefix.len().checked_sub(2).map(|i| prefix[i].clone()),
                l => l.map(str::to_owned),
            };
            if let Some(name) = alias.clone().or(last) {
                out.push((name, prefix.join("::"), t.prefix.span));
            }
        }
        UseTreeKind::Group(children) => {
            for c in children {
                use_leaves(c, prefix, out);
            }
        }
        UseTreeKind::Glob | UseTreeKind::GlobRecursive => {}
    }
    prefix.truncate(n);
}

/// Every pattern span in `p` (a `for` pattern's binders).
fn pat_spans(p: &Pattern, out: &mut HashSet<(u32, u32)>) {
    out.insert(key(p.span));
    match &p.kind {
        PatternKind::Binding { sub: Some(s), .. } => pat_spans(s, out),
        PatternKind::Tuple(ps)
        | PatternKind::Or(ps)
        | PatternKind::EnumVariant { args: ps, .. } => {
            ps.iter().for_each(|x| pat_spans(x, out));
        }
        PatternKind::Struct { fields, .. } => {
            for f in fields {
                if let Some(x) = &f.pat {
                    pat_spans(x, out);
                }
            }
        }
        _ => {}
    }
}

/// Path names a pattern mentions (enum / struct / constant paths).
fn pat_names(p: &Pattern, out: &mut HashSet<String>) {
    match &p.kind {
        PatternKind::Struct { path, fields, .. } => {
            out.extend(path.segments.iter().map(|s| s.name.clone()));
            for f in fields {
                if let Some(x) = &f.pat {
                    pat_names(x, out);
                }
            }
        }
        PatternKind::EnumVariant { path, args } => {
            out.extend(path.segments.iter().map(|s| s.name.clone()));
            args.iter().for_each(|x| pat_names(x, out));
        }
        PatternKind::Binding { name, sub } => {
            out.insert(name.clone());
            if let Some(s) = sub {
                pat_names(s, out);
            }
        }
        PatternKind::TypeCheck { ty, .. } => {
            if let TyKind::Path(p) = &ty.kind {
                out.extend(p.segments.iter().map(|s| s.name.clone()));
            }
        }
        PatternKind::Tuple(ps) | PatternKind::Or(ps) => ps.iter().for_each(|x| pat_names(x, out)),
        _ => {}
    }
}

impl AstVisitor for Cx<'_> {
    fn push_scope(&mut self) {
        self.scopes.push(Scope {
            bindings: Vec::new(),
            exempt: std::mem::take(&mut self.exempt_next),
        });
    }

    fn pop_scope(&mut self) {
        let Some(s) = self.scopes.pop() else { return };
        if s.exempt {
            return;
        }
        for b in s.bindings {
            if !b.used {
                self.findings.push(Finding {
                    lint: "unused_variables",
                    span: b.span,
                    msg: format!("unused variable `{}`", b.name),
                    notes: vec![format!(
                        "if this is intentional, prefix it with an underscore: `_{}`",
                        b.name
                    )],
                    secondary: None,
                });
            }
        }
    }

    fn bind_at(&mut self, name: &str, at: Span) {
        if name == "self" || name.starts_with('_') || name.starts_with(|c: char| c.is_uppercase()) {
            return;
        }
        let is_loop = self.loop_pats.contains(&key(at));
        if !is_loop {
            let shadows = self
                .scopes
                .iter()
                .any(|s| s.bindings.iter().any(|b| b.is_loop && b.name == name));
            if shadows {
                self.hit(
                    "shadowed_loop_var",
                    at,
                    format!("`{name}` shadows the loop variable `{name}`"),
                );
            }
        }
        self.name_lint("variable", name, at, 0);
        if let Some(s) = self.scopes.last_mut() {
            s.bindings.push(Binding {
                name: name.to_owned(),
                span: at,
                used: false,
                is_loop,
            });
        }
    }

    fn ty(&mut self, t: &Ty) {
        if let TyKind::Path(p) = &t.kind {
            self.file_names
                .extend(p.segments.iter().map(|s| s.name.clone()));
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Assign(target, value) => {
                if let ExprKind::Path(p) = &target.kind {
                    if let [seg] = p.segments.as_slice() {
                        self.assign_targets.insert(key(target.span));
                        if matches!(&value.kind, ExprKind::Path(q)
                            if q.segments.len() == 1 && q.segments[0].name == seg.name)
                        {
                            self.hit(
                                "self_assignment",
                                s.span,
                                format!("`{0}` is assigned to itself", seg.name),
                            );
                        }
                    }
                }
            }
            StmtKind::Expr(e) => self.discarded(e),
            StmtKind::LetPattern { pat, .. } => pat_names(pat, &mut self.file_names),
            StmtKind::LetStruct { path, .. } => {
                self.file_names
                    .extend(path.segments.iter().map(|s| s.name.clone()));
            }
            StmtKind::Item(i) => {
                // A nested item can't see the enclosing locals.
                let saved = std::mem::take(&mut self.scopes);
                self.item(i);
                self.scopes = saved;
            }
            _ => {}
        }
    }

    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Path(p) => {
                self.file_names
                    .extend(p.segments.iter().map(|s| s.name.clone()));
                if let [seg] = p.segments.as_slice() {
                    if !self.assign_targets.contains(&key(e.span)) {
                        let n = seg.name.clone();
                        self.mark_used(&n);
                    }
                }
            }
            ExprKind::Literal(Literal::FStr(text)) => {
                // Holes that were not desugared: any word may be a read.
                for w in text.split(|c: char| !(c.is_alphanumeric() || c == '_')) {
                    if !w.is_empty() {
                        self.mark_used(w);
                    }
                }
            }
            ExprKind::Call { callee, .. } => {
                if let ExprKind::Path(p) = &callee.kind {
                    if let Some(last) = p.segments.last() {
                        let n = last.name.clone();
                        self.deprecated_use(&n, e.span);
                    }
                }
            }
            ExprKind::MethodCall { method, args, .. } => {
                self.file_names.insert(method.clone());
                let m = method.clone();
                self.deprecated_use(&m, e.span);
                for a in args {
                    if let CallArg::Named { name, .. } = a {
                        self.file_names.insert(name.clone());
                    }
                }
            }
            ExprKind::QuestionDot(_, tails) => {
                for t in tails {
                    if let AccessTail::Method { method, .. } = t {
                        self.file_names.insert(method.clone());
                    }
                }
            }
            ExprKind::StructInit { path, .. } => {
                self.file_names
                    .extend(path.segments.iter().map(|s| s.name.clone()));
            }
            ExprKind::Cast(_, ty) => {
                let genuine = self
                    .texts
                    .get(usize::try_from(ty.span.file).unwrap_or(0).wrapping_sub(1))
                    .and_then(|(_, t)| t.get(..usize::try_from(ty.span.start).ok()?))
                    .is_some_and(|before| before.trim_end().ends_with("as"));
                if genuine {
                    self.casts.insert(key(e.span));
                }
            }
            ExprKind::OpInfix { op, lhs, rhs } => self.comparison(e, op, lhs, rhs),
            ExprKind::While { cond, body, .. } => {
                if matches!(cond.kind, ExprKind::Literal(Literal::Bool(true))) {
                    self.hit("while_true", e.span, "`while true` is `loop`".to_owned());
                }
                self.block(body);
            }
            ExprKind::For { pat, body, .. } => {
                pat_spans(pat, &mut self.loop_pats);
                pat_names(pat, &mut self.file_names);
                self.block(body);
            }
            ExprKind::Match { arms, .. } => {
                for a in arms {
                    pat_names(&a.pat, &mut self.file_names);
                }
            }
            ExprKind::Is(_, pat) | ExprKind::LetElse { pat, .. } => {
                pat_names(pat, &mut self.file_names);
                if let ExprKind::LetElse { else_body, .. } = &e.kind {
                    self.block(else_body);
                }
            }
            ExprKind::Catch {
                catches, finally, ..
            } => {
                for c in catches {
                    pat_names(&c.pat, &mut self.file_names);
                    self.block(&c.body);
                }
                if let Some(f) = finally {
                    self.block(f);
                }
            }
            ExprKind::Block(b)
            | ExprKind::Unsafe(b)
            | ExprKind::Loop { body: b, .. }
            | ExprKind::AsyncBlock(b)
            | ExprKind::YieldBlock(b)
            | ExprKind::AsyncYieldBlock(b) => self.block(b),
            ExprKind::If { then_branch, .. } => self.block(then_branch),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_and_levels() {
        assert!(is_snake("σ²") && is_snake("a_b1") && !is_snake("aB"));
        assert!(is_camel("Foo") && is_camel("HTTP") && !is_camel("foo") && !is_camel("Foo_Bar"));
        assert!(is_upper("MAX_N") && !is_upper("Max"));
        assert_eq!(to_snake("myVarName"), "my_var_name");
        assert_eq!(to_camel("my_type"), "MyType");
        assert_eq!(expand("unused").unwrap().len(), 5);
        assert_eq!(expand("all").unwrap().len(), LINTS.len());
        assert!(expand("nope").is_none());
        assert_eq!(Level::parse("deny"), Some(Level::Deny));
    }
}

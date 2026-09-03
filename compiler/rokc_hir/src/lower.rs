//! AST → HIR lowering.

use std::collections::HashMap;

use rokc_ast::{
    Block, CallArg, EnumDef as AstEnumDef, EnumVariantKind as AstEnumVariantKind, Expr, ExprKind,
    FnDef, ImplItem as AstImplItem, Item, Literal as AstLit,
    MatchArm as AstMatchArm, Param, Path as AstPath, Pattern as AstPattern,
    PatternKind as AstPatternKind, Program, Stmt, StmtKind, StructDef as AstStructDef,
    StructKind as AstStructKind, Ty, TyKind as AstTyKind,
};
use rokc_core::Visibility;
use rokc_ir_common::{ConstVal, FunctionId, LocalId, PrimOp, PrimTy};
use rokc_parser::{Fixity, PrecTable};

use crate::ty::resolve_ty;
use crate::{
    EnumId, HirBlock, HirEnumDef, HirEnumVariant, HirExpr, HirExprKind, HirField, HirFunction,
    HirLocal, HirMatchArm, HirModule, HirParam, HirPattern, HirStaticDef, HirStmt, HirStructDef,
    HirTy, HirUnionKind, StructId, UnionStorage,
};

/// Strip the leaf segment from a `module::path::name` string and
/// return the module path joined back with `::`. Returns an empty
/// string for free functions in the package root.
fn module_of(name: &str) -> String {
    match name.rsplit_once("::") {
        Some((mod_path, _)) => mod_path.to_owned(),
        None => String::new(),
    }
}

/// Best-effort const-folding of a static initializer. Accepts integer
/// and bool literals (with optional unary minus) plus string literals.
/// Returns `None` for non-literal initializers — caller falls back to
/// `ConstVal::Unit` and the codegen emits a zero-init global.
fn literal_to_const_val(expr: &Expr, ty: &HirTy) -> Option<ConstVal> {
    use rokc_ast::Literal as L;
    let lit = match &expr.kind {
        ExprKind::Literal(l) => l,
        ExprKind::OpPrefix { op, operand } if op == "-" => {
            // Negate a leading unary minus (`static N: i32 = -1;`).
            if let ExprKind::Literal(L::Int(text)) = &operand.kind {
                let stripped = strip_int_suffix(text.as_str());
                if let Ok(n) = stripped.parse::<i128>() {
                    let prim = match ty {
                        HirTy::Prim(p) => *p,
                        _ => return None,
                    };
                    return Some(ConstVal::Int { value: -n, ty: prim });
                }
            }
            return None;
        }
        _ => return None,
    };
    match lit {
        L::Int(text) => {
            let stripped = strip_int_suffix(text.as_str());
            let value: i128 = stripped.parse().ok()?;
            let prim = match ty {
                HirTy::Prim(p) => *p,
                _ => return None,
            };
            Some(ConstVal::Int { value, ty: prim })
        }
        L::Bool(b) => Some(ConstVal::Bool(*b)),
        L::Str(s) => Some(ConstVal::Str(s.clone())),
        L::RawStr(s) => Some(ConstVal::Str(s.clone())),
        L::None => Some(ConstVal::None),
        _ => None,
    }
}

fn strip_int_suffix(s: &str) -> &str {
    const SUFFIXES: &[&str] = &[
        "isize", "usize", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
    ];
    for sfx in SUFFIXES {
        if let Some(rest) = s.strip_suffix(sfx) {
            return rest;
        }
    }
    s
}

/// Outcome of glob resolution for one bare name. Single imports always
/// trump glob imports (per Rust 2018+ rules), so a Single hit returns
/// immediately. Glob hits are accumulated — two distinct globs landing
/// on the same suffix yield `Ambiguous`, which the caller surfaces as
/// a diagnostic.
enum LookupOutcome {
    None,
    Resolved(String),
    Ambiguous(Vec<String>),
}

/// A name table to resolve against: membership test plus (lazily) the
/// full key list, needed only by `use a::**` deep globs.
struct NameSet<'b> {
    exists: &'b dyn Fn(&str) -> bool,
    keys: &'b dyn Fn() -> Vec<String>,
}

fn lookup_in_use_entries_full(
    entries: &[crate::uses::UseEntry],
    segments: &[&str],
    suffix: &str,
    set: &NameSet<'_>,
) -> LookupOutcome {
    let mut glob_hits: Vec<String> = Vec::new();
    for entry in entries {
        match entry {
            crate::uses::UseEntry::Single { local, full } => {
                if segments.len() == 1 && segments[0] == local && (set.exists)(full) {
                    return LookupOutcome::Resolved(full.clone());
                }
                // `use foo::bar` lets `bar::baz` resolve as `foo::bar::baz`.
                if !segments.is_empty() && segments[0] == local {
                    let mut joined = full.clone();
                    for s in &segments[1..] {
                        joined.push_str("::");
                        joined.push_str(s);
                    }
                    if (set.exists)(&joined) {
                        return LookupOutcome::Resolved(joined);
                    }
                }
            }
            crate::uses::UseEntry::Glob { prefix } => {
                let candidate = if prefix.is_empty() {
                    suffix.to_owned()
                } else {
                    format!("{prefix}::{suffix}")
                };
                if (set.exists)(&candidate) && !glob_hits.contains(&candidate) {
                    glob_hits.push(candidate);
                }
            }
            crate::uses::UseEntry::GlobDeep { prefix } => {
                let direct = if prefix.is_empty() {
                    suffix.to_owned()
                } else {
                    format!("{prefix}::{suffix}")
                };
                if (set.exists)(&direct) && !glob_hits.contains(&direct) {
                    glob_hits.push(direct);
                    continue;
                }
                let prefix_with_sep = if prefix.is_empty() {
                    String::new()
                } else {
                    format!("{prefix}::")
                };
                let suffix_with_sep = format!("::{suffix}");
                for key in (set.keys)() {
                    if key.starts_with(&prefix_with_sep)
                        && key.ends_with(&suffix_with_sep)
                        && !glob_hits.contains(&key)
                    {
                        glob_hits.push(key);
                    }
                }
            }
        }
    }
    // Deterministic order regardless of HashMap iteration.
    glob_hits.sort();
    match glob_hits.len() {
        0 => LookupOutcome::None,
        1 => LookupOutcome::Resolved(glob_hits.remove(0)),
        _ => LookupOutcome::Ambiguous(glob_hits),
    }
}

/// Module-aware path resolution shared by the value (fn) and type
/// namespaces. Order: `pkg::` / `sup::` roots are made absolute; then the
/// current module and each ancestor, innermost first (root last); then
/// function-local `use`s (innermost scope first); then the module-level
/// `use` table. `Err(hits)` = ambiguous glob import (hits sorted).
fn resolve_name(
    segments: &[&str],
    module: &str,
    local_uses: &[Vec<crate::uses::UseEntry>],
    uses: &crate::uses::UseTable,
    set: &NameSet<'_>,
) -> Result<Option<String>, Vec<String>> {
    let resolved_segs: Vec<&str> = match segments.first().copied() {
        Some("pkg") => segments[1..].to_vec(),
        Some("sup") => {
            let mut parts: Vec<&str> = if module.is_empty() {
                Vec::new()
            } else {
                module.split("::").collect()
            };
            let mut i = 0;
            while i < segments.len() && segments[i] == "sup" {
                parts.pop();
                i += 1;
            }
            parts.extend(segments[i..].iter().copied());
            return Ok(Some(parts.join("::")).filter(|k| (set.exists)(k)));
        }
        _ => segments.to_vec(),
    };
    let segments = resolved_segs.as_slice();
    let suffix = segments.join("::");
    let mut cur: Vec<&str> = if module.is_empty() {
        Vec::new()
    } else {
        module.split("::").collect()
    };
    loop {
        let candidate = if cur.is_empty() {
            suffix.clone()
        } else {
            format!("{}::{suffix}", cur.join("::"))
        };
        if (set.exists)(&candidate) {
            return Ok(Some(candidate));
        }
        if cur.pop().is_none() {
            break;
        }
    }
    for scope in local_uses.iter().rev() {
        match lookup_in_use_entries_full(scope, segments, &suffix, set) {
            LookupOutcome::Resolved(s) => return Ok(Some(s)),
            LookupOutcome::Ambiguous(hits) => return Err(hits),
            LookupOutcome::None => {}
        }
    }
    if let Some(entries) = uses.get(module) {
        match lookup_in_use_entries_full(entries, segments, &suffix, set) {
            LookupOutcome::Resolved(s) => return Ok(Some(s)),
            LookupOutcome::Ambiguous(hits) => return Err(hits),
            LookupOutcome::None => {}
        }
    }
    Ok(None)
}

/// Can code in `cur_module` see an item declared in `def_module` with
/// visibility `vis`? (spec 5.6)
fn visible_from(cur_module: &str, def_module: &str, vis: Visibility) -> bool {
    match vis {
        // Single-package compilation today: everything reaching out
        // (Pub) or staying within the package (Pkg) is reachable.
        Visibility::Pub | Visibility::Pkg => true,
        Visibility::Sub => {
            def_module.is_empty()
                || cur_module == def_module
                || cur_module.starts_with(&format!("{def_module}::"))
        }
        // Spec 5.6.2: no keyword = visible in the declaring module only.
        Visibility::Private => cur_module == def_module,
    }
}

fn module_display(m: &str) -> &str {
    if m.is_empty() { "<root>" } else { m }
}

/// Type-namespace index: every struct / union / enum / alias / trait
/// name (driver-qualified, e.g. `a::P`; generic bases unmangled) plus
/// `pub use` re-export aliases. All type paths — in signatures, fields,
/// struct literals, patterns, enum paths — resolve through `canon`.
struct TypeNames<'a> {
    names: std::collections::HashSet<String>,
    traits: std::collections::HashSet<String>,
    /// `pub use` alias key → full path it re-exports.
    reexports: HashMap<String, String>,
    visibility: HashMap<String, Visibility>,
    uses: &'a crate::uses::UseTable,
    diags: std::cell::RefCell<Vec<rokc_diagnostic::RokDiagnostic>>,
}

impl TypeNames<'_> {
    fn canon(
        &self,
        segments: &[&str],
        module: &str,
        local_uses: &[Vec<crate::uses::UseEntry>],
    ) -> Option<String> {
        let exists = |k: &str| self.names.contains(k) || self.reexports.contains_key(k);
        let keys = || {
            let mut v: Vec<String> = self.names.iter().cloned().collect();
            v.extend(self.reexports.keys().cloned());
            v
        };
        let set = NameSet { exists: &exists, keys: &keys };
        let mut full = match resolve_name(segments, module, local_uses, self.uses, &set) {
            Ok(r) => r?,
            Err(hits) => {
                self.error(format!(
                    "type name `{}` is ambiguous in module `{}` — multiple glob imports \
                     resolve it: {}",
                    segments.join("::"),
                    module_display(module),
                    hits.join(", ")
                ));
                hits.into_iter().next()?
            }
        };
        for _ in 0..8 {
            match self.reexports.get(&full) {
                Some(t) => full = t.clone(),
                None => break,
            }
        }
        if let Some(&vis) = self.visibility.get(&full) {
            let def_module = module_of(&full);
            if !visible_from(module, &def_module, vis) {
                self.error(format!(
                    "type `{full}` is private to module `{}` and cannot be used from \
                     `{}` (spec 5.6 — add `pub` to expose it)",
                    module_display(&def_module),
                    module_display(module)
                ));
            }
        }
        Some(full)
    }

    /// Key under which `impl Trait for T` is recorded: a user trait's
    /// qualified name, else (bootstrap traits such as `core::ops::Add`)
    /// the last path segment.
    fn trait_key(&self, segments: &[&str], module: &str) -> String {
        self.canon(segments, module, &[])
            .filter(|full| self.traits.contains(full))
            .unwrap_or_else(|| segments.last().copied().unwrap_or_default().to_owned())
    }

    fn error(&self, msg: String) {
        self.diags.borrow_mut().push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            msg,
        ));
    }
}

/// Where a type is being resolved: the name index plus the module the
/// referencing item lives in.
#[derive(Clone, Copy)]
struct Scope<'b> {
    names: &'b TypeNames<'b>,
    module: &'b str,
}

/// Module path of an item after the driver flattened the module tree
/// (`a::b::name` → `a::b`). Impl blocks carry it on their methods.
fn item_module(item: &Item) -> String {
    match item {
        Item::Fn(f) => module_of(&f.name),
        Item::Struct(s) => module_of(&s.name),
        Item::Enum(e) => module_of(&e.name),
        Item::Union(u) => module_of(&u.name),
        Item::Const(c) => module_of(&c.name),
        Item::Static(s) => module_of(&s.name),
        Item::TypeAlias(a) => module_of(&a.name),
        Item::Trait(t) => module_of(&t.name),
        Item::Impl(i) => impl_module(i),
        _ => String::new(),
    }
}

fn impl_module(i: &rokc_ast::ImplDef) -> String {
    i.items
        .iter()
        .find_map(|it| match it {
            AstImplItem::Method(m) => Some(module_of(&m.name)),
            _ => None,
        })
        .unwrap_or_default()
}

/// Leaf of a driver-qualified name (`a::b::f` → `f`).
fn leaf_name(name: &str) -> &str {
    name.rsplit_once("::").map_or(name, |(_, l)| l)
}

// AST → HIR. Three passes: register struct names, then function
// signatures, then lower function bodies.
#[must_use]
pub fn lower(program: &Program, prec: &PrecTable) -> HirModule {
    let empty_uses: crate::uses::UseTable = HashMap::new();
    let empty_reexports: Vec<crate::uses::ReExport> = Vec::new();
    lower_full(program, prec, &empty_uses, &empty_reexports)
}

#[must_use]
pub fn lower_with_uses(
    program: &Program,
    prec: &PrecTable,
    uses: &crate::uses::UseTable,
) -> HirModule {
    let empty_reexports: Vec<crate::uses::ReExport> = Vec::new();
    lower_full(program, prec, uses, &empty_reexports)
}

#[must_use]
pub fn lower_full(
    program: &Program,
    prec: &PrecTable,
    uses: &crate::uses::UseTable,
    reexports: &[crate::uses::ReExport],
) -> HirModule {
    // Diagnostics emitted during pre-body passes (impl-target validation
    // etc.) — folded into module.diagnostics once the module exists.
    let mut pre_diags: Vec<rokc_diagnostic::RokDiagnostic> = Vec::new();
    let err = |pre: &mut Vec<rokc_diagnostic::RokDiagnostic>, msg: String| {
        pre.push(rokc_diagnostic::RokDiagnostic::error(rokc_diagnostic::ErrorKind::Type, msg));
    };
    // Spec 6.2: `#[derive(...)]` expansion isn't implemented in stage-1.
    // Pass over every item and emit an explicit refusal so users don't
    // get a silent miscompile (`a == b` returning `false` when they
    // expected the auto-derived equality, etc.).
    for item in &program.items {
        let attrs: &[rokc_ast::Attribute] = match item {
            Item::Struct(s) => &s.attrs,
            Item::Enum(e) => &e.attrs,
            Item::Union(u) => &u.attrs,
            _ => continue,
        };
        for a in attrs {
            if a.path.as_slice() == ["derive"] {
                err(
                    &mut pre_diags,
                    "`#[derive(...)]` expansion is not yet implemented; \
                     write the trait impl by hand for now (spec 6.2)"
                        .to_owned(),
                );
            }
        }
    }

    // Pass 0: the type namespace. Every type-like item name (already
    // module-qualified by the driver) goes into one index; a second
    // definition of the same name is an error (and is skipped below so
    // ids stay consistent).
    let mut type_set: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut traits: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut type_vis: HashMap<String, Visibility> = HashMap::new();
    for item in &program.items {
        let (name, vis) = match item {
            Item::Struct(s) => (&s.name, s.vis),
            Item::Enum(e) => (&e.name, e.vis),
            Item::Union(u) => (&u.name, u.vis),
            Item::TypeAlias(a) => (&a.name, a.vis),
            Item::Trait(t) => {
                traits.insert(t.name.clone());
                (&t.name, t.vis)
            }
            _ => continue,
        };
        if type_set.insert(name.clone()) {
            type_vis.insert(name.clone(), vis);
        } else {
            err(&mut pre_diags, format!("type `{name}` is defined more than once"));
        }
    }
    let mut type_reexports: HashMap<String, String> = HashMap::new();
    for _ in 0..3 {
        for re in reexports {
            if type_set.contains(&re.full_path) || type_reexports.contains_key(&re.full_path) {
                type_reexports.insert(reexport_key(re), re.full_path.clone());
            }
        }
    }
    let names = TypeNames {
        names: type_set,
        traits,
        reexports: type_reexports,
        visibility: type_vis,
        uses,
        diags: std::cell::RefCell::new(Vec::new()),
    };

    // Pass 1a: enums. Generic enums get stashed for lazy instantiation.
    let mut enum_table: HashMap<String, EnumId> = HashMap::new();
    let mut enum_decls: Vec<&AstEnumDef> = Vec::new();
    let mut generic_enums: HashMap<String, &AstEnumDef> = HashMap::new();
    for item in &program.items {
        if let Item::Enum(e) = item {
            if enum_table.contains_key(&e.name) || generic_enums.contains_key(&e.name) {
                continue;
            }
            if !e.generics.params.is_empty() {
                generic_enums.insert(e.name.clone(), e);
                continue;
            }
            let id = EnumId(u32::try_from(enum_decls.len()).expect("EnumId overflow"));
            enum_table.insert(e.name.clone(), id);
            enum_decls.push(e);
        }
    }
    // Pass 1b: structs and unions (one id space; unions after structs).
    // Generic structs are stashed aside and instantiated as type uses
    // surface them.
    let mut struct_table: HashMap<String, StructId> = HashMap::new();
    let mut generic_structs: HashMap<String, &AstStructDef> = HashMap::new();
    let mut struct_decls: Vec<&AstStructDef> = Vec::new();
    for item in &program.items {
        if let Item::Struct(s) = item {
            if struct_table.contains_key(&s.name) || generic_structs.contains_key(&s.name) {
                continue;
            }
            if !s.generics.params.is_empty() {
                generic_structs.insert(s.name.clone(), s);
                continue;
            }
            let id = StructId(u32::try_from(struct_decls.len()).expect("StructId overflow"));
            struct_table.insert(s.name.clone(), id);
            struct_decls.push(s);
        }
    }
    // Spec 2.x / i-want 322-340: `union { ... }` declarations live in
    // the same name space as structs. Register each one in
    // `struct_table` so paths resolve uniformly, and tag the resulting
    // `HirStructDef` with a `union_kind` so init/read sites know to use
    // the bitcast/cast access path instead of the regular field-by-index.
    let mut union_decls: Vec<&rokc_ast::UnionDef> = Vec::new();
    for item in &program.items {
        if let Item::Union(u) = item {
            if struct_table.contains_key(&u.name) || generic_structs.contains_key(&u.name) {
                continue;
            }
            let id = StructId(
                u32::try_from(struct_decls.len() + union_decls.len()).expect("StructId overflow"),
            );
            struct_table.insert(u.name.clone(), id);
            union_decls.push(u);
        }
    }

    let mut enum_defs: Vec<HirEnumDef> = Vec::with_capacity(enum_decls.len());
    for (i, e) in enum_decls.iter().enumerate() {
        let id = EnumId(u32::try_from(i).expect("EnumId overflow"));
        let module = module_of(&e.name);
        let sc = Scope { names: &names, module: &module };
        enum_defs.push(lower_enum_def(e, id, &struct_table, &enum_table, sc, &mut pre_diags));
    }
    let mut struct_defs: Vec<HirStructDef> =
        Vec::with_capacity(struct_decls.len() + union_decls.len());
    for (i, s) in struct_decls.iter().enumerate() {
        let id = StructId(u32::try_from(i).expect("StructId overflow"));
        let module = module_of(&s.name);
        let sc = Scope { names: &names, module: &module };
        struct_defs.push(lower_struct_def(s, id, &struct_table, &enum_table, sc));
    }
    for (i, u) in union_decls.iter().enumerate() {
        let id = StructId(
            u32::try_from(struct_decls.len() + i).expect("StructId overflow"),
        );
        let module = module_of(&u.name);
        let sc = Scope { names: &names, module: &module };
        struct_defs.push(lower_union_def(u, id, &struct_table, &enum_table, sc, &mut pre_diags));
    }
    // Pass 1b.1: walk the program collecting every generic-struct
    // instantiation (`Path("Pair", [T...])`) and materialize a fresh
    // `HirStructDef` for each unique substitution.
    instantiate_generic_structs(
        program,
        &generic_structs,
        &mut struct_table,
        &mut struct_defs,
        &enum_table,
        &names,
    );
    // Pass 1b.2: same idea for generic enums.
    instantiate_generic_enums(
        program,
        &generic_enums,
        &mut struct_table,
        &mut enum_table,
        &mut enum_defs,
        &names,
    );

    // Pass 1c: collect module-level `const` items. Their value
    // expressions are stored as AST and inlined at each use site.
    // `static` items follow a different path — they get stable global
    // storage (`HirStaticDef`) and reads/writes go through addressof
    // + load/store at codegen time.
    let mut consts: HashMap<String, (Ty, Expr)> = HashMap::new();
    for item in &program.items {
        if let Item::Const(c) = item {
            if consts.insert(c.name.clone(), (c.ty.clone(), c.value.clone())).is_some() {
                err(&mut pre_diags, format!("const `{}` is defined more than once", c.name));
            }
        }
    }
    let mut static_defs: Vec<HirStaticDef> = Vec::new();
    let mut static_tys: HashMap<String, HirTy> = HashMap::new();
    for item in &program.items {
        if let Item::Static(s) = item {
            if static_tys.contains_key(&s.name) {
                err(&mut pre_diags, format!("static `{}` is defined more than once", s.name));
                continue;
            }
            let module = module_of(&s.name);
            let sc = Scope { names: &names, module: &module };
            let ty = resolve_ty_with_structs(&s.ty, &struct_table, &enum_table, sc);
            // Stage-1: the initializer must const-fold to a literal. A
            // non-literal used to zero-initialize the global silently.
            let init = match s.value.as_ref() {
                Some(v) => literal_to_const_val(v, &ty).unwrap_or_else(|| {
                    err(
                        &mut pre_diags,
                        format!(
                            "static `{}` initializer must be a literal constant \
                             (stage-1 limitation)",
                            s.name
                        ),
                    );
                    ConstVal::Unit
                }),
                None => ConstVal::Unit,
            };
            static_tys.insert(s.name.clone(), ty.clone());
            static_defs.push(HirStaticDef {
                name: s.name.clone(),
                ty,
                init,
                is_mut: s.is_mut,
                span: s.span,
            });
        }
    }
    // Pass 1d: collect type aliases. Names resolve to the aliased type
    // wherever a `Path` appears in a type position. We do a post-pass
    // expansion so the alias table can refer to other aliases.
    let mut type_aliases: HashMap<String, HirTy> = HashMap::new();
    for item in &program.items {
        if let Item::TypeAlias(a) = item {
            let module = module_of(&a.name);
            let sc = Scope { names: &names, module: &module };
            let resolved = resolve_ty_with_structs(&a.ty, &struct_table, &enum_table, sc);
            type_aliases.entry(a.name.clone()).or_insert(resolved);
        }
    }
    // Substitute alias references inside aliases up to a small fixed
    // depth — direct cycles flatten harmlessly.
    for _ in 0..4 {
        let snapshot = type_aliases.clone();
        for v in type_aliases.values_mut() {
            substitute_aliases(v, &snapshot);
        }
    }
    // Spec 2.x: an alias that still mentions an alias after expansion is
    // cyclic (`type A = B; type B = A;`) and has no meaning.
    {
        let mut cyclic: Vec<&String> = type_aliases
            .iter()
            .filter(|(_, v)| ty_mentions_any(v, &type_aliases))
            .map(|(k, _)| k)
            .collect();
        cyclic.sort();
        for k in cyclic {
            err(&mut pre_diags, format!("type alias `{k}` is cyclic"));
        }
    }
    // Substitute aliases inside struct field types so the rest of the
    // pipeline never sees `Path(["Maybe"])`.
    for s in &mut struct_defs {
        for f in &mut s.fields {
            substitute_aliases(&mut f.ty, &type_aliases);
        }
    }
    for e in &mut enum_defs {
        for v in &mut e.variants {
            if let Some(t) = v.payload_ty.as_mut() {
                substitute_aliases(t, &type_aliases);
            }
        }
    }

    // A struct that contains itself by value (directly or through
    // tuples / arrays / sums / other structs) has no finite size.
    for (i, sd) in struct_defs.iter().enumerate() {
        let me = StructId(u32::try_from(i).expect("StructId overflow"));
        let mut stack: Vec<HirTy> = sd.fields.iter().map(|f| f.ty.clone()).collect();
        let mut seen: std::collections::HashSet<StructId> = std::collections::HashSet::new();
        while let Some(t) = stack.pop() {
            match t {
                HirTy::Struct(id) if id == me => {
                    err(
                        &mut pre_diags,
                        format!(
                            "recursive type `{}` has infinite size (a struct can't contain \
                             itself by value)",
                            sd.name
                        ),
                    );
                    break;
                }
                HirTy::Struct(id) => {
                    if seen.insert(id) {
                        if let Some(d) = struct_defs.get(id.0 as usize) {
                            stack.extend(d.fields.iter().map(|f| f.ty.clone()));
                        }
                    }
                }
                HirTy::Tuple(ps) | HirTy::Sum(ps) => stack.extend(ps),
                HirTy::Array(e, _) => stack.push(*e),
                _ => {}
            }
        }
    }

    // Pass 2: collect every function-like declaration. Free functions
    // first, then `impl` methods (each method becomes a synthetic free
    // function `Type::method` with `self` as its first parameter).
    // Generic functions don't get a single concrete signature — they
    // monomorphize per-call. We stash the AST aside instead of putting
    // them in `decls` / `fn_table`.
    let mut fn_table: HashMap<String, FnSig> = HashMap::new();
    let mut method_table: HashMap<(MethodTarget, String), FunctionId> = HashMap::new();
    let mut method_info: HashMap<FunctionId, MethodInfo> = HashMap::new();
    // Records `(Type, TraitName)` for each `impl Trait for Type` block
    // — feeds the generic-bound check at monomorphization time.
    let mut impl_traits: std::collections::HashSet<(MethodTarget, String)> =
        std::collections::HashSet::new();
    let mut decls: Vec<MethodOrFn<'_>> = Vec::new();
    let mut generic_fns: HashMap<String, &FnDef> = HashMap::new();
    let sig_of = |fn_def: &FnDef, id: FunctionId, self_ty: Option<&HirTy>, sc: Scope<'_>| {
        let resolve = |t: &Ty| {
            let mut r = resolve_ty_with_structs(t, &struct_table, &enum_table, sc);
            if let Some(st) = self_ty {
                substitute_aliases(&mut r, &HashMap::from([("Self".to_owned(), st.clone())]));
            }
            r
        };
        FnSig {
            id,
            ret_ty: fn_def.ret_ty.as_ref().map_or(HirTy::Unit, resolve),
            param_defaults: fn_def.params.iter().map(|p| p.default.clone()).collect(),
            param_tys: fn_def
                .params
                .iter()
                .map(|p| match (self_ty, p.name.as_str(), &p.ty) {
                    (Some(st), "self", _) => st.clone(),
                    (_, _, Some(t)) => resolve(t),
                    (_, _, None) => HirTy::Any,
                })
                .collect(),
            param_names: fn_def.params.iter().map(|p| p.name.clone()).collect(),
        }
    };
    for item in &program.items {
        match item {
            Item::Fn(fn_def) => {
                if fn_table.contains_key(&fn_def.name) || generic_fns.contains_key(&fn_def.name) {
                    err(
                        &mut pre_diags,
                        format!("function `{}` is defined more than once", fn_def.name),
                    );
                    continue;
                }
                if !fn_def.generics.params.is_empty() {
                    generic_fns.insert(fn_def.name.clone(), fn_def);
                    continue;
                }
                // Spec 4.1 / 변경점 833: `xs: ...T` variadic. Stage-1
                // call-site lowering doesn't yet wrap trailing args into
                // a Slice<T>, so any call would fail with arity mismatch
                // at codegen — emit an explicit refusal up front.
                if fn_def.params.iter().any(|p| p.variadic) {
                    err(
                        &mut pre_diags,
                        format!(
                            "function `{}` has a `...T` variadic parameter; \
                             call-site slicing isn't implemented yet \
                             (spec 4.1 — stage-1 limitation)",
                            fn_def.name
                        ),
                    );
                }
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let module = module_of(&fn_def.name);
                let sc = Scope { names: &names, module: &module };
                fn_table.insert(fn_def.name.clone(), sig_of(fn_def, id, None, sc));
                decls.push(MethodOrFn::Fn(fn_def));
            }
            Item::Extern(blk) => {
                for ei in &blk.items {
                    let rokc_ast::ExternItem::Fn(fn_def) = ei else { continue };
                    // A repeated extern declaration names the same symbol;
                    // keep the first.
                    if fn_table.contains_key(&fn_def.name) {
                        continue;
                    }
                    let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                    let sc = Scope { names: &names, module: "" };
                    fn_table.insert(fn_def.name.clone(), sig_of(fn_def, id, None, sc));
                    decls.push(MethodOrFn::Fn(fn_def));
                }
            }
            _ => {}
        }
    }
    // Pre-collect every trait declaration so `impl Trait for T` blocks
    // can pick up default method bodies.
    let mut trait_defs: HashMap<String, &rokc_ast::TraitDef> = HashMap::new();
    for item in &program.items {
        if let Item::Trait(t) = item {
            trait_defs.entry(t.name.clone()).or_insert(t);
        }
    }

    for item in &program.items {
        let Item::Impl(impl_def) = item else { continue };
        let module = impl_module(impl_def);
        let sc = Scope { names: &names, module: &module };
        let target_ty = resolve_ty_with_structs(&impl_def.self_ty, &struct_table, &enum_table, sc);
        let target = method_target_for(&target_ty);
        // Resolve the trait (a user trait resolves to its qualified name;
        // a bootstrap trait like `core::ops::Add` keeps its last segment).
        let trait_name: Option<String> = impl_def.trait_path.as_ref().map(|tp| {
            let segs: Vec<&str> = tp.segments.iter().map(|s| s.name.as_str()).collect();
            names.trait_key(&segs, &module)
        });
        if let (Some(tn), Some(target_key)) = (&trait_name, target.clone()) {
            impl_traits.insert((target_key, tn.clone()));
        }
        let trait_def = trait_name.as_ref().and_then(|tn| trait_defs.get(tn).copied());
        let target_display = impl_def_display(&impl_def.self_ty);
        // Names of methods this impl block explicitly provides —
        // used below to avoid double-registering a default that's
        // overridden here.
        let mut explicit_methods: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        for ii in &impl_def.items {
            let m = match ii {
                AstImplItem::Method(m) => m,
                AstImplItem::Const(c) => {
                    err(
                        &mut pre_diags,
                        format!(
                            "associated const `{}` in impl blocks is not implemented yet \
                             (stage-1 limitation)",
                            c.name
                        ),
                    );
                    continue;
                }
                AstImplItem::AssocType { .. } => continue,
            };
            let leaf = leaf_name(&m.name).to_owned();
            // Spec 2.9.2: `ref self` means the receiver mutates the
            // caller's binding. Pointer-typed receivers aren't yet
            // wired through codegen, so the body would silently
            // mutate a copy — reject explicitly to block the silent
            // miscompile until ref semantics land.
            if let Some(first) = m.params.first() {
                if first.name == "self" && first.by_ref {
                    err(
                        &mut pre_diags,
                        format!(
                            "method `{leaf}` declares `ref self`, but ref-self \
                             semantics aren't implemented yet — mutations \
                             would silently target a copy (spec 2.9.2)"
                        ),
                    );
                }
            }
            if !explicit_methods.insert(leaf.clone()) {
                err(
                    &mut pre_diags,
                    format!("method `{leaf}` is defined more than once for `{target_display}`"),
                );
                continue;
            }
            if let Some(td) = trait_def {
                let in_trait = td.items.iter().any(
                    |ti| matches!(ti, rokc_ast::TraitItem::Method(tm) if tm.name == leaf),
                );
                if !in_trait {
                    err(
                        &mut pre_diags,
                        format!(
                            "method `{leaf}` is not a member of trait `{}`",
                            td.name
                        ),
                    );
                }
            }
            let key = format!("{}__{leaf}", ty_mangle(&target_ty));
            if fn_table.contains_key(&key) {
                err(
                    &mut pre_diags,
                    format!("method `{leaf}` is defined more than once for `{target_display}`"),
                );
                continue;
            }
            let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
            fn_table.insert(key, sig_of(m, id, Some(&target_ty), sc));
            if let Some(t) = target.clone() {
                method_table.insert((t, leaf.clone()), id);
            }
            // Trait-impl methods are as visible as the trait itself;
            // inherent methods carry their own visibility.
            let vis = if trait_name.is_some() { Visibility::Pub } else { m.vis };
            method_info.insert(
                id,
                MethodInfo { module: module.clone(), vis, trait_name: trait_name.clone() },
            );
            decls.push(MethodOrFn::Method {
                fn_def: m,
                self_ty: target_ty.clone(),
                module: module.clone(),
            });
        }

        // Pull in default-method bodies from the trait this impl
        // is for, when the impl doesn't override them. Each default
        // gets specialized for `Self = target_ty` by reusing the
        // method-lowering machinery. A required method (no body) that
        // the impl doesn't provide is an error.
        if let Some(trait_def) = trait_def {
            let trait_module = module_of(&trait_def.name);
            for ti in &trait_def.items {
                let rokc_ast::TraitItem::Method(tm) = ti else { continue };
                if explicit_methods.contains(&tm.name) {
                    continue;
                }
                if tm.body.is_none() {
                    err(
                        &mut pre_diags,
                        format!(
                            "impl of trait `{}` for `{target_display}` is missing method `{}`",
                            trait_def.name, tm.name
                        ),
                    );
                    continue;
                }
                let key = format!("{}__{}", ty_mangle(&target_ty), tm.name);
                if fn_table.contains_key(&key) {
                    err(
                        &mut pre_diags,
                        format!(
                            "method `{}` is defined more than once for `{target_display}`",
                            tm.name
                        ),
                    );
                    continue;
                }
                let id = FunctionId(u32::try_from(decls.len()).expect("FunctionId overflow"));
                let tsc = Scope { names: &names, module: &trait_module };
                fn_table.insert(key, sig_of(tm, id, Some(&target_ty), tsc));
                if let Some(t) = target.clone() {
                    method_table.insert((t, tm.name.clone()), id);
                }
                method_info.insert(
                    id,
                    MethodInfo {
                        module: trait_module.clone(),
                        vis: Visibility::Pub,
                        trait_name: trait_name.clone(),
                    },
                );
                decls.push(MethodOrFn::Method {
                    fn_def: tm,
                    self_ty: target_ty.clone(),
                    module: trait_module.clone(),
                });
            }
        }
    }

    // Install `pub use` re-exports as fn/static table aliases (types go
    // through `TypeNames`). A fixed-point loop handles re-exports that
    // name another re-export's short form.
    for _ in 0..3 {
        for re in reexports {
            let alias_key = reexport_key(re);
            if let Some(sig) = fn_table.get(&re.full_path).cloned() {
                fn_table.entry(alias_key.clone()).or_insert(sig);
            }
            if let Some(ty) = static_tys.get(&re.full_path).cloned() {
                static_tys.entry(alias_key.clone()).or_insert(ty);
            }
        }
    }

    // Substitute aliases in collected fn signatures before lowering
    // bodies so `wrap_into_sum` and other type-driven decisions see
    // concrete sum / struct / fn types instead of unresolved paths.
    if !type_aliases.is_empty() {
        for sig in fn_table.values_mut() {
            substitute_aliases(&mut sig.ret_ty, &type_aliases);
            for p in &mut sig.param_tys {
                substitute_aliases(p, &type_aliases);
            }
        }
    }

    // Name → Visibility for every value-namespace item (fns, consts,
    // statics) plus type items; consulted by path resolution.
    let mut item_visibility: HashMap<String, Visibility> = HashMap::new();
    for item in &program.items {
        match item {
            Item::Fn(f) => {
                item_visibility.entry(f.name.clone()).or_insert(f.vis);
            }
            Item::Const(c) => {
                item_visibility.entry(c.name.clone()).or_insert(c.vis);
            }
            Item::Static(s) => {
                item_visibility.entry(s.name.clone()).or_insert(s.vis);
            }
            _ => {}
        }
    }
    let field_vis = collect_field_visibility(program);

    // Pass 3: function bodies.
    let sink = ClosureSink {
        extras: std::cell::RefCell::new(Vec::new()),
        next_id: std::cell::Cell::new(u32::try_from(decls.len()).expect("FunctionId overflow")),
        mono_cache: std::cell::RefCell::new(HashMap::new()),
        mono_sigs: std::cell::RefCell::new(HashMap::new()),
        mono_depth: std::cell::Cell::new(0),
        extra_structs: std::cell::RefCell::new(Vec::new()),
        extra_struct_table: std::cell::RefCell::new(HashMap::new()),
        diagnostics: std::cell::RefCell::new(Vec::new()),
    };
    let env = Env {
        fn_table,
        method_table,
        method_info,
        structs: struct_defs,
        enums: enum_defs,
        struct_table,
        enum_table,
        consts,
        type_aliases,
        generic_fns,
        generic_structs,
        prec,
        sink,
        item_visibility,
        field_vis,
        uses,
        impl_traits,
        statics: static_tys,
        names,
    };
    let mut functions: Vec<HirFunction> = Vec::with_capacity(decls.len());
    for (i, decl) in decls.iter().enumerate() {
        let id = FunctionId(u32::try_from(i).expect("FunctionId overflow"));
        functions.push(match decl {
            MethodOrFn::Fn(fn_def) => lower_fn(&env, fn_def, id, None, module_of(&fn_def.name)),
            MethodOrFn::Method { fn_def, self_ty, module } => {
                lower_fn(&env, fn_def, id, Some(self_ty.clone()), module.clone())
            }
        });
    }
    let Env { structs, enums, sink, type_aliases, names, .. } = env;
    // Append every closure body / monomorphization lifted to a top-level
    // function during expression lowering, and every struct instantiated
    // lazily from a literal (`Box { v: 5 }`).
    functions.extend(sink.extras.into_inner());
    let mut structs = structs;
    structs.extend(sink.extra_structs.into_inner());
    let mut module = HirModule {
        functions,
        structs,
        enums,
        statics: static_defs,
        diagnostics: pre_diags,
    };
    // Final pass: rewrite any leftover `HirTy::Path([alias])` nodes in
    // function signatures and locals using the alias table.
    if !type_aliases.is_empty() {
        for f in &mut module.functions {
            substitute_aliases(&mut f.ret_ty, &type_aliases);
            for p in &mut f.params {
                substitute_aliases(&mut p.ty, &type_aliases);
            }
            for l in &mut f.locals {
                substitute_aliases(&mut l.ty, &type_aliases);
            }
        }
    }
    module.diagnostics.extend(names.diags.into_inner());
    module.diagnostics.extend(sink.diagnostics.into_inner());
    check_unresolved_types(&mut module);
    // The same root cause can be reached from several passes (e.g. a
    // type resolved once per instantiation sweep): report it once.
    let mut seen = std::collections::HashSet::new();
    module.diagnostics.retain(|d| seen.insert(d.message.clone()));
    module
}

fn reexport_key(re: &crate::uses::ReExport) -> String {
    if re.module_path.is_empty() {
        re.short_name.clone()
    } else {
        format!("{}::{}", re.module_path, re.short_name)
    }
}

/// Source-ish rendering of an AST type for diagnostics.
fn impl_def_display(ty: &Ty) -> String {
    match &ty.kind {
        AstTyKind::Path(p) => p.segments.iter().map(|s| s.name.as_str()).collect::<Vec<_>>().join("::"),
        _ => "<type>".to_owned(),
    }
}

/// Does `ty` still name any key of `aliases`? (alias-cycle detection)
fn ty_mentions_any(ty: &HirTy, aliases: &HashMap<String, HirTy>) -> bool {
    match ty {
        HirTy::Path(p) => p.len() == 1 && aliases.contains_key(&p[0]),
        HirTy::Sum(parts) | HirTy::Tuple(parts) => parts.iter().any(|p| ty_mentions_any(p, aliases)),
        HirTy::Array(e, _) => ty_mentions_any(e, aliases),
        HirTy::Fn(a, r) | HirTy::Closure { args: a, ret: r, .. } => {
            a.iter().any(|p| ty_mentions_any(p, aliases)) || ty_mentions_any(r, aliases)
        }
        _ => false,
    }
}

/// `struct name → field name → visibility` from the AST (driver-qualified
/// struct names; generic instantiations look up their base name).
fn collect_field_visibility(program: &Program) -> HashMap<String, HashMap<String, Visibility>> {
    let mut out: HashMap<String, HashMap<String, Visibility>> = HashMap::new();
    for item in &program.items {
        match item {
            Item::Struct(s) => {
                let AstStructKind::Named(fs) = &s.kind else { continue };
                out.entry(s.name.clone())
                    .or_insert_with(|| fs.iter().map(|f| (f.name.clone(), f.vis)).collect());
            }
            Item::Union(u) => {
                out.entry(u.name.clone())
                    .or_insert_with(|| u.fields.iter().map(|f| (f.name.clone(), f.vis)).collect());
            }
            _ => {}
        }
    }
    out
}

/// Safety net: no expression or binding may leave lowering with an
/// unresolved type unless an error was already reported. A leftover
/// `HirTy::Path` is an unknown type name; a leftover `Unknown` /
/// `UnresolvedPath` means some lowering path fell through silently —
/// refuse to hand that to MIR (it would be lowered as unit / `any`).
fn check_unresolved_types(module: &mut HirModule) {
    let mut unknown_types: Vec<String> = Vec::new();
    let mut note = |ty: &HirTy| collect_unknown_paths(ty, &mut unknown_types);
    for s in &module.structs {
        for f in &s.fields {
            note(&f.ty);
        }
    }
    for e in &module.enums {
        for v in &e.variants {
            if let Some(t) = &v.payload_ty {
                note(t);
            }
        }
    }
    for st in &module.statics {
        note(&st.ty);
    }
    for f in &module.functions {
        note(&f.ret_ty);
        for p in &f.params {
            note(&p.ty);
        }
        for l in &f.locals {
            note(&l.ty);
        }
    }
    unknown_types.sort();
    unknown_types.dedup();
    for t in unknown_types {
        module.diagnostics.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            format!("cannot find type `{t}` in this scope"),
        ));
    }
    if module.diagnostics.iter().any(rokc_diagnostic::RokDiagnostic::is_error) {
        return;
    }
    let mut bad: Option<String> = None;
    for f in &module.functions {
        if f.params.iter().any(|p| p.ty == HirTy::Unknown)
            || f.locals.iter().any(|l| l.ty == HirTy::Unknown)
            || f.body.as_ref().is_some_and(hir_block_has_unknown)
        {
            bad = Some(f.name.clone());
            break;
        }
    }
    if let Some(name) = bad {
        module.diagnostics.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "internal compiler error: an expression in `{name}` has no resolved type \
                 (lowering fell through without a diagnostic) — please report"
            ),
        ));
    }
}

fn collect_unknown_paths(ty: &HirTy, out: &mut Vec<String>) {
    match ty {
        HirTy::Path(p) if p.as_slice() != ["none"] => out.push(p.join("::")),
        HirTy::Sum(parts) | HirTy::Tuple(parts) => {
            for p in parts {
                collect_unknown_paths(p, out);
            }
        }
        HirTy::Array(e, _) => collect_unknown_paths(e, out),
        HirTy::Fn(a, r) | HirTy::Closure { args: a, ret: r, .. } => {
            for p in a {
                collect_unknown_paths(p, out);
            }
            collect_unknown_paths(r, out);
        }
        _ => {}
    }
}

fn hir_block_has_unknown(b: &HirBlock) -> bool {
    b.stmts.iter().any(|s| match s {
        HirStmt::Let { init: e, .. }
        | HirStmt::Assign { value: e, .. }
        | HirStmt::StaticAssign { value: e, .. }
        | HirStmt::Expr(e)
        | HirStmt::Throw(e)
        | HirStmt::Return(Some(e))
        | HirStmt::Break { value: Some(e), .. } => hir_expr_has_unknown(e),
        HirStmt::ArrayAssign { index, value, .. } => {
            hir_expr_has_unknown(index) || hir_expr_has_unknown(value)
        }
        HirStmt::Return(None) | HirStmt::Break { value: None, .. } | HirStmt::Continue { .. } => {
            false
        }
    }) || b.trailing.as_ref().is_some_and(hir_expr_has_unknown)
}

fn hir_expr_has_unknown(e: &HirExpr) -> bool {
    use HirExprKind as K;
    if e.ty == HirTy::Unknown {
        return true;
    }
    let any = |es: &[HirExpr]| es.iter().any(hir_expr_has_unknown);
    match &e.kind {
        K::UnresolvedPath(_) => true,
        K::Const(_) | K::Local(_) | K::StaticRef(_) | K::FnRef(_) => false,
        K::Block(b) => hir_block_has_unknown(b),
        K::PrimBinOp { lhs, rhs, .. } => hir_expr_has_unknown(lhs) || hir_expr_has_unknown(rhs),
        K::PrimUnaryOp { operand, .. } | K::Cast { operand, .. } => hir_expr_has_unknown(operand),
        K::Call { args, .. } => any(args),
        K::CallIndirect { callee, args, .. } => hir_expr_has_unknown(callee) || any(args),
        K::ClosureValue { env, .. } => hir_expr_has_unknown(env),
        K::CallClosure { closure, args, .. } => hir_expr_has_unknown(closure) || any(args),
        K::If { cond, then_block, else_branch } => {
            hir_expr_has_unknown(cond)
                || hir_block_has_unknown(then_block)
                || else_branch.as_deref().is_some_and(hir_expr_has_unknown)
        }
        K::While { cond, body, .. } => hir_expr_has_unknown(cond) || hir_block_has_unknown(body),
        K::Loop { body, .. } => hir_block_has_unknown(body),
        K::Match { scrutinee, arms } => {
            hir_expr_has_unknown(scrutinee)
                || arms.iter().any(|a| {
                    a.guard.as_ref().is_some_and(hir_expr_has_unknown)
                        || hir_expr_has_unknown(&a.body)
                })
        }
        K::StructInit { fields, .. } | K::Tuple { fields } => any(fields),
        K::FieldRead { target, .. } | K::TupleField { target, .. } | K::UnionRead { target, .. } => {
            hir_expr_has_unknown(target)
        }
        K::WithField { target, value, .. } => {
            hir_expr_has_unknown(target) || hir_expr_has_unknown(value)
        }
        K::EnumVariantInit { args, .. } => any(args),
        K::SumWrap { value, .. } => value.as_deref().is_some_and(hir_expr_has_unknown),
        K::ArrayInit { elements, .. } => any(elements),
        K::ArrayIndex { array, index, .. } => {
            hir_expr_has_unknown(array) || hir_expr_has_unknown(index)
        }
        K::UnionWrite { value, .. } => hir_expr_has_unknown(value),
    }
}

/// Per-method facts consulted at call sites: the module whose privacy
/// rules apply, the method's visibility, and the trait it implements
/// (operator dispatch requires a trait impl, spec 0.4 / 6.4).
struct MethodInfo {
    module: String,
    vis: Visibility,
    trait_name: Option<String>,
}

/// Module-wide, read-only lowering environment shared by every function
/// body (plus the interior-mutable `sink`).
struct Env<'a> {
    fn_table: HashMap<String, FnSig>,
    method_table: HashMap<(MethodTarget, String), FunctionId>,
    method_info: HashMap<FunctionId, MethodInfo>,
    structs: Vec<HirStructDef>,
    enums: Vec<HirEnumDef>,
    struct_table: HashMap<String, StructId>,
    enum_table: HashMap<String, EnumId>,
    /// Module-level `const NAME: T = expr;` items. A bare `Path(NAME)`
    /// resolves to the const's value expression inlined at the use site.
    consts: HashMap<String, (Ty, Expr)>,
    /// Module-level type aliases. Walked over every `HirTy` produced
    /// from AST resolution so downstream code never sees `Path([alias])`.
    type_aliases: HashMap<String, HirTy>,
    /// Generic function templates keyed by name. lower_call queries
    /// this when the callee path matches a generic function.
    generic_fns: HashMap<String, &'a FnDef>,
    /// Generic struct templates, for instantiation inferred from a
    /// struct literal (`Box { v: 5 }` → `Box<i32>`).
    generic_structs: HashMap<String, &'a AstStructDef>,
    prec: &'a PrecTable,
    sink: ClosureSink,
    /// Visibility of every value-namespace item, keyed by full name.
    item_visibility: HashMap<String, Visibility>,
    /// Struct name → field name → visibility.
    field_vis: HashMap<String, HashMap<String, Visibility>>,
    /// Per-module `use` table — feeds into bare-name and unresolved
    /// path lookups. Empty when no `use` declarations were collected.
    uses: &'a crate::uses::UseTable,
    /// Set of `(Type, TraitName)` pairs declared by `impl Trait for Type`
    /// blocks. Consulted at monomorphization time to enforce generic
    /// trait bounds.
    impl_traits: std::collections::HashSet<(MethodTarget, String)>,
    /// Module-level `static` items by name → declared type.
    statics: HashMap<String, HirTy>,
    names: TypeNames<'a>,
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum MethodTarget {
    Struct(StructId),
    Enum(EnumId),
    /// Mangled HirTy for impl targets that aren't a single struct or
    /// enum (Tuple/Array/Sum/Fn/Prim per spec 2.9.1 — type_expr is any
    /// type). Keyed by `ty_mangle` so two impls on the same shape land
    /// on the same target.
    Mangled(String),
}

/// Map a runtime `HirTy` to the `MethodTarget` used in `method_table`
/// keys. Mirrors `impl_target_key`'s strategy: direct mapping for
/// Struct/Enum, mangled fallback for everything else.
fn method_target_for(ty: &HirTy) -> Option<MethodTarget> {
    match ty {
        HirTy::Struct(id) => Some(MethodTarget::Struct(*id)),
        HirTy::Enum(id) => Some(MethodTarget::Enum(*id)),
        HirTy::Unknown => None,
        other => Some(MethodTarget::Mangled(ty_mangle(other))),
    }
}

enum MethodOrFn<'a> {
    Fn(&'a FnDef),
    /// `module` is where the body's names resolve: the impl's module
    /// for explicit methods, the trait's module for default bodies.
    Method { fn_def: &'a FnDef, self_ty: HirTy, module: String },
}

fn lower_enum_def(
    e: &AstEnumDef,
    id: EnumId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    sc: Scope<'_>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> HirEnumDef {
    let variants = e
        .variants
        .iter()
        .enumerate()
        .filter_map(|(i, v)| {
            let tag = u32::try_from(i).expect("variant index overflow");
            match &v.kind {
                AstEnumVariantKind::Unit => Some(HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: None,
                    named_fields: Vec::new(),
                    arity: 0,
                }),
                // Single-element tuple — store the payload type directly.
                AstEnumVariantKind::Tuple(tys) if tys.len() == 1 => Some(HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(resolve_ty_with_structs(&tys[0], structs, enums, sc)),
                    named_fields: Vec::new(),
                    arity: 1,
                }),
                // Multi-element tuple — pack into a tuple payload type.
                AstEnumVariantKind::Tuple(tys) => Some(HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(HirTy::Tuple(
                        tys.iter()
                            .map(|t| resolve_ty_with_structs(t, structs, enums, sc))
                            .collect(),
                    )),
                    named_fields: Vec::new(),
                    arity: tys.len(),
                }),
                // Named-form variant `Move { x: i32; y: i32; }` — pack
                // into a tuple payload by declaration order, recording
                // the field names so initialiser/pattern lowering can
                // map name → tuple index. Spec 2.4.
                AstEnumVariantKind::Named(fields) => Some(HirEnumVariant {
                    name: v.name.clone(),
                    tag,
                    payload_ty: Some(HirTy::Tuple(
                        fields
                            .iter()
                            .map(|f| resolve_ty_with_structs(&f.ty, structs, enums, sc))
                            .collect(),
                    )),
                    named_fields: fields.iter().map(|f| f.name.clone()).collect(),
                    arity: fields.len(),
                }),
                // Dropping the variant would shift every later tag.
                AstEnumVariantKind::Value(_) => {
                    pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "explicit discriminant on enum variant `{}::{}` is not \
                             implemented yet (stage-1 limitation)",
                            e.name, v.name
                        ),
                    ));
                    Some(HirEnumVariant {
                        name: v.name.clone(),
                        tag,
                        payload_ty: None,
                        named_fields: Vec::new(),
                        arity: 0,
                    })
                }
            }
        })
        .collect();
    HirEnumDef {
        id,
        def_id: None,
        name: e.name.clone(),
        variants,
        span: e.span,
    }
}

fn lower_struct_def(
    s: &AstStructDef,
    id: StructId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    sc: Scope<'_>,
) -> HirStructDef {
    let fields = match &s.kind {
        AstStructKind::Named(fs) => fs
            .iter()
            .map(|f| HirField {
                name: f.name.clone(),
                ty: resolve_ty_with_structs(&f.ty, structs, enums, sc),
                // Spec 2.x / i-want 942-950: keep the default expr so
                // a literal that omits this field can fill it lazily
                // at the use site.
                default: f.default.clone(),
            })
            .collect(),
        // Tuple struct `Foo(A, B)` — synthesize positional field names
        // ("0", "1", ...) so `n.0` tuple-style field access lands in
        // the same field-read path as named structs (spec 2.7.4).
        AstStructKind::Tuple(fs) => fs
            .iter()
            .enumerate()
            .map(|(i, f)| HirField {
                name: i.to_string(),
                ty: resolve_ty_with_structs(&f.ty, structs, enums, sc),
                default: None,
            })
            .collect(),
        AstStructKind::Unit => Vec::new(),
    };
    HirStructDef {
        id,
        def_id: None,
        name: s.name.clone(),
        fields,
        span: s.span,
        generic_args: Vec::new(),
        union_kind: None,
    }
}

/// Lower a `union { f1: T1; f2: T2; ... }` declaration into a single
/// synthetic `HirStructDef` with one field `__data` whose type is the
/// chosen storage. The field name → declared type table goes into
/// `union_kind.aliases`. See `union_storage_strategy` for the
/// fast-path (A) vs general-path (B) decision.
fn lower_union_def(
    u: &rokc_ast::UnionDef,
    id: StructId,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    sc: Scope<'_>,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> HirStructDef {
    let aliases: Vec<(String, HirTy)> = u
        .fields
        .iter()
        .map(|f| (f.name.clone(), resolve_ty_with_structs(&f.ty, structs, enums, sc)))
        .collect();
    let is_repr_c = u.attrs.iter().any(|a| {
        a.path.as_slice() == ["repr"]
            && matches!(&a.body, rokc_ast::AttrBody::Args(args)
                if args.iter().any(|arg| matches!(arg, rokc_ast::AttrArg::Word(w) if w == "C")))
    });
    let storage = union_storage_strategy(&aliases, is_repr_c, &u.name, u.span, pre_diags);
    let storage_ty = match &storage {
        UnionStorage::WidestPrim(p) => HirTy::Prim(*p),
        UnionStorage::ByteArray { size, .. } => {
            HirTy::Array(Box::new(HirTy::Prim(PrimTy::U8)), *size)
        }
    };
    HirStructDef {
        id,
        def_id: None,
        name: u.name.clone(),
        fields: vec![HirField {
            name: "__data".to_owned(),
            ty: storage_ty,
            default: None,
        }],
        span: u.span,
        generic_args: Vec::new(),
        union_kind: Some(HirUnionKind {
            storage,
            aliases,
            is_repr_c,
        }),
    }
}

/// Pick the union backing storage. All-prim unions without `#[repr(C)]`
/// take the fast path (single widest primitive — model A). Anything
/// else (struct/enum field, `#[repr(C)]`) falls through to the general
/// `[u8; size]` byte-array path (model B).
fn union_storage_strategy(
    aliases: &[(String, HirTy)],
    is_repr_c: bool,
    name: &str,
    span: rokc_diagnostic::Span,
    pre_diags: &mut Vec<rokc_diagnostic::RokDiagnostic>,
) -> UnionStorage {
    let _ = span;
    if aliases.is_empty() {
        pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Type,
            format!("union `{name}` declares no fields (spec 2.x)"),
        ));
        return UnionStorage::WidestPrim(PrimTy::U8);
    }
    let all_prim = aliases.iter().all(|(_, t)| matches!(t, HirTy::Prim(_)));
    if all_prim && !is_repr_c {
        // Pick the widest primitive. Tie-break: prefer unsigned > signed
        // > float so written bits round-trip cleanly through a wider read.
        let mut best: Option<PrimTy> = None;
        let mut best_score: (u32, u8) = (0, 0);
        for (_, t) in aliases {
            if let HirTy::Prim(p) = t {
                let width = p.bit_width(64);
                let kind_pref: u8 = match p {
                    PrimTy::U8
                    | PrimTy::U16
                    | PrimTy::U32
                    | PrimTy::U64
                    | PrimTy::Usize => 3,
                    PrimTy::I8
                    | PrimTy::I16
                    | PrimTy::I32
                    | PrimTy::I64
                    | PrimTy::Isize
                    | PrimTy::CChar
                    | PrimTy::Char => 2,
                    PrimTy::F32 | PrimTy::F64 => 1,
                    PrimTy::Bool | PrimTy::Str => 0,
                };
                let score = (width, kind_pref);
                if best.is_none() || score > best_score {
                    best = Some(*p);
                    best_score = score;
                }
            }
        }
        return UnionStorage::WidestPrim(best.unwrap_or(PrimTy::U8));
    }
    // Byte-array path. Compute size = max byte size, align = max byte
    // alignment over all declared fields.
    let mut size: u32 = 0;
    let mut align: u32 = 1;
    for (fname, t) in aliases {
        let (sz, al) = ty_size_align_bytes(t).unwrap_or_else(|| {
            pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "union `{name}` field `{fname}` has type whose size is \
                     not yet computable in stage-1 (struct fields with \
                     pointer/closure types — spec 2.x byte-array union)"
                ),
            ));
            (0, 1)
        });
        if sz > size {
            size = sz;
        }
        if al > align {
            align = al;
        }
    }
    if size == 0 {
        size = 1;
    }
    // Round size up to align (C ABI: padding to alignment boundary).
    let padded = ((size + align - 1) / align) * align;
    // Stage-1: byte-array storage path is reserved in HIR (model B) but
    // codegen for value-level bitcast between primitive ↔ `[u8; N]` is
    // not yet wired through (mlir-translate rejects
    // `unrealized_conversion_cast` for these). Emit an explicit message
    // up front so users see a clear stage-1 limitation rather than an
    // opaque MLIR error. Stage-2 will replace this with alloca + GEP +
    // pointer bitcast + store/load pattern.
    pre_diags.push(rokc_diagnostic::RokDiagnostic::error(
        rokc_diagnostic::ErrorKind::Type,
        format!(
            "union `{name}` falls into byte-array storage (non-primitive \
             field or `#[repr(C)]`) — stage-1 codegen for byte-storage \
             union is not yet implemented (spec 2.x byte-array union, \
             stage-2)"
        ),
    ));
    UnionStorage::ByteArray { size: padded, align }
}

/// Best-effort byte size + alignment for a `HirTy`. Returns `None` for
/// types whose size depends on layout choices we haven't pinned yet
/// (closures with environment, generic struct without monomorphization).
fn ty_size_align_bytes(ty: &HirTy) -> Option<(u32, u32)> {
    match ty {
        HirTy::Prim(p) => {
            let bits = p.bit_width(64);
            if bits == 0 {
                None
            } else {
                let bytes = bits / 8;
                Some((bytes, bytes))
            }
        }
        HirTy::Tuple(parts) | HirTy::Sum(parts) => {
            let mut total: u32 = 0;
            let mut align: u32 = 1;
            for p in parts {
                let (sz, al) = ty_size_align_bytes(p)?;
                if al > align {
                    align = al;
                }
                let pad = ((total + al - 1) / al) * al;
                total = pad + sz;
            }
            let padded = ((total + align - 1) / align) * align;
            Some((padded, align))
        }
        HirTy::Array(elem, n) => {
            let (sz, al) = ty_size_align_bytes(elem)?;
            Some((sz * n, al))
        }
        // Stage-1: struct/enum sizes need module access; report as
        // unknown so the caller falls back to the byte-array
        // diagnostic. Adding accurate sizing requires plumbing the
        // module reference here — separate milestone.
        HirTy::Struct(_) | HirTy::Enum(_) => None,
        HirTy::Path(_) | HirTy::Unknown | HirTy::Any | HirTy::Unit => None,
        HirTy::Fn(_, _) | HirTy::Closure { .. } => None,
    }
}

/// Match an AST parameter type against a concrete `HirTy` (the call
/// argument's inferred type) to discover bindings for generic type
/// parameters. Walks structurally — `[T; N]` against `[i32; 4]` binds
/// `T → i32`, etc.
fn unify_param_ty_with(
    param_ty: &rokc_ast::Ty,
    arg_ty: &HirTy,
    generic_names: &std::collections::HashSet<String>,
    subst: &mut HashMap<String, HirTy>,
    ctx: &LowerCtx<'_>,
) {
    let mut rec = |p: &rokc_ast::Ty, a: &HirTy| {
        unify_param_ty_with(p, a, generic_names, subst, ctx);
    };
    match (&param_ty.kind, arg_ty) {
        (rokc_ast::TyKind::Path(p), _)
            if p.segments.len() == 1 && generic_names.contains(&p.segments[0].name) =>
        {
            // First binding wins; a conflicting later argument surfaces
            // as an argument type mismatch at the call site.
            subst.entry(p.segments[0].name.clone()).or_insert_with(|| arg_ty.clone());
        }
        // Generic struct param `Pair<T>` against arg `Pair__i32`:
        // recover T by reading the struct's recorded generic args.
        (rokc_ast::TyKind::Path(p), HirTy::Struct(sid)) => {
            let Some(last) = p.segments.last() else { return };
            let def = ctx.struct_def(*sid);
            for (param_arg, concrete) in last.generics.iter().zip(def.generic_args.iter()) {
                rec(param_arg, concrete);
            }
        }
        (rokc_ast::TyKind::Array(elem, _), HirTy::Array(arg_elem, _)) => rec(elem, arg_elem),
        (rokc_ast::TyKind::Tuple(parts), HirTy::Tuple(arg_parts))
        | (rokc_ast::TyKind::Sum(parts), HirTy::Sum(arg_parts)) => {
            for (p, a) in parts.iter().zip(arg_parts.iter()) {
                rec(p, a);
            }
        }
        (
            rokc_ast::TyKind::Fn(args, ret),
            HirTy::Fn(arg_args, arg_ret) | HirTy::Closure { args: arg_args, ret: arg_ret, .. },
        ) => {
            for (p, a) in args.iter().zip(arg_args.iter()) {
                rec(p, a);
            }
            rec(ret, arg_ret);
        }
        // Nothing to bind: the argument type check reports mismatches.
        _ => {}
    }
}

/// Instantiation limits: deeper nesting means the generic recursion
/// never reaches a fixed point (`fn r<T>(x: T) { r((x, x)) }`).
const MONO_DEPTH_LIMIT: u32 = 64;
const MONO_TYPE_SIZE_LIMIT: usize = 256;

fn ty_size(ty: &HirTy) -> usize {
    1 + match ty {
        HirTy::Sum(p) | HirTy::Tuple(p) => p.iter().map(ty_size).sum(),
        HirTy::Array(e, _) => ty_size(e),
        HirTy::Fn(a, r) => a.iter().map(ty_size).sum::<usize>() + ty_size(r),
        HirTy::Closure { args, ret, env } => {
            args.iter().map(ty_size).sum::<usize>() + ty_size(ret) + ty_size(env)
        }
        _ => 0,
    }
}

/// Look up or generate a specialized version of a generic function.
/// Returns `(specialized_fn_id, return_type)` on success; `None` after
/// reporting why the call can't be instantiated. Type-parameter
/// substitution is inferred by zipping the call's lowered argument types
/// with the AST parameter type ascriptions.
fn monomorphize(
    ctx: &mut LowerCtx<'_>,
    fn_def: &FnDef,
    args: &[HirExpr],
    _span: rokc_diagnostic::Span,
) -> Option<(FunctionId, HirTy)> {
    let fn_module = module_of(&fn_def.name);
    // Infer concrete types for each generic param by unifying the AST
    // parameter type ascription against the call's arg type. Walks into
    // arrays, tuples, sums, function types, and closures. The first
    // binding wins; a conflicting later argument is reported by the
    // argument type check at the call site.
    let generic_names: std::collections::HashSet<String> = fn_def
        .generics
        .params
        .iter()
        .filter_map(|gp| match gp {
            rokc_ast::GenericParam::Type { name, .. } => Some(name.clone()),
            rokc_ast::GenericParam::Const { .. } => None,
        })
        .collect();
    let mut subst: HashMap<String, HirTy> = HashMap::new();
    for (param, arg) in fn_def.params.iter().zip(args.iter()) {
        let Some(t) = &param.ty else { continue };
        unify_param_ty_with(t, &arg.ty, &generic_names, &mut subst, ctx);
    }

    // Spec 2.10.5: if a generic param has a default and no concrete type
    // got inferred for it, apply the default. Order is one pass — defaults
    // can't depend on other defaults (would need iteration).
    for gp in &fn_def.generics.params {
        if let rokc_ast::GenericParam::Type { name, default: Some(d), .. } = gp {
            if !subst.contains_key(name) {
                let sc = Scope { names: &ctx.env.names, module: &fn_module };
                let resolved =
                    resolve_ty_with_structs(d, &ctx.env.struct_table, &ctx.env.enum_table, sc);
                subst.insert(name.clone(), resolved);
            }
        }
    }

    // Every generic param must be inferable.
    let mut subst_tys: Vec<HirTy> = Vec::new();
    for gp in &fn_def.generics.params {
        match gp {
            rokc_ast::GenericParam::Type { name, .. } => match subst.get(name) {
                Some(t) => subst_tys.push(t.clone()),
                None => {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "cannot infer type parameter `{name}` of `{}` from the call \
                             arguments",
                            fn_def.name
                        ),
                    );
                    return None;
                }
            },
            rokc_ast::GenericParam::Const { name, .. } => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "const generic parameter `{name}` of `{}` is not implemented yet \
                         (stage-1 limitation)",
                        fn_def.name
                    ),
                );
                return None;
            }
        }
    }
    if subst_tys.iter().any(|t| matches!(t, HirTy::Unknown)) {
        // An argument already failed to lower (reported).
        return None;
    }
    if subst_tys.iter().any(|t| ty_size(t) > MONO_TYPE_SIZE_LIMIT)
        || ctx.env.sink.mono_depth.get() >= MONO_DEPTH_LIMIT
    {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "instantiating generic function `{}` recursed past the limit \
                 (depth {MONO_DEPTH_LIMIT}) — the instantiation never reaches a \
                 fixed point",
                fn_def.name
            ),
        );
        return None;
    }

    // Check generic-bound satisfaction: for each `T: Bound` declared on
    // the fn, verify that the inferred concrete type for `T` carries an
    // `impl Bound for T` block.
    for gp in &fn_def.generics.params {
        let rokc_ast::GenericParam::Type { name, bounds, default: _ } = gp else {
            continue;
        };
        let Some(concrete) = subst.get(name) else { continue };
        let Some(target) = method_target_for(concrete) else { continue };
        for bound in bounds {
            let rokc_ast::TyKind::Path(p) = &bound.kind else { continue };
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            let bound_name = ctx.env.names.trait_key(&segs, &fn_module);
            if !ctx.env.impl_traits.contains(&(target.clone(), bound_name.clone())) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "type `{}` does not satisfy trait bound `{bound_name}` required \
                         by `{}`",
                        ctx.ty_name(concrete),
                        fn_def.name
                    ),
                );
            }
        }
    }

    let key = (
        fn_def.name.clone(),
        subst_tys.iter().map(ty_mangle).collect::<Vec<_>>(),
    );
    if let Some(&existing_id) = ctx.env.sink.mono_cache.borrow().get(&key) {
        let ret_ty = ctx
            .env
            .sink
            .mono_sigs
            .borrow()
            .get(&existing_id)
            .map(|s| s.ret_ty.clone())
            .expect("mono signature registered with its cache entry");
        return Some((existing_id, ret_ty));
    }

    // Allocate a fresh id and lower the FnDef under the substitution.
    let new_id = FunctionId(ctx.env.sink.next_id.get());
    ctx.env.sink.next_id.set(new_id.0 + 1);
    // Pre-cache so a recursive call inside the body finds the in-progress mono.
    ctx.env.sink.mono_cache.borrow_mut().insert(key, new_id);
    // Pre-resolve the return type from AST + subst so a recursive
    // `sum_down(n - 1)` inside the body sees the correct result type.
    let preview_ret_ty = match &fn_def.ret_ty {
        Some(t) => {
            let mut rcx = LowerCtx::new(ctx.env, &subst, None);
            rcx.current_module = fn_module.clone();
            rcx.resolve_ast_ty(t)
        }
        None => HirTy::Unit,
    };
    ctx.env.sink.mono_sigs.borrow_mut().insert(
        new_id,
        FnSig {
            id: new_id,
            ret_ty: preview_ret_ty,
            param_defaults: Vec::new(),
            param_tys: Vec::new(),
            param_names: Vec::new(),
        },
    );

    let mangled_name = format!(
        "{}__mono__{}",
        fn_def.name,
        subst_tys.iter().map(ty_mangle).collect::<Vec<_>>().join("_")
    );

    ctx.env.sink.mono_depth.set(ctx.env.sink.mono_depth.get() + 1);
    let mono_fn = lower_fn_inner(ctx.env, fn_def, new_id, mangled_name, None, fn_module, &subst);
    ctx.env.sink.mono_depth.set(ctx.env.sink.mono_depth.get() - 1);

    let ret_ty = mono_fn.ret_ty.clone();
    let mono_param_tys: Vec<HirTy> =
        mono_fn.params.iter().map(|p| p.ty.clone()).collect();
    let mono_param_names: Vec<String> =
        mono_fn.params.iter().map(|p| p.name.clone()).collect();
    ctx.env.sink.mono_sigs.borrow_mut().insert(
        new_id,
        FnSig {
            id: new_id,
            ret_ty: ret_ty.clone(),
            param_defaults: Vec::new(),
            param_tys: mono_param_tys,
            param_names: mono_param_names,
        },
    );
    ctx.env.sink.extras.borrow_mut().push(mono_fn);
    Some((new_id, ret_ty))
}

/// Lower one function body. `subst` is the type-parameter substitution
/// of a monomorphization (empty otherwise); `module` is where the
/// body's names resolve.
fn lower_fn_inner(
    env: &Env<'_>,
    fn_def: &FnDef,
    id: FunctionId,
    name: String,
    self_ty: Option<HirTy>,
    module: String,
    subst: &HashMap<String, HirTy>,
) -> HirFunction {
    let mut ctx = LowerCtx::new(env, subst, self_ty);
    ctx.current_module = module;

    let mut params = Vec::with_capacity(fn_def.params.len());
    for p in &fn_def.params {
        params.push(lower_param(&mut ctx, p));
    }

    let ret_ty = match &fn_def.ret_ty {
        Some(t) => ctx.resolve_ast_ty(t),
        None => HirTy::Unit,
    };
    ctx.fn_ret_ty = ret_ty.clone();

    let body = fn_def.body.as_ref().map(|b| lower_fn_body(&mut ctx, b, &fn_def.name));

    HirFunction {
        id,
        def_id: None,
        name,
        params,
        locals: ctx.into_locals(),
        ret_ty,
        body,
        is_async: fn_def.is_async,
        is_generator: fn_def.is_generator,
        span: fn_def.span,
    }
}

/// Like `resolve_ty_with_structs`, but applies an AST-level type-param
/// substitution before lookup. For `Pair<T>` with `subst = {T → i32}`,
/// resolves to `Pair__i32`. Walks recursively into nested types.
fn resolve_ast_with_subst(
    ty: &rokc_ast::Ty,
    struct_table: &HashMap<String, StructId>,
    enum_table: &HashMap<String, EnumId>,
    subst: &HashMap<String, HirTy>,
    sc: Scope<'_>,
) -> HirTy {
    let rec = |t: &rokc_ast::Ty| resolve_ast_with_subst(t, struct_table, enum_table, subst, sc);
    match &ty.kind {
        rokc_ast::TyKind::Path(p) => {
            // Bare type-param reference — resolve directly from subst.
            if p.segments.len() == 1 && p.segments[0].generics.is_empty() {
                if let Some(replacement) = subst.get(&p.segments[0].name) {
                    return replacement.clone();
                }
            }
            // Generic-struct/enum path: resolve generic args under subst,
            // then look up the mangled instantiation.
            let generics = p.segments.last().map(|s| s.generics.as_slice()).unwrap_or(&[]);
            if !generics.is_empty() {
                let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                if let Some(full) = sc.names.canon(&segs, sc.module, &[]) {
                    let args: Vec<HirTy> = generics.iter().map(rec).collect();
                    let mangled = mangle_inst(&full, &args);
                    if let Some(id) = struct_table.get(&mangled) {
                        return HirTy::Struct(*id);
                    }
                    if let Some(id) = enum_table.get(&mangled) {
                        return HirTy::Enum(*id);
                    }
                }
            }
            // Fall back to the regular resolver, then post-substitute
            // any leaked type-param paths.
            let mut t = resolve_ty_with_structs(ty, struct_table, enum_table, sc);
            substitute_aliases(&mut t, subst);
            t
        }
        rokc_ast::TyKind::Sum(parts) => HirTy::Sum(parts.iter().map(rec).collect()),
        rokc_ast::TyKind::Tuple(parts) if parts.is_empty() => HirTy::Unit,
        rokc_ast::TyKind::Tuple(parts) => HirTy::Tuple(parts.iter().map(rec).collect()),
        rokc_ast::TyKind::Array(elem, _) => {
            match resolve_ty_with_structs(ty, struct_table, enum_table, sc) {
                HirTy::Array(_, n) => HirTy::Array(Box::new(rec(elem)), n),
                other => other,
            }
        }
        rokc_ast::TyKind::Fn(args, ret) => {
            HirTy::Fn(args.iter().map(rec).collect(), Box::new(rec(ret)))
        }
        _ => {
            let mut t = resolve_ty_with_structs(ty, struct_table, enum_table, sc);
            substitute_aliases(&mut t, subst);
            t
        }
    }
}

/// `{T → arg}` for a generic item's type parameters.
fn generic_subst(generics: &rokc_ast::Generics, args: &[HirTy]) -> HashMap<String, HirTy> {
    let mut subst = HashMap::new();
    for (i, gp) in generics.params.iter().enumerate() {
        if let rokc_ast::GenericParam::Type { name, .. } = gp {
            if let Some(arg) = args.get(i) {
                subst.insert(name.clone(), arg.clone());
            }
        }
    }
    subst
}

/// Field list of a generic struct instantiated with `args`.
fn generic_struct_fields(
    def: &AstStructDef,
    args: &[HirTy],
    struct_table: &HashMap<String, StructId>,
    enum_table: &HashMap<String, EnumId>,
    sc: Scope<'_>,
) -> Vec<HirField> {
    let subst = generic_subst(&def.generics, args);
    let field = |name: String, ty: &Ty, default: Option<Expr>| HirField {
        name,
        ty: resolve_ast_with_subst(ty, struct_table, enum_table, &subst, sc),
        default,
    };
    match &def.kind {
        AstStructKind::Named(fs) => fs
            .iter()
            .map(|f| field(f.name.clone(), &f.ty, f.default.clone()))
            .collect(),
        AstStructKind::Tuple(fs) => fs
            .iter()
            .enumerate()
            .map(|(i, f)| field(i.to_string(), &f.ty, None))
            .collect(),
        AstStructKind::Unit => Vec::new(),
    }
}

/// Same as `instantiate_generic_structs` but for `enum Maybe<T>` etc.
fn instantiate_generic_enums(
    program: &Program,
    generic_enums: &HashMap<String, &AstEnumDef>,
    struct_table: &mut HashMap<String, StructId>,
    enum_table: &mut HashMap<String, EnumId>,
    enum_defs: &mut Vec<HirEnumDef>,
    names: &TypeNames<'_>,
) {
    if generic_enums.is_empty() {
        return;
    }
    for _ in 0..8 {
        let before = enum_table.len();
        for item in &program.items {
            let module = item_module(item);
            let sc = Scope { names, module: &module };
            crate::walk::for_each_ty(item, &mut |ty| {
                visit_ty_for_enum_mono(ty, generic_enums, struct_table, enum_table, enum_defs, sc);
            });
        }
        if enum_table.len() == before {
            break;
        }
    }
}

/// Canonical generic base + resolved args for a `Base<A, ...>` type path,
/// when every arg is concrete (no unresolved type parameter).
fn generic_use<'t, V>(
    ty: &rokc_ast::Ty,
    generic_defs: &'t HashMap<String, V>,
    struct_table: &HashMap<String, StructId>,
    enum_table: &HashMap<String, EnumId>,
    sc: Scope<'_>,
) -> Option<(String, &'t V, Vec<HirTy>)> {
    let rokc_ast::TyKind::Path(p) = &ty.kind else { return None };
    let last = p.segments.last()?;
    if last.generics.is_empty() {
        return None;
    }
    let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
    let full = sc.names.canon(&segs, sc.module, &[])?;
    let def = generic_defs.get(&full)?;
    let args: Vec<HirTy> = last
        .generics
        .iter()
        .map(|t| resolve_ty_with_structs(t, struct_table, enum_table, sc))
        .collect();
    let mut leftover = Vec::new();
    for a in &args {
        collect_unknown_paths(a, &mut leftover);
    }
    if !leftover.is_empty() {
        return None;
    }
    Some((full, def, args))
}

fn visit_ty_for_enum_mono(
    ty: &rokc_ast::Ty,
    generic_enums: &HashMap<String, &AstEnumDef>,
    struct_table: &mut HashMap<String, StructId>,
    enum_table: &mut HashMap<String, EnumId>,
    enum_defs: &mut Vec<HirEnumDef>,
    sc: Scope<'_>,
) {
    let Some((full, def, arg_tys)) = generic_use(ty, generic_enums, struct_table, enum_table, sc)
    else {
        return;
    };
    let mangled = mangle_inst(&full, &arg_tys);
    if enum_table.contains_key(&mangled) {
        return;
    }
    let id = EnumId(u32::try_from(enum_defs.len()).expect("EnumId overflow"));
    enum_table.insert(mangled.clone(), id);
    let subst = generic_subst(&def.generics, &arg_tys);
    let res = |t: &Ty| resolve_ast_with_subst(t, struct_table, enum_table, &subst, sc);
    let variants: Vec<HirEnumVariant> = def
        .variants
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let tag = u32::try_from(i).expect("variant index overflow");
            let (payload_ty, named_fields, arity) = match &v.kind {
                rokc_ast::EnumVariantKind::Unit | rokc_ast::EnumVariantKind::Value(_) => {
                    (None, Vec::new(), 0)
                }
                rokc_ast::EnumVariantKind::Tuple(tys) if tys.len() == 1 => {
                    (Some(res(&tys[0])), Vec::new(), 1)
                }
                rokc_ast::EnumVariantKind::Tuple(tys) => {
                    (Some(HirTy::Tuple(tys.iter().map(res).collect())), Vec::new(), tys.len())
                }
                rokc_ast::EnumVariantKind::Named(fields) => (
                    Some(HirTy::Tuple(fields.iter().map(|f| res(&f.ty)).collect())),
                    fields.iter().map(|f| f.name.clone()).collect(),
                    fields.len(),
                ),
            };
            HirEnumVariant { name: v.name.clone(), tag, payload_ty, named_fields, arity }
        })
        .collect();
    enum_defs.push(HirEnumDef {
        id,
        def_id: None,
        name: mangled,
        variants,
        span: def.span,
    });
}

/// Eager pre-pass over the program AST that finds every generic-struct
/// type usage (`Path("Pair", [T])`) and registers a fresh concrete
/// `HirStructDef` per unique substitution. The instantiation name is
/// mangled (`Pair__i32`) so subsequent type resolution treats it as
/// just another concrete struct.
fn instantiate_generic_structs(
    program: &Program,
    generic_structs: &HashMap<String, &AstStructDef>,
    struct_table: &mut HashMap<String, StructId>,
    struct_defs: &mut Vec<HirStructDef>,
    enum_table: &HashMap<String, EnumId>,
    names: &TypeNames<'_>,
) {
    if generic_structs.is_empty() {
        return;
    }
    // Iterate to a fixpoint: instantiations themselves can reference
    // other generic structs.
    for _ in 0..8 {
        let before = struct_table.len();
        for item in &program.items {
            let module = item_module(item);
            let sc = Scope { names, module: &module };
            crate::walk::for_each_ty(item, &mut |ty| {
                let Some((full, def, args)) =
                    generic_use(ty, generic_structs, struct_table, enum_table, sc)
                else {
                    return;
                };
                let mangled = mangle_inst(&full, &args);
                if struct_table.contains_key(&mangled) {
                    return;
                }
                // Reserve the id first so a self-reference inside the
                // fields resolves to itself rather than recursing.
                let id = StructId(u32::try_from(struct_defs.len()).expect("StructId overflow"));
                struct_table.insert(mangled.clone(), id);
                let fields = generic_struct_fields(def, &args, struct_table, enum_table, sc);
                struct_defs.push(HirStructDef {
                    id,
                    def_id: None,
                    name: mangled,
                    fields,
                    span: def.span,
                    generic_args: args,
                    union_kind: None,
                });
            });
        }
        if struct_table.len() == before {
            break;
        }
    }
}

/// Walk a `HirTy` substituting any unresolved `Path([alias_name])`
/// nodes with their concrete type from `aliases`. Multi-level
/// resolution is handled by the caller (a small fixed-iteration loop
/// over the alias table itself).
fn substitute_aliases(ty: &mut HirTy, aliases: &HashMap<String, HirTy>) {
    match ty {
        HirTy::Path(parts) => {
            if parts.len() == 1 {
                if let Some(replacement) = aliases.get(&parts[0]) {
                    *ty = replacement.clone();
                }
            }
        }
        HirTy::Sum(parts) | HirTy::Tuple(parts) => {
            for p in parts {
                substitute_aliases(p, aliases);
            }
        }
        HirTy::Array(elem, _) => substitute_aliases(elem, aliases),
        HirTy::Fn(args, ret) | HirTy::Closure { args, ret, .. } => {
            for a in args {
                substitute_aliases(a, aliases);
            }
            substitute_aliases(ret, aliases);
        }
        _ => {}
    }
}

/// `resolve_ty` plus module-aware struct / enum / alias name lookup.
/// Unresolvable names stay `HirTy::Path` (generic params get substituted
/// later; anything left over is reported by `check_unresolved_types`).
fn resolve_ty_with_structs(
    ty: &rokc_ast::Ty,
    structs: &HashMap<String, StructId>,
    enums: &HashMap<String, EnumId>,
    sc: Scope<'_>,
) -> HirTy {
    let rec = |t: &rokc_ast::Ty| resolve_ty_with_structs(t, structs, enums, sc);
    match &ty.kind {
        AstTyKind::Path(p) => {
            let prim = resolve_ty(ty);
            if matches!(prim, HirTy::Prim(_)) {
                return prim;
            }
            let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
            let generics = p.segments.last().map(|s| s.generics.as_slice()).unwrap_or(&[]);
            let Some(full) = sc.names.canon(&segs, sc.module, &[]) else {
                return HirTy::Path(segs.iter().map(|s| (*s).to_owned()).collect());
            };
            if sc.names.traits.contains(&full) {
                sc.names.error(format!(
                    "trait `{full}` cannot be used as a type directly — use a closed \
                     sum (`A | B`) or a generic parameter (`<T: {full}>`) instead \
                     (i-want-this 538)"
                ));
                return HirTy::Any;
            }
            if !generics.is_empty() {
                let args: Vec<HirTy> = generics.iter().map(rec).collect();
                let mangled = mangle_inst(&full, &args);
                if let Some(id) = structs.get(&mangled) {
                    return HirTy::Struct(*id);
                }
                if let Some(id) = enums.get(&mangled) {
                    return HirTy::Enum(*id);
                }
                return HirTy::Path(vec![full]);
            }
            if let Some(id) = structs.get(&full) {
                return HirTy::Struct(*id);
            }
            if let Some(id) = enums.get(&full) {
                return HirTy::Enum(*id);
            }
            // Type alias (substituted later) or a generic base used
            // without arguments.
            HirTy::Path(vec![full])
        }
        AstTyKind::Array(elem, len) => {
            let n = match len {
                rokc_ast::ConstExpr::Literal(rokc_ast::Literal::Int(s)) => {
                    let cleaned: String = s.chars().filter(|c| *c != '_').collect();
                    cleaned.parse::<u32>().ok()
                }
                _ => None,
            };
            let Some(n) = n else {
                sc.names.error(
                    "array length must be an integer literal (stage-1 limitation)".to_owned(),
                );
                return HirTy::Any;
            };
            HirTy::Array(Box::new(rec(elem)), n)
        }
        // `T | U` — recurse so Path("Counter") resolves to Struct(id), not
        // an opaque path the MIR layer would treat as `Any`.
        AstTyKind::Sum(parts) => HirTy::Sum(parts.iter().map(rec).collect()),
        AstTyKind::Tuple(parts) if parts.is_empty() => HirTy::Unit,
        AstTyKind::Tuple(parts) => HirTy::Tuple(parts.iter().map(rec).collect()),
        AstTyKind::Fn(args, ret) => HirTy::Fn(args.iter().map(rec).collect(), Box::new(rec(ret))),
        _ => resolve_ty(ty),
    }
}

/// Table key of a generic instantiation: `a::Pair` + `[i32, bool]` →
/// `a::Pair__i32_bool`.
fn mangle_inst(base: &str, args: &[HirTy]) -> String {
    format!("{base}__{}", args.iter().map(ty_mangle).collect::<Vec<_>>().join("_"))
}

/// Per-function signature used by lowering. Avoids re-resolving the AST
/// return type at every call site. `param_defaults` mirrors the function's
/// parameter list — each entry is `Some(expr)` if the parameter has a
/// default value the caller may omit, else `None`.
#[derive(Clone)]
struct FnSig {
    id: FunctionId,
    ret_ty: HirTy,
    param_defaults: Vec<Option<Expr>>,
    /// Resolved parameter types in declaration order. Used by `lower_call`
    /// to push expected-type hints into argument lowering — that's how an
    /// untyped closure (`apply(3, |x| { x*4 })`) picks up `i32` for `x`
    /// from the callee's `f: fn(i32) -> i32` signature.
    param_tys: Vec<HirTy>,
    /// Parameter names in declaration order. Used by `lower_call` to
    /// reorder named arguments (`f(name: 42)` per spec 4.1) into their
    /// positional slots.
    param_names: Vec<String>,
}

fn lower_fn(
    env: &Env<'_>,
    fn_def: &FnDef,
    id: FunctionId,
    method_self_ty: Option<HirTy>,
    module: String,
) -> HirFunction {
    // Methods get a synthetic mangled name so multiple impls of the
    // same method name don't collide as MLIR symbols.
    let name = method_self_ty.as_ref().map_or_else(
        || fn_def.name.clone(),
        |ty| format!("{}__{}", ty_mangle(ty), leaf_name(&fn_def.name)),
    );
    lower_fn_inner(env, fn_def, id, name, method_self_ty, module, &HashMap::new())
}

fn none_ty() -> HirTy {
    HirTy::Path(vec!["none".to_owned()])
}

/// The `none` sentinel type (spec 2.x `T | none`).
fn is_none_ty(ty: &HirTy) -> bool {
    matches!(ty, HirTy::Path(p) if p.as_slice() == ["none"])
}

// If `slot_ty` is a Sum and `value.ty` matches one of its variants,
// wrap the value into the sum's tagged-union representation.
fn wrap_into_sum(slot_ty: &HirTy, value: HirExpr) -> HirExpr {
    let HirTy::Sum(variants) = slot_ty else { return value };
    let Some(idx) = sum_variant_index(variants, &value.ty) else { return value };
    let span = value.span;
    let payload = if is_none_ty(&variants[idx]) { None } else { Some(Box::new(value)) };
    HirExpr {
        kind: HirExprKind::SumWrap {
            sum_ty: slot_ty.clone(),
            variant_index: u32::try_from(idx).expect("variant overflow"),
            value: payload,
        },
        ty: slot_ty.clone(),
        span,
    }
}

// Locate `value_ty` in a sum's variant list (structural equality).
fn sum_variant_index(variants: &[HirTy], value_ty: &HirTy) -> Option<usize> {
    variants.iter().position(|v| v == value_ty)
}

/// Can a value of type `actual` flow into a slot of type `expected`
/// (after `wrap_into_sum`)? `Unknown` (an error was already reported)
/// and `Any` (dynamic slot) are compatible with everything.
fn ty_compatible(expected: &HirTy, actual: &HirTy) -> bool {
    let all = |a: &[HirTy], b: &[HirTy]| {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| ty_compatible(x, y))
    };
    match (expected, actual) {
        (HirTy::Unknown | HirTy::Any, _) | (_, HirTy::Unknown | HirTy::Any) => true,
        (HirTy::Sum(vs), a) if !matches!(a, HirTy::Sum(_)) => sum_variant_index(vs, a).is_some(),
        (HirTy::Tuple(a), HirTy::Tuple(b)) | (HirTy::Sum(a), HirTy::Sum(b)) => all(a, b),
        (HirTy::Array(a, n), HirTy::Array(b, m)) => n == m && ty_compatible(a, b),
        (HirTy::Fn(a1, r1), HirTy::Fn(a2, r2)) => all(a1, a2) && ty_compatible(r1, r2),
        _ => expected == actual,
    }
}

/// Wrap `value` into `slot` (sum injection) and report a type mismatch.
/// `what` names the slot for the diagnostic ("argument 1 of `f`").
fn coerce(ctx: &LowerCtx<'_>, slot: &HirTy, value: HirExpr, what: &dyn Fn() -> String) -> HirExpr {
    let v = wrap_into_sum(slot, value);
    if !ty_compatible(slot, &v.ty) {
        let hint = if matches!((slot, &v.ty), (HirTy::Fn(..), HirTy::Closure { .. })) {
            " — a closure that captures variables is not a plain `fn` pointer (spec 4.6)"
        } else {
            ""
        };
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "mismatched types: {} expects `{}`, found `{}`{hint}",
                what(),
                ctx.ty_name(slot),
                ctx.ty_name(&v.ty)
            ),
        );
    }
    v
}

/// Lower `e` with `ty` as its expected type (`Unknown` = no expectation).
fn lower_expected(ctx: &mut LowerCtx<'_>, e: &Expr, ty: HirTy) -> HirExpr {
    ctx.push_expected(ty);
    let r = lower_expr(ctx, e);
    ctx.pop_expected();
    r
}

/// A block / expression whose evaluation never completes normally:
/// it ends in `return` / `throw` / `break` / `continue`, a `loop` with
/// no `break` out of it, or an `if` / `match` whose every branch diverges.
fn hir_block_diverges(b: &HirBlock) -> bool {
    b.stmts.iter().any(|s| match s {
        HirStmt::Return(_)
        | HirStmt::Throw(_)
        | HirStmt::Break { .. }
        | HirStmt::Continue { .. } => true,
        HirStmt::Expr(e) | HirStmt::Let { init: e, .. } => hir_expr_diverges(e),
        _ => false,
    }) || b.trailing.as_ref().is_some_and(hir_expr_diverges)
}

fn hir_expr_diverges(e: &HirExpr) -> bool {
    match &e.kind {
        HirExprKind::Block(b) => hir_block_diverges(b),
        HirExprKind::If { then_block, else_branch: Some(eb), .. } => {
            hir_block_diverges(then_block) && hir_expr_diverges(eb)
        }
        HirExprKind::Match { arms, .. } => {
            !arms.is_empty() && arms.iter().all(|a| hir_expr_diverges(&a.body))
        }
        HirExprKind::Loop { label, body, .. } => !block_breaks_out(body, label.as_deref(), true),
        _ => false,
    }
}

/// Does `b` contain a `break` that exits the loop labelled `label`?
/// `direct` = we're not inside a nested loop (unlabelled breaks count).
fn block_breaks_out(b: &HirBlock, label: Option<&str>, direct: bool) -> bool {
    let in_expr = |e: &HirExpr| expr_breaks_out(e, label, direct);
    b.stmts.iter().any(|s| match s {
        HirStmt::Break { label: bl, .. } => {
            (bl.is_none() && direct) || (bl.is_some() && bl.as_deref() == label)
        }
        HirStmt::Let { init: e, .. }
        | HirStmt::Assign { value: e, .. }
        | HirStmt::StaticAssign { value: e, .. }
        | HirStmt::Expr(e)
        | HirStmt::Return(Some(e)) => in_expr(e),
        _ => false,
    }) || b.trailing.as_ref().is_some_and(in_expr)
}

fn expr_breaks_out(e: &HirExpr, label: Option<&str>, direct: bool) -> bool {
    match &e.kind {
        HirExprKind::Block(b) => block_breaks_out(b, label, direct),
        HirExprKind::If { then_block, else_branch, .. } => {
            block_breaks_out(then_block, label, direct)
                || else_branch.as_deref().is_some_and(|x| expr_breaks_out(x, label, direct))
        }
        HirExprKind::Match { arms, .. } => {
            arms.iter().any(|a| expr_breaks_out(&a.body, label, direct))
        }
        HirExprKind::While { body, .. } | HirExprKind::Loop { body, .. } => {
            block_breaks_out(body, label, false)
        }
        _ => false,
    }
}

fn ty_mangle(ty: &HirTy) -> String {
    match ty {
        HirTy::Struct(id) => format!("Struct{}", id.0),
        HirTy::Enum(id) => format!("Enum{}", id.0),
        HirTy::Prim(p) => p.name().to_owned(),
        HirTy::Unit => "Unit".to_owned(),
        HirTy::Any => "Any".to_owned(),
        HirTy::Unknown => "Unknown".to_owned(),
        HirTy::Tuple(parts) => {
            let inner: Vec<String> = parts.iter().map(ty_mangle).collect();
            format!("Tup{}of{}", parts.len(), inner.join("x"))
        }
        HirTy::Array(elem, len) => format!("Arr{}x{}", len, ty_mangle(elem)),
        HirTy::Sum(variants) => {
            let inner: Vec<String> = variants.iter().map(ty_mangle).collect();
            format!("Sum{}of{}", variants.len(), inner.join("x"))
        }
        HirTy::Fn(params, ret) => {
            let inner: Vec<String> = params.iter().map(ty_mangle).collect();
            format!("Fn{}of{}_to_{}", params.len(), inner.join("x"), ty_mangle(ret))
        }
        HirTy::Path(segs) => format!("Path_{}", segs.join("_")),
        HirTy::Closure { args, ret, env } => {
            let inner: Vec<String> = args.iter().map(ty_mangle).collect();
            format!(
                "Closure{}of{}_to_{}_env{}",
                args.len(),
                inner.join("x"),
                ty_mangle(ret),
                ty_mangle(env)
            )
        }
    }
}

fn lower_param(ctx: &mut LowerCtx<'_>, p: &Param) -> HirParam {
    let ty = if p.name == "self" {
        // Implicit `self` receiver inherits the impl target's type.
        ctx.self_ty.clone().unwrap_or(HirTy::Any)
    } else {
        p.ty.as_ref().map_or(HirTy::Any, |t| ctx.resolve_ast_ty(t))
    };
    let local = ctx.declare(Some(p.name.clone()), ty.clone());
    HirParam { name: p.name.clone(), local, ty, by_ref: p.by_ref }
}

/// Lower a function body and check its value against the return type:
/// the trailing expression must match, and a non-unit function without
/// a trailing value must not fall off the end.
fn lower_fn_body(ctx: &mut LowerCtx<'_>, b: &Block, fn_name: &str) -> HirBlock {
    let ret = ctx.fn_ret_ty.clone();
    ctx.push_expected(ret.clone());
    let mut block = lower_block(ctx, b);
    ctx.pop_expected();
    match block.trailing.take() {
        // A unit function discards a trailing value (`fn f() { g() }`).
        Some(t) if ret == HirTy::Unit && t.ty != HirTy::Unit => block.stmts.push(HirStmt::Expr(t)),
        Some(t) if hir_expr_diverges(&t) => block.trailing = Some(t),
        // `fn f() -> i32 { if c { return 1; } }`: a unit-valued tail
        // means some path falls off the end.
        Some(t) if t.ty == HirTy::Unit && !matches!(ret, HirTy::Unknown | HirTy::Unit) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "function `{}` returns `{}` but its body can finish without \
                     returning a value (missing `return`)",
                    leaf_name(fn_name),
                    ctx.ty_name(&ret)
                ),
            );
            block.trailing = Some(t);
        }
        Some(t) => {
            let name = leaf_name(fn_name).to_owned();
            block.trailing = Some(coerce(ctx, &ret, t, &|| format!("the body of `{name}`")));
        }
        None => {
            if !matches!(ret, HirTy::Unit | HirTy::Unknown) && !hir_block_diverges(&block) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "function `{}` returns `{}` but its body can finish without \
                         returning a value (missing `return`)",
                        leaf_name(fn_name),
                        ctx.ty_name(&ret)
                    ),
                );
            }
        }
    }
    block
}

fn lower_block(ctx: &mut LowerCtx<'_>, block: &Block) -> HirBlock {
    ctx.push_scope();
    let mut stmts = Vec::with_capacity(block.stmts.len());
    for s in &block.stmts {
        match &s.kind {
            StmtKind::LetStruct { path, fields, rest: _, ty, init } => {
                lower_let_struct(ctx, path, fields, ty.as_ref(), init, s.span, &mut stmts);
            }
            StmtKind::LetTuple { names, rest, ty, init } => {
                lower_let_tuple(ctx, names, rest.as_ref(), ty.as_ref(), init, s.span, &mut stmts);
            }
            _ => {
                if let Some(stmt) = lower_stmt(ctx, s) {
                    stmts.push(stmt);
                }
            }
        }
    }
    // The trailing expression is the block's value: it inherits the
    // block's expected type.
    let trailing = block.trailing.as_ref().map(|e| lower_expr(ctx, e));
    ctx.pop_scope();
    HirBlock {
        stmts,
        trailing,
        label: block.label.clone(),
    }
}

/// `let S { f1, f2: alias, .. } [: T] = init;` → temp local + one field
/// read per binding.
fn lower_let_struct(
    ctx: &mut LowerCtx<'_>,
    path: &AstPath,
    fields: &[(String, String)],
    ty: Option<&Ty>,
    init: &Expr,
    span: rokc_diagnostic::Span,
    stmts: &mut Vec<HirStmt>,
) {
    let pre_ty = ty.map(|t| ctx.resolve_ast_ty(t));
    let init_h = lower_expected(ctx, init, pre_ty.clone().unwrap_or(HirTy::Unknown));
    let init_h = match &pre_ty {
        Some(t) => coerce(ctx, t, init_h, &|| "the destructured value".to_owned()),
        None => init_h,
    };
    let init_ty = init_h.ty.clone();
    let temp_local = ctx.declare(None, init_ty.clone());
    stmts.push(HirStmt::Let { local: temp_local, init: init_h });
    let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
    let named = ctx.canon_type(&segs).and_then(|full| ctx.lookup_struct(&full));
    let sid = match (&init_ty, named) {
        (HirTy::Unknown, _) => {
            // Init failed (reported); bind the names so later uses don't
            // cascade into "cannot find value".
            for (_, bind) in fields {
                ctx.declare(Some(bind.clone()), HirTy::Unknown);
            }
            return;
        }
        (HirTy::Struct(sid), Some(n)) if *sid == n => *sid,
        (HirTy::Struct(sid), None) if path.segments.is_empty() => *sid,
        _ => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "struct pattern `{}` does not match the value's type `{}`",
                    segs.join("::"),
                    ctx.ty_name(&init_ty)
                ),
            );
            for (_, bind) in fields {
                ctx.declare(Some(bind.clone()), HirTy::Unknown);
            }
            return;
        }
    };
    let def = ctx.struct_def(sid);
    for (field_name, bind_name) in fields {
        let Some(idx) = def.fields.iter().position(|f| &f.name == field_name) else {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("struct `{}` has no field `{field_name}`", ctx.ty_name(&init_ty)),
            );
            ctx.declare(Some(bind_name.clone()), HirTy::Unknown);
            continue;
        };
        ctx.check_field_visible(sid, field_name);
        let field_ty = def.fields[idx].ty.clone();
        let read = HirExpr {
            ty: field_ty.clone(),
            span,
            kind: HirExprKind::FieldRead {
                target: Box::new(HirExpr {
                    ty: init_ty.clone(),
                    span,
                    kind: HirExprKind::Local(temp_local),
                }),
                struct_id: sid,
                field_index: u32::try_from(idx).expect("field idx overflow"),
                field_ty: field_ty.clone(),
            },
        };
        let local = ctx.declare(Some(bind_name.clone()), field_ty);
        stmts.push(HirStmt::Let { local, init: read });
    }
}

/// `let (a, b, ..rest) [: T] = init;` → fresh tuple local plus per-name
/// index reads (spec 3.15.2 / 3.15.3).
fn lower_let_tuple(
    ctx: &mut LowerCtx<'_>,
    names: &[String],
    rest: Option<&(usize, Option<String>)>,
    ty: Option<&Ty>,
    init: &Expr,
    span: rokc_diagnostic::Span,
    stmts: &mut Vec<HirStmt>,
) {
    let pre_ty = ty.map(|t| ctx.resolve_ast_ty(t));
    let init_h = lower_expected(ctx, init, pre_ty.clone().unwrap_or(HirTy::Unknown));
    let init_h = match &pre_ty {
        Some(t) => coerce(ctx, t, init_h, &|| "the destructured value".to_owned()),
        None => init_h,
    };
    let init_ty = init_h.ty.clone();
    let elem_tys: Vec<HirTy> = match &init_ty {
        HirTy::Tuple(ts) => ts.clone(),
        HirTy::Unknown => vec![HirTy::Unknown; names.len()],
        other => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("tuple destructure of a non-tuple value of type `{}`", ctx.ty_name(other)),
            );
            vec![HirTy::Unknown; names.len()]
        }
    };
    // Spec 3.15.2/3.15.3: length must match (no rest), or be ≥
    // names.len() when a `..` is present.
    let needed = names.len();
    let have = elem_tys.len();
    if rest.is_none() && have != needed {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "tuple destructure length mismatch: pattern has {needed} element{}, value \
                 has {have} (spec 3.15.2)",
                if needed == 1 { "" } else { "s" }
            ),
        );
    } else if rest.is_some() && have < needed {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "tuple destructure too short: pattern needs at least {needed} non-rest \
                 element{}, value has {have} (spec 3.15.3)",
                if needed == 1 { "" } else { "s" }
            ),
        );
    }
    let tuple_local = ctx.declare(None, init_ty.clone());
    stmts.push(HirStmt::Let { local: tuple_local, init: init_h });
    // Source-position → name mapping. With a rest at index `r` and a
    // value tuple of length `N`:
    //   names[..r]      → init.0  .. init.r-1
    //   rest (if named) → tuple of init.r .. init.r + (N-needed) - 1
    //   names[r..]      → init.r+(N-needed) .. init.N-1
    let rest_take = if rest.is_some() { have.saturating_sub(needed) } else { 0 };
    let rest_idx = rest.map_or(needed, |(i, _)| *i);
    let read = |index: usize, ety: HirTy| HirExpr {
        ty: ety.clone(),
        span,
        kind: HirExprKind::TupleField {
            target: Box::new(HirExpr {
                ty: init_ty.clone(),
                span,
                kind: HirExprKind::Local(tuple_local),
            }),
            index: u32::try_from(index).expect("tuple index overflow"),
            field_ty: ety,
        },
    };
    for (i, name) in names.iter().enumerate() {
        if name == "_" {
            continue;
        }
        let init_index = if i < rest_idx { i } else { i + rest_take };
        let elem_ty = elem_tys.get(init_index).cloned().unwrap_or(HirTy::Unknown);
        let init = read(init_index, elem_ty.clone());
        let local = ctx.declare(Some(name.clone()), elem_ty);
        stmts.push(HirStmt::Let { local, init });
    }
    // Synthesize the rest-binding's sub-tuple if it was named.
    if let Some((rest_idx, Some(rest_name))) = rest {
        let sub: Vec<HirExpr> = (0..rest_take)
            .map(|k| {
                let src = rest_idx + k;
                read(src, elem_tys.get(src).cloned().unwrap_or(HirTy::Unknown))
            })
            .collect();
        let rest_ty = HirTy::Tuple(sub.iter().map(|e| e.ty.clone()).collect());
        let rest_local = ctx.declare(Some(rest_name.clone()), rest_ty.clone());
        stmts.push(HirStmt::Let {
            local: rest_local,
            init: HirExpr { ty: rest_ty, span, kind: HirExprKind::Tuple { fields: sub } },
        });
    }
}

/// Build the runtime abort `rok_panic(msg, len)` (spec 805: writes `msg`
/// to stderr and exits with code 101). The message is a string literal;
/// `len` is its byte length.
fn panic_call(ctx: &LowerCtx<'_>, msg: &str, span: rokc_diagnostic::Span) -> HirExpr {
    let Some(sig) = ctx.env.fn_table.get("rok_panic") else {
        return ctx.error_expr(
            span,
            "internal: runtime hook `rok_panic` is not declared".to_owned(),
        );
    };
    let len = i128::try_from(msg.len()).expect("message length fits i128");
    HirExpr {
        kind: HirExprKind::Call {
            callee: sig.id,
            args: vec![
                HirExpr {
                    kind: HirExprKind::Const(ConstVal::Str(msg.to_owned())),
                    ty: HirTy::Prim(PrimTy::Str),
                    span,
                },
                HirExpr {
                    kind: HirExprKind::Const(ConstVal::Int { value: len, ty: PrimTy::Usize }),
                    ty: HirTy::Prim(PrimTy::Usize),
                    span,
                },
            ],
        },
        ty: HirTy::Unit,
        span,
    }
}

fn lower_stmt(ctx: &mut LowerCtx<'_>, stmt: &Stmt) -> Option<HirStmt> {
    match &stmt.kind {
        StmtKind::Let { name, ty, init } => {
            // Spec variant 238-239: same-scope `let` redeclaration is
            // banned (typo guard, no shadowing). Different scopes still
            // create fresh bindings.
            if ctx.lookup_in_current_scope(name).is_some() {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "`{name}` is already declared in this scope. rok forbids \
                         redeclaration with `let`; use `=` to reassign or pick a \
                         different name (spec variant 238)"
                    ),
                );
            }
            // The declared type (if any) is the init's expected type, so
            // literals and generic-enum leaves (`Box::None`) pick it up.
            let pre_ty = ty.as_ref().map(|t| ctx.resolve_ast_ty(t));
            let init = lower_expected(ctx, init, pre_ty.clone().unwrap_or(HirTy::Unknown));
            let (declared_ty, init) = match pre_ty {
                Some(t) => {
                    let init = coerce(ctx, &t, init, &|| format!("`let {name}`"));
                    (t, init)
                }
                None => (init.ty.clone(), init),
            };
            let local = ctx.declare(Some(name.clone()), declared_ty);
            Some(HirStmt::Let { local, init })
        }
        StmtKind::Return(value) => {
            let ret = ctx.fn_ret_ty.clone();
            let Some(e) = value else {
                if !matches!(ret, HirTy::Unit | HirTy::Unknown) {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("`return;` without a value in a function returning `{}`", ctx.ty_name(&ret)),
                    );
                }
                return Some(HirStmt::Return(None));
            };
            let lowered = lower_expected(ctx, e, ret.clone());
            // A closure without a declared return type takes it from its
            // first `return`.
            if ret == HirTy::Unknown && ctx.infer_ret {
                ctx.fn_ret_ty = lowered.ty.clone();
                return Some(HirStmt::Return(Some(lowered)));
            }
            // Spec 4.5/4.6: a capturing closure is a `{fn_ptr, env}` pair,
            // not a bare `fn(...)` pointer.
            if matches!((&ret, &lowered.ty), (HirTy::Fn(..), HirTy::Closure { .. })) {
                return Some(HirStmt::Return(Some(ctx.error_expr(
                    lowered.span,
                    "cannot return a closure through a `fn(...)` pointer return type — \
                     closures with captures aren't bare function pointers (spec 4.6)"
                        .to_owned(),
                ))));
            }
            Some(HirStmt::Return(Some(coerce(ctx, &ret, lowered, &|| "the return value".to_owned()))))
        }
        // Statement position: the value is discarded (expected `()`), so
        // `if` / `match` arms needn't agree on a type.
        StmtKind::Expr(expr) | StmtKind::Trailing(expr) => {
            Some(HirStmt::Expr(lower_expected(ctx, expr, HirTy::Unit)))
        }
        StmtKind::Item(rokc_ast::Item::Use(u)) => {
            // Function-local `use` — flatten the tree into UseEntries
            // and push them into the current scope's local_uses list.
            let mut entries = Vec::new();
            crate::uses::flatten_tree_for_local(&u.tree, &[], &ctx.current_module, &mut entries);
            for e in entries {
                ctx.add_local_use(e);
            }
            None
        }
        StmtKind::Item(_) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "items (fn / struct / impl ...) declared inside a function body are not \
                 supported yet — move them to module level (stage-1 limitation)"
                    .to_owned(),
            );
            None
        }
        StmtKind::Assign(target, value) => lower_assign(ctx, target, value, stmt.span),
        StmtKind::CompoundAssign { target, op, value } => {
            // The parser desugars `a op= b` to `a = a op b`; keep a
            // working path should a front end hand us the raw form.
            let op = op.trim_end_matches('=').to_owned();
            let combined = Expr {
                span: stmt.span,
                kind: ExprKind::OpInfix {
                    op,
                    lhs: Box::new(target.clone()),
                    rhs: Box::new(value.clone()),
                },
            };
            lower_assign(ctx, target, &combined, stmt.span)
        }
        StmtKind::LetTuple { .. } | StmtKind::LetStruct { .. } => {
            unreachable!("destructuring lets are expanded by lower_block")
        }
        StmtKind::Break { label, value } => {
            check_jump_target(ctx, "break", label.as_deref(), false);
            Some(HirStmt::Break {
                label: label.clone(),
                value: value.as_ref().map(|e| lower_expected(ctx, e, HirTy::Unknown)),
            })
        }
        StmtKind::Continue { label } => {
            check_jump_target(ctx, "continue", label.as_deref(), true);
            Some(HirStmt::Continue { label: label.clone() })
        }
        StmtKind::Throw(value) => {
            // Stage 1: no unwinding. `throw v` aborts through the runtime
            // panic hook (exit 101) followed by an unreachable terminator
            // (spec 3.14.1). A string payload becomes the message.
            let value_h = lower_expected(ctx, value, HirTy::Unknown);
            let msg = match &value_h.kind {
                HirExprKind::Const(ConstVal::Str(s)) => format!("uncaught throw: {s}"),
                HirExprKind::Const(ConstVal::Int { value, .. }) => {
                    format!("uncaught throw: {value}")
                }
                _ => "uncaught throw".to_owned(),
            };
            Some(HirStmt::Throw(panic_call(ctx, &msg, stmt.span)))
        }
    }
}

/// `target = value;` for a local / static, a struct-field chain rooted
/// at a local, or an element of a local array.
fn lower_assign(
    ctx: &mut LowerCtx<'_>,
    target: &Expr,
    value: &Expr,
    span: rokc_diagnostic::Span,
) -> Option<HirStmt> {
    match &target.kind {
        // Bare-name assignment (local, else `static`).
        ExprKind::Path(p) if p.segments.len() == 1 => {
            let name = &p.segments[0].name;
            if let Some(local) = ctx.lookup(name) {
                let slot_ty = ctx.local_ty(local);
                let v = lower_expected(ctx, value, slot_ty.clone());
                let value = coerce(ctx, &slot_ty, v, &|| format!("assignment to `{name}`"));
                return Some(HirStmt::Assign { local, value });
            }
            let segs = [name.as_str()];
            if let Some(full) = ctx.resolve_in(&segs, &ctx.env.statics) {
                ctx.check_item_visible(&full, "static");
                let ty = ctx.env.statics[&full].clone();
                let v = lower_expected(ctx, value, ty.clone());
                let value = coerce(ctx, &ty, v, &|| format!("assignment to `{name}`"));
                return Some(HirStmt::StaticAssign { name: full, value });
            }
            // Spec variant 234-235: bare-name assign requires the name to
            // have been previously declared (with `let`).
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "`{name}` is not declared. Use `let` to introduce a new \
                     binding (typo guard, spec variant 234)"
                ),
            );
            None
        }
        // `arr[idx] = value` — element store on a local array.
        ExprKind::Index(arr_expr, idx_expr) => {
            let arr_h = lower_expected(ctx, arr_expr, HirTy::Unknown);
            let idx_h = lower_expected(ctx, idx_expr, HirTy::Unknown);
            let elem = match (&arr_h.kind, &arr_h.ty) {
                (HirExprKind::Local(l), HirTy::Array(elem, _)) => Some((*l, (**elem).clone())),
                (_, HirTy::Unknown) => return None,
                _ => None,
            };
            let Some((array_local, elem_ty)) = elem else {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "indexed assignment needs a local array variable as target \
                         (found `{}`)",
                        ctx.ty_name(&arr_h.ty)
                    ),
                );
                return None;
            };
            check_index_ty(ctx, &idx_h);
            let v = lower_expected(ctx, value, elem_ty.clone());
            let value = coerce(ctx, &elem_ty, v, &|| "the array element".to_owned());
            Some(HirStmt::ArrayAssign { array_local, index: idx_h, value, elem_ty })
        }
        // `a.f1.f2.... = value` — peel field accesses to find the root
        // local, then thread `WithField` updates back out so the rebuilt
        // aggregate gets assigned to that local.
        ExprKind::Field(_, _) => {
            let mut chain: Vec<&str> = Vec::new();
            let mut cur: &Expr = target;
            while let ExprKind::Field(inner, name) = &cur.kind {
                chain.push(name);
                cur = inner;
            }
            chain.reverse();
            let root_h = lower_expected(ctx, cur, HirTy::Unknown);
            if root_h.ty == HirTy::Unknown {
                return None;
            }
            let HirExprKind::Local(local) = root_h.kind else {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    "field assignment needs a local variable at the root of the target \
                     (`v.f = x`)"
                        .to_owned(),
                );
                return None;
            };
            // Walk the chain to get each level's struct id and field index.
            struct Step {
                ty: HirTy,
                struct_id: StructId,
                field_index: u32,
            }
            let mut steps: Vec<Step> = Vec::new();
            let mut step_ty = root_h.ty.clone();
            for name in &chain {
                let HirTy::Struct(sid) = step_ty.clone() else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("no field `{name}` on type `{}`", ctx.ty_name(&step_ty)),
                    );
                    return None;
                };
                let def = ctx.struct_def(sid);
                if def.union_kind.is_some() {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "assigning a field of union `{}` is not implemented yet — \
                             re-initialize the whole union",
                            def.name
                        ),
                    );
                    return None;
                }
                let Some(idx) = def.fields.iter().position(|f| f.name == *name) else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("struct `{}` has no field `{name}`", ctx.ty_name(&step_ty)),
                    );
                    return None;
                };
                ctx.check_field_visible(sid, name);
                steps.push(Step {
                    ty: step_ty.clone(),
                    struct_id: sid,
                    field_index: u32::try_from(idx).expect("field index overflow"),
                });
                step_ty = def.fields[idx].ty.clone();
            }
            let last_name = chain.last().copied().unwrap_or_default().to_owned();
            let v = lower_expected(ctx, value, step_ty.clone());
            let mut acc = coerce(ctx, &step_ty, v, &|| format!("field `{last_name}`"));
            // Materialize parent values via field reads so each
            // WithField has a concrete target.
            let mut targets: Vec<HirExpr> = Vec::new();
            let mut walk = root_h.clone();
            for step in &steps[..steps.len() - 1] {
                let next_ty = ctx.struct_def(step.struct_id).fields[step.field_index as usize]
                    .ty
                    .clone();
                let read = HirExpr {
                    ty: next_ty.clone(),
                    span: target.span,
                    kind: HirExprKind::FieldRead {
                        target: Box::new(walk.clone()),
                        struct_id: step.struct_id,
                        field_index: step.field_index,
                        field_ty: next_ty,
                    },
                };
                targets.push(walk);
                walk = read;
            }
            targets.push(walk);
            for (i, step) in steps.iter().enumerate().rev() {
                acc = HirExpr {
                    ty: step.ty.clone(),
                    span: target.span,
                    kind: HirExprKind::WithField {
                        target: Box::new(targets[i].clone()),
                        struct_id: step.struct_id,
                        field_index: step.field_index,
                        value: Box::new(acc),
                    },
                };
            }
            Some(HirStmt::Assign { local, value: acc })
        }
        _ => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("invalid assignment target (spec 3.4) at line {}", span.line),
            );
            None
        }
    }
}

/// `break` / `continue` must target an enclosing loop (or, for a
/// labelled `break`, a labelled block); MIR would otherwise emit an
/// `unreachable` terminator in its place.
fn check_jump_target(ctx: &LowerCtx<'_>, kw: &str, label: Option<&str>, needs_loop: bool) {
    let ok = match label {
        None => ctx.breakables.iter().any(|(_, is_loop)| *is_loop),
        Some(l) => ctx
            .breakables
            .iter()
            .any(|(bl, is_loop)| bl.as_deref() == Some(l) && (*is_loop || !needs_loop)),
    };
    if !ok {
        let what = label.map_or_else(|| "a loop".to_owned(), |l| format!("a loop labelled `'{l}`"));
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!("`{kw}` outside of {what}"),
        );
    }
}

/// Array indices are integers.
fn check_index_ty(ctx: &LowerCtx<'_>, idx: &HirExpr) {
    if !matches!(&idx.ty, HirTy::Prim(p) if p.is_int()) && idx.ty != HirTy::Unknown {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!("array index must be an integer, found `{}`", ctx.ty_name(&idx.ty)),
        );
    }
}

fn lower_expr(ctx: &mut LowerCtx<'_>, expr: &Expr) -> HirExpr {
    let span = expr.span;
    let unsupported = |ctx: &LowerCtx<'_>, what: &str| {
        ctx.error_expr(span, format!("{what} is not supported yet (stage-1 limitation)"))
    };
    match &expr.kind {
        ExprKind::Literal(lit) => lower_literal(ctx, lit, false, span),
        ExprKind::Path(p) => lower_path(ctx, p, span),
        ExprKind::SelfLower => match ctx.lookup("self") {
            Some(local) => HirExpr { kind: HirExprKind::Local(local), ty: ctx.local_ty(local), span },
            None => ctx.error_expr(span, "`self` is only available inside methods".to_owned()),
        },
        ExprKind::SelfUpper => ctx.error_expr(span, "`Self` is a type, not a value".to_owned()),
        ExprKind::Block(b) => {
            let labelled = b.label.is_some();
            if labelled {
                ctx.breakables.push((b.label.clone(), false));
            }
            let block = lower_block(ctx, b);
            if labelled {
                ctx.breakables.pop();
            }
            // Spec 3.9.10: a labelled block's value can come from a
            // `break 'label value` inside its body, not just from a
            // trailing expression.
            let break_ty = block
                .label
                .as_deref()
                .and_then(|lbl| first_break_value_ty(&block, Some(lbl)));
            let ty = block
                .trailing
                .as_ref()
                .map_or_else(|| break_ty.clone().unwrap_or(HirTy::Unit), |e| e.ty.clone());
            HirExpr { kind: HirExprKind::Block(Box::new(block)), ty, span }
        }
        ExprKind::OpInfix { op, lhs, rhs } => lower_infix(ctx, op, lhs, rhs, span),
        ExprKind::OpPrefix { op, operand } => lower_prefix(ctx, op, operand, span),
        ExprKind::OpPostfix { op, .. } => {
            ctx.error_expr(span, format!("postfix operator `{op}` has no implementation"))
        }
        ExprKind::Call { callee, args, trailing_closure } => {
            // Spec 4.8: trailing closure becomes the last positional arg.
            let mut all_args: Vec<rokc_ast::CallArg> = args.clone();
            if let Some(tc) = trailing_closure {
                all_args.push(rokc_ast::CallArg::Positional((**tc).clone()));
            }
            lower_call(ctx, callee, &all_args, span)
        }
        ExprKind::MethodCall { receiver, method, args, trailing_closure, .. } => {
            let mut all_args: Vec<rokc_ast::CallArg> = args.clone();
            if let Some(tc) = trailing_closure {
                all_args.push(rokc_ast::CallArg::Positional((**tc).clone()));
            }
            lower_method_call(ctx, receiver, method, &all_args, span)
        }
        ExprKind::If { cond, then_branch, else_branch } => {
            lower_if(ctx, cond, then_branch, else_branch.as_deref(), span)
        }
        ExprKind::While { label, cond, body } => {
            let cond_h = lower_cond(ctx, cond);
            ctx.breakables.push((label.clone(), true));
            let body_h = lower_loop_body(ctx, body);
            ctx.breakables.pop();
            HirExpr {
                kind: HirExprKind::While {
                    label: label.clone(),
                    cond: Box::new(cond_h),
                    body: Box::new(body_h),
                },
                ty: HirTy::Unit,
                span,
            }
        }
        ExprKind::For { label, pat, iter, body } => lower_for(ctx, label, pat, iter, body, span),
        ExprKind::Match { scrutinee, arms } => lower_match(ctx, scrutinee, arms, span),
        ExprKind::Try { body, catches, finally } => {
            // Stage 1: no real unwind — a `throw` aborts the process via
            // `rok_panic`, so a catch arm could never run. Refuse it
            // rather than silently ignoring the handler.
            if !catches.is_empty() {
                return ctx.error_expr(
                    span,
                    "`catch` is not implemented yet: a `throw` aborts the process \
                     instead of reaching the handler (spec 3.14.2, stage-1 limitation)"
                        .to_owned(),
                );
            }
            let body_h = lower_block(ctx, body);
            let body_ty = body_h.trailing.as_ref().map_or(HirTy::Unit, |e| e.ty.clone());
            // No finally → forward the body block as-is so its trailing
            // expression remains the value.
            let Some(fin) = finally else {
                return HirExpr { kind: HirExprKind::Block(Box::new(body_h)), ty: body_ty, span };
            };
            // With finally: stash the body's value in a temp, run
            // finally's stmts, then yield the temp as the trailing
            // expression.
            let mut stmts = body_h.stmts;
            let result_local = body_h.trailing.map(|t| {
                let local = ctx.declare(None, body_ty.clone());
                stmts.push(HirStmt::Let { local, init: t });
                local
            });
            ctx.push_expected(HirTy::Unknown);
            let fin_h = lower_block(ctx, fin);
            ctx.pop_expected();
            stmts.extend(fin_h.stmts);
            if let Some(t) = fin_h.trailing {
                stmts.push(HirStmt::Expr(t));
            }
            let trailing = result_local.map(|l| HirExpr {
                kind: HirExprKind::Local(l),
                ty: body_ty.clone(),
                span,
            });
            HirExpr {
                kind: HirExprKind::Block(Box::new(HirBlock { stmts, trailing, label: None })),
                ty: body_ty,
                span,
            }
        }
        ExprKind::StructInit { path, fields, spread } => {
            if spread.is_some() {
                return unsupported(ctx, "struct update syntax `..base`");
            }
            lower_struct_init(ctx, path, fields, span)
        }
        ExprKind::Field(target, name) => lower_field(ctx, target, name, span),
        ExprKind::Tuple(items) if items.is_empty() => {
            HirExpr { kind: HirExprKind::Const(ConstVal::Unit), ty: HirTy::Unit, span }
        }
        ExprKind::Tuple(items) => {
            let expected: Option<Vec<HirTy>> = match ctx.current_expected() {
                Some(HirTy::Tuple(ts)) if ts.len() == items.len() => Some(ts.clone()),
                _ => None,
            };
            let lowered: Vec<HirExpr> = items
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    let slot = expected.as_ref().map_or(HirTy::Unknown, |ts| ts[i].clone());
                    let v = lower_expected(ctx, e, slot.clone());
                    wrap_into_sum(&slot, v)
                })
                .collect();
            let tys: Vec<HirTy> = lowered.iter().map(|e| e.ty.clone()).collect();
            HirExpr { ty: HirTy::Tuple(tys), span, kind: HirExprKind::Tuple { fields: lowered } }
        }
        ExprKind::TupleField(target, index) => {
            let target_h = lower_expected(ctx, target, HirTy::Unknown);
            let i = *index as usize;
            match target_h.ty.clone() {
                HirTy::Tuple(ts) => match ts.get(i) {
                    Some(field_ty) => HirExpr {
                        ty: field_ty.clone(),
                        span,
                        kind: HirExprKind::TupleField {
                            target: Box::new(target_h),
                            index: *index,
                            field_ty: field_ty.clone(),
                        },
                    },
                    None => ctx.error_expr(
                        span,
                        format!("tuple index {index} out of range for a {}-tuple", ts.len()),
                    ),
                },
                // Spec 2.7.4: tuple-form structs (`struct Foo(i32);`)
                // expose their fields via the same `.N` syntax.
                HirTy::Struct(sid) => {
                    let def = ctx.struct_def(sid);
                    match def.fields.get(i) {
                        Some(f) if f.name == i.to_string() => HirExpr {
                            ty: f.ty.clone(),
                            span,
                            kind: HirExprKind::FieldRead {
                                target: Box::new(target_h),
                                struct_id: sid,
                                field_index: *index,
                                field_ty: f.ty.clone(),
                            },
                        },
                        _ => ctx.error_expr(
                            span,
                            format!("struct `{}` has no field `{index}`", def.name),
                        ),
                    }
                }
                HirTy::Unknown => target_h,
                other => ctx.error_expr(
                    span,
                    format!("no field `{index}` on type `{}`", ctx.ty_name(&other)),
                ),
            }
        }
        ExprKind::List(items) => {
            let expected_elem = match ctx.current_expected() {
                Some(HirTy::Array(e, _)) => Some((**e).clone()),
                _ => None,
            };
            let mut elem_ty = expected_elem.clone();
            let mut lowered: Vec<HirExpr> = Vec::with_capacity(items.len());
            for (i, e) in items.iter().enumerate() {
                let v = lower_expected(ctx, e, elem_ty.clone().unwrap_or(HirTy::Unknown));
                let v = match &elem_ty {
                    Some(t) => coerce(ctx, t, v, &|| format!("array element {i}")),
                    None => {
                        elem_ty = Some(v.ty.clone());
                        v
                    }
                };
                lowered.push(v);
            }
            let Some(elem_ty) = elem_ty else {
                return ctx.error_expr(
                    span,
                    "cannot infer the element type of an empty array literal — annotate \
                     the binding (`let a: [i32; 0] = [];`)"
                        .to_owned(),
                );
            };
            let len = u32::try_from(lowered.len()).expect("array literal length overflow");
            HirExpr {
                ty: HirTy::Array(Box::new(elem_ty.clone()), len),
                span,
                kind: HirExprKind::ArrayInit { elem_ty, elements: lowered },
            }
        }
        ExprKind::Index(arr, idx) => {
            let arr_h = lower_expected(ctx, arr, HirTy::Unknown);
            let idx_h = lower_expected(ctx, idx, HirTy::Unknown);
            check_index_ty(ctx, &idx_h);
            let elem_ty = match &arr_h.ty {
                HirTy::Array(t, _) => (**t).clone(),
                HirTy::Unknown => return arr_h,
                other => {
                    return ctx.error_expr(
                        span,
                        format!("cannot index into a value of type `{}`", ctx.ty_name(other)),
                    );
                }
            };
            HirExpr {
                ty: elem_ty.clone(),
                span,
                kind: HirExprKind::ArrayIndex {
                    array: Box::new(arr_h),
                    index: Box::new(idx_h),
                    elem_ty,
                },
            }
        }
        ExprKind::Loop { label, body } => {
            ctx.breakables.push((label.clone(), true));
            let body_h = lower_loop_body(ctx, body);
            ctx.breakables.pop();
            // Pick the first `break <value>` we can see in the body.
            let result_ty = first_break_value_ty(&body_h, label.as_deref()).unwrap_or(HirTy::Unit);
            HirExpr {
                kind: HirExprKind::Loop {
                    label: label.clone(),
                    body: Box::new(body_h),
                    result_ty: result_ty.clone(),
                },
                ty: result_ty,
                span,
            }
        }
        ExprKind::Closure { captures, params, ret_ty, body, is_async, is_generator } => {
            // Spec 4.6.2: `[ref x]` capture-list. Only value capture
            // (snapshot at creation) is modelled; refuse ref captures so
            // mutation isn't silently lost.
            if captures.iter().any(|c| matches!(c, rokc_ast::CaptureSpec::Ref(_))) {
                return ctx.error_expr(
                    span,
                    "`[ref x]` capture is not yet implemented; closures currently \
                     only support value capture (spec 4.6.2)"
                        .to_owned(),
                );
            }
            if *is_async || *is_generator {
                return unsupported(ctx, "an async / generator closure");
            }
            lower_closure_expr(ctx, params, ret_ty.as_ref(), body, span)
        }
        ExprKind::QuestionDot(receiver, tail) => {
            let recv_h = lower_expected(ctx, receiver, HirTy::Unknown);
            desugar_question_dot(ctx, recv_h, tail, span)
        }
        ExprKind::TryQ(inner) => {
            let inner_h = lower_expected(ctx, inner, HirTy::Unknown);
            desugar_try_q(ctx, inner_h, span)
        }
        ExprKind::NullishCoalesce(lhs, rhs) => {
            let lhs_h = lower_expected(ctx, lhs, HirTy::Unknown);
            desugar_nullish_coalesce(ctx, lhs_h, rhs, span)
        }
        ExprKind::Cast(operand, ty) => {
            let operand_h = lower_expected(ctx, operand, HirTy::Unknown);
            // Spec 2.10.5: monomorphized bodies need `as T` to substitute
            // the concrete type for the type-param (`resolve_ast_ty`).
            let to_ty = ctx.resolve_ast_ty(ty);
            let from_ty = operand_h.ty.clone();
            let castable = |t: &HirTy| matches!(t, HirTy::Prim(p) if p.is_int() || p.is_float() || matches!(p, PrimTy::Bool | PrimTy::CChar | PrimTy::Char));
            if !(from_ty == to_ty
                || matches!(from_ty, HirTy::Unknown)
                || matches!(to_ty, HirTy::Unknown)
                || (castable(&from_ty) && castable(&to_ty)))
            {
                return ctx.error_expr(
                    span,
                    format!(
                        "cannot cast `{}` as `{}` (only numeric / bool / char casts)",
                        ctx.ty_name(&from_ty),
                        ctx.ty_name(&to_ty)
                    ),
                );
            }
            HirExpr {
                kind: HirExprKind::Cast {
                    operand: Box::new(operand_h),
                    from_ty,
                    to_ty: to_ty.clone(),
                },
                ty: to_ty,
                span,
            }
        }
        // Stage-1 await: drop straight through to the inner expression.
        // The async runtime (`rok_task_*`) is all nullptr stubs; when the
        // scheduler lands, this arm becomes a real suspend point.
        ExprKind::Await(inner) => lower_expr(ctx, inner),
        // Spec 4.11: generator `yield N`. Coroutine runtime is a nullptr
        // stub at stage-1, so refuse explicitly rather than miscompile.
        ExprKind::Yield(_) => ctx.error_expr(
            span,
            "`yield` is not yet implemented; generator coroutines require a scheduler \
             that doesn't exist in stage-1 (spec 4.11)"
                .to_owned(),
        ),
        ExprKind::Range { .. } => {
            unsupported(ctx, "a range value outside a `for` loop header (`for i in a..b`)")
        }
        ExprKind::Dict(_) => unsupported(ctx, "a dict literal"),
        ExprKind::Set(_) => unsupported(ctx, "a set literal"),
        ExprKind::Is(..) => unsupported(ctx, "the `is` operator"),
        ExprKind::Slice { .. } => unsupported(ctx, "slicing (`a[i:j]`)"),
        ExprKind::LetElse { .. } => unsupported(ctx, "`let ... else` in expression position"),
        ExprKind::AsyncBlock(_) | ExprKind::YieldBlock(_) | ExprKind::AsyncYieldBlock(_) => {
            unsupported(ctx, "an async / generator block")
        }
        ExprKind::Spread(_) => unsupported(ctx, "a spread expression here"),
        ExprKind::Discard(_) => unsupported(ctx, "a discard expression"),
    }
}

/// `if` / `while` conditions are `bool`.
fn lower_cond(ctx: &mut LowerCtx<'_>, cond: &Expr) -> HirExpr {
    let c = lower_expected(ctx, cond, HirTy::Prim(PrimTy::Bool));
    coerce(ctx, &HirTy::Prim(PrimTy::Bool), c, &|| "the condition".to_owned())
}

/// Loop bodies yield no value (expected `()`).
fn lower_loop_body(ctx: &mut LowerCtx<'_>, body: &Block) -> HirBlock {
    ctx.push_expected(HirTy::Unit);
    let b = lower_block(ctx, body);
    ctx.pop_expected();
    b
}

/// Lift a closure into an anonymous top-level function and return a
/// closure value. Captures named outer locals by value (snapshot at
/// creation time). Non-capturing closures stay as plain function
/// pointers so existing `fn(...)` types keep working.
fn lower_closure_expr(
    ctx: &mut LowerCtx<'_>,
    params: &[Param],
    ret_ty: Option<&Ty>,
    body: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // Names referenced but not bound inside the closure (exhaustive AST
    // walk), filtered to those that resolve to outer locals.
    let captures: Vec<(String, LocalId, HirTy)> = crate::walk::free_names(params, body)
        .into_iter()
        .filter_map(|name| {
            let local = ctx.lookup(&name)?;
            Some((name, local, ctx.local_ty(local)))
        })
        .collect();

    let closure_id = FunctionId(ctx.env.sink.next_id.get());
    ctx.env.sink.next_id.set(closure_id.0 + 1);

    // Spec 4.5/4.8: in a context expecting a function type (e.g. an
    // argument to a `fn(i32) -> i32` parameter), unannotated params and
    // the return type come from the expected signature.
    let (expected_param_tys, expected_ret): (Option<Vec<HirTy>>, Option<HirTy>) =
        match ctx.current_expected() {
            Some(HirTy::Fn(args, ret) | HirTy::Closure { args, ret, .. }) => {
                (Some(args.clone()), Some((**ret).clone()))
            }
            _ => (None, None),
        };
    let declared_ret = ret_ty.map(|t| ctx.resolve_ast_ty(t));

    let mut cl_ctx = LowerCtx::new(ctx.env, ctx.ty_subst, ctx.self_ty.clone());
    cl_ctx.current_module = ctx.current_module.clone();
    cl_ctx.local_uses = ctx.local_uses.clone();

    // Closures with captures take an extra `env` parameter (a tuple of
    // captured values). The env param is declared first so its LocalId
    // is stable; closure params follow.
    let env_ty = (!captures.is_empty())
        .then(|| HirTy::Tuple(captures.iter().map(|(_, _, t)| t.clone()).collect()));
    let mut hir_params: Vec<HirParam> = Vec::with_capacity(params.len() + 1);
    let mut prelude: Vec<HirStmt> = Vec::new();
    if let Some(et) = &env_ty {
        let env_local = cl_ctx.declare(Some("__env".to_owned()), et.clone());
        hir_params.push(HirParam {
            name: "__env".to_owned(),
            local: env_local,
            ty: et.clone(),
            by_ref: false,
        });
        // Each captured name becomes a local inside the body initialised
        // from the corresponding env tuple field.
        for (i, (cap_name, _, cap_ty)) in captures.iter().enumerate() {
            let inner_local = cl_ctx.declare(Some(cap_name.clone()), cap_ty.clone());
            prelude.push(HirStmt::Let {
                local: inner_local,
                init: HirExpr {
                    kind: HirExprKind::TupleField {
                        target: Box::new(HirExpr {
                            kind: HirExprKind::Local(env_local),
                            ty: et.clone(),
                            span,
                        }),
                        index: u32::try_from(i).expect("capture index overflow"),
                        field_ty: cap_ty.clone(),
                    },
                    ty: cap_ty.clone(),
                    span,
                },
            });
        }
    }

    let mut user_arg_tys: Vec<HirTy> = Vec::with_capacity(params.len());
    for (pi, p) in params.iter().enumerate() {
        let ty = match &p.ty {
            Some(t) => ctx.resolve_ast_ty(t),
            None => match expected_param_tys.as_ref().and_then(|v| v.get(pi)) {
                Some(t) if *t != HirTy::Unknown => t.clone(),
                _ => {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "cannot infer the type of closure parameter `{}` — annotate \
                             it (`|{}: i32| ...`)",
                            p.name, p.name
                        ),
                    );
                    HirTy::Unknown
                }
            },
        };
        let local = cl_ctx.declare(Some(p.name.clone()), ty.clone());
        hir_params.push(HirParam { name: p.name.clone(), local, ty: ty.clone(), by_ref: p.by_ref });
        user_arg_tys.push(ty);
    }

    // `return` inside the closure targets the closure: its declared (or
    // expected) return type, else the first `return` value's type.
    let fixed_ret = declared_ret.or(expected_ret.filter(|t| *t != HirTy::Unknown));
    cl_ctx.fn_ret_ty = fixed_ret.clone().unwrap_or(HirTy::Unknown);
    cl_ctx.infer_ret = fixed_ret.is_none();
    let ret_hint = cl_ctx.fn_ret_ty.clone();
    let body_h = lower_expected(&mut cl_ctx, body, ret_hint);
    let diverges = hir_expr_diverges(&body_h);
    let final_ret_ty = match (fixed_ret, cl_ctx.fn_ret_ty.clone()) {
        (Some(t), _) => t,
        // A `return` fixed the type; a value-producing body must agree.
        (None, HirTy::Unknown) => body_h.ty.clone(),
        (None, t) => t,
    };
    let body_h = if diverges || (body_h.ty == HirTy::Unit && final_ret_ty == HirTy::Unit) {
        body_h
    } else {
        coerce(&cl_ctx, &final_ret_ty, body_h, &|| "the closure body".to_owned())
    };

    let body_block = HirBlock { stmts: prelude, trailing: Some(body_h), label: None };
    let cl_fn = HirFunction {
        id: closure_id,
        def_id: None,
        name: format!("__closure_{}", closure_id.0),
        params: hir_params,
        locals: cl_ctx.into_locals(),
        ret_ty: final_ret_ty.clone(),
        body: Some(body_block),
        is_async: false,
        is_generator: false,
        span,
    };
    ctx.env.sink.extras.borrow_mut().push(cl_fn);

    let Some(env_ty_v) = env_ty else {
        return HirExpr {
            kind: HirExprKind::FnRef(closure_id),
            ty: HirTy::Fn(user_arg_tys, Box::new(final_ret_ty)),
            span,
        };
    };
    // Materialize the env value at the creation site: a tuple of the
    // current outer locals' values, snapshotted by-value.
    let env_value = HirExpr {
        kind: HirExprKind::Tuple {
            fields: captures
                .iter()
                .map(|(_, outer_local, ty)| HirExpr {
                    kind: HirExprKind::Local(*outer_local),
                    ty: ty.clone(),
                    span,
                })
                .collect(),
        },
        ty: env_ty_v.clone(),
        span,
    };
    HirExpr {
        kind: HirExprKind::ClosureValue {
            fn_id: closure_id,
            env: Box::new(env_value),
            arg_tys: user_arg_tys.clone(),
            ret_ty: final_ret_ty.clone(),
            env_ty: env_ty_v.clone(),
        },
        ty: HirTy::Closure {
            args: user_arg_tys,
            ret: Box::new(final_ret_ty),
            env: Box::new(env_ty_v),
        },
        span,
    }
}

/// `T | none`-shaped sum: index of `none` plus the non-none variants.
fn optional_parts(ty: &HirTy) -> Option<(usize, Vec<(usize, HirTy)>)> {
    let HirTy::Sum(variants) = ty else { return None };
    let none_idx = variants.iter().position(is_none_ty)?;
    let some: Vec<(usize, HirTy)> = variants
        .iter()
        .enumerate()
        .filter(|(_, v)| !is_none_ty(v))
        .map(|(i, v)| (i, v.clone()))
        .collect();
    Some((none_idx, some))
}

/// The value type left after removing `none`: the single payload, or a
/// sum of the remaining variants.
fn without_none(some: &[(usize, HirTy)]) -> HirTy {
    match some {
        [(_, t)] => t.clone(),
        many => HirTy::Sum(many.iter().map(|(_, t)| t.clone()).collect()),
    }
}

/// `match scrut { v: T_k => wrap(v), ..., none => none_body }` with one
/// arm per non-none variant; each payload is re-wrapped into `result_ty`.
fn optional_match(
    ctx: &mut LowerCtx<'_>,
    scrut: HirExpr,
    none_idx: usize,
    some: &[(usize, HirTy)],
    some_body: &mut dyn FnMut(&mut LowerCtx<'_>, HirExpr) -> HirExpr,
    none_body: HirExpr,
    result_ty: HirTy,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let sum_ty = scrut.ty.clone();
    let mut arms = Vec::with_capacity(some.len() + 1);
    for (idx, payload_ty) in some {
        let bind_local = ctx.declare(None, payload_ty.clone());
        let value = HirExpr { kind: HirExprKind::Local(bind_local), ty: payload_ty.clone(), span };
        arms.push(HirMatchArm {
            pat: HirPattern::SumVariant {
                sum_ty: sum_ty.clone(),
                variant_index: u32::try_from(*idx).expect("variant overflow"),
                binder: Some(bind_local),
                payload_ty: Some(payload_ty.clone()),
            },
            guard: None,
            body: some_body(ctx, value),
        });
    }
    arms.push(HirMatchArm {
        pat: HirPattern::SumVariant {
            sum_ty,
            variant_index: u32::try_from(none_idx).expect("variant overflow"),
            binder: None,
            payload_ty: None,
        },
        guard: None,
        body: none_body,
    });
    HirExpr {
        kind: HirExprKind::Match { scrutinee: Box::new(scrut), arms },
        ty: result_ty,
        span,
    }
}

fn sum_none(sum_ty: &HirTy, span: rokc_diagnostic::Span) -> HirExpr {
    wrap_into_sum(sum_ty, HirExpr { kind: HirExprKind::Const(ConstVal::None), ty: none_ty(), span })
}

/// Desugar `x?.tail` to `match x { v: T => v.tail, none => none }`. The
/// scrutinee must be `T | none` with one payload variant; the result is
/// `tail_ty | none` (or the tail's own optional type — spec 3.8.2: `?.`
/// chains compose monadically).
fn desugar_question_dot(
    ctx: &mut LowerCtx<'_>,
    recv: HirExpr,
    tail: &rokc_ast::AccessTail,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    if recv.ty == HirTy::Unknown {
        return recv;
    }
    let Some((none_idx, some)) = optional_parts(&recv.ty) else {
        // Non-optional receiver — a plain access.
        return apply_access_tail(ctx, recv, tail, span);
    };
    if some.len() != 1 {
        return ctx.error_expr(
            span,
            format!(
                "`?.` needs a `T | none` receiver with a single payload type, found `{}`",
                ctx.ty_name(&recv.ty)
            ),
        );
    }
    // Lower the tail once against a placeholder local to learn its type.
    let payload_ty = some[0].1.clone();
    let bind_local = ctx.declare(None, payload_ty.clone());
    let unwrapped = HirExpr { kind: HirExprKind::Local(bind_local), ty: payload_ty.clone(), span };
    let inner = apply_access_tail(ctx, unwrapped, tail, span);
    if inner.ty == HirTy::Unknown {
        return inner;
    }
    let inner_optional = optional_parts(&inner.ty).is_some();
    let result_ty = if inner_optional {
        inner.ty.clone()
    } else {
        HirTy::Sum(vec![inner.ty.clone(), none_ty()])
    };
    let some_body = if inner_optional { inner } else { wrap_into_sum(&result_ty, inner) };
    let none_body = sum_none(&result_ty, span);
    HirExpr {
        kind: HirExprKind::Match {
            scrutinee: Box::new(recv.clone()),
            arms: vec![
                HirMatchArm {
                    pat: HirPattern::SumVariant {
                        sum_ty: recv.ty.clone(),
                        variant_index: u32::try_from(some[0].0).expect("variant overflow"),
                        binder: Some(bind_local),
                        payload_ty: Some(payload_ty),
                    },
                    guard: None,
                    body: some_body,
                },
                HirMatchArm {
                    pat: HirPattern::SumVariant {
                        sum_ty: recv.ty.clone(),
                        variant_index: u32::try_from(none_idx).expect("variant overflow"),
                        binder: None,
                        payload_ty: None,
                    },
                    guard: None,
                    body: none_body,
                },
            ],
        },
        ty: result_ty,
        span,
    }
}

/// Apply an `AccessTail` to an already-lowered HIR receiver. Supports
/// the same forms `?.` does: field, tuple field, and method call.
fn apply_access_tail(
    ctx: &mut LowerCtx<'_>,
    recv: HirExpr,
    tail: &rokc_ast::AccessTail,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    match tail {
        rokc_ast::AccessTail::Field(name) => field_access(ctx, recv, name, span),
        rokc_ast::AccessTail::TupleField(idx) => match recv.ty.clone() {
            HirTy::Tuple(parts) => match parts.get(*idx as usize) {
                Some(field_ty) => HirExpr {
                    kind: HirExprKind::TupleField {
                        target: Box::new(recv),
                        index: *idx,
                        field_ty: field_ty.clone(),
                    },
                    ty: field_ty.clone(),
                    span,
                },
                None => ctx.error_expr(
                    span,
                    format!("tuple index {idx} out of range for a {}-tuple", parts.len()),
                ),
            },
            other => {
                ctx.error_expr(span, format!("no field `{idx}` on type `{}`", ctx.ty_name(&other)))
            }
        },
        rokc_ast::AccessTail::Method { method, args, .. } => {
            method_call_on(ctx, recv, method, args, span)
        }
        rokc_ast::AccessTail::Index(_) => ctx.error_expr(
            span,
            "`?.[index]` is not supported yet (stage-1 limitation)".to_owned(),
        ),
    }
}

/// Desugar `expr?` (spec 3.14): unwrap the payload of a `T | none` value
/// or propagate `none` out of the enclosing function, which must itself
/// return a sum containing `none`. With several payload variants the
/// value keeps the remaining sum (`A | B | none` → `A | B`).
fn desugar_try_q(ctx: &mut LowerCtx<'_>, inner: HirExpr, span: rokc_diagnostic::Span) -> HirExpr {
    if inner.ty == HirTy::Unknown {
        return inner;
    }
    let Some((none_idx, some)) = optional_parts(&inner.ty) else {
        return ctx.error_expr(
            span,
            format!(
                "`?` needs an optional value (`T | none`), found `{}`",
                ctx.ty_name(&inner.ty)
            ),
        );
    };
    let ret_ty = ctx.fn_ret_ty.clone();
    if optional_parts(&ret_ty).is_none() {
        return ctx.error_expr(
            span,
            format!(
                "`?` propagates `none`, but the enclosing function returns `{}` — its \
                 return type must include `none`",
                ctx.ty_name(&ret_ty)
            ),
        );
    }
    let value_ty = without_none(&some);
    let none_body = HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock {
            stmts: vec![HirStmt::Return(Some(sum_none(&ret_ty, span)))],
            trailing: None,
            label: None,
        })),
        ty: value_ty.clone(),
        span,
    };
    let vt = value_ty.clone();
    optional_match(
        ctx,
        inner,
        none_idx,
        &some,
        &mut |_, v| wrap_into_sum(&vt, v),
        none_body,
        value_ty,
        span,
    )
}

/// Desugar `lhs ?? rhs` to `match lhs { v: T => v, none => rhs }`; the
/// default must have the payload type.
fn desugar_nullish_coalesce(
    ctx: &mut LowerCtx<'_>,
    lhs: HirExpr,
    rhs: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let Some((none_idx, some)) = optional_parts(&lhs.ty) else {
        let rhs_h = lower_expected(ctx, rhs, HirTy::Unknown);
        if lhs.ty == HirTy::Unknown || rhs_h.ty == HirTy::Unknown {
            return poison(span);
        }
        return ctx.error_expr(
            span,
            format!(
                "`??` needs an optional left operand (`T | none`), found `{}`",
                ctx.ty_name(&lhs.ty)
            ),
        );
    };
    let value_ty = without_none(&some);
    let rhs_h = lower_expected(ctx, rhs, value_ty.clone());
    let rhs_h = coerce(ctx, &value_ty, rhs_h, &|| "the `??` default".to_owned());
    let vt = value_ty.clone();
    optional_match(
        ctx,
        lhs,
        none_idx,
        &some,
        &mut |_, v| wrap_into_sum(&vt, v),
        rhs_h,
        value_ty,
        span,
    )
}

/// Walk one loop's body looking for the first `break value;` whose
/// label targets this loop. Skips nested loops (they own their breaks).
fn first_break_value_ty(b: &HirBlock, label: Option<&str>) -> Option<HirTy> {
    fn walk_block(b: &HirBlock, label: Option<&str>) -> Option<HirTy> {
        for s in &b.stmts {
            if let Some(t) = walk_stmt(s, label) {
                return Some(t);
            }
        }
        b.trailing.as_ref().and_then(|t| walk_expr(t, label))
    }

    fn walk_stmt(s: &HirStmt, label: Option<&str>) -> Option<HirTy> {
        match s {
            HirStmt::Break { label: bl, value } => {
                // Exact match: an unlabeled break belongs only to an
                // unlabeled outer; `break 'L` belongs only to the loop
                // labeled `'L`.
                if bl.as_deref() == label {
                    value.as_ref().map(|v| v.ty.clone())
                } else {
                    None
                }
            }
            HirStmt::Let { init, .. } => walk_expr(init, label),
            HirStmt::Assign { value, .. } => walk_expr(value, label),
            HirStmt::Expr(e) | HirStmt::Return(Some(e)) => walk_expr(e, label),
            _ => None,
        }
    }

    fn walk_expr(e: &HirExpr, label: Option<&str>) -> Option<HirTy> {
        match &e.kind {
            HirExprKind::Block(b) => walk_block(b, label),
            HirExprKind::If { cond, then_block, else_branch } => {
                walk_expr(cond, label)
                    .or_else(|| walk_block(then_block, label))
                    .or_else(|| else_branch.as_deref().and_then(|e| walk_expr(e, label)))
            }
            HirExprKind::PrimBinOp { lhs, rhs, .. } => {
                walk_expr(lhs, label).or_else(|| walk_expr(rhs, label))
            }
            HirExprKind::PrimUnaryOp { operand, .. } => walk_expr(operand, label),
            HirExprKind::Call { args, .. } => args.iter().find_map(|a| walk_expr(a, label)),
            // For an unlabeled outer, nested loops own all their breaks —
            // skip. For a labeled outer, recurse so a `break 'outer …`
            // inside a nested loop is reachable, but stop at any inner
            // loop that shadows the label.
            HirExprKind::While { label: inner, body, .. } => {
                if label.is_some() && inner.as_deref() != label {
                    walk_block(body, label)
                } else {
                    None
                }
            }
            HirExprKind::Loop { label: inner, body, .. } => {
                if label.is_some() && inner.as_deref() != label {
                    walk_block(body, label)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    walk_block(b, label)
}

/// Outcome of resolving `[..enum path.., Variant]`.
enum EnumRes {
    /// The prefix doesn't name an enum.
    NotEnum,
    Found(EnumId, usize),
    /// An enum was named but the variant / instantiation is wrong
    /// (already reported).
    Error,
}

fn enum_base_name(name: &str) -> &str {
    name.split("__").next().unwrap_or(name)
}

/// Resolve an enum variant path. For a generic enum the instantiation
/// comes from `hint` (expected / scrutinee type), else from the single
/// instantiation whose variant payload fits `arg_tys`.
fn resolve_enum_variant(
    ctx: &LowerCtx<'_>,
    segs: &[&str],
    hint: Option<&HirTy>,
    arg_tys: Option<&[HirTy]>,
) -> EnumRes {
    let Some((full, vname)) = ctx.enum_path(segs) else { return EnumRes::NotEnum };
    let variant_of = |eid: EnumId| {
        ctx.env.enums[eid.0 as usize].variants.iter().position(|v| v.name == vname)
    };
    let eid = if let Some(HirTy::Enum(h)) =
        hint.filter(|h| matches!(h, HirTy::Enum(e) if enum_base_name(&ctx.env.enums[e.0 as usize].name) == full))
    {
        *h
    } else if let Some(&eid) = ctx.env.enum_table.get(&full) {
        eid
    } else {
        let insts = LowerCtx::instantiations(&ctx.env.enum_table, &full);
        if insts.is_empty() {
            return EnumRes::NotEnum;
        }
        let fits: Vec<EnumId> = insts
            .into_iter()
            .filter(|&eid| {
                let Some(vi) = variant_of(eid) else { return false };
                let v = &ctx.env.enums[eid.0 as usize].variants[vi];
                match (arg_tys, &v.payload_ty) {
                    (None, None) => true,
                    (Some(args), Some(p)) => {
                        let parts: Vec<HirTy> = match (v.arity, p) {
                            (1, t) => vec![t.clone()],
                            (_, HirTy::Tuple(ps)) => ps.clone(),
                            (_, t) => vec![t.clone()],
                        };
                        parts.len() == args.len()
                            && parts.iter().zip(args).all(|(p, a)| ty_compatible(p, a) && *a != HirTy::Unknown)
                    }
                    _ => false,
                }
            })
            .collect();
        match fits.as_slice() {
            [one] => *one,
            [] => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!("no instantiation of generic enum `{full}` matches `{}`", segs.join("::")),
                );
                return EnumRes::Error;
            }
            _ => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "cannot infer the type arguments of `{full}` for `{}` — annotate the \
                         binding with the concrete type",
                        segs.join("::")
                    ),
                );
                return EnumRes::Error;
            }
        }
    };
    match variant_of(eid) {
        Some(i) => EnumRes::Found(eid, i),
        None => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("enum `{full}` has no variant `{vname}`"),
            );
            EnumRes::Error
        }
    }
}

/// Payload slot types of a variant, one per constructor argument.
fn variant_arg_tys(v: &HirEnumVariant) -> Vec<HirTy> {
    match (&v.payload_ty, v.arity) {
        (None, _) => Vec::new(),
        (Some(t), 1) => vec![t.clone()],
        (Some(HirTy::Tuple(ps)), _) => ps.clone(),
        (Some(t), _) => vec![t.clone()],
    }
}

// `Foo { field: value, ... }` — fields are placed in declaration order.
fn lower_struct_init(
    ctx: &mut LowerCtx<'_>,
    path: &AstPath,
    fields: &[(String, Expr)],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
    {
        let mut seen = std::collections::HashSet::new();
        for (n, _) in fields {
            if !seen.insert(n.as_str()) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!("field `{n}` specified more than once in `{}` literal", segs.join("::")),
                );
            }
        }
    }
    // `EnumName::Variant { x: ..., y: ... }` — enum named-form variant
    // initialiser (spec 2.4). Pack fields into the variant's tuple
    // payload according to declaration order.
    let hint = ctx.current_expected().cloned();
    match resolve_enum_variant(ctx, &segs, hint.as_ref(), None) {
        EnumRes::Error => return poison(span),
        EnumRes::Found(enum_id, idx) => {
            let variant = ctx.env.enums[enum_id.0 as usize].variants[idx].clone();
            if variant.named_fields.is_empty() {
                return ctx.error_expr(
                    span,
                    format!("`{}` is not a struct-like enum variant", segs.join("::")),
                );
            }
            let field_tys = variant_arg_tys(&variant);
            let mut payload_args: Vec<Option<HirExpr>> = vec![None; variant.named_fields.len()];
            for (n, e) in fields {
                match variant.named_fields.iter().position(|f| f == n) {
                    Some(i) => {
                        let v = lower_expected(ctx, e, field_tys[i].clone());
                        payload_args[i] =
                            Some(coerce(ctx, &field_tys[i], v, &|| format!("field `{n}`")));
                    }
                    None => {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!("enum variant `{}` has no field `{n}` (spec 2.4)", segs.join("::")),
                        );
                    }
                }
            }
            let mut args = Vec::with_capacity(payload_args.len());
            for (i, a) in payload_args.into_iter().enumerate() {
                match a {
                    Some(a) => args.push(a),
                    None => {
                        ctx.emit_error(
                            rokc_diagnostic::ErrorKind::Type,
                            format!(
                                "enum variant `{}` is missing field `{}` (spec 2.4)",
                                segs.join("::"),
                                variant.named_fields[i]
                            ),
                        );
                        args.push(poison(span));
                    }
                }
            }
            return HirExpr {
                kind: HirExprKind::EnumVariantInit {
                    enum_id,
                    variant_index: u32::try_from(idx).expect("variant overflow"),
                    args,
                },
                ty: HirTy::Enum(enum_id),
                span,
            };
        }
        EnumRes::NotEnum => {}
    }

    let Some(full) = ctx.canon_type(&segs) else {
        for (_, e) in fields {
            lower_expected(ctx, e, HirTy::Unknown);
        }
        return ctx.error_expr(span, format!("cannot find struct `{}` in this scope", segs.join("::")));
    };
    // Values lowered before the struct is known (generic inference);
    // reused below so each field expression is evaluated exactly once.
    let mut pre: Vec<Option<HirExpr>> = vec![None; fields.len()];
    let explicit_generics = path.segments.last().is_some_and(|s| !s.generics.is_empty());
    let struct_id = if explicit_generics {
        let synth = Ty { kind: AstTyKind::Path(path.clone()), span: path.span };
        match ctx.resolve_ast_ty(&synth) {
            HirTy::Struct(id) => id,
            _ => {
                return ctx.error_expr(
                    span,
                    format!("cannot instantiate `{}` with these type arguments", segs.join("::")),
                );
            }
        }
    } else if let Some(id) = ctx.lookup_struct(&full) {
        id
    } else if let Some(def) = ctx.env.generic_structs.get(&full).copied() {
        // `Box { v: 5 }`: the expected type picks the instantiation;
        // otherwise infer the type arguments from the field values.
        match &hint {
            Some(HirTy::Struct(h))
                if enum_base_name(&ctx.struct_def(*h).name) == full
                    && !ctx.struct_def(*h).generic_args.is_empty() =>
            {
                *h
            }
            _ => {
                let AstStructKind::Named(decl_fields) = &def.kind else {
                    return ctx.error_expr(span, format!("`{full}` is not a struct with named fields"));
                };
                let generic_names: std::collections::HashSet<String> = def
                    .generics
                    .params
                    .iter()
                    .filter_map(|gp| match gp {
                        rokc_ast::GenericParam::Type { name, .. } => Some(name.clone()),
                        rokc_ast::GenericParam::Const { .. } => None,
                    })
                    .collect();
                let mut subst: HashMap<String, HirTy> = HashMap::new();
                for (i, (n, e)) in fields.iter().enumerate() {
                    let v = lower_expected(ctx, e, HirTy::Unknown);
                    if let Some(df) = decl_fields.iter().find(|f| f.name == *n) {
                        unify_param_ty_with(&df.ty, &v.ty, &generic_names, &mut subst, ctx);
                    }
                    pre[i] = Some(v);
                }
                let mut args = Vec::new();
                for gp in &def.generics.params {
                    if let rokc_ast::GenericParam::Type { name, default, .. } = gp {
                        match subst.get(name).cloned().or_else(|| {
                            default.as_ref().map(|d| ctx.resolve_ast_ty(d))
                        }) {
                            Some(t) if t != HirTy::Unknown => args.push(t),
                            Some(_) => return poison(span),
                            None => {
                                return ctx.error_expr(
                                    span,
                                    format!(
                                        "cannot infer type parameter `{name}` of `{full}` — \
                                         write `{}<...> {{ ... }}`",
                                        segs.join("::")
                                    ),
                                );
                            }
                        }
                    }
                }
                match ctx.instantiate_struct(&full, args) {
                    Some(id) => id,
                    None => return poison(span),
                }
            }
        }
    } else {
        return ctx.error_expr(span, format!("`{full}` is not a struct"));
    };
    let def = ctx.struct_def(struct_id);
    let ty_display = ctx.ty_name(&HirTy::Struct(struct_id));
    // Spec 2.x / i-want 322: `union { ... }` initialiser. Exactly one
    // declared field gets its value cast/bitcast into the synthetic
    // `__data` storage slot.
    if let Some(union_kind) = def.union_kind.clone() {
        if fields.len() != 1 {
            return ctx.error_expr(
                span,
                format!(
                    "union `{}` initialiser must list exactly one field (spec 2.x — got {})",
                    def.name,
                    fields.len()
                ),
            );
        }
        let (fname, value) = &fields[0];
        let Some(field_ty) =
            union_kind.aliases.iter().find(|(n, _)| n == fname).map(|(_, t)| t.clone())
        else {
            return ctx.error_expr(span, format!("union `{}` has no field `{fname}` (spec 2.x)", def.name));
        };
        ctx.check_field_visible(struct_id, fname);
        let lowered = lower_expected(ctx, value, field_ty.clone());
        let lowered = coerce(ctx, &field_ty, lowered, &|| format!("field `{fname}`"));
        let storage_ty = def.fields[0].ty.clone();
        let casted = HirExpr {
            kind: HirExprKind::UnionWrite {
                struct_id,
                from_ty: lowered.ty.clone(),
                storage_ty: storage_ty.clone(),
                value: Box::new(lowered),
            },
            ty: storage_ty,
            span,
        };
        return HirExpr {
            kind: HirExprKind::StructInit { struct_id, fields: vec![casted] },
            ty: HirTy::Struct(struct_id),
            span,
        };
    }
    let mut ordered: Vec<Option<HirExpr>> = vec![None; def.fields.len()];
    for (i, (name, value)) in fields.iter().enumerate() {
        let Some(idx) = def.fields.iter().position(|f| f.name == *name) else {
            if pre[i].is_none() {
                lower_expected(ctx, value, HirTy::Unknown);
            }
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("struct `{ty_display}` has no field `{name}`"),
            );
            continue;
        };
        ctx.check_field_visible(struct_id, name);
        let target_ty = def.fields[idx].ty.clone();
        let lowered = match pre[i].take() {
            Some(v) => v,
            None => lower_expected(ctx, value, target_ty.clone()),
        };
        ordered[idx] = Some(coerce(ctx, &target_ty, lowered, &|| format!("field `{name}`")));
    }
    // Spec 2.x / i-want 942-950: missing fields fall back to their
    // declared default expression; no default → "missing field" error.
    let mut out = Vec::with_capacity(ordered.len());
    for (f, v) in def.fields.iter().zip(ordered) {
        match (v, &f.default) {
            (Some(v), _) => out.push(v),
            (None, Some(default_expr)) => {
                let lowered = lower_expected(ctx, default_expr, f.ty.clone());
                out.push(coerce(ctx, &f.ty, lowered, &|| format!("the default of field `{}`", f.name)));
            }
            (None, None) => {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "struct `{ty_display}` is missing field `{}` and no default is \
                         declared (spec 2.x / i-want 942-950)",
                        f.name
                    ),
                );
                out.push(poison(span));
            }
        }
    }
    HirExpr {
        kind: HirExprKind::StructInit { struct_id, fields: out },
        ty: HirTy::Struct(struct_id),
        span,
    }
}

// `expr.field` on a struct.
fn lower_field(ctx: &mut LowerCtx<'_>, target: &Expr, name: &str, span: rokc_diagnostic::Span) -> HirExpr {
    let target_h = lower_expected(ctx, target, HirTy::Unknown);
    field_access(ctx, target_h, name, span)
}

/// Read field `name` of an already-lowered struct / union value.
fn field_access(
    ctx: &mut LowerCtx<'_>,
    target_h: HirExpr,
    name: &str,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let struct_id = match &target_h.ty {
        HirTy::Struct(id) => *id,
        HirTy::Unknown => return target_h,
        other => {
            return ctx.error_expr(span, format!("no field `{name}` on type `{}`", ctx.ty_name(other)));
        }
    };
    let def = ctx.struct_def(struct_id);
    // Spec 2.x / i-want 322: union field read goes through `UnionRead`
    // so MIR/codegen can issue the right cast/bitcast against the
    // single `__data` storage slot.
    if let Some(union_kind) = def.union_kind.clone() {
        let storage_ty = def.fields[0].ty.clone();
        let Some(field_ty) = union_kind.aliases.iter().find(|(n, _)| n == name).map(|(_, t)| t.clone())
        else {
            return ctx.error_expr(span, format!("union `{}` has no field `{name}` (spec 2.x)", def.name));
        };
        ctx.check_field_visible(struct_id, name);
        return HirExpr {
            kind: HirExprKind::UnionRead {
                struct_id,
                target: Box::new(target_h),
                field_name: name.to_owned(),
                storage_ty,
                field_ty: field_ty.clone(),
            },
            ty: field_ty,
            span,
        };
    }
    let Some(idx) = def.fields.iter().position(|f| f.name == name) else {
        return ctx.error_expr(
            span,
            format!("struct `{}` has no field `{name}`", ctx.ty_name(&HirTy::Struct(struct_id))),
        );
    };
    ctx.check_field_visible(struct_id, name);
    let field_ty = def.fields[idx].ty.clone();
    HirExpr {
        kind: HirExprKind::FieldRead {
            target: Box::new(target_h),
            struct_id,
            field_index: u32::try_from(idx).expect("field index overflow"),
            field_ty: field_ty.clone(),
        },
        ty: field_ty,
        span,
    }
}

/// An unsuffixed numeric literal (optionally negated): its type comes
/// from context.
fn is_untyped_literal(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Literal(AstLit::Int(t)) => !has_int_suffix(t),
        ExprKind::Literal(AstLit::Float(t)) => !t.ends_with("f32") && !t.ends_with("f64"),
        ExprKind::OpPrefix { op, operand } if op == "-" => is_untyped_literal(operand),
        _ => false,
    }
}

/// Lower two sibling operands that must share a type: an untyped
/// literal on either side takes the other side's type. Evaluation stays
/// left-to-right except when the left side is a literal (no effects).
fn lower_sibling_pair(
    ctx: &mut LowerCtx<'_>,
    lhs: &Expr,
    rhs: &Expr,
    lhs_expected: HirTy,
) -> (HirExpr, HirExpr) {
    if is_untyped_literal(lhs) && !is_untyped_literal(rhs) {
        let r = lower_expected(ctx, rhs, lhs_expected);
        let l = lower_expected(ctx, lhs, r.ty.clone());
        (l, r)
    } else {
        let l = lower_expected(ctx, lhs, lhs_expected);
        let r = lower_expected(ctx, rhs, l.ty.clone());
        (l, r)
    }
}

fn hir_local(local: LocalId, ty: &HirTy, span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr { kind: HirExprKind::Local(local), ty: ty.clone(), span }
}

fn hir_int(value: i128, prim: PrimTy, span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr { kind: HirExprKind::Const(ConstVal::Int { value, ty: prim }), ty: HirTy::Prim(prim), span }
}

fn hir_binop(op: PrimOp, lhs: HirExpr, rhs: HirExpr, ty: HirTy, span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr { kind: HirExprKind::PrimBinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }, ty, span }
}

/// Bind an irrefutable `for` / destructuring pattern to `value`:
/// a name, `_`, or (nested) tuples of those.
fn bind_irrefutable(
    ctx: &mut LowerCtx<'_>,
    pat: &AstPattern,
    value: HirExpr,
    stmts: &mut Vec<HirStmt>,
) {
    let span = value.span;
    match (&pat.kind, value.ty.clone()) {
        (AstPatternKind::Wildcard, _) => {}
        (AstPatternKind::Binding { name, sub: None }, ty) => {
            if name == "_" {
                return;
            }
            let local = ctx.declare(Some(name.clone()), ty);
            stmts.push(HirStmt::Let { local, init: value });
        }
        (AstPatternKind::Tuple(pats), HirTy::Tuple(tys)) if pats.len() == tys.len() => {
            let tmp = ctx.declare(None, value.ty.clone());
            let tuple_ty = value.ty.clone();
            stmts.push(HirStmt::Let { local: tmp, init: value });
            for (i, (p, t)) in pats.iter().zip(tys).enumerate() {
                let read = HirExpr {
                    kind: HirExprKind::TupleField {
                        target: Box::new(hir_local(tmp, &tuple_ty, span)),
                        index: u32::try_from(i).expect("tuple index overflow"),
                        field_ty: t.clone(),
                    },
                    ty: t.clone(),
                    span,
                };
                bind_irrefutable(ctx, p, read, stmts);
            }
        }
        (_, HirTy::Unknown) => {}
        (_, ty) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!(
                    "this pattern can't destructure a value of type `{}` here — `for` \
                     bindings must be a name, `_`, or a tuple of those",
                    ctx.ty_name(&ty)
                ),
            );
        }
    }
}

/// `for pat in iter { body }` (spec 3.9). Supported iterables: an integer
/// range `a..b` / `a..=b` (bounds evaluated once) and any array value.
/// Everything else is rejected — never silently skipped.
///
/// Desugars to a block `{ <setup>; while <cond> { <step>; let pat = ..;
/// body } }` with the step before the body so `continue` can't skip it.
/// `label` goes on the synthesized `While` so `break 'outer` /
/// `continue 'outer` inside the body resolve correctly.
fn lower_for(
    ctx: &mut LowerCtx<'_>,
    label: &Option<String>,
    pat: &AstPattern,
    iter: &Expr,
    body: &Block,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let mut out: Vec<HirStmt> = Vec::new();
    ctx.push_scope();
    ctx.breakables.push((label.clone(), true));
    let while_expr = match &iter.kind {
        ExprKind::Range { start: Some(start_e), end: Some(end_e), inclusive } => {
            lower_for_range(ctx, label, pat, start_e, end_e, *inclusive, body, span, &mut out)
        }
        ExprKind::Range { .. } => Some(ctx.error_expr(
            span,
            "`for` over an unbounded range needs both bounds (`a..b`)".to_owned(),
        )),
        _ => {
            let iter_h = lower_expected(ctx, iter, HirTy::Unknown);
            match iter_h.ty.clone() {
                HirTy::Array(elem, len) => {
                    lower_for_array(ctx, label, pat, iter_h, (*elem).clone(), len, body, span, &mut out)
                }
                HirTy::Unknown => None,
                other => Some(ctx.error_expr(
                    span,
                    format!(
                        "cannot iterate over a value of type `{}` — `for` supports integer \
                         ranges (`a..b`) and arrays (stage-1 limitation)",
                        ctx.ty_name(&other)
                    ),
                )),
            }
        }
    };
    ctx.breakables.pop();
    ctx.pop_scope();
    match while_expr {
        Some(w) => out.push(HirStmt::Expr(w)),
        None => return poison(span),
    }
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock { stmts: out, trailing: None, label: None })),
        ty: HirTy::Unit,
        span,
    }
}

/// Integer range loop. Exclusive: `c < end`. Inclusive uses a `go` flag
/// so `a..=MAX` terminates instead of wrapping.
#[allow(clippy::too_many_arguments)]
fn lower_for_range(
    ctx: &mut LowerCtx<'_>,
    label: &Option<String>,
    pat: &AstPattern,
    start_e: &Expr,
    end_e: &Expr,
    inclusive: bool,
    body: &Block,
    span: rokc_diagnostic::Span,
    out: &mut Vec<HirStmt>,
) -> Option<HirExpr> {
    let (start_h, end_h) = lower_sibling_pair(ctx, start_e, end_e, HirTy::Unknown);
    if start_h.ty == HirTy::Unknown || end_h.ty == HirTy::Unknown {
        return None;
    }
    let elem_ty = start_h.ty.clone();
    let prim = match &elem_ty {
        HirTy::Prim(p) if p.is_int() && start_h.ty == end_h.ty => *p,
        _ => {
            return Some(ctx.error_expr(
                span,
                format!(
                    "range bounds must be integers of the same type, found `{}` and `{}`",
                    ctx.ty_name(&start_h.ty),
                    ctx.ty_name(&end_h.ty)
                ),
            ));
        }
    };
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let counter = ctx.declare(None, elem_ty.clone());
    let end = ctx.declare(None, elem_ty.clone());
    out.push(HirStmt::Let { local: counter, init: start_h });
    out.push(HirStmt::Let { local: end, init: end_h });
    let c = || hir_local(counter, &elem_ty, span);
    let e = || hir_local(end, &elem_ty, span);
    let inc = |c: HirExpr| hir_binop(PrimOp::Add, c, hir_int(1, prim, span), elem_ty.clone(), span);

    let mut body_stmts: Vec<HirStmt> = Vec::new();
    let snap = ctx.declare(None, elem_ty.clone());
    body_stmts.push(HirStmt::Let { local: snap, init: c() });
    let cond = if inclusive {
        // go = start <= end; while go { snap = c; go = c < end; if go { c += 1 } ... }
        let go = ctx.declare(None, bool_ty.clone());
        out.push(HirStmt::Let { local: go, init: hir_binop(PrimOp::Le, c(), e(), bool_ty.clone(), span) });
        body_stmts.push(HirStmt::Assign {
            local: go,
            value: hir_binop(PrimOp::Lt, c(), e(), bool_ty.clone(), span),
        });
        body_stmts.push(HirStmt::Expr(HirExpr {
            kind: HirExprKind::If {
                cond: Box::new(hir_local(go, &bool_ty, span)),
                then_block: Box::new(HirBlock {
                    stmts: vec![HirStmt::Assign { local: counter, value: inc(c()) }],
                    trailing: None,
                    label: None,
                }),
                else_branch: None,
            },
            ty: HirTy::Unit,
            span,
        }));
        hir_local(go, &bool_ty, span)
    } else {
        body_stmts.push(HirStmt::Assign { local: counter, value: inc(c()) });
        hir_binop(PrimOp::Lt, c(), e(), bool_ty, span)
    };
    bind_irrefutable(ctx, pat, hir_local(snap, &elem_ty, span), &mut body_stmts);
    let lowered_body = lower_loop_body(ctx, body);
    body_stmts.push(HirStmt::Expr(HirExpr {
        kind: HirExprKind::Block(Box::new(lowered_body)),
        ty: HirTy::Unit,
        span,
    }));
    Some(HirExpr {
        ty: HirTy::Unit,
        span,
        kind: HirExprKind::While {
            label: label.clone(),
            cond: Box::new(cond),
            body: Box::new(HirBlock { stmts: body_stmts, trailing: None, label: None }),
        },
    })
}

/// `for x in arr` over a `[T; N]` value: the array is bound to a local
/// once, then indexed by a counter.
#[allow(clippy::too_many_arguments)]
fn lower_for_array(
    ctx: &mut LowerCtx<'_>,
    label: &Option<String>,
    pat: &AstPattern,
    iter_h: HirExpr,
    elem_ty: HirTy,
    len: u32,
    body: &Block,
    span: rokc_diagnostic::Span,
    out: &mut Vec<HirStmt>,
) -> Option<HirExpr> {
    let arr_ty = iter_h.ty.clone();
    let arr_local = match iter_h.kind {
        HirExprKind::Local(l) => l,
        _ => {
            let l = ctx.declare(None, arr_ty.clone());
            out.push(HirStmt::Let { local: l, init: iter_h });
            l
        }
    };
    let idx_prim = PrimTy::I32;
    let idx_ty = HirTy::Prim(idx_prim);
    let counter = ctx.declare(None, idx_ty.clone());
    out.push(HirStmt::Let { local: counter, init: hir_int(0, idx_prim, span) });
    let cond = hir_binop(
        PrimOp::Lt,
        hir_local(counter, &idx_ty, span),
        hir_int(i128::from(len), idx_prim, span),
        HirTy::Prim(PrimTy::Bool),
        span,
    );
    let mut body_stmts: Vec<HirStmt> = Vec::new();
    let snap = ctx.declare(None, idx_ty.clone());
    body_stmts.push(HirStmt::Let { local: snap, init: hir_local(counter, &idx_ty, span) });
    body_stmts.push(HirStmt::Assign {
        local: counter,
        value: hir_binop(
            PrimOp::Add,
            hir_local(counter, &idx_ty, span),
            hir_int(1, idx_prim, span),
            idx_ty.clone(),
            span,
        ),
    });
    let elem_read = HirExpr {
        ty: elem_ty.clone(),
        span,
        kind: HirExprKind::ArrayIndex {
            array: Box::new(hir_local(arr_local, &arr_ty, span)),
            index: Box::new(hir_local(snap, &idx_ty, span)),
            elem_ty,
        },
    };
    bind_irrefutable(ctx, pat, elem_read, &mut body_stmts);
    let lowered_body = lower_loop_body(ctx, body);
    body_stmts.push(HirStmt::Expr(HirExpr {
        kind: HirExprKind::Block(Box::new(lowered_body)),
        ty: HirTy::Unit,
        span,
    }));
    Some(HirExpr {
        ty: HirTy::Unit,
        span,
        kind: HirExprKind::While {
            label: label.clone(),
            cond: Box::new(cond),
            body: Box::new(HirBlock { stmts: body_stmts, trailing: None, label: None }),
        },
    })
}

fn lower_match(
    ctx: &mut LowerCtx<'_>,
    scrutinee: &Expr,
    arms: &[AstMatchArm],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let scrut_h = lower_expected(ctx, scrutinee, HirTy::Unknown);
    let scrut_ty = scrut_h.ty.clone();
    if scrut_ty == HirTy::Unknown {
        return scrut_h;
    }
    // A known slot type (`let x: T = match ...`) unifies the arms.
    let expected = ctx.current_expected().cloned().filter(|t| *t != HirTy::Unknown);
    let mut arm_h: Vec<HirMatchArm> = Vec::with_capacity(arms.len());
    for arm in arms {
        ctx.push_scope();
        let pat = lower_pattern(ctx, &arm.pat, &scrut_ty);
        let guard = arm.guard.as_ref().map(|g| lower_cond(ctx, g));
        let body = lower_expr(ctx, &arm.body);
        ctx.pop_scope();
        arm_h.push(HirMatchArm { pat, guard, body });
    }
    // Spec 3.12.5: exhaustiveness.
    check_match_exhaustiveness(ctx, &scrut_ty, &arm_h);

    // Result type: the expected slot, else the first arm that produces
    // a value; every other value-producing arm must agree.
    let result_ty = expected.unwrap_or_else(|| {
        arm_h
            .iter()
            .find(|a| !hir_expr_diverges(&a.body))
            .map_or(HirTy::Unit, |a| a.body.ty.clone())
    });
    // `let x: T = v else { ... };` is parsed as a two-arm match whose
    // second arm is the else block (parser desugar).
    let is_let_else = matches!(
        arms.first().map(|a| &a.pat.kind),
        Some(AstPatternKind::Binding { name, .. } | AstPatternKind::TypeCheck { binder: Some(name), .. })
            if name == "__letelse_v"
    );
    let mut out = Vec::with_capacity(arm_h.len());
    for (i, mut a) in arm_h.into_iter().enumerate() {
        // A unit-typed match (statement position) discards arm values.
        if !hir_expr_diverges(&a.body) && (result_ty != HirTy::Unit || is_let_else) {
            if is_let_else && i == 1 {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    "the `else` block of `let ... else` must diverge (end in `return`, \
                     `break`, `continue` or `throw`) (spec 3.15)"
                        .to_owned(),
                );
            } else {
                a.body = coerce(ctx, &result_ty, a.body, &|| format!("match arm {}", i + 1));
            }
        }
        out.push(a);
    }
    HirExpr {
        kind: HirExprKind::Match { scrutinee: Box::new(scrut_h), arms: out },
        ty: result_ty,
        span,
    }
}

/// Matches every value of its type (no refutable sub-pattern).
fn hir_pattern_irrefutable(p: &HirPattern) -> bool {
    match p {
        HirPattern::Wildcard | HirPattern::Binding { .. } => true,
        HirPattern::Tuple(parts) => parts.iter().all(hir_pattern_irrefutable),
        HirPattern::Struct { fields, .. } => fields.iter().all(|(_, p)| hir_pattern_irrefutable(p)),
        HirPattern::Or(alts) => alts.iter().any(hir_pattern_irrefutable),
        HirPattern::Literal { .. }
        | HirPattern::Range { .. }
        | HirPattern::EnumVariant { .. }
        | HirPattern::SumVariant { .. } => false,
    }
}

/// Enum variants / sum variants fully covered by `p`.
fn covered_variants(p: &HirPattern, out: &mut Vec<u32>) {
    match p {
        HirPattern::EnumVariant { variant_index, args, .. }
            if args.iter().all(hir_pattern_irrefutable) =>
        {
            out.push(*variant_index);
        }
        HirPattern::SumVariant { variant_index, .. } => out.push(*variant_index),
        HirPattern::Or(alts) => {
            for a in alts {
                covered_variants(a, out);
            }
        }
        _ => {}
    }
}

/// Spec 3.12.5: the arms must cover the scrutinee's type. Bool needs
/// both literals; enums / sums need every variant (an arm with a guard
/// covers nothing); other types need a catch-all.
fn check_match_exhaustiveness(ctx: &LowerCtx<'_>, scrut_ty: &HirTy, arms: &[HirMatchArm]) {
    let unguarded: Vec<&HirPattern> =
        arms.iter().filter(|a| a.guard.is_none()).map(|a| &a.pat).collect();
    if unguarded.iter().any(|p| hir_pattern_irrefutable(p)) {
        return;
    }
    let missing: Vec<String> = match scrut_ty {
        HirTy::Prim(PrimTy::Bool) => {
            let mut seen = [false, false];
            fn bools(p: &HirPattern, seen: &mut [bool; 2]) {
                match p {
                    HirPattern::Literal { value: ConstVal::Bool(b), .. } => seen[usize::from(*b)] = true,
                    HirPattern::Or(alts) => alts.iter().for_each(|a| bools(a, seen)),
                    _ => {}
                }
            }
            for p in &unguarded {
                bools(p, &mut seen);
            }
            [("false", seen[0]), ("true", seen[1])]
                .iter()
                .filter(|(_, s)| !s)
                .map(|(n, _)| format!("`{n}`"))
                .collect()
        }
        HirTy::Enum(eid) => {
            let mut covered = Vec::new();
            for p in &unguarded {
                covered_variants(p, &mut covered);
            }
            let def = &ctx.env.enums[eid.0 as usize];
            let base = enum_base_name(&def.name);
            def.variants
                .iter()
                .enumerate()
                .filter(|(i, _)| !covered.contains(&u32::try_from(*i).expect("variant overflow")))
                .map(|(_, v)| format!("`{base}::{}`", v.name))
                .collect()
        }
        HirTy::Sum(variants) => {
            let mut covered = Vec::new();
            for p in &unguarded {
                covered_variants(p, &mut covered);
            }
            variants
                .iter()
                .enumerate()
                .filter(|(i, _)| !covered.contains(&u32::try_from(*i).expect("variant overflow")))
                .map(|(_, v)| format!("`{}`", ctx.ty_name(v)))
                .collect()
        }
        other => vec![format!("values of `{}` (add a `_` arm)", ctx.ty_name(other))],
    };
    if !missing.is_empty() {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!(
                "non-exhaustive match on `{}`: {} not covered (spec 3.12.5)",
                ctx.ty_name(scrut_ty),
                missing.join(", ")
            ),
        );
    }
}

fn lower_pattern(ctx: &mut LowerCtx<'_>, pat: &AstPattern, scrut_ty: &HirTy) -> HirPattern {
    let p = lower_pattern_inner(ctx, pat, scrut_ty);
    // A pattern that failed to lower still declares its names (as
    // poisoned locals) so their uses don't cascade into "cannot find".
    if matches!(p, HirPattern::Wildcard) {
        for name in pattern_bound_names(pat) {
            if ctx.lookup_in_current_scope(&name).is_none() {
                ctx.declare(Some(name), HirTy::Unknown);
            }
        }
    }
    p
}

fn lower_pattern_inner(ctx: &mut LowerCtx<'_>, pat: &AstPattern, scrut_ty: &HirTy) -> HirPattern {
    let mismatch = |ctx: &LowerCtx<'_>, what: String| {
        if *scrut_ty != HirTy::Unknown {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("{what} can't match a value of type `{}`", ctx.ty_name(scrut_ty)),
            );
        }
        HirPattern::Wildcard
    };
    match &pat.kind {
        AstPatternKind::Wildcard => HirPattern::Wildcard,
        AstPatternKind::Binding { name, sub: None } if name == "_" => HirPattern::Wildcard,
        AstPatternKind::Binding { name, sub: None } => {
            // Spec 3.11.4: when an enclosing or-pattern shares this name
            // across alternatives, reuse the preset local and check that
            // each alt binds the same type.
            if let Some(&local) = ctx.or_pattern_binders.last().and_then(|m| m.get(name)) {
                let existing = ctx.local_ty(local);
                if matches!(existing, HirTy::Unknown) {
                    ctx.locals[local.0 as usize].ty = scrut_ty.clone();
                } else if existing != *scrut_ty {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "or-pattern binding `{name}` has inconsistent types across \
                             alternatives (spec 3.11.4)"
                        ),
                    );
                }
                return HirPattern::Binding { local, ty: scrut_ty.clone() };
            }
            let local = ctx.declare(Some(name.clone()), scrut_ty.clone());
            HirPattern::Binding { local, ty: scrut_ty.clone() }
        }
        AstPatternKind::Binding { name, sub: Some(_) } => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                format!("`{name} @ pattern` bindings are not supported yet (stage-1 limitation)"),
            );
            HirPattern::Wildcard
        }
        AstPatternKind::Literal(AstLit::None) => {
            // `none` against a sum scrutinee → match the none variant.
            if let HirTy::Sum(variants) = scrut_ty {
                if let Some(idx) = variants.iter().position(is_none_ty) {
                    return HirPattern::SumVariant {
                        sum_ty: scrut_ty.clone(),
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        binder: None,
                        payload_ty: None,
                    };
                }
            }
            mismatch(ctx, "a `none` pattern".to_owned())
        }
        AstPatternKind::Literal(lit) => match literal_to_const(ctx, lit, scrut_ty) {
            Some((value, prim)) => HirPattern::Literal { value, prim },
            None => mismatch(ctx, "this literal pattern".to_owned()),
        },
        AstPatternKind::TypeCheck { binder, ty } => {
            // `name: T` — narrow a sum scrutinee to variant `T` (or, on a
            // non-sum of exactly type `T`, bind it).
            let target_ty = ctx.resolve_ast_ty(ty);
            let bind = |ctx: &mut LowerCtx<'_>| {
                binder.as_ref().map(|name| ctx.declare(Some(name.clone()), target_ty.clone()))
            };
            if let HirTy::Sum(variants) = scrut_ty {
                if let Some(idx) = sum_variant_index(variants, &target_ty) {
                    let bind_local = bind(ctx);
                    return HirPattern::SumVariant {
                        sum_ty: scrut_ty.clone(),
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        binder: bind_local,
                        payload_ty: Some(target_ty),
                    };
                }
            } else if *scrut_ty == target_ty {
                return match bind(ctx) {
                    Some(local) => HirPattern::Binding { local, ty: target_ty },
                    None => HirPattern::Wildcard,
                };
            }
            mismatch(ctx, format!("type pattern `{}`", ctx.ty_name(&target_ty)))
        }
        AstPatternKind::Or(alts) => {
            // Spec 3.11.4: every alternative must bind the same set of
            // names. Pre-allocate one shared local per name (with type
            // resolved during the first alt's lowering and checked for
            // consistency on subsequent alts).
            let name_sets: Vec<std::collections::BTreeSet<String>> =
                alts.iter().map(pattern_bound_names).collect();
            let bound_names = name_sets.first().cloned().unwrap_or_default();
            for (i, set) in name_sets.iter().enumerate().skip(1) {
                if *set != bound_names {
                    let missing: Vec<_> = bound_names.difference(set).cloned().collect();
                    let extra: Vec<_> = set.difference(&bound_names).cloned().collect();
                    let mut detail = String::new();
                    if !missing.is_empty() {
                        detail.push_str(&format!(" missing {missing:?}"));
                    }
                    if !extra.is_empty() {
                        detail.push_str(&format!(" extra {extra:?}"));
                    }
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "or-pattern alternatives bind different name sets \
                             (alternative {i}:{detail}, spec 3.11.4)"
                        ),
                    );
                }
            }
            let mut shared: HashMap<String, LocalId> = HashMap::new();
            for name in &bound_names {
                let local = ctx.declare(Some(name.clone()), HirTy::Unknown);
                shared.insert(name.clone(), local);
            }
            ctx.or_pattern_binders.push(shared);
            let lowered: Vec<HirPattern> = alts.iter().map(|a| lower_pattern(ctx, a, scrut_ty)).collect();
            ctx.or_pattern_binders.pop();
            HirPattern::Or(lowered)
        }
        // `Color::Red` or `Result::Ok(n)` patterns.
        AstPatternKind::EnumVariant { path, args } => {
            let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
            let (enum_id, idx) = match resolve_enum_variant(ctx, &segs, Some(scrut_ty), None) {
                EnumRes::Found(e, i) => (e, i),
                EnumRes::Error => return HirPattern::Wildcard,
                EnumRes::NotEnum => {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("cannot find enum variant `{}`", segs.join("::")),
                    );
                    return HirPattern::Wildcard;
                }
            };
            if *scrut_ty != HirTy::Enum(enum_id) {
                return mismatch(ctx, format!("pattern `{}`", segs.join("::")));
            }
            let variant = ctx.env.enums[enum_id.0 as usize].variants[idx].clone();
            let slots = variant_arg_tys(&variant);
            if args.len() != slots.len() {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!(
                        "pattern `{}` has {} field{}, but the variant has {}",
                        segs.join("::"),
                        args.len(),
                        if args.len() == 1 { "" } else { "s" },
                        slots.len()
                    ),
                );
                return HirPattern::Wildcard;
            }
            let lowered_args: Vec<HirPattern> =
                args.iter().zip(&slots).map(|(p, t)| lower_pattern(ctx, p, t)).collect();
            HirPattern::EnumVariant {
                enum_id,
                variant_index: u32::try_from(idx).expect("variant overflow"),
                args: lowered_args,
            }
        }
        AstPatternKind::Tuple(pats) => match scrut_ty {
            HirTy::Tuple(elem_tys) if pats.len() == elem_tys.len() => HirPattern::Tuple(
                pats.iter().zip(elem_tys.iter()).map(|(p, t)| lower_pattern(ctx, p, t)).collect(),
            ),
            _ => mismatch(ctx, format!("a {}-tuple pattern", pats.len())),
        },
        AstPatternKind::Range { start, end, inclusive } => {
            let prim = match scrut_ty {
                HirTy::Prim(p) if p.is_int() => *p,
                _ => return mismatch(ctx, "a range pattern".to_owned()),
            };
            let bound = |ctx: &LowerCtx<'_>, lit: &Option<AstLit>| match lit {
                None => Some(None),
                Some(l) => literal_to_const(ctx, l, scrut_ty).map(|(v, _)| Some(v)),
            };
            match (bound(ctx, start), bound(ctx, end)) {
                (Some(s), Some(e)) => HirPattern::Range { start: s, end: e, inclusive: *inclusive, prim },
                _ => mismatch(ctx, "this range pattern".to_owned()),
            }
        }
        AstPatternKind::Struct { path, fields, .. } => {
            let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
            // `EnumName::Variant { x, y }` — enum named-form variant
            // pattern. Map each field name to its position in the
            // variant's tuple payload (spec 2.4).
            match resolve_enum_variant(ctx, &segs, Some(scrut_ty), None) {
                EnumRes::Error => return HirPattern::Wildcard,
                EnumRes::Found(enum_id, idx) => {
                    if *scrut_ty != HirTy::Enum(enum_id) {
                        return mismatch(ctx, format!("pattern `{}`", segs.join("::")));
                    }
                    let variant = ctx.env.enums[enum_id.0 as usize].variants[idx].clone();
                    let field_tys = variant_arg_tys(&variant);
                    let mut args = vec![HirPattern::Wildcard; variant.named_fields.len()];
                    for fp in fields {
                        let Some(i) = variant.named_fields.iter().position(|n| *n == fp.name) else {
                            ctx.emit_error(
                                rokc_diagnostic::ErrorKind::Type,
                                format!("enum variant `{}` has no field `{}`", segs.join("::"), fp.name),
                            );
                            continue;
                        };
                        let ty = field_tys[i].clone();
                        args[i] = match &fp.pat {
                            Some(p) => lower_pattern(ctx, p, &ty),
                            None => {
                                let local = ctx.declare(Some(fp.name.clone()), ty.clone());
                                HirPattern::Binding { local, ty }
                            }
                        };
                    }
                    return HirPattern::EnumVariant {
                        enum_id,
                        variant_index: u32::try_from(idx).expect("variant overflow"),
                        args,
                    };
                }
                EnumRes::NotEnum => {}
            }
            let struct_id = ctx.canon_type(&segs).and_then(|full| ctx.lookup_struct(&full));
            let Some(struct_id) = struct_id else {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!("cannot find struct `{}` in this scope", segs.join("::")),
                );
                return HirPattern::Wildcard;
            };
            if *scrut_ty != HirTy::Struct(struct_id) {
                return mismatch(ctx, format!("struct pattern `{}`", segs.join("::")));
            }
            let def = ctx.struct_def(struct_id);
            let mut lowered: Vec<(u32, HirPattern)> = Vec::new();
            for fp in fields {
                let Some(idx) = def.fields.iter().position(|f| f.name == fp.name) else {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("struct `{}` has no field `{}`", def.name, fp.name),
                    );
                    continue;
                };
                ctx.check_field_visible(struct_id, &fp.name);
                let field_ty = def.fields[idx].ty.clone();
                let sub = match &fp.pat {
                    Some(p) => lower_pattern(ctx, p, &field_ty),
                    // Shorthand `Foo { x }` — bind a local of the field's name.
                    None => {
                        let local = ctx.declare(Some(fp.name.clone()), field_ty.clone());
                        HirPattern::Binding { local, ty: field_ty }
                    }
                };
                lowered.push((u32::try_from(idx).expect("field index overflow"), sub));
            }
            HirPattern::Struct { struct_id, fields: lowered }
        }
        AstPatternKind::Rest(_) => {
            ctx.emit_error(
                rokc_diagnostic::ErrorKind::Type,
                "a rest pattern `..` is only allowed in tuple destructuring `let`".to_owned(),
            );
            HirPattern::Wildcard
        }
    }
}

/// Names bound by a pattern (sorted, for or-pattern consistency).
fn pattern_bound_names(pat: &AstPattern) -> std::collections::BTreeSet<String> {
    struct Names(std::collections::BTreeSet<String>);
    impl crate::walk::AstVisitor for Names {
        fn bind(&mut self, name: &str) {
            self.0.insert(name.to_owned());
        }
    }
    let mut n = Names(std::collections::BTreeSet::new());
    match &pat.kind {
        // Spec 3.11.4: alternatives bind the same names; the first one
        // stands for the whole or-pattern.
        AstPatternKind::Or(alts) => {
            if let Some(first) = alts.first() {
                crate::walk::walk_pat(&mut n, first);
            }
        }
        _ => crate::walk::walk_pat(&mut n, pat),
    }
    n.0
}

/// Convert an AST literal that appears in a pattern to a `ConstVal` plus
/// the primitive type the comparison should use. `None` when the
/// literal's type doesn't fit the scrutinee (the caller reports).
fn literal_to_const(ctx: &LowerCtx<'_>, lit: &AstLit, scrut_ty: &HirTy) -> Option<(ConstVal, PrimTy)> {
    let HirTy::Prim(sp) = scrut_ty else { return None };
    match lit {
        AstLit::Int(text) => {
            // Bare literals take the scrutinee's type.
            let (value, mut ty) = parse_int_literal(text)?;
            if !has_int_suffix(text) {
                ty = *sp;
            }
            if ty != *sp || !sp.is_int() {
                return None;
            }
            if !int_fits(value, ty) {
                ctx.emit_error(
                    rokc_diagnostic::ErrorKind::Type,
                    format!("literal `{text}` out of range for `{}`", ty.name()),
                );
            }
            Some((ConstVal::Int { value, ty }, ty))
        }
        AstLit::Bool(b) if *sp == PrimTy::Bool => Some((ConstVal::Bool(*b), PrimTy::Bool)),
        AstLit::Char(s) if *sp == PrimTy::Char => {
            parse_char_literal(s).map(|c| (ConstVal::Char(c), PrimTy::Char))
        }
        // An ASCII `'a'` against a `c_char` scrutinee takes that type.
        AstLit::Char(s) if *sp == PrimTy::CChar => parse_char_literal(s)
            .filter(|c| *c < 0x80)
            .map(|c| (ConstVal::Char(c), PrimTy::CChar)),
        AstLit::CChar(s) if *sp == PrimTy::CChar => {
            parse_char_literal(s).map(|c| (ConstVal::Char(c), PrimTy::CChar))
        }
        // String / float literal patterns would need value equality the
        // backend doesn't lower yet.
        _ => None,
    }
}

/// Does `v` fit in primitive integer type `p`? (64-bit target)
fn int_fits(v: i128, p: PrimTy) -> bool {
    let bits = p.bit_width(64);
    if bits == 0 || bits >= 128 {
        return true;
    }
    if p.is_signed_int() {
        let lim = 1i128 << (bits - 1);
        (-lim..lim).contains(&v)
    } else {
        (0..(1i128 << bits)).contains(&v)
    }
}

// Decode a `"..."` literal body (spec 1.7.1). The lexer already
// rejected malformed escapes, so the fallback is never taken.
fn decode_str_escapes(s: &str) -> String {
    rokc_ast::escape::unescape(s, rokc_ast::escape::EscapeMode::Str).unwrap_or_else(|_| s.to_owned())
}

fn has_int_suffix(text: &str) -> bool {
    const SUFFIXES: &[&str] = &[
        "isize", "usize", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
    ];
    SUFFIXES.iter().any(|s| text.ends_with(s))
}

fn lower_if(
    ctx: &mut LowerCtx<'_>,
    cond: &Expr,
    then_block: &Block,
    else_branch: Option<&Expr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let cond_h = lower_cond(ctx, cond);
    let expected = ctx.current_expected().cloned().filter(|t| *t != HirTy::Unknown);
    let mut then_h = lower_block(ctx, then_block);
    let Some(else_e) = else_branch else {
        // No else: the if is a statement; any then-value is discarded.
        return HirExpr {
            kind: HirExprKind::If { cond: Box::new(cond_h), then_block: Box::new(then_h), else_branch: None },
            ty: HirTy::Unit,
            span,
        };
    };
    let mut else_h = lower_expr(ctx, else_e);
    // Spec 3.14.1: a diverging branch (`return` / `throw` / ...) takes
    // the other branch's type.
    let then_ty = then_h.trailing.as_ref().map_or(HirTy::Unit, |e| e.ty.clone());
    let else_ty = else_h.ty.clone();
    let then_div = hir_block_diverges(&then_h);
    let else_div = hir_expr_diverges(&else_h);
    let result_ty = if expected == Some(HirTy::Unit) {
        // Statement position: branch values are discarded.
        HirTy::Unit
    } else if then_div {
        else_ty
    } else if else_div || then_ty == else_ty {
        then_ty
    } else if then_ty == HirTy::Unknown || else_ty == HirTy::Unknown {
        HirTy::Unknown
    } else if let Some(t) = expected.filter(|t| ty_compatible(t, &then_ty) && ty_compatible(t, &else_ty)) {
        t
    } else {
        // Spec 변경점 1019: 분기 타입이 다르면 결과는 자동 합 타입
        // (`if c { 7 } else { 3.14 }` → `i32 | f64`).
        HirTy::Sum(vec![then_ty, else_ty])
    };
    if matches!(result_ty, HirTy::Sum(_)) {
        if let Some(t) = then_h.trailing.take() {
            then_h.trailing = Some(wrap_into_sum(&result_ty, t));
        }
        else_h = wrap_if_block_trailing(else_h, &result_ty);
    }
    HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(cond_h),
            then_block: Box::new(then_h),
            else_branch: Some(Box::new(else_h)),
        },
        ty: result_ty,
        span,
    }
}

// For an else branch — typically a Block expression — wrap the block's
// trailing expression into the unifying sum. Falls back to wrapping the
// whole expression when the else isn't a block (e.g. `else if`).
fn wrap_if_block_trailing(expr: HirExpr, sum_ty: &HirTy) -> HirExpr {
    match expr.kind {
        HirExprKind::Block(mut b) => {
            if let Some(t) = b.trailing.take() {
                b.trailing = Some(wrap_into_sum(sum_ty, t));
            }
            HirExpr { ty: sum_ty.clone(), kind: HirExprKind::Block(b), span: expr.span }
        }
        _ => wrap_into_sum(sum_ty, expr),
    }
}

/// Where call arguments come from: still-AST expressions (lowered
/// against the parameter type) or values already lowered (spread).
enum ArgSrc<'e> {
    Ast(&'e Expr),
    Lowered(HirExpr),
}

/// Lower call arguments against a signature: named arguments go to
/// their parameter slot (spec 4.1), tuple spreads fill consecutive
/// slots, missing trailing parameters take their defaults, and every
/// argument is checked against its parameter type. `receiver` fills
/// slot 0 (method calls).
fn lower_args_for(
    ctx: &mut LowerCtx<'_>,
    sig: &FnSig,
    callee: &str,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> (Vec<HirExpr>, Vec<HirStmt>) {
    let n = sig.param_tys.len();
    let mut lets: Vec<HirStmt> = Vec::new();
    let mut slots: Vec<Option<ArgSrc<'_>>> = (0..n).map(|_| None).collect();
    let mut next = 0usize;
    let mut extra = 0usize;
    if let Some(r) = receiver {
        if n > 0 {
            slots[0] = Some(ArgSrc::Lowered(r));
        }
        next = 1;
    }
    for a in args {
        match a {
            CallArg::Positional(e) => {
                if next < n {
                    slots[next] = Some(ArgSrc::Ast(e));
                } else {
                    lower_expected(ctx, e, HirTy::Unknown);
                    extra += 1;
                }
                next += 1;
            }
            CallArg::Named { name, value } => {
                match sig.param_names.iter().position(|p| p == name) {
                    Some(i) if slots[i].is_none() => slots[i] = Some(ArgSrc::Ast(value)),
                    Some(_) => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("argument `{name}` provided more than once (spec 4.1)"),
                    ),
                    None => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("`{callee}` has no parameter named `{name}` (spec 4.1)"),
                    ),
                }
            }
            CallArg::Spread(e) => {
                // Spec 4.1 / variant 838: `f(..t)` with a tuple value.
                let lh = lower_expected(ctx, e, HirTy::Unknown);
                match lh.ty.clone() {
                    HirTy::Tuple(parts) => {
                        // Evaluate the tuple once into a temp, then read
                        // its fields.
                        let tuple_ty = lh.ty.clone();
                        let tmp = ctx.declare(None, tuple_ty.clone());
                        lets.push(HirStmt::Let { local: tmp, init: lh });
                        for (i, part_ty) in parts.iter().enumerate() {
                            let field = HirExpr {
                                kind: HirExprKind::TupleField {
                                    target: Box::new(hir_local(tmp, &tuple_ty, span)),
                                    index: u32::try_from(i).expect("tuple field overflow"),
                                    field_ty: part_ty.clone(),
                                },
                                ty: part_ty.clone(),
                                span,
                            };
                            if next < n {
                                slots[next] = Some(ArgSrc::Lowered(field));
                            } else {
                                extra += 1;
                            }
                            next += 1;
                        }
                    }
                    HirTy::Unknown => {}
                    other => ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!(
                            "spread `f(..x)` needs a tuple value, found `{}` (List/Dict \
                             spread are separate milestones, spec 4.1)",
                            ctx.ty_name(&other)
                        ),
                    ),
                }
            }
        }
    }
    if extra > 0 {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Type,
            format!("`{callee}` takes {n} argument(s) but {} were supplied", n + extra),
        );
    }
    let mut out = Vec::with_capacity(n);
    for (i, slot) in slots.into_iter().enumerate() {
        let pty = sig.param_tys[i].clone();
        let pname = sig.param_names.get(i).cloned().unwrap_or_default();
        let v = match slot {
            Some(ArgSrc::Ast(e)) => lower_expected(ctx, e, pty.clone()),
            Some(ArgSrc::Lowered(h)) => h,
            None => match sig.param_defaults.get(i).cloned().flatten() {
                Some(d) => lower_expected(ctx, &d, pty.clone()),
                None => {
                    ctx.emit_error(
                        rokc_diagnostic::ErrorKind::Type,
                        format!("missing argument `{pname}` in call to `{callee}`"),
                    );
                    poison(span)
                }
            },
        };
        out.push(coerce(ctx, &pty, v, &|| format!("argument `{pname}` of `{callee}`")));
    }
    (out, lets)
}

/// `Call` to a statically known function with checked arguments.
fn call_sig(
    ctx: &mut LowerCtx<'_>,
    sig: &FnSig,
    callee: &str,
    receiver: Option<HirExpr>,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let (lowered, lets) = lower_args_for(ctx, sig, callee, receiver, args, span);
    with_lets(lets, HirExpr {
        kind: HirExprKind::Call { callee: sig.id, args: lowered },
        ty: sig.ret_ty.clone(),
        span,
    })
}

/// `{ lets; e }` — temporaries a spread argument introduced, so the
/// spread tuple is evaluated once.
fn with_lets(lets: Vec<HirStmt>, e: HirExpr) -> HirExpr {
    if lets.is_empty() {
        return e;
    }
    let (ty, span) = (e.ty.clone(), e.span);
    HirExpr {
        kind: HirExprKind::Block(Box::new(HirBlock { stmts: lets, trailing: Some(e), label: None })),
        ty,
        span,
    }
}

// `recv.method(args)` → Call to `Type__method(recv, args)`.
fn lower_method_call(
    ctx: &mut LowerCtx<'_>,
    receiver: &Expr,
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let recv_h = lower_expected(ctx, receiver, HirTy::Unknown);
    method_call_on(ctx, recv_h, method, args, span)
}

/// Method call on an already-lowered receiver (also used by `?.`).
fn method_call_on(
    ctx: &mut LowerCtx<'_>,
    recv_h: HirExpr,
    method: &str,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let lower_args_only = |ctx: &mut LowerCtx<'_>| discard_args(ctx, args);
    if recv_h.ty == HirTy::Unknown {
        lower_args_only(ctx);
        return recv_h;
    }
    let found = method_target_for(&recv_h.ty)
        .and_then(|t| ctx.env.method_table.get(&(t, method.to_owned())).copied());
    let Some(fn_id) = found else {
        lower_args_only(ctx);
        // Spec 3.5.2: a missing method is a hard error, not a silent
        // unit return.
        return ctx.error_expr(
            span,
            format!(
                "no method `{method}` found for type `{}` (spec 3.5.2). Either add \
                 `impl {{ fn {method}(...) {{...}} }}` or import a trait that provides it.",
                ctx.ty_name(&recv_h.ty)
            ),
        );
    };
    check_method_visible(ctx, fn_id, method);
    let key = format!("{}__{}", ty_mangle(&recv_h.ty), method);
    let sig = ctx.env.fn_table[&key].clone();
    if sig.param_names.first().map(String::as_str) != Some("self") {
        lower_args_only(ctx);
        return ctx.error_expr(
            span,
            format!(
                "`{method}` is an associated function, not a method — call it as \
                 `{}::{method}(...)`",
                ctx.ty_name(&recv_h.ty)
            ),
        );
    }
    call_sig(ctx, &sig, method, Some(recv_h), args, span)
}

/// Spec 5.6 for methods: an inherent method without `pub` is private to
/// the module of its impl block.
fn check_method_visible(ctx: &LowerCtx<'_>, fn_id: FunctionId, method: &str) {
    let Some(info) = ctx.env.method_info.get(&fn_id) else { return };
    if !ctx.is_visible(&info.module, info.vis) {
        ctx.emit_error(
            rokc_diagnostic::ErrorKind::Module,
            format!(
                "method `{method}` is private to module `{}` and cannot be called from `{}` \
                 (spec 5.6 — add `pub` to expose it)",
                module_display(&info.module),
                module_display(&ctx.current_module)
            ),
        );
    }
}

/// Call through a function-pointer or closure value.
fn call_value(
    ctx: &mut LowerCtx<'_>,
    callee_h: HirExpr,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let (arg_tys, ret, env) = match callee_h.ty.clone() {
        HirTy::Fn(a, r) => (a, *r, None),
        HirTy::Closure { args, ret, env } => (args, *ret, Some(*env)),
        HirTy::Unknown => {
            discard_args(ctx, args);
            return callee_h;
        }
        other => {
            return ctx.error_expr(span, format!("a value of type `{}` is not callable", ctx.ty_name(&other)));
        }
    };
    if args.iter().any(|a| !matches!(a, CallArg::Positional(_))) {
        return ctx.error_expr(
            span,
            "named / spread arguments need a statically known callee (spec 4.1)".to_owned(),
        );
    }
    let sig = FnSig {
        id: FunctionId(u32::MAX),
        ret_ty: ret.clone(),
        param_defaults: vec![None; arg_tys.len()],
        param_tys: arg_tys.clone(),
        param_names: (0..arg_tys.len()).map(|i| format!("#{}", i + 1)).collect(),
    };
    let (lowered, lets) = lower_args_for(ctx, &sig, "the function value", None, args, span);
    let kind = match env {
        None => HirExprKind::CallIndirect { callee: Box::new(callee_h), args: lowered, ret_ty: ret.clone() },
        Some(env_ty) => HirExprKind::CallClosure {
            closure: Box::new(callee_h),
            args: lowered,
            arg_tys,
            ret_ty: ret.clone(),
            env_ty,
        },
    };
    with_lets(lets, HirExpr { kind, ty: ret, span })
}

fn lower_call(
    ctx: &mut LowerCtx<'_>,
    callee: &Expr,
    args: &[CallArg],
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let ExprKind::Path(p) = &callee.kind else {
        // `(s.f)(x)`, `make()(x)`, ...: call through the value.
        let callee_h = lower_expected(ctx, callee, HirTy::Unknown);
        return call_value(ctx, callee_h, args, span);
    };
    let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
    let display = segs.join("::");

    // A local of `fn(...)` / closure type shadows items.
    if let [name] = segs.as_slice() {
        if let Some(local) = ctx.lookup(name) {
            let callee_h = hir_local(local, &ctx.local_ty(local), callee.span);
            return call_value(ctx, callee_h, args, span);
        }
    }

    // Free function / extern / re-export, module-aware (spec 5.x).
    if let Some(full) = ctx.resolve_fn_name(&segs) {
        ctx.check_item_visible(&full, "function");
        let sig = ctx.env.fn_table[&full].clone();
        return call_sig(ctx, &sig, &full, None, args, span);
    }

    // Generic function — monomorphize on the argument types.
    if let Some(full) = ctx.resolve_in(&segs, &ctx.env.generic_fns) {
        ctx.check_item_visible(&full, "function");
        let generic_def = ctx.env.generic_fns[&full];
        let mut lowered: Vec<HirExpr> = Vec::with_capacity(args.len());
        for a in args {
            match a {
                CallArg::Positional(e) => lowered.push(lower_expected(ctx, e, HirTy::Unknown)),
                _ => {
                    return ctx.error_expr(
                        span,
                        format!("named / spread arguments to generic `{full}` are not supported yet"),
                    );
                }
            }
        }
        if lowered.len() != generic_def.params.len() {
            return ctx.error_expr(
                span,
                format!(
                    "`{full}` takes {} argument(s) but {} were supplied",
                    generic_def.params.len(),
                    lowered.len()
                ),
            );
        }
        let Some((mono_id, ret_ty)) = monomorphize(ctx, generic_def, &lowered, span) else {
            return poison(span);
        };
        let param_tys = ctx
            .env
            .sink
            .mono_sigs
            .borrow()
            .get(&mono_id)
            .map(|s| s.param_tys.clone())
            .unwrap_or_default();
        let lowered: Vec<HirExpr> = lowered
            .into_iter()
            .enumerate()
            .map(|(i, a)| match param_tys.get(i) {
                Some(t) => coerce(ctx, t, a, &|| format!("argument {} of `{full}`", i + 1)),
                None => a,
            })
            .collect();
        return HirExpr { kind: HirExprKind::Call { callee: mono_id, args: lowered }, ty: ret_ty, span };
    }

    // `Foo(arg, ...)` — tuple-struct constructor (spec 2.7.4).
    if let Some(sid) = ctx.canon_type(&segs).and_then(|full| ctx.lookup_struct(&full)) {
        let def = ctx.struct_def(sid);
        let is_tuple_form = !def.fields.is_empty()
            && def.fields.iter().enumerate().all(|(i, f)| f.name == i.to_string());
        if !is_tuple_form {
            return ctx.error_expr(
                span,
                format!("`{display}` is not a tuple struct — use `{display} {{ field: ... }}`"),
            );
        }
        let sig = FnSig {
            id: FunctionId(u32::MAX),
            ret_ty: HirTy::Struct(sid),
            param_defaults: vec![None; def.fields.len()],
            param_tys: def.fields.iter().map(|f| f.ty.clone()).collect(),
            param_names: def.fields.iter().map(|f| f.name.clone()).collect(),
        };
        let (fields, lets) = lower_args_for(ctx, &sig, &display, None, args, span);
        return with_lets(
            lets,
            HirExpr { kind: HirExprKind::StructInit { struct_id: sid, fields }, ty: HirTy::Struct(sid), span },
        );
    }

    // `EnumName::Variant(payload)` — tuple-form enum constructor. For a
    // generic enum without an expected type, the instantiation is
    // picked from the argument types.
    let hint = ctx.current_expected().cloned();
    let is_generic_enum_base = ctx
        .enum_path(&segs)
        .is_some_and(|(full, _)| !ctx.env.enum_table.contains_key(&full));
    let pre_args: Option<Vec<HirExpr>> = if is_generic_enum_base
        && !matches!(&hint, Some(HirTy::Enum(_)))
        && args.iter().all(|a| matches!(a, CallArg::Positional(_)))
    {
        Some(
            args.iter()
                .map(|a| match a {
                    CallArg::Positional(e) => lower_expected(ctx, e, HirTy::Unknown),
                    _ => unreachable!("checked positional"),
                })
                .collect(),
        )
    } else {
        None
    };
    let arg_tys: Option<Vec<HirTy>> = pre_args.as_ref().map(|v| v.iter().map(|e| e.ty.clone()).collect());
    match resolve_enum_variant(ctx, &segs, hint.as_ref(), arg_tys.as_deref()) {
        EnumRes::Error => return poison(span),
        EnumRes::Found(enum_id, idx) => {
            let variant = ctx.env.enums[enum_id.0 as usize].variants[idx].clone();
            let slots = variant_arg_tys(&variant);
            if !variant.named_fields.is_empty() {
                return ctx.error_expr(span, format!("`{display}` has named fields — use `{display} {{ ... }}`"));
            }
            let mut lets = Vec::new();
            let args_h = match pre_args {
                Some(pre) => {
                    if pre.len() != slots.len() {
                        return ctx.error_expr(
                            span,
                            format!("`{display}` takes {} argument(s) but {} were supplied", slots.len(), pre.len()),
                        );
                    }
                    pre.into_iter()
                        .zip(&slots)
                        .enumerate()
                        .map(|(i, (a, t))| coerce(ctx, t, a, &|| format!("argument {} of `{display}`", i + 1)))
                        .collect()
                }
                None => {
                    let sig = FnSig {
                        id: FunctionId(u32::MAX),
                        ret_ty: HirTy::Enum(enum_id),
                        param_defaults: vec![None; slots.len()],
                        param_tys: slots.clone(),
                        param_names: (0..slots.len()).map(|i| format!("#{}", i + 1)).collect(),
                    };
                    let (a, l) = lower_args_for(ctx, &sig, &display, None, args, span);
                    lets = l;
                    a
                }
            };
            return with_lets(lets, HirExpr {
                kind: HirExprKind::EnumVariantInit {
                    enum_id,
                    variant_index: u32::try_from(idx).expect("variant overflow"),
                    args: args_h,
                },
                ty: HirTy::Enum(enum_id),
                span,
            });
        }
        EnumRes::NotEnum => {}
    }

    // `Type::method(args)` — static call through the method table. A
    // generic base (`Stack::new()`) resolves when exactly one
    // instantiation provides the method.
    if let Some((method, ty_segs)) = segs.split_last() {
        if !ty_segs.is_empty() {
            if let Some(full) = ctx.canon_type(ty_segs) {
                let method = (*method).to_owned();
                let mut targets: Vec<MethodTarget> = Vec::new();
                if let Some(sid) = ctx.lookup_struct(&full) {
                    targets.push(MethodTarget::Struct(sid));
                } else if let Some(&eid) = ctx.env.enum_table.get(&full) {
                    targets.push(MethodTarget::Enum(eid));
                } else {
                    targets.extend(
                        LowerCtx::instantiations(&ctx.env.struct_table, &full)
                            .into_iter()
                            .map(MethodTarget::Struct),
                    );
                    targets.extend(
                        LowerCtx::instantiations(&ctx.env.enum_table, &full)
                            .into_iter()
                            .map(MethodTarget::Enum),
                    );
                }
                let hits: Vec<(MethodTarget, FunctionId)> = targets
                    .into_iter()
                    .filter_map(|t| ctx.env.method_table.get(&(t.clone(), method.clone())).map(|&id| (t, id)))
                    .collect();
                match hits.as_slice() {
                    [(target, fn_id)] => {
                        check_method_visible(ctx, *fn_id, &method);
                        let prefix = match target {
                            MethodTarget::Struct(sid) => format!("Struct{}", sid.0),
                            MethodTarget::Enum(eid) => format!("Enum{}", eid.0),
                            MethodTarget::Mangled(s) => s.clone(),
                        };
                        let sig = ctx.env.fn_table[&format!("{prefix}__{method}")].clone();
                        return call_sig(ctx, &sig, &display, None, args, span);
                    }
                    [] => {
                        return ctx.error_expr(span, format!("no associated function `{method}` on `{full}`"));
                    }
                    _ => {
                        return ctx.error_expr(
                            span,
                            format!(
                                "`{display}` is ambiguous: several instantiations of `{full}` \
                                 provide `{method}` — name the type arguments"
                            ),
                        );
                    }
                }
            }
        }
    }

    discard_args(ctx, args);
    ctx.error_expr(span, format!("cannot find function `{display}` in this scope"))
}

/// Lower call arguments only for their diagnostics (the call itself
/// failed to resolve).
fn discard_args(ctx: &mut LowerCtx<'_>, args: &[CallArg]) {
    for a in args {
        let (CallArg::Positional(e) | CallArg::Named { value: e, .. } | CallArg::Spread(e)) = a;
        lower_expected(ctx, e, HirTy::Unknown);
    }
}

fn is_arith_op(op: &str) -> bool {
    matches!(op, "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>")
}

fn lower_infix(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    lhs: &Expr,
    rhs: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // Spec 3.2 / 3.1: `&&` and `||` short-circuit. Desugar before
    // lowering rhs so that side effects in rhs only run when needed.
    if op == "&&" || op == "||" {
        return lower_short_circuit(ctx, op, lhs, rhs, span);
    }
    // Arithmetic operands share the result's type (so `let x: i64 = 1 + 2`
    // types both literals as i64); comparison operands don't.
    let lhs_expected = if is_arith_op(op) {
        ctx.current_expected().cloned().unwrap_or(HirTy::Unknown)
    } else {
        HirTy::Unknown
    };
    let (lhs_h, rhs_h) = lower_sibling_pair(ctx, lhs, rhs, lhs_expected);
    if lhs_h.ty == HirTy::Unknown || rhs_h.ty == HirTy::Unknown {
        return poison(span);
    }
    // Spec 0.4 / 3.1: `a + b` on a user type desugars to the operator
    // trait's method (`impl Add for T`).
    if matches!(lhs_h.ty, HirTy::Struct(_) | HirTy::Enum(_)) {
        return dispatch_user_op(ctx, op, Fixity::Infix, lhs_h, Some(rhs_h), span);
    }
    if let (HirTy::Prim(lp), HirTy::Prim(rp)) = (&lhs_h.ty, &rhs_h.ty) {
        if lp == rp {
            if let Some((primop, result_ty)) = infix_for_prim(op, *lp) {
                return hir_binop(primop, lhs_h, rhs_h, result_ty, span);
            }
        }
    }
    ctx.error_expr(
        span,
        format!(
            "operator `{op}` cannot be applied to `{}` and `{}`",
            ctx.ty_name(&lhs_h.ty),
            ctx.ty_name(&rhs_h.ty)
        ),
    )
}

fn lower_short_circuit(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    lhs: &Expr,
    rhs: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let lhs_h = lower_cond(ctx, lhs);
    let rhs_h = lower_cond(ctx, rhs);
    let mk_const_bool = |b: bool| HirExpr {
        kind: HirExprKind::Const(ConstVal::Bool(b)),
        ty: bool_ty.clone(),
        span,
    };
    let mk_block = |trailing: HirExpr| HirBlock { stmts: Vec::new(), trailing: Some(trailing), label: None };
    //   a && b  →  if a { b } else { false }
    //   a || b  →  if a { true } else { b }
    let (then_expr, else_expr) =
        if op == "&&" { (rhs_h, mk_const_bool(false)) } else { (mk_const_bool(true), rhs_h) };
    HirExpr {
        kind: HirExprKind::If {
            cond: Box::new(lhs_h),
            then_block: Box::new(mk_block(then_expr)),
            else_branch: Some(Box::new(else_expr)),
        },
        ty: bool_ty,
        span,
    }
}

fn lower_prefix(
    ctx: &mut LowerCtx<'_>,
    op: &str,
    operand: &Expr,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    // `-5` / `-1.5`: a negative literal (range-checked as negative).
    if op == "-" {
        if let ExprKind::Literal(lit @ (AstLit::Int(_) | AstLit::Float(_))) = &operand.kind {
            return lower_literal(ctx, lit, true, span);
        }
    }
    let operand_h = lower_expr(ctx, operand);
    if operand_h.ty == HirTy::Unknown {
        return operand_h;
    }
    if matches!(operand_h.ty, HirTy::Struct(_) | HirTy::Enum(_)) {
        return dispatch_user_op(ctx, op, Fixity::Prefix, operand_h, None, span);
    }
    if let HirTy::Prim(p) = &operand_h.ty {
        if let Some((primop, result_ty)) = prefix_for_prim(op, *p) {
            return HirExpr {
                kind: HirExprKind::PrimUnaryOp { op: primop, operand: Box::new(operand_h) },
                ty: result_ty,
                span,
            };
        }
    }
    ctx.error_expr(
        span,
        format!("operator `{op}` cannot be applied to `{}`", ctx.ty_name(&operand_h.ty)),
    )
}

/// Dispatch an operator on a user type to its operator-trait method
/// (spec 0.4: `a + b` ≡ `Add::add(a, b)`). The method must come from a
/// trait impl (`impl Add for T`) — an inherent method that merely has
/// the right name doesn't make the type support the operator.
fn dispatch_user_op(
    ctx: &mut LowerCtx<'_>,
    sym: &str,
    fixity: Fixity,
    lhs: HirExpr,
    rhs: Option<HirExpr>,
    span: rokc_diagnostic::Span,
) -> HirExpr {
    let ty_name = ctx.ty_name(&lhs.ty);
    let Some(entry) = ctx.env.prec.lookup(sym, fixity) else {
        return ctx.error_expr(span, format!("operator `{sym}` cannot be applied to `{ty_name}`"));
    };
    let method = entry.method_name.clone();
    let fn_id = method_target_for(&lhs.ty)
        .and_then(|t| ctx.env.method_table.get(&(t, method.clone())).copied())
        .filter(|id| ctx.env.method_info.get(id).is_some_and(|i| i.trait_name.is_some()));
    let Some(fn_id) = fn_id else {
        return ctx.error_expr(
            span,
            format!(
                "operator `{sym}` cannot be applied to `{ty_name}`: no operator trait impl \
                 provides `{method}` for it (an inherent `fn {method}` is not enough)"
            ),
        );
    };
    let sig = ctx.env.fn_table[&format!("{}__{method}", ty_mangle(&lhs.ty))].clone();
    let expected_arity = if rhs.is_some() { 2 } else { 1 };
    if sig.param_tys.len() != expected_arity {
        return ctx.error_expr(
            span,
            format!(
                "`{method}` for `{ty_name}` must take {expected_arity} parameter(s) to implement \
                 operator `{sym}`"
            ),
        );
    }
    let mut args = vec![lhs];
    if let Some(r) = rhs {
        let pty = sig.param_tys[1].clone();
        args.push(coerce(ctx, &pty, r, &|| format!("the right operand of `{sym}`")));
    }
    HirExpr { kind: HirExprKind::Call { callee: fn_id, args }, ty: sig.ret_ty, span }
}

/// Map an infix operator symbol + primitive operand type to a primitive
/// op and its result type. `None` if the combination isn't valid for
/// primitives.
fn infix_for_prim(sym: &str, prim: PrimTy) -> Option<(PrimOp, HirTy)> {
    let bool_ty = HirTy::Prim(PrimTy::Bool);
    let same_ty = HirTy::Prim(prim);
    let arith = |op: PrimOp| Some((op, same_ty.clone()));
    let cmp = |op: PrimOp| Some((op, bool_ty.clone()));
    let num = prim.is_int() || prim.is_float();
    match sym {
        "+" if num => arith(PrimOp::Add),
        "-" if num => arith(PrimOp::Sub),
        "*" if num => arith(PrimOp::Mul),
        "/" if num => arith(PrimOp::Div),
        "%" if num => arith(PrimOp::Rem),
        "&" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitAnd),
        "|" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitOr),
        "^" if prim.is_int() || matches!(prim, PrimTy::Bool) => arith(PrimOp::BitXor),
        "<<" if prim.is_int() => arith(PrimOp::Shl),
        ">>" if prim.is_int() => arith(PrimOp::Shr),
        // `str` equality would compare pointers, not contents.
        "==" | "≡" if prim != PrimTy::Str => cmp(PrimOp::Eq),
        "!=" | "≠" if prim != PrimTy::Str => cmp(PrimOp::Ne),
        "<" if num => cmp(PrimOp::Lt),
        "<=" | "≤" if num => cmp(PrimOp::Le),
        ">" if num => cmp(PrimOp::Gt),
        ">=" | "≥" if num => cmp(PrimOp::Ge),
        _ => None,
    }
}

fn prefix_for_prim(sym: &str, prim: PrimTy) -> Option<(PrimOp, HirTy)> {
    let same_ty = HirTy::Prim(prim);
    match sym {
        "-" if prim.is_signed_int() || prim.is_float() => Some((PrimOp::Neg, same_ty)),
        "!" if matches!(prim, PrimTy::Bool) => Some((PrimOp::LogicalNot, same_ty)),
        "~" if prim.is_int() => Some((PrimOp::Not, same_ty)),
        _ => None,
    }
}

fn lower_path(ctx: &mut LowerCtx<'_>, path: &AstPath, span: rokc_diagnostic::Span) -> HirExpr {
    let segs: Vec<&str> = path.segments.iter().map(|s| s.name.as_str()).collect();
    if let [name] = segs.as_slice() {
        if let Some(local) = ctx.lookup(name) {
            return hir_local(local, &ctx.local_ty(local), span);
        }
    }
    // Module-level `const NAME: T = expr;` — inline the value at the
    // use site, typed by the const's declaration.
    if let Some(full) = ctx.resolve_in(&segs, &ctx.env.consts) {
        ctx.check_item_visible(&full, "const");
        let (ty, value) = ctx.env.consts[&full].clone();
        let module = module_of(&full);
        let sc = Scope { names: &ctx.env.names, module: &module };
        let ty = resolve_ty_with_structs(&ty, &ctx.env.struct_table, &ctx.env.enum_table, sc);
        let v = lower_expected(ctx, &value, ty.clone());
        return coerce(ctx, &ty, v, &|| format!("const `{full}`"));
    }
    // Module-level `static` — a load through the global address.
    if let Some(full) = ctx.resolve_in(&segs, &ctx.env.statics) {
        ctx.check_item_visible(&full, "static");
        let ty = ctx.env.statics[&full].clone();
        return HirExpr { kind: HirExprKind::StaticRef(full), ty, span };
    }
    // A function used as a value → function pointer.
    if let Some(full) = ctx.resolve_fn_name(&segs) {
        ctx.check_item_visible(&full, "function");
        let sig = ctx.env.fn_table[&full].clone();
        return HirExpr {
            kind: HirExprKind::FnRef(sig.id),
            ty: HirTy::Fn(sig.param_tys, Box::new(sig.ret_ty)),
            span,
        };
    }
    if ctx.resolve_in(&segs, &ctx.env.generic_fns).is_some() {
        return ctx.error_expr(
            span,
            format!("generic function `{}` can only be called, not used as a value", segs.join("::")),
        );
    }
    // `EnumName::Variant` (unit form). Tuple variants come through
    // `lower_call` because the parser wraps them in a Call expression.
    let hint = ctx.current_expected().cloned();
    match resolve_enum_variant(ctx, &segs, hint.as_ref(), None) {
        EnumRes::Found(enum_id, idx) => {
            let variant = &ctx.env.enums[enum_id.0 as usize].variants[idx];
            if variant.payload_ty.is_some() {
                return ctx.error_expr(
                    span,
                    format!("enum variant `{}` takes arguments: `{}(...)`", segs.join("::"), segs.join("::")),
                );
            }
            return HirExpr {
                kind: HirExprKind::EnumVariantInit {
                    enum_id,
                    variant_index: u32::try_from(idx).expect("variant overflow"),
                    args: Vec::new(),
                },
                ty: HirTy::Enum(enum_id),
                span,
            };
        }
        EnumRes::Error => return poison(span),
        EnumRes::NotEnum => {}
    }
    ctx.error_expr(span, format!("cannot find value `{}` in this scope", segs.join("::")))
}

/// Integer type an unsuffixed literal takes from its expected slot.
fn expected_prim(ctx: &LowerCtx<'_>, want: fn(PrimTy) -> bool) -> Option<PrimTy> {
    match ctx.current_expected()? {
        HirTy::Prim(p) if want(*p) => Some(*p),
        // `let x: i64 | none = 5` — the sum's single matching variant.
        HirTy::Sum(vs) => {
            let mut hits = vs.iter().filter_map(|v| match v {
                HirTy::Prim(p) if want(*p) => Some(*p),
                _ => None,
            });
            let first = hits.next()?;
            hits.next().is_none().then_some(first)
        }
        _ => None,
    }
}

/// Lower a literal (`negate` = it sits under a unary minus). Unsuffixed
/// numbers take the expected type (else `i32` / `f64`); integers are
/// range-checked against their final type.
fn lower_literal(ctx: &LowerCtx<'_>, lit: &AstLit, negate: bool, span: rokc_diagnostic::Span) -> HirExpr {
    let konst = |kind: ConstVal, ty: HirTy| HirExpr { kind: HirExprKind::Const(kind), ty, span };
    match lit {
        AstLit::Int(text) => {
            let Some((value, suffix_ty)) = parse_int_literal(text) else {
                return ctx.error_expr(span, format!("malformed integer literal `{text}`"));
            };
            let ty = if has_int_suffix(text) {
                suffix_ty
            } else {
                expected_prim(ctx, |p| p.is_int() && !matches!(p, PrimTy::CChar | PrimTy::Char)).unwrap_or(PrimTy::I32)
            };
            let value = if negate { -value } else { value };
            if negate && !ty.is_signed_int() {
                return ctx.error_expr(span, format!("cannot negate unsigned literal `{text}` of type `{}`", ty.name()));
            }
            if !int_fits(value, ty) {
                let shown = if negate { format!("-{text}") } else { text.clone() };
                return ctx.error_expr(span, format!("integer literal `{shown}` out of range for `{}`", ty.name()));
            }
            konst(ConstVal::Int { value, ty }, HirTy::Prim(ty))
        }
        AstLit::Float(text) => {
            let suffixed = text.ends_with("f32") || text.ends_with("f64");
            let ty = if suffixed {
                parse_float_literal(text).map_or(PrimTy::F64, |(_, t)| t)
            } else {
                expected_prim(ctx, PrimTy::is_float).unwrap_or(PrimTy::F64)
            };
            let digits = text.trim_end_matches("f32").trim_end_matches("f64");
            let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
            let Ok(v) = cleaned.parse::<f64>() else {
                return ctx.error_expr(span, format!("malformed float literal `{text}`"));
            };
            let v = if negate { -v } else { v };
            let bits = if ty == PrimTy::F32 {
                #[allow(clippy::cast_possible_truncation)]
                u64::from((v as f32).to_bits())
            } else {
                v.to_bits()
            };
            konst(ConstVal::Float { bits, ty }, HirTy::Prim(ty))
        }
        AstLit::Bool(b) => konst(ConstVal::Bool(*b), HirTy::Prim(PrimTy::Bool)),
        AstLit::Str(s) => konst(ConstVal::Str(decode_str_escapes(s)), HirTy::Prim(PrimTy::Str)),
        AstLit::RawStr(s) => konst(ConstVal::Str(s.clone()), HirTy::Prim(PrimTy::Str)),
        AstLit::None => konst(ConstVal::None, none_ty()),
        AstLit::Char(s) => match parse_char_literal(s) {
            // An ASCII `'a'` flowing into a `c_char` slot takes that type.
            Some(c) if c < 0x80 && expected_prim(ctx, |p| p == PrimTy::CChar).is_some() => {
                konst(ConstVal::Char(c), HirTy::Prim(PrimTy::CChar))
            }
            Some(c) => konst(ConstVal::Char(c), HirTy::Prim(PrimTy::Char)),
            None => ctx.error_expr(span, format!("unsupported character literal `'{s}'`")),
        },
        AstLit::CChar(s) => match parse_char_literal(s) {
            Some(c) => konst(ConstVal::Char(c), HirTy::Prim(PrimTy::CChar)),
            None => ctx.error_expr(span, format!("unsupported character literal `c'{s}'`")),
        },
        AstLit::FStr(_) => ctx.error_expr(span, "f-string literals are not supported yet (stage-1 limitation)".to_owned()),
    }
}

// `'A'` / `c'A'` payload is the body as written (without quotes);
// decode it with the shared escape table (spec 1.8).
fn parse_char_literal(text: &str) -> Option<u32> {
    let decoded = rokc_ast::escape::unescape(text, rokc_ast::escape::EscapeMode::CChar).ok()?;
    let mut chars = decoded.chars();
    let c = chars.next()?;
    chars.next().is_none().then_some(c as u32)
}

/// Parse an integer literal. Bare (unsuffixed) integer literals fall
/// back to `i32` — the most common integer type in rok programs.
fn parse_int_literal(text: &str) -> Option<(i128, PrimTy)> {
    const SUFFIXES: &[(&str, PrimTy)] = &[
        ("isize", PrimTy::Isize),
        ("usize", PrimTy::Usize),
        ("i64", PrimTy::I64),
        ("u64", PrimTy::U64),
        ("i32", PrimTy::I32),
        ("u32", PrimTy::U32),
        ("i16", PrimTy::I16),
        ("u16", PrimTy::U16),
        ("i8", PrimTy::I8),
        ("u8", PrimTy::U8),
    ];

    let (digits, ty) = SUFFIXES
        .iter()
        .find_map(|(suf, ty)| text.strip_suffix(suf).map(|d| (d, *ty)))
        .unwrap_or((text, PrimTy::I32));

    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    let (radix, body) = if let Some(rest) = cleaned.strip_prefix("0x").or_else(|| cleaned.strip_prefix("0X")) {
        (16u32, rest.to_owned())
    } else if let Some(rest) = cleaned.strip_prefix("0b").or_else(|| cleaned.strip_prefix("0B")) {
        (2u32, rest.to_owned())
    } else if let Some(rest) = cleaned.strip_prefix("0o").or_else(|| cleaned.strip_prefix("0O")) {
        (8u32, rest.to_owned())
    } else {
        (10u32, cleaned)
    };

    let value = i128::from_str_radix(&body, radix).ok()?;
    Some((value, ty))
}

fn parse_float_literal(text: &str) -> Option<(u64, PrimTy)> {
    const SUFFIXES: &[(&str, PrimTy)] = &[("f32", PrimTy::F32), ("f64", PrimTy::F64)];
    let (digits, ty) = SUFFIXES
        .iter()
        .find_map(|(suf, ty)| text.strip_suffix(suf).map(|d| (d, *ty)))
        .unwrap_or((text, PrimTy::F64));

    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    let bits = match ty {
        PrimTy::F32 => u64::from(cleaned.parse::<f32>().ok()?.to_bits()),
        _ => cleaned.parse::<f64>().ok()?.to_bits(),
    };
    Some((bits, ty))
}

/// Shared mutable sink for closures lifted into anonymous top-level
/// functions, generic-function monomorphizations and lazily instantiated
/// generic structs. Lowering pushes here as it walks expressions.
struct ClosureSink {
    extras: std::cell::RefCell<Vec<HirFunction>>,
    next_id: std::cell::Cell<u32>,
    /// Cached monomorphizations: `(generic_fn_name, concrete_type_args)`
    /// → specialized `FunctionId`.
    mono_cache: std::cell::RefCell<HashMap<(String, Vec<String>), FunctionId>>,
    /// Specialized `FnSig` per monomorphization for call-site lookup.
    mono_sigs: std::cell::RefCell<HashMap<FunctionId, FnSig>>,
    /// Current monomorphization nesting (bounded by `MONO_DEPTH_LIMIT`).
    mono_depth: std::cell::Cell<u32>,
    /// Generic structs instantiated from a literal during body lowering
    /// (ids continue after `Env::structs`).
    extra_structs: std::cell::RefCell<Vec<HirStructDef>>,
    extra_struct_table: std::cell::RefCell<HashMap<String, StructId>>,
    /// Diagnostics emitted during lowering — surfaced through
    /// `HirModule.diagnostics` so the driver can fail the build.
    diagnostics: std::cell::RefCell<Vec<rokc_diagnostic::RokDiagnostic>>,
}

/// Per-function lowering state: scoped name → local-id map plus the
/// running list of local declarations, on top of the shared `Env`.
struct LowerCtx<'a> {
    env: &'a Env<'a>,
    locals: Vec<HirLocal>,
    scopes: Vec<HashMap<String, LocalId>>,
    /// Per-monomorphization type-parameter substitution. Empty for
    /// non-generic functions. `T` → concrete `HirTy` overrides the
    /// alias table when both contain the same name.
    ty_subst: &'a HashMap<String, HirTy>,
    self_ty: Option<HirTy>,
    /// Enclosing function's (or closure's) return type. `return v;`
    /// checks against it and wraps `v` into a matching sum type.
    fn_ret_ty: HirTy,
    /// Closure without a declared / expected return type: the first
    /// `return v;` fixes `fn_ret_ty`.
    infer_ret: bool,
    /// Enclosing breakable constructs, innermost last: `(label,
    /// is_loop)` — labelled blocks accept `break 'l` but not `continue`.
    breakables: Vec<(Option<String>, bool)>,
    /// Stack of expected types. Every sub-expression whose type is not
    /// its parent's pushes its own expectation (or `Unknown` for none),
    /// so literals and leaf lowerings (`Box::None`, `5` → `i64`) only
    /// ever see the slot they actually flow into.
    expected_ty_stack: Vec<HirTy>,
    /// Module path of the function currently being lowered, joined with
    /// `::`. Empty string for free functions in the package root.
    current_module: String,
    /// Function-/block-scoped `use` entries. Mirrors `scopes`: each
    /// `push_scope` pushes an empty Vec, `pop_scope` pops it. Resolution
    /// walks this stack top-down before consulting module-level uses.
    local_uses: Vec<Vec<crate::uses::UseEntry>>,
    /// Or-pattern shared binders. Each Or-pattern lowering pushes a map
    /// of `name → preset LocalId` so each alternative's `Binding` reuses
    /// the same local instead of allocating a fresh one. Spec 3.11.4 —
    /// `E::A(x) | E::B(x)` must bind `x` once, with consistent type.
    or_pattern_binders: Vec<HashMap<String, LocalId>>,
}

impl<'a> LowerCtx<'a> {
    fn new(env: &'a Env<'a>, ty_subst: &'a HashMap<String, HirTy>, self_ty: Option<HirTy>) -> Self {
        Self {
            env,
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            ty_subst,
            self_ty,
            fn_ret_ty: HirTy::Unit,
            infer_ret: false,
            breakables: Vec::new(),
            expected_ty_stack: Vec::new(),
            current_module: String::new(),
            local_uses: vec![Vec::new()],
            or_pattern_binders: Vec::new(),
        }
    }

    /// Push a lowering-time diagnostic onto the shared sink. Drained
    /// into `HirModule.diagnostics` at the end of the lower pass.
    fn emit_error(&self, kind: rokc_diagnostic::ErrorKind, msg: String) {
        self.env
            .sink
            .diagnostics
            .borrow_mut()
            .push(rokc_diagnostic::RokDiagnostic::error(kind, msg));
    }

    /// Report a type error and return a poisoned placeholder (`Unknown`
    /// type). Checks skip `Unknown` operands, so one root cause yields
    /// one diagnostic.
    fn error_expr(&self, span: rokc_diagnostic::Span, msg: String) -> HirExpr {
        self.emit_error(rokc_diagnostic::ErrorKind::Type, msg);
        poison(span)
    }

    /// User-facing type name (no internal `Struct0` / mangled names).
    fn ty_name(&self, ty: &HirTy) -> String {
        match ty {
            HirTy::Struct(id) => {
                let def = self.struct_def(*id);
                if def.generic_args.is_empty() {
                    def.name
                } else {
                    let base = def.name.split("__").next().unwrap_or(&def.name).to_owned();
                    let args: Vec<String> = def.generic_args.iter().map(|a| self.ty_name(a)).collect();
                    format!("{base}<{}>", args.join(", "))
                }
            }
            HirTy::Enum(id) => {
                let name = &self.env.enums[id.0 as usize].name;
                name.split("__").next().unwrap_or(name).to_owned()
            }
            HirTy::Prim(p) => p.name().to_owned(),
            HirTy::Unit => "()".to_owned(),
            HirTy::Any => "any".to_owned(),
            HirTy::Unknown => "{unknown}".to_owned(),
            HirTy::Path(p) => p.join("::"),
            HirTy::Tuple(parts) => {
                let inner: Vec<String> = parts.iter().map(|t| self.ty_name(t)).collect();
                format!("({})", inner.join(", "))
            }
            HirTy::Sum(parts) => {
                let inner: Vec<String> = parts.iter().map(|t| self.ty_name(t)).collect();
                inner.join(" | ")
            }
            HirTy::Array(e, n) => format!("[{}; {n}]", self.ty_name(e)),
            HirTy::Fn(args, ret) | HirTy::Closure { args, ret, .. } => {
                let inner: Vec<String> = args.iter().map(|t| self.ty_name(t)).collect();
                let kw = if matches!(ty, HirTy::Fn(..)) { "fn" } else { "closure" };
                format!("{kw}({}) -> {}", inner.join(", "), self.ty_name(ret))
            }
        }
    }

    fn struct_def(&self, id: StructId) -> HirStructDef {
        let i = id.0 as usize;
        match self.env.structs.get(i) {
            Some(d) => d.clone(),
            None => self.env.sink.extra_structs.borrow()[i - self.env.structs.len()].clone(),
        }
    }

    /// Struct id by table key, including lazily instantiated ones.
    fn lookup_struct(&self, key: &str) -> Option<StructId> {
        self.env
            .struct_table
            .get(key)
            .copied()
            .or_else(|| self.env.sink.extra_struct_table.borrow().get(key).copied())
    }

    /// Instantiate generic struct `base` with `args` on demand (struct
    /// literal inference: `Box { v: 5 }` → `Box<i32>`).
    fn instantiate_struct(&self, base: &str, args: Vec<HirTy>) -> Option<StructId> {
        let key = mangle_inst(base, &args);
        if let Some(id) = self.lookup_struct(&key) {
            return Some(id);
        }
        let def = *self.env.generic_structs.get(base)?;
        let id = StructId(
            u32::try_from(self.env.structs.len() + self.env.sink.extra_structs.borrow().len())
                .expect("StructId overflow"),
        );
        self.env.sink.extra_struct_table.borrow_mut().insert(key.clone(), id);
        let module = module_of(base);
        let sc = Scope { names: &self.env.names, module: &module };
        let fields =
            generic_struct_fields(def, &args, &self.env.struct_table, &self.env.enum_table, sc);
        self.env.sink.extra_structs.borrow_mut().push(HirStructDef {
            id,
            def_id: None,
            name: key,
            fields,
            span: def.span,
            generic_args: args,
            union_kind: None,
        });
        Some(id)
    }

    fn scope(&self) -> Scope<'_> {
        Scope { names: &self.env.names, module: &self.current_module }
    }

    /// Canonical type-namespace name for a path (struct / enum / alias /
    /// trait, generic bases included), resolved from this function's
    /// module and `use`s.
    fn canon_type(&self, segments: &[&str]) -> Option<String> {
        self.env.names.canon(segments, &self.current_module, &self.local_uses)
    }

    /// Split `a::E::V` into (`a::E` enum, `V`) when the prefix names an
    /// enum (or generic enum base).
    fn enum_path<'p>(&self, segments: &'p [&'p str]) -> Option<(String, &'p str)> {
        let (variant, ty) = segments.split_last()?;
        if ty.is_empty() {
            return None;
        }
        Some((self.canon_type(ty)?, variant))
    }

    /// Instantiations of generic base `base` in `table`, sorted by key
    /// for deterministic choice.
    fn instantiations<V: Copy>(table: &HashMap<String, V>, base: &str) -> Vec<V> {
        let prefix = format!("{base}__");
        let mut hits: Vec<(&String, V)> =
            table.iter().filter(|(k, _)| k.starts_with(&prefix)).map(|(k, v)| (k, *v)).collect();
        hits.sort_by(|a, b| a.0.cmp(b.0));
        hits.into_iter().map(|(_, v)| v).collect()
    }

    /// Resolve a value-namespace path against `table` (fns, consts,
    /// statics) from this function's module and `use`s.
    fn resolve_in<T>(&self, segments: &[&str], table: &HashMap<String, T>) -> Option<String> {
        let exists = |k: &str| table.contains_key(k);
        let keys = || table.keys().cloned().collect::<Vec<_>>();
        let set = NameSet { exists: &exists, keys: &keys };
        match resolve_name(segments, &self.current_module, &self.local_uses, self.env.uses, &set) {
            Ok(r) => r,
            Err(hits) => {
                self.report_ambiguous(&segments.join("::"), &hits);
                hits.into_iter().next()
            }
        }
    }

    /// Resolve a callee name (single- or multi-segment path) to a fully
    /// qualified fn-table key.
    fn resolve_fn_name(&self, segments: &[&str]) -> Option<String> {
        self.resolve_in(segments, &self.env.fn_table)
    }

    fn report_ambiguous(&self, name: &str, hits: &[String]) {
        self.emit_error(
            rokc_diagnostic::ErrorKind::Module,
            format!(
                "name `{name}` is ambiguous in module `{}` — multiple glob imports \
                 resolve it: {}",
                module_display(&self.current_module),
                hits.join(", ")
            ),
        );
    }

    /// Visibility check: can a caller in `self.current_module` see an
    /// item declared in `def_module` with the given visibility?
    fn is_visible(&self, def_module: &str, vis: Visibility) -> bool {
        visible_from(&self.current_module, def_module, vis)
    }

    /// Report use of a private value item (fn / const / static).
    fn check_item_visible(&self, full: &str, what: &str) -> bool {
        let vis = self.env.item_visibility.get(full).copied().unwrap_or(Visibility::Pub);
        let def_module = module_of(full);
        if self.is_visible(&def_module, vis) {
            return true;
        }
        self.emit_error(
            rokc_diagnostic::ErrorKind::Module,
            format!(
                "{what} `{full}` is private to module `{}` and cannot be used from `{}` \
                 (spec 5.6 — add `pub` to expose it)",
                module_display(&def_module),
                module_display(&self.current_module)
            ),
        );
        false
    }

    /// Report access to a private field from outside its struct's module.
    fn check_field_visible(&self, sid: StructId, field: &str) {
        let def = self.struct_def(sid);
        let base = if def.generic_args.is_empty() {
            def.name.clone()
        } else {
            def.name.split("__").next().unwrap_or(&def.name).to_owned()
        };
        let Some(vis) = self.env.field_vis.get(&base).and_then(|m| m.get(field)).copied() else {
            return;
        };
        let def_module = module_of(&base);
        if !self.is_visible(&def_module, vis) {
            self.emit_error(
                rokc_diagnostic::ErrorKind::Module,
                format!(
                    "field `{field}` of `{}` is private to module `{}` (spec 5.6 — add \
                     `pub` to the field to expose it)",
                    self.ty_name(&HirTy::Struct(sid)),
                    module_display(&def_module)
                ),
            );
        }
    }

    fn push_expected(&mut self, ty: HirTy) {
        self.expected_ty_stack.push(ty);
    }
    fn pop_expected(&mut self) {
        self.expected_ty_stack.pop();
    }
    fn current_expected(&self) -> Option<&HirTy> {
        self.expected_ty_stack.last()
    }

    /// Resolve an AST type into a concrete `HirTy`, applying any
    /// monomorphization substitution, `Self`, and the alias map. Generic
    /// struct uses with concrete arguments are instantiated on demand
    /// (`Tagged<T>` under `T = i32` inside a monomorphized body).
    fn resolve_ast_ty(&self, ty: &rokc_ast::Ty) -> HirTy {
        let mut t = self.resolve_ty_inner(ty);
        if let Some(st) = &self.self_ty {
            substitute_aliases(&mut t, &HashMap::from([("Self".to_owned(), st.clone())]));
        }
        substitute_aliases(&mut t, &self.env.type_aliases);
        t
    }

    fn resolve_ty_inner(&self, ty: &rokc_ast::Ty) -> HirTy {
        let rec = |t: &rokc_ast::Ty| self.resolve_ty_inner(t);
        match &ty.kind {
            AstTyKind::Path(p) => {
                if let [seg] = p.segments.as_slice() {
                    if seg.generics.is_empty() {
                        if let Some(t) = self.ty_subst.get(&seg.name) {
                            return t.clone();
                        }
                    }
                }
                let generics = p.segments.last().map(|s| s.generics.as_slice()).unwrap_or(&[]);
                if !generics.is_empty() {
                    let segs: Vec<&str> = p.segments.iter().map(|s| s.name.as_str()).collect();
                    if let Some(full) = self.canon_type(&segs) {
                        let args: Vec<HirTy> = generics.iter().map(rec).collect();
                        let mut leftover = Vec::new();
                        args.iter().for_each(|a| collect_unknown_paths(a, &mut leftover));
                        if leftover.is_empty() && self.env.generic_structs.contains_key(&full) {
                            if let Some(id) = self.instantiate_struct(&full, args) {
                                return HirTy::Struct(id);
                            }
                        }
                    }
                }
                let mut t = resolve_ty_with_structs(ty, &self.env.struct_table, &self.env.enum_table, self.scope());
                substitute_aliases(&mut t, self.ty_subst);
                t
            }
            AstTyKind::Sum(parts) => HirTy::Sum(parts.iter().map(rec).collect()),
            AstTyKind::Tuple(parts) if parts.is_empty() => HirTy::Unit,
            AstTyKind::Tuple(parts) => HirTy::Tuple(parts.iter().map(rec).collect()),
            AstTyKind::Array(elem, _) => {
                match resolve_ty_with_structs(ty, &self.env.struct_table, &self.env.enum_table, self.scope()) {
                    HirTy::Array(_, n) => HirTy::Array(Box::new(rec(elem)), n),
                    other => other,
                }
            }
            AstTyKind::Fn(args, ret) => HirTy::Fn(args.iter().map(rec).collect(), Box::new(rec(ret))),
            _ => resolve_ty_with_structs(ty, &self.env.struct_table, &self.env.enum_table, self.scope()),
        }
    }

    fn into_locals(self) -> Vec<HirLocal> {
        self.locals
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.local_uses.push(Vec::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
        self.local_uses.pop();
    }

    fn add_local_use(&mut self, entry: crate::uses::UseEntry) {
        if let Some(top) = self.local_uses.last_mut() {
            top.push(entry);
        }
    }

    fn declare(&mut self, name: Option<String>, ty: HirTy) -> LocalId {
        let id = LocalId(u32::try_from(self.locals.len()).expect("LocalId overflow"));
        if let Some(n) = &name {
            if let Some(scope) = self.scopes.last_mut() {
                scope.insert(n.clone(), id);
            }
        }
        self.locals.push(HirLocal { id, name, ty });
        id
    }

    fn lookup(&self, name: &str) -> Option<LocalId> {
        for scope in self.scopes.iter().rev() {
            if let Some(id) = scope.get(name) {
                return Some(*id);
            }
        }
        None
    }

    /// Look up a name only in the innermost scope. Used by the let
    /// redeclaration check (spec variant 238): nested scopes can
    /// rebind, but the same scope cannot.
    fn lookup_in_current_scope(&self, name: &str) -> Option<LocalId> {
        self.scopes.last().and_then(|s| s.get(name).copied())
    }

    fn local_ty(&self, id: LocalId) -> HirTy {
        self.locals
            .get(id.0 as usize)
            .map_or(HirTy::Unknown, |l| l.ty.clone())
    }
}

/// Placeholder for an expression whose lowering failed (an error has
/// been reported). Never reaches MIR: the driver stops on errors and
/// `check_unresolved_types` refuses `Unknown` otherwise.
fn poison(span: rokc_diagnostic::Span) -> HirExpr {
    HirExpr { kind: HirExprKind::Const(ConstVal::Unit), ty: HirTy::Unknown, span }
}

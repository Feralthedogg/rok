//! Compiler driver. Threads source through lexer, parser,
//! HIR lowering (name resolution + type checks), and MIR lowering.

mod cfg;
mod entry;
mod toolchain;

use std::path::{Path, PathBuf};

use rokc_diagnostic::RokDiagnostic;
use rokc_hir::HirModule;
use rokc_lexer::Lexer;
use rokc_mir::MirModule;
use rokc_parser::{LangTable, PrecTable, collect_lang_table, collect_prec_table, parse_program};

pub use cfg::CfgEnv;
pub use toolchain::{BuildOptions, EmitKind, TempDir, emit, link_executable, mlir_text};

#[derive(Clone, Debug, Default)]
pub struct CompilerConfig {
    /// Files containing operator declarations to pre-load before parsing
    /// the user input. Populates the `PrecTable`.
    pub bootstrap_files: Vec<PathBuf>,
    /// `--cfg` flags. Each entry is either a bare flag (`"test"`) or a
    /// `key=value` pair (`"target_os=macos"`). Consulted by `#[cfg(...)]`
    /// during the pre-HIR filter pass.
    pub cfg_flags: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct CompiledModule {
    pub name: String,
    pub path: PathBuf,
    pub hir: HirModule,
    pub mir: MirModule,
}

#[derive(Clone, Debug, Default)]
pub struct CompiledProject {
    pub modules: Vec<CompiledModule>,
    pub warnings: Vec<RokDiagnostic>,
    pub link_libraries: Vec<String>,
}

pub fn compile_file(
    path: &Path,
    config: &CompilerConfig,
) -> Result<CompiledProject, Vec<RokDiagnostic>> {
    let source = std::fs::read_to_string(path).map_err(|e| {
        vec![RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Module,
            format!("cannot read {}: {e}", path.display()),
        )]
    })?;
    compile_source(&source, path, config)
}

pub fn compile_source(
    source: &str,
    path: &Path,
    config: &CompilerConfig,
) -> Result<CompiledProject, Vec<RokDiagnostic>> {
    let mut diags: Vec<RokDiagnostic> = Vec::new();

    // Bootstrap PrecTable from operator-declaration sources, if any.
    let prec = build_prec_table(&config.bootstrap_files, &mut diags)?;
    // Bootstrap LangTable from `#[lang(...)]` attributes (spec 6.4).
    // Spec 6.4.6 enforces "one item per slot" — duplicate declarations
    // surface as diagnostics here. The table itself is not yet wired
    // into HIR/codegen; this pass exists so registrations can be checked
    // for malformed shape and slot collisions before stdlib wires
    // consumers (none_type / iterator_trait / index_trait / ...).
    let mut _lang = build_lang_table(&config.bootstrap_files, &mut diags)?;

    // Walk the user package's module tree (`mod foo;` follows files
    // alongside the entry `main.rok` / `lib.rok`) and merge every
    // visited file's items into one `Program` so HIR sees a single
    // flat compilation unit.
    let root_dir = path
        .parent()
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    // Build cfg env from CLI flags + automatic target keys.
    let mut cfg_env = CfgEnv::new();
    cfg_env.populate_target_defaults();
    for f in &config.cfg_flags {
        cfg_env.add(f);
    }

    let mut all_items: Vec<rokc_ast::Item> = Vec::new();
    let mut all_uses: Vec<(String, rokc_core::Visibility, rokc_ast::UseTree)> = Vec::new();
    let top_stmts = collect_module_tree(
        path,
        Some(source),
        Some(&root_dir),
        &[],
        &prec,
        &cfg_env,
        &mut diags,
        &mut all_items,
        &mut all_uses,
    );
    let is_lib = path.file_name().is_some_and(|n| n == "lib.rok");
    if !is_lib {
        entry::resolve_entry(top_stmts, &mut all_items, &mut diags);
    } else if !top_stmts.is_empty() {
        diags.push(entry::stmts_outside_entry(path));
    }
    // Auto-inject the `rok_panic(msg, len) -> !` runtime hook so
    // `throw` lowering has a target without each user file declaring
    // the extern themselves.
    all_items.insert(0, builtin_panic_extern());
    let program = rokc_ast::Program {
        attrs: Vec::new(),
        items: all_items,
        stmts: Vec::new(),
    };

    // Spec 6.4: collect `#[lang(...)]` slots from the merged user program
    // (bootstrap files were scanned earlier in `build_lang_table`). Spec
    // 6.4.6: "한 슬롯에 한 항목" — a slot already bound by bootstrap or
    // by an earlier user item collides here.
    {
        let (sub_table, mut sub_diags) = collect_lang_table(&program);
        diags.append(&mut sub_diags);
        for entry in sub_table.entries().cloned() {
            if let Some(prev) = _lang.lookup(&entry.slot) {
                diags.push(RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Meta,
                    format!(
                        "lang slot `{}` already bound to `{}` — cannot also bind to \
                         `{}` (spec 6.4.6)",
                        entry.slot, prev.item_name, entry.item_name
                    ),
                ));
                continue;
            }
            _lang = merge_lang_entry(_lang, entry);
        }
    }

    // Name resolution and type / exhaustiveness checking happen during
    // HIR lowering (`rokc_hir::lower_full`), where every type is known.
    let errors: Vec<RokDiagnostic> = diags.iter().filter(|d| d.is_error()).cloned().collect();
    if !errors.is_empty() {
        return Err(errors);
    }

    // Convert raw use trees into a per-module table of resolution
    // entries that the HIR resolver can consult during name lookup, plus
    // a list of `pub use` re-exports the lower pass installs as fn-table
    // aliases.
    let (use_table, reexports, mut use_diags) = rokc_hir::build_use_table(&all_uses);
    diags.append(&mut use_diags);
    let mut hir = rokc_hir::lower_full(&program, &prec, &use_table, &reexports);
    diags.append(&mut hir.diagnostics);
    let errors: Vec<RokDiagnostic> = diags.iter().filter(|d| d.is_error()).cloned().collect();
    if !errors.is_empty() {
        return Err(errors);
    }
    let unsupported: Vec<RokDiagnostic> = rokc_mir::enums_without_layout(&hir)
        .into_iter()
        .map(|(name, payloads)| {
            RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Unsupported,
                format!(
                    "enum `{name}` mixes payload shapes {payloads:?}; only identical or \
                     all-scalar variant payloads have a layout yet"
                ),
            )
        })
        .collect();
    if !unsupported.is_empty() {
        return Err(unsupported);
    }
    let mir = rokc_mir::lower(&hir);

    Ok(CompiledProject {
        modules: vec![CompiledModule {
            name: path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("module")
                .to_owned(),
            path: path.to_path_buf(),
            hir,
            mir,
        }],
        warnings: diags.into_iter().filter(|d| !d.is_error()).collect(),
        link_libraries: Vec::new(),
    })
}

fn build_lang_table(
    roots: &[PathBuf],
    diags: &mut Vec<RokDiagnostic>,
) -> Result<LangTable, Vec<RokDiagnostic>> {
    let mut table = LangTable::new();
    let empty = PrecTable::new();
    for root in roots {
        let modules = resolve_module_tree(root, &empty, diags);
        for prog in modules {
            let (sub_table, mut sub_diags) = collect_lang_table(&prog);
            diags.append(&mut sub_diags);
            for entry in sub_table.entries().cloned() {
                if let Some(prev) = table.lookup(&entry.slot) {
                    diags.push(RokDiagnostic::error(
                        rokc_diagnostic::ErrorKind::Meta,
                        format!(
                            "lang slot `{}` already bound to `{}` — cannot also bind to \
                             `{}` (spec 6.4.6)",
                            entry.slot, prev.item_name, entry.item_name
                        ),
                    ));
                    continue;
                }
                // Manual insert via re-collect; LangTable has no public
                // insert method, so we assemble through a temp HashMap.
                table = merge_lang_entry(table, entry);
            }
        }
    }
    Ok(table)
}

fn merge_lang_entry(mut table: LangTable, entry: rokc_parser::LangEntry) -> LangTable {
    table.insert_entry(entry);
    table
}

fn build_prec_table(
    roots: &[PathBuf],
    diags: &mut Vec<RokDiagnostic>,
) -> Result<PrecTable, Vec<RokDiagnostic>> {
    let mut table = PrecTable::new();
    let empty = PrecTable::new();
    for root in roots {
        // Walk the package starting from the given root file (typically
        // `lib.rok` or `main.rok`), following `mod x;` declarations to
        // their files. Collect the parsed AST of every module visited.
        let modules = resolve_module_tree(root, &empty, diags);
        for prog in modules {
            let (sub_table, mut collect_diags) = collect_prec_table(&prog);
            diags.append(&mut collect_diags);
            for entry in sub_table.entries().cloned() {
                if let Some(existing) = table.lookup(&entry.symbol, entry.fixity) {
                    if existing.prec != entry.prec || existing.assoc != entry.assoc {
                        diags.push(RokDiagnostic::error(
                            rokc_diagnostic::ErrorKind::Meta,
                            format!(
                                "operator `{}` registered twice with different \
                                 precedence/associativity",
                                entry.symbol
                            ),
                        ));
                        continue;
                    }
                }
                table.insert(entry);
            }
        }
    }
    Ok(table)
}

/// Walk a package's module tree from `root_path` (the package root file —
/// `lib.rok` or `main.rok`). For every `mod name;` encountered, resolves
/// the name to a sibling `.rok` file and recurses. Inline `mod name {}`
/// blocks have their items walked in place.
///
/// Returns each visited module's parsed `Program`. Errors (missing files,
/// `mod` in a single-file leaf, etc.) are appended to `diags`.
fn resolve_module_tree(
    root_path: &Path,
    prec: &PrecTable,
    diags: &mut Vec<RokDiagnostic>,
) -> Vec<rokc_ast::Program> {
    let mut programs = Vec::new();
    // Submodule directory of the package root is the directory that
    // contains `lib.rok` / `main.rok` (per spec §5.4.4).
    let root_dir = root_path
        .parent()
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
    parse_and_descend(root_path, Some(&root_dir), prec, diags, &mut programs);
    programs
}

fn parse_and_descend(
    body_path: &Path,
    submodule_dir: Option<&Path>,
    prec: &PrecTable,
    diags: &mut Vec<RokDiagnostic>,
    out: &mut Vec<rokc_ast::Program>,
) {
    let source = match std::fs::read_to_string(body_path) {
        Ok(s) => s,
        Err(e) => {
            diags.push(RokDiagnostic::error(
                rokc_diagnostic::ErrorKind::Module,
                format!("cannot read module file {}: {e}", body_path.display()),
            ));
            return;
        }
    };
    let file = body_path.display().to_string();
    let lexer = Lexer::new(&source, file.clone());
    let (tokens, mut lex_diags) = lexer.lex_all();
    diags.append(&mut lex_diags);

    let (program, mut parse_diags) = parse_program(&tokens, prec, file);
    diags.append(&mut parse_diags);
    if !program.stmts.is_empty() {
        diags.push(entry::stmts_outside_entry(body_path));
    }

    walk_mod_decls(&program.items, submodule_dir, prec, diags, out);
    out.push(program);
}

fn walk_mod_decls(
    items: &[rokc_ast::Item],
    submodule_dir: Option<&Path>,
    prec: &PrecTable,
    diags: &mut Vec<RokDiagnostic>,
    out: &mut Vec<rokc_ast::Program>,
) {
    for item in items {
        let rokc_ast::Item::Mod(m) = item else {
            continue;
        };
        match &m.items {
            // Inline module: `mod name { ... }` — walk its items directly.
            Some(inline_items) => walk_mod_decls(inline_items, submodule_dir, prec, diags, out),
            // File-mapped module: resolve sibling `name.rok`.
            None => resolve_file_mod(&m.name, submodule_dir, prec, diags, out),
        }
    }
}

fn resolve_file_mod(
    name: &str,
    submodule_dir: Option<&Path>,
    prec: &PrecTable,
    diags: &mut Vec<RokDiagnostic>,
    out: &mut Vec<rokc_ast::Program>,
) {
    let Some(dir) = submodule_dir else {
        diags.push(RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Module,
            format!(
                "`mod {name}` in a single-file module — declare a sibling `{name}/` folder \
                 to host submodules"
            ),
        ));
        return;
    };
    let body = dir.join(format!("{name}.rok"));
    let folder = dir.join(name);
    if !body.exists() {
        diags.push(RokDiagnostic::error(
            rokc_diagnostic::ErrorKind::Module,
            format!("module `{name}` body not found at `{}`", body.display()),
        ));
        return;
    }
    let next_dir = if folder.is_dir() { Some(folder) } else { None };
    parse_and_descend(&body, next_dir.as_deref(), prec, diags, out);
}

/// Walk a package's module tree starting from `body_path`, qualifying
/// each item's name with the module path it lives under. Inline
/// `mod foo { ... }` extends the path; file-mapped `mod foo;` recurses
/// into `foo.rok` with the same extension.
///
/// Items are flattened into a single list with `name` rewritten as
/// `parent::child::leaf`. Leaf names are unchanged in the root module.
fn collect_module_tree(
    body_path: &Path,
    preloaded: Option<&str>,
    submodule_dir: Option<&Path>,
    module_path: &[String],
    prec: &PrecTable,
    cfg_env: &CfgEnv,
    diags: &mut Vec<RokDiagnostic>,
    out: &mut Vec<rokc_ast::Item>,
    uses: &mut Vec<(String, rokc_core::Visibility, rokc_ast::UseTree)>,
) -> Vec<rokc_ast::Stmt> {
    let source = match preloaded {
        Some(s) => s.to_owned(),
        None => match std::fs::read_to_string(body_path) {
            Ok(s) => s,
            Err(e) => {
                diags.push(RokDiagnostic::error(
                    rokc_diagnostic::ErrorKind::Module,
                    format!("cannot read module file {}: {e}", body_path.display()),
                ));
                return Vec::new();
            }
        },
    };
    let file = body_path.display().to_string();
    let lexer = Lexer::new(&source, file.clone());
    let (tokens, mut lex_diags) = lexer.lex_all();
    diags.append(&mut lex_diags);

    let (program, mut parse_diags) = parse_program(&tokens, prec, file);
    diags.append(&mut parse_diags);

    // Filter `#[cfg(...)]`-gated items before walking — excluded modules
    // shouldn't get their files resolved or their inline items flattened.
    let filtered = cfg::filter_items(program.items, cfg_env);

    flatten_module_items(
        filtered,
        module_path,
        submodule_dir,
        prec,
        cfg_env,
        diags,
        out,
        uses,
    );
    program.stmts
}

fn flatten_module_items(
    items: Vec<rokc_ast::Item>,
    module_path: &[String],
    submodule_dir: Option<&Path>,
    prec: &PrecTable,
    cfg_env: &CfgEnv,
    diags: &mut Vec<RokDiagnostic>,
    out: &mut Vec<rokc_ast::Item>,
    uses: &mut Vec<(String, rokc_core::Visibility, rokc_ast::UseTree)>,
) {
    let module_key = module_path.join("::");
    for item in items {
        match item {
            rokc_ast::Item::Use(u) => {
                uses.push((module_key.clone(), u.vis, u.tree));
            }
            rokc_ast::Item::Mod(m) => {
                let mut child_path = module_path.to_vec();
                child_path.push(m.name.clone());
                if let Some(inner) = m.items {
                    flatten_module_items(
                        inner,
                        &child_path,
                        submodule_dir,
                        prec,
                        cfg_env,
                        diags,
                        out,
                        uses,
                    );
                } else {
                    // File-mapped `mod foo;`. Resolve to `foo.rok` (and
                    // optional sibling `foo/` for further submodules).
                    let Some(dir) = submodule_dir else {
                        diags.push(RokDiagnostic::error(
                            rokc_diagnostic::ErrorKind::Module,
                            format!(
                                "`mod {}` in a single-file module — declare a sibling `{0}/` folder \
                                 to host submodules",
                                m.name
                            ),
                        ));
                        continue;
                    };
                    let body = dir.join(format!("{}.rok", m.name));
                    let folder = dir.join(&m.name);
                    if !body.exists() {
                        diags.push(RokDiagnostic::error(
                            rokc_diagnostic::ErrorKind::Module,
                            format!("module `{}` body not found at `{}`", m.name, body.display()),
                        ));
                        continue;
                    }
                    let next_dir = if folder.is_dir() { Some(folder) } else { None };
                    let stray = collect_module_tree(
                        &body,
                        None,
                        next_dir.as_deref(),
                        &child_path,
                        prec,
                        cfg_env,
                        diags,
                        out,
                        uses,
                    );
                    if !stray.is_empty() {
                        diags.push(entry::stmts_outside_entry(&body));
                    }
                }
            }
            other => {
                out.push(rename_with_prefix(other, module_path));
            }
        }
    }
}

/// Prepend `module_path::` (joined with `::`) to the name of any item
/// that has one. `module_path = []` returns the item untouched.
fn rename_with_prefix(item: rokc_ast::Item, module_path: &[String]) -> rokc_ast::Item {
    if module_path.is_empty() {
        return item;
    }
    let prefix = module_path.join("::");
    match item {
        rokc_ast::Item::Fn(mut f) => {
            f.name = format!("{prefix}::{}", f.name);
            rokc_ast::Item::Fn(f)
        }
        rokc_ast::Item::Struct(mut s) => {
            s.name = format!("{prefix}::{}", s.name);
            rokc_ast::Item::Struct(s)
        }
        rokc_ast::Item::Enum(mut e) => {
            e.name = format!("{prefix}::{}", e.name);
            rokc_ast::Item::Enum(e)
        }
        rokc_ast::Item::Const(mut c) => {
            c.name = format!("{prefix}::{}", c.name);
            rokc_ast::Item::Const(c)
        }
        rokc_ast::Item::Static(mut s) => {
            s.name = format!("{prefix}::{}", s.name);
            rokc_ast::Item::Static(s)
        }
        rokc_ast::Item::TypeAlias(mut a) => {
            a.name = format!("{prefix}::{}", a.name);
            rokc_ast::Item::TypeAlias(a)
        }
        rokc_ast::Item::Trait(mut t) => {
            t.name = format!("{prefix}::{}", t.name);
            rokc_ast::Item::Trait(t)
        }
        rokc_ast::Item::Union(mut u) => {
            u.name = format!("{prefix}::{}", u.name);
            rokc_ast::Item::Union(u)
        }
        // Impl blocks have no name; their methods carry the module path
        // (`a::get`) so HIR resolves the impl target and the method
        // bodies in the right module (HIR strips it back to the leaf).
        rokc_ast::Item::Impl(mut i) => {
            for it in &mut i.items {
                if let rokc_ast::ImplItem::Method(m) = it {
                    m.name = format!("{prefix}::{}", m.name);
                }
            }
            rokc_ast::Item::Impl(i)
        }
        rokc_ast::Item::Use(_) // already extracted into `uses`
        | rokc_ast::Item::Extern(_)
        | rokc_ast::Item::Mod(_) => item,
    }
}

/// Synthesize the runtime `extern "C"` block with the small set of
/// always-available primitives — `rok_panic` (used by `throw`),
/// `rok_print_str`, `rok_print_i32`, and `rok_print_i64`. Every user
/// source file gets these for free without writing an extern block.
fn builtin_panic_extern() -> rokc_ast::Item {
    use rokc_ast::{ExternBlock, ExternItem, FnDef, Generics, Param, ThrowsKind, Ty, TyKind};
    use rokc_diagnostic::Span;

    let span = Span::DUMMY;
    let path_ty = |name: &str| Ty {
        kind: TyKind::Path(rokc_ast::Path {
            segments: vec![rokc_ast::PathSegment {
                name: name.to_owned(),
                generics: Vec::new(),
            }],
            span,
        }),
        span,
    };
    let make_fn = |fn_name: &str, params: Vec<(&str, Ty)>, ret: Option<Ty>| FnDef {
        vis: rokc_core::Visibility::Pub,
        attrs: Vec::new(),
        name: fn_name.to_owned(),
        generics: Generics::default(),
        params: params
            .into_iter()
            .map(|(n, t)| Param {
                name: n.to_owned(),
                ty: Some(t),
                by_ref: false,
                default: None,
                variadic: false,
                span,
            })
            .collect(),
        ret_ty: ret,
        body: None,
        is_async: false,
        is_generator: false,
        throws: ThrowsKind::None,
        where_clause: Vec::new(),
        span,
    };
    // Spec 805: `rok_panic(msg, len) -> !` — message bytes to stderr,
    // exit 101. Codegen-inserted runtime checks call it too.
    let panic_fn = make_fn(
        "rok_panic",
        vec![("msg", path_ty("str")), ("len", path_ty("usize"))],
        None,
    );
    let assert_fn = make_fn(
        "rok_assert",
        vec![("cond", path_ty("i32"))],
        Some(path_ty("i32")),
    );
    let print_str_fn = make_fn(
        "rok_print_str",
        vec![("s", path_ty("str"))],
        Some(path_ty("i32")),
    );
    let print_i32_fn = make_fn(
        "rok_print_i32",
        vec![("n", path_ty("i32"))],
        Some(path_ty("i32")),
    );
    let print_i64_fn = make_fn(
        "rok_print_i64",
        vec![("n", path_ty("i64"))],
        Some(path_ty("i32")),
    );
    // ABI nit: bool/i1 doesn't have a stable C calling convention, so
    // the extern is declared `b: i32` and callers cast `value as i32`.
    let print_bool_fn = make_fn(
        "rok_print_bool",
        vec![("b", path_ty("i32"))],
        Some(path_ty("i32")),
    );
    let print_f64_fn = make_fn(
        "rok_print_f64",
        vec![("d", path_ty("f64"))],
        Some(path_ty("i32")),
    );
    rokc_ast::Item::Extern(ExternBlock {
        attrs: Vec::new(),
        abi: "C".to_owned(),
        items: vec![
            ExternItem::Fn(panic_fn),
            ExternItem::Fn(assert_fn),
            ExternItem::Fn(print_str_fn),
            ExternItem::Fn(print_i32_fn),
            ExternItem::Fn(print_i64_fn),
            ExternItem::Fn(print_bool_fn),
            ExternItem::Fn(print_f64_fn),
        ],
        span,
    })
}

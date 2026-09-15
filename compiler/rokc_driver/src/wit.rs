//! `ffi::wit::import` / `ffi::wit::export` (stdlib 1.8): each module of
//! the program's package holding them gets the WIT bindings
//! `rokc_wit` generates, and the link gets the component's world.

use std::path::Path;

use rokc_ast::{AttrArg, AttrBody, Attribute, ExternItem, Item, Literal};
use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};
use rokc_lexer::Lexer;
use rokc_mir::WitLink;
use rokc_parser::{ExtOps, apply_keywords, parse_program_meta};

use crate::{CfgEnv, MetaCtx, ModItem, UseEntry, flatten_module_items};

/// Replace the `ffi::wit` items of `items` (the package's, by module)
/// with their bindings; the component's link data when there are any.
#[allow(clippy::too_many_arguments)] // the parse context of the package
pub fn expand(
    items: &mut Vec<ModItem>,
    uses: &mut Vec<UseEntry>,
    target: &rokc_mir::TargetSpec,
    cfg_env: &CfgEnv,
    ext: &ExtOps,
    metas: &MetaCtx,
    diags: &mut Vec<RokDiagnostic>,
) -> Option<WitLink> {
    // The `ffi::wit` items by module, in order.
    let mut groups: Vec<(String, Vec<(rokc_wit::Request, Span)>)> = Vec::new();
    items.retain(|(module, item)| {
        let Item::Extern(b) = item else { return true };
        let Some(w) = &b.wit else { return true };
        let dir = rokc_diagnostic::file_path(b.span.file)
            .and_then(|p| Path::new(&p).parent().map(Path::to_path_buf))
            .unwrap_or_default();
        let req = rokc_wit::Request {
            export: w.export,
            paths: w.paths.iter().map(|p| dir.join(p)).collect(),
        };
        match groups.iter_mut().find(|(m, _)| m == module) {
            Some((_, g)) => g.push((req, b.span)),
            None => groups.push((module.clone(), vec![(req, b.span)])),
        }
        false
    });
    if groups.is_empty() {
        return None;
    }
    let mut link = WitLink::default();
    let mut any = false;
    let mut world = String::new();
    for (module, g) in groups {
        let span = g[0].1;
        let requests: Vec<rokc_wit::Request> = g.into_iter().map(|(r, _)| r).collect();
        let fail = |diags: &mut Vec<RokDiagnostic>, msg: String| {
            diags.push(RokDiagnostic::error(ErrorKind::Module, span, msg));
        };
        let loaded = match rokc_wit::load(&requests) {
            Ok(l) => l,
            Err(e) => {
                fail(diags, format!("WIT: {e}"));
                continue;
            }
        };
        // A changed `.wit` file rebuilds (`rokc_interface::fresh`).
        crate::READ.with(|r| {
            r.borrow_mut()
                .extend(loaded.resolve.files.iter().map(|(p, _)| p.clone()));
        });
        let base = if module.is_empty() {
            "pkg".to_owned()
        } else {
            format!("pkg::{module}")
        };
        let b = match rokc_wit::bind(&loaded, &requests, &base) {
            Ok(b) => b,
            Err(e) => {
                fail(diags, format!("WIT: {e}"));
                continue;
            }
        };
        // The WIT is checked for any target; only a component (a WASI
        // preview 2 target) has the core imports and exports the
        // bindings stand for.
        if target.linker != rokc_target::Linker::WasmComponentLd {
            fail(
                diags,
                format!(
                    "`ffi::wit` builds a WebAssembly component: it needs a component target such as \
                     `--target wasm32-wasi`, not {} (stdlib 1.8)",
                    target.name
                ),
            );
            continue;
        }
        let name = format!("<WIT bindings of `{base}`>");
        let file_id = rokc_diagnostic::register_file(name.clone(), b.source.clone());
        let (mut tokens, lex) = Lexer::new(&b.source, name.clone())
            .with_ext_ops(ext.symbols())
            .lex_all();
        for t in &mut tokens {
            t.span.file = file_id;
        }
        diags.extend(lex);
        apply_keywords(&mut tokens, &metas.keywords, diags);
        let (program, parse_diags) = parse_program_meta(
            &tokens,
            name,
            ext,
            &metas.table,
            &metas.literals,
            Some(cfg_env),
        );
        diags.extend(parse_diags);
        let mut generated = program.items;
        mark_imports(&mut generated, &b.imports);
        let path: Vec<String> = if module.is_empty() {
            Vec::new()
        } else {
            module.split("::").map(str::to_owned).collect()
        };
        flatten_module_items(
            generated, &path, None, cfg_env, ext, metas, diags, items, uses, None,
        );
        any = true;
        world.push_str(&b.world);
        for s in loaded.units {
            if !link.sources.contains(&s) {
                link.sources.push(s);
            }
        }
        for e in b.exports {
            if !link.exports.contains(&e) {
                link.exports.push(e);
            }
        }
    }
    if !any {
        return None;
    }
    link.world = format!("package rok:component;\n\nworld component {{\n{world}}}\n");
    Some(link)
}

/// `#wasm_import(module, name)` on each generated extern function.
fn mark_imports(items: &mut [Item], imports: &[(String, String, String)]) {
    for item in items {
        match item {
            Item::Mod(m) => mark_imports(m.items.as_deref_mut().unwrap_or_default(), imports),
            Item::Extern(b) => {
                for ei in &mut b.items {
                    let ExternItem::Fn(f) = ei else { continue };
                    if let Some((_, module, name)) = imports.iter().find(|(n, ..)| *n == f.name) {
                        f.attrs.push(Attribute {
                            path: vec![rokc_ast::WASM_IMPORT_ATTR.to_owned()],
                            body: AttrBody::Args(vec![
                                AttrArg::Lit(Literal::Str(module.clone())),
                                AttrArg::Lit(Literal::Str(name.clone())),
                            ]),
                            inner: false,
                            span: f.span,
                        });
                    }
                }
            }
            _ => {}
        }
    }
}

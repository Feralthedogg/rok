//! The check pipeline (`rokc check`, `rokc lint`, the language server)
//! and the queries the language server and the REPL run on its result.

use std::path::Path;

use rokc_ast::{ImplItem, Item, TraitItem};
use rokc_diagnostic::{RokDiagnostic, Span};
pub use rokc_hir::each_block;
use rokc_hir::{HirExpr, HirFunction, HirModule, HirTy};
use rokc_interface::{BuildOptions, CompileResult, Session, SourceFile};

use crate::lint::{self, Level};

/// Front end, then the lints at `levels`, then with `codegen` MLIR codegen.
///
/// Codegen rejects what the backend cannot lower. `source` stands for the
/// root file's text (`None`: read `path`). The diagnostics are in report
/// order; the result keeps the parsed files.
pub fn check(
    session: &mut Session,
    source: Option<&str>,
    path: &Path,
    levels: &[(Level, String)],
    codegen: Option<&BuildOptions>,
) -> (CompileResult, Vec<RokDiagnostic>) {
    session.set_keep_ast(true);
    let result = match source {
        Some(s) => session.compile_source(s, path),
        None => session.compile_file(path),
    };
    if result.has_errors() {
        let diags = result
            .warnings
            .iter()
            .chain(&result.errors)
            .cloned()
            .collect();
        return (result, diags);
    }
    let mut diags = lint::run(&result, levels);
    if let Some(opts) = codegen {
        diags.extend(result.check_codegen(opts).err());
    }
    (result, diags)
}

/// One check of a buffer.
pub struct Analysis {
    pub diags: Vec<RokDiagnostic>,
    /// The registered files of this compile, `Span::file - 1` indexed.
    pub files: Vec<(String, String)>,
    /// Present when the program type-checked.
    pub hir: Option<HirModule>,
    pub sources: Vec<SourceFile>,
}

/// Check `source` as the root file `path` (no codegen).
pub fn analyze(
    session: &mut Session,
    source: &str,
    path: &Path,
    levels: &[(Level, String)],
) -> Analysis {
    // The file table is global: cleared per compile so a long-lived
    // server does not grow it forever.
    rokc_diagnostic::clear_files();
    let (r, diags) = check(session, Some(source), path, levels, None);
    Analysis {
        diags,
        files: rokc_diagnostic::registered_files(),
        hir: r.modules.into_iter().next().map(|m| m.hir),
        sources: r.sources,
    }
}

impl Analysis {
    /// Path and text of a span's file.
    pub fn file(&self, span: Span) -> Option<&(String, String)> {
        self.files
            .get(usize::try_from(span.file).ok()?.checked_sub(1)?)
    }

    pub(crate) fn in_file(&self, span: Span, path: &str) -> bool {
        self.file(span).is_some_and(|(p, _)| p == path)
    }

    /// The doc comment of the function defined at `span`.
    pub fn fn_doc(&self, span: Span) -> String {
        fn find(items: &[Item], span: Span) -> Option<&[rokc_ast::Attribute]> {
            items.iter().find_map(|item| match item {
                Item::Fn(f) if f.span == span => Some(f.attrs.as_slice()),
                Item::Impl(i) => i.items.iter().find_map(|ii| match ii {
                    ImplItem::Method(m) if m.span == span => Some(m.attrs.as_slice()),
                    _ => None,
                }),
                Item::Trait(t) => t.items.iter().find_map(|ti| match ti {
                    TraitItem::Method(m) if m.span == span => Some(m.attrs.as_slice()),
                    _ => None,
                }),
                Item::Mod(m) => find(m.items.as_deref().unwrap_or_default(), span),
                _ => None,
            })
        }
        self.sources
            .iter()
            .filter(|f| f.file_id == span.file)
            .find_map(|f| find(&f.items, span))
            .map(crate::doc::doc_text)
            .unwrap_or_default()
    }

    /// The doc comment of field `name` of the struct defined at `span`.
    pub fn field_doc(&self, span: Span, name: &str) -> String {
        fn find<'a>(
            items: &'a [Item],
            span: Span,
            name: &str,
        ) -> Option<&'a [rokc_ast::Attribute]> {
            items.iter().find_map(|item| match item {
                Item::Struct(s) if s.span == span => match &s.kind {
                    rokc_ast::StructKind::Named(fs) => fs
                        .iter()
                        .find(|f| f.name == name)
                        .map(|f| f.attrs.as_slice()),
                    _ => None,
                },
                Item::Mod(m) => find(m.items.as_deref().unwrap_or_default(), span, name),
                _ => None,
            })
        }
        self.sources
            .iter()
            .filter(|f| f.file_id == span.file)
            .find_map(|f| find(&f.items, span, name))
            .map(crate::doc::doc_text)
            .unwrap_or_default()
    }

    /// The path a diagnostic belongs to (explicit, else its primary span's).
    pub fn diag_path(&self, d: &RokDiagnostic) -> Option<String> {
        d.file
            .clone()
            .or_else(|| Some(self.file(d.primary.as_ref()?.span)?.0.clone()))
    }

    /// A typed expression of `path` whose span matches `pick`: the
    /// innermost (smallest span, deepest on ties), or with `outer` the
    /// outermost. A compound expression's span is its first token's
    /// (the parser's convention), so equal spans are common.
    pub fn find_expr(
        &self,
        path: &str,
        pick: impl Fn(Span) -> bool,
        outer: bool,
    ) -> Option<&HirExpr> {
        let hir = self.hir.as_ref()?;
        let mut best: Option<&HirExpr> = None;
        let size = |s: Span| s.end.saturating_sub(s.start);
        for f in &hir.functions {
            let Some(body) = &f.body else { continue };
            each_block(body, &mut |e| {
                if !e.span.is_dummy()
                    && self.in_file(e.span, path)
                    && pick(e.span)
                    && !matches!(e.ty, HirTy::Unknown)
                    && best.is_none_or(|b| {
                        if outer {
                            size(e.span) > size(b.span)
                        } else {
                            size(e.span) <= size(b.span)
                        }
                    })
                {
                    best = Some(e);
                }
            });
        }
        best
    }
}

/// User-facing type name (struct / enum by name, generics as `<..>`).
pub fn ty_name(hir: &HirModule, ty: &HirTy) -> String {
    ty_text(hir, ty, false)
}

/// `ty_name` with struct / enum by their full path (`rok::core::..`),
/// which names them from any module without a `use`.
pub fn ty_path(hir: &HirModule, ty: &HirTy) -> String {
    ty_text(hir, ty, true)
}

fn ty_text(hir: &HirModule, ty: &HirTy, full: bool) -> String {
    let rec = |t: &HirTy| ty_text(hir, t, full);
    let list = |ts: &[HirTy]| ts.iter().map(rec).collect::<Vec<_>>().join(", ");
    // Types by their own name (`List<i32>`, not the module path), as
    // the REPL shows them (907.7).
    let generic = |name: &str, args: &[HirTy]| {
        let base = name.split("__").next().unwrap_or(name);
        let base = if full {
            base
        } else {
            base.rsplit("::").next().unwrap_or(base)
        };
        if args.is_empty() {
            base.to_owned()
        } else {
            format!("{base}<{}>", list(args))
        }
    };
    match ty {
        HirTy::Unknown => "{unknown}".to_owned(),
        HirTy::Unit => "()".to_owned(),
        HirTy::Never => "!".to_owned(),
        HirTy::Mlir(t) => format!("__mlir_type<{t:?}>"),
        HirTy::Prim(p) => p.name().to_owned(),
        HirTy::Any => "any".to_owned(),
        HirTy::AnyTrait(b) if b.is_empty() => "any".to_owned(),
        HirTy::AnyTrait(b) if b.len() == 1 => format!("any {}", b[0]),
        HirTy::AnyTrait(b) => format!("any ({})", b.join(" + ")),
        HirTy::Path(p) => p.join("::"),
        HirTy::Sum(_) => ty.sum_name(rec),
        HirTy::Tuple(ts) => format!("({})", list(ts)),
        HirTy::Struct(id) => hir.structs.iter().find(|s| s.id == *id).map_or_else(
            || "{struct}".to_owned(),
            |s| generic(&s.name, &s.generic_args),
        ),
        HirTy::Enum(id) => hir.enums.iter().find(|e| e.id == *id).map_or_else(
            || "{enum}".to_owned(),
            |e| generic(&e.name, &e.generic_args),
        ),
        HirTy::Array(t, n) => format!("[{}; {n}]", rec(t)),
        HirTy::GcBuf(t) => format!("GcBuf<{}>", rec(t)),
        HirTy::Fn(args, ret, _) => format!("fn({}) -> {}", list(args), rec(ret)),
        HirTy::Closure { args, ret, .. } => format!("closure({}) -> {}", list(args), rec(ret)),
        HirTy::Throws { ok, err } => format!("throws ({}) -> {}", rec(err), rec(ok)),
    }
}

/// `fn name(a: T, ..) -> R`.
pub fn signature(hir: &HirModule, f: &HirFunction) -> String {
    let params: Vec<String> = f
        .params
        .iter()
        // `#caller` (`#[track_caller]`) is hidden.
        .filter(|p| !p.name.starts_with('#'))
        .map(|p| format!("{}: {}", p.name, ty_name(hir, &p.ty)))
        .collect();
    format!(
        "fn {}({}) -> {}",
        short_name(&f.name),
        params.join(", "),
        ty_name(hir, &f.ret_ty)
    )
}

/// The name a user writes for a HIR function: the last `::` segment,
/// and the method name of an `<Type>__method` impl function (a
/// dependency's: `<module>::<Type>.method[__by_Trait]`).
pub fn short_name(name: &str) -> &str {
    let last = name.rsplit("::").next().unwrap_or(name);
    if let Some((_, method)) = last.split_once('.') {
        return method.split("__").next().unwrap_or(method);
    }
    last.rsplit("__").next().unwrap_or(last)
}

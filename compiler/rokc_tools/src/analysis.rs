//! Front-end queries shared by the LSP and the REPL: compile a buffer
//! through HIR, then look things up by byte offset in the typed HIR.

use std::path::Path;

use rokc_diagnostic::{RokDiagnostic, Span};
pub use rokc_hir::each_block;
use rokc_hir::{HirExpr, HirFunction, HirModule, HirTy};
use rokc_interface::Session;

/// One compile of a buffer.
pub struct Analysis {
    /// Errors, then warnings.
    pub diags: Vec<RokDiagnostic>,
    /// The registered files of this compile, `Span::file - 1` indexed.
    pub files: Vec<(String, String)>,
    /// Present when the program type-checked.
    pub hir: Option<HirModule>,
}

/// Compile `source` as the root file `path` (front end through HIR + MIR,
/// no codegen).
pub fn analyze(session: &Session, source: &str, path: &Path) -> Analysis {
    // ponytail: one global file table; cleared per compile so a
    // long-lived server does not grow it forever.
    rokc_diagnostic::clear_files();
    let r = session.compile_source(source, path);
    let mut diags = r.errors;
    diags.extend(r.warnings);
    Analysis {
        diags,
        files: rokc_diagnostic::registered_files(),
        hir: r.modules.into_iter().next().map(|m| m.hir),
    }
}

impl Analysis {
    /// Path and text of a span's file.
    pub fn file(&self, span: Span) -> Option<&(String, String)> {
        self.files
            .get(usize::try_from(span.file).ok()?.checked_sub(1)?)
    }

    fn in_file(&self, span: Span, path: &str) -> bool {
        self.file(span).is_some_and(|(p, _)| p == path)
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
        .map(|p| format!("{}: {}", p.name, ty_name(hir, &p.ty)))
        .collect();
    format!(
        "fn {}({}) -> {}",
        f.name,
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

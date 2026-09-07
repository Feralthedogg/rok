//! Entry point rules (spec 4.16): `main.rok` provides either an explicit
//! `fn main` or top-level statements (the implicit `main`), never both.
//! Every other file is definitions-only.

use std::path::Path;

use rokc_ast::{AttrBody, Attribute, Block, FnDef, Generics, Item, Stmt, ThrowsKind, TyKind};
use rokc_diagnostic::{ErrorKind, RokDiagnostic, Span};

/// Marker attribute on the synthesized implicit `main`. `#` cannot start
/// an identifier, so user code can never spell it.
pub const IMPLICIT_MAIN_ATTR: &str = "#implicit_main";

pub fn stmts_outside_entry(file: &Path) -> RokDiagnostic {
    RokDiagnostic::error(
        ErrorKind::Module,
        format!(
            "{}: top-level statements are only allowed in the entry file `main.rok`; \
             modules are definitions-only (spec 4.16.6)",
            file.display()
        ),
    )
}

/// Turn the entry file's top-level statements into the implicit `main`
/// and validate an explicit one.
pub fn resolve_entry(stmts: Vec<Stmt>, items: &mut Vec<Item>, diags: &mut Vec<RokDiagnostic>) {
    let explicit = items.iter().find_map(|i| match i {
        Item::Fn(f) if f.name == "main" => Some(f),
        _ => None,
    });
    match (explicit, stmts.is_empty()) {
        (Some(_), false) => diags.push(RokDiagnostic::error(
            ErrorKind::Module,
            "`main.rok` has both top-level statements and `fn main`; use exactly one \
             entry point (spec 4.16.1)"
                .to_owned(),
        )),
        (Some(f), true) => check_main_signature(f, diags),
        (None, false) => items.push(Item::Fn(implicit_main(stmts))),
        (None, true) => {}
    }
}

fn implicit_main(stmts: Vec<Stmt>) -> FnDef {
    let span = stmts.first().map_or(Span::DUMMY, |s| s.span);
    FnDef {
        vis: rokc_core::Visibility::Private,
        attrs: vec![Attribute {
            path: vec![IMPLICIT_MAIN_ATTR.to_owned()],
            body: AttrBody::Empty,
            inner: false,
            span,
        }],
        name: "main".to_owned(),
        generics: Generics::default(),
        params: Vec::new(),
        ret_ty: None,
        body: Some(Block {
            stmts,
            trailing: None,
            span,
            label: None,
        }),
        // ponytail: spec 4.16.5 makes it `async` when `await` appears at top
        // level; async main needs the scheduler, which the runtime lacks.
        is_async: false,
        is_generator: false,
        throws: ThrowsKind::None,
        where_clause: Vec::new(),
        span,
    }
}

/// Spec 4.16.3: no parameters or generics; returns `()` or `i32`, and may
/// `throws (E)` (an escaping error exits 1, see HIR `uncaught_in_main`).
/// A `Result` return is not an entry form (E4).
// ponytail: `async` main (4.16.5) waits for the scheduler.
fn check_main_signature(f: &FnDef, diags: &mut Vec<RokDiagnostic>) {
    let mut bad = |msg: &str| {
        diags.push(RokDiagnostic::error(
            ErrorKind::Type,
            format!("`fn main`: {msg} (spec 4.16.3)"),
        ));
    };
    if !f.params.is_empty() {
        bad("takes no parameters; read arguments through `rok::std::env`");
    }
    if !f.generics.params.is_empty() {
        bad("cannot be generic");
    }
    if f.is_generator {
        bad("cannot be a generator");
    }
    let ret_ok = match &f.ret_ty {
        None => true,
        Some(t) => match &t.kind {
            TyKind::Path(p) => p.segments.len() == 1 && p.segments[0].name == "i32",
            TyKind::Tuple(elems) => elems.is_empty(),
            _ => false,
        },
    };
    let is_result = f.ret_ty.as_ref().is_some_and(|t| {
        matches!(&t.kind, TyKind::Path(p) if p.segments.last().is_some_and(|s| s.name == "Result"))
    });
    if is_result {
        bad(
            "cannot return `Result`; declare `fn main() throws (E)` so an escaping error \
             exits 1, and call `rok::std::env::exit(code)` for any other exit code",
        );
    } else if !ret_ok {
        bad("must return `()` or `i32`");
    }
}

//! Language server over stdio (JSON-RPC 2.0 with `Content-Length`
//! framing). Full-text sync; every query runs on the last check of the
//! buffer (`analysis::check`: front end and lints, no codegen).

use std::collections::HashMap;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use std::sync::mpsc;

use rokc_ast::{Expr, ExprKind, ImplItem, Item, TraitItem};
use rokc_diagnostic::{RokDiagnostic, Span};
use rokc_hir::walk::{AstVisitor, walk_item, walk_stmt};
use rokc_hir::{HirExprKind, HirModule, HirTy};
use rokc_interface::Session;

use rokc_diagnostic::Json;

use crate::analysis::{Analysis, analyze, short_name, signature, ty_name};
use crate::lint::Level;

struct Doc {
    text: String,
    /// Needs a compile (changed since the last one).
    dirty: bool,
    /// The last compile that type-checked: hover / definition /
    /// completion keep working while the buffer has errors.
    good: Option<Analysis>,
}

struct Server<W> {
    out: W,
    bootstrap: Vec<PathBuf>,
    externs: Vec<(String, PathBuf)>,
    levels: Vec<(Level, String)>,
    docs: HashMap<String, Doc>,
    shutdown: bool,
}

/// Serve requests from `input` until `exit` (or end of input), linting
/// at `levels`. Returns the process exit code: 0 after a `shutdown`,
/// else 1 (LSP spec).
pub fn serve(
    input: impl BufRead + Send + 'static,
    out: impl Write,
    bootstrap: Vec<PathBuf>,
    externs: Vec<(String, PathBuf)>,
    levels: Vec<(Level, String)>,
) -> i32 {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut input = input;
        while let Some(msg) = read_message(&mut input) {
            if tx.send(msg).is_err() {
                break;
            }
        }
    });
    let mut server = Server {
        out,
        bootstrap,
        externs,
        levels,
        docs: HashMap::new(),
        shutdown: false,
    };
    while let Ok(first) = rx.recv() {
        // Handle everything already queued before compiling: a burst
        // of edits costs one compile, not one per keystroke.
        let batch: Vec<Json> = std::iter::once(first).chain(rx.try_iter()).collect();
        for msg in batch {
            if let Some(code) = server.handle(&msg) {
                return code;
            }
        }
        let dirty: Vec<String> = server
            .docs
            .iter()
            .filter(|(_, d)| d.dirty)
            .map(|(u, _)| u.clone())
            .collect();
        for uri in dirty {
            server.refresh(&uri);
        }
    }
    i32::from(!server.shutdown)
}

/// One framed message; `None` at end of input. Unparsable bodies are
/// skipped.
fn read_message(input: &mut impl BufRead) -> Option<Json> {
    loop {
        let mut len = None;
        loop {
            let mut line = String::new();
            if input.read_line(&mut line).ok()? == 0 {
                return None;
            }
            let line = line.trim_end();
            if line.is_empty() {
                break;
            }
            if let Some((k, v)) = line.split_once(':') {
                if k.eq_ignore_ascii_case("content-length") {
                    len = v.trim().parse::<usize>().ok();
                }
            }
        }
        let mut body = vec![0; len?];
        input.read_exact(&mut body).ok()?;
        if let Ok(msg) = Json::parse(&String::from_utf8_lossy(&body)) {
            return Some(msg);
        }
    }
}

impl<W: Write> Server<W> {
    fn send(&mut self, msg: &Json) {
        let body = msg.to_string();
        // A closed client: nothing left to do but stop on the next read.
        let _ = write!(self.out, "Content-Length: {}\r\n\r\n{body}", body.len());
        let _ = self.out.flush();
    }

    fn reply(&mut self, id: &Json, result: Json) {
        self.send(&Json::obj([
            ("jsonrpc", Json::str("2.0")),
            ("id", id.clone()),
            ("result", result),
        ]));
    }

    /// Returns the exit code on `exit`.
    fn handle(&mut self, msg: &Json) -> Option<i32> {
        let method = msg.get("method").as_str().unwrap_or("");
        let id = msg.get("id");
        let params = msg.get("params");
        let uri = params
            .get("textDocument")
            .get("uri")
            .as_str()
            .unwrap_or("")
            .to_owned();
        let result = match method {
            "initialize" => Json::obj([
                (
                    "capabilities",
                    Json::obj([
                        ("textDocumentSync", Json::num(1)),
                        ("hoverProvider", Json::Bool(true)),
                        ("definitionProvider", Json::Bool(true)),
                        ("documentSymbolProvider", Json::Bool(true)),
                        ("documentFormattingProvider", Json::Bool(true)),
                        (
                            "completionProvider",
                            Json::obj([(
                                "triggerCharacters",
                                Json::Arr(vec![Json::str("."), Json::str(":")]),
                            )]),
                        ),
                    ]),
                ),
                (
                    "serverInfo",
                    Json::obj([
                        ("name", Json::str("rokls")),
                        ("version", Json::str(env!("CARGO_PKG_VERSION"))),
                    ]),
                ),
            ]),
            "shutdown" => {
                self.shutdown = true;
                Json::Null
            }
            "exit" => return Some(i32::from(!self.shutdown)),
            "textDocument/didOpen" | "textDocument/didChange" => {
                let text = if method == "textDocument/didOpen" {
                    params.get("textDocument").get("text")
                } else {
                    match params.get("contentChanges") {
                        Json::Arr(cs) => cs.last().map_or(&Json::Null, |c| c.get("text")),
                        _ => &Json::Null,
                    }
                };
                if let Some(text) = text.as_str() {
                    let doc = self.docs.entry(uri).or_insert(Doc {
                        text: String::new(),
                        dirty: true,
                        good: None,
                    });
                    text.clone_into(&mut doc.text);
                    doc.dirty = true;
                }
                return None;
            }
            "textDocument/didClose" => {
                self.docs.remove(&uri);
                self.publish(&uri, Vec::new());
                return None;
            }
            "textDocument/hover"
            | "textDocument/definition"
            | "textDocument/documentSymbol"
            | "textDocument/completion"
            | "textDocument/formatting" => {
                if self.docs.get(&uri).is_some_and(|d| d.dirty) {
                    self.refresh(&uri);
                }
                let pos = params.get("position");
                let line = pos.get("line").as_u32().unwrap_or(0);
                let col = pos.get("character").as_u32().unwrap_or(0);
                self.query(method, &uri, line, col).unwrap_or(Json::Null)
            }
            _ if matches!(id, Json::Null) => return None,
            _ => {
                self.send(&Json::obj([
                    ("jsonrpc", Json::str("2.0")),
                    ("id", id.clone()),
                    (
                        "error",
                        Json::obj([
                            ("code", Json::num(-32601)),
                            (
                                "message",
                                Json::str(format!("unsupported method `{method}`")),
                            ),
                        ]),
                    ),
                ]));
                return None;
            }
        };
        self.reply(id, result);
        None
    }

    fn session(&self, anonymous: bool) -> Session {
        let mut s = Session::new();
        for b in &self.bootstrap {
            s.add_bootstrap_file(b.clone());
        }
        for (n, p) in &self.externs {
            s.add_extern(n.clone(), p.clone());
        }
        s.set_anonymous(anonymous);
        s
    }

    /// Check `text` standing for the buffer `path`: the package root
    /// (902.2) with this buffer's text when it is the root, else the
    /// root as open or on disk; a file outside any package is anonymous.
    /// Unsaved edits of a submodule buffer are not seen (module files are
    /// read from disk).
    fn compile(&self, path: &Path, text: &str) -> Analysis {
        let root = rokc_interface::discover(path)
            .ok()
            .filter(|p| !p.anonymous)
            .and_then(|p| std::path::absolute(&p.root).ok());
        let levels = &self.levels;
        match root {
            Some(root) if root != path => {
                let open = self.docs.get(&path_uri(&root)).map(|d| d.text.clone());
                let root_text = open
                    .or_else(|| std::fs::read_to_string(&root).ok())
                    .unwrap_or_default();
                analyze(&mut self.session(false), &root_text, &root, levels)
            }
            Some(_) => analyze(&mut self.session(false), text, path, levels),
            None => analyze(&mut self.session(true), text, path, levels),
        }
    }

    /// Recompile a buffer and publish its diagnostics.
    fn refresh(&mut self, uri: &str) {
        let Some(doc) = self.docs.get(uri) else {
            return;
        };
        let path = uri_path(uri);
        // A `.rokon` data file (`rok.rokon`, the package manifest) is one
        // RokON value, not a module: only its syntax is checked here.
        if path.extension().is_some_and(|x| x == "rokon") {
            let diags = match rokc_rokon::parse(&doc.text) {
                Ok(_) => Vec::new(),
                Err(e) => {
                    let d = RokDiagnostic::error(rokc_diagnostic::ErrorKind::Parse, &e.message)
                        .with_span(e.span, "");
                    vec![diag_json(&d, &doc.text)]
                }
            };
            self.docs.get_mut(uri).expect("checked above").dirty = false;
            self.publish(uri, diags);
            return;
        }
        let a = self.compile(&path, &doc.text);
        let key = path.display().to_string();
        let diags = a
            .diags
            .iter()
            .filter(|d| a.diag_path(d).is_none_or(|p| p == key))
            .map(|d| {
                let span = d.primary.as_ref().map(|l| l.span).unwrap_or_default();
                diag_json(d, a.file(span).map_or("", |(_, t)| t.as_str()))
            })
            .collect();
        let doc = self.docs.get_mut(uri).expect("checked above");
        doc.dirty = false;
        if a.hir.is_some() {
            doc.good = Some(a);
        }
        self.publish(uri, diags);
    }

    fn publish(&mut self, uri: &str, diags: Vec<Json>) {
        self.send(&Json::obj([
            ("jsonrpc", Json::str("2.0")),
            ("method", Json::str("textDocument/publishDiagnostics")),
            (
                "params",
                Json::obj([("uri", Json::str(uri)), ("diagnostics", Json::Arr(diags))]),
            ),
        ]));
    }

    fn query(&self, method: &str, uri: &str, line: u32, col: u32) -> Option<Json> {
        let doc = self.docs.get(uri)?;
        let text = doc.text.as_str();
        let path = uri_path(uri);
        let key = path.display().to_string();
        let off = offset(text, line, col);
        match method {
            "textDocument/formatting" => {
                let new = rokc_fmt::format_file(&path, text).ok()?;
                Some(Json::Arr(if new == text {
                    Vec::new()
                } else {
                    vec![Json::obj([
                        ("range", range(text, 0, text.len())),
                        ("newText", Json::Str(new)),
                    ])]
                }))
            }
            "textDocument/documentSymbol" => {
                let program = parse_doc(text, &key);
                Some(Json::Arr(
                    program
                        .items
                        .iter()
                        .filter_map(|i| symbol(i, text))
                        .collect(),
                ))
            }
            "textDocument/hover" => {
                let a = doc.good.as_ref()?;
                let value = hover(a, &key, text, off)?;
                Some(Json::obj([(
                    "contents",
                    Json::obj([("kind", Json::str("markdown")), ("value", Json::str(value))]),
                )]))
            }
            "textDocument/definition" => {
                let (ident, _) = ident_at(text, off)?;
                // A local: resolve through the scopes of the buffer's AST.
                let mut v = Locals {
                    off,
                    scopes: vec![Vec::new()],
                    found: None,
                };
                let program = parse_doc(text, &key);
                walk_items(&mut v, &program.items);
                program.stmts.iter().for_each(|s| walk_stmt(&mut v, s));
                if let Some(span) = v.found {
                    return Some(location(uri, text, span));
                }
                let a = doc.good.as_ref()?;
                let span = definition(a, &key, ident, off)?;
                let (p, t) = a.file(span)?;
                Some(location(&path_uri(Path::new(p)), t, span))
            }
            "textDocument/completion" => Some(Json::Arr(self.complete(doc, &path, off))),
            _ => None,
        }
    }

    fn complete(&self, doc: &Doc, path: &Path, off: usize) -> Vec<Json> {
        let text = doc.text.as_str();
        let key = path.display().to_string();
        let line_start = text[..off].rfind('\n').map_or(0, |i| i + 1);
        let before = &text[line_start..off];
        let head = before.trim_end_matches(is_ident_char);
        let partial = &before[head.len()..];
        let item = |label: &str, kind: u32, detail: String| {
            Json::obj([
                ("label", Json::str(label)),
                ("kind", Json::num(kind)),
                ("detail", Json::Str(detail)),
            ])
        };
        let mut out: Vec<Json> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut push = |label: &str, kind: u32, detail: String| {
            if label.starts_with(partial) && seen.insert(label.to_owned()) {
                out.push(item(label, kind, detail));
            }
        };
        if head.ends_with('.') && !head.ends_with("..") {
            // Type the receiver: recompile without `.partial` and take
            // the outermost expression starting where the receiver does.
            let dot = line_start + head.len() - 1;
            let start = receiver_start(text, dot);
            // At a line end the receiver ends a statement: close it.
            let rest = &text[off..];
            let at_end = rest.split('\n').next().is_some_and(|l| l.trim().is_empty());
            let edited = format!("{}{}{rest}", &text[..dot], if at_end { ";" } else { "" });
            let fresh = self.compile(path, &edited);
            let starts = |s: Span| s.start as usize == start;
            let found = fresh
                .find_expr(&key, starts, true)
                .map(|e| (&fresh, e.ty.clone()))
                .or_else(|| {
                    let a = doc.good.as_ref()?;
                    Some((a, a.find_expr(&key, starts, true)?.ty.clone()))
                });
            let Some((a, ty)) = found else {
                return out;
            };
            let hir = a.hir.as_ref().expect("find_expr needs HIR");
            if let HirTy::Struct(id) = &ty {
                if let Some(s) = hir.structs.iter().find(|s| s.id == *id) {
                    for f in &s.fields {
                        push(&f.name, 5, ty_name(hir, &f.ty));
                    }
                }
            }
            for f in &hir.functions {
                if f.params
                    .first()
                    .is_some_and(|p| p.name == "self" && p.ty == ty)
                {
                    push(short_name(&f.name), 2, signature(hir, f));
                }
            }
        } else if let Some(prefix) = head.strip_suffix("::") {
            let start = prefix
                .rfind(|c: char| !(is_ident_char(c) || c == ':'))
                .map_or(0, |i| i + 1);
            let segs: Vec<&str> = prefix[start..].split("::").collect();
            // Item names only: the last good compile has them (the
            // buffer with a dangling `a::` does not compile).
            let Some(hir) = doc.good.as_ref().and_then(|a| a.hir.as_ref()) else {
                return out;
            };
            path_completions(hir, &segs, &mut push);
        }
        out
    }
}

/// `a::b::` → the next segments of every item path under it, plus the
/// associated functions / variants of a type named by the path.
fn path_completions(hir: &HirModule, segs: &[&str], push: &mut impl FnMut(&str, u32, String)) {
    let n = segs.len();
    let mut names: Vec<(&str, u32)> = Vec::new();
    names.extend(
        hir.functions
            .iter()
            .filter(|f| !f.name.contains("__") && !f.name.contains('.'))
            .map(|f| (f.name.as_str(), 3)),
    );
    names.extend(hir.structs.iter().map(|s| (s.name.as_str(), 22)));
    names.extend(hir.enums.iter().map(|e| (e.name.as_str(), 13)));
    for (name, kind) in names {
        let name = name.split("__").next().unwrap_or(name);
        let parts: Vec<&str> = name.split("::").collect();
        if parts.len() > n && parts[..n] == *segs {
            let more = parts.len() > n + 1;
            push(parts[n], if more { 9 } else { kind }, name.to_owned());
        }
    }
    // `Type::` — its impl functions are named `<key>__<method>`.
    let last = segs[n - 1];
    let mut keys = vec![last.to_owned()];
    for s in &hir.structs {
        if short_name(&s.name) == last || s.name.rsplit("::").next() == Some(last) {
            keys.push(format!("Struct{}", s.id.0));
        }
    }
    for e in &hir.enums {
        if e.name.rsplit("::").next() == Some(last) {
            keys.push(format!("Enum{}", e.id.0));
            for v in &e.variants {
                push(&v.name, 20, e.name.clone());
            }
        }
    }
    for f in &hir.functions {
        if let Some((key, method)) = f.name.split_once("__") {
            if keys.iter().any(|k| k == key) {
                push(method, 3, signature(hir, f));
            }
        }
        // A dependency's method: `<module>::<Type>.<method>`.
        if let Some((ty, _)) = f.name.rsplit("::").next().and_then(|l| l.split_once('.')) {
            if ty == last {
                push(short_name(&f.name), 3, signature(hir, f));
            }
        }
    }
}

/// Hover markdown: the code in a `rok` fence, then a function's doc
/// text from its `#[doc]` attributes (spec 1.2).
fn hover(a: &Analysis, key: &str, text: &str, off: usize) -> Option<String> {
    let hir = a.hir.as_ref()?;
    let fenced = |code: String| format!("```rok\n{code}\n```");
    let with_doc = |f: &rokc_hir::HirFunction| {
        let doc = a.fn_doc(f.span);
        let code = fenced(signature(hir, f));
        if doc.is_empty() {
            code
        } else {
            format!("{code}\n\n{doc}")
        }
    };
    let ident = ident_at(text, off).map(|(s, _)| s);
    if let Some(e) = a.find_expr(
        key,
        |s| (s.start as usize..s.end as usize).contains(&off),
        false,
    ) {
        if let HirExprKind::Call { callee, .. } | HirExprKind::FnRef(callee) = &e.kind {
            let f = hir.functions.iter().find(|f| f.id == *callee)?;
            if ident == Some(short_name(&f.name)) {
                return Some(with_doc(f));
            }
        }
        let ty = ty_name(hir, &e.ty);
        let src = text.get(e.span.start as usize..e.span.end as usize);
        return Some(fenced(match ident {
            Some(name) if src == Some(name) => format!("{name}: {ty}"),
            _ => ty,
        }));
    }
    // A binding site (`let x`, a parameter) has no expression: the
    // buffer's locals and items of that name.
    let name = ident?;
    let doc_fns = hir
        .functions
        .iter()
        .filter(|f| a.file(f.span).is_some_and(|(p, _)| p == key));
    for f in doc_fns {
        if short_name(&f.name) == name {
            return Some(with_doc(f));
        }
        if let Some(l) = f.locals.iter().find(|l| l.name.as_deref() == Some(name)) {
            return Some(fenced(format!("{name}: {}", ty_name(hir, &l.ty))));
        }
    }
    None
}

/// Where the item under the cursor is defined (functions, types).
fn definition(a: &Analysis, key: &str, ident: &str, off: usize) -> Option<Span> {
    let hir = a.hir.as_ref()?;
    let fn_span = |id| hir.functions.iter().find(|f| f.id == id).map(|f| f.span);
    let struct_span = |id| hir.structs.iter().find(|s| s.id == id).map(|s| s.span);
    let at = a.find_expr(
        key,
        |s| (s.start as usize..s.end as usize).contains(&off),
        false,
    );
    let hit =
        at.and_then(|e| match &e.kind {
            HirExprKind::Call { callee, .. } | HirExprKind::FnRef(callee) => fn_span(*callee)
                .filter(|_| {
                    hir.functions
                        .iter()
                        .any(|f| f.id == *callee && short_name(&f.name) == ident)
                }),
            HirExprKind::StructInit { struct_id, .. }
            | HirExprKind::FieldRead { struct_id, .. } => struct_span(*struct_id),
            HirExprKind::EnumVariantInit { enum_id, .. } => {
                hir.enums.iter().find(|e| e.id == *enum_id).map(|e| e.span)
            }
            _ => None,
        });
    let real = |s: &Span| !s.is_dummy() && a.file(*s).is_some();
    hit.filter(real).or_else(|| {
        // By name: functions, then types.
        let fns = hir
            .functions
            .iter()
            .filter(|f| short_name(&f.name) == ident)
            .map(|f| f.span);
        let types = hir
            .structs
            .iter()
            .filter(|s| short_name(&s.name) == ident)
            .map(|s| s.span)
            .chain(
                hir.enums
                    .iter()
                    .filter(|e| short_name(&e.name) == ident)
                    .map(|e| e.span),
            );
        fns.chain(types).filter(real).min_by_key(|s| {
            // Prefer the buffer itself.
            a.file(*s).is_none_or(|(p, _)| p != key)
        })
    })
}

/// Scope walk of the buffer's AST: the binding a one-segment path at
/// `off` refers to.
struct Locals {
    off: usize,
    scopes: Vec<Vec<(String, Span)>>,
    found: Option<Span>,
}

impl AstVisitor for Locals {
    fn expr(&mut self, e: &Expr) {
        if let ExprKind::Path(p) = &e.kind {
            if let [seg] = p.segments.as_slice() {
                if (e.span.start as usize..=e.span.end as usize).contains(&self.off) {
                    let hit = self
                        .scopes
                        .iter()
                        .rev()
                        .flat_map(|s| s.iter().rev())
                        .find(|(n, _)| *n == seg.name);
                    if let Some((_, span)) = hit {
                        self.found = Some(*span);
                    }
                }
            }
        }
    }
    fn bind_at(&mut self, name: &str, at: Span) {
        if let Some(s) = self.scopes.last_mut() {
            s.push((name.to_owned(), at));
        }
    }
    fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }
    fn pop_scope(&mut self) {
        self.scopes.pop();
    }
}

fn walk_items(v: &mut Locals, items: &[Item]) {
    for item in items {
        match item {
            Item::Mod(m) => walk_items(v, m.items.as_deref().unwrap_or(&[])),
            item => walk_item(v, item),
        }
    }
}

/// LSP `Diagnostic` of `d`, whose span is in `text`.
fn diag_json(d: &RokDiagnostic, text: &str) -> Json {
    let span = d.primary.as_ref().map(|l| l.span).unwrap_or_default();
    let mut message = d.message.clone();
    for n in &d.notes {
        message.push_str("\nnote: ");
        message.push_str(n);
    }
    Json::obj([
        ("range", range(text, span.start as usize, span.end as usize)),
        ("severity", Json::num(if d.is_error() { 1 } else { 2 })),
        ("code", Json::str(d.kind.code())),
        ("source", Json::str("rokc")),
        ("message", Json::str(message)),
    ])
}

/// The buffer alone, parsed for its shape (no library operators).
fn parse_doc(text: &str, file: &str) -> rokc_ast::Program {
    let (tokens, _) = rokc_lexer::Lexer::new(text, file.to_owned()).lex_all();
    rokc_parser::parse_program(&tokens, file).0
}

/// LSP `DocumentSymbol` of an item.
fn symbol(item: &Item, text: &str) -> Option<Json> {
    let fn_sym = |f: &rokc_ast::FnDef, kind: u32| sym(&f.name, kind, f.span, text, Vec::new());
    let (name, kind, children): (String, u32, Vec<Json>) = match item {
        Item::Fn(f) => return Some(fn_sym(f, 12)),
        Item::Struct(s) => (s.name.clone(), 23, Vec::new()),
        Item::Union(u) => (u.name.clone(), 23, Vec::new()),
        Item::Enum(e) => (e.name.clone(), 10, Vec::new()),
        Item::Trait(t) => (
            t.name.clone(),
            11,
            t.items
                .iter()
                .filter_map(|i| match i {
                    TraitItem::Method(f) => Some(fn_sym(f, 6)),
                    _ => None,
                })
                .collect(),
        ),
        Item::Impl(i) => {
            // `impl Tr for T` as written, up to the body. A derive's
            // generated impl (its span is the attribute's) is no symbol.
            let head = text.get(i.span.start as usize..)?;
            if !(head.starts_with("impl") || head.starts_with("unsafe")) {
                return None;
            }
            let head = head.split('{').next().unwrap_or(head);
            (
                head.split_whitespace().collect::<Vec<_>>().join(" "),
                5,
                i.items
                    .iter()
                    .filter_map(|i| match i {
                        ImplItem::Method(f) => Some(fn_sym(f, 6)),
                        _ => None,
                    })
                    .collect(),
            )
        }
        Item::Const(c) => (c.name.clone(), 14, Vec::new()),
        Item::Static(s) => (s.name.clone(), 13, Vec::new()),
        Item::TypeAlias(t) => (t.name.clone(), 26, Vec::new()),
        Item::Mod(m) => (
            m.name.clone(),
            2,
            m.items
                .iter()
                .flatten()
                .filter_map(|i| symbol(i, text))
                .collect(),
        ),
        Item::Use(_) | Item::Extern(_) => return None,
    };
    Some(sym(&name, kind, item.span(), text, children))
}

fn sym(name: &str, kind: u32, span: Span, text: &str, children: Vec<Json>) -> Json {
    let r = range(text, span.start as usize, span.end as usize);
    Json::obj([
        ("name", Json::str(name)),
        ("kind", Json::num(kind)),
        ("range", r.clone()),
        ("selectionRange", r),
        ("children", Json::Arr(children)),
    ])
}

fn location(uri: &str, text: &str, span: Span) -> Json {
    Json::obj([
        ("uri", Json::str(uri)),
        ("range", range(text, span.start as usize, span.end as usize)),
    ])
}

fn is_ident_char(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

/// Where the receiver of the `.` at `dot` starts: back over a chain of
/// identifiers, `.`, `::` and bracketed groups (`a.b(x)[0].`).
fn receiver_start(text: &str, dot: usize) -> usize {
    let b = text.as_bytes();
    let (mut i, mut depth) = (dot, 0u32);
    while i > 0 {
        let c = b[i - 1];
        match c {
            b')' | b']' => depth += 1,
            b'(' | b'[' if depth > 0 => depth -= 1,
            _ if depth > 0 => {}
            _ if c.is_ascii_alphanumeric() || c >= 0x80 || b"_.:".contains(&c) => {}
            _ => break,
        }
        i -= 1;
    }
    i
}

/// The identifier around byte `off` and its start.
fn ident_at(text: &str, off: usize) -> Option<(&str, usize)> {
    let off = off.min(text.len());
    let start = text[..off]
        .rfind(|c: char| !is_ident_char(c))
        .map_or(0, |i| {
            i + text[i..].chars().next().map_or(1, char::len_utf8)
        });
    let end = text[off..]
        .find(|c: char| !is_ident_char(c))
        .map_or(text.len(), |i| off + i);
    let s = &text[start..end];
    (!s.is_empty() && !s.starts_with(|c: char| c.is_ascii_digit())).then_some((s, start))
}

/// Byte offset of an LSP position (UTF-16 columns).
fn offset(text: &str, line: u32, col: u32) -> usize {
    let start = if line == 0 {
        0
    } else {
        text.match_indices('\n')
            .nth(line as usize - 1)
            .map_or(text.len(), |(i, _)| i + 1)
    };
    let mut units = 0;
    for (i, c) in text[start..].char_indices() {
        if units >= col as usize || c == '\n' {
            return start + i;
        }
        units += c.len_utf16();
    }
    text.len()
}

/// LSP position of a byte offset.
fn position(text: &str, off: usize) -> Json {
    let mut off = off.min(text.len());
    while !text.is_char_boundary(off) {
        off -= 1;
    }
    let before = &text[..off];
    let line = before.matches('\n').count();
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    let col: usize = before[line_start..].chars().map(char::len_utf16).sum();
    Json::obj([
        ("line", Json::num(line as u32)),
        ("character", Json::num(col as u32)),
    ])
}

fn range(text: &str, start: usize, end: usize) -> Json {
    Json::obj([
        ("start", position(text, start)),
        ("end", position(text, end.max(start))),
    ])
}

fn uri_path(uri: &str) -> PathBuf {
    let Some(rest) = uri.strip_prefix("file://") else {
        return PathBuf::from(uri);
    };
    let bytes = rest.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let hex = bytes
            .get(i + 1..i + 3)
            .and_then(|h| std::str::from_utf8(h).ok())
            .and_then(|h| u8::from_str_radix(h, 16).ok());
        match (bytes[i], hex) {
            (b'%', Some(b)) => {
                out.push(b);
                i += 3;
            }
            (b, _) => {
                out.push(b);
                i += 1;
            }
        }
    }
    PathBuf::from(String::from_utf8_lossy(&out).into_owned())
}

fn path_uri(path: &Path) -> String {
    let mut out = String::from("file://");
    for b in path.display().to_string().bytes() {
        if b.is_ascii_alphanumeric() || b"/-_.~".contains(&b) {
            out.push(b as char);
        } else {
            out.push_str(&format!("%{b:02X}"));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn positions_round_trip_utf16() {
        let text = "ab\né😀x\n";
        let x = text.find('x').unwrap();
        assert_eq!(
            position(text, x),
            Json::obj([("line", Json::num(1)), ("character", Json::num(3))])
        );
        assert_eq!(offset(text, 1, 3), x);
        assert_eq!(offset(text, 9, 0), text.len());
        assert_eq!(ident_at("let foo = 1", 5), Some(("foo", 4)));
        assert_eq!(ident_at("a + 12", 5), None);
        let s = "x = 1 + a.b(f(c))[0].";
        assert_eq!(receiver_start(s, s.len() - 1), s.find('a').unwrap());
        let p = Path::new("/tmp/a b/é.rok");
        assert_eq!(uri_path(&path_uri(p)), p);
    }
}

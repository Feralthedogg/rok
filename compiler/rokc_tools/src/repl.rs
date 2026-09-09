//! `repl`: an interactive session without a JIT engine (906).
//!
//! The session is one anonymous `main.rok` (907.1: a run of cells is
//! the implicit `main.rok` with top-level statements and items appended).
//!
//! Default mode: a long-lived host process (`repl_host.c`, the runtime
//! linked in, initialized once) loads each cell as a shared library and
//! runs it once. Items (`fn`, `struct`, `impl`, ..) are recompiled into
//! every cell; statements are not. A top-level binding lives in an
//! exported global slot (a GC root) the defining cell owns; later cells
//! declare it `extern "C" { static mut .. }` with its type as written
//! and copy it into a local of the same name on entry (and back out on
//! exit, so assignments persist). A cell that dies (panic) leaves the
//! session as it was before it: the host forks a snapshot per cell.
//!
//! `--replay` mode: each input recompiles the whole program, links it,
//! and runs it; the output of the new cell is what follows a marker the
//! cell prints first. Earlier cells run again: their side effects (I/O,
//! time, randomness) repeat. It keeps bindings whose types cannot be
//! named in source (closures, ..), which the default mode refuses.

use std::collections::HashSet;
use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};

use rokc_hir::{HirExpr, HirExprKind, HirModule, HirStmt, HirTy};
use rokc_interface::{
    BuildOptions, CompileResult, EmitKind, ReplCell, Session, TempDir, link_host, report,
};

use crate::analysis::ty_name;

const OUT_MARK: &str = "@@rok-repl-out@@";
const VAL_MARK: &str = "@@rok-repl-val@@";
const VALUE: &str = "__rok_repl_v";
/// The host's `__rok_repl_out`: a cell's shown value.
const SHOWN: &str = "__rok_repl_out";
const HOST_C: &str = include_str!("repl_host.c");
const DYLIB: &str = if cfg!(target_vendor = "apple") {
    "dylib"
} else {
    "so"
};

const HELP: &str = "\
  <expr>         evaluate and print `type: value`
  let x = ..;    bind (a top-level `let` may rebind a name, 907.3)
  fn / struct / enum / impl / trait / use ..   define (a new `fn f` /
                 `struct S` replaces the old one)
  :type <expr>   print the type of an expression
  :add <name> --path <dir> | --git <url> [--rev|--tag|--branch <r>]
                 add a dependency to the active environment (`rok repl`)
  :reset         forget every cell
  :quit          leave (also end of input)
";

/// The cells so far, as source.
#[derive(Clone, Default)]
struct State {
    /// Items with their replace key (`fn f`, `struct S`; `None` for impls).
    items: Vec<(Option<String>, String)>,
    /// Top-level statements; a rebinding `let` opens a nested block.
    stmts: String,
    depth: usize,
    /// Names `let`-bound at the innermost block.
    names: HashSet<String>,
}

enum Cell<'a> {
    Item(Option<String>),
    /// `let <name> ..;` (the name when it is a plain binding).
    Let(Option<&'a str>),
    Stmt,
    Expr,
}

#[derive(PartialEq, Eq)]
enum Outcome {
    Ok,
    CompileError,
    RunError,
}

impl State {
    /// The session program with `cell` appended to the statements.
    fn program(&self, cell: &str) -> String {
        let mut src = String::new();
        for (_, item) in &self.items {
            src.push_str(item);
            src.push('\n');
        }
        src.push_str(&self.stmts);
        src.push_str(cell);
        src.push('\n');
        src.push_str(&"}\n".repeat(self.depth));
        src
    }
}

/// A top-level binding (default mode).
#[derive(Clone)]
struct Binding {
    name: String,
    /// The exported global holding its value.
    sym: String,
    /// Its type, as source.
    ty: String,
}

/// The session host (`repl_host.c`) and its command socket.
struct Host {
    child: Child,
    ctl: UnixStream,
}

impl Drop for Host {
    fn drop(&mut self) {
        let _ = self.ctl.shutdown(std::net::Shutdown::Both);
        let _ = self.child.wait();
    }
}

pub struct Repl {
    bootstrap: Vec<PathBuf>,
    /// Dependencies (`--extern name=root`).
    pub externs: Vec<(String, PathBuf)>,
    /// `--replay`: every cell reruns the whole session.
    pub replay: bool,
    opts: BuildOptions,
    state: State,
    host: Option<Host>,
    bindings: Vec<Binding>,
    /// Cells built (library and slot names).
    built: u32,
    /// GC type ids earlier cells took.
    type_offset: u32,
    tmp: TempDir,
}

impl Repl {
    pub fn new(bootstrap: Vec<PathBuf>, opts: BuildOptions) -> Result<Self, String> {
        Ok(Self {
            bootstrap,
            externs: Vec::new(),
            replay: false,
            tmp: TempDir::new(opts.keep_temps).map_err(|d| d.message)?,
            opts,
            state: State::default(),
            host: None,
            bindings: Vec::new(),
            built: 0,
            type_offset: 0,
        })
    }

    /// Read cells from `input` until `:quit` or its end. `interactive`
    /// shows the `>` / `...` prompts.
    pub fn run(&mut self, input: impl BufRead, interactive: bool) {
        let prompt = |cont: bool| {
            if interactive {
                print!("{}", if cont { "... " } else { "> " });
                let _ = std::io::stdout().flush();
            }
        };
        let mut buf = String::new();
        prompt(false);
        for line in input.lines() {
            let Ok(line) = line else { break };
            buf.push_str(&line);
            buf.push('\n');
            if incomplete(&buf) {
                prompt(true);
                continue;
            }
            let cell = std::mem::take(&mut buf);
            if !self.cell(cell.trim()) {
                return;
            }
            prompt(false);
        }
        if interactive {
            println!();
        }
    }

    /// One input; `false` to stop.
    pub fn cell(&mut self, cell: &str) -> bool {
        match cell {
            "" => {}
            ":q" | ":quit" | ":exit" => return false,
            ":reset" => {
                self.state = State::default();
                self.bindings.clear();
            }
            ":help" | ":h" => print!("{HELP}"),
            _ if cell.starts_with(":type ") || cell.starts_with(":t ") => {
                let expr = cell.split_once(' ').map_or("", |(_, e)| e).trim();
                let src =
                    self.session(&self.state, &format!("let {VALUE} = ({expr});"), None, None);
                if let Some(ty) = self
                    .compile(&src, false)
                    .and_then(|r| binding_ty(&r, VALUE))
                {
                    println!("{ty}");
                }
            }
            _ if cell.starts_with(":add ") => self.add_dep(&cell[5..]),
            _ if cell.starts_with(':') => eprintln!("unknown command `{cell}` (:help lists them)"),
            _ => match classify(cell) {
                Cell::Item(key) => self.item(cell, key),
                Cell::Let(name) if !self.replay => self.run_once(cell, name),
                Cell::Stmt if !self.replay => self.run_once(cell, None),
                Cell::Expr if !self.replay => {
                    self.run_once(&format!("let {VALUE} = ({cell});"), Some(VALUE));
                }
                Cell::Let(name) => {
                    // 907.3: rebinding a name at the top level opens a
                    // block, so the old binding is shadowed instead of
                    // redeclared (5.1.4).
                    let mut next = self.state.clone();
                    if name.is_some_and(|n| next.names.contains(n)) {
                        next.depth += 1;
                        next.names.clear();
                        next.stmts.push_str("{\n");
                    }
                    if self.run_cell(&next, cell, name) {
                        next.stmts.push_str(cell);
                        next.stmts.push('\n');
                        next.names.extend(name.map(str::to_owned));
                        self.state = next;
                    }
                }
                Cell::Stmt => {
                    if self.run_cell(&self.state, cell, None) {
                        self.state.stmts.push_str(cell);
                        self.state.stmts.push('\n');
                    }
                }
                Cell::Expr => {
                    let bind = format!("let {VALUE} = ({cell});");
                    if self.run_cell(&self.state, &bind, Some(VALUE)) {
                        // Later runs evaluate it again, without showing it.
                        self.state.stmts.push_str(&format!("({cell});\n"));
                    }
                }
            },
        }
        true
    }

    /// `:add <args>`: `$ROK add [--env $ROK_ENV] <args>` (the `rok`
    /// that started this session), then reload the dependency list from
    /// `$ROK deps`.
    fn add_dep(&mut self, args: &str) {
        let Some(rok) = std::env::var_os("ROK") else {
            eprintln!("`:add` needs a session started by `rok repl`");
            return;
        };
        let env: Vec<String> = std::env::var("ROK_ENV")
            .ok()
            .filter(|e| !e.is_empty())
            .map(|e| vec!["--env".to_owned(), e])
            .unwrap_or_default();
        let run = |cmd: &str, extra: &[&str]| {
            Command::new(&rok)
                .arg(cmd)
                .args(&env)
                .args(extra)
                .stderr(std::process::Stdio::inherit())
                .output()
                .ok()
                .filter(|o| o.status.success())
        };
        let words: Vec<&str> = args.split_whitespace().collect();
        if run("add", &words).is_none() {
            return;
        }
        let Some(out) = run("deps", &[]) else { return };
        self.externs = String::from_utf8_lossy(&out.stdout)
            .lines()
            .filter_map(|l| l.split_once('='))
            .map(|(n, p)| (n.to_owned(), PathBuf::from(p)))
            .collect();
    }

    fn item(&mut self, cell: &str, key: Option<String>) {
        // A new definition replaces the old one of the same name.
        let mut next = self.state.clone();
        next.items.retain(|(k, _)| key.is_none() || *k != key);
        next.items.push((key.clone(), cell.to_owned()));
        let Some(r) = self.compile(&self.session(&next, "", None, None), false) else {
            return;
        };
        // Codegen too, like `check`: it rejects what cannot be lowered.
        if let Err(d) = r.emit(EmitKind::Mlir, &self.opts) {
            report(&d);
            return;
        }
        // A binding of a redefined type would be read with the new
        // layout: forget it.
        let old = key.as_deref().filter(|k| {
            !k.starts_with("fn ")
                && self
                    .state
                    .items
                    .iter()
                    .any(|(o, _)| o.as_deref() == Some(k))
        });
        if let Some(ty) = old.and_then(|k| k.split(' ').nth(1)) {
            self.bindings.retain(|b| {
                let keep = !b
                    .ty
                    .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                    .any(|w| w == ty);
                if !keep {
                    eprintln!("note: `{}` is gone: its type `{ty}` was redefined", b.name);
                }
                keep
            });
        }
        self.state = next;
    }

    /// The source of a cell: the replayed session (`--replay`), or the
    /// items, the bindings' slots, `body`, and (unless `new` is `None`:
    /// a front-end pass) the stores of the bindings back to their slots
    /// (`new`: the cell's own) and of `show`'s `Debug` text to the host.
    fn session(
        &self,
        state: &State,
        body: &str,
        new: Option<&[Binding]>,
        show: Option<&str>,
    ) -> String {
        if self.replay {
            return state.program(body);
        }
        let mut src = String::new();
        for (_, item) in &state.items {
            src.push_str(item);
            src.push('\n');
        }
        let _ = writeln!(src, "extern \"C\" {{\n    static mut {SHOWN}: str;");
        for b in self.bindings.iter().chain(new.unwrap_or_default()) {
            let _ = writeln!(src, "    static mut {}: {};", b.sym, b.ty);
        }
        src.push_str("}\n");
        for b in &self.bindings {
            let _ = writeln!(src, "let {} = {};", b.name, b.sym);
        }
        // Its own block: a `let` may rebind a name (907.3, 5.1.4).
        src.push_str("{\n");
        src.push_str(body);
        src.push('\n');
        let Some(new) = new else {
            src.push_str("}\n");
            return src;
        };
        // ponytail: every binding goes back (a `let` can be assigned);
        // only the ones the cell assigns would need to.
        for b in &self.bindings {
            if !new.iter().any(|n| n.name == b.name) {
                let _ = writeln!(src, "{} = {};", b.sym, b.name);
            }
        }
        for b in new {
            let _ = writeln!(src, "{} = {};", b.sym, b.name);
        }
        if let Some(n) = show {
            let _ = writeln!(src, "{SHOWN} = f\"{{{n}:?}}\";");
        }
        src.push_str("}\n");
        src
    }

    /// Default mode: build `cell` as a library, run it in the host, keep
    /// its top-level bindings and show `type: value` of `show`.
    fn run_once(&mut self, cell: &str, show: Option<&str>) {
        // The new bindings' names and types: a front-end pass first (not
        // needed without a `let`, nor for the value of an expression).
        let user = cell
            .strip_prefix(&format!("let {VALUE} = "))
            .unwrap_or(cell);
        let new = if user.contains("let") {
            let src = self.session(&self.state, cell, None, None);
            let Some(r) = self.compile(&src, false) else {
                return;
            };
            match self.new_bindings(&r) {
                Ok(new) => new,
                Err(e) => {
                    eprintln!("error: {e}");
                    return;
                }
            }
        } else {
            Vec::new()
        };
        let mut shown = show.is_some();
        let r = loop {
            let src = self.session(&self.state, cell, Some(&new), show.filter(|_| shown));
            match self.compile(&src, shown) {
                Some(r) => break r,
                // Most likely no `Debug`; the plain build reports real errors.
                None if shown => shown = false,
                None => {
                    if !new.is_empty() {
                        eprintln!(
                            "note: a later cell names each binding's type; `rokc repl --replay` \
                             keeps bindings whose type cannot be named"
                        );
                    }
                    return;
                }
            }
        };
        self.built += 1;
        let lib = self.tmp.path().join(format!("cell{}.{DYLIB}", self.built));
        let mut opts = self.opts.clone();
        opts.repl = Some(ReplCell {
            type_offset: self.type_offset,
            define: new.iter().map(|b| b.sym.clone()).collect(),
        });
        match r.link_shared(&opts, &lib) {
            Ok(n) => self.type_offset += n,
            Err(d) => {
                report(&d);
                return;
            }
        }
        let Some(value) = self.load(&lib) else {
            return;
        };
        self.bindings
            .retain(|b| !new.iter().any(|n| n.name == b.name));
        self.bindings.extend(new);
        if let Some(ty) = show.and_then(|n| binding_ty(&r, n)) {
            if ty == "()" {
            } else if shown {
                println!("{ty}: {value}");
            } else {
                println!("{ty}");
            }
        }
        let _ = std::io::stdout().flush();
    }

    /// The `let`s at the top of the cell's block in a front-end result
    /// (`session`): the last one of each name.
    fn new_bindings(&self, r: &CompileResult) -> Result<Vec<Binding>, String> {
        let Some(hir) = r.modules.first().map(|m| &m.hir) else {
            return Ok(Vec::new());
        };
        let Some(main) = hir.functions.iter().find(|f| f.name == "main") else {
            return Ok(Vec::new());
        };
        // The cell's block (`session`).
        let Some(block) = main
            .body
            .iter()
            .flat_map(|b| &b.stmts)
            .find_map(|s| match s {
                HirStmt::Expr(HirExpr {
                    kind: HirExprKind::Block(b),
                    ..
                }) => Some(b),
                _ => None,
            })
        else {
            return Ok(Vec::new());
        };
        let lets = block.stmts.iter().filter_map(|s| match s {
            HirStmt::Let { local, .. } => Some(*local),
            _ => None,
        });
        let mut out: Vec<Binding> = Vec::new();
        for (i, id) in lets.enumerate() {
            let Some(l) = main.locals.iter().find(|l| l.id == id) else {
                continue;
            };
            let Some(name) = l
                .name
                .as_deref()
                .filter(|n| !n.starts_with("__") && *n != "_")
            else {
                continue;
            };
            let ty = ty_name(hir, &l.ty);
            // ponytail: what the HIR printer cannot write as source
            // (closures, unresolved types) is refused; `--replay` keeps it.
            if ty.contains('{') || ty.starts_with("closure") {
                return Err(format!(
                    "`{name}: {ty}` cannot be kept for later cells (its type has no name); \
                     `rokc repl --replay` keeps it"
                ));
            }
            out.retain(|b| b.name != name);
            out.push(Binding {
                name: name.to_owned(),
                sym: format!("__rok_repl_{}_{i}", self.built + 1),
                ty,
            });
        }
        Ok(out)
    }

    /// Run the library `lib` in the host (started on first use): the
    /// shown value, or `None` when the cell failed.
    fn load(&mut self, lib: &std::path::Path) -> Option<String> {
        if self.host.is_none() {
            self.host = Some(self.start_host()?);
        }
        let host = self.host.as_mut()?;
        let _ = std::io::stdout().flush();
        let reply = (|| {
            writeln!(host.ctl, "{}", lib.display())?;
            let mut rd = BufReader::new(&host.ctl);
            let mut line = String::new();
            rd.read_line(&mut line)?;
            let Some(n) = line.strip_prefix("ok ") else {
                return Ok(line);
            };
            let mut value = vec![0; n.trim().parse().unwrap_or(0)];
            rd.read_exact(&mut value)?;
            Ok::<_, std::io::Error>(format!("ok {}", String::from_utf8_lossy(&value)))
        })();
        match reply {
            Ok(r) if r.starts_with("ok ") => Some(r[3..].to_owned()),
            Ok(r) if r == "err\n" => {
                eprintln!("error: the cell failed; the session is as it was before it");
                None
            }
            _ => {
                eprintln!("error: the session host is gone; the bindings are lost");
                self.host = None;
                self.bindings.clear();
                None
            }
        }
    }

    /// Build and start the session host.
    fn start_host(&self) -> Option<Host> {
        let src = self.tmp.path().join("host.c");
        let exe = self.tmp.path().join("host");
        if let Err(e) = std::fs::write(&src, HOST_C) {
            eprintln!("error: cannot write {}: {e}", src.display());
            return None;
        }
        if let Err(d) = link_host(&src, &self.opts, &exe) {
            report(&d);
            return None;
        }
        let (ctl, theirs) = match UnixStream::pair() {
            Ok(p) => p,
            Err(e) => {
                eprintln!("error: cannot make the host socket: {e}");
                return None;
            }
        };
        match Command::new(&exe)
            .stdin(Stdio::from(OwnedFd::from(theirs)))
            .spawn()
        {
            Ok(child) => Some(Host { child, ctl }),
            Err(e) => {
                eprintln!("error: cannot run {}: {e}", exe.display());
                None
            }
        }
    }

    /// Run `cell` after the statements of `base`, showing `type: value`
    /// of the binding `show` (without the value when it has no `Debug`).
    fn run_cell(&self, base: &State, cell: &str, show: Option<&str>) -> bool {
        let marked = format!("println(\"{OUT_MARK}\");\neprintln(\"{OUT_MARK}\");\n{cell}");
        if let Some(n) = show {
            let src = base.program(&format!(
                "{marked}\nprintln(\"{VAL_MARK}\");\nprintln(f\"{{{n}:?}}\");"
            ));
            match self.execute(&src, show, true) {
                Outcome::Ok => return true,
                Outcome::RunError => return false,
                // Most likely no `Debug`; the plain run reports real errors.
                Outcome::CompileError => {}
            }
        }
        self.execute(&base.program(&marked), show, false) == Outcome::Ok
    }

    /// Front end; reports errors unless `quiet`.
    fn compile(&self, src: &str, quiet: bool) -> Option<CompileResult> {
        let mut s = Session::new();
        for b in &self.bootstrap {
            s.add_bootstrap_file(b.clone());
        }
        for (n, p) in &self.externs {
            s.add_extern(n.clone(), p.clone());
        }
        s.set_anonymous(true);
        rokc_diagnostic::clear_files();
        let r = s.compile_source(src, &self.tmp.path().join("repl.rok"));
        if !r.has_errors() {
            return Some(r);
        }
        if !quiet {
            r.report_errors();
        }
        None
    }

    /// Compile, link and run `src`; print the new cell's output and
    /// `type: value` of `name`.
    fn execute(&self, src: &str, name: Option<&str>, quiet: bool) -> Outcome {
        let Some(r) = self.compile(src, quiet) else {
            return Outcome::CompileError;
        };
        let exe = self.tmp.path().join("repl");
        if let Err(d) = r.link(&self.opts, &exe) {
            report(&d);
            return Outcome::CompileError;
        }
        let out = match Command::new(&exe).output() {
            Ok(o) => o,
            Err(e) => {
                eprintln!("error: cannot run {}: {e}", exe.display());
                return Outcome::RunError;
            }
        };
        let mark = format!("{OUT_MARK}\n");
        let after = |b: &[u8]| {
            let s = String::from_utf8_lossy(b).into_owned();
            s.split_once(&mark)
                .map_or_else(String::new, |(_, t)| t.to_owned())
        };
        let stdout = after(&out.stdout);
        let (printed, value) = match stdout.split_once(&format!("{VAL_MARK}\n")) {
            Some((p, v)) => (p, Some(v.trim_end_matches('\n'))),
            None => (stdout.as_str(), None),
        };
        print!("{printed}");
        eprint!("{}", after(&out.stderr));
        if !out.status.success() {
            // ponytail: replaying a failing cell would fail every later
            // run, so unlike 907.5 the cell is dropped.
            eprintln!("error: the cell failed ({}); it is not kept", out.status);
            return Outcome::RunError;
        }
        if let Some(ty) = name.and_then(|n| binding_ty(&r, n)) {
            match value {
                Some(_) if ty == "()" => {}
                Some(v) => println!("{ty}: {v}"),
                None if ty != "()" => println!("{ty}"),
                None => {}
            }
        }
        let _ = std::io::stdout().flush();
        Outcome::Ok
    }
}

/// The type of the last top-level binding `name` of `main`, as written.
fn binding_ty(r: &CompileResult, name: &str) -> Option<String> {
    let hir: &HirModule = &r.modules.first()?.hir;
    let main = hir.functions.iter().find(|f| f.name == "main")?;
    let local = main
        .locals
        .iter()
        .rev()
        .find(|l| l.name.as_deref() == Some(name))?;
    Some(match &local.ty {
        HirTy::Unit => "()".to_owned(),
        t => ty_name(hir, t),
    })
}

fn classify(cell: &str) -> Cell<'_> {
    // Leading attributes belong to the item after them.
    let mut rest = cell;
    while rest.starts_with("#[") {
        let Some(end) = matching(rest, 1) else { break };
        rest = rest[end + 1..].trim_start();
    }
    let words: Vec<&str> = rest
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|w| !w.is_empty())
        .take(4)
        .collect();
    let first = words.first().copied().unwrap_or("");
    let item_kw = [
        "fn", "struct", "enum", "union", "trait", "impl", "use", "mod", "type", "const", "static",
        "extern", "pub", "async", "unsafe",
    ];
    if item_kw.contains(&first) && !(first == "unsafe" && rest[6..].trim_start().starts_with('{')) {
        // `fn f` / `struct S` / `pub fn f` name what a redefinition replaces.
        let named = words.windows(2).find(|w| {
            [
                "fn", "struct", "enum", "union", "trait", "type", "const", "static",
            ]
            .contains(&w[0])
        });
        return Cell::Item(named.map(|w| format!("{} {}", w[0], w[1])));
    }
    if first == "let" {
        let name = match words.get(1) {
            Some(&"mut") => words.get(2).copied(),
            n => n.copied(),
        };
        // A pattern (`let (a, b) = ..`) binds no single name.
        let plain = rest[3..]
            .trim_start()
            .starts_with(|c: char| c.is_alphanumeric() || c == '_');
        return Cell::Let(name.filter(|_| plain));
    }
    if cell.ends_with(';') {
        Cell::Stmt
    } else {
        Cell::Expr
    }
}

/// Byte index of the bracket closing the one at `open`.
fn matching(s: &str, open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices().skip(open) {
        match c {
            '[' | '(' | '{' => depth += 1,
            ']' | ')' | '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// The input needs more lines: open brackets / string, or a dangling
/// operator or `let` (907.8 `...` continuation).
fn incomplete(src: &str) -> bool {
    let mut depth = 0i32;
    let mut chars = src.chars().peekable();
    let mut in_str = false;
    while let Some(c) = chars.next() {
        if in_str {
            match c {
                '\\' => {
                    chars.next();
                }
                '"' => in_str = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => in_str = true,
            '/' if chars.peek() == Some(&'/') => {
                // Line comment.
                for c in chars.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
    }
    let t = src.trim_end();
    let dangling = [
        "=", "+", "-", "*", "/", ",", ".", "&&", "||", "->", "=>", "|",
    ]
    .iter()
    .any(|op| t.ends_with(op));
    in_str
        || depth > 0
        || (dangling && !t.is_empty())
        || (t.starts_with("let ") && !t.ends_with(';') && !t.ends_with('}'))
        // Attributes wait for their item.
        || (t.starts_with("#[") && t.lines().all(|l| l.trim_start().starts_with("#[")))
}

/// `rok repl` with the stdin it was started on.
pub fn main(
    bootstrap: Vec<PathBuf>,
    externs: Vec<(String, PathBuf)>,
    opts: BuildOptions,
    interactive: bool,
    replay: bool,
) -> i32 {
    match Repl::new(bootstrap, opts) {
        Ok(mut r) => {
            r.externs = externs;
            r.replay = replay;
            r.run(std::io::stdin().lock(), interactive);
            0
        }
        Err(e) => {
            eprintln!("error: {e}");
            1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cells_classify_and_continue() {
        assert!(matches!(classify("1 + 2"), Cell::Expr));
        assert!(matches!(classify("println(\"x\");"), Cell::Stmt));
        assert!(matches!(classify("let mut x = 1;"), Cell::Let(Some("x"))));
        assert!(matches!(classify("let (a, b) = (1, 2);"), Cell::Let(None)));
        assert!(
            matches!(classify("#[derive(Debug)]\nstruct P { x: i32; }"), Cell::Item(Some(k)) if k == "struct P")
        );
        assert!(matches!(classify("pub fn f() {}"), Cell::Item(Some(k)) if k == "fn f"));
        assert!(matches!(classify("impl P {}"), Cell::Item(None)));
        assert!(incomplete("let x =\n"));
        assert!(incomplete("fn f() {\n"));
        assert!(incomplete("#[derive(Debug)]\n"));
        assert!(incomplete("let s = \"a\n"));
        assert!(!incomplete("let x =\n42i32;\n"));
        assert!(!incomplete("f(\"(\")\n"));
    }
}

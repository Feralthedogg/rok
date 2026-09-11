//! `repl`: an interactive session on a JIT (906).
//!
//! The session is one anonymous `main.rok` (907.1: a run of cells is
//! the implicit `main.rok` with top-level statements and items appended).
//!
//! rokc compiles each cell to LLVM IR text (`mlir-opt | mlir-translate`;
//! rokc links no LLVM, 0.2.4) and sends it to a long-lived host process
//! (`repl_host.c`: the runtime linked in and initialized once, and
//! LLVM's ORC JIT through the LLVM-C API), which JIT-compiles it and
//! runs it once. Items (`fn`, `struct`, `impl`, ..) are in every cell's
//! program; statements are not. A function the host already compiled
//! with the same text (library code, unchanged items) is only declared
//! (`ReplCell::known`), so library code is compiled once per session.
//! A top-level binding lives in an exported global slot (a GC root) the
//! defining cell owns; later cells declare it `extern "C" { static mut
//! .. }` with its type as written and copy it into a local of the same
//! name on entry (and back out on exit, so assignments persist). A cell
//! that dies (panic) leaves the session as it was before it: the host
//! forks a snapshot per cell.
//!
//! `--replay` mode: each input recompiles the whole program and the
//! host runs it in a throwaway child; the output of the new cell is
//! what follows a marker the cell prints first. Earlier cells run
//! again: their side effects (I/O, time, randomness) repeat. It keeps
//! bindings whose types cannot be named in source (closures, ..), which
//! the default mode refuses.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use rokc_hir::{HirExpr, HirExprKind, HirModule, HirStaticDef, HirStmt, HirTy};
use rokc_interface::{
    BuildOptions, CompileResult, EmitKind, ReplCell, ReplFn, Session, TempDir, link_host, report,
};
use rokc_ir_common::{ConstVal, LocalId};

use crate::analysis::{ty_name, ty_path};

const OUT_MARK: &str = "@@rok-repl-out@@";
const VAL_MARK: &str = "@@rok-repl-val@@";
const VALUE: &str = "__rok_repl_v";
/// The host's `__rok_repl_out`: a cell's shown value.
const SHOWN: &str = "__rok_repl_out";
const HOST_C: &str = include_str!("repl_host.c");

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

/// `ROK_REPL_TIME=1`: each phase of a cell's build on stderr.
struct Lap(Option<std::time::Instant>);

impl Lap {
    fn start() -> Self {
        Self(
            std::env::var_os("ROK_REPL_TIME")
                .is_some_and(|v| !v.is_empty() && v != "0")
                .then(std::time::Instant::now),
        )
    }

    fn note(&self, what: &str) {
        if self.0.is_some() {
            eprintln!("[repl] {what}");
        }
    }

    fn mark(&mut self, what: &str) {
        if let Some(t) = &mut self.0 {
            eprintln!("[repl] {what}: {:.1}ms", t.elapsed().as_secs_f64() * 1e3);
            *t = std::time::Instant::now();
        }
    }
}

/// The host's reply to a cell: its shown value, or `None` when it
/// failed (reported; the session is as before it).
type Loaded = Option<String>;

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
    /// It holds an `any` value (whose type a redefinition may change).
    holds_any: bool,
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
    /// Dependencies (`--extern name=<name>.rhir`).
    pub externs: Vec<(String, PathBuf)>,
    /// Where `:add` prebuilds dependencies.
    pub deps_dir: PathBuf,
    /// The dependency archives the host has linked.
    linked: HashSet<PathBuf>,
    /// `--replay`: every cell reruns the whole session.
    pub replay: bool,
    /// The first cell (`repl --package`: `use <pkg>::*;`); `:reset`
    /// runs it again.
    pub prelude: Option<String>,
    opts: BuildOptions,
    state: State,
    host: Option<Host>,
    /// The host being built while the first cell compiles.
    starting: Option<std::thread::JoinHandle<Option<Host>>>,
    bindings: Vec<Binding>,
    /// Statics (MIR names) a loaded cell defined: later cells use its
    /// storage (`ReplCell::statics`), so their state carries over.
    statics: HashSet<String>,
    /// Types loaded cells stored into `any` slots: every cell stores
    /// them too (`any_seeds`), so its `any` methods know them all (the
    /// tags are the same in every cell: a hash of the type's name).
    any_types: std::collections::BTreeSet<String>,
    /// Cells built (slot names).
    built: u32,
    /// The `ScanTable`s loaded cells registered (`ReplCell::gc_tables`).
    gc_tables: Vec<Vec<u32>>,
    /// Functions the host has compiled: symbol → (text hash, symbols it
    /// uses). A cell whose function has the same text declares it
    /// instead of compiling it again (`ReplCell::known`).
    known: HashMap<String, (u64, Vec<String>)>,
    tmp: TempDir,
    /// The host process running the current cell (0: none). `SIGINT`
    /// to it ends the cell; the session goes on as before it.
    pub running: Arc<AtomicU32>,
}

impl Repl {
    pub fn new(bootstrap: Vec<PathBuf>, opts: BuildOptions) -> Result<Self, String> {
        Ok(Self {
            bootstrap,
            externs: Vec::new(),
            deps_dir: PathBuf::new(),
            linked: HashSet::new(),
            replay: false,
            prelude: None,
            tmp: TempDir::new(opts.keep_temps).map_err(|d| d.message)?,
            opts,
            state: State::default(),
            host: None,
            starting: None,
            bindings: Vec::new(),
            statics: HashSet::new(),
            any_types: std::collections::BTreeSet::new(),
            built: 0,
            gc_tables: Vec::new(),
            known: HashMap::new(),
            running: Arc::default(),
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
                self.statics.clear();
                self.any_types.clear();
                if let Some(p) = self.prelude.clone() {
                    self.cell(&p);
                }
            }
            ":help" | ":h" => print!("{HELP}"),
            _ if cell.starts_with(":type ") || cell.starts_with(":t ") => {
                let expr = cell.split_once(' ').map_or("", |(_, e)| e).trim();
                let src = self.session(&self.state, &format!("let {VALUE} = ({expr});"), None);
                if let Some(ty) = self
                    .compile(&src, false)
                    .and_then(|r| binding_ty(&r, VALUE))
                {
                    println!("{ty}");
                }
            }
            _ if cell.starts_with(":add ") => self.add_dep(&cell[5..]),
            _ if cell.starts_with(':') => eprintln!("unknown command `{cell}` (:help lists them)"),
            _ if !self.replay => {
                if let Ok(Some(shown)) = self.eval(cell) {
                    println!("{shown}");
                }
            }
            _ => match classify(cell) {
                Cell::Item(key) => {
                    self.item(cell, key);
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
                    if self.run_cell(&self.state.clone(), cell, None) {
                        self.state.stmts.push_str(cell);
                        self.state.stmts.push('\n');
                    }
                }
                Cell::Expr => {
                    let bind = format!("let {VALUE} = ({cell});");
                    if self.run_cell(&self.state.clone(), &bind, Some(VALUE)) {
                        // Later runs evaluate it again, without showing it.
                        self.state.stmts.push_str(&format!("({cell});\n"));
                    }
                }
            },
        }
        true
    }

    /// One cell in the default mode (not `--replay`): what it shows
    /// (`type: value`, or the type alone), or `Err` when it failed (the
    /// errors went to stderr). Output of the cell goes to stdout / stderr.
    // The errors are reported as they happen: nothing more to carry.
    #[allow(clippy::result_unit_err)]
    pub fn eval(&mut self, cell: &str) -> Result<Option<String>, ()> {
        match classify(cell) {
            Cell::Item(key) => self.item(cell, key).then_some(None).ok_or(()),
            Cell::Let(name) => self.run_once(cell, name),
            Cell::Stmt => self.run_once(cell, None),
            Cell::Expr => self.run_once(&format!("let {VALUE} = ({cell});"), Some(VALUE)),
        }
    }

    /// The names the session defines: bindings, then items.
    pub fn names(&self) -> Vec<&str> {
        let items = self.state.items.iter();
        let items = items.filter_map(|(k, _)| k.as_deref()?.split(' ').nth(1));
        self.bindings
            .iter()
            .map(|b| b.name.as_str())
            .chain(items)
            .collect()
    }

    /// `:add <args>`: `$ROK add [--env $ROK_ENV] <args>` (the `rok`
    /// that started this session), then prebuild the dependency list of
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
        let deps: Vec<(String, PathBuf)> = String::from_utf8_lossy(&out.stdout)
            .lines()
            .filter_map(|l| l.split_once('='))
            .map(|(n, p)| (n.to_owned(), PathBuf::from(p)))
            .collect();
        let build = rokc_interface::DepBuild {
            bootstrap: &self.bootstrap,
            cfg: &[],
            opts: &self.opts,
            target: None,
            dir: &self.deps_dir,
            quiet: true,
        };
        match build.prebuild(&deps) {
            Ok(externs) => self.externs = externs,
            Err(e) => eprintln!("error: {e}"),
        }
    }

    fn item(&mut self, cell: &str, key: Option<String>) -> bool {
        // A new definition replaces the old one of the same name.
        let mut next = self.state.clone();
        next.items.retain(|(k, _)| key.is_none() || *k != key);
        next.items.push((key.clone(), cell.to_owned()));
        let Some(r) = self.compile(&self.session(&next, "", None), false) else {
            return false;
        };
        // Codegen too, like `check`: it rejects what cannot be lowered.
        if let Err(d) = r.emit(EmitKind::Mlir, &self.opts) {
            report(&d);
            return false;
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
                } else if b.holds_any {
                    // It may hold an old `{ty}`, which the new
                    // one's tag would claim; keeping the ones that cannot
                    // needs the value's tag.
                    eprintln!(
                        "note: `{}` is gone: it holds an `any` value and `{ty}` was redefined",
                        b.name
                    );
                    return false;
                }
                keep
            });
        }
        // A redefined static starts over: the next cell defines it anew.
        if let Some(name) = key.as_deref().and_then(|k| k.strip_prefix("static ")) {
            let lib = |s: &str| {
                s.starts_with("rok::")
                    || self
                        .externs
                        .iter()
                        .any(|(n, _)| s.starts_with(&format!("{n}::")))
            };
            self.statics
                .retain(|s| lib(s) || s.rsplit("::").next() != Some(name));
        }
        self.state = next;
        true
    }

    /// The source of a cell: the replayed session (`--replay`), or the
    /// items, the bindings' slots, `body`, and the store of `show`'s
    /// `Debug` text to the host. `keep` adds the stores of the bindings
    /// back to their slots to the compiled HIR.
    fn session(&self, state: &State, body: &str, show: Option<&str>) -> String {
        if self.replay {
            return state.program(body);
        }
        let mut src = String::new();
        for (_, item) in &state.items {
            src.push_str(item);
            src.push('\n');
        }
        // Every type earlier cells stored in `any` slots: stored here too.
        for (i, t) in self.any_types.iter().enumerate() {
            let _ = writeln!(src, "fn __rok_repl_any_{i}(x: {t}) -> any {{ return x; }}");
        }
        let _ = writeln!(src, "extern \"C\" {{\n    static mut {SHOWN}: str;");
        for b in &self.bindings {
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
        if let Some(n) = show {
            let _ = writeln!(src, "{SHOWN} = f\"{{{n}:?}}\";");
        }
        src.push_str("}\n");
        src
    }

    /// Default mode: build `cell` as a library, run it in the host, keep
    /// its top-level bindings; `type: value` of `show` (`eval`).
    fn run_once(&mut self, cell: &str, show: Option<&str>) -> Result<Option<String>, ()> {
        self.start_host();
        let mut lap = Lap::start();
        let mut shown = show.is_some();
        let mut r = loop {
            let src = self.session(&self.state, cell, show.filter(|_| shown));
            match self.compile(&src, shown) {
                Some(r) => break r,
                // Most likely no `Debug`; the plain build reports real errors.
                None if shown => shown = false,
                None => return Err(()),
            }
        };
        lap.mark("front end");
        let new = match self.keep(&mut r) {
            Ok(new) => new,
            Err(e) => {
                eprintln!("error: {e}");
                return Err(());
            }
        };
        lap.mark("bindings");
        self.built += 1;
        let mut opts = self.opts.clone();
        // `-g` cells compile everything (their text carries
        // locations, which differ from cell to cell anyway).
        let known = if opts.debug {
            HashMap::new()
        } else {
            self.known
                .iter()
                .map(|(k, (h, _))| (k.clone(), *h))
                .collect()
        };
        opts.repl = Some(ReplCell {
            gc_tables: self.gc_tables.clone(),
            known,
            define: new.iter().map(|b| b.sym.clone()).collect(),
            statics: self.statics.iter().cloned().collect(),
        });
        let (ir, out) = match r.cell_ir(&opts) {
            Ok(x) => x,
            Err(d) => {
                report(&d);
                return Err(());
            }
        };
        lap.mark("mlir-opt | mlir-translate");
        lap.note(&format!(
            "functions: {} compiled, {} from earlier cells",
            out.fns.len(),
            out.reused
        ));
        self.link_archives(&r);
        let value = self.load("cell", &ir);
        lap.mark("jit + run");
        let value = value.ok_or(())?;
        self.gc_tables = out.gc_tables;
        self.learn(out.fresh, out.fns);
        self.bindings
            .retain(|b| !new.iter().any(|n| n.name == b.name));
        self.bindings.extend(new);
        if let Some(m) = r.modules.first() {
            let defined = m.mir.statics.iter().filter(|s| !s.is_extern);
            self.statics.extend(defined.map(|s| s.name.clone()));
            // Names a later cell writes at its top level: visible there.
            let visible = |t: &&String| {
                t.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == ':'))
                    .all(|p| p.is_empty() || rokc_hir::type_visible(&m.hir, p, ""))
            };
            let stored = m.hir.any_types.iter().filter(visible);
            self.any_types.extend(stored.cloned());
        }
        Ok(show
            .and_then(|n| binding_ty(&r, n))
            .filter(|ty| ty != "()")
            .map(|ty| if shown { format!("{ty}: {value}") } else { ty }))
    }

    /// The cell's new bindings: the `let`s at the top of its block in
    /// `r` (`session`), the last one of each name. Adds their slots to
    /// the HIR and, at the end of the block, the stores of every
    /// binding back to its slot (a `let` can be assigned).
    fn keep(&self, r: &mut CompileResult) -> Result<Vec<Binding>, String> {
        let Some(hir) = r.modules.first_mut().map(|m| &mut m.hir) else {
            return Ok(Vec::new());
        };
        let Some(main) = hir.functions.iter().position(|f| f.name == "main") else {
            return Ok(Vec::new());
        };
        // The `let`s before the cell's block load the old bindings.
        let mut outer: Vec<LocalId> = Vec::new();
        let mut cell = None;
        for (i, s) in hir.functions[main]
            .body
            .iter()
            .flat_map(|b| &b.stmts)
            .enumerate()
        {
            match s {
                HirStmt::Let { local, .. } => outer.push(*local),
                HirStmt::Expr(HirExpr {
                    kind: HirExprKind::Block(b),
                    ..
                }) => {
                    cell = Some((i, b));
                    break;
                }
                _ => {}
            }
        }
        let Some((at, block)) = cell else {
            return Ok(Vec::new());
        };
        let locals = &hir.functions[main].locals;
        let local = |id: LocalId| locals.iter().find(|l| l.id == id);
        let named = |id: LocalId| {
            local(id)?
                .name
                .as_deref()
                .filter(|n| !n.starts_with("__") && *n != "_")
        };
        let lets = block.stmts.iter().filter_map(|s| match s {
            HirStmt::Let { local, .. } => Some(*local),
            _ => None,
        });
        let mut new: Vec<(Binding, LocalId)> = Vec::new();
        for (i, id) in lets.enumerate() {
            let (Some(name), Some(l)) = (named(id), local(id)) else {
                continue;
            };
            // What the HIR printer cannot write as source
            // (closures, unresolved types) is refused; `--replay` keeps it.
            // Full paths, so later cells name the type without a `use`.
            let ty = ty_path(hir, &l.ty);
            if ty.contains('{') || ty.starts_with("closure") {
                return Err(format!(
                    "`{name}: {}` cannot be kept for later cells (its type has no name); \
                     `rokc repl --replay` keeps it",
                    ty_name(hir, &l.ty)
                ));
            }
            let holds_any = holds_any(hir, &l.ty, &mut Vec::new());
            // The next cell writes `ty` at the top level of the session:
            // every type it names must be visible there (spec 5.6).
            let hidden = ty
                .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == ':'))
                .find(|p| !rokc_hir::type_visible(hir, p, ""));
            if let Some(p) = hidden {
                return Err(format!(
                    "`{name}: {}` cannot be kept for later cells (`{p}` is private to its \
                     module); `rokc repl --replay` keeps it",
                    ty_name(hir, &l.ty)
                ));
            }
            new.retain(|(b, _)| b.name != name);
            let sym = format!("__rok_repl_{}_{i}", self.built + 1);
            let name = name.to_owned();
            new.push((
                Binding {
                    name,
                    sym,
                    ty,
                    holds_any,
                },
                id,
            ));
        }
        // Every binding goes back (a `let` can be assigned);
        // only the ones the cell assigns would need to.
        let old = self
            .bindings
            .iter()
            .filter(|b| !new.iter().any(|(n, _)| n.name == b.name))
            .filter_map(|b| {
                let id = outer.iter().rev().find(|&&id| named(id) == Some(&b.name))?;
                Some((b.sym.clone(), *id))
            });
        let stores: Vec<HirStmt> = old
            .chain(new.iter().map(|(b, id)| (b.sym.clone(), *id)))
            .filter_map(|(name, id)| {
                let ty = local(id)?.ty.clone();
                let kind = HirExprKind::Local(id);
                let span = rokc_diagnostic::Span::DUMMY;
                Some(HirStmt::StaticAssign {
                    name,
                    value: HirExpr { kind, ty, span },
                })
            })
            .collect();
        let slots: Vec<HirStaticDef> = new
            .iter()
            .filter_map(|(b, id)| {
                Some(HirStaticDef {
                    name: b.sym.clone(),
                    ty: local(*id)?.ty.clone(),
                    init: ConstVal::Unit,
                    is_mut: true,
                    is_extern: true,
                    init_fn: None,
                    span: rokc_diagnostic::Span::DUMMY,
                })
            })
            .collect();
        hir.statics.extend(slots);
        let body = hir.functions[main].body.as_mut();
        if let Some(HirStmt::Expr(e)) = body.and_then(|b| b.stmts.get_mut(at)) {
            if let HirExprKind::Block(b) = &mut e.kind {
                if let Some(t) = b.trailing.take() {
                    b.stmts.push(HirStmt::Expr(t));
                    e.ty = HirTy::Unit;
                }
                b.stmts.extend(stores);
            }
        }
        r.relower();
        Ok(new.into_iter().map(|(b, _)| b).collect())
    }

    /// Build and start the host in the background (the first cell
    /// compiles meanwhile).
    fn start_host(&mut self) {
        if self.host.is_none() && self.starting.is_none() {
            let (dir, opts) = (self.tmp.path().to_owned(), self.opts.clone());
            self.starting = Some(std::thread::spawn(move || start_host(&dir, &opts)));
        }
    }

    /// The host now has `fns`; `fresh` (symbols the cell defined anew)
    /// replaced earlier definitions, so what was compiled against those
    /// (and what uses that, ..) is no longer the same code.
    fn learn(&mut self, fresh: Vec<String>, fns: Vec<ReplFn>) {
        let mut gone: HashSet<String> = fresh.into_iter().collect();
        loop {
            let stale: Vec<String> = self
                .known
                .iter()
                .filter(|(_, (_, refs))| refs.iter().any(|r| gone.contains(r)))
                .map(|(k, _)| k.clone())
                .collect();
            if stale.is_empty() {
                break;
            }
            for k in stale {
                self.known.remove(&k);
                gone.insert(k);
            }
        }
        for f in fns {
            self.known.insert(f.name, (f.hash, f.refs));
        }
    }

    /// The host, started on first use.
    fn host(&mut self) -> Option<&mut Host> {
        if self.host.is_none() {
            self.host = match self.starting.take() {
                Some(h) => h.join().ok().flatten(),
                None => start_host(self.tmp.path(), &self.opts),
            };
        }
        self.host.as_mut()
    }

    /// Link the prebuilt dependencies `r` uses into the host, once each.
    fn link_archives(&mut self, r: &CompileResult) {
        let archives = r.modules.first().map_or(&[][..], |m| &m.archives[..]);
        for a in archives {
            if self.linked.contains(a) {
                continue;
            }
            let Some(host) = self.host() else { return };
            let path = a.display().to_string();
            let reply = (|| {
                writeln!(host.ctl, "lib {}", path.len())?;
                host.ctl.write_all(path.as_bytes())?;
                let mut line = String::new();
                BufReader::new(&host.ctl).read_line(&mut line)?;
                Ok::<_, std::io::Error>(line)
            })();
            if reply.is_ok_and(|l| l.starts_with("ok")) {
                self.linked.insert(a.clone());
            } else {
                eprintln!("error: cannot link {path} into the session");
            }
        }
    }

    /// Send the host (started on first use) `<head> <len>` and the
    /// cell's LLVM IR; its shown value.
    fn load(&mut self, head: &str, ir: &[u8]) -> Loaded {
        self.host()?;
        let host = self.host.as_mut()?;
        let _ = std::io::stdout().flush();
        let reply = (|| {
            let (word, rest) = head.split_once(' ').unwrap_or((head, ""));
            writeln!(host.ctl, "{word} {} {rest}", ir.len())?;
            host.ctl.write_all(ir)?;
            let mut rd = BufReader::new(&host.ctl);
            let mut line = String::new();
            // `pid <n>`: the process the cell runs in.
            rd.read_line(&mut line)?;
            let pid = line
                .strip_prefix("pid ")
                .and_then(|p| p.trim().parse().ok());
            self.running.store(pid.unwrap_or(0), Ordering::Relaxed);
            line.clear();
            rd.read_line(&mut line)?;
            self.running.store(0, Ordering::Relaxed);
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
                if head == "cell" {
                    eprintln!("error: the cell failed; the session is as it was before it");
                }
                None
            }
            _ => {
                eprintln!("error: the session host is gone; the bindings are lost");
                self.host = None;
                self.linked.clear();
                self.bindings.clear();
                self.statics.clear();
                self.any_types.clear();
                self.gc_tables.clear();
                self.known.clear();
                None
            }
        }
    }

    /// Run `cell` after the statements of `base`, showing `type: value`
    /// of the binding `show` (without the value when it has no `Debug`).
    fn run_cell(&mut self, base: &State, cell: &str, show: Option<&str>) -> bool {
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
        s.set_cache_library(true);
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

    /// Compile `src` and run it in a throwaway child of the host (its
    /// JIT, nothing kept); print the new cell's output and `type: value`
    /// of `name`.
    fn execute(&mut self, src: &str, name: Option<&str>, quiet: bool) -> Outcome {
        self.start_host();
        let Some(r) = self.compile(src, quiet) else {
            return Outcome::CompileError;
        };
        let mut opts = self.opts.clone();
        opts.repl = Some(ReplCell::default());
        let ir = match r.cell_ir(&opts) {
            Ok((ir, _)) => ir,
            Err(d) => {
                report(&d);
                return Outcome::CompileError;
            }
        };
        let (out, err) = (self.tmp.path().join("out"), self.tmp.path().join("err"));
        self.link_archives(&r);
        let ran = self.load(&format!("once {} {}", out.display(), err.display()), &ir);
        let mark = format!("{OUT_MARK}\n");
        let after = |f: &std::path::Path| {
            let s = String::from_utf8_lossy(&std::fs::read(f).unwrap_or_default()).into_owned();
            s.split_once(&mark)
                .map_or_else(String::new, |(_, t)| t.to_owned())
        };
        let stdout = after(&out);
        let (printed, value) = match stdout.split_once(&format!("{VAL_MARK}\n")) {
            Some((p, v)) => (p, Some(v.trim_end_matches('\n'))),
            None => (stdout.as_str(), None),
        };
        print!("{printed}");
        eprint!("{}", after(&err));
        if ran.is_none() {
            // Replaying a failing cell would fail every later
            // run, so unlike 907.5 the cell is dropped.
            eprintln!("error: the cell failed; it is not kept");
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

/// Build and start the session host.
fn start_host(dir: &std::path::Path, opts: &BuildOptions) -> Option<Host> {
    let src = dir.join("host.c");
    let exe = dir.join("host");
    if let Err(e) = std::fs::write(&src, HOST_C) {
        eprintln!("error: cannot write {}: {e}", src.display());
        return None;
    }
    if let Err(d) = link_host(&src, opts, &exe) {
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
        .arg(&opts.opt_level)
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

/// Whether a value of `ty` can hold an `any` value (`seen` cuts
/// recursive types).
fn holds_any(hir: &HirModule, ty: &HirTy, seen: &mut Vec<HirTy>) -> bool {
    if seen.contains(ty) {
        return false;
    }
    seen.push(ty.clone());
    let mut any = |ts: &[HirTy]| ts.iter().any(|t| holds_any(hir, t, seen));
    match ty {
        HirTy::Any | HirTy::AnyTrait(_) => true,
        HirTy::Sum(ts) | HirTy::Tuple(ts) => any(ts),
        HirTy::Array(t, _) | HirTy::GcBuf(t) => any(std::slice::from_ref(t)),
        HirTy::Throws { ok, err } => any(&[(**ok).clone(), (**err).clone()]),
        HirTy::Struct(id) => hir.structs.iter().filter(|s| s.id == *id).any(|s| {
            let fields: Vec<HirTy> = s.fields.iter().map(|f| f.ty.clone()).collect();
            any(&fields)
        }),
        HirTy::Enum(id) => hir.enums.iter().filter(|e| e.id == *id).any(|e| {
            let payloads: Vec<HirTy> = e
                .variants
                .iter()
                .filter_map(|v| v.payload_ty.clone())
                .collect();
            any(&payloads)
        }),
        _ => false,
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
pub(crate) fn incomplete(src: &str) -> bool {
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
    deps_dir: PathBuf,
    opts: BuildOptions,
    interactive: bool,
    replay: bool,
    prelude: Option<&str>,
) -> i32 {
    match Repl::new(bootstrap, opts) {
        Ok(mut r) => {
            r.externs = externs;
            r.deps_dir = deps_dir;
            r.replay = replay;
            if let Some(p) = prelude {
                r.prelude = Some(p.to_owned());
                r.cell(p);
            }
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

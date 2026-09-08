//! `repl`: an interactive session without a JIT engine (906).
//!
//! The session is one anonymous `main.rok` (907.1: a run of cells is
//! the implicit `main.rok` with top-level statements and items appended).
//! Each input recompiles that whole program, links it, and runs it; the
//! output of the new cell is what follows a marker the cell prints
//! first, so earlier cells' output is not shown again. Earlier cells do
//! run again: their side effects (I/O, time, randomness) repeat.

use std::collections::HashSet;
use std::io::{BufRead, Write};
use std::path::PathBuf;
use std::process::Command;

use rokc_hir::{HirModule, HirTy};
use rokc_interface::{BuildOptions, CompileResult, EmitKind, Session, TempDir, report};

use crate::analysis::ty_name;

const OUT_MARK: &str = "@@rok-repl-out@@";
const VAL_MARK: &str = "@@rok-repl-val@@";
const VALUE: &str = "__rok_repl_v";

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

pub struct Repl {
    bootstrap: Vec<PathBuf>,
    /// Dependencies (`--extern name=root`).
    pub externs: Vec<(String, PathBuf)>,
    opts: BuildOptions,
    tmp: TempDir,
    state: State,
}

impl Repl {
    pub fn new(bootstrap: Vec<PathBuf>, opts: BuildOptions) -> Result<Self, String> {
        Ok(Self {
            bootstrap,
            externs: Vec::new(),
            tmp: TempDir::new(opts.keep_temps).map_err(|d| d.message)?,
            opts,
            state: State::default(),
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
            ":reset" => self.state = State::default(),
            ":help" | ":h" => print!("{HELP}"),
            _ if cell.starts_with(":type ") || cell.starts_with(":t ") => {
                let expr = cell.split_once(' ').map_or("", |(_, e)| e).trim();
                let src = self.state.program(&format!("let {VALUE} = ({expr});"));
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
        next.items.push((key, cell.to_owned()));
        let Some(r) = self.compile(&next.program(""), false) else {
            return;
        };
        // Codegen too, like `check`: it rejects what cannot be lowered.
        match r.emit(EmitKind::Mlir, &self.opts) {
            Ok(_) => self.state = next,
            Err(d) => report(&d),
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
) -> i32 {
    match Repl::new(bootstrap, opts) {
        Ok(mut r) => {
            r.externs = externs;
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

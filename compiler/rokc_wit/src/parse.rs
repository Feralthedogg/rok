//! WIT text to its syntax tree (component model `WIT.md`).
//!
//! Packages (nested ones too), interfaces, worlds, `use`, type
//! definitions, functions. Feature gates (`@since`, `@deprecated`) are
//! read and dropped; `@unstable` items are left out, as `wit-parser`
//! does by default.

use std::fmt;
use std::path::{Path, PathBuf};

/// A problem in a `.wit` file, at `line:col` (1-based).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub path: PathBuf,
    pub line: usize,
    pub col: usize,
    pub msg: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}:{}: {}",
            self.path.display(),
            self.line,
            self.col,
            self.msg
        )
    }
}

/// `ns:name@version` (nested namespaces `a:b:c` keep their colons in
/// `ns`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PkgName {
    pub ns: String,
    pub name: String,
    pub version: Option<String>,
}

impl fmt::Display for PkgName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.ns, self.name)?;
        if let Some(v) = &self.version {
            write!(f, "@{v}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct File {
    pub path: PathBuf,
    /// `package ns:name;` heading the file.
    pub package: Option<PkgName>,
    pub items: Vec<TopItem>,
    /// `package ns:name { .. }` blocks.
    pub nested: Vec<(PkgName, Vec<TopItem>)>,
}

#[derive(Clone, Debug)]
pub enum TopItem {
    Interface(Interface),
    World(World),
    /// `use ns:pkg/iface as name;` at the top of a file.
    Use(UsePath, String, Pos),
}

/// Byte offset into its file, for messages.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Pos(pub usize);

#[derive(Clone, Debug)]
pub struct Interface {
    pub name: String,
    pub items: Vec<IfaceItem>,
    pub pos: Pos,
}

#[derive(Clone, Debug)]
pub enum IfaceItem {
    Type(TypeDecl),
    Use(Use),
    Func(Func),
}

#[derive(Clone, Debug)]
pub struct TypeDecl {
    pub name: String,
    pub kind: TypeDeclKind,
    pub pos: Pos,
}

#[derive(Clone, Debug)]
pub enum TypeDeclKind {
    Alias(Ty),
    Record(Vec<(String, Ty)>),
    Variant(Vec<(String, Option<Ty>)>),
    Enum(Vec<String>),
    Flags(Vec<String>),
    Resource(Vec<Func>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FuncKind {
    Free,
    Method,
    Static,
    Constructor,
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub kind: FuncKind,
    pub params: Vec<(String, Ty)>,
    pub result: Option<Ty>,
    pub pos: Pos,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Prim {
    Bool,
    U8,
    U16,
    U32,
    U64,
    S8,
    S16,
    S32,
    S64,
    F32,
    F64,
    Char,
    String,
}

#[derive(Clone, Debug)]
pub enum Ty {
    Prim(Prim),
    List(Box<Ty>),
    Option(Box<Ty>),
    Result(Option<Box<Ty>>, Option<Box<Ty>>),
    Tuple(Vec<Ty>),
    Own(String, Pos),
    Borrow(String, Pos),
    Named(String, Pos),
}

#[derive(Clone, Debug)]
pub enum UsePath {
    /// An interface of the same package.
    Local(String),
    Foreign {
        pkg: PkgName,
        iface: String,
    },
}

#[derive(Clone, Debug)]
pub struct Use {
    pub path: UsePath,
    /// `(name, as)`.
    pub names: Vec<(String, Option<String>)>,
    pub pos: Pos,
}

#[derive(Clone, Debug)]
pub struct World {
    pub name: String,
    pub items: Vec<WorldItem>,
    pub pos: Pos,
}

#[derive(Clone, Debug)]
pub enum WorldItem {
    Import(Extern),
    Export(Extern),
    Use(Use),
    Type(TypeDecl),
    Include(UsePath, Pos),
}

#[derive(Clone, Debug)]
pub enum Extern {
    Path(UsePath, Pos),
    Func(Func),
    Interface(String, Vec<IfaceItem>, Pos),
}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Id(String),
    /// `%name`: an identifier that is never a keyword.
    Escaped(String),
    /// A version or integer (starts with a digit).
    Num(String),
    Punct(&'static str),
    Eof,
}

const PUNCT: &[&str] = &[
    "->", "{", "}", "(", ")", "<", ">", ",", ":", ";", "=", ".", "/", "@", "*", "_",
];

const KEYWORDS: &[&str] = &[
    "package",
    "interface",
    "world",
    "use",
    "as",
    "type",
    "record",
    "variant",
    "enum",
    "flags",
    "resource",
    "func",
    "static",
    "constructor",
    "import",
    "export",
    "include",
    "with",
    "own",
    "borrow",
    "async",
];

struct Lexer<'a> {
    src: &'a str,
    at: usize,
}

impl Lexer<'_> {
    fn skip_trivia(&mut self) -> Result<(), (usize, String)> {
        let b = self.src.as_bytes();
        loop {
            while self.at < b.len() && b[self.at].is_ascii_whitespace() {
                self.at += 1;
            }
            if self.src[self.at..].starts_with("//") {
                while self.at < b.len() && b[self.at] != b'\n' {
                    self.at += 1;
                }
            } else if self.src[self.at..].starts_with("/*") {
                let start = self.at;
                let mut depth = 0;
                loop {
                    if self.at >= b.len() {
                        return Err((start, "unterminated block comment".into()));
                    }
                    if self.src[self.at..].starts_with("/*") {
                        depth += 1;
                        self.at += 2;
                    } else if self.src[self.at..].starts_with("*/") {
                        depth -= 1;
                        self.at += 2;
                        if depth == 0 {
                            break;
                        }
                    } else {
                        self.at += 1;
                    }
                }
            } else {
                return Ok(());
            }
        }
    }

    fn next(&mut self) -> Result<(Tok, usize), (usize, String)> {
        self.skip_trivia()?;
        let b = self.src.as_bytes();
        let start = self.at;
        let Some(&c) = b.get(self.at) else {
            return Ok((Tok::Eof, start));
        };
        let word = |at: &mut usize| {
            // `a-b-c`: words joined by single dashes.
            let from = *at;
            while *at < b.len()
                && (b[*at].is_ascii_alphanumeric()
                    || (b[*at] == b'-' && b.get(*at + 1).is_some_and(u8::is_ascii_alphanumeric)))
            {
                *at += 1;
            }
            from..*at
        };
        if c == b'%' {
            self.at += 1;
            let r = word(&mut self.at);
            if r.is_empty() {
                return Err((start, "expected an identifier after `%`".into()));
            }
            return Ok((Tok::Escaped(self.src[r].to_owned()), start));
        }
        if c.is_ascii_alphabetic() {
            let r = word(&mut self.at);
            return Ok((Tok::Id(self.src[r].to_owned()), start));
        }
        if c.is_ascii_digit() {
            // Versions: `0.2.0`, `1.0.0-rc.1+build.5` (not the `.` of
            // `use a:b/c@1.0.0.{x}`).
            while self.at < b.len()
                && (b[self.at].is_ascii_alphanumeric()
                    || (matches!(b[self.at], b'.' | b'-' | b'+')
                        && b.get(self.at + 1).is_some_and(u8::is_ascii_alphanumeric)))
            {
                self.at += 1;
            }
            return Ok((Tok::Num(self.src[start..self.at].to_owned()), start));
        }
        for p in PUNCT {
            if self.src[self.at..].starts_with(p) {
                self.at += p.len();
                return Ok((Tok::Punct(p), start));
            }
        }
        let ch = self.src[self.at..].chars().next().unwrap_or(' ');
        Err((start, format!("unexpected character `{ch}`")))
    }
}

struct Parser<'a> {
    path: &'a Path,
    src: &'a str,
    toks: Vec<(Tok, usize)>,
    i: usize,
}

type PResult<T> = Result<T, Error>;

/// Parse one `.wit` file.
pub fn parse_file(path: &Path, src: &str) -> PResult<File> {
    let mut lx = Lexer { src, at: 0 };
    let mut toks = Vec::new();
    loop {
        let t = lx
            .next()
            .map_err(|(at, msg)| error_at(path, src, at, msg))?;
        let eof = t.0 == Tok::Eof;
        toks.push(t);
        if eof {
            break;
        }
    }
    let mut p = Parser {
        path,
        src,
        toks,
        i: 0,
    };
    p.file()
}

fn error_at(path: &Path, src: &str, at: usize, msg: String) -> Error {
    let before = &src[..at.min(src.len())];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    Error {
        path: path.to_owned(),
        line,
        col,
        msg,
    }
}

/// `pos` of `path`'s text `src` as a message.
pub fn error_pos(path: &Path, src: &str, pos: Pos, msg: String) -> Error {
    error_at(path, src, pos.0, msg)
}

impl Parser<'_> {
    fn peek(&self) -> &Tok {
        &self.toks[self.i].0
    }

    fn peek_at(&self, n: usize) -> &Tok {
        &self.toks[(self.i + n).min(self.toks.len() - 1)].0
    }

    fn pos(&self) -> Pos {
        Pos(self.toks[self.i].1)
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.i].0.clone();
        if self.i + 1 < self.toks.len() {
            self.i += 1;
        }
        t
    }

    fn err<T>(&self, msg: impl Into<String>) -> PResult<T> {
        Err(error_at(
            self.path,
            self.src,
            self.toks[self.i].1,
            msg.into(),
        ))
    }

    fn found(&self) -> String {
        match self.peek() {
            Tok::Id(s) | Tok::Num(s) => format!("`{s}`"),
            Tok::Escaped(s) => format!("`%{s}`"),
            Tok::Punct(p) => format!("`{p}`"),
            Tok::Eof => "end of file".into(),
        }
    }

    fn is_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), Tok::Id(s) if s == kw)
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.is_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn is_punct(&self, p: &str) -> bool {
        matches!(self.peek(), Tok::Punct(q) if *q == p)
    }

    fn eat(&mut self, p: &str) -> bool {
        if self.is_punct(p) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, p: &str) -> PResult<()> {
        if self.eat(p) {
            Ok(())
        } else {
            self.err(format!("expected `{p}`, found {}", self.found()))
        }
    }

    fn expect_kw(&mut self, kw: &str) -> PResult<()> {
        if self.eat_kw(kw) {
            Ok(())
        } else {
            self.err(format!("expected `{kw}`, found {}", self.found()))
        }
    }

    /// An identifier: a word that is no keyword, or `%word`.
    fn id(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Escaped(s) => {
                self.bump();
                Ok(s)
            }
            Tok::Id(s) if !KEYWORDS.contains(&s.as_str()) => {
                check_id(&s).map_or(Ok(()), |m| self.err(m))?;
                self.bump();
                Ok(s)
            }
            _ => self.err(format!("expected an identifier, found {}", self.found())),
        }
    }

    fn version(&mut self) -> PResult<Option<String>> {
        if !self.eat("@") {
            return Ok(None);
        }
        if let Tok::Num(v) = self.peek().clone() {
            self.bump();
            return Ok(Some(v));
        }
        self.err("expected a version after `@`")
    }

    /// `ns:name@version` after `package`.
    fn pkg_name(&mut self) -> PResult<PkgName> {
        let mut parts = vec![self.id()?];
        while self.eat(":") {
            parts.push(self.id()?);
        }
        if parts.len() < 2 {
            return self.err("expected `namespace:name` package name");
        }
        let name = parts.pop().unwrap_or_default();
        let version = self.version()?;
        Ok(PkgName {
            ns: parts.join(":"),
            name,
            version,
        })
    }

    /// `name` or `ns:pkg/name@version`.
    fn use_path(&mut self) -> PResult<UsePath> {
        let first = self.id()?;
        if !self.is_punct(":") {
            return Ok(UsePath::Local(first));
        }
        let mut parts = vec![first];
        while self.eat(":") {
            parts.push(self.id()?);
        }
        self.expect("/")?;
        let iface = self.id()?;
        let version = self.version()?;
        let name = parts.pop().unwrap_or_default();
        Ok(UsePath::Foreign {
            pkg: PkgName {
                ns: parts.join(":"),
                name,
                version,
            },
            iface,
        })
    }

    /// Feature gates before an item: `false` when `@unstable` hides it.
    fn gates(&mut self) -> PResult<bool> {
        let mut shown = true;
        while self.is_punct("@") {
            self.bump();
            let name = self.id()?;
            self.expect("(")?;
            let mut depth = 1;
            while depth > 0 {
                match self.bump() {
                    Tok::Punct("(") => depth += 1,
                    Tok::Punct(")") => depth -= 1,
                    Tok::Eof => return self.err("unterminated feature gate"),
                    _ => {}
                }
            }
            match name.as_str() {
                "unstable" => shown = false,
                "since" | "deprecated" => {}
                _ => return self.err(format!("unknown feature gate `@{name}`")),
            }
        }
        Ok(shown)
    }

    fn file(&mut self) -> PResult<File> {
        let mut file = File {
            path: self.path.to_owned(),
            package: None,
            items: Vec::new(),
            nested: Vec::new(),
        };
        self.gates()?;
        if self.eat_kw("package") {
            let name = self.pkg_name()?;
            if self.eat("{") {
                let items = self.top_items(true)?;
                file.nested.push((name, items));
            } else {
                self.expect(";")?;
                file.package = Some(name);
            }
        }
        loop {
            if *self.peek() == Tok::Eof {
                return Ok(file);
            }
            if self.is_kw("package") {
                self.bump();
                let name = self.pkg_name()?;
                self.expect("{")?;
                let items = self.top_items(true)?;
                file.nested.push((name, items));
                continue;
            }
            let mut items = self.top_items(false)?;
            file.items.append(&mut items);
        }
    }

    /// Items up to `}` (`nested`) or the next `package` / end of file.
    fn top_items(&mut self, nested: bool) -> PResult<Vec<TopItem>> {
        let mut items = Vec::new();
        loop {
            if nested && self.eat("}") {
                return Ok(items);
            }
            if !nested && (*self.peek() == Tok::Eof || self.is_kw("package")) {
                return Ok(items);
            }
            let shown = self.gates()?;
            let pos = self.pos();
            let item = if self.eat_kw("interface") {
                let name = self.id()?;
                let body = self.iface_body()?;
                TopItem::Interface(Interface {
                    name,
                    items: body,
                    pos,
                })
            } else if self.eat_kw("world") {
                let name = self.id()?;
                TopItem::World(self.world_body(name, pos)?)
            } else if self.eat_kw("use") {
                let path = self.use_path()?;
                let alias = if self.eat_kw("as") {
                    self.id()?
                } else {
                    match &path {
                        UsePath::Local(n) | UsePath::Foreign { iface: n, .. } => n.clone(),
                    }
                };
                self.expect(";")?;
                TopItem::Use(path, alias, pos)
            } else {
                return self.err(format!(
                    "expected `interface`, `world`, `use` or `package`, found {}",
                    self.found()
                ));
            };
            if shown {
                items.push(item);
            }
        }
    }

    fn iface_body(&mut self) -> PResult<Vec<IfaceItem>> {
        self.expect("{")?;
        let mut items = Vec::new();
        while !self.eat("}") {
            let shown = self.gates()?;
            let item = self.iface_item()?;
            if shown {
                items.push(item);
            }
        }
        Ok(items)
    }

    fn iface_item(&mut self) -> PResult<IfaceItem> {
        if self.is_kw("use") {
            return self.use_item().map(IfaceItem::Use);
        }
        if let Some(t) = self.typedef()? {
            return Ok(IfaceItem::Type(t));
        }
        let pos = self.pos();
        let name = self.id()?;
        self.expect(":")?;
        let f = self.func_type(name, FuncKind::Free, pos)?;
        self.expect(";")?;
        Ok(IfaceItem::Func(f))
    }

    fn use_item(&mut self) -> PResult<Use> {
        let pos = self.pos();
        self.expect_kw("use")?;
        let path = self.use_path()?;
        self.expect(".")?;
        self.expect("{")?;
        let mut names = Vec::new();
        loop {
            if self.eat("}") {
                break;
            }
            let n = self.id()?;
            let alias = if self.eat_kw("as") {
                Some(self.id()?)
            } else {
                None
            };
            names.push((n, alias));
            if !self.eat(",") {
                self.expect("}")?;
                break;
            }
        }
        self.expect(";")?;
        Ok(Use { path, names, pos })
    }

    /// `func(params) -> result` after `name:`.
    fn func_type(&mut self, name: String, kind: FuncKind, pos: Pos) -> PResult<Func> {
        if self.is_kw("async") {
            return self.err("`async` functions (WASI preview 3) are not supported");
        }
        self.expect_kw("func")?;
        let params = self.params()?;
        let result = if self.eat("->") {
            Some(self.ty()?)
        } else {
            None
        };
        Ok(Func {
            name,
            kind,
            params,
            result,
            pos,
        })
    }

    fn params(&mut self) -> PResult<Vec<(String, Ty)>> {
        self.expect("(")?;
        let mut params = Vec::new();
        loop {
            if self.eat(")") {
                return Ok(params);
            }
            let n = self.id()?;
            self.expect(":")?;
            params.push((n, self.ty()?));
            if !self.eat(",") {
                self.expect(")")?;
                return Ok(params);
            }
        }
    }

    /// `{ a, b, }` of names (`f(name)` gives each one).
    fn comma_list<T>(&mut self, mut f: impl FnMut(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        self.expect("{")?;
        let mut out = Vec::new();
        loop {
            if self.eat("}") {
                return Ok(out);
            }
            let shown = self.gates()?;
            let x = f(self)?;
            if shown {
                out.push(x);
            }
            if !self.eat(",") {
                self.expect("}")?;
                return Ok(out);
            }
        }
    }

    fn typedef(&mut self) -> PResult<Option<TypeDecl>> {
        let pos = self.pos();
        let kind = match self.peek() {
            Tok::Id(k) if self.peek_at(1) != &Tok::Punct(":") => k.clone(),
            _ => return Ok(None),
        };
        let kind = match kind.as_str() {
            "type" => {
                self.bump();
                let name = self.id()?;
                self.expect("=")?;
                let t = self.ty()?;
                self.expect(";")?;
                return Ok(Some(TypeDecl {
                    name,
                    kind: TypeDeclKind::Alias(t),
                    pos,
                }));
            }
            "record" => {
                self.bump();
                let name = self.id()?;
                let fields = self.comma_list(|p| {
                    let n = p.id()?;
                    p.expect(":")?;
                    Ok((n, p.ty()?))
                })?;
                (name, TypeDeclKind::Record(fields))
            }
            "variant" => {
                self.bump();
                let name = self.id()?;
                let cases = self.comma_list(|p| {
                    let n = p.id()?;
                    let t = if p.eat("(") {
                        let t = p.ty()?;
                        p.expect(")")?;
                        Some(t)
                    } else {
                        None
                    };
                    Ok((n, t))
                })?;
                (name, TypeDeclKind::Variant(cases))
            }
            "enum" => {
                self.bump();
                let name = self.id()?;
                (name, TypeDeclKind::Enum(self.comma_list(Self::id)?))
            }
            "flags" => {
                self.bump();
                let name = self.id()?;
                (name, TypeDeclKind::Flags(self.comma_list(Self::id)?))
            }
            "resource" => {
                self.bump();
                let name = self.id()?;
                let mut funcs = Vec::new();
                if !self.eat(";") {
                    self.expect("{")?;
                    while !self.eat("}") {
                        let shown = self.gates()?;
                        let f = self.resource_func()?;
                        if shown {
                            funcs.push(f);
                        }
                    }
                }
                (name, TypeDeclKind::Resource(funcs))
            }
            _ => return Ok(None),
        };
        Ok(Some(TypeDecl {
            name: kind.0,
            kind: kind.1,
            pos,
        }))
    }

    fn resource_func(&mut self) -> PResult<Func> {
        let pos = self.pos();
        if self.eat_kw("constructor") {
            let params = self.params()?;
            if self.eat("->") {
                return self
                    .err("fallible constructors (`constructor(..) -> result`) are not supported");
            }
            self.expect(";")?;
            return Ok(Func {
                name: String::new(),
                kind: FuncKind::Constructor,
                params,
                result: None,
                pos,
            });
        }
        let name = self.id()?;
        self.expect(":")?;
        let kind = if self.eat_kw("static") {
            FuncKind::Static
        } else {
            FuncKind::Method
        };
        let f = self.func_type(name, kind, pos)?;
        self.expect(";")?;
        Ok(f)
    }

    fn angle_one(&mut self) -> PResult<Ty> {
        self.expect("<")?;
        let t = self.ty()?;
        self.expect(">")?;
        Ok(t)
    }

    fn ty(&mut self) -> PResult<Ty> {
        let pos = self.pos();
        let word = match self.peek().clone() {
            Tok::Escaped(s) => {
                self.bump();
                return Ok(Ty::Named(s, pos));
            }
            Tok::Id(s) => s,
            _ => return self.err(format!("expected a type, found {}", self.found())),
        };
        let prim = match word.as_str() {
            "bool" => Some(Prim::Bool),
            "u8" => Some(Prim::U8),
            "u16" => Some(Prim::U16),
            "u32" => Some(Prim::U32),
            "u64" => Some(Prim::U64),
            "s8" => Some(Prim::S8),
            "s16" => Some(Prim::S16),
            "s32" => Some(Prim::S32),
            "s64" => Some(Prim::S64),
            "f32" | "float32" => Some(Prim::F32),
            "f64" | "float64" => Some(Prim::F64),
            "char" => Some(Prim::Char),
            "string" => Some(Prim::String),
            _ => None,
        };
        if let Some(p) = prim {
            self.bump();
            return Ok(Ty::Prim(p));
        }
        match word.as_str() {
            "list" => {
                self.bump();
                self.expect("<")?;
                let t = self.ty()?;
                if self.eat(",") {
                    return self.err("fixed-length lists (`list<T, N>`) are not supported");
                }
                self.expect(">")?;
                Ok(Ty::List(Box::new(t)))
            }
            "option" => {
                self.bump();
                Ok(Ty::Option(Box::new(self.angle_one()?)))
            }
            "result" => {
                self.bump();
                if !self.eat("<") {
                    return Ok(Ty::Result(None, None));
                }
                let ok = if self.eat("_") {
                    None
                } else {
                    Some(Box::new(self.ty()?))
                };
                let err = if self.eat(",") {
                    Some(Box::new(self.ty()?))
                } else {
                    None
                };
                if ok.is_none() && err.is_none() {
                    return self.err("expected `,` after `result<_`");
                }
                self.expect(">")?;
                Ok(Ty::Result(ok, err))
            }
            "tuple" => {
                self.bump();
                self.expect("<")?;
                let mut ts = Vec::new();
                loop {
                    if self.eat(">") {
                        break;
                    }
                    ts.push(self.ty()?);
                    if !self.eat(",") {
                        self.expect(">")?;
                        break;
                    }
                }
                Ok(Ty::Tuple(ts))
            }
            "own" | "borrow" => {
                self.bump();
                self.expect("<")?;
                let p = self.pos();
                let n = self.id()?;
                self.expect(">")?;
                Ok(if word == "own" {
                    Ty::Own(n, p)
                } else {
                    Ty::Borrow(n, p)
                })
            }
            "future" | "stream" | "error-context" => {
                self.err(format!("`{word}` (WASI preview 3) is not supported"))
            }
            _ => Ok(Ty::Named(self.id()?, pos)),
        }
    }

    fn world_body(&mut self, name: String, pos: Pos) -> PResult<World> {
        self.expect("{")?;
        let mut items = Vec::new();
        while !self.eat("}") {
            let shown = self.gates()?;
            let item = if self.is_kw("import") || self.is_kw("export") {
                let import = self.is_kw("import");
                self.bump();
                let e = self.extern_item()?;
                if import {
                    WorldItem::Import(e)
                } else {
                    WorldItem::Export(e)
                }
            } else if self.is_kw("use") {
                WorldItem::Use(self.use_item()?)
            } else if self.is_kw("include") {
                let p = self.pos();
                self.bump();
                let path = self.use_path()?;
                if self.is_kw("with") {
                    return self.err("`include .. with { .. }` is not supported");
                }
                self.expect(";")?;
                WorldItem::Include(path, p)
            } else if let Some(t) = self.typedef()? {
                WorldItem::Type(t)
            } else {
                return self.err(format!(
                    "expected `import`, `export`, `use`, `include` or a type, found {}",
                    self.found()
                ));
            };
            if shown {
                items.push(item);
            }
        }
        Ok(World { name, items, pos })
    }

    /// After `import` / `export`.
    fn extern_item(&mut self) -> PResult<Extern> {
        let pos = self.pos();
        let named = matches!(self.peek(), Tok::Id(_) | Tok::Escaped(_))
            && *self.peek_at(1) == Tok::Punct(":")
            && matches!(self.peek_at(2), Tok::Id(k) if k == "func" || k == "interface" || k == "async");
        if !named {
            let path = self.use_path()?;
            self.expect(";")?;
            return Ok(Extern::Path(path, pos));
        }
        let name = self.id()?;
        self.expect(":")?;
        if self.eat_kw("interface") {
            let items = self.iface_body()?;
            return Ok(Extern::Interface(name, items, pos));
        }
        let f = self.func_type(name, FuncKind::Free, pos)?;
        self.expect(";")?;
        Ok(Extern::Func(f))
    }
}

/// Why `s` is no WIT identifier (words of lowercase or uppercase
/// letters and digits, each starting with a letter).
fn check_id(s: &str) -> Option<String> {
    for w in s.split('-') {
        let first = w.chars().next()?;
        let lower = w
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit());
        let upper = w
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit());
        if !first.is_ascii_alphabetic() || !(lower || upper) {
            return Some(format!("`{s}` is not a WIT identifier (kebab-case words)"));
        }
    }
    None
}

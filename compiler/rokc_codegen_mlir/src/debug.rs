//! `-g` (spec 9.9.6): DWARF through MLIR's LLVM-dialect debug
//! attributes. Each function with a source span gets a
//! `#llvm.di_subprogram` named by its rok path as its fused location (no
//! linkage name: lldb would show the `_Y` symbol, which it cannot
//! demangle, instead of the name); each op gets the `file:line:col` of
//! the MIR `Statement::Loc` before it; named locals get an
//! `llvm.intr.dbg.declare` of their stack slot, typed by `di_type`
//! (primitives; structs with their field names, tuples, `str`, `any`,
//! sums and arrays as composites; GC references and `fn` values as
//! pointers).
//!
//! The attribute aliases are module-level text placed before `module`;
//! op locations are appended to the op lines of a finished function
//! body (`locate`), which sees `//loc L C` marker lines.

use std::collections::BTreeMap;
use std::fmt::Write;
use std::path::{Path, PathBuf};

use rokc_ir_common::PrimTy;
use rokc_mir::{MirFunction, MirTy, Statement};

/// Module-wide debug-info state.
pub struct DebugInfo {
    /// Source paths by `Span::file` (id − 1), made absolute.
    paths: Vec<PathBuf>,
    /// Attribute alias definitions, in definition order.
    pub defs: String,
    /// `#di_file` alias by file id.
    files: BTreeMap<u32, String>,
    cu: Option<String>,
    /// DWARF type alias by `MirTy` (its `Debug` text).
    types: BTreeMap<String, String>,
    next: u32,
    /// Target pointer width in bits.
    pw: u32,
    /// Struct name and field names by `StructId` (`MirModule::struct_names`).
    pub struct_names: std::collections::HashMap<u32, (String, Vec<String>)>,
}

/// What a function body needs to place its locations.
pub struct FnDebug {
    /// Escaped absolute path of the function's file.
    pub file: String,
    pub line: u32,
    pub col: u32,
    pub subprogram: String,
    /// `#llvm.di_lexical_block` alias by MIR scope id (not 0, the body).
    pub scopes: BTreeMap<u32, String>,
}

/// Marker line the body emitter writes for a `Statement::Loc`.
pub const MARK: &str = "    //loc ";

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

impl Default for DebugInfo {
    fn default() -> Self {
        Self::new(64)
    }
}

impl DebugInfo {
    #[must_use]
    pub fn new(pw: u32) -> Self {
        let cwd = std::env::current_dir().unwrap_or_default();
        let paths = rokc_diagnostic::registered_files()
            .into_iter()
            .map(|(p, _)| cwd.join(p))
            .collect();
        Self {
            paths,
            defs: String::new(),
            files: BTreeMap::new(),
            cu: None,
            types: BTreeMap::new(),
            next: 0,
            pw,
            struct_names: std::collections::HashMap::new(),
        }
    }

    fn path(&self, file: u32) -> Option<&Path> {
        self.paths
            .get(usize::try_from(file).ok()?.checked_sub(1)?)
            .map(PathBuf::as_path)
    }

    fn file_alias(&mut self, file: u32) -> Option<String> {
        if let Some(a) = self.files.get(&file) {
            return Some(a.clone());
        }
        let p = self.path(file)?;
        let name = escape(&p.file_name()?.to_string_lossy());
        let dir = escape(
            &p.parent()
                .map_or_else(String::new, |d| d.to_string_lossy().into_owned()),
        );
        let alias = format!("#di_file{file}");
        let _ = writeln!(
            self.defs,
            "{alias} = #llvm.di_file<\"{name}\" in \"{dir}\">"
        );
        self.files.insert(file, alias.clone());
        Some(alias)
    }

    fn fresh(&mut self) -> u32 {
        self.next += 1;
        self.next
    }

    /// The subprogram of `f`, named `name`, or `None` when it has
    /// no source position (synthetic functions).
    pub fn subprogram(&mut self, f: &MirFunction, name: &str) -> Option<FnDebug> {
        let span = f.span;
        if span.line == 0 {
            return None;
        }
        let file = self.file_alias(span.file)?;
        let cu = if let Some(cu) = &self.cu {
            cu.clone()
        } else {
            // The first described function's file names the unit.
            let _ = writeln!(
                self.defs,
                "#di_cu = #llvm.di_compile_unit<id = distinct[0]<>, sourceLanguage = DW_LANG_C, \
                 file = {file}, producer = \"rokc\", isOptimized = false, emissionKind = Full>\n\
                 #di_fn_ty = #llvm.di_subroutine_type<callingConvention = DW_CC_normal>"
            );
            self.cu = Some("#di_cu".to_owned());
            "#di_cu".to_owned()
        };
        let n = self.fresh();
        let sp = format!("#di_sp{n}");
        let _ = writeln!(
            self.defs,
            "{sp} = #llvm.di_subprogram<id = distinct[{n}]<>, compileUnit = {cu}, scope = {file}, \
             name = \"{}\", file = {file}, line = {line}, scopeLine = {line}, \
             subprogramFlags = Definition, type = #di_fn_ty>",
            escape(name),
            line = span.line
        );
        let mut d = FnDebug {
            file: escape(&self.path(span.file)?.to_string_lossy()),
            line: span.line,
            col: span.col.max(1),
            subprogram: sp,
            scopes: BTreeMap::new(),
        };
        // A lexical block per nested scope, at its first position;
        // parents have smaller ids, so they come first.
        let mut first: BTreeMap<u32, (rokc_diagnostic::Span, u32)> = BTreeMap::new();
        for s in f.blocks.iter().flat_map(|b| &b.stmts) {
            if let Statement::Loc(at, sc) = s {
                if sc.id != 0 {
                    first.entry(sc.id).or_insert((*at, sc.parent));
                }
            }
        }
        for (id, (at, parent)) in first {
            let parent = d.scopes.get(&parent).unwrap_or(&d.subprogram).clone();
            let n = self.fresh();
            let alias = format!("#di_lb{n}");
            let _ = writeln!(
                self.defs,
                "{alias} = #llvm.di_lexical_block<scope = {parent}, file = {file}, line = {}, \
                 column = {}>",
                at.line,
                at.col.max(1)
            );
            d.scopes.insert(id, alias);
        }
        Some(d)
    }

    /// A `#llvm.di_local_variable` for local `name` (a `ty`) of the
    /// function `sp`, declared at `line`; `arg` is its 1-based parameter
    /// position. `None` for types without a DWARF description here.
    pub fn local(
        &mut self,
        sp: &str,
        file: u32,
        name: &str,
        ty: &MirTy,
        line: u32,
        arg: Option<usize>,
    ) -> Option<String> {
        let ty = self.di_type(ty)?;
        let file = self.file_alias(file)?;
        let n = self.fresh();
        let alias = format!("#di_var{n}");
        let arg = arg.map(|a| format!("arg = {a}, ")).unwrap_or_default();
        let _ = writeln!(
            self.defs,
            "{alias} = #llvm.di_local_variable<scope = {sp}, name = \"{}\", file = {file}, \
             line = {line}, {arg}type = {ty}>",
            escape(name)
        );
        Some(alias)
    }

    /// A DWARF type for `ty`, or `None` for `()`.
    fn di_type(&mut self, ty: &MirTy) -> Option<String> {
        let key = format!("{ty:?}");
        if let Some(a) = self.types.get(&key) {
            return Some(a.clone());
        }
        let pw = self.pw;
        let (size, align) = crate::emit::size_align(ty, pw);
        let def = match ty {
            MirTy::Unit => return None,
            MirTy::Prim(PrimTy::Str) => {
                let u8 = self.basic_type(PrimTy::U8)?;
                let ptr = format!(
                    "#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = {u8}, sizeInBits = {pw}>"
                );
                let len = self.basic_type(PrimTy::Usize)?;
                Self::composite("str", size, align, &[("ptr", ptr, 0), ("len", len, pw / 8)])
            }
            MirTy::Prim(p) => return self.basic_type(*p),
            MirTy::GcRef | MirTy::Fn(..) => {
                let name = if *ty == MirTy::GcRef { "gcref" } else { "fn" };
                format!(
                    "#llvm.di_derived_type<tag = DW_TAG_pointer_type, name = \"{name}\", sizeInBits = {pw}>"
                )
            }
            MirTy::Any => {
                let tag = self.basic_type(PrimTy::I32)?;
                let payload = self.basic_type(PrimTy::Usize)?;
                Self::composite(
                    "any",
                    size,
                    align,
                    &[("tag", tag, 0), ("payload", payload, pw / 8)],
                )
            }
            MirTy::Sum(ps) => {
                let layout = rokc_mir::sum_layout(ps);
                let MirTy::Tuple(parts) = &layout else {
                    return self.di_type(&layout);
                };
                let fields = self.members(parts, &["tag", "payload"]);
                Self::composite("sum", size, align, &fields)
            }
            MirTy::Tuple(ps) => {
                let fields = self.members(ps, &[]);
                Self::composite("tuple", size, align, &fields)
            }
            MirTy::Struct(id, ps) => {
                let (name, names) = self
                    .struct_names
                    .get(&id.0)
                    .cloned()
                    .unwrap_or_else(|| (format!("Struct#{}", id.0), Vec::new()));
                let names: Vec<&str> = names.iter().map(String::as_str).collect();
                let names = if names.len() == ps.len() {
                    names
                } else {
                    Vec::new()
                };
                let fields = self.members(ps, &names);
                Self::composite(&name, size, align, &fields)
            }
            MirTy::Array(elem, n) => {
                let base = self.di_type(elem)?;
                format!(
                    "#llvm.di_composite_type<tag = DW_TAG_array_type, baseType = {base}, \
                     sizeInBits = {}, alignInBits = {}, elements = #llvm.di_subrange<count = {n} : i64>>",
                    size * 8,
                    align * 8
                )
            }
        };
        let alias = format!("#di_ty{}", self.fresh());
        let _ = writeln!(self.defs, "{alias} = {def}");
        self.types.insert(key, alias.clone());
        Some(alias)
    }

    /// `(name, type, byte offset)` of each part of a C-laid-out aggregate
    /// (`names[i]`, else `i`); `()` parts are left out.
    fn members(&mut self, parts: &[MirTy], names: &[&str]) -> Vec<(String, String, u32)> {
        let mut out = Vec::new();
        let mut off = 0u32;
        for (i, t) in parts.iter().enumerate() {
            let (s, a) = crate::emit::size_align(t, self.pw);
            off = off.next_multiple_of(a);
            if let Some(ty) = self.di_type(t) {
                let name = names
                    .get(i)
                    .map_or_else(|| i.to_string(), |n| (*n).to_owned());
                out.push((name, ty, off));
            }
            off += s;
        }
        out
    }

    /// A `DW_TAG_structure_type` of `members` (`(name, type, offset)`).
    fn composite<N: AsRef<str>>(
        name: &str,
        size: u32,
        align: u32,
        members: &[(N, String, u32)],
    ) -> String {
        let elements: Vec<String> = members
            .iter()
            .map(|(n, t, off)| {
                format!(
                    "#llvm.di_derived_type<tag = DW_TAG_member, name = \"{}\", baseType = {t}, \
                     offsetInBits = {}>",
                    escape(n.as_ref()),
                    off * 8
                )
            })
            .collect();
        let elements = if elements.is_empty() {
            String::new()
        } else {
            format!(", elements = {}", elements.join(", "))
        };
        format!(
            "#llvm.di_composite_type<tag = DW_TAG_structure_type, name = \"{}\", \
             sizeInBits = {}, alignInBits = {}{elements}>",
            escape(name),
            size * 8,
            align * 8
        )
    }

    fn basic_type(&mut self, p: PrimTy) -> Option<String> {
        let word = self.pw;
        let (name, bits, enc) = match p {
            PrimTy::I8 => ("i8", 8, "DW_ATE_signed"),
            PrimTy::I16 => ("i16", 16, "DW_ATE_signed"),
            PrimTy::I32 => ("i32", 32, "DW_ATE_signed"),
            PrimTy::I64 => ("i64", 64, "DW_ATE_signed"),
            PrimTy::Isize => ("isize", word, "DW_ATE_signed"),
            PrimTy::U8 => ("u8", 8, "DW_ATE_unsigned"),
            PrimTy::U16 => ("u16", 16, "DW_ATE_unsigned"),
            PrimTy::U32 => ("u32", 32, "DW_ATE_unsigned"),
            PrimTy::U64 => ("u64", 64, "DW_ATE_unsigned"),
            PrimTy::Usize => ("usize", word, "DW_ATE_unsigned"),
            PrimTy::F32 => ("f32", 32, "DW_ATE_float"),
            PrimTy::F64 => ("f64", 64, "DW_ATE_float"),
            PrimTy::Bool => ("bool", 8, "DW_ATE_boolean"),
            PrimTy::CChar => ("c_char", 8, "DW_ATE_signed_char"),
            PrimTy::Char => ("char", 32, "DW_ATE_UTF"),
            PrimTy::Str => return None,
        };
        if let Some(a) = self.types.get(name) {
            return Some(a.clone());
        }
        let alias = format!("#di_{name}");
        let _ = writeln!(
            self.defs,
            "{alias} = #llvm.di_basic_type<tag = DW_TAG_base_type, name = \"{name}\", \
             sizeInBits = {bits}, encoding = {enc}>"
        );
        self.types.insert(name.to_owned(), alias.clone());
        Some(alias)
    }
}

/// Line and lexical scope of each named local's first assignment (its
/// `let`), from the `Statement::Loc` markers in block order.
#[must_use]
pub fn decl_lines(f: &MirFunction) -> BTreeMap<u32, (u32, u32)> {
    let mut out = BTreeMap::new();
    let (mut line, mut scope) = (f.span.line, 0);
    for b in &f.blocks {
        for s in &b.stmts {
            match s {
                Statement::Loc(sp, sc) => (line, scope) = (sp.line, sc.id),
                Statement::Assign { target, .. } => {
                    out.entry(target.0).or_insert((line, scope));
                }
                _ => {}
            }
        }
    }
    out
}

/// Append a `loc(..)` to every op line of a function body: the position
/// of the latest marker, or the function's own before the first one.
#[must_use]
pub fn locate(body: &str, d: &FnDebug) -> String {
    let mut out = String::with_capacity(body.len() * 2);
    let (mut line, mut col, mut scope) = (d.line, d.col, None);
    for l in body.lines() {
        if let Some(pos) = l.strip_prefix(MARK) {
            let mut it = pos.split(' ').filter_map(|n| n.parse::<u32>().ok());
            line = it.next().unwrap_or(line);
            col = it.next().unwrap_or(col);
            scope = it.next().and_then(|s| d.scopes.get(&s));
            continue;
        }
        out.push_str(l);
        let t = l.trim_start();
        if !(t.is_empty() || t.starts_with('^') || t.starts_with("//") || t.contains(" loc(")) {
            match scope {
                Some(lb) => {
                    let _ = write!(out, " loc(fused<{lb}>[\"{}\":{line}:{col}])", d.file);
                }
                None => {
                    let _ = write!(out, " loc(\"{}\":{line}:{col})", d.file);
                }
            }
        }
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn locate_tags_op_lines_only() {
        let d = FnDebug {
            file: "/p/a.rok".to_owned(),
            line: 3,
            col: 1,
            subprogram: "#di_sp1".to_owned(),
            scopes: BTreeMap::from([(2, "#di_lb3".to_owned())]),
        };
        let body = "    %0 = arith.constant 1 : i32\n    //loc 4 5\n  ^bb1:\n    func.return %0 : i32\n    //loc 6 2 2\n    %1 = arith.constant 2 : i32\n";
        assert_eq!(
            locate(body, &d),
            "    %0 = arith.constant 1 : i32 loc(\"/p/a.rok\":3:1)\n  ^bb1:\n    \
             func.return %0 : i32 loc(\"/p/a.rok\":4:5)\n    \
             %1 = arith.constant 2 : i32 loc(fused<#di_lb3>[\"/p/a.rok\":6:2])\n"
        );
    }
}

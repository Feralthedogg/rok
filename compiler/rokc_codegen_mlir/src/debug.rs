//! `-g` (spec 9.9.6): DWARF through MLIR's LLVM-dialect debug
//! attributes. Each function with a source span gets a
//! `#llvm.di_subprogram` named by its rok path as its fused location (no
//! linkage name: lldb would show the `_Y` symbol, which it cannot
//! demangle, instead of the name); each op gets the `file:line:col` of
//! the MIR `Statement::Loc` before it; named primitive locals get an
//! `llvm.intr.dbg.declare` of their stack slot.
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
    types: BTreeMap<&'static str, String>,
    next: u32,
}

/// What a function body needs to place its locations.
pub struct FnDebug {
    /// Escaped absolute path of the function's file.
    pub file: String,
    pub line: u32,
    pub col: u32,
    pub subprogram: String,
}

/// Marker line the body emitter writes for a `Statement::Loc`.
pub const MARK: &str = "    //loc ";

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

impl Default for DebugInfo {
    fn default() -> Self {
        Self::new()
    }
}

impl DebugInfo {
    #[must_use]
    pub fn new() -> Self {
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
        Some(FnDebug {
            file: escape(&self.path(span.file)?.to_string_lossy()),
            line: span.line,
            col: span.col.max(1),
            subprogram: sp,
        })
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
        let MirTy::Prim(p) = ty else { return None };
        let ty = self.basic_type(*p)?;
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

    fn basic_type(&mut self, p: PrimTy) -> Option<String> {
        let (name, bits, enc) = match p {
            PrimTy::I8 => ("i8", 8, "DW_ATE_signed"),
            PrimTy::I16 => ("i16", 16, "DW_ATE_signed"),
            PrimTy::I32 => ("i32", 32, "DW_ATE_signed"),
            PrimTy::I64 => ("i64", 64, "DW_ATE_signed"),
            PrimTy::Isize => ("isize", 64, "DW_ATE_signed"),
            PrimTy::U8 => ("u8", 8, "DW_ATE_unsigned"),
            PrimTy::U16 => ("u16", 16, "DW_ATE_unsigned"),
            PrimTy::U32 => ("u32", 32, "DW_ATE_unsigned"),
            PrimTy::U64 => ("u64", 64, "DW_ATE_unsigned"),
            PrimTy::Usize => ("usize", 64, "DW_ATE_unsigned"),
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
        self.types.insert(name, alias.clone());
        Some(alias)
    }
}

/// Line of each named local's first assignment (its `let`), from the
/// `Statement::Loc` markers in block order.
#[must_use]
pub fn decl_lines(f: &MirFunction) -> BTreeMap<u32, u32> {
    let mut out = BTreeMap::new();
    let mut line = f.span.line;
    for b in &f.blocks {
        for s in &b.stmts {
            match s {
                Statement::Loc(sp) => line = sp.line,
                Statement::Assign { target, .. } => {
                    out.entry(target.0).or_insert(line);
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
    let (mut line, mut col) = (d.line, d.col);
    for l in body.lines() {
        if let Some(pos) = l.strip_prefix(MARK) {
            let mut it = pos.split(' ').filter_map(|n| n.parse::<u32>().ok());
            line = it.next().unwrap_or(line);
            col = it.next().unwrap_or(col);
            continue;
        }
        out.push_str(l);
        let t = l.trim_start();
        if !(t.is_empty() || t.starts_with('^') || t.starts_with("//")) {
            let _ = write!(out, " loc(\"{}\":{line}:{col})", d.file);
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
        };
        let body =
            "    %0 = arith.constant 1 : i32\n    //loc 4 5\n  ^bb1:\n    func.return %0 : i32\n";
        assert_eq!(
            locate(body, &d),
            "    %0 = arith.constant 1 : i32 loc(\"/p/a.rok\":3:1)\n  ^bb1:\n    \
             func.return %0 : i32 loc(\"/p/a.rok\":4:5)\n"
        );
    }
}

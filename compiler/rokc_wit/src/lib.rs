//! WIT for rok (stdlib spec 1.8): the `.wit` files an
//! `ffi::wit::import` / `ffi::wit::export` names are parsed and
//! resolved ([`load`]), and rok source binding them through the
//! canonical ABI is generated ([`bind`]), with the world the linker
//! (`wasm-component-ld`) gives the component.
//!
//! A path names a `.wit` file or a directory: a directory's `*.wit`
//! files are one package, and its `deps/` holds the packages it uses
//! (files or directories), as `wit-parser` reads them. A file is read
//! with the rest of its directory but names only what it defines.

// Code generation reads best with the canonical ABI's own short names
// (`t` type, `v` value, `a` address, `p` / `n` pointer and length).
#![allow(clippy::many_single_char_names)]

pub mod abi;
mod bind;
pub mod parse;
pub mod resolve;

use std::path::{Path, PathBuf};

pub use bind::{Bindings, bind};
pub use parse::Error;
pub use resolve::{IfaceId, Resolve, WorldId};

/// What one `ffi::wit` item asks for, by path.
#[derive(Clone, Debug)]
pub struct Request {
    pub export: bool,
    pub paths: Vec<PathBuf>,
}

/// The files read: the ones a request names (`roots`, one entry per
/// path: the indices of its files in `Resolve::files`) and their
/// dependencies.
#[derive(Debug)]
pub struct Loaded {
    pub resolve: Resolve,
    pub roots: Vec<Vec<usize>>,
    /// What the linker's WIT directory is made of: each package source,
    /// a file or a directory.
    pub units: Vec<PathBuf>,
}

fn read_wit(path: &Path) -> Result<(parse::File, String), Error> {
    let src = std::fs::read_to_string(path).map_err(|e| Error {
        path: path.to_owned(),
        line: 0,
        col: 0,
        msg: format!("cannot read: {e}"),
    })?;
    Ok((parse::parse_file(path, &src)?, src))
}

/// The `*.wit` files of `dir`, sorted; a file without `package` takes
/// the one another file of the directory declares.
fn read_dir(dir: &Path) -> Result<Vec<(parse::File, String)>, Error> {
    let mut paths: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| Error {
            path: dir.to_owned(),
            line: 0,
            col: 0,
            msg: format!("cannot read: {e}"),
        })?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.is_file() && p.extension().is_some_and(|x| x == "wit"))
        .collect();
    paths.sort();
    let mut files = paths
        .iter()
        .map(|p| read_wit(p))
        .collect::<Result<Vec<_>, _>>()?;
    let pkg = files.iter().find_map(|(f, _)| f.package.clone());
    for (f, _) in &mut files {
        if f.package.is_none() {
            f.package.clone_from(&pkg);
        }
    }
    Ok(files)
}

/// Read and resolve every path of `requests` (and their `deps/`).
pub fn load(requests: &[Request]) -> Result<Loaded, Error> {
    let mut files: Vec<(parse::File, String)> = Vec::new();
    // Each source read once: its canonical path and its files.
    let mut seen: Vec<(PathBuf, Vec<usize>)> = Vec::new();
    let mut units = Vec::new();
    let mut roots = Vec::new();
    let mut add = |path: &Path,
                   files: &mut Vec<(parse::File, String)>,
                   units: &mut Vec<PathBuf>|
     -> Result<Vec<usize>, Error> {
        let canon = std::fs::canonicalize(path).map_err(|e| Error {
            path: path.to_owned(),
            line: 0,
            col: 0,
            msg: format!("cannot read: {e}"),
        })?;
        if let Some((_, ids)) = seen.iter().find(|(p, _)| *p == canon) {
            return Ok(ids.clone());
        }
        let read = if canon.is_dir() {
            read_dir(&canon)?
        } else {
            vec![read_wit(&canon)?]
        };
        let ids: Vec<usize> = (files.len()..files.len() + read.len()).collect();
        files.extend(read);
        units.push(canon.clone());
        seen.push((canon, ids.clone()));
        Ok(ids)
    };
    let mut deps_dirs = Vec::new();
    for req in requests {
        for p in &req.paths {
            // A file is read with its directory (its package), but names
            // only what it defines.
            let dir = if p.is_dir() {
                p.clone()
            } else {
                p.parent()
                    .map_or_else(|| PathBuf::from("."), Path::to_path_buf)
            };
            let mut ids = add(&dir, &mut files, &mut units)?;
            if !p.is_dir() {
                let canon = std::fs::canonicalize(p).map_err(|e| Error {
                    path: p.clone(),
                    line: 0,
                    col: 0,
                    msg: format!("cannot read: {e}"),
                })?;
                ids.retain(|&i| files[i].0.path == canon);
            }
            roots.push(ids);
            if dir.join("deps").is_dir() {
                deps_dirs.push(dir.join("deps"));
            }
        }
    }
    // Dependencies: each entry of a `deps/` directory is a package, and
    // may have `deps/` of its own.
    while let Some(d) = deps_dirs.pop() {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(&d)
            .map(|rd| rd.filter_map(|e| e.ok().map(|e| e.path())).collect())
            .unwrap_or_default();
        entries.sort();
        for e in entries {
            if e.is_dir() || e.extension().is_some_and(|x| x == "wit") {
                add(&e, &mut files, &mut units)?;
                if e.join("deps").is_dir() {
                    deps_dirs.push(e.join("deps"));
                }
            }
        }
    }
    let resolve = Resolve::new(files)?;
    Ok(Loaded {
        resolve,
        roots,
        units,
    })
}

#[cfg(test)]
mod tests;

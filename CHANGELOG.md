# Changelog

## 0.1.0-rc.1 (unreleased)

First release candidate.

- Compiler `rokc` (AOT via MLIR / LLVM 22, REPL, Jupyter kernel, language server, `fmt`, `lint`, `doc`, `test`,
  `bench`, `bindgen`), package / build front-end `rok` (`rok.rokon` / `rok.lock`, path / git dependencies, stones,
  environments, toolchains), runtime `librokr.a`, standard library `core` / `std` / `bare`.
- Install: rustup-style layout (`~/.rok/bin` proxies, `~/.rok/toolchains/<version>-<triple>/`), `install.sh` /
  `install.ps1`, and `rok-<version>-<triple>.tar.gz` (Windows `.zip`) archives built by `dist.sh`.
- `rok` / `rokc` / `rokls --version` print the version, commit, and date.
- License `MIT OR Apache-2.0`.

### Language

- Using a value after it was handed off (`Mutex::new`, `send`, `Handoff::new`, through calls) is a compile
  error; the check follows conditions and call outcomes.
- Duplicate items point at both definitions; a tuple or unit struct's constructor shares the value namespace
  with functions, consts and statics. A named `use` and a local item of the same name are an error; a glob
  import gives way.
- Names from another module need a `use`; "cannot find" errors suggest the `use` to add or the missing `pub`.
- Generic argument counts are checked; a bare generic type says it needs arguments.
- Generic unions; impls on generic type aliases; an alias's `where` is checked in declaration types.
- Block-local items (`struct`, `enum`, `impl`, `use`, `const` in a block), including module glob `use`.
- Statics and consts of `fn` type are callable. `Sync` rules for statics, `RwLock` and `[ref]` cells.
- `#[cold]` keeps a function out of line.

### Tools

- Scripts: `rok <file>`, shebang lines, dependencies from the file's `//! rokon` block (`rok add <lib> <file>`),
  `mod helper;` across script files; `import` gets an error naming `mod` / `use`.
- Packages with both `src/lib.rok` and `src/main.rok`; `rok install <stone>` installs executables, keeps one
  installed at the same version and rebuilds with `--force`; `rok install <lib>` serves the REPL and Jupyter.
- The package name `rok` is reserved for the standard library.
- Build profiles: debug info by default; release folds identical code and strips.
- Lints in every compiling command; hints for habits from other languages.

### Platforms

- Windows x86_64: the full test suite passes on a Windows host; libclang (`rokc bindgen`), a Windows PGO
  profile, `dist.sh` and `install.ps1 -NoModifyPath`.
- `riscv64gc-unknown-linux-gnu`, verified on a riscv64 kernel.

### Performance

- Bounds checks of counted loops over lists move in front of the loop; short loops and loop nests run without
  safepoint polls; a fixed-index element stays in a register.
- Calls between rok functions pass the thread block as an argument; the GC frame links only on paths that reach
  a safepoint.
- rok / C instructions on the bench suite: nbody 1.43x, fannkuch 1.67x, spectral_norm 1.11x, throw_parse 1.85x.

# Changelog

## 0.1.0 (unreleased)

First release.

- Compiler `rokc` (AOT via MLIR / LLVM 22, REPL, Jupyter kernel, language server, `fmt`, `lint`, `doc`, `test`,
  `bench`, `bindgen`), package / build front-end `rok` (`rok.rokon` / `rok.lock`, path / git dependencies, stones,
  environments, toolchains), runtime `librokr.a`, standard library `core` / `std` / `bare`.
- Install: rustup-style layout (`~/.rok/bin` proxies, `~/.rok/toolchains/<version>-<triple>/`), `install.sh`, and
  `rok-<version>-<triple>.tar.gz` archives built by `dist.sh`.
- `rok` / `rokc` / `rokls --version` print the version, commit, and date.
- License `MIT OR Apache-2.0`.

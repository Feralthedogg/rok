# rok

The implementation of the rok language: the compiler `rokc`, the package / build front-end `rok`, the language
server `rokls`, the runtime `librokr.a`, and the standard library (`library/{core,std,bare}`). The language
specification lives in [rok-lang/spec](https://github.com/rok-lang/spec); the introduction and getting-started
guide are at [rok-lang.org](https://rok-lang.org).

## Requirements

- A toolchain needs no LLVM install: `rokc` links LLVM, MLIR and lld (pinned LLVM 22.1.8) and runs the whole
  back end in process. On macOS the link needs the SDK of Xcode's command line tools (`xcode-select --install`);
  on Linux, the C library's development files (`crt1.o`, `libc.so`) and GCC's runtime. Set `ROK_CC` to link
  with a C compiler driver instead.
- The REPL and the Jupyter kernel run on macOS arm64.
- Building from source needs Rust (`rust-toolchain.toml`; no external crates are used), and for anything above
  `-O0` the pinned LLVM: `llvm/build.sh` builds it once into `~/.cache/rok` (cmake, ninja, about an hour; see
  `llvm/README.md`). Without it `rokc` builds `-O0` only (the native backend), linking with the system `cc`.

## Install

```sh
curl -fsSL https://rok-lang.org/install.sh | sh
```

Or from a release archive:

```sh
sh install.sh --archive rok-0.1.0-aarch64-apple-darwin.tar.gz
# from inside an unpacked archive
rok-0.1.0-aarch64-apple-darwin/install.sh
```

Then add `~/.rok/bin` to `PATH` (the script tells you how).

```sh
export PATH="$HOME/.rok/bin:$PATH"      # bash / zsh
fish_add_path ~/.rok/bin                 # fish
```

## Install layout

rustup / cargo style (spec 9.2.19). `ROK_HOME` defaults to `~/.rok`.

```
$ROK_HOME/
├── bin/{rok,rokc,rokls}              proxies: run the same-named binary of the active toolchain
├── toolchains/<version>-<triple>/    self-contained toolchain
│   ├── bin/{rok,rokc,rokls}
│   └── lib/librokr.a, lib/rok/{core,std,bare}/
├── cache/                            git, registry, script locks
├── envs/<name>/, envs/CURRENT        named environments
└── config.rokon                      Config { registry: "..", toolchain: ".." }
```

- `rokc` finds the standard library and runtime relative to its own executable (sysroot = `bin/..`) and ignores
  `ROK_HOME`. A `rokc` built in the repository (`target/<profile>/rokc`) uses the repository's `library/` and the
  `librokr.a` next to it.
- Active toolchain: `rok +<version> ..` > `ROK_TOOLCHAIN` > `toolchain: "X"` in the nearest `rok.rokon` >
  `rok toolchain default`.

```sh
rok toolchain list
rok toolchain install 0.1.0 --from rok-0.1.0-aarch64-apple-darwin.tar.gz   # directory, archive, or URL
rok toolchain default 0.1
rok toolchain remove 0.1.0-aarch64-apple-darwin
```

## Quick start

```sh
rok new hello        # hello/{main.rok, rok.rokon, .gitignore} + git init
cd hello
rok run              # Hello, world!
rok repl .           # run it in a REPL session, then stay there with its bindings
rok test
rok jupyter install  # rok kernel for Jupyter / VS Code
```

## Building from source

```sh
cargo build --release                 # target/release/{rok,rokc,rokls}, librokr.a
./dist.sh                             # dist/rok-<version>-<triple>.tar.gz (+ .sha256)
sh install.sh --archive dist/rok-*.tar.gz
```

During development you can use `target/debug/rok` / `rokc` directly (they find the repository's `library/`).

### Checks

```sh
cargo fmt --all --check
cargo clippy --all-targets -- -D warnings
ROK_REQUIRE_LLVM=1 cargo test --no-fail-fast
ROK_TEST_OPT=-O2 ROK_REQUIRE_LLVM=1 cargo test --test integration
cargo run -p rokc -- fmt --check library
```

## License

`MIT OR Apache-2.0` ([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)). The specification repository
is CC-BY-4.0.

# rok

The implementation of the rok language: the compiler `rokc`, the package / build front-end `rok`, the language
server `rokls`, the runtime `librokr.a`, and the standard library (`library/{core,std,bare}`). The language
specification lives in [rok-lang/spec](https://github.com/rok-lang/spec); the introduction and getting-started
guide are at [rok-lang.org](https://rok-lang.org).

## Requirements

- A toolchain needs no LLVM install: `rokc` links LLVM, MLIR and lld (pinned LLVM 22.1.8) and runs the whole
  back end in process. On macOS the link needs the SDK of Xcode's command line tools (`xcode-select --install`).
  Linux targets need nothing: the toolchain ships their runtime and C library (musl, and link stubs of glibc
  2.36: executables need glibc 2.34 or later) in `lib/rok/targets/<triple>/`, so `--target <linux triple>` works
  from any host, and so does the other macOS arch. Set `ROK_CC` to link with a C compiler driver instead.
- Code generation: rok's native backend builds `-O0` for arm64 and x86_64; every other target (the 32-bit
  `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`, `armv7-unknown-linux-gnueabihf`) and every optimized build
  goes through LLVM.
- The REPL and the Jupyter kernel run on macOS and Linux (arm64, x86_64).
- Building from source needs Rust (`rust-toolchain.toml`; no external crates are used), and for anything above
  `-O0` the pinned LLVM: `llvm/build.sh` builds it once into `~/.cache/rok` (cmake, ninja, about an hour; see
  `llvm/README.md`). Without it `rokc` builds `-O0` only (the native backend), linking with the system `cc`.
  `targets/build.sh` builds what `--target` links into `target/lib/rok/targets/` (rustup, curl, python3, clang).

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

On Windows (PowerShell; installs into `%USERPROFILE%\.rok` and puts its `bin` on the user's `PATH`):

```powershell
powershell -ExecutionPolicy Bypass -c "irm https://rok-lang.org/install.ps1 | iex"
powershell -ExecutionPolicy Bypass -File install.ps1 -Archive rok-0.1.0-x86_64-pc-windows-msvc.zip
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
│   └── lib/librokr.a, lib/rok/{core,std,bare}/, lib/rok/targets/<triple>/
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
rok new hello        # hello/{src/main.rok, rok.rokon, .gitignore} + git init
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
ROK_TEST_OPT=-O2 ROK_REQUIRE_LLVM=1 cargo test --test integration --test differential
./target/debug/rokc fmt --check library
```

On a Linux host run `targets/build.sh <host triple>` once first: a Linux build, native too, links the
toolchain's C library (glibc link stubs), which it puts in `target/lib/rok/targets/`.

The WebAssembly targets have their own corpus run: `targets/test-wasm.sh [<target>..]` builds the
runtimes of `wasm32-wasi`, `wasm32-wasi-threads` and `wasm32-unknown-unknown`, fetches the pinned wasmtime
(v46.0.3, the last release with wasi-threads), and runs every integration and differential case for each at
`-O0` and `-O2`: the WASI targets under wasmtime, the browser target under node with `rok.mjs`. Cases that need
what a target lacks (`// needs:`) are skipped there; others assert its `Unsupported` errors (`// only-target:`).
Set `CC` to a clang with a WebAssembly backend to include `wasm32-wasi`'s profile-guided-optimization test.

### CI

`.github/workflows/ci.yml` (GitHub Actions). Linux runs on every push and pull request; macOS and Windows on
pushes to `main` and on a manual run (`workflow_dispatch`, whose `hosts` / `jobs` inputs pick a subset).
Changes to Markdown files alone run nothing; a newer push to the same branch cancels the older run.

- `llvm`, per host (`ubuntu-24.04` x86_64, `ubuntu-24.04-arm` aarch64, `macos-26` arm64, `macos-26-intel`
  x86_64, `windows-2022` x86_64): the pinned LLVM prefix (`.github/actions/llvm-prefix`), built by
  `llvm/build.sh` (Windows `llvm/build.ps1`) only when the actions cache has none for the hash of the build
  script and its PGO profile, then stripped of what `rokc_llvm` does not link and saved (120–175 MB each in
  the cache). On a private repository's standard runners a build took 0.5 h (macOS arm64), 2.2 h (macOS
  x86_64, Linux aarch64), 4.5 h (Linux x86_64) and 6.0 h (Windows: at the 6 h job limit). Linux needs clang
  19+ to read `rok.profdata.xz`; a build without PGO fails. A hit only looks the entry up. Caches made on a
  branch serve that branch only, so the first push to `main` builds every host once.
- `gate`, per host: the checks above (on Linux after `targets/build.sh <host>`), every step even after one
  fails, plus the compiler / runtime crate isolation check.
- `cross` (Linux x86_64): `targets/build.sh` for the Linux targets and `i686-pc-windows-msvc`, the sysroot
  link test, and the integration and differential corpora at `-O0` and `-O2` for `i686-unknown-linux-gnu`
  (the i386 loader) and `armv7-unknown-linux-gnueabihf` (qemu-user).
- `wasm` (Linux x86_64), a job per wasm32 target: `targets/test-wasm.sh <target>`, with the image's node and
  clang (which has the WebAssembly target, so `wasm32-wasi`'s PGO test runs).

## License

`MIT OR Apache-2.0` ([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)). The specification repository
is CC-BY-4.0.

# rok

The implementation of the rok language: the compiler `rokc`, the package / build front-end `rok`, the language
server `rokls`, the runtime `librokr.a`, and the standard library (`library/{core,std,bare}`). The language
specification lives in [rok-lang/spec](https://github.com/rok-lang/spec); the guide, the
reference and the standard library API are at [docs.rok-lang.org](https://docs.rok-lang.org).

## Requirements

- A toolchain needs no LLVM install: `rokc` links LLVM, MLIR and lld (pinned LLVM 22.1.8) and runs the whole
  back end in process. On macOS the link needs the SDK of Xcode's command line tools (`xcode-select --install`).
  Other targets need nothing: the toolchain ships each one's runtime and C library in
  `lib/rok/targets/<triple>/` (musl; link stubs of glibc 2.36, whose executables need glibc 2.34 or later;
  Windows import libraries; wasi-libc), so `--target <triple>` links from any host; Apple targets link from
  macOS. Set `ROK_CC` to link with a C compiler driver instead.
- Code generation: rok's native backend builds `-O0` for arm64 and x86_64; every other target (the 32-bit
  `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`, `armv7-unknown-linux-gnueabihf`;
  `riscv64gc-unknown-linux-gnu`; `wasm32-*`) and every optimized build goes through LLVM.
- The REPL and the Jupyter kernel run on macOS, Linux and Windows; a static (musl) `rokc` has no REPL,
  `rokc bindgen` or MLIR plugins.
- Building from source needs Rust (`rust-toolchain.toml`; only the `libc` sys crate otherwise), and for anything above
  `-O0` the pinned LLVM: `llvm/build.sh` builds it once into `~/.cache/rok` (cmake, ninja, about an hour; see
  `llvm/README.md`). Without it `rokc` builds `-O0` only (the native backend), linking with the system `cc`.
  `targets/build.sh` builds what `--target` links into `target/lib/rok/targets/` (rustup with llvm-tools, curl, make,
  python3, bash, clang; Apple's clang has no RISC-V target, so on an arm64 Mac the non-Apple targets use the pinned
  LLVM release's clang, downloaded once into `~/.cache/rok`).
  `rokc bindgen` loads libclang at run time (nothing else needs it): a toolchain ships it, a build from source
  uses `llvm/build-libclang.sh`'s (about 5 minutes on 10 cores; `llvm/README.md`).

## Install

```sh
curl -fsSL https://rok-lang.org/install.sh | sh
```

Or from a release archive:

```sh
sh install.sh --archive rok-0.1.0-aarch64-apple-darwin.tar.xz   # or the .tar.gz
rok-0.1.0-aarch64-apple-darwin/install.sh     # from inside an unpacked archive
```

`install.sh` does not edit shell files; add `~/.rok/bin` to `PATH` as it says:

```sh
export PATH="$HOME/.rok/bin:$PATH"      # bash / zsh
fish_add_path ~/.rok/bin                 # fish
```

On Windows (PowerShell) the toolchain goes into `%USERPROFILE%\.rok` and its `bin` onto the user's `PATH`
(`-NoModifyPath` leaves `PATH` alone):

```powershell
powershell -ExecutionPolicy Bypass -c "irm https://rok-lang.org/install.ps1 | iex"
powershell -ExecutionPolicy Bypass -File install.ps1 -Archive rok-0.1.0-x86_64-pc-windows-msvc.zip
```

`install.sh --version <v>` and `install.ps1 -Version <v>` pick a release; both check a download against its
`.sha256`.

## Platforms

The toolchain (`rok`, `rokc`, `rokls`) is tested natively on macOS arm64 (macOS 26 and 27), Linux x86_64
(NixOS, Ubuntu 24.04 and 26.04, Alpine), Linux aarch64 (Ubuntu 26.04) and Windows 11 x86_64. macOS x86_64 and
Windows arm64 are untested as hosts. The Linux archives (x86_64, aarch64) need glibc 2.34 or later, as the
programs they build do: RHEL / Rocky / Alma 9, Ubuntu 22.04, Debian 12 and newer.

`--target` covers 15 triples. The test corpus runs programs for Apple arm64 and x86_64 (Rosetta); Linux
x86_64 and aarch64 (gnu and musl; aarch64 natively and under qemu-user), i686, armv7 (qemu-user) and riscv64 (a riscv64
kernel under qemu-system); Windows x86_64 and i686; and the three wasm32 targets (wasmtime, node).
`aarch64-pc-windows-msvc` links but has not run.

## Install layout

rustup / cargo style (spec 9.2.19). `ROK_HOME` defaults to `~/.rok`.

```
$ROK_HOME/
├── bin/{rok,rokc,rokls}              proxies: run the same-named binary of the active toolchain
├── toolchains/<version>-<triple>/    self-contained toolchain
│   ├── bin/{rok,rokc,rokls}
│   └── lib/librokr.a, lib/rok/{core,std,bare}/src/, lib/rok/targets/<triple>/,
│       lib/libclang.{dylib,so,dll}, lib/clang/<major>/include   (rokc bindgen)
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
rok toolchain update             # the newest release becomes the default (older ones stay installed)
rok toolchain update 0.1.1       # a given release
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
./dist.sh                             # dist/rok-<version>-<triple>.tar.gz and .tar.xz (+ .sha256),
                                      # dist/rok-mlir-dev-<version>-<triple>.tar.gz (MLIR plugins)
sh install.sh --archive dist/rok-*.tar.gz
```

During development use `target/debug/rok` / `rokc` directly (they find the repository's `library/`). On
Windows, `dist.sh` runs from Git Bash inside a Developer PowerShell for VS. The Linux release archives come
from `./dist-linux.sh` (same output; podman or docker), which runs `dist.sh` in a Debian 11 container so the
toolchain runs on glibc 2.34 and later (RHEL 9, Ubuntu 22.04, Debian 12); `dist.sh` refuses a Linux build that
needs a newer glibc.

### Checks

```sh
cargo fmt --all --check
cargo clippy --all-targets -- -D warnings
ROK_REQUIRE_LLVM=1 cargo test --no-fail-fast
ROK_TEST_OPT=-O2 ROK_REQUIRE_LLVM=1 cargo test --test integration --test differential
./target/debug/rokc fmt --check library
```

On a Linux host run `targets/build.sh <host triple>` once first: a Linux build, native too, links the
toolchain's C library (glibc link stubs), which it puts in `target/lib/rok/targets/`. With nix (NixOS has
no `/usr/include` or `/usr/bin/c++`), `nix-shell` at the repository root (`shell.nix`) gives everything
`llvm/build.sh`, `targets/build.sh` and the checks use, with clang as `cc` (so the LLVM build gets PGO).
A cross target's corpus runs its executables through `ROK_TEST_RUNNER` when no binfmt handler is
registered, e.g. `ROK_TEST_RUNNER="qemu-aarch64 -L <sysroot>"`.

The WebAssembly targets have their own corpus run: `targets/test-wasm.sh [<target>..]` builds the
runtimes of `wasm32-wasi`, `wasm32-wasi-threads` and `wasm32-unknown-unknown`, fetches the pinned wasmtime
(v46.0.3, the last release with wasi-threads), and runs every integration and differential case for each at
`-O0` and `-O2`: the WASI targets under wasmtime, the browser target under node with `rok.mjs`. Cases that need
what a target lacks (`// needs:`) are skipped there; others assert its `Unsupported` errors (`// only-target:`).
Set `CC` to a clang with a WebAssembly backend to include `wasm32-wasi`'s profile-guided-optimization test.

### CI

`.github/workflows/ci.yml` in three tiers: pushes to branches and pull requests check Linux x86_64; pushes to
`main` and the merge queue add Linux aarch64 and Windows x86_64; a nightly run covers every host at `-O0` and
`-O2`, the cross targets, wasm and `rokc bindgen`. Jobs, runners and the self-hosted setup: [docs/ci.md](docs/ci.md).

## License

`MIT OR Apache-2.0` ([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)). The specification repository
is CC-BY-4.0.

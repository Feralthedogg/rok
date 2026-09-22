# Pinned LLVM

rokc links LLVM, MLIR and lld statically (`compiler/rokc_llvm`) and runs
the whole native back end in process: MLIR passes, translation to LLVM IR,
the LLVM optimization pipeline, object emission (split across cores for a
big module), the link (lld) and, for `-g` on macOS, dsymutil. Users do not
install LLVM; macOS needs the SDK of Xcode's command line tools.

The pin is **LLVM 22.1.8** (`VERSION` in `build.sh`, `LLVM_VERSION` in
`compiler/rokc_llvm`). The C++ shim uses the MLIR / LLVM / lld C++ APIs,
which change between majors, so exactly one version is supported; 22.1.8
is the last release of the newest major the emitted MLIR is tested with.

## Building it

```sh
llvm/build.sh            # → ~/.cache/rok/llvm-22.1.8 (ROK_LLVM_CACHE)
llvm/build.sh <prefix>   # anywhere else
```

Hosts:

- macOS (arm64, x86_64): Xcode's command line tools, cmake, ninja.
- Linux (x86_64, aarch64; glibc or musl): cmake, ninja, curl, xz and a
  C++17 compiler (`apt install cmake ninja-build g++ curl xz-utils`;
  Alpine: `apk add cmake samurai g++ curl xz linux-headers`). rokc_llvm
  links the C++ runtime the archives were built against: libstdc++, or
  libc++ when they name `std::__1`.
- Windows (x86_64, arm64; MSVC ABI): `llvm\build.ps1 [prefix]` from a
  Developer PowerShell for VS (the MSVC C++ build tools, cmake, ninja) →
  `%LOCALAPPDATA%\rok\llvm-22.1.8`. The same libraries as `.lib` with
  the dynamic CRT (`/MD`, as rustc links), no DIA SDK. rokc_llvm compiles
  its shim with `cl` (or `CXX`, e.g. `clang-cl`) and archives it with
  `lib`. Only building rok needs these: the toolchain links Windows
  programs with its own lld and import libraries.

`cargo check --target <another triple>` builds the stub (below) when the
prefix is this machine's (`LLVM_HOST_TRIPLE` names another architecture
or OS).

A Release build of static libraries only: targets AArch64, X86, ARM,
RISCV and WebAssembly; the MLIR and lld (Mach-O, ELF, COFF, MinGW, wasm)
libraries; no tests, tools (but lld's own binary), examples, docs, bindings, zlib, zstd or
libxml2. dsymutil is a tool, not a library: its sources and generated
option table are kept in `share/rok/dsymutil` and compiled into rokc. The
source tarball is checked against a pinned SHA-256; the source and build
trees are deleted after the install.

On a 10-core Apple Silicon machine: about 50 minutes; 700 MB installed.

### PGO

`build.sh` optimizes LLVM with `rok.profdata.xz`, an IR profile
(sparse, xz) of rokc's own `-O2` builds, whenever the C++ compiler can
read it: it tries (`-fprofile-instr-use` on an empty unit) and says when
it builds without. Its function names are Itanium-mangled, so it serves
macOS (Xcode's clang) and Linux (a clang at least as new as the
profile's indexed format: version 12 now, written by Xcode's
llvm-profdata) alike. gcc reads no clang profile: a Linux build with gcc
(the default `c++` on most distributions) has no PGO; `CXX=clang++
CC=clang` gives it. Nothing extra is fetched either way.

An MSVC-ABI build names functions by MSVC mangling, which that profile
does not have. `build.ps1` uses `rok-msvc.profdata.tar.xz` instead,
with clang-cl (`CXX=clang-cl`) when it can read it; cl reads no clang
profile. That profile is not in the repository yet: `train-pgo.ps1`
makes it on a Windows host (below), and until then Windows builds have
no PGO.

`llvm/train-pgo.sh` regenerates `rok.profdata.xz` (macOS, Xcode's
clang): an instrumented LLVM (`ROK_LLVM_INSTRUMENT=1 build.sh`), a
release rokc against it, linked with the profile runtime, then three
quarters of `compiler/rokc/tests/cases` built with it at `-O2` (a third
of them as x86_64 Linux objects, so the X86 back end is profiled too).
`llvm\train-pgo.ps1` does the same on Windows with clang-cl and the
llvm-profdata of its installation (the third as objects for the other
Windows architecture) into `rok-msvc.profdata.tar.xz`. `train-pgo.sh`
peaks at ~5 GB of scratch space and takes about 35 minutes on a 10-core
Apple Silicon machine. Regenerate after a change of the pinned LLVM or
a large change of what rokc asks LLVM to do; a stale profile still
builds, with less benefit.

## Using it

`compiler/rokc_llvm/build.rs` takes `ROK_LLVM_PREFIX`, else the default
prefix of `build.sh`. Without either, rokc_llvm builds a stub whose entry
points return an error: that rokc builds `-O0` with the native backend
only and links with the system's `cc`, reports `llvm: none` in
`rokc version -v`, and the tests that need LLVM skip (fail under
`ROK_REQUIRE_LLVM=1`). A `ROK_LLVM_PREFIX` that does
not hold this LLVM with MLIR, lld and the dsymutil sources fails the
build. `dist.sh` runs `build.sh` when no prefix is given.

rokc registers only the MLIR dialects it lowers to and those
`__mlir_op` offers (`register_dialects` / `register_passes` in
`src/shim.cpp`), so the linker leaves the rest of MLIR out. It exports
the non-weak symbols of the MLIR it links and all of LLVMSupport /
LLVMDemangle, for MLIR plugins to bind to (`write_exports` in
`build.rs`: `-exported_symbols_list` on macOS, `--dynamic-list` on
Linux, with `nm`; on Windows a `/DEF` module definition file from the
archives' COFF symbol tables, whose import library `rokc.lib` plugins
link); everything else is dead-stripped. The headers plugins build with
are in `target/<profile>/mlir-plugin-dev` (docs/mlir-plugins.md).

Homebrew's `llvm` (22.1.8) has static LLVM and MLIR archives but ships lld
only as shared libraries, so it cannot serve as the prefix; release and
development builds both use `build.sh`.

## libclang (`rokc bindgen`)

`rokc bindgen` reads C headers through libclang's C API, which it loads at
run time (`dlopen` / `LoadLibraryW`): rokc does not link it, and no other
command needs it. It comes from the same source tarball, built apart from
the prefix above so that prefix (and its CI cache key) stays as it is:

```sh
llvm/build-libclang.sh            # → ~/.cache/rok/libclang-22.1.8 (ROK_LLVM_CACHE)
llvm\build-libclang.ps1           # Windows (MSVC) → %LOCALAPPDATA%\rok\libclang-22.1.8
```

It builds only the `libclang` shared library and `clang-resource-headers`:
Release, no LLVM back end (`LLVM_TARGETS_TO_BUILD` empty: clang's target
info for `-target` is its own), no tools, tests or docs. The prefix holds
`lib/libclang.{dylib,so,dll}` and `lib/clang/22/include` (clang's built-in
headers, passed as `-resource-dir`); the build tree is deleted at the end.
On a 10-core Apple Silicon machine: 5.5 minutes, a build tree of ~2 GB at
its peak, 36 MB installed (libclang.dylib 29 MB, headers 7.7 MB; 12 MB
compressed).

rokc looks for it in its toolchain's `lib/` (`dist.sh` copies it there,
from `ROK_LIBCLANG_PREFIX` or this script's prefix), else, for a build in
the repository, in this script's prefix. Without one, `rokc bindgen` says
how to get it and the bindgen tests skip (fail under
`ROK_REQUIRE_LIBCLANG=1`).

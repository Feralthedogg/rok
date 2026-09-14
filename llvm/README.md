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

A Release build of static libraries only: targets AArch64, X86, ARM,
RISCV and WebAssembly; the MLIR and lld (Mach-O, ELF, COFF, MinGW, wasm)
libraries; no tests, tools (but lld's own binary), examples, docs, bindings, zlib, zstd or
libxml2. dsymutil is a tool, not a library: its sources and generated
option table are kept in `share/rok/dsymutil` and compiled into rokc. The
source tarball is checked against a pinned SHA-256; the source and build
trees are deleted after the install.

On a 10-core Apple Silicon machine: about 50 minutes; 717 MB installed.

## Using it

`compiler/rokc_llvm/build.rs` takes `ROK_LLVM_PREFIX`, else the default
prefix of `build.sh`. Without either, rokc_llvm builds a stub whose entry
points return an error: that rokc builds `-O0` with the native backend
only and links with the system's `cc`, reports `llvm: none` in
`rokc version -v`, and the tests that need LLVM skip (fail under
`ROK_REQUIRE_LLVM=1`). A `ROK_LLVM_PREFIX` that does
not hold this LLVM with MLIR, lld and the dsymutil sources fails the
build. `dist.sh` runs `build.sh` when no prefix is given.

Homebrew's `llvm` (22.1.8) has static LLVM and MLIR archives but ships lld
only as shared libraries, so it cannot serve as the prefix; release and
development builds both use `build.sh`.

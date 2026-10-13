# MLIR plugins

`rokc --load-mlir-plugin` / `--load-mlir-pass-plugin` load MLIR dialect and pass plugins into rokc's own
MLIR (std `rok::bare::mlir`, 1.10), and `--mlir-pass <pass>` runs a pass before the LLVM lowering. A
plugin is a shared library with MLIR's entry points (`mlirGetDialectPluginInfo`, `mlirGetPassPluginInfo`)
built against the LLVM / MLIR rokc embeds (22.1.8). It does not link MLIR: its MLIR and LLVM symbols bind
to the ones rokc exports, which are the MLIR rokc links (its dialects and what they use) and all of
LLVMSupport. Anything else, such as another upstream dialect, the plugin carries itself.

## The development bundle

`dist.sh` ships `rok-mlir-dev-<version>-<triple>.{tar.gz,zip}` beside the toolchain (a build from source
has the same tree in `target/<profile>/mlir-plugin-dev`):

| Path | |
|---|---|
| `include/` | the LLVM and MLIR headers of rokc's LLVM, plus `rok/mlir_typeid.h` |
| `lib/rokc.lib` | Windows: rokc.exe's import library, which plugins link |
| `example/answer.cpp` | a dialect (`rokt.answer : () -> i32`) and a pass (`rokt-lower`, which rewrites it to `arith.constant 42`) |

Use the bundle of the same rokc version and host. `mlir-tblgen` is not included: write ops in C++ as the
example does, or run the `mlir-tblgen` of an LLVM 22.1.8 build.

## Building the example

`DEV` is the unpacked bundle.

macOS:

```sh
c++ -std=c++17 -O2 -DNDEBUG -fno-rtti -fno-exceptions -fPIC -fvisibility-inlines-hidden \
  -shared -mmacosx-version-min=11.0 -undefined dynamic_lookup \
  -I"$DEV/include" "$DEV/example/answer.cpp" -o librokt.dylib
```

Linux (rokc's LLVM uses libstdc++):

```sh
c++ -std=c++17 -O2 -DNDEBUG -fno-rtti -fno-exceptions -fPIC -fvisibility-inlines-hidden \
  -shared -I"$DEV/include" "$DEV/example/answer.cpp" -o librokt.so
```

Windows, from a Developer Command Prompt for VS (x64, or the arm64 one on arm64), with `cl` or `clang-cl`:

```bat
cl /nologo /std:c++17 /O2 /DNDEBUG /GR- /MD /EHs-c- /D_HAS_EXCEPTIONS=0 /Zc:__cplusplus /bigobj ^
  /LD /I%DEV%\include %DEV%\example\answer.cpp /Ferokt.dll /link %DEV%\lib\rokc.lib
```

## Using it

```rok
use rok::bare::mlir::__mlir_op;

fn main() -> i32 {
    let x: i32 = unsafe { __mlir_op::<"rokt.answer", i32>() };
    println(f"{x}");
    0
}
```

```sh
rokc build p.rok --load-mlir-plugin ./librokt.dylib --load-mlir-pass-plugin ./librokt.dylib \
  --mlir-pass rokt-lower -o p
./p     # 42
```

A bare name is looked up in the directories of `ROK_MLIR_PLUGIN_PATH` as `lib<name>.dylib` or
`lib<name>.so` (macOS), `lib<name>.so` (Linux) or `<name>.dll` (Windows): `--load-mlir-plugin rokt`.

## Requirements

- A static (musl) `rokc` loads no plugins.
- Build against the bundle's headers, with the flags above: no RTTI, `NDEBUG`, C++17. A plugin linked
  against its own MLIR registers into registries rokc never sees.
- Export the entry points: `extern "C" LLVM_ATTRIBUTE_WEAK LLVM_ALWAYS_EXPORT` (on Windows
  `LLVM_ATTRIBUTE_WEAK` is empty and `LLVM_ALWAYS_EXPORT` is `__declspec(dllexport)`).
- Windows: `/MD` (the release DLL CRT, as rokc: memory crosses the boundary), and the import library
  binds the plugin to an executable named `rokc.exe`, so load it only through the toolchain's `rokc`.
- Windows: a DLL reaches another module's data only through `__declspec(dllimport)`, which MLIR's headers
  do not declare. The explicit TypeIDs MLIR keeps as data (`MLIR_DECLARE_EXPLICIT_TYPE_ID`: dialects,
  ops, types, attributes, and `TypeID::get<void>()` behind every default `TypeID`) are therefore looked
  up in rokc.exe's exports by name at first use: the bundle's `mlir/Support/TypeID.h` includes
  `rok/mlir_typeid.h`, which redefines the two macros, so a plugin needs no code for it. Its own
  `MLIR_DECLARE_EXPLICIT_TYPE_ID` / `MLIR_DEFINE_EXPLICIT_TYPE_ID` types get TypeIDs owned by the plugin.
  rokc.lib exports every other data symbol `DATA`: a plugin that touches one directly fails to link
  (`unresolved external symbol`) rather than misbehaving.
- TypeIDs resolved by type name (interfaces, traits, passes without an explicit TypeID) are shared through
  rokc on every host; those of `MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID` stay per library.

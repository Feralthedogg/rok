#!/bin/sh
# Build a release toolchain archive (spec 9.2.19):
#
#   dist/rok-<version>-<triple>.tar.gz     (Windows: .zip)
#     rok-<version>-<triple>/
#       bin/{rok,rokc,rokls}                (Windows: .exe)
#       lib/librokr.a                       (Windows: rokr.lib)
#       lib/rok/{core,std,bare}/src/      the standard library sources
#       lib/rok/lldb/rok_lldb.py    lldb formatters for -g programs (rokc --print lldbinit)
#       lib/rok/targets/<triple>/   what --target links (targets/build.sh)
#       lib/libclang.{so,dylib,dll}, lib/clang/<major>/include
#                                   what `rokc bindgen` loads (llvm/build-libclang.sh;
#                                   not with a static, musl rokc)
#       install.sh install.ps1 README.md CHANGELOG.md LICENSE-MIT LICENSE-APACHE
#       COPYING.mingw-w64 (Windows module definitions embedded in rokc)
#
#   dist/rok-mlir-dev-<version>-<triple>.tar.gz (Windows: .zip; none for musl)
#     rok-mlir-dev-<version>-<triple>/     MLIR plugin development
#       include/{llvm,llvm-c,mlir,mlir-c,rok}  the headers plugins build with
#       lib/rokc.lib                        (Windows) rokc.exe's import library
#       example/answer.cpp README.md        docs/mlir-plugins.md
#
# plus their .sha256 and dist/rok-version; every file is a release asset.
#
#   ./dist.sh [--out <dir>]    (Windows: Git Bash in a Developer prompt)
#
# LLVM comes from ROK_LLVM_PREFIX, libclang from ROK_LIBCLANG_PREFIX,
# else llvm/build*.sh's (.ps1 on Windows), built here when missing.
set -eu

cd "$(dirname "$0")"
out=dist
case "${1-}" in
  --out) out=$2 ;;
  "") ;;
  *) echo "usage: ./dist.sh [--out <dir>]" >&2; exit 2 ;;
esac

# The host's executable suffix, runtime archive and archive format.
case $(uname -s) in
  MINGW* | MSYS* | CYGWIN*)
    exe=.exe rt=rokr.lib ext=zip libclang=libclang.dll
    build_llvm="powershell -NoProfile -ExecutionPolicy Bypass -File llvm/build.ps1"
    build_libclang="powershell -NoProfile -ExecutionPolicy Bypass -File llvm/build-libclang.ps1"
    cache=$(cygpath -u "${ROK_LLVM_CACHE:-$LOCALAPPDATA/rok}")
    # MSYS's /usr/bin/link (coreutils) would be rustc's link.exe.
    [ -n "${VCToolsInstallDir-}" ] || {
      echo "dist.sh: run from a Developer prompt for the MSVC build tools" >&2
      exit 1
    }
    PATH=$(cygpath -u "${VCToolsInstallDir}bin/Host$VSCMD_ARG_HOST_ARCH/$VSCMD_ARG_TGT_ARCH"):$PATH
    # GNU tar reads `C:\..` as a remote host (CI's $RUNNER_TEMP is one).
    out=$(cygpath -u "$out")
    ;;
  *)
    exe="" rt=librokr.a ext=tar.gz build_llvm=./llvm/build.sh build_libclang=./llvm/build-libclang.sh
    cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
    libclang=libclang.so
    [ "$(uname -s)" != Darwin ] || libclang=libclang.dylib
    ;;
esac

# A musl rokc is static: it loads nothing at run time, so it ships no
# libclang (`rokc bindgen` says it cannot load one) and exports no
# symbols for MLIR plugins (no development bundle).
static=""
case $(rustc -vV | sed -n 's/^host: //p') in *-musl) static=1 ;; esac
[ -n "${ROK_LLVM_PREFIX-}" ] || $build_llvm
if [ -n "${ROK_LIBCLANG_PREFIX-}" ]; then
  lc=$ROK_LIBCLANG_PREFIX
elif [ -z "$static" ]; then
  $build_libclang
  lc=$cache/libclang-$(sed -n 's/^VERSION=//p' llvm/build-libclang.sh)
fi
cargo build --release --locked -p rok -p rokc
# The runtime as one object (fat LTO): only its exports stay global
# (runtime/rokr/localize.sh).
CARGO_PROFILE_RELEASE_LTO=fat cargo build --release --locked -p rokr
./targets/build.sh

target=${CARGO_TARGET_DIR:-target}/release
version=$("$target/rokc$exe" --version | awk '{ print $2 }')
triple=$("$target/rokc$exe" --version --verbose | sed -n 's/^host: //p')
if "$target/rokc$exe" --version --verbose | grep -q '^llvm: none'; then
  echo "dist.sh: rokc was built without LLVM (see llvm/README.md)" >&2
  exit 1
fi
name=rok-$version-$triple

# install.sh / install.ps1 download this version by default.
grep -q "^version=\"\${ROK_VERSION:-$version}\"" install.sh &&
  grep -q "else { '$version' }" install.ps1 || {
  echo "dist.sh: install.sh's or install.ps1's default version is not $version" >&2
  exit 1
}

stage=$out/$name
rm -rf "$stage" "$out/$name.$ext" "$out/$name.$ext.sha256"
mkdir -p "$stage/bin" "$stage/lib/rok"
# Without debug info and local symbols. rokc keeps its exported symbols:
# the MLIR plugins it loads bind to them.
mb() { echo "$(($(wc -c < "$1") / 1000000)) MB"; }
for t in rok rokc rokls; do
  cp "$target/$t$exe" "$stage/bin/"
  # PE has no symbol table to strip; the linker leaves debug info in the .pdb.
  [ -n "$exe" ] || strip -x "$stage/bin/$t"
  echo "$t: $(mb "$target/$t$exe") -> $(mb "$stage/bin/$t$exe")"
done
dev=$target/mlir-plugin-dev
devname=""
if [ -z "$static" ]; then
  devname=rok-mlir-dev-$version-$triple
  [ -n "$exe" ] || nm -g "$stage/bin/rokc" | grep -q '[^U] _*_ZN4llvm24DisableABIBreakingChecksE$' || {
    echo "dist.sh: the stripped rokc does not export its LLVM / MLIR symbols" >&2
    exit 1
  }
fi
[ -z "$exe" ] || [ -f "$dev/lib/rokc.lib" ] || {
  echo "dist.sh: rokc.exe's link left no import library ($dev/lib/rokc.lib)" >&2
  exit 1
}
runtime/rokr/localize.sh "$target/$rt" "$stage/lib/$rt"
# The library sources.
tar -C library -cf - core/src std/src bare/src lldb | tar -C "$stage/lib/rok" -xf -
cp -R "${CARGO_TARGET_DIR:-target}/lib/rok/targets" "$stage/lib/rok/"
# libclang (the file a Linux .so link names) and its built-in headers.
if [ -z "$static" ]; then
  cp -L "$lc/lib/$libclang" "$stage/lib/"
  cp -R "$lc/lib/clang" "$stage/lib/"
  echo "libclang: $(mb "$stage/lib/$libclang")"
fi
cp install.sh install.ps1 README.md CHANGELOG.md LICENSE-MIT LICENSE-APACHE \
  compiler/rokc_driver/windows/COPYING.mingw-w64 "$stage/"

# The toolchain runs from its new place, with no LLVM on PATH: its rokc
# finds its library and builds with its own LLVM and lld.
printf 'fn main() -> i32 {\n    println("ok");\n    0\n}\n' > "$stage/check.rok"
for o in -O0 -O2; do
  PATH=/usr/bin:/bin "$stage/bin/rokc$exe" -q build "$stage/check.rok" $o -o "$stage/check$exe"
  [ "$("$stage/check$exe")" = ok ]
  # Every shipped target links (it runs only where the machine can).
  for t in $(ls "$stage/lib/rok/targets"); do
    PATH=/usr/bin:/bin "$stage/bin/rokc$exe" -q build "$stage/check.rok" $o --target "$t" -o "$stage/check$exe"
  done
done
# bindgen loads the toolchain's libclang, which finds its own headers.
if [ -z "$static" ]; then
  printf '#include <stddef.h>\nsize_t check_len(const char *s);\n' > "$stage/check.h"
  PATH=/usr/bin:/bin "$stage/bin/rokc$exe" bindgen "$stage/check.h" |
    grep -q 'pub fn check_len(s: CPtr<c_char>) -> usize;'
fi
rm -rf "$stage/check.h" "$stage/check.rok" "$stage/check$exe" "$stage/.check$exe.fp" "$stage/check.pdb" "$stage/lib/rok-cache"

# The MLIR plugin development bundle (docs/mlir-plugins.md): rokc_llvm's
# plugin tree for this build.
if [ -n "$devname" ]; then
  devstage=$out/$devname
  rm -rf "$devstage" "$out/$devname.$ext" "$out/$devname.$ext.sha256"
  mkdir -p "$devstage/example"
  cp -R "$dev/include" "$devstage/"
  [ -z "$exe" ] || cp -R "$dev/lib" "$devstage/"
  cp docs/mlir-plugins.md "$devstage/README.md"
  cp compiler/rokc/tests/plugin/answer.cpp "$devstage/example/"
fi

sum=$(command -v sha256sum || echo "shasum -a 256")
for n in "$name" $devname; do
  case $ext in
    # cmake (needed for LLVM anyway) writes zip; Git Bash's tar does not.
    zip) (cd "$out" && cmake -E tar cf "$n.zip" --format=zip "$n") ;;
    *) tar -C "$out" -czf "$out/$n.$ext" "$n" ;;
  esac
  (cd "$out" && $sum "$n.$ext" > "$n.$ext.sha256")
  rm -rf "${out:?}/$n"
  echo "archive: $(mb "$out/$n.$ext")"
  echo "$out/$n.$ext"
done
# The release's version: `rok toolchain update` reads the newest release's
# from releases/latest/download/rok-version.
printf '%s\n' "$version" > "$out/rok-version"
echo "$out/rok-version"

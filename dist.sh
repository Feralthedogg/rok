#!/bin/sh
# Build a release toolchain archive (spec 9.2.19):
#
#   dist/rok-<version>-<triple>.tar.gz     (Windows: .zip)
#     rok-<version>-<triple>/
#       bin/{rok,rokc,rokls}                (Windows: .exe)
#       lib/librokr.a                       (Windows: rokr.lib)
#       lib/rok/{core,std,bare}/src/      the standard library sources
#       lib/rok/targets/<triple>/   what --target links (targets/build.sh)
#       install.sh install.ps1 README.md CHANGELOG.md LICENSE-MIT LICENSE-APACHE
#       COPYING.mingw-w64 (Windows module definitions embedded in rokc)
#
# and its .sha256. Usage: ./dist.sh [--out <dir>] (on Windows from Git
# Bash / MSYS2, in a Developer prompt for the MSVC build tools).
#
# rokc links the pinned LLVM / MLIR / lld statically: ROK_LLVM_PREFIX,
# else llvm/build.sh's (llvm/build.ps1's on Windows; built here when
# missing). The toolchain needs no LLVM install; on macOS only the SDK
# (Xcode's command line tools).
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
    exe=.exe rt=rokr.lib ext=zip
    build_llvm="powershell -NoProfile -ExecutionPolicy Bypass -File llvm/build.ps1"
    ;;
  *) exe="" rt=librokr.a ext=tar.gz build_llvm=./llvm/build.sh ;;
esac

[ -n "${ROK_LLVM_PREFIX-}" ] || $build_llvm
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
[ -n "$exe" ] || nm -g "$stage/bin/rokc" | grep -q '[^U] _*_ZN4llvm24DisableABIBreakingChecksE$' || {
  echo "dist.sh: the stripped rokc does not export its LLVM / MLIR symbols" >&2
  exit 1
}
runtime/rokr/localize.sh "$target/$rt" "$stage/lib/$rt"
# The library sources.
tar -C library -cf - core/src std/src bare/src | tar -C "$stage/lib/rok" -xf -
cp -R "${CARGO_TARGET_DIR:-target}/lib/rok/targets" "$stage/lib/rok/"
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
rm -rf "$stage/check.rok" "$stage/check$exe" "$stage/.check$exe.fp" "$stage/check.pdb" "$stage/lib/rok-cache"

case $ext in
  # cmake (needed for LLVM anyway) writes zip; Git Bash's tar does not.
  zip) (cd "$out" && cmake -E tar cf "$name.zip" --format=zip "$name") ;;
  *) tar -C "$out" -czf "$out/$name.$ext" "$name" ;;
esac
sum=$(command -v sha256sum || echo "shasum -a 256")
(cd "$out" && $sum "$name.$ext" > "$name.$ext.sha256")
rm -rf "$stage"
echo "archive: $(mb "$out/$name.$ext")"
echo "$out/$name.$ext"

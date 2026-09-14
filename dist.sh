#!/bin/sh
# Build a release toolchain archive (spec 9.2.19):
#
#   dist/rok-<version>-<triple>.tar.gz
#     rok-<version>-<triple>/
#       bin/{rok,rokc,rokls}
#       lib/librokr.a
#       lib/rok/{core,std,bare}/
#       install.sh README.md CHANGELOG.md LICENSE-MIT LICENSE-APACHE
#
# and its .sha256. Usage: ./dist.sh [--out <dir>]
#
# rokc links the pinned LLVM / MLIR / lld statically: ROK_LLVM_PREFIX,
# else llvm/build.sh's (built here when missing). The toolchain needs no
# LLVM install; on macOS only the SDK (Xcode's command line tools).
set -eu

cd "$(dirname "$0")"
out=dist
case "${1-}" in
  --out) out=$2 ;;
  "") ;;
  *) echo "usage: ./dist.sh [--out <dir>]" >&2; exit 2 ;;
esac

[ -n "${ROK_LLVM_PREFIX-}" ] || ./llvm/build.sh
cargo build --release --locked -p rok -p rokc -p rokr

target=${CARGO_TARGET_DIR:-target}/release
version=$("$target/rokc" --version | awk '{ print $2 }')
triple=$("$target/rokc" --version --verbose | sed -n 's/^host: //p')
if "$target/rokc" --version --verbose | grep -q '^llvm: none'; then
  echo "dist.sh: rokc was built without LLVM (see llvm/README.md)" >&2
  exit 1
fi
name=rok-$version-$triple

# install.sh downloads this version by default.
grep -q "^version=\"\${ROK_VERSION:-$version}\"" install.sh || {
  echo "dist.sh: install.sh's default version is not $version" >&2
  exit 1
}

stage=$out/$name
rm -rf "$stage" "$out/$name.tar.gz" "$out/$name.tar.gz.sha256"
mkdir -p "$stage/bin" "$stage/lib/rok"
for t in rok rokc rokls; do
  cp "$target/$t" "$stage/bin/"
done
cp "$target/librokr.a" "$stage/lib/"
# The library sources, without build output.
tar -C library --exclude target -cf - core std bare | tar -C "$stage/lib/rok" -xf -
cp install.sh README.md CHANGELOG.md LICENSE-MIT LICENSE-APACHE "$stage/"

# The toolchain runs from its new place, with no LLVM on PATH: its rokc
# finds its library and builds with its own LLVM and lld.
printf 'fn main() -> i32 {\n    println("ok");\n    0\n}\n' > "$stage/check.rok"
for o in -O0 -O2; do
  PATH=/usr/bin:/bin "$stage/bin/rokc" -q build "$stage/check.rok" $o -o "$stage/check"
  [ "$("$stage/check")" = ok ]
done
rm -rf "$stage/check.rok" "$stage/check" "$stage/lib/rok-cache"

tar -C "$out" -czf "$out/$name.tar.gz" "$name"
sum=$(command -v sha256sum || echo "shasum -a 256")
(cd "$out" && $sum "$name.tar.gz" > "$name.tar.gz.sha256")
rm -rf "$stage"
echo "$out/$name.tar.gz"

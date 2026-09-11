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
set -eu

cd "$(dirname "$0")"
out=dist
case "${1-}" in
  --out) out=$2 ;;
  "") ;;
  *) echo "usage: ./dist.sh [--out <dir>]" >&2; exit 2 ;;
esac

cargo build --release --locked -p rok -p rokc -p rokr

target=${CARGO_TARGET_DIR:-target}/release
version=$("$target/rokc" --version | awk '{ print $2 }')
triple=$("$target/rokc" --version --verbose | sed -n 's/^host: //p')
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

# The toolchain runs from its new place: its rokc finds its library.
printf 'let x: i32 = 1;\n' > "$stage/check.rok"
"$stage/bin/rokc" -q check "$stage/check.rok"
rm "$stage/check.rok"

tar -C "$out" -czf "$out/$name.tar.gz" "$name"
sum=$(command -v sha256sum || echo "shasum -a 256")
(cd "$out" && $sum "$name.tar.gz" > "$name.tar.gz.sha256")
rm -rf "$stage"
echo "$out/$name.tar.gz"

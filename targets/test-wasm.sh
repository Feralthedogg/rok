#!/bin/sh
# The wasm32 corpora: every integration and differential case built for
# each wasm32 target at -O0 and -O2 and run under the target's host, then
# the CLI tests that run wasm modules.
#
#   targets/test-wasm.sh [<target>..]   (default: all three)
#
# wasm32-wasi (a preview 2 component) and wasm32-wasi-threads (preview 1
# with wasi-threads) run under wasmtime v46.0.3, the last release with
# wasi-threads, fetched (SHA-256 checked) into the cache of
# targets/build.sh; wasm32-unknown-unknown runs under node (18+) with the
# shipped rok.mjs. The targets' runtimes are built first
# (targets/build.sh). Needs rustup, curl and, for the browser, node.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
cd "$here/.."
cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
V=v46.0.3

case $(uname -m) in
arm64 | aarch64) arch=aarch64 ;;
*) arch=x86_64 ;;
esac
case $(uname -s) in
Darwin) os=macos ext=tar.xz ;;
Linux) os=linux ext=tar.xz ;;
*) os=windows ext=zip ;;
esac
name=wasmtime-$V-$arch-$os
case $name in
wasmtime-$V-aarch64-linux) sha=99aa698281ce7c18cb174899df86296d730bf39d6e4826ae6e56a773e0cbe53f ;;
wasmtime-$V-aarch64-macos) sha=a5ae4844eedc9bce875b443ab07e3154f0ff06cb2959bbbbb734c0cde62fa39f ;;
wasmtime-$V-aarch64-windows) sha=92b78fce601267c4ed22c1e18383e8d7d44fd2cc67f862a705068087ca6ae8cb ;;
wasmtime-$V-x86_64-linux) sha=a13087bea96394e183a205d653e7337d50b596aca3090d496330efc770a54121 ;;
wasmtime-$V-x86_64-macos) sha=c30069bdd538a43cbcdc899d4e8041c4cad9b32a18b1c0fbacd0311b5950dbc2 ;;
wasmtime-$V-x86_64-windows) sha=35411bda40177b63e6ef3c4564a5d59eb29c031a1f42cb7201330e1819b57442 ;;
esac

file=$cache/$name.$ext
if [ ! -f "$file" ]; then
	mkdir -p "$cache"
	curl -fsSL --retry 3 -o "$file.part" "https://github.com/bytecodealliance/wasmtime/releases/download/$V/$name.$ext"
	mv "$file.part" "$file"
fi
got=$( (shasum -a 256 "$file" 2>/dev/null || sha256sum "$file") | cut -d' ' -f1)
if [ "$got" != "$sha" ]; then
	echo "checksum mismatch for $file: $got" >&2
	exit 1
fi
if [ ! -d "$cache/$name" ]; then
	case $ext in
	zip) (cd "$cache" && unzip -q "$file") ;;
	*) tar -xJf "$file" -C "$cache" ;;
	esac
fi
runner=$cache/$name/wasmtime
[ "$os" = windows ] && runner=$runner.exe

[ $# -gt 0 ] || set -- wasm32-wasi wasm32-wasi-threads wasm32-unknown-unknown
"$here/build.sh" "$@"

export ROK_REQUIRE_LLVM=1 ROK_TEST_WASM_RUNNER="$runner"
for t in "$@"; do
	for o in "" -O2; do
		echo "== $t ${o:--O0}"
		ROK_TEST_TARGET=$t ROK_TEST_OPT=$o cargo test --test integration --test differential
	done
done
cargo test --test cli -- cross_targets browser_module_exports_to_js profile_guided_optimization_on_wasm32_wasi

#!/bin/sh
# Regenerates llvm/rok.profdata.xz, the profile build.sh optimizes LLVM
# with.
#
#   llvm/train-pgo.sh [workdir]
#
# Builds an instrumented LLVM (build.sh with ROK_LLVM_INSTRUMENT=1) and a
# release rokc against it, then has that rokc build three quarters of
# compiler/rokc/tests/cases at -O2: two of three for the host (linked),
# the third as Linux objects of the other architecture (x86_64 on an
# arm64 host, aarch64 on an x86_64 one), so both main back ends are warm.
# The rest of the cases and bench/ are left to measure the result.
# macOS with Xcode's command line tools, or Linux with clang, its
# llvm-profdata and targets/build.sh's C library for the host (RUSTFLAGS,
# e.g. the nix shell's run path, is kept); workdir (default
# $ROK_LLVM_CACHE/pgo) peaks at ~5 GB and is deleted afterwards; about
# 35 minutes on 10 cores.
set -eu

root=$(cd "$(dirname "$0")/.." && pwd)
cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
work=${1:-$cache/pgo}
prof=$work/profiles
jobs=$(getconf _NPROCESSORS_ONLN)
case $(uname -m) in
x86_64) other=aarch64-unknown-linux-gnu ;;
*) other=x86_64-unknown-linux-gnu ;;
esac

ROK_LLVM_INSTRUMENT=1 "$root/llvm/build.sh" "$work/llvm"
# -fprofile-generate at the link pulls in the profile runtime. With an
# explicit --target, RUSTFLAGS reach rokc but not the build scripts,
# whose link (GNU ld) would put the runtime after libc.
host=$(rustc -vV | sed -n 's/^host: //p')
(cd "$root" && ROK_LLVM_PREFIX=$work/llvm CARGO_TARGET_DIR=$work/target \
	RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }-Clink-arg=-fprofile-generate" \
	cargo build --release -q --target "$host" -p rokc -p rokr)
rokc=$work/target/$host/release/rokc
# A Linux host links against the C library targets/build.sh made.
[ "$(uname -s)" = Darwin ] || ln -sfn "${CARGO_TARGET_DIR:-$root/target}/lib" "$work/target/$host/lib"
rokr=$work/target/$host/release/librokr.a

rm -rf "$prof"
mkdir -p "$prof/out"
export LLVM_PROFILE_FILE="$prof/%m.profraw" ROK_HOME="$root"
i=0 n=0
for f in "$root"/compiler/rokc/tests/cases/*.rok; do
	grep -q -e expect-error -e rokc-arg "$f" && continue
	i=$((i + 1))
	[ $((i % 4)) -eq 0 ] && continue
	n=$((n + 1))
	if [ $((n % 3)) -eq 0 ]; then
		"$rokc" -q build "$f" -O2 --target=$other \
			--emit=obj -o "$prof/out/$n.o" >/dev/null 2>&1 &
	else
		"$rokc" -q build "$f" -O2 --rokr "$rokr" -o "$prof/out/$n" \
			>/dev/null 2>&1 &
	fi
	[ $((n % jobs)) -eq 0 ] && wait
done
wait

# Sparse: functions the corpus never ran get no profile (optimized as
# without PGO) rather than a cold one.
profdata=llvm-profdata
[ "$(uname -s)" != Darwin ] || profdata="xcrun llvm-profdata"
$profdata merge --sparse -o "$work/rok.profdata" "$prof"/*.profraw
xz -9e <"$work/rok.profdata" >"$root/llvm/rok.profdata.xz"
rm -rf "$work"
ls -l "$root/llvm/rok.profdata.xz"

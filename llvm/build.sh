#!/bin/sh
# Builds the pinned LLVM + MLIR + lld that rokc links statically.
#
#   llvm/build.sh [prefix]
#
# prefix defaults to $ROK_LLVM_CACHE/llvm-<version>, ROK_LLVM_CACHE to
# ~/.cache/rok. The source and build trees live beside the prefix and are
# deleted once the install succeeds. Build rokc against the result with
# ROK_LLVM_PREFIX=<prefix>.
#
# Release static libraries only: no tools, tests, examples, docs or
# bindings; no zlib / zstd / libxml2 / terminfo, so the archives need
# nothing beyond the platform C++ runtime. Needs cmake, ninja, curl, xz
# and a C++17 compiler (Linux: `apt install cmake ninja-build g++ curl
# xz-utils`, `apk add cmake samurai g++ curl xz linux-headers`). Windows
# hosts: llvm/build.ps1.
set -eu

VERSION=22.1.8
SHA256=922f1817a0df7b1489272d18134ee0087a8b068828f87ac63b9861b1a9965888
TARGETS="AArch64;X86;ARM;RISCV;WebAssembly"

cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
prefix=${1:-$cache/llvm-$VERSION}
work=$prefix.work
jobs=${ROK_LLVM_JOBS:-$(getconf _NPROCESSORS_ONLN)}

built() {
	[ -f "$prefix/lib/cmake/mlir/MLIRConfig.cmake" ] && [ -f "$prefix/lib/liblldCommon.a" ]
}
dsym=$prefix/share/rok/dsymutil
if built && [ -f "$dsym/Options.inc" ]; then
	echo "LLVM $VERSION already in $prefix"
	exit 0
fi

mkdir -p "$work"
tarball=$work/llvm-project-$VERSION.src.tar.xz
if [ ! -f "$tarball" ]; then
	curl -fL --retry 3 -o "$tarball.part" \
		"https://github.com/llvm/llvm-project/releases/download/llvmorg-$VERSION/llvm-project-$VERSION.src.tar.xz"
	mv "$tarball.part" "$tarball"
fi
got=$( (shasum -a 256 "$tarball" 2>/dev/null || sha256sum "$tarball") | cut -d' ' -f1)
if [ "$got" != "$SHA256" ]; then
	echo "checksum mismatch for $tarball: $got" >&2
	exit 1
fi

src=$work/llvm-project-$VERSION.src
if [ ! -d "$src" ]; then
	# Only what the build reads.
	top=llvm-project-$VERSION.src
	tar -xJf "$tarball" -C "$work" "$top/llvm" "$top/mlir" "$top/lld" \
		"$top/cmake" "$top/third-party" "$top/libunwind/include"
fi

extra=
# PGO: a clang that reads rok.profdata.xz (a profile of rokc's own
# builds, made by train-pgo.sh) optimizes LLVM with it. Its names are
# Itanium-mangled, so the clang of any Unix host matches them. gcc reads
# no clang profile, and a clang older than the profile's indexed format
# cannot: those build without it (said here). ROK_LLVM_INSTRUMENT=1
# builds the instrumented libraries train-pgo.sh profiles instead.
here=$(cd "$(dirname "$0")" && pwd)
if [ -n "${ROK_LLVM_INSTRUMENT-}" ]; then
	extra="-DLLVM_BUILD_INSTRUMENTED=IR"
else
	xz -dc "$here/rok.profdata.xz" >"$work/rok.profdata"
	# clang reads the profile even for an empty unit.
	if echo 'int x;' | ${CXX:-c++} -x c++ -fprofile-instr-use="$work/rok.profdata" \
		-c -o /dev/null - 2>/dev/null; then
		extra="-DLLVM_PROFDATA_FILE=$work/rok.profdata"
	else
		echo "llvm/build.sh: ${CXX:-c++} cannot read llvm/rok.profdata.xz (gcc, or a clang" \
			"older than its format): building LLVM without PGO" >&2
	fi
fi
case $(uname -s) in
Darwin) extra="$extra -DCMAKE_OSX_DEPLOYMENT_TARGET=11.0" ;;
# The system compiler (gcc / libstdc++, or CC / CXX); x86_64 or aarch64,
# glibc or musl.
Linux) ;;
MINGW* | MSYS* | CYGWIN*)
	echo "on Windows run llvm/build.ps1 (MSVC ABI) instead" >&2
	exit 1
	;;
*)
	echo "llvm/build.sh: unsupported host $(uname -s)" >&2
	exit 1
	;;
esac

# shellcheck disable=SC2086
cmake -G Ninja -S "$src/llvm" -B "$work/build" \
	-DCMAKE_BUILD_TYPE=Release \
	-DCMAKE_INSTALL_PREFIX="$prefix" \
	-DLLVM_ENABLE_PROJECTS="mlir;lld" \
	-DLLVM_TARGETS_TO_BUILD="$TARGETS" \
	-DLLVM_ENABLE_ASSERTIONS=OFF \
	-DLLVM_ENABLE_RTTI=OFF \
	-DLLVM_BUILD_TOOLS=OFF \
	-DLLVM_BUILD_UTILS=OFF \
	-DLLVM_INCLUDE_TESTS=OFF \
	-DLLVM_INCLUDE_BENCHMARKS=OFF \
	-DLLVM_INCLUDE_EXAMPLES=OFF \
	-DLLVM_INCLUDE_DOCS=OFF \
	-DMLIR_INCLUDE_TESTS=OFF \
	-DMLIR_ENABLE_BINDINGS_PYTHON=OFF \
	-DLLVM_ENABLE_BINDINGS=OFF \
	-DLLVM_ENABLE_ZLIB=OFF \
	-DLLVM_ENABLE_ZSTD=OFF \
	-DLLVM_ENABLE_LIBXML2=OFF \
	-DLLVM_ENABLE_LIBEDIT=OFF \
	-DLLVM_ENABLE_LIBPFM=OFF \
	-DLLVM_ENABLE_TERMINFO=OFF \
	-DLLVM_ENABLE_Z3_SOLVER=OFF \
	-DLLVM_ENABLE_CURL=OFF \
	-DLLVM_ENABLE_HTTPLIB=OFF \
	$extra
if ! built; then
	cmake --build "$work/build" --target install -j "$jobs"
fi

# dsymutil is a tool, not a library: rokc compiles its sources itself
# (rokc_llvm's build.rs), with the option table generated here.
cmake --build "$work/build" --target DsymutilTableGen -j "$jobs"
mkdir -p "$dsym/llvm/Config"
cp "$src"/llvm/tools/dsymutil/*.cpp "$src"/llvm/tools/dsymutil/*.h "$dsym/"
# A private header of the build tree the sources include.
cp "$work/build/include/llvm/Config/config.h" "$dsym/llvm/Config/"
cp "$work/build/tools/dsymutil/Options.inc" "$dsym/"

rm -rf "$work"
du -sh "$prefix"

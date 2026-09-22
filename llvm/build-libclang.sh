#!/bin/sh
# Builds libclang (the shared library) and clang's resource headers from
# the pinned LLVM source, for `rokc bindgen`.
#
#   llvm/build-libclang.sh [prefix]
#
# prefix defaults to $ROK_LLVM_CACHE/libclang-<version>, ROK_LLVM_CACHE
# to ~/.cache/rok. Independent of build.sh's prefix: rokc does not link
# libclang, it loads it at run time. The source and build trees live
# beside the prefix and are deleted once the install succeeds.
#
# Installs lib/libclang.{dylib,so} and lib/clang/<major>/include only.
# No LLVM back end is built: parsing needs clang's own target info,
# not LLVM's code generators. Needs what build.sh needs, plus python3
# on macOS (the export list). Windows hosts: llvm/build-libclang.ps1.
set -eu

VERSION=22.1.8
SHA256=922f1817a0df7b1489272d18134ee0087a8b068828f87ac63b9861b1a9965888

cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
prefix=${1:-$cache/libclang-$VERSION}
work=$prefix.work
jobs=${ROK_LLVM_JOBS:-$(getconf _NPROCESSORS_ONLN)}

case $(uname -s) in
Darwin) lib=libclang.dylib extra="-DCMAKE_OSX_DEPLOYMENT_TARGET=11.0" ;;
Linux) lib=libclang.so extra= ;;
MINGW* | MSYS* | CYGWIN*)
	echo "on Windows run llvm/build-libclang.ps1 (MSVC ABI) instead" >&2
	exit 1
	;;
*)
	echo "llvm/build-libclang.sh: unsupported host $(uname -s)" >&2
	exit 1
	;;
esac

major=${VERSION%%.*}
if [ -f "$prefix/lib/$lib" ] && [ -f "$prefix/lib/clang/$major/include/stddef.h" ]; then
	echo "libclang $VERSION already in $prefix"
	exit 0
fi

mkdir -p "$work"
# build.sh's tarball when it is still there.
tarball=$work/llvm-project-$VERSION.src.tar.xz
for t in "$cache/llvm-project-$VERSION.src.tar.xz" "$cache/llvm-$VERSION.work/llvm-project-$VERSION.src.tar.xz"; do
	[ -f "$tarball" ] || [ ! -f "$t" ] || tarball=$t
done
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
	top=llvm-project-$VERSION.src
	tar -xJf "$tarball" -C "$work" "$top/llvm" "$top/clang" "$top/cmake" "$top/third-party"
fi

# shellcheck disable=SC2086
cmake -G Ninja -S "$src/llvm" -B "$work/build" \
	-DCMAKE_BUILD_TYPE=Release \
	-DCMAKE_INSTALL_PREFIX="$prefix" \
	-DLLVM_ENABLE_PROJECTS=clang \
	-DLLVM_TARGETS_TO_BUILD= \
	-DLLVM_ENABLE_ASSERTIONS=OFF \
	-DLLVM_ENABLE_RTTI=OFF \
	-DLLVM_BUILD_TOOLS=OFF \
	-DLLVM_BUILD_UTILS=OFF \
	-DLLVM_INCLUDE_TESTS=OFF \
	-DLLVM_INCLUDE_BENCHMARKS=OFF \
	-DLLVM_INCLUDE_EXAMPLES=OFF \
	-DLLVM_INCLUDE_DOCS=OFF \
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
	-DCLANG_BUILD_TOOLS=OFF \
	-DCLANG_INCLUDE_TESTS=OFF \
	-DCLANG_INCLUDE_DOCS=OFF \
	-DCLANG_ENABLE_STATIC_ANALYZER=OFF \
	-DCLANG_PLUGIN_SUPPORT=OFF \
	-DCLANG_PYTHON_BINDINGS_VERSIONS= \
	$extra
cmake --build "$work/build" --target libclang -j "$jobs"
cmake --build "$work/build" --target install-libclang-stripped install-clang-resource-headers -j "$jobs"

rm -rf "$work"
du -sh "$prefix"

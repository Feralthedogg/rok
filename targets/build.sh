#!/bin/sh
# Builds what rokc links for a --target (spec 9.2.14), into
# <cargo target dir>/lib/rok/targets/<triple>/ (a toolchain's lib/rok/targets/):
#
#   librokr.a            the runtime, by cargo for that target
#                        (Windows: rokr.lib; rokc carries the rest)
#   Linux, -musl:        crt1.o crti.o crtn.o libc.a: musl, the copy the
#                        pinned Rust toolchain ships for the target
#   Linux, -gnu(eabihf): Scrt1.o crti.o crtn.o libc_nonshared.a and stub
#                        libc.so / libm.so (sonames .so.6), made by
#                        glibc_stubs.py from glibc 2.36 (Debian 12 amd64 /
#                        arm64 / i386 / armhf; the packages are checked
#                        against pinned SHA-256s). Executables need
#                        glibc >= 2.34 (the 32-bit runtimes call its
#                        time64 symbols, .cargo/config.toml).
#   wasm32-*:            crt1-command.o libc.a: wasi-libc, the copy the
#                        pinned Rust toolchain ships for the Rust target
#                        the runtime is built for: wasm32-wasip2 for
#                        wasm32-wasi (plus that toolchain's
#                        wasm-component-ld, which makes the component),
#                        wasm32-wasip1-threads for wasm32-wasi-threads,
#                        wasm32-wasip1 for wasm32-unknown-unknown (plus
#                        rok.mjs, the JS host that gives a browser or node
#                        the WASI imports it uses).
#   libclang_rt.profile.a  what `-C profile-generate` links: compiler-rt's
#                        profile runtime from the pinned LLVM's sources,
#                        compiled with clang against the target's C
#                        headers (Apple: the macOS SDK, on a macOS host
#                        only; glibc: Debian 12's, with linux-libc-dev
#                        6.1; musl: musl 1.2.5's; Windows:
#                        clang_rt.profile.lib, against mingw-w64's
#                        headers, with profile_windows.c). Every target
#                        but wasm32, which it does not support.
#
#   targets/build.sh [<triple>...]
#
# Default: every shipped target (an Apple host's runtime is lib/librokr.a:
# only its profile runtime is built here). Needs rustup (and its
# llvm-tools component's llvm-ar), curl, make, python3, clang (as the
# assembler and C compiler) and the pinned LLVM's ld.lld (ROK_LLVM_PREFIX,
# else llvm/build.sh's).
set -eu

TARGETS="x86_64-apple-darwin aarch64-apple-darwin x86_64-unknown-linux-gnu
aarch64-unknown-linux-gnu x86_64-unknown-linux-musl aarch64-unknown-linux-musl
x86_64-pc-windows-msvc aarch64-pc-windows-msvc i686-unknown-linux-gnu
i686-pc-windows-msvc armv7-unknown-linux-gnueabihf wasm32-wasi
wasm32-wasi-threads wasm32-unknown-unknown"
GLIBC=2.36-9+deb12u14
GLIBC_URL=https://snapshot.debian.org/archive/debian/20260504T025922Z/pool/main/g/glibc
LINUX=6.1.159-1
LINUX_URL=https://snapshot.debian.org/archive/debian/20260504T025922Z/pool/main/l/linux
# <package>_<arch> <sha256>
DEB_SHA256="
libc6_amd64 ba4f88f73dbc3ae9055f3c20f4523bfdbaf1ad13ff95e258924f77d20b4fbedf
libc6_arm64 01f4330719fd4f65580e16ea5a0527f372fca750e8f588d26deaf09f2d3b1cf4
libc6-dev_amd64 0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae
libc6-dev_arm64 8bc395bf2ee9939f1a6ae395f974cffdcf541d98f99adfe89ce7e4bef36d159e
libc6_i386 76b12e06be66ec3fc2c1791d7d8cf34c2b828ed210e3913feeeb8edc9688f820
libc6-dev_i386 c02c0adacabf53b8f34364940c7c4fe5aedaf921765e915742cc31ffc7a9d1ad
libc6_armhf 758c68b92654747025b48476a45c315bf16df1321224abdd9be672bfd120be45
libc6-dev_armhf ca9486dc7f2dfb25c61c0c93d561c01f8abdf9866bd4c157f0ccd518295bbbb7
linux-libc-dev_amd64 117349f98e0d9c4522bf1b8f33c6239ab9c4c5904c56f6379be3eb790a97e7dc
linux-libc-dev_arm64 6da0f62a7a63524364bc0f4da96d11181cc15010051ff2f4c0dbd4a0ca5e085c
linux-libc-dev_i386 72e870c8b56344008990a7939edd44f71ae728152b5473c0fcc95a191a04d05f
linux-libc-dev_armhf 536d83afebd9a89e35dd104a4f3529b34833fd5fe279c4df18f2c6e9174f0e47"
MUSL=1.2.5
MUSL_SHA256=a9a118bbe84d8764da0ea0d28b3ab3fae8477fc7e4085d90102b8596fc7c75e4
# The commit of the module definitions rokc carries (gen.sh).
MINGW_SHA256=94469ea48f974f9a4f7d8b7050cb7eceaa92c1f941ed3b6b8137591ba19491de

here=$(cd "$(dirname "$0")" && pwd)
# The host's executable suffix.
exe() { case $(uname -s) in MINGW* | MSYS* | CYGWIN*) echo .exe ;; esac; }
cd "$here/.."
cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
lld=${ROK_LLVM_PREFIX:-$cache/llvm-22.1.8}/bin/ld.lld
out=${CARGO_TARGET_DIR:-target}/lib/rok/targets
host=$(rustc -vV | sed -n 's/^host: //p')
sysroot=$(rustc --print sysroot)
rustup component add llvm-tools >/dev/null
ar=$sysroot/lib/rustlib/$host/bin/llvm-ar
LLVM=$(sed -n 's/^VERSION=//p' llvm/build.sh)
LLVM_SHA256=$(sed -n 's/^SHA256=//p' llvm/build.sh)
MINGW=$(sed -n 's/^COMMIT=//p' compiler/rokc_driver/windows/gen.sh)

# $1 downloaded from $2 into the cache, checked against SHA-256 $3.
fetch() {
	file=$cache/$1
	if [ ! -f "$file" ]; then
		mkdir -p "$(dirname "$file")"
		curl -fsSL --retry 3 -o "$file.part" "$2"
		mv "$file.part" "$file"
	fi
	got=$( (shasum -a 256 "$file" 2>/dev/null || sha256sum "$file") | cut -d' ' -f1)
	if [ "$got" != "$3" ]; then
		echo "checksum mismatch for $file: $got" >&2
		exit 1
	fi
}

# A Debian package's data.tar.xz, verified, unpacked under $1.
deb() {
	into=$1 pkg=$2 darch=$3
	[ -f "$into/.$pkg" ] && return
	case $pkg in
	linux-*) version=$LINUX url=$LINUX_URL ;;
	*) version=$GLIBC url=$GLIBC_URL ;;
	esac
	name=${pkg}_${version}_$darch.deb
	fetch "glibc-$GLIBC/$name" "$url/$name" "$(echo "$DEB_SHA256" | sed -n "s/^${pkg}_$darch //p")"
	mkdir -p "$into"
	tar -xOf "$cache/glibc-$GLIBC/$name" data.tar.xz | tar -xJf - -C "$into"
	touch "$into/.$pkg"
}

# Debian's architecture and multiarch directory of a Linux target.
debian() {
	case ${1%%-*} in
	x86_64) deb=amd64 multi=x86_64-linux-gnu ;;
	aarch64) deb=arm64 multi=aarch64-linux-gnu ;;
	i686) deb=i386 multi=i386-linux-gnu ;;
	armv7) deb=armhf multi=arm-linux-gnueabihf ;;
	esac
	root=$cache/glibc-$GLIBC/$deb
}

# compiler-rt's profile runtime for $1 into $2: its sources from the
# pinned LLVM's tarball, the C headers per target.
profile() {
	t=$1 dir=$2
	arch=${t%%-*}
	src=$cache/compiler-rt-$LLVM
	if [ ! -d "$src" ]; then
		fetch "llvm-project-$LLVM.src.tar.xz" \
			"https://github.com/llvm/llvm-project/releases/download/llvmorg-$LLVM/llvm-project-$LLVM.src.tar.xz" \
			"$LLVM_SHA256"
		top=llvm-project-$LLVM.src/compiler-rt
		tar -xJf "$cache/llvm-project-$LLVM.src.tar.xz" -C "$cache" "$top/lib/profile" "$top/include/profile"
		mv "$cache/$top" "$src"
		rmdir "$cache/llvm-project-$LLVM.src"
	fi
	format=gnu
	unix="-fPIC -DCOMPILER_RT_HAS_FCNTL_LCK=1 -DCOMPILER_RT_HAS_FLOCK=1 -DCOMPILER_RT_HAS_UNAME=1"
	lib=libclang_rt.profile.a
	extra=
	case $t in
	*-apple-*)
		if [ "$(uname -s)" != Darwin ]; then
			echo "$t: no profile runtime (needs the macOS SDK)" >&2
			return
		fi
		format=darwin
		flags="--target=$arch-apple-macosx11.0 -isysroot $(xcrun --show-sdk-path) $unix"
		;;
	*-linux-musl)
		inc=$cache/musl-$MUSL/$arch
		if [ ! -d "$inc" ]; then
			fetch "musl-$MUSL.tar.gz" "https://musl.libc.org/releases/musl-$MUSL.tar.gz" "$MUSL_SHA256"
			work=$cache/musl-$MUSL/src
			rm -rf "$work"
			mkdir -p "$work"
			tar -xzf "$cache/musl-$MUSL.tar.gz" -C "$work"
			make -s -C "$work/musl-$MUSL" ARCH="$arch" prefix= DESTDIR="$inc" install-headers
			rm -rf "$work"
		fi
		flags="--target=$t -nostdlibinc -isystem $inc/include $unix"
		;;
	*-linux-gnu | *-linux-gnueabihf)
		debian "$t"
		deb "$root" libc6-dev "$deb"
		deb "$root" linux-libc-dev "$deb"
		flags="--target=$t --sysroot=$root $unix"
		case $arch in
		armv7) flags="$flags -mfloat-abi=hard -mfpu=neon" ;;
		esac
		;;
	*-windows-msvc)
		# mingw-w64's headers expect its own target; the objects are
		# COFF with the same C ABI. Its UCRT headers, version 0xa00.
		inc=$cache/mingw-w64-$MINGW
		if [ ! -d "$inc" ]; then
			fetch "mingw-w64-$MINGW.tar.gz" "https://github.com/mingw-w64/mingw-w64/archive/$MINGW.tar.gz" "$MINGW_SHA256"
			tar -xzf "$cache/mingw-w64-$MINGW.tar.gz" -C "$cache" "mingw-w64-$MINGW/mingw-w64-headers/crt" \
				"mingw-w64-$MINGW/mingw-w64-headers/include"
			rm -rf "$inc.tmp"
			mv "$cache/mingw-w64-$MINGW/mingw-w64-headers" "$inc.tmp"
			rm -rf "$cache/mingw-w64-$MINGW"
			sed -e 's/@DEFAULT_MSVCRT_VERSION@/0xE00/' -e 's/@DEFAULT_WIN32_WINNT@/0xa00/' \
				"$inc.tmp/crt/_mingw.h.in" >"$inc.tmp/crt/_mingw.h"
			mv "$inc.tmp" "$inc"
		fi
		flags="--target=$arch-w64-windows-gnu -nostdlibinc -isystem $inc/crt -isystem $inc/include -D_UCRT"
		lib=clang_rt.profile.lib format=coff
		extra=$here/profile_windows.c
		;;
	*)
		return
		;;
	esac
	work=$dir/profile
	mkdir -p "$work"
	for f in "$src"/lib/profile/*.c "$src"/lib/profile/*.cpp $extra; do
		# profile_windows.c registers the runtime instead.
		case $t,${f##*/} in *-windows-*,InstrProfilingRuntime.cpp) continue ;; esac
		# shellcheck disable=SC2086
		clang $flags -O2 -fno-exceptions -fno-rtti -nostdinc++ -w -DCOMPILER_RT_HAS_ATOMICS=1 \
			-I"$src/lib" -I"$src/include" -c "$f" -o "$work/${f##*/}.o"
	done
	rm -f "$dir/$lib"
	"$ar" rcs --format=$format "$dir/$lib" "$work"/*.o
	rm -rf "$work"
}

for t in ${*:-$TARGETS}; do
	dir=$out/$t
	case $t in *-apple-*) if [ "$t" = "$host" ]; then
		rm -rf "$dir"
		mkdir -p "$dir"
		profile "$t" "$dir"
		echo "$dir"
		continue
	fi ;; esac
	case $t in
	wasm32-wasi) rust=wasm32-wasip2 ;;
	wasm32-wasi-threads) rust=wasm32-wasip1-threads ;;
	wasm32-unknown-unknown) rust=wasm32-wasip1 ;;
	*) rust=$t ;;
	esac
	rustup target add "$rust" >/dev/null
	cargo build --release --locked -p rokr --target "$rust"
	rm -rf "$dir"
	mkdir -p "$dir"
	case $t in *-windows-*) rt=rokr.lib ;; *) rt=librokr.a ;; esac
	cp "${CARGO_TARGET_DIR:-target}/$rust/release/$rt" "$dir/"
	case $t in
	wasm32-*)
		for f in crt1-command.o libc.a; do
			cp "$sysroot/lib/rustlib/$rust/lib/self-contained/$f" "$dir/"
		done
		case $t in
		wasm32-wasi) cp "$sysroot/lib/rustlib/$host/bin/wasm-component-ld$(exe)" "$dir/" ;;
		wasm32-unknown-unknown) cp "$here/rok.mjs" "$dir/" ;;
		esac
		;;
	*-linux-musl)
		for f in crt1.o crti.o crtn.o libc.a; do
			cp "$sysroot/lib/rustlib/$t/lib/self-contained/$f" "$dir/"
		done
		;;
	*-linux-gnu | *-linux-gnueabihf)
		debian "$t"
		deb "$root" libc6 "$deb"
		deb "$root" libc6-dev "$deb"
		for f in Scrt1.o crti.o crtn.o libc_nonshared.a; do
			cp "$root/usr/lib/$multi/$f" "$dir/"
		done
		work=$dir/stub
		mkdir -p "$work"
		for lib in c m; do
			python3 "$here/glibc_stubs.py" "$root/lib/$multi/lib$lib.so.6" "$work/$lib.s" "$work/$lib.map"
			clang --target="$t" -c "$work/$lib.s" -o "$work/$lib.o"
			"$lld" -shared -soname "lib$lib.so.6" --version-script "$work/$lib.map" -o "$dir/lib$lib.so" "$work/$lib.o"
		done
		rm -rf "$work"
		;;
	esac
	profile "$t" "$dir"
	echo "$dir"
done

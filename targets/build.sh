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
#                        glibc >= 2.34.
#
#   targets/build.sh [<triple>...]
#
# Default: every shipped target but an Apple host (whose runtime is
# lib/librokr.a). Needs rustup, curl, python3, clang (as the assembler)
# and the pinned LLVM's ld.lld (ROK_LLVM_PREFIX, else llvm/build.sh's).
set -eu

TARGETS="x86_64-apple-darwin aarch64-apple-darwin x86_64-unknown-linux-gnu
aarch64-unknown-linux-gnu x86_64-unknown-linux-musl aarch64-unknown-linux-musl
x86_64-pc-windows-msvc aarch64-pc-windows-msvc i686-unknown-linux-gnu
i686-pc-windows-msvc armv7-unknown-linux-gnueabihf"
GLIBC=2.36-9+deb12u14
GLIBC_URL=https://snapshot.debian.org/archive/debian/20260504T025922Z/pool/main/g/glibc
# <package>_<arch> <sha256>
GLIBC_SHA256="
libc6_amd64 ba4f88f73dbc3ae9055f3c20f4523bfdbaf1ad13ff95e258924f77d20b4fbedf
libc6_arm64 01f4330719fd4f65580e16ea5a0527f372fca750e8f588d26deaf09f2d3b1cf4
libc6-dev_amd64 0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae
libc6-dev_arm64 8bc395bf2ee9939f1a6ae395f974cffdcf541d98f99adfe89ce7e4bef36d159e
libc6_i386 76b12e06be66ec3fc2c1791d7d8cf34c2b828ed210e3913feeeb8edc9688f820
libc6-dev_i386 c02c0adacabf53b8f34364940c7c4fe5aedaf921765e915742cc31ffc7a9d1ad
libc6_armhf 758c68b92654747025b48476a45c315bf16df1321224abdd9be672bfd120be45
libc6-dev_armhf ca9486dc7f2dfb25c61c0c93d561c01f8abdf9866bd4c157f0ccd518295bbbb7"

here=$(cd "$(dirname "$0")" && pwd)
cd "$here/.."
cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
lld=${ROK_LLVM_PREFIX:-$cache/llvm-22.1.8}/bin/ld.lld
out=${CARGO_TARGET_DIR:-target}/lib/rok/targets
host=$(rustc -vV | sed -n 's/^host: //p')
sysroot=$(rustc --print sysroot)

# A Debian package's data.tar.xz, verified, unpacked under $1.
deb() {
	into=$1 pkg=$2 darch=$3
	[ -f "$into/.$pkg" ] && return
	file=$cache/glibc-$GLIBC/${pkg}_${GLIBC}_$darch.deb
	if [ ! -f "$file" ]; then
		mkdir -p "$(dirname "$file")"
		curl -fsSL --retry 3 -o "$file.part" "$GLIBC_URL/${pkg}_${GLIBC}_$darch.deb"
		mv "$file.part" "$file"
	fi
	want=$(echo "$GLIBC_SHA256" | sed -n "s/^${pkg}_$darch //p")
	got=$( (shasum -a 256 "$file" 2>/dev/null || sha256sum "$file") | cut -d' ' -f1)
	if [ "$got" != "$want" ]; then
		echo "checksum mismatch for $file: $got" >&2
		exit 1
	fi
	mkdir -p "$into"
	tar -xOf "$file" data.tar.xz | tar -xJf - -C "$into"
	touch "$into/.$pkg"
}

for t in ${*:-$TARGETS}; do
	case $t in *-apple-*) [ "$t" = "$host" ] && continue ;; esac
	rustup target add "$t" >/dev/null
	cargo build --release --locked -p rokr --target "$t"
	dir=$out/$t
	rm -rf "$dir"
	mkdir -p "$dir"
	case $t in *-windows-*) rt=rokr.lib ;; *) rt=librokr.a ;; esac
	cp "${CARGO_TARGET_DIR:-target}/$t/release/$rt" "$dir/"
	case $t in
	*-linux-musl)
		for f in crt1.o crti.o crtn.o libc.a; do
			cp "$sysroot/lib/rustlib/$t/lib/self-contained/$f" "$dir/"
		done
		;;
	*-linux-gnu | *-linux-gnueabihf)
		# Debian's architecture and multiarch directory.
		case ${t%%-*} in
		x86_64) deb=amd64 multi=x86_64-linux-gnu ;;
		aarch64) deb=arm64 multi=aarch64-linux-gnu ;;
		i686) deb=i386 multi=i386-linux-gnu ;;
		armv7) deb=armhf multi=arm-linux-gnueabihf ;;
		esac
		root=$cache/glibc-$GLIBC/$deb
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
	echo "$dir"
done

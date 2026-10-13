#!/bin/sh
# Regenerate the module definitions rokc builds Windows import libraries
# from (`windows/<arch>/<lib>.def`): mingw-w64's, at a pinned commit,
# preprocessed per arch. Needs curl and clang (as the preprocessor).
set -eu

COMMIT=63ebe6cdb3ec4d5c586b7f0f0c03dd502e44c296
BASE=https://raw.githubusercontent.com/mingw-w64/mingw-w64/$COMMIT/mingw-w64-crt
# <link name> <source under mingw-w64-crt/> <i686 source, when different>
# (lib32/: the x86 names, stdcall-decorated)
LIBS="
ucrtbase lib-common/ucrtbase.def.in
kernel32 lib-common/kernel32.def.in lib32/kernel32.def
ntdll lib-common/ntdll.def.in lib32/ntdll.def
ws2_32 lib-common/ws2_32.def.in
advapi32 lib-common/advapi32.def.in lib32/advapi32.def
bcrypt lib-common/bcrypt.def lib32/bcrypt.def
synchronization lib-common/api-ms-win-core-synch-l1-2-0.def lib32/api-ms-win-core-synch-l1-2-0.def
userenv lib-common/userenv.def lib32/userenv.def
shell32 lib-common/shell32.def lib32/shell32.def
ole32 lib-common/ole32.def.in lib32/ole32.def
user32 lib-common/user32.def.in lib32/user32.def"
INCLUDES="def-include/func.def.in def-include/crt-aliases.def.in lib-common/ucrtbase-common.def.in"

here=$(cd "$(dirname "$0")" && pwd)
src=$(mktemp -d)
trap 'rm -rf "$src"' EXIT

fetch() {
	mkdir -p "$src/$(dirname "$1")"
	curl -fsSL --retry 3 -o "$src/$1" "$BASE/$1"
}
for f in $INCLUDES; do fetch "$f"; done
echo "$LIBS" | while read -r name path x86; do
	[ -n "$name" ] || continue
	fetch "$path"
	[ -z "$x86" ] || fetch "$x86"
done
curl -fsSL --retry 3 -o "$here/COPYING.mingw-w64" "${BASE%/mingw-w64-crt}/COPYING"

for arch in x86_64 aarch64 i686; do
	mkdir -p "$here/$arch"
	echo "$LIBS" | while read -r name path x86; do
		[ -n "$name" ] || continue
		# stdcall's `@<bytes>` stays on x86 (rokc imports those
		# undecorated, like dlltool -k); the other arches have none.
		strip='s/^\([A-Za-z_][A-Za-z0-9_]*\)@[0-9][0-9]*/\1/'
		if [ "$arch" = i686 ]; then
			strip='s/^$//'
			path=${x86:-$path}
		fi
		{
			echo "; $(basename "$path") of mingw-w64 $COMMIT (COPYING.mingw-w64),"
			echo "; preprocessed for $arch-pc-windows-msvc by gen.sh, comments dropped."
			clang -E -P -x c -target "$arch-pc-windows-msvc" -w -I"$src/def-include" "$src/$path" |
				sed -e 's/[[:space:]]*;.*$//' -e '/^[[:space:]]*$/d' -e "$strip"
			# The 64-bit arithmetic helpers LLVM calls on x86 (MSVC's
			# names), which x86 ntdll exports and mingw-w64 lists not.
			if [ "$arch$name" = i686ntdll ]; then
				printf '%s\n' _alldiv _alldvrm _allmul _allrem _allshl _allshr \
					_aulldiv _aulldvrm _aullrem _aullshr
			fi
		} > "$here/$arch/$name.def"
	done
done

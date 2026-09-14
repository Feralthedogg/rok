#!/bin/sh
# Regenerates the module definitions rokc builds Windows import
# libraries from (`windows/<arch>/<lib>.def`, embedded in rokc): the
# mingw-w64 CRT's, at a pinned commit, preprocessed for each arch.
#
#   compiler/rokc_driver/windows/gen.sh
#
# Needs curl and clang (only as the C preprocessor).
set -eu

COMMIT=63ebe6cdb3ec4d5c586b7f0f0c03dd502e44c296
BASE=https://raw.githubusercontent.com/mingw-w64/mingw-w64/$COMMIT/mingw-w64-crt
# <link name> <source under mingw-w64-crt/>
LIBS="
ucrtbase lib-common/ucrtbase.def.in
kernel32 lib-common/kernel32.def.in
ntdll lib-common/ntdll.def.in
ws2_32 lib-common/ws2_32.def.in
advapi32 lib-common/advapi32.def.in
bcrypt lib-common/bcrypt.def
synchronization lib-common/api-ms-win-core-synch-l1-2-0.def
userenv lib-common/userenv.def
shell32 lib-common/shell32.def
ole32 lib-common/ole32.def.in
user32 lib-common/user32.def.in"
INCLUDES="def-include/func.def.in def-include/crt-aliases.def.in lib-common/ucrtbase-common.def.in"

here=$(cd "$(dirname "$0")" && pwd)
src=$(mktemp -d)
trap 'rm -rf "$src"' EXIT

fetch() {
	curl -fsSL --retry 3 -o "$src/$(basename "$1")" "$BASE/$1"
}
for f in $INCLUDES; do fetch "$f"; done
echo "$LIBS" | while read -r name path; do
	[ -n "$name" ] && fetch "$path"
done
curl -fsSL --retry 3 -o "$here/COPYING.mingw-w64" "${BASE%/mingw-w64-crt}/COPYING"

for arch in x86_64 aarch64; do
	mkdir -p "$here/$arch"
	echo "$LIBS" | while read -r name path; do
		[ -n "$name" ] || continue
		out=$here/$arch/$name.def
		{
			echo "; $(basename "$path") of mingw-w64 $COMMIT (COPYING.mingw-w64),"
			echo "; preprocessed for $arch-pc-windows-msvc by gen.sh, comments dropped."
			# No stdcall on these arches: drop `@<bytes>` (dlltool's -k).
			clang -E -P -x c -target "$arch-pc-windows-msvc" -w -I"$src" "$src/$(basename "$path")" |
				sed -e 's/[[:space:]]*;.*$//' -e '/^[[:space:]]*$/d' \
					-e 's/^\([A-Za-z_][A-Za-z0-9_]*\)@[0-9][0-9]*/\1/'
		} > "$out"
	done
done

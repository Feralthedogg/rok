#!/bin/sh
# Rewrite the archive <in> as <out>: one relocatable object in which only
# the `rok_*` symbols stay global. The `core` / `compiler_builtins` /
# mangled Rust symbols cargo leaves exported become local, so librokr.a
# links next to another Rust staticlib.
#
# Usage: runtime/rokr/localize.sh <in.a> <out.a>   (or <in.lib> <out.lib>)
set -eu

in=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
out=$2
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

case $in in
  *.lib)
    # COFF has no relocatable link (lld-link has no -r), so a member
    # cannot see another's symbols once they are local: rokr.lib ships
    # as cargo built it.
    cp "$in" "$out"
    exit 0
    ;;
esac

case $(uname -s) in
  Darwin)
    # ld64 -r ignores archive members even under -all_load: pass objects.
    mkdir "$tmp/x"
    (cd "$tmp/x" && ar x "$in")
    cc -r -nostdlib "$tmp"/x/*.o -Wl,-exported_symbol,'_rok_*' -o "$tmp/rokr.o"
    ;;
  *)
    ld -r --whole-archive "$in" -o "$tmp/rokr.o"
    objcopy --wildcard --keep-global-symbol='rok_*' "$tmp/rokr.o"
    ;;
esac

rm -f "$out"
ar rcs "$out" "$tmp/rokr.o"

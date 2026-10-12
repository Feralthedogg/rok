#!/bin/sh
# Rewrite the archive <in> as <out>: one relocatable object in which only
# the `rok_*` symbols stay global (ELF: and compiler_builtins' `__*`
# intrinsics, weak). The `core` / mangled Rust symbols cargo leaves
# exported become local, so librokr.a links next to another Rust
# staticlib. <in> is built with fat LTO
# (dist.sh, targets/build.sh): its Rust code is one object exporting only
# `rok_*`.
#
# ELF (any host): the pinned LLVM's ld.lld -r (ROK_LLVM_PREFIX, else
# llvm/build.sh's), then llvm-objcopy and llvm-ar from rustup's
# llvm-tools component. Mach-O (macOS hosts): the system cc -r (ld64).
# COFF (any host): llvm-nm, llvm-objcopy and llvm-ar.
#
# Usage: runtime/rokr/localize.sh <in.a> <out.a>   (or <in.lib> <out.lib>)
set -eu

in=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
out=$2
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

case $(uname -s) in MINGW* | MSYS* | CYGWIN*) exe=.exe ;; *) exe="" ;; esac
host=$(rustc -vV | sed -n 's/^host: //p')
rustup component add llvm-tools >/dev/null
bin=$(rustc --print sysroot)/lib/rustlib/$host/bin
cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
lld=${ROK_LLVM_PREFIX:-$cache/llvm-22.1.8}/bin/ld.lld$exe

mkdir "$tmp/x"
(cd "$tmp/x" && "$bin/llvm-ar$exe" x "$in")
first=$(ls "$tmp"/x/*.o | head -n 1)
case $in in *.lib) magic=COFF ;; *) magic=$(od -An -c -N4 "$first" | tr -d ' ') ;; esac
case $magic in
  COFF)
    # No relocatable link (lld-link has no -r), and llvm-objcopy cannot
    # make a COFF symbol local. Fat LTO leaves rokr's Rust code one
    # object defining only `rok*` globals; every other global definition
    # (compiler_builtins' members, which rustc keeps out of LTO) becomes
    # `rokr.<name>` in every member, references included, so it never
    # meets another staticlib's. The intrinsics are weak externals
    # already and keep their names. x86 spells C names `_rok*`.
    "$bin/llvm-nm$exe" --defined-only --extern-only "$tmp"/x/*.o |
      awk '$2 ~ /^[TDRB]$/ && $3 !~ /^_?rok/ { print $3, "rokr." $3 }' | sort -u >"$tmp/names"
    for o in "$tmp"/x/*.o; do
      "$bin/llvm-objcopy$exe" --redefine-syms="$tmp/names" "$o"
    done
    rm -f "$out"
    "$bin/llvm-ar$exe" rcs --format=coff "$out" "$tmp"/x/*.o
    exit 0
    ;;
  177ELF)
    "$lld" -r --whole-archive "$in" -o "$tmp/rokr.o"
    # compiler_builtins' intrinsics stay global for the C library
    # (aarch64 musl's long double code calls `__netf2`), but weak: they
    # yield to another staticlib's copy. No debug info, as the release
    # profile strips rokr's own: the precompiled core / compiler_builtins
    # units of code the final link drops would sit at the DWARF tombstone.
    "$bin/llvm-objcopy$exe" --strip-debug --wildcard \
      --keep-global-symbol='rok_*' --keep-global-symbol='__*' \
      --weaken-symbol='__*' "$tmp/rokr.o"
    format=gnu
    ;;
  *)
    # Mach-O. ld64 -r ignores archive members even under -all_load: pass
    # the objects. -S: no debug info either. The exports are listed by
    # name: ld64 refuses to export a private extern (`_rok_tls_addr`)
    # that a `_rok_*` pattern matches; private externs become local.
    nm -gmU "$tmp"/x/*.o | awk '$0 !~ /private external/ && $NF ~ /^_rok_/ { print $NF }' |
      sort -u >"$tmp/exports"
    cc -r -nostdlib -arch "$(lipo -archs "$first")" "$tmp"/x/*.o \
      -Wl,-exported_symbols_list,"$tmp/exports" -Wl,-S -o "$tmp/rokr.o"
    format=darwin
    ;;
esac

rm -f "$out"
"$bin/llvm-ar$exe" rcs --format=$format "$out" "$tmp/rokr.o"

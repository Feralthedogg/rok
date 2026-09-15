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
#
# Usage: runtime/rokr/localize.sh <in.a> <out.a>   (or <in.lib> <out.lib>)
set -eu

in=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
out=$2
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

case $in in
  *.lib)
    # COFF has no relocatable link (lld-link has no -r): fat LTO's one
    # object is the localization. compiler_builtins' members stay as
    # rustc leaves them in any MSVC staticlib.
    cp "$in" "$out"
    exit 0
    ;;
esac

case $(uname -s) in MINGW* | MSYS* | CYGWIN*) exe=.exe ;; *) exe="" ;; esac
host=$(rustc -vV | sed -n 's/^host: //p')
rustup component add llvm-tools >/dev/null
bin=$(rustc --print sysroot)/lib/rustlib/$host/bin
cache=${ROK_LLVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok}
lld=${ROK_LLVM_PREFIX:-$cache/llvm-22.1.8}/bin/ld.lld$exe

mkdir "$tmp/x"
(cd "$tmp/x" && "$bin/llvm-ar$exe" x "$in")
first=$(ls "$tmp"/x/*.o | head -n 1)
case $(od -An -c -N4 "$first" | tr -d ' ') in
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
    # the objects. -S: no debug info either.
    cc -r -nostdlib -arch "$(lipo -archs "$first")" "$tmp"/x/*.o \
      -Wl,-exported_symbol,'_rok_*' -Wl,-S -o "$tmp/rokr.o"
    format=darwin
    ;;
esac

rm -f "$out"
"$bin/llvm-ar$exe" rcs --format=$format "$out" "$tmp/rokr.o"

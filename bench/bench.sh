#!/bin/sh
# Alloc-heavy benchmarks (not CI): builds the release runtime + rokc,
# compiles each bench/*.rok at -O2 and prints the best of 3 wall times.
# Usage: bench/bench.sh
#
# macOS arm64, 2026-10-12 (best of 3):
#                  malloc mark-sweep   block/line heap + inline TLAB
#   alloc_boxes        0.54s               0.21s
#   alloc_strings      0.39s               0.18s
#   alloc_threads      1.05s               0.16s
#
# Sticky mark-bit generations (2026-10-13, loaded shared machine, so
# min user+sys CPU of 5; ROK_GC_GEN=0 = previous collector):
#                  non-generational    generational
#   binary_trees       2.22s               1.62s
#   gc_old_heap        0.75s               0.68s
#   store_heavy        1.98s (no barrier)  2.04s (barrier fast path)
# ROK_GC_STATS=1 prints collections / pause totals at exit.
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
cargo build --release -q -p rokr -p rokc
out="$root/target/bench"
mkdir -p "$out"
for src in bench/*.rok; do
    name=$(basename "$src" .rok)
    target/release/rokc build "$src" \
        --bootstrap library/core/lib.rok --bootstrap library/std/lib.rok \
        --bootstrap library/bare/lib.rok --rokr target/release/librokr.a \
        -O2 -o "$out/$name"
    best=
    for _ in 1 2 3; do
        t=$( { /usr/bin/time -p "$out/$name" > /dev/null; } 2>&1 | awk '/^real/ {print $2}')
        if [ -z "$best" ] || [ "$(echo "$t < $best" | bc)" = 1 ]; then best=$t; fi
    done
    echo "$name: ${best}s"
done

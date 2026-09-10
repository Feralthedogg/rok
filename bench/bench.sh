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
#
# GC limits removed (2026-10-13, load average 20-30: process CPU
# user+sys min of 5 / collector CPU from ROK_GC_STATS min of 3):
#                  before          +cards          +per-thread log  +lazy zero/parse, pin list
#   binary_trees   1.62s / 582ms   1.60s / 591ms   1.62s / 591ms    1.12s /  83ms
#   gc_old_heap    0.70s / 382ms   0.64s / 316ms   0.63s / 318ms    0.51s / 177ms
#   gc_big_buffer  1.74s / 752ms   1.55s / 562ms   1.56s / 585ms    0.90s /  93ms
#   wb_threads     2.26s / 407ms   2.64s / 391ms   1.47s / 409ms    1.33s / 229ms
#   alloc_boxes    0.27s / 122ms   0.26s / 124ms   0.25s / 127ms    0.13s /   2ms
#   alloc_threads  0.44s / 199ms   0.45s / 192ms   0.44s / 195ms    0.25s /   6ms
#   store_heavy    1.5-2.0s in every column (noise; barrier fast path unchanged)
#
# Timer heap cancel cleanup (2026-10-13, `timers`: 20k 1 ms sleeps, then
# 20k cancelled 1 h sleeps; its own line has the per-phase times):
#                  O(heap) per cancel  lazy sweep (amortized O(1))
#   20k sleeps         ~100 ms             ~100 ms
#   20k cancels        30-50 s             ~130 ms
#
# Precise scanning + opportunistic evacuation (2026-10-13, quiet machine:
# process CPU min of 5 / collector CPU min of 5 / peak RSS / resident
# blocks at exit; "before" = the collector above):
#                  before                  ROK_GC_EVAC=off         default (evacuates)
#   gc_fragment    0.33s / 124ms / 269 MiB  0.30s / 102ms / 269 / 193 MiB  0.26s / 95ms / 237 / 116 MiB
#   binary_trees   0.86s /  62ms           0.86s /  65ms           0.86s /  65ms
#   gc_old_heap    0.38s / 134ms           0.36s / 122ms           0.37s / 124ms
#   gc_big_buffer  0.84s /  88ms           0.82s /  82ms           0.81s /  83ms
#   alloc_strings  0.10s /  32ms           0.10s /  32ms           0.10s /  31ms
#   wb_threads     0.85s / 147ms           0.85s / 153ms           0.84s / 152ms
# ROK_GC_STATS=1 prints collections / pause totals / collector CPU, then
# blocks / resident KiB / evacuations / bytes moved at exit.
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

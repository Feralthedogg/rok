#!/bin/sh
# Alloc- and GC-heavy benchmarks (not CI): builds the release runtime and
# rokc, compiles each bench/*.rok at -O2 and prints the best of 3 wall
# times. ROK_GC_STATS=1 makes each program print collections, pause
# totals and collector CPU, then blocks / resident KiB / evacuations /
# bytes moved at exit.
# Usage: bench/bench.sh
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
cargo build --release -q -p rokr -p rokc
out="$root/target/bench"
mkdir -p "$out"
for src in bench/*.rok; do
    name=$(basename "$src" .rok)
    target/release/rokc -q build "$src" -O2 -o "$out/$name"
    best=
    for _ in 1 2 3; do
        t=$( { /usr/bin/time -p "$out/$name" > /dev/null; } 2>&1 | awk '/^real/ {print $2}')
        if [ -z "$best" ] || [ "$(echo "$t < $best" | bc)" = 1 ]; then best=$t; fi
    done
    echo "$name: ${best}s"
done

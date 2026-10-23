#!/bin/sh
# Build the static musl release archive: dist.sh in Alpine
# (dist-musl.Containerfile), so rok, rokc, rokls and librokr.a link
# against musl and run anywhere, Alpine and old glibc included. A static
# rokc ships no libclang (`rokc bindgen` is unavailable) and no MLIR dev
# bundle; dist.sh handles that when the host is musl.
#
#   ./dist-musl.sh [--out <dir>]
#
# For the host's architecture (x86_64 or aarch64), with podman, else
# docker. The checkout is mounted read-only; rustup, cargo, LLVM and the
# target directory live in ROK_DIST_CACHE (default ~/.cache/rok/dist-musl),
# the archives land in <dir> (default dist). Then the installed toolchain
# builds and runs a program in a bare Alpine.
set -eu

cd "$(dirname "$0")"
out=dist
case "${1-}" in
  --out) out=$2 ;;
  "") ;;
  *)
    echo "usage: ./dist-musl.sh [--out <dir>]" >&2
    exit 2
    ;;
esac
# The commit for --version, taken here: the container may not see the
# repository (a worktree's .git points outside the mount).
if [ -z "${ROK_COMMIT_HASH-}" ] || [ -z "${ROK_COMMIT_DATE-}" ]; then
  if h=$(git rev-parse --short=9 HEAD 2> /dev/null) &&
    d=$(git log -1 --format=%cs 2> /dev/null); then
    ROK_COMMIT_HASH=${ROK_COMMIT_HASH:-$h}
    ROK_COMMIT_DATE=${ROK_COMMIT_DATE:-$d}
  else
    echo "dist-musl.sh: no commit for --version: run from a git checkout, or set" \
      "ROK_COMMIT_HASH and ROK_COMMIT_DATE (\`git rev-parse --short=9 HEAD\` and" \
      "\`git log -1 --format=%cs\` in the checkout this was made from)" >&2
    exit 1
  fi
fi
export ROK_COMMIT_HASH ROK_COMMIT_DATE

engine=$(command -v podman || command -v docker) || {
  echo "dist-musl.sh: needs podman or docker" >&2
  exit 1
}
cache=${ROK_DIST_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/rok/dist-musl}
mkdir -p "$out" "$cache"
out=$(cd "$out" && pwd)

# The image is named after its definition.
tag=rok-dist-musl:$(sha256sum dist-musl.Containerfile | cut -c1-12)
$engine image inspect "$tag" > /dev/null 2>&1 ||
  $engine build -t "$tag" - < dist-musl.Containerfile

# Rootless podman maps the container's root to the caller; docker's is
# root, so it runs as the caller.
user=""
case $engine in */docker) user="--user $(id -u):$(id -g)" ;; esac
# shellcheck disable=SC2086
$engine run --rm $user \
  -v "$PWD:/src:ro" -v "$cache:/cache" -v "$out:/out" -w /src \
  -e HOME=/cache/home -e RUSTUP_HOME=/cache/rustup -e CARGO_HOME=/cache/cargo \
  -e ROK_LLVM_CACHE=/cache/rok -e CARGO_TARGET_DIR=/cache/target -e TMPDIR=/cache/tmp \
  -e ROK_LLVM_JOBS="${ROK_LLVM_JOBS-}" \
  -e ROK_COMMIT_HASH="$ROK_COMMIT_HASH" -e ROK_COMMIT_DATE="$ROK_COMMIT_DATE" \
  "$tag" sh -euc '
    mkdir -p "$HOME" "$TMPDIR"
    [ -x "$CARGO_HOME/bin/rustup" ] ||
      rustup-init -y -q --no-modify-path --profile minimal --default-toolchain none
    PATH=$CARGO_HOME/bin:$PATH
    rustup toolchain install
    [ -n "$ROK_LLVM_JOBS" ] || unset ROK_LLVM_JOBS
    ./dist.sh --out /out'

# The installed static archive builds and runs a program in a bare
# Alpine, with nothing else there.
name=rok-$(cat "$out/rok-version")-$(uname -m)-unknown-linux-musl
# shellcheck disable=SC2086
$engine run --rm $user -v "$out:/out:ro" -e HOME=/tmp \
  docker.io/library/alpine:3.21@sha256:ee16d92f96db08d9d2d07da48555a27f3a69d8f0759021dbc601195ed0d2b5bd \
  sh -euc '
    cd /tmp
    tar -xzf "/out/$1.tar.gz"
    "$1/install.sh" >/dev/null
    printf "fn main() {\n    println(\"ok\");\n}\n" >check.rok
    for o in -O0 -O2; do
      ~/.rok/bin/rokc -q build check.rok $o -o check
      [ "$(./check)" = ok ]
    done
    echo "$1: runs on Alpine $(cat /etc/alpine-release)"' sh "$name"

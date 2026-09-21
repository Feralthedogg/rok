#!/bin/sh
# Install a rok toolchain into $ROK_HOME (default ~/.rok, spec 9.2.19):
# $ROK_HOME/toolchains/<version>-<triple>/, made the default, with the
# proxies $ROK_HOME/bin/{rok,rokc,rokls}.
#
#   curl -fsSL https://rok-lang.org/install.sh | sh
#   sh install.sh --archive rok-<version>-<triple>.tar.gz
#   rok-<version>-<triple>/install.sh          (from an unpacked archive)
#
# Environment: ROK_HOME, ROK_VERSION (default below), ROK_DIST (where
# releases are downloaded from).
set -eu

version="${ROK_VERSION:-0.1.0}"
dist="${ROK_DIST:-https://github.com/rok-lang/rok/releases/download}"
home="${ROK_HOME:-$HOME/.rok}"
archive=""

say() { printf '%s\n' "$*"; }
die() { printf 'install.sh: error: %s\n' "$*" >&2; exit 1; }
usage() {
  say "usage: install.sh [--archive <rok-*.tar.gz>] [--version <version>]"
  say "installs into \$ROK_HOME (now $home)"
}

while [ $# -gt 0 ]; do
  case $1 in
    --archive) [ $# -ge 2 ] || { usage >&2; exit 2; }; archive=$2; shift 2 ;;
    --version) [ $# -ge 2 ] || { usage >&2; exit 2; }; version=$2; shift 2 ;;
    -h | --help) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done

host_triple() {
  arch=$(uname -m)
  case $arch in
    arm64 | aarch64) arch=aarch64 ;;
    x86_64 | amd64) arch=x86_64 ;;
    *) die "no rok toolchain for the $arch architecture" ;;
  esac
  case $(uname -s) in
    Darwin) say "$arch-apple-darwin" ;;
    Linux)
      # A musl system has its loader, /lib/ld-musl-<arch>.so.1.
      if ls /lib/ld-musl-* >/dev/null 2>&1; then
        say "$arch-unknown-linux-musl"
      else
        say "$arch-unknown-linux-gnu"
      fi
      ;;
    MINGW* | MSYS* | CYGWIN*) die "on Windows use install.ps1 (PowerShell)" ;;
    *) die "no rok toolchain for $(uname -s)" ;;
  esac
}

# Check archive $1 against the SHA-256 in $2 (a release's .sha256).
check_sum() {
  want=$(awk '{ print tolower($1); exit }' "$2")
  if command -v sha256sum >/dev/null 2>&1; then
    got=$(sha256sum "$1" | awk '{ print $1 }')
  elif command -v shasum >/dev/null 2>&1; then
    got=$(shasum -a 256 "$1" | awk '{ print $1 }')
  else
    die "sha256sum or shasum is needed to check $1"
  fi
  [ "$got" = "$want" ] || die "$1 has SHA-256 $got, but its .sha256 says $want (a damaged or altered download)"
}

tmp=$(mktemp -d "${TMPDIR:-/tmp}/rok-install.XXXXXX")
trap 'rm -rf "$tmp"' EXIT INT TERM

# An unpacked toolchain around this script installs itself.
here=$(cd "$(dirname "$0")" 2>/dev/null && pwd) || here=""
if [ -z "$archive" ] && [ -n "$here" ] && [ -x "$here/bin/rok" ] && [ -x "$here/bin/rokc" ]; then
  src=$here
else
  if [ -z "$archive" ]; then
    triple=$(host_triple)
    url="$dist/v$version/rok-$version-$triple.tar.gz"
    say "downloading $url"
    archive="$tmp/rok.tar.gz"
    curl -fsSL --proto '=https' -o "$archive" "$url" || die "cannot download $url"
    curl -fsSL --proto '=https' -o "$archive.sha256" "$url.sha256" || die "cannot download $url.sha256"
  fi
  [ -f "$archive" ] || die "$archive does not exist"
  # A download is checked against its release's .sha256, an archive
  # file against the one beside it, if any.
  if [ -f "$archive.sha256" ]; then check_sum "$archive" "$archive.sha256"; fi
  mkdir "$tmp/files"
  tar -xzf "$archive" -C "$tmp/files" || die "cannot unpack $archive"
  src=$(find "$tmp/files" -mindepth 2 -maxdepth 2 -name bin -type d | head -n 1)
  [ -n "$src" ] || die "$archive is not a rok toolchain (no bin/)"
  src=$(dirname "$src")
fi

full=$("$src/bin/rokc" --version | awk 'NR == 1 { print $2 }') || die "cannot run $src/bin/rokc"
# The toolchain's own rok installs it (and checks it).
ROK_HOME=$home "$src/bin/rok" -q toolchain install "$full" --from "$src"
ROK_HOME=$home "$src/bin/rok" -q toolchain default "$full"
"$home/bin/rok" --version >/dev/null || die "the installed proxy $home/bin/rok does not run"

say ""
say "rok $full is installed in $home"
case ":${PATH-}:" in
  *":$home/bin:"*) ;;
  *)
    say ""
    say "Add $home/bin to PATH:"
    say "  bash / zsh:  echo 'export PATH=\"$home/bin:\$PATH\"' >> ~/.zshrc   (or ~/.bashrc)"
    say "  fish:        fish_add_path $home/bin"
    ;;
esac

# rokc links its own LLVM and linker; on macOS the link needs the SDK of
# Xcode's command line tools.
if [ "$(uname -s)" = Darwin ] && ! xcrun --show-sdk-path >/dev/null 2>&1; then
  say ""
  say "rok needs the macOS SDK to link programs: xcode-select --install"
fi
# On Linux it links against the system C library's and GCC's runtime
# files (crt1.o, crtbeginS.o, libgcc).
if [ "$(uname -s)" = Linux ]; then
  found=""
  for f in /usr/lib/gcc/*/*/crtbeginS.o /usr/lib64/gcc/*/*/crtbeginS.o; do
    if [ -f "$f" ]; then found=1; fi
  done
  if [ -z "$found" ]; then
    say ""
    say "rok needs the C library and GCC runtime files to link programs:"
    say "  Debian / Ubuntu: apt install gcc   Fedora: dnf install gcc   Alpine: apk add gcc musl-dev"
  fi
fi

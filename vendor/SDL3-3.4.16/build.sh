#!/bin/sh
# build.sh: build SDL3 3.4.16 as a static library, and keep only what a program links.
#
#   vendor/SDL3-3.4.16/build.sh OUT    install the headers, libSDL3.a and sdl3.pc under OUT
#
# The tarball is fetched and verified first (fetch.sh: its SHA-256 and both signatures). It is
# extracted and built in a temporary folder outside the checkout, removed afterward, so the source
# (with its own AGENTS.md and CLAUDE.md) never stands in the tree. The logs of configure, build
# and install are kept in OUT/logs. Needs CMake (the owner's yes of 2026-10-09: Homebrew's).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=${1:?usage: build.sh OUT}
mkdir -p "$out/logs"
out=$(cd "$out" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/sdl3-build.XXXXXX")
trap 'rm -rf "$work"' EXIT
tarball=$("$here/fetch.sh" "$work")
tar -xzf "$tarball" -C "$work"
cmake -S "$work/SDL3-3.4.16" -B "$work/build" -DCMAKE_BUILD_TYPE=Release \
  -DSDL_SHARED=OFF -DSDL_STATIC=ON -DSDL_TEST_LIBRARY=OFF -DSDL_TESTS=OFF -DSDL_EXAMPLES=OFF \
  -DCMAKE_INSTALL_PREFIX="$out" > "$out/logs/configure.log" 2>&1
cmake --build "$work/build" -j 4 > "$out/logs/build.log" 2>&1
cmake --install "$work/build" > "$out/logs/install.log" 2>&1
echo "$out"

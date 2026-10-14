#!/bin/sh
# fetch.sh: download ThorVG 1.1.2's source, and verify it before anything reads it.
#
#   vendor/thorvg-1.1.2/fetch.sh DIR    leave the verified tarball at DIR/thorvg-1.1.2.tar.xz
#
# One check: the SHA-256 in SHA256SUMS. ThorVG signs no release; the sum was taken from the
# download of 2026-10-14 and matched GitHub's published asset digest. On a failure the tarball is
# removed and the script answers 1.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=${1:?usage: fetch.sh DIR}
mkdir -p "$out"
tarball="$out/thorvg-1.1.2.tar.xz"
curl -sSfL -o "$tarball" https://github.com/thorvg/thorvg/releases/download/v1.1.2/thorvg-1.1.2.tar.xz
want=$(cut -d' ' -f1 "$here/SHA256SUMS")
got=$(shasum -a 256 "$tarball" | cut -d' ' -f1)
[ "$want" = "$got" ] || { echo "fetch.sh: SHA-256 differs: $got" >&2; rm -f "$tarball"; exit 1; }
echo "$tarball"

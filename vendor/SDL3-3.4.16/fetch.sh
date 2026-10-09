#!/bin/sh
# fetch.sh: download SDL3 3.4.16's source, and verify it before anything reads it.
#
#   vendor/SDL3-3.4.16/fetch.sh DIR    leave the verified tarball at DIR/SDL3-3.4.16.tar.gz
#
# Two checks, both required: the SHA-256 in SHA256SUMS, and both release signatures against the
# two keys in keys/ (Sam Lantinga's DSA and RSA keys, by full fingerprint), in a keyring made for
# this run alone. On any failure the tarball is removed and the script answers 1.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=${1:?usage: fetch.sh DIR}
mkdir -p "$out"
base=https://github.com/libsdl-org/SDL/releases/download/release-3.4.16
tarball="$out/SDL3-3.4.16.tar.gz"
curl -sSfL -o "$tarball" "$base/SDL3-3.4.16.tar.gz"
curl -sSfL -o "$tarball.sig" "$base/SDL3-3.4.16.tar.gz.sig"
fail() { echo "fetch.sh: $1" >&2; rm -f "$tarball" "$tarball.sig"; exit 1; }
want=$(cut -d' ' -f1 "$here/SHA256SUMS")
got=$(shasum -a 256 "$tarball" | cut -d' ' -f1)
[ "$want" = "$got" ] || fail "SHA-256 differs: $got"
# The keyring stands in a short path: gpg's agent socket refuses a long one.
ring=$(mktemp -d /tmp/sdl3k.XXXXXX)
chmod 700 "$ring"
gpg --homedir "$ring" --quiet --import "$here"/keys/*.asc 2>/dev/null || { rm -rf "$ring"; fail "the keys do not import"; }
good=$(gpg --homedir "$ring" --status-fd 1 --verify "$tarball.sig" "$tarball" 2>/dev/null | grep -c '^\[GNUPG:\] VALIDSIG' || true)
rm -rf "$ring"
[ "$good" = 2 ] || fail "expected two valid signatures, found $good"
rm -f "$tarball.sig"
echo "$tarball"

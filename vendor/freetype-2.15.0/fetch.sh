#!/bin/sh
# fetch.sh: download FreeType 2.15.0's source, and verify it before anything reads it.
#
#   vendor/freetype-2.15.0/fetch.sh DIR    leave the verified tarball at DIR/freetype-2.15.0.tar.xz
#
# Two checks, both required: the SHA-256 in SHA256SUMS, and the release signature against the key
# in keys/ (Werner Lemberg's RSA key, by full fingerprint), in a keyring made for this run alone.
# On any failure the tarball is removed and the script answers 1.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=${1:?usage: fetch.sh DIR}
mkdir -p "$out"
base=https://download.savannah.gnu.org/releases/freetype
tarball="$out/freetype-2.15.0.tar.xz"
curl -sSfL -o "$tarball" "$base/freetype-2.15.0.tar.xz"
curl -sSfL -o "$tarball.sig" "$base/freetype-2.15.0.tar.xz.sig"
fail() { echo "fetch.sh: $1" >&2; rm -f "$tarball" "$tarball.sig"; exit 1; }
want=$(cut -d' ' -f1 "$here/SHA256SUMS")
got=$(shasum -a 256 "$tarball" | cut -d' ' -f1)
[ "$want" = "$got" ] || fail "SHA-256 differs: $got"
# The keyring stands in a short path: gpg's agent socket refuses a long one.
ring=$(mktemp -d /tmp/ftk.XXXXXX)
chmod 700 "$ring"
gpg --homedir "$ring" --quiet --import "$here"/keys/*.asc 2>"$ring/import.log" || { rm -rf "$ring"; fail "the key does not import"; }
good=$(gpg --homedir "$ring" --status-fd 1 --verify "$tarball.sig" "$tarball" 2>"$ring/verify.log" | grep -c '^\[GNUPG:\] VALIDSIG E30674707856409FF1948010BE6C3AAC63AD8E3F' || true)
rm -rf "$ring"
[ "$good" = 1 ] || fail "expected one valid signature by E30674707856409FF1948010BE6C3AAC63AD8E3F, found $good"
rm -f "$tarball.sig"
echo "$tarball"

#!/bin/sh
# fetch.sh: download ECMA-262's source at the tag es2026 (the 2026 edition), and verify it.
#
#   vendor/ecma262-es2026/fetch.sh DIR    leave the verified spec.html and LICENSE.md in DIR
#
# The source is tc39/ecma262 on GitHub, tag es2026 (tag object f7db29f16c5175a93f0d6e8fb27a8e3cb9b97a9e).
# spec.html's git blob is e8bfc6c7526c22b5200613edf39f0efa56040f15, as the tag's tree records it.
# Each file must match its SHA-256 in SHA256SUMS; on any failure both files are removed.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=${1:?usage: fetch.sh DIR}
mkdir -p "$out"
base=https://raw.githubusercontent.com/tc39/ecma262/es2026
for f in spec.html LICENSE.md; do curl -sSfL -o "$out/$f" "$base/$f"; done
if ! (cd "$out" && shasum -a 256 -c "$here/SHA256SUMS" > /dev/null); then
  rm -f "$out/spec.html" "$out/LICENSE.md"
  echo "fetch.sh: a SHA-256 differs" >&2
  exit 1
fi
echo "$out"

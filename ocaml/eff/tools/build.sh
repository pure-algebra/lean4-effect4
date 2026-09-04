#!/usr/bin/env bash
# Build the effect4_eff library alone, in its own build root (ocaml/eff/_build),
# so it never contends with the ocaml/ workspace build another lane drives.
set -uo pipefail
eval "$(opam env --switch=effect4 --set-switch)"
cd /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml/eff || exit 1
dune build --root . 2>&1
echo "=== build exit: $? ==="

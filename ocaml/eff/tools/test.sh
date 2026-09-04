#!/usr/bin/env bash
# Build and run the eff test battery in its own build root.
set -uo pipefail
eval "$(opam env --switch=effect4 --set-switch)"
cd /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml/eff || exit 1
dune build --root . 2>&1
b=$?
echo "=== build exit: $b ==="
[ $b -ne 0 ] && exit $b
dune test --root . --force 2>&1
echo "=== test exit: $? ==="

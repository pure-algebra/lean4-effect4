#!/usr/bin/env bash
# Print the signature ocamlc infers for eff_typed.ml, against the library's compiled
# interfaces. Used to check eff_typed.mli against what the implementation actually exports.
set -uo pipefail
eval "$(opam env --switch=effect4 --set-switch)"
cd /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml/eff || exit 1
dune build --root . 2>&1 || exit 1
ocamlc -i -w -a -I _build/default/.effect4_eff.objs/byte eff_typed.ml
echo "=== infer exit: $? ==="

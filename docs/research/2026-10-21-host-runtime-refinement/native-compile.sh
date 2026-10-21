#!/bin/sh
# Compile and link the measured closure. No application driver runs here.
set -eu
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
STAGE=${TMPDIR:-/tmp}/effect4-host-runtime-closure/engine
cd "$ROOT"
opam exec --switch=effect4 -- dune build --root ocaml -j 3 \
  eff/effect4_eff.cmxa lcnf/effect4_lcnf.cmxa
for unit in engine_gen todo_host_gen todo_model_gen; do
  opam exec --switch=effect4 -- ocamlfind ocamlopt \
    -w @55 -package zarith \
    -I "$ROOT/ocaml/_build/default/eff/.effect4_eff.objs/byte" \
    -I "$ROOT/ocaml/_build/default/lcnf/.effect4_lcnf.objs/byte" \
    -I "$STAGE" -c "$STAGE/$unit.ml"
  echo "compiled: $unit"
done
opam exec --switch=effect4 -- ocamlfind ocamlopt \
  -package zarith -linkpkg \
  -I "$ROOT/ocaml/_build/default/eff/.effect4_eff.objs/byte" \
  -I "$ROOT/ocaml/_build/default/lcnf/.effect4_lcnf.objs/byte" \
  -I "$STAGE" \
  "$ROOT/ocaml/_build/default/lcnf/effect4_lcnf.cmxa" \
  "$ROOT/ocaml/_build/default/eff/effect4_eff.cmxa" \
  "$STAGE/engine_gen.cmx" "$STAGE/todo_host_gen.cmx" "$STAGE/todo_model_gen.cmx" \
  -o "$STAGE/closure_link.exe"
"$STAGE/closure_link.exe"
echo "linked and initialized: no application driver"

#!/usr/bin/env bash
# Seat F1: the dune build of the avatar in the `effect4` switch, out of tree.
#
#   build-dune.sh            # build the library and both executables in all three modes
#   build-dune.sh witnesses  # ...and run the witness report on the three dune-built hosts
#
# The build directory is out of tree (`DUNE_BUILD` names it), never inside the repository.
# For the in-tree build the rest of the estate uses, `cd ocaml && dune build avatar`.
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build=${DUNE_BUILD:-${TMPDIR:-/tmp}/effect4-dune-avatar}
eval "$(opam env --switch=effect4 --set-switch)"
echo "ocaml $(ocamlfind ocamlc -version 2>/dev/null || ocamlc -version), dune $(dune --version), js_of_ocaml $(js_of_ocaml --version)"
dune build --root "$here" --build-dir "$build" ./avatar_main.exe ./avatar_main.bc ./avatar_main.bc.js \
  ./avatar_witnesses.exe ./avatar_witnesses.bc ./avatar_witnesses.bc.js 2>&1 | grep -v "^ *$" || true
d="$build/default"
for f in avatar_main.exe avatar_main.bc avatar_main.bc.js avatar_witnesses.exe avatar_witnesses.bc avatar_witnesses.bc.js; do
  [ -f "$d/$f" ] || { echo "MISSING $d/$f"; exit 1; }
done
echo "dune: library + 2 executables x 3 modes built"
if [ "${1:-}" = "witnesses" ]; then
  ocamlrun "$d/avatar_witnesses.bc" > "$build/byte.tsv"
  "$d/avatar_witnesses.exe" > "$build/native.tsv"
  node "$d/avatar_witnesses.bc.js" > "$build/jsoo.tsv"
  if cmp -s "$build/byte.tsv" "$build/native.tsv" && cmp -s "$build/byte.tsv" "$build/jsoo.tsv"; then
    echo "dune hosts witnesses AGREE (bytecode = native = js_of_ocaml 5.7.1 from the switch)"
  else
    echo "dune hosts witnesses DISAGREE"; exit 1
  fi
  if cmp -s "$build/byte.tsv" "$here/out/witnesses.report.tsv"; then
    echo "dune report IDENTICAL to the shell build's report"
  else
    echo "dune report DIFFERS from the shell build's report"; exit 1
  fi
fi

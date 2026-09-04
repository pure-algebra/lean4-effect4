#!/usr/bin/env bash
# Seat F1: the witness and clause report on the three OCaml hosts.
#
# Builds `avatar-witnesses` (bytecode, native, js_of_ocaml --enable effects) from the avatar
# modules plus `deep_census.ml`, `deep_clauses.ml`, `deep_witnesses.ml` and the report driver
# `avatar_witnesses.ml`; runs it on each host; requires the three reports byte-identical;
# writes the report to `out/witnesses.report.tsv`; and guards the entry counts against the
# Lean files (`Clauses.lean` theorems = `Deep_clauses.count`, `Witnesses.lean` theorems =
# `Deep_witnesses.count`, `deep_census.ml` identical to `RuntimeCoverage.lean`).
#
# Exit 1 on: a build failure, hosts that disagree, a count drift, a census drift, or a
# witness statement that FAILS. A clause that FAILS or is NOT PORTABLE is reported, not
# fatal: those are the report's rows (`docs/research/2026-09-04-seat-w1-deep-port.md`).
set -uo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(CDPATH= cd -- "$here/../../.." && pwd)
out=${A0_BUILD:-/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/a0}
oc=${OCAML5_BIN:-/Users/pooks/.opam/default/bin}
jsoo=${JSOO5_BIN:-/Users/pooks/Dev/effect4_of_ocaml/_build/toolchains/ocaml5-jsoo-5.7.1/_build/default/vendor/js_of_ocaml-compiler.5.7.1/compiler/bin-js_of_ocaml/js_of_ocaml.exe}
mkdir -p "$out/witnesses" "$here/out"
cp "$here"/*.ml "$out/witnesses/"
cd "$out/witnesses"
status=0

modules="deep_fibers.ml deep_stores.ml deep_layer.ml avatar_trace.ml deep_census.ml deep_clauses.ml deep_witnesses.ml avatar_witnesses.ml"
"$oc/ocamlc"   -o witnesses.byte   $modules || exit 1
"$oc/ocamlopt" -o witnesses.native $modules || exit 1
"$jsoo" compile --enable effects --target-env=nodejs witnesses.byte -o witnesses.js 2>/dev/null || exit 1

"$oc/ocamlrun" ./witnesses.byte > byte.tsv
./witnesses.native > native.tsv
node witnesses.js > jsoo.tsv
if cmp -s byte.tsv native.tsv && cmp -s byte.tsv jsoo.tsv; then
  echo "hosts witnesses AGREE (bytecode = native = js_of_ocaml)"
else
  echo "hosts witnesses DISAGREE"; status=1
fi
cp byte.tsv "$here/out/witnesses.report.tsv"

# The entry counts against the Lean files.
lean_clauses=$(grep -c '^theorem' "$repo/Effect4/Deep/Clauses.lean")
lean_witnesses=$(grep -c '^theorem' "$repo/Effect4/Deep/Witnesses.lean")
have_clauses=$(awk -F'\t' '$1=="clauses"{print $2}' byte.tsv)
have_witnesses=$(awk -F'\t' '$1=="witnesses"{print $2}' byte.tsv)
if [ "$lean_clauses" = "$have_clauses" ]; then echo "clauses: $have_clauses entries = $lean_clauses Clauses.lean theorems"
else echo "clauses: $have_clauses entries != $lean_clauses Clauses.lean theorems"; status=1; fi
if [ "$lean_witnesses" = "$have_witnesses" ]; then echo "witnesses: $have_witnesses entries = $lean_witnesses Witnesses.lean theorems"
else echo "witnesses: $have_witnesses entries != $lean_witnesses Witnesses.lean theorems"; status=1; fi
python3 "$here/extract-census.py" --check || status=1

grep -E '^clauses|^witnesses|^run-clauses' byte.tsv
if [ "$(awk -F'\t' '$1=="witnesses"{print $6}' byte.tsv)" != "0" ]; then
  echo "witness statements FAIL on the avatar:"; grep -B1 '^  statement	FAILS' byte.tsv; status=1
fi
exit $status

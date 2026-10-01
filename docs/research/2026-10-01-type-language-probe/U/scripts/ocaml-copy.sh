#!/bin/bash
# Probe U, question 4: rebuild the OCaml estate copy and rerun the two comparisons.
#   sh U/scripts/ocaml-copy.sh      (from the worktree root; dune only through the effect4 switch)
# 1. the zero control: an unmodified copy of ocaml/ builds; `dune test eff` with the coverage
#    instrument appended to prop_wire.ml reports the hand rand_ty's reach; `dune test engine`;
# 2. the emitted mirrors: of_ty and rand_ty emitted from eff_manifest.txt
#    (scripts/emit-ocaml-ty.py), the same instrument, the same tests.
# The copy lives in U/ocaml-copy (not committed: a 6.5 MB copy of tracked files plus _build).
set -eu
R=docs/research/2026-10-01-type-language-probe/U
DUNE="opam exec --switch=effect4 -- dune"
python3 $R/scripts/emit-ocaml-ty.py ocaml/eff/eff_manifest.txt ocaml/engine/e4_program.ml ocaml/eff/test/prop_wire.ml $R/ocaml/emitted > $R/logs/emit-ocaml.log
rm -rf $R/ocaml-copy && cp -R ocaml $R/ocaml-copy && rm -rf $R/ocaml-copy/_build
cat $R/ocaml/coverage-instrument.ml >> $R/ocaml-copy/eff/test/prop_wire.ml
( cd $R/ocaml-copy && $DUNE build -j 2 && $DUNE test eff -j 2 --force 2>&1 | grep -E "prop_wire|rand_ty coverage|failures" ) > $R/logs/ocaml-zero-coverage.log 2>&1
( cd $R/ocaml-copy && $DUNE test engine -j 2 --force 2>&1 | grep -E "^== |^FAIL|^PASS Fast|checks$" ) > $R/logs/ocaml-zero-engine.summary 2>&1 || true
cp $R/ocaml/emitted/e4_program.ml $R/ocaml-copy/engine/e4_program.ml
cp $R/ocaml/emitted/prop_wire.ml $R/ocaml-copy/eff/test/prop_wire.ml
cat $R/ocaml/coverage-instrument.ml >> $R/ocaml-copy/eff/test/prop_wire.ml
( cd $R/ocaml-copy && $DUNE build -j 2 && $DUNE test eff -j 2 --force 2>&1 | grep -E "prop_wire|rand_ty coverage|failures" ) > $R/logs/ocaml-emitted-eff.log 2>&1
( cd $R/ocaml-copy && $DUNE test engine -j 2 --force 2>&1 | grep -E "^== |^FAIL|^PASS Fast|checks$" ) > $R/logs/ocaml-emitted-engine.summary 2>&1 || true
norm() { sed -E 's/, [0-9.]+ s ==$/ ==/' "$1" | sort; }
if diff <(norm $R/logs/ocaml-zero-engine.summary) <(norm $R/logs/ocaml-emitted-engine.summary) > /dev/null; then
  echo "engine tests, hand of_ty vs emitted of_ty: identical summaries once sorted and the wall-clock figure dropped" > $R/logs/ocaml-engine-compare.log
else
  echo "engine tests DIFFER between the hand and the emitted of_ty" > $R/logs/ocaml-engine-compare.log
fi
cat $R/logs/ocaml-zero-coverage.log $R/logs/ocaml-emitted-eff.log $R/logs/ocaml-engine-compare.log

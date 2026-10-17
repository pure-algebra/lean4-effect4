#!/usr/bin/env bash
# reproduce.sh -- rebuild every artifact, check and number of this note from its sources.
#
# Run from the repository root:
#   bash docs/research/2026-10-16-itrees/reproduce.sh OUTDIR [VESSEL_ARTIFACTS]
# OUTDIR receives the generated files, the builds and logs/. VESSEL_ARTIFACTS is the vessel's
# saved runs (apps/vessel/artifacts of branch codex/vessel-dogfood; the default is the checkout
# that holds them). It needs three opam switches: effect4 (the estate), rocq (Rocq 9.0.1, ITree
# 5.2.1, rocq-of-ocaml 1ac69a7) and ctree (Coq 8.20.1, coq-ctree 2.0). It edits nothing tracked.
set -euo pipefail

HERE=docs/research/2026-10-16-itrees
OUT=$(mkdir -p "${1:?usage: reproduce.sh OUTDIR [VESSEL_ARTIFACTS]}" && cd "$1" && pwd)
VESSEL=${2:-/Users/pooks/.codex/worktrees/iso-probe-verification/lean4-effect4/apps/vessel/artifacts}
ROOT=$(pwd)
BUILD=$ROOT/ocaml/_build/default
RUNS="20a54feed085-a1c48e b1eadbb02044-c3b98e dca7dc5dd65c-55a575 0c11ca2d8218-54b36b e974939c2d7c-5b805b 28b063ee1f3e-e99f3d"
mkdir -p "$OUT"/{gen,rocq,check,ctree,lane,logs}
cp "$HERE"/gen/* "$OUT/gen/"
cp "$HERE"/rocq/*.v "$OUT/rocq/"
log() { printf '$ %s\n' "$*" >> "$OUT/logs/$LOG"; }
run() { log "$@"; "$@" >> "$OUT/logs/$LOG" 2>&1; }
inrocq() { opam exec --switch=rocq -- "$@"; }
ineffect4() { opam exec --switch=effect4 -- "$@"; }
inctree() { opam exec --switch=ctree -- "$@"; }
# rocq-of-ocaml writes no Require for a sibling module; the one line it needs is added here
needs_types() { python3 -c "import sys; p=sys.argv[1]; s=open(p).read(); open(p,'w').write(s.replace('Require Import RocqOfOCaml.Settings.\n', 'Require Import RocqOfOCaml.Settings.\nRequire E4.Eff_types.\n', 1))" "$1"; }

# 1. The estate's libraries the generators load.
LOG=1-estate.log
(cd ocaml && run ineffect4 dune build eff engine/test/todo)

# 2. The program types: Lean -> LCNF -> ocaml/eff/eff_types.ml -> components -> rocq-of-ocaml.
LOG=2-types.log
cd "$OUT/gen"
run inrocq ocamlfind ocamlopt -package compiler-libs.common -linkpkg split_types.ml -o split_types
run inrocq ocamlfind ocamlopt -package compiler-libs.common -linkpkg extract_map.ml -o extract_map
cd "$OUT/rocq"
log "split_types eff_types.ml > eff_types.ml"; "$OUT/gen/split_types" "$ROOT/ocaml/eff/eff_types.ml" > eff_types.ml
log "extract_map eff_types.ml > EffExtract.v"; "$OUT/gen/extract_map" "$ROOT/ocaml/eff/eff_types.ml" > EffExtract.v
run inrocq ocamlfind ocamlc -bin-annot -c eff_types.ml
run inrocq rocq-of-ocaml -output Eff_types.v eff_types.ml

# 3. The fixtures as Rocq data: Lean's bytes -> OCaml values (toplevel) -> checked -> rocq-of-ocaml.
LOG=3-fixtures.log
cd "$ROOT"
run python3 "$HERE/gen/fixture_to_ml.py" "$OUT/rocq/todo_fixture.ml"
REPLAYS=""; for r in $RUNS; do REPLAYS="$REPLAYS $VESSEL/$r/replay.json"; done
log "shasum -a 256 (each vessel run)"; for r in $RUNS; do shasum -a 256 "$VESSEL/$r/replay.json" >> "$OUT/logs/$LOG"; done
# shellcheck disable=SC2086
run python3 "$HERE/gen/vessel_to_ml.py" "$OUT/rocq/vessel_fixture.ml" $REPLAYS
# the byte checks build in their own folder: rocq/ holds an eff_types.cmi of the rocq switch's OCaml
cp "$OUT/rocq/todo_fixture.ml" "$OUT/rocq/vessel_fixture.ml" "$OUT/check/"
cd "$OUT/check"
INC=""; for d in eff/.effect4_eff clock/.effect4_clock engine/bytes/.effect4_bytes engine/.effect4_engine engine/test/todo/.todo_lane; do
  INC="$INC -I $BUILD/$d.objs/byte -I $BUILD/$d.objs/native"; done
# shellcheck disable=SC2086
run ineffect4 ocamlfind ocamlopt -package zarith -linkpkg $INC "$BUILD/eff/effect4_eff.cmxa" todo_fixture.ml "$OUT/gen/check_fixture.ml" -o "$OUT/gen/check_fixture"
log "TODO_FIXTURE=ocaml/engine/test/todo/todo-host.txt check_fixture"
TODO_FIXTURE=$ROOT/ocaml/engine/test/todo/todo-host.txt "$OUT/gen/check_fixture" >> "$OUT/logs/$LOG" 2>&1
# shellcheck disable=SC2086
run ineffect4 ocamlfind ocamlopt -package zarith,yojson -linkpkg $INC "$BUILD/eff/effect4_eff.cmxa" vessel_fixture.ml "$OUT/gen/check_vessel.ml" -o "$OUT/gen/check_vessel"
# shellcheck disable=SC2086
run "$OUT/gen/check_vessel" $REPLAYS
cd "$OUT/rocq"
for m in todo_fixture vessel_fixture; do
  run inrocq ocamlfind ocamlc -bin-annot -c $m.ml
done
run inrocq rocq-of-ocaml -output Todo_fixture.v todo_fixture.ml
run inrocq rocq-of-ocaml -output Vessel_fixture.v vessel_fixture.ml
needs_types Todo_fixture.v; needs_types Vessel_fixture.v

# 4. The Rocq development, each file timed, then every assumption printed.
LOG=4-rocq.log
cd "$OUT/rocq"
for f in Eff_types Denote Run Todo_fixture TodoCheck Vessel_fixture VesselCheck Judgments VesselTypes Vessel EffExtract Extract; do
  log "rocq compile -Q . E4 $f.v"
  { /usr/bin/time -p opam exec --switch=rocq -- rocq compile -Q . E4 "$f.v"; } >> "$OUT/logs/$LOG" 2>&1
done
LOG=5-assumptions.log
cat > Assumptions.v <<'EOF'
Require Import E4.Judgments E4.Vessel E4.TodoCheck E4.VesselCheck.
Print Assumptions E4.Judgments.traces_iff_equivalent.
Print Assumptions E4.Judgments.exit_not_divergence.
Print Assumptions E4.Judgments.frontier_not_divergence.
Print Assumptions E4.Judgments.tape_respects_equivalence.
Print Assumptions E4.Judgments.loop_diverges.
Print Assumptions E4.Vessel.assess_sound_every_host.
Print Assumptions E4.Vessel.assess_sound_every_stateful_host.
Print Assumptions E4.Vessel.study_checks_never_fire.
Print Assumptions E4.Vessel.raw_refuses.
Print Assumptions E4.TodoCheck.reference_0.
Print Assumptions E4.TodoCheck.broken_6.
Print Assumptions E4.TodoCheck.control_frontier.
Print Assumptions E4.VesselCheck.accepted_0.
Print Assumptions E4.VesselCheck.refused_capacity_3.
Print Assumptions E4.VesselCheck.fmi_failed_5.
EOF
run inrocq rocq compile -Q . E4 Assumptions.v

# 5. The choice-tree development, in its own switch.
LOG=6-ctree.log
cp "$OUT/rocq/VesselTypes.v" "$OUT/rocq/VesselCtreeHost.v" "$OUT/rocq/VesselCtree.v" "$OUT/ctree/"
cd "$OUT/ctree"
for f in VesselTypes VesselCtreeHost VesselCtree; do run inctree coqc -Q . E4 "$f.v"; done
printf 'Require Import E4.VesselCtreeHost.\nPrint Assumptions E4.VesselCtreeHost.mock_answers_within_spec.\nPrint Assumptions E4.VesselCtreeHost.mock_meets.\n' > AuditHost.v
run inctree coqc -Q . E4 AuditHost.v
printf 'Unset Universe Checking.\nRequire Import E4.VesselCtree.\nPrint Assumptions E4.VesselCtree.mock_refines_spec.\n' > AuditCtree.v
run inctree coqc -Q . E4 AuditCtree.v
log "the control: ctrees' interpretation lemmas do not load with universe checking on"
for imp in "CTree Eq" "Interp.Fold" "Interp.FoldCTree" "Interp.FoldStateT"; do
  printf 'From CTree Require Import %s.\n' "$imp" > Control.v
  if inctree coqc Control.v > /dev/null 2>&1; then echo "loads: $imp" >> "$OUT/logs/$LOG"; else echo "refused: $imp" >> "$OUT/logs/$LOG"; fi
done

# 6. The extracted tree under the to-do lane's hosts, against Lean and timed against the engine.
LOG=7-extracted.log
cp "$OUT/rocq/itree_run.ml" "$OUT/rocq/itree_run.mli" "$OUT/gen/itree_lane.ml" "$OUT/lane/"
cd "$OUT/lane"
# shellcheck disable=SC2086
run ineffect4 ocamlfind ocamlopt -package zarith,unix,threads.posix -linkpkg -w -a $INC \
  "$BUILD/eff/effect4_eff.cmxa" "$BUILD/clock/effect4_clock.cmxa" "$BUILD/engine/bytes/effect4_bytes.cmxa" \
  "$BUILD/engine/effect4_engine.cmxa" "$BUILD/engine/test/todo/todo_lane.cmxa" itree_run.mli itree_run.ml itree_lane.ml -o itree_lane
log "uptime"; uptime >> "$OUT/logs/$LOG"
run ./itree_lane "$ROOT/ocaml/engine/test/todo/todo-host.txt"

# 7. The red control on the meaning: the option decision's branches swapped; TodoCheck must fail.
LOG=8-mutant.log
mkdir -p "$OUT/mutant"
cp "$OUT/rocq"/{Eff_types.v,Run.v,Todo_fixture.v,TodoCheck.v} "$OUT/mutant/"
sed 's/  | Decision_option, Val_none => Some (true, \[\])/  | Decision_option, Val_none => Some (false, [])/; s/  | Decision_option, Val_some a => Some (false, \[a\])/  | Decision_option, Val_some a => Some (true, [a])/' \
  "$OUT/rocq/Denote.v" > "$OUT/mutant/Denote.v"
cd "$OUT/mutant"
log "diff rocq/Denote.v mutant/Denote.v"; diff "$OUT/rocq/Denote.v" Denote.v >> "$OUT/logs/$LOG" || true
for f in Eff_types Denote Run Todo_fixture; do inrocq rocq compile -Q . E4 "$f.v" > /dev/null 2>&1; done
log "rocq compile -Q . E4 TodoCheck.v   (must fail)"
if inrocq rocq compile -Q . E4 TodoCheck.v >> "$OUT/logs/$LOG" 2>&1; then
  echo "FAIL the mutant passed TodoCheck" >> "$OUT/logs/$LOG"; exit 1
else
  echo "PASS the mutant fails TodoCheck" >> "$OUT/logs/$LOG"
fi

# 8. The budget relation (rocq/Budget.v): Lean's budgeted call tree is the budget-k truncation of
#    the meaning; with definitions by budgeted unfolding, for every program (rocq/BudgetDefs.v).
#    Then the API on it, the examples and their checks, the to-do fixture at a budget, each file
#    timed, with Rocq's own evaluator timed on two runs; every assumption printed.
LOG=9-budget.log
cd "$OUT/rocq"
for f in Budget BudgetDefs Api Examples BudgetCheck TodoBudgetCheck BudgetExtract; do
  log "rocq compile -Q . E4 $f.v"
  { /usr/bin/time -p opam exec --switch=rocq -- rocq compile -Q . E4 "$f.v"; } >> "$OUT/logs/$LOG" 2>&1
done
cat > Speed.v <<'EOF'
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import E4.Eff_types E4.Budget E4.Api E4.Examples.
Time Eval vm_compute in stop_at (run_at 100000 by_unit ping ([], tt)).
Time Eval vm_compute in length (frames 1000 by_unit ping ([], tt)).
EOF
run inrocq rocq compile -Q . E4 Speed.v
LOG=10-budget-assumptions.log
cat > BudgetAssumptions.v <<'EOF'
Require Import E4.Budget E4.BudgetDefs E4.Api E4.BudgetCheck E4.TodoBudgetCheck.
Print Assumptions E4.Budget.denoteB_approx.
Print Assumptions E4.Budget.meaning_fragment.
Print Assumptions E4.Budget.truncation_is_denoteB.
Print Assumptions E4.Budget.denoteB_below_meaning.
Print Assumptions E4.Budget.adequacy.
Print Assumptions E4.Budget.meaning_finishes_iff.
Print Assumptions E4.Budget.meaning_waits_iff.
Print Assumptions E4.Budget.meaning_diverges_under_iff.
Print Assumptions E4.Budget.meaning_diverges_iff.
Print Assumptions E4.BudgetDefs.denoteD_approx.
Print Assumptions E4.BudgetDefs.denoteD_below.
Print Assumptions E4.BudgetDefs.adequacyD.
Print Assumptions E4.BudgetDefs.finishesD_iff.
Print Assumptions E4.BudgetDefs.waitsD_iff.
Print Assumptions E4.BudgetDefs.divergesD_iff.
Print Assumptions E4.BudgetDefs.meaning_divergesD_iff.
Print Assumptions E4.BudgetDefs.denoteBD_same.
Print Assumptions E4.Api.run_at_lean.
Print Assumptions E4.Api.run_at_finished.
Print Assumptions E4.Api.run_at_waits.
Print Assumptions E4.Api.run_at_grows.
Print Assumptions E4.Api.settle_finished.
Print Assumptions E4.Api.settle_complete.
Print Assumptions E4.Api.diverges_iff_never_settles.
Print Assumptions E4.Api.edit_congruence.
Print Assumptions E4.Api.edit_keeps_outcomes.
Print Assumptions E4.BudgetCheck.doubling_finishes.
Print Assumptions E4.BudgetCheck.doubling_waits.
Print Assumptions E4.BudgetCheck.forever_cut_everywhere.
Print Assumptions E4.BudgetCheck.edit_outcomes.
Print Assumptions E4.BudgetCheck.doubling_rec_finishes.
Print Assumptions E4.BudgetCheck.self_call_diverges.
Print Assumptions E4.TodoBudgetCheck.reference_0.
Print Assumptions E4.TodoBudgetCheck.broken_6.
EOF
run inrocq rocq compile -Q . E4 BudgetAssumptions.v

# 9. The view: the extracted runner writes the frames of each example; the page plays them.
LOG=11-view.log
mkdir -p "$OUT/view"
cp "$OUT/rocq/budget_run.ml" "$OUT/rocq/budget_run.mli" "$OUT/gen/budget_view.ml" "$OUT/view/"
cd "$OUT/view"
# shellcheck disable=SC2086
run ineffect4 ocamlfind ocamlopt -package zarith -linkpkg -w -a $INC "$BUILD/eff/effect4_eff.cmxa" \
  budget_run.mli budget_run.ml budget_view.ml -o budget_view
log "uptime"; uptime >> "$OUT/logs/$LOG"
run ./budget_view frames.json
log "budget_view.html with frames.json in place of its marker > budget-view.html"
python3 -c "import sys; t=open(sys.argv[1]).read(); j=open(sys.argv[2]).read(); assert '/*FRAMES_JSON*/' in t; open(sys.argv[3],'w').write(t.replace('/*FRAMES_JSON*/', j, 1))" \
  "$OUT/gen/budget_view.html" frames.json budget-view.html

# 10. The red control on the budget: Lean's tree given one more test per loop, the truncation
#     unchanged. Budget.v must fail, at truncation_is_denoteB.
LOG=12-budget-mutant.log
mkdir -p "$OUT/budget-mutant"
cp "$OUT/rocq"/{Eff_types.v,Denote.v,Run.v,Judgments.v} "$OUT/budget-mutant/"
sed '/(iterB (loop_stepB/ s/ k c0)$/ (S k) c0)/' "$OUT/rocq/Budget.v" > "$OUT/budget-mutant/Budget.v"
cd "$OUT/budget-mutant"
log "diff rocq/Budget.v budget-mutant/Budget.v"; diff "$OUT/rocq/Budget.v" Budget.v >> "$OUT/logs/$LOG" || true
for f in Eff_types Denote Run Judgments; do inrocq rocq compile -Q . E4 "$f.v" > /dev/null 2>&1; done
log "rocq compile -Q . E4 Budget.v   (must fail)"
if inrocq rocq compile -Q . E4 Budget.v >> "$OUT/logs/$LOG" 2>&1; then
  echo "FAIL the mutant passed Budget.v" >> "$OUT/logs/$LOG"; exit 1
else
  echo "PASS the mutant fails Budget.v" >> "$OUT/logs/$LOG"
fi

# 11. The red control on the definitions: a call's body run at the caller's environment instead
#     of its request alone. BudgetDefs.v must fail, at denoteW_below.
LOG=13-defs-mutant.log
mkdir -p "$OUT/defs-mutant"
cp "$OUT/rocq"/{Eff_types.v,Denote.v,Run.v,Judgments.v,Budget.v} "$OUT/defs-mutant/"
sed 's/| Some body => call body \[v\] ((\[\], \[\]) :: ps) ctx/| Some body => call body env (([], []) :: ps) ctx/' \
  "$OUT/rocq/BudgetDefs.v" > "$OUT/defs-mutant/BudgetDefs.v"
cd "$OUT/defs-mutant"
log "diff rocq/BudgetDefs.v defs-mutant/BudgetDefs.v"; diff "$OUT/rocq/BudgetDefs.v" BudgetDefs.v >> "$OUT/logs/$LOG" || true
for f in Eff_types Denote Run Judgments Budget; do inrocq rocq compile -Q . E4 "$f.v" > /dev/null 2>&1; done
log "rocq compile -Q . E4 BudgetDefs.v   (must fail)"
if inrocq rocq compile -Q . E4 BudgetDefs.v >> "$OUT/logs/$LOG" 2>&1; then
  echo "FAIL the mutant passed BudgetDefs.v" >> "$OUT/logs/$LOG"; exit 1
else
  echo "PASS the mutant fails BudgetDefs.v" >> "$OUT/logs/$LOG"
fi

echo "reproduce.sh: done; logs in $OUT/logs"

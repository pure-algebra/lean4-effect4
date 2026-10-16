#!/bin/bash
# The host closure's compile probe (S3's receipt; the types audit, §6.7): lower the to-do host
# run's closure through LCNF, then type it with ocamlopt against the built eff and clock
# libraries (`dune build` first). Usage: host-compile.sh OUT_DIR. Run the Lean step in the slot.
set -euo pipefail
R=/Users/pooks/Dev/lean4-effect4
OUT=$1
mkdir -p "$OUT"
cd "$R"
"$R/scratch/lean-slot.sh" lake env lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean \
  --out "$OUT/todo_host.ml" --import Test.Dogfood.Scenario.Todo.Host --cap 4000 --open Eff_types \
  --open-types Effect4.ServiceName,Effect4.ServiceTypeCode,Effect4.ServiceKey,Effect4.Program.Ty,Effect4.Program.Lit,Effect4.Program.FieldReadMode,Effect4.Program.Term,Effect4.Program.Terms,Effect4.Program.CauseTerm,Effect4.Supervision.MaskMode,Effect4.Supervision.ForkOptions,Effect4.Supervision.ObserverMode,Effect4.FinalizerStrategy,Effect4.Program.NativeOp,Effect4.Program.Decision,Effect4.Program.DefRole,Effect4.Program.ParamDecl,Effect4.Program.DefDecl,Effect4.Program.Eff,Effect4.Program.Stmt,Effect4.Program.Stmts,Effect4.Program.Effs,Effect4.Program.ActionTerm,Effect4.Program.LayerTerm,Effect4.Program.LayerTerms,Effect4.Program.RowKind,Effect4.Program.RowShape,Effect4.Program.Registration,Effect4.Program.RowArg,Effect4.Program.Row,Effect4.Program.EffTy,Effect4.Store.Val,Effect4.Machine.Err,Effect4.Machine.Defect,Effect4.Reason,Effect4.Exit,Effect4.Machine.Completion \
  Test.Dogfood.Scenario.Todo.Host.serveBuilt Test.Dogfood.Scenario.Todo.Host.serveBuiltForgetful
cd "$R/ocaml"
opam exec --switch=effect4 -- ocamlfind ocamlopt -package zarith \
  -I _build/default/eff/.effect4_eff.objs/byte -I _build/default/clock/.effect4_clock.objs/byte \
  -c -o "$OUT/todo_host.cmx" "$OUT/todo_host.ml"
echo "PASS host-compile: ocamlopt types $(wc -l < "$OUT/todo_host.ml") lines"

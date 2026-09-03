import Lean
import Lean.Util.CollectAxioms
import Effect4.Target.TypeScript.Lower

/-!
# Lowering coverage numerator

The frozen evidence rows of the lowering ledger (`docs/LOWERING-COVERAGE.md`).
One row per `Rule`: the goldens that exercise it, whether a host receipt and a
property batch are claimed, the type receipt, and the Lean-side proof, if any.
At elaboration time this module checks that every rule has exactly one row,
that every `proof` names a theorem within the axiom ceiling, and that the
declared state is the state the evidence derives; then it prints one
`E4LOWCOV` row per rule for `scripts/generate-lowering-coverage.sh`, which
joins the claims against the files on disk.

This module inspects the environment (`MetaM`), so it is an audit
implementation module in the axiom gate. It supplies no semantic declaration.
-/

open Lean Elab Command

namespace Effect4Test.Target.TypeScript.LoweringCoverage

open Effect4.Target.EffectV4

inductive State where
  | absent | pinned | checked | covered | provedLeanSide
deriving DecidableEq, Repr

def State.name : State → String
  | .absent => "absent" | .pinned => "pinned" | .checked => "checked"
  | .covered => "covered" | .provedLeanSide => "proved-lean-side"

structure Row where
  rule : Rule
  state : State
  goldens : List String
  host : Bool
  property : Bool
  typeReceipt : Bool
  proof : Option Name

/-- The derived state: what the claimed evidence supports. -/
def derive (row : Row) : State :=
  if row.proof.isSome then .provedLeanSide
  else if row.goldens.isEmpty then .absent
  else if !row.host then .pinned
  else if !row.property then .checked
  else .covered

/-- The frozen rows. Goldens are names under `generated/traces/`. -/
def rows : List Row :=
  [ { rule := .serviceAcquire, state := .checked, goldens := ["incr.empty", "twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .nullaryValue, state := .checked, goldens := ["incr.empty", "twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .performCall, state := .checked, goldens := ["incr.empty", "twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .performBind, state := .checked, goldens := ["incr.empty", "twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .performDiscard, state := .checked, goldens := ["incr.empty", "twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .atomCall, state := .checked, goldens := ["incr.empty", "twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .ret, state := .checked, goldens := ["incr.empty", "twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .errorAbort, state := .checked, goldens := ["fallible.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  -- the dispatch form (FlowLower.lean); goldens are the Flow-runner face under generated/traces/flow/
  , { rule := .dispatchLoop, state := .checked,
      goldens := ["flow/incr.empty", "flow/twice.empty", "flow/chooser.left", "flow/swap.once"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .blockCase, state := .checked,
      goldens := ["flow/incr.empty", "flow/twice.empty", "flow/chooser.left", "flow/swap.once"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .paramMove, state := .checked,
      goldens := ["flow/incr.empty", "flow/twice.empty", "flow/chooser.left", "flow/swap.once", "flow/swap.twice"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .flowPerform, state := .checked, goldens := ["flow/incr.empty", "flow/twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .flowAtom, state := .checked, goldens := ["flow/incr.empty", "flow/twice.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .flowLiteral, state := .checked, goldens := ["flow/incr.empty", "flow/twice.empty", "flow/swap.once"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .chooseIf, state := .checked,
      goldens := ["flow/chooser.left", "flow/chooser.right", "flow/swap.once", "flow/swap.twice"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .flowRet, state := .checked,
      goldens := ["flow/incr.empty", "flow/twice.empty", "flow/chooser.left", "flow/swap.once"],
      host := true, property := false, typeReceipt := true, proof := none } ]

private def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#lowering_coverage" : command => do
  -- one row per rule, both directions
  for rule in Rule.all do
    match rows.filter (·.rule = rule) with
    | [_] => pure ()
    | found => throwError "lowering coverage: rule {rule.id} has {found.length} rows; expected exactly one"
  for row in rows do
    unless Rule.all.contains row.rule do
      throwError "lowering coverage: row names a rule outside Rule.all"
  -- derived state equals declared state
  for row in rows do
    unless derive row = row.state do
      throwError "lowering coverage: rule {row.rule.id} declares {row.state.name} but its evidence derives {(derive row).name}"
  -- proofs are theorems within the ceiling
  let environment ← getEnv
  for row in rows do
    if let some proof := row.proof then
      match environment.find? proof with
      | some (.thmInfo _) =>
          let axioms ← liftCoreM (collectAxioms proof)
          for used in axioms do
            unless allowedAxioms.contains used do
              throwError "lowering coverage: proof {proof} for {row.rule.id} reaches {used}"
      | _ => throwError "lowering coverage: proof {proof} for {row.rule.id} is not a theorem"
  -- emit
  for row in rows do
    let goldens := String.intercalate "," row.goldens
    let proof := match row.proof with | some name => name.toString | none => "-"
    let flag (b : Bool) := if b then "1" else "0"
    IO.println s!"E4LOWCOV\t{row.rule.id}\t{row.state.name}\t{goldens}\t{flag row.host}\t{flag row.property}\t{flag row.typeReceipt}\t{proof}"
  logInfo m!"lowering coverage: {rows.length} rows over {Rule.all.length} rules"

#lowering_coverage

end Effect4Test.Target.TypeScript.LoweringCoverage

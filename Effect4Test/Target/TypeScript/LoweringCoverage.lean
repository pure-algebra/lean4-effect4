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
  , { rule := .dispatchLoop, state := .covered,
      goldens := ["flow/incr.empty", "flow/twice.empty", "flow/chooser.left", "flow/swap.once"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .blockCase, state := .covered,
      goldens := ["flow/incr.empty", "flow/twice.empty", "flow/chooser.left", "flow/swap.once"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .paramMove, state := .covered,
      goldens := ["flow/incr.empty", "flow/twice.empty", "flow/chooser.left", "flow/swap.once", "flow/swap.twice"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .flowPerform, state := .covered, goldens := ["flow/incr.empty", "flow/twice.empty"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .flowAtom, state := .covered, goldens := ["flow/incr.empty", "flow/twice.empty"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .flowLiteral, state := .covered, goldens := ["flow/incr.empty", "flow/twice.empty", "flow/swap.once"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .chooseIf, state := .covered,
      goldens := ["flow/chooser.left", "flow/chooser.right", "flow/swap.once", "flow/swap.twice"],
      host := true, property := true, typeReceipt := true, proof := none }
  -- interruption as decisions (Skeleton.lean, packet M2); the goldens are the
  -- three interrupt programs. No host column: the interrupt goldens run through
  -- `interrupt-tail.ts`, whose receipts live under receipts/flow/interrupt/ and
  -- are written by the host gate, not by this join.
  , { rule := .interruptPoint, state := .pinned,
      goldens := ["flow/interrupt/interruptUnmasked", "flow/interrupt/interruptMasked",
                  "flow/interrupt/interruptFinalizer"],
      host := false, property := false, typeReceipt := false, proof := none }
  -- regions (RegionLower.lean); the goldens are the region programs of the harness
  , { rule := .regionEnter, state := .checked,
      goldens := ["flow/regionNested.empty", "flow/regionTwoFail.empty", "flow/regionBothSucceed.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  -- a masked region (packet M2 repair): `Effect.uninterruptible` around the scoped
  -- generator; pinned on the masked interrupt golden through `interrupt-tail.ts`
  , { rule := .regionMasked, state := .pinned,
      goldens := ["flow/interrupt/interruptMasked"],
      host := false, property := false, typeReceipt := false, proof := none }
  , { rule := .regionAcquire, state := .checked,
      goldens := ["flow/regionNested.empty", "flow/regionTwoFail.empty", "flow/regionBothSucceed.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .regionLeave, state := .checked,
      goldens := ["flow/regionNested.empty", "flow/regionTwoFail.empty", "flow/regionBothSucceed.empty"],
      host := true, property := false, typeReceipt := true, proof := none }
  -- the structured form (StructuredLower.lean); swap has a self-loop, irreducible falls back
  , { rule := .structuredLoop, state := .covered, goldens := ["flow/swap.once", "flow/swap.twice"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .structuredMerge, state := .covered, goldens := ["flow/swap.once", "flow/swap.twice"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .structuredContinue, state := .covered, goldens := ["flow/swap.once", "flow/swap.twice"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .structuredBreak, state := .covered, goldens := ["flow/swap.once", "flow/swap.twice"],
      host := true, property := true, typeReceipt := true, proof := none }
  , { rule := .dispatchFallback, state := .checked, goldens := ["flow/irreducible.left", "flow/irreducible.right"],
      host := true, property := false, typeReceipt := true, proof := none }
  , { rule := .flowRet, state := .covered,
      goldens := ["flow/incr.empty", "flow/twice.empty", "flow/chooser.left", "flow/swap.once"],
      host := true, property := true, typeReceipt := true, proof := none }
  -- a two-parameter operation performed from one request slot (Skeleton.lean);
  -- pinned on the job goldens, whose `ack`, `requeue` and `run` are the only
  -- multi-argument calls the harness lowers. No host column: the job goldens
  -- run through `job-tail.ts`, whose receipts live under receipts/job/ and are
  -- written by the host gate, not by this join.
  , { rule := .performTuple, state := .pinned,
      goldens := ["job/jobRunner.clean", "job/jobRunner.requeue", "job/jobPoison.poison"],
      host := false, property := false, typeReceipt := false, proof := none } ]

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

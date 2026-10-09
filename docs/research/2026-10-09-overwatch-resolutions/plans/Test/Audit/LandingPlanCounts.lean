import Tools.LoadPaths
import Effect4.Laws.Store.ShapeRead

/-!
Controls of the landing plan (`#landing_plan`, `tools/Tools/LoadPaths.lean`), from Codex's S1
load review (`docs/research/2026-10-08-s1-overwatch-receipt.md`):

1. **One count** (S1-PLAN-02). Two helpers reuse one tree theorem, and a top uses both. The plan
   counts edges as `#load_report` does: two tree edges against two local ones, 50%.
2. **Standing** (S1-PLAN-01). A helper that rests on a planned goal is listed as not proved, with
   the goal it rests on, as `ProofGraph.standing` says.
3. **Data is no top** (S1-PLAN-03). A definition is refused, as an unknown name is.

The theorems below are tooling controls with no semantic placement: their consumer is this file.
-/
namespace Test.LandingPlanCounts
open Lean Elab Command Tools.LoadPaths

/-- A tooling control: a step that reuses `natOfBinary64_exact`. -/
theorem helperOne {bits : UInt64} {n : Nat} (h : Effect4.Store.natOfBinary64 bits = some n) :
    Effect4.Arch.binary64OfNat n = bits :=
  Effect4.Store.natOfBinary64_exact h

/-- A tooling control: a second step that reuses the same theorem. -/
theorem helperTwo {bits : UInt64} {n : Nat} (h : Effect4.Store.natOfBinary64 bits = some n) :
    bits = Effect4.Arch.binary64OfNat n :=
  (Effect4.Store.natOfBinary64_exact h).symm

/-- A tooling control: the top that uses both steps. -/
theorem topPair {bits : UInt64} {n : Nat} (h : Effect4.Store.natOfBinary64 bits = some n) :
    Effect4.Arch.binary64OfNat n = bits ∧ bits = Effect4.Arch.binary64OfNat n :=
  ⟨helperOne h, helperTwo h⟩

#landing_plan topPair
#load_report Test.Audit.LandingPlanCounts
run_cmd do
  let env ← getEnv
  let g := buildGraph env
  let rs := roots env
  let modules := [`Test.Audit.LandingPlanCounts]
  let prediction := predict env modules #[``topPair]
  let planned := countEdges env g modules prediction.members.toList
  let measured := measure env g rs (loadBearing g rs) modules
  unless planned.ratio == 50 && measured.edges.ratio == 50 &&
      planned.tree == 2 && measured.edges.tree == 2 &&
      planned.local_ == 2 && measured.edges.local_ == 2 do
    throwError "shared plan/report count does not match the independent four-edge example"
/--
error: #landing_plan: Nat is not an authored theorem; a plan's top is a theorem
-/
#guard_msgs (error) in
#landing_plan Nat
/--
error: #landing_plan: Nat.zero is not an authored theorem; a plan's top is a theorem
-/
#guard_msgs (error) in
#landing_plan Nat.zero
end Test.LandingPlanCounts

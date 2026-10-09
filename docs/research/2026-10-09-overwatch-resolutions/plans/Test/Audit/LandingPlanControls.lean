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
namespace Test.LandingPlanControls
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

-- 1. the plan's count: one joint named twice, two local edges, 50%, as the report counts
/--
info: landing plan for [Test.LandingPlanControls.topPair (proved)] in [Test.Audit.LandingPlanControls]
  to land (0 planned goals): []
  local steps, proved (2): [Test.LandingPlanControls.helperOne, Test.LandingPlanControls.helperTwo]
  local steps, not proved (0): []
  joints reused (1, 1 of them load-bearing): [Effect4.Store.natOfBinary64_exact ×2]
  predicted reuse: 50% (2 tree edges, 2 local), as `#load_report` counts it
-/
#guard_msgs in
#landing_plan topPair

-- 2. a step that rests on a goal is not proved, and the goal is owed
proof_goal localGoal : True
/-- A tooling control: a step that rests on `localGoal`. -/
theorem pendingHelper : True := localGoal
/-- A tooling control: the top over the pending step. -/
theorem pendingTop : True := pendingHelper

/--
info: landing plan for [Test.LandingPlanControls.pendingTop (modulo [Test.LandingPlanControls.localGoal])] in [Test.Audit.LandingPlanControls]
  to land (1 planned goals): [Test.LandingPlanControls.localGoal]
  local steps, proved (0): []
  local steps, not proved (1): [Test.LandingPlanControls.pendingHelper (modulo [Test.LandingPlanControls.localGoal])]
  joints reused (0, 0 of them load-bearing): []
  predicted reuse: 0% (0 tree edges, 2 local), as `#load_report` counts it
-/
#guard_msgs in
#landing_plan pendingTop

-- 3. red: a definition is no top
/-- A tooling control: data. -/
def dataTop : PLift True := ⟨True.intro⟩

/--
error: #landing_plan: Test.LandingPlanControls.dataTop is not an authored theorem; a plan's top is a theorem
-/
#guard_msgs (error) in
#landing_plan dataTop

end Test.LandingPlanControls

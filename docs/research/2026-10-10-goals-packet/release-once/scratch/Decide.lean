import Test.Dogfood.Scenario.Atomic

/-! Scratch: can the kernel decide a static fact of a built program? A measurement: `decide`
must evaluate the shop's build (elaboration, checking, admission) and the static test. -/

set_option autoImplicit false
set_option maxRecDepth 100000

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Test.Dogfood.Scenario

namespace Scratch.Decide

def onceChild : Node NativeOp → Nat → Bool
  | .eff (.suspend _), 0 => true
  | .eff (.bind _ _), _ => true
  | .eff (.withFiber _), 0 => true
  | .eff (.onExit _ _), _ => true
  | .action (.fork _ _), 0 => true
  | _, _ => false

def OncePlaced : Node NativeOp → List Nat → Bool
  | _, [] => true
  | n, i :: rest =>
    onceChild n i &&
      match n.child i with
      | some c => OncePlaced c rest
      | none => false

/-- The static fact at request 1's `onExit`, read off the shop's build. -/
def shopFact : Bool :=
  match Effect4.Api.Author.build (Atomic.shop .none) with
  | .ok b => OncePlaced (Node.eff b.program) [1, 1, 1, 1, 0, 0, 0]
  | .error _ => false

#eval shopFact

set_option maxHeartbeats 2000000 in
theorem shopFact_true : shopFact = true := by decide

end Scratch.Decide

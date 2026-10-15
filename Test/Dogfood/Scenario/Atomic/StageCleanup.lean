import Test.Dogfood.Scenario.Atomic.StageRequest

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the request finalizer entry of `Atomic.Store.shop_stages`.
The actual finalizer reads one window, appends one note and finishes with pure unit binders.
Its captured read carries the positive decision count into the later note operation.
The native mask and command invariant remain separate producer obligations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageCleanup
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open StageWorld

def path (id : Nat) : List Nat := SourcePaths.requestPath id ++ [1]

/-- The finalizer shape retains the literal request identity and its actual captured-read binder. -/
def site (root : NativeEff) (id : Nat) : Bool :=
  match SourceScope.levelAt (.eff root) 0 (path id), Node.at_ (.eff root) (path id) with
  | some level, some (.eff (.bind (.perform .refGet (.var 0))
      (.bind (.perform (.refUpdateWith term) (.var 2))
        (.bind (.succeed (.lit .unit)) (.succeed (.lit .unit)))))) =>
      term == Store.noteAt id (level + 1)
  | _, _ => false

/-- All six actual finalizers preserve this read, note and pure-tail source shape. -/
theorem source_census :
    (Store.shopProgram.map fun root => requests.all (site root)) = some true := by
  kernel_rfl
end Test.Dogfood.Scenario.Atomic.StageCleanup

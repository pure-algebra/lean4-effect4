import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: N1's stuck step. `#reduce` prints the normal form that the elaborator reaches
at a symbolic literal, so a stuck term shows its head. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option pp.deepTerms false

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace KMProbe3

def loop0 (total : Nat) : Module NativeOp :=
  { main := iterateWith (bool true)
        { while_ := fun _ => bool true
          body := fun _ => succeed (nat total)
          step := fun c _ => c } }

-- 1. The minted loop's tree at the empty scope.
#reduce fun total : Nat => ((loop0 total).main {} []).toOption.isSome

-- 2. Its layer sites.
#reduce fun total : Nat => ((loop0 total).main {} []).toOption.map fun t => (t.refSites []).isEmpty

-- 3. The module's elaboration.
#reduce fun total : Nat => (elaborateModule (loop0 total)).toOption.isSome

end KMProbe3

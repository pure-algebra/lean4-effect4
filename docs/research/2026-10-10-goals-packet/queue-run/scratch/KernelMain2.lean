import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: N1's route, with every definition unfoldable. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace KMProbe2

def scopeOf (m : Module NativeOp) : Env := { layers := [], rows := RowDef.names m.rowDefs, defs := [] }

set_option profiler true in
/-- The crew's main program, at every job count, with every definition unfoldable. -/
example (total : Nat) : ((crew total).main (scopeOf (crew total)) []).toOption.isSome = true := by
  with_unfolding_all rfl

set_option profiler true in
/-- The whole module, at every job count, with every definition unfoldable. -/
example (total : Nat) : (Program.Authoring.elaborateModule (crew total)).toOption.isSome = true := by
  with_unfolding_all rfl

end KMProbe2

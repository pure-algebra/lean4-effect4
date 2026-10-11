import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: N1's route. Does the crew's main program elaborate at a symbolic job count,
in the scope that `elaborateModule` gives it, and do its layer sites reduce there? -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace KMProbe

/-- The scope that `elaborateModule` gives a module with rows and no layer or definition. -/
def scopeOf (m : Module NativeOp) : Env := { layers := [], rows := RowDef.names m.rowDefs, defs := [] }

set_option profiler true in
/-- The crew's main program elaborates at every job count. -/
example (total : Nat) : ((crew total).main (scopeOf (crew total)) []).toOption.isSome = true := by
  rfl

set_option profiler true in
/-- Its tree names no layer, at every job count. -/
example (total : Nat) :
    (((crew total).main (scopeOf (crew total)) []).toOption.map fun tree =>
      (tree.refSites []).isEmpty) = some true := by
  rfl

end KMProbe

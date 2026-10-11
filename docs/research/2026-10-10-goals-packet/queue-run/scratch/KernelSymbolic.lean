import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: the kernel on crew's elaboration with a symbolic job count. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace KSProbe

/-- Worker 1's loop path, from the census. -/
def workerLoop : List Nat := [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1]

set_option profiler true in
/-- Elaborator's `rfl` at a fixed job count. -/
example : (Program.Authoring.elaborateModule (crew 3)).toOption.isSome = true := by
  rfl

set_option profiler true in
/-- The kernel alone, at every job count. -/
theorem crew_elaborates (total : Nat) :
    (Program.Authoring.elaborateModule (crew total)).toOption.isSome = true := by
  decide +kernel

set_option profiler true in
/-- The kernel alone: the node at worker 1's loop path is a program, at every job count. -/
theorem crew_loop_node (total : Nat) :
    ((Program.Authoring.elaborateModule (crew total)).toOption.bind fun p =>
      ((Node.eff p).at_ workerLoop).bind Node.eff?).isSome = true := by
  decide +kernel

end KSProbe

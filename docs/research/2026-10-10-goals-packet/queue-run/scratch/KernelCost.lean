import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: how much the kernel pays to reduce crew's elaboration and its compiled code. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace KCProbe

/-- The node at worker 1's loop path, by evaluation. -/
def workerLoop : List Nat := [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1]

#eval match Program.Authoring.elaborateModule (crew 3) with
  | .ok p =>
    match (Node.eff p).at_ workerLoop with
    | some (Node.eff (.iterate ..)) => "iterate at the worker's loop path"
    | some (Node.eff _) => "another program at the worker's loop path"
    | some _ => "a node that is no program"
    | none => "no node"
  | .error _ => "refused"

set_option profiler true in
/-- Kernel: the crew's elaboration at three jobs succeeds. -/
theorem crew3_elaborates : (Program.Authoring.elaborateModule (crew 3)).toOption.isSome = true := by
  decide

set_option profiler true in
/-- Kernel: the node at worker 1's loop path is a loop, at three jobs. -/
theorem crew3_loop :
    ((Program.Authoring.elaborateModule (crew 3)).toOption.bind fun p =>
      (Node.eff p).at_ workerLoop).isSome = true := by
  decide

end KCProbe

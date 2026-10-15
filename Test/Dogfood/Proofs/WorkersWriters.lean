import Test.Dogfood.Scenario.Programs
import Effect4.Laws.Auto.KernelRfl
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.ControlSteps
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario

/-!
Concept: scope-lifetime-finalization R11.
Question: source-address and acquired-value census serves Workers.Assertions.logs_step.
Reach: the actual elaborated Workers source at every job total.
Limit: the source equations prove no runtime slot ownership or log debit.
Unlock: they identify the smallest exact slot relation before dynamic writer preservation.
-/


namespace Test.Dogfood.Proofs.WorkersWriters
open Effect4.Laws.Auto

def appendOne (old : Nat) (entry : Term) : Term :=
  .app "append" (.cons (.var old) (.cons
    (.app "cons" (.cons entry (.cons (.app "nil" .nil) .nil))) .nil))

theorem release_one (total : Nat) :
    Node.at_ (.eff (Programs.workersProgram total)) (Programs.crewAcquire 1 ++ [1]) =
      some (.eff (.perform (.refUpdateWith (appendOne 7 (.var 5))) (.var 1))) := by
  kernel_rfl

theorem release_two (total : Nat) :
    Node.at_ (.eff (Programs.workersProgram total)) (Programs.crewAcquire 2 ++ [1]) =
      some (.eff (.perform (.refUpdateWith (appendOne 8 (.var 6))) (.var 1))) := by
  kernel_rfl

theorem acquire_one (total : Nat) :
    Node.at_ (.eff (Programs.workersProgram total)) (Programs.crewAcquire 1 ++ [0]) =
      some (.eff (.bind (.perform (.refUpdateWith (appendOne 5 (.lit (.nat 1)))) (.var 0))
        (.succeed (.lit (.nat 1))))) := by
  kernel_rfl

theorem acquire_two (total : Nat) :
    Node.at_ (.eff (Programs.workersProgram total)) (Programs.crewAcquire 2 ++ [0]) =
      some (.eff (.bind (.perform (.refUpdateWith (appendOne 6 (.lit (.nat 2)))) (.var 0))
        (.succeed (.lit (.nat 2))))) := by
  kernel_rfl

/-- These are the five root bindings; the release cell remains an explicit parameter.
The actual history must establish the bindings and the acquired literal before using this producer. -/
def rootEnv (opened : Val) (released : RefKey) (assigned count gate : Val) : List Val :=
  [opened, .cell released, assigned, count, gate]

theorem release_one_code (total : Nat) (opened assigned count gate : Val) (released : RefKey)
    (exit : Val) (fuel : Nat) (tape : List Bool) :
    resolve (Programs.workersProgram total)
      {path := Programs.crewAcquire 1 ++ [1], env := rootEnv opened released assigned count gate ++ [.nat 1, exit],
        fuel := fuel + 1, tape} =
      .sync (.op (.refUpdate released (appendOne 7 (.var 5))
        (rootEnv opened released assigned count gate ++ [.nat 1, exit]))) := by
  rw [Agreement.resolve_of_at (release_one total)]
  cases released
  kernel_rfl

theorem release_two_code (total : Nat) (opened assigned count gate previous : Val) (released : RefKey)
    (exit : Val) (fuel : Nat) (tape : List Bool) :
    resolve (Programs.workersProgram total)
      {path := Programs.crewAcquire 2 ++ [1], env := rootEnv opened released assigned count gate ++ [previous, .nat 2, exit],
        fuel := fuel + 1, tape} =
      .sync (.op (.refUpdate released (appendOne 8 (.var 6))
        (rootEnv opened released assigned count gate ++ [previous, .nat 2, exit]))) := by
  rw [Agreement.resolve_of_at (release_two total)]
  cases released
  kernel_rfl

theorem append_one_value (opened assigned count gate exit : Val) (released : RefKey) (old : List Val) :
    evalTerm ((rootEnv opened released assigned count gate ++ [.nat 1, exit]) ++ [.list old])
      (appendOne 7 (.var 5)) = some (.list (old ++ [.nat 1])) := by
  kernel_rfl

theorem append_two_value (opened assigned count gate previous exit : Val) (released : RefKey) (old : List Val) :
    evalTerm ((rootEnv opened released assigned count gate ++ [previous, .nat 2, exit]) ++ [.list old])
      (appendOne 8 (.var 6)) = some (.list (old ++ [.nat 2])) := by
  kernel_rfl

/-- The actual release expression writes its acquired literal once and answers unit.
The history consumer still owes the explicit environment and heap-read premises. -/
theorem release_one_step (state : Stores) (opened assigned count gate exit : Val)
    (released : RefKey) (old : List Val)
    (read : refPeek state.refs released = some (.list old)) :
    syncOpStep (.refUpdate released (appendOne 7 (.var 5))
      (rootEnv opened released assigned count gate ++ [.nat 1, exit])) state =
      some ({ state with refs := refPoke state.refs released (.list (old ++ [.nat 1])) }, .unit) := by
  change (refStep (.refUpdate released (appendOne 7 (.var 5))
      (rootEnv opened released assigned count gate ++ [.nat 1, exit])) state.refs).map _ = _
  rw [refStep_update state.refs released _ _ _ _ read
    (append_one_value opened assigned count gate exit released old)]
  rfl

theorem release_two_step (state : Stores) (opened assigned count gate previous exit : Val)
    (released : RefKey) (old : List Val)
    (read : refPeek state.refs released = some (.list old)) :
    syncOpStep (.refUpdate released (appendOne 8 (.var 6))
      (rootEnv opened released assigned count gate ++ [previous, .nat 2, exit])) state =
      some ({ state with refs := refPoke state.refs released (.list (old ++ [.nat 2])) }, .unit) := by
  change (refStep (.refUpdate released (appendOne 8 (.var 6))
      (rootEnv opened released assigned count gate ++ [previous, .nat 2, exit])) state.refs).map _ = _
  rw [refStep_update state.refs released _ _ _ _ read
    (append_two_value opened assigned count gate previous exit released old)]
  rfl

/-- The first real command consumer retains other fibers and unfinished commands.
It spends a supplied source/slot witness; it does not establish that witness from history. -/
theorem release_one_command (total : Nat) (table : RowTable) (machine : Api.Machine)
    (id : FiberId) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (opened assigned count gate exit : Val) (released : RefKey) (old : List Val)
    (fuel : Nat) (tape : List Bool) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : machine.fiber? id = some fiber)
    (current : fiber.frame.current = resolve (Programs.workersProgram total)
      {path := Programs.crewAcquire 1 ++ [1],
        env := rootEnv opened released assigned count gate ++ [.nat 1, exit], fuel := fuel + 1, tape})
    (read : refPeek machine.state.refs released = some (.list old))
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 1 < fiber.maxOpsBeforeYield) :
    driveStep (evaluator := evaluatorFor (Programs.workersProgram total) table)
      (interpOf (Programs.workersProgram total) table) machine (.loop id yielding) rest =
      (({machine with state := {machine.state with
          refs := refPoke machine.state.refs released (Val.list (old ++ [Val.nat 1]))}}).update
        {countOp fiber with frame := {fiber.frame with current := .success .unit}},
       [.drainDue, .deliver id yielding] ++ rest) := by
  rw [release_one_code] at current
  exact ControlSteps.loop_sync_op _ table machine id fiber _ _ .unit yielding rest
    found current interrupt override budget
    (release_one_step machine.state opened assigned count gate exit released old read)

end Test.Dogfood.Proofs.WorkersWriters


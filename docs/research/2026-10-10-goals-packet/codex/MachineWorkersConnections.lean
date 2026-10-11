import MachineWorkersSlots

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual acquired values and captured slots serve Workers.Assertions.logs_step.
Reach: both actual acquisition sites, every job total and supplied native source point.
Limit: history must retain the binding prefix and reach each callback with its actual answer.
Consumer: the existing actual release writer command consumes the captured environment.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace MachineWorkersConnections
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario MachineWorkersSlots

theorem acquisition_one_level (total : Nat) :
    SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 (Programs.crewAcquire 1) = some 5 := by
  kernel_rfl

theorem acquisition_two_level (total : Nat) :
    SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 (Programs.crewAcquire 2) = some 6 := by
  kernel_rfl

/-- The actual first acquisition has no unnamed environment entries after its five bindings. -/
theorem acquisition_one_env (total : Nat) (point : Point)
    (path : point.path = Programs.crewAcquire 1)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) : point.env = bindings := by
  have length : point.env.length = 5 := by
    change SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 point.path =
      some point.env.length at lexical
    rw [path, acquisition_one_level] at lexical
    exact (Option.some.inj lexical).symm
  rw [List.take_of_length_le (by omega)] at leading
  exact leading

/-- The second acquisition retains its previous fork answer after the five bindings. -/
theorem acquisition_two_env (total : Nat) (point : Point)
    (path : point.path = Programs.crewAcquire 2)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) : ∃ previous, point.env = bindings ++ [previous] := by
  have length : point.env.length = 6 := by
    change SourceScope.levelAt (.eff (Programs.workersProgram total)) 0 point.path =
      some point.env.length at lexical
    rw [path, acquisition_two_level] at lexical
    exact (Option.some.inj lexical).symm
  have residual : (point.env.drop 5).length = 1 := by
    rw [List.length_drop, length]
  have split := List.take_append_drop 5 point.env
  rw [leading] at split
  cases dropped : point.env.drop 5 with
  | nil => rw [dropped] at residual; cases residual
  | cons previous rest =>
    rw [dropped] at residual
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by
      change rest.length + 1 = 1 at residual
      omega)
    rw [dropped, empty] at split
    exact ⟨previous, split.symm⟩

/-- The acquisition's actual return source fixes the first connection literal. -/
theorem acquisition_one_answer (total : Nat) (point : Point) (fuel : Nat)
    (path : point.path = Programs.crewAcquire 1 ++ [0, 1])
    (amount : point.fuel = fuel + 1) :
    resolve (Programs.workersProgram total) point = .success (.nat 1) := by
  have found : Node.at_ (.eff (Programs.workersProgram total)) point.path =
      some (.eff (.succeed (.lit (.nat 1)))) := by
    rw [path]
    kernel_rfl
  rw [Agreement.resolve_of_at found, Agreement.compileEff_succeed _ amount]
  rfl

/-- The acquisition's actual return source fixes the second connection literal. -/
theorem acquisition_two_answer (total : Nat) (point : Point) (fuel : Nat)
    (path : point.path = Programs.crewAcquire 2 ++ [0, 1])
    (amount : point.fuel = fuel + 1) :
    resolve (Programs.workersProgram total) point = .success (.nat 2) := by
  have found : Node.at_ (.eff (Programs.workersProgram total)) point.path =
      some (.eff (.succeed (.lit (.nat 2)))) := by
    rw [path]
    kernel_rfl
  rw [Agreement.resolve_of_at found, Agreement.compileEff_succeed _ amount]
  rfl

/-- The actual captured first release keeps both the cell and the acquired identity.
The destination appends the exit binder beyond the saved acquisition value. -/
theorem captured_one_writer (total : Nat) (point : Point) (context : Ctx)
    (exit : Val) (view : List (FiberId × ExitV)) (fuel : Nat)
    (path : point.path = Programs.crewAcquire 1)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) (amount : point.fuel = fuel + 2) :
    resolve (Programs.workersProgram total)
      ((Point.ofCapture (point.capture (.nat 1) context) view).childWith 1 exit) =
      .sync (.op (.refUpdate ⟨1⟩ (MachineWorkersWriters.appendOne 7 (.var 5))
        (bindings ++ [.nat 1, exit]))) := by
  have env := acquisition_one_env total point path lexical leading
  have found : Node.at_ (.eff (Programs.workersProgram total))
      ((Point.ofCapture (point.capture (.nat 1) context) view).childWith 1 exit).path =
      some (.eff (.perform (.refUpdateWith (MachineWorkersWriters.appendOne 7 (.var 5))) (.var 1))) := by
    change Node.at_ _ (point.path ++ [1]) = _
    rw [path]
    exact MachineWorkersWriters.release_one total
  rw [Agreement.resolve_of_at found]
  rw [Agreement.compileEff_perform_sync _ _ (k := fuel) (by
    change point.fuel - 1 = fuel + 1
    rw [amount]
    omega) rfl]
  change (match evalTerm (point.env ++ [Val.nat 1] ++ [exit]) (.var 1) with
    | some val => match NativeOp.syncOpOf (.refUpdateWith (MachineWorkersWriters.appendOne 7 (.var 5))) (point.env ++ [Val.nat 1] ++ [exit]) val with
      | some operation => Prim.sync (EffThunk.op operation)
      | none => badShape
    | none => badShape) = _
  rw [env]
  kernel_rfl


/-- The second captured release keeps its previous answer and the second connection literal. -/
theorem captured_two_writer (total : Nat) (point : Point) (context : Ctx)
    (exit : Val) (view : List (FiberId × ExitV)) (fuel : Nat)
    (path : point.path = Programs.crewAcquire 2)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) (amount : point.fuel = fuel + 2) :
    ∃ previous, resolve (Programs.workersProgram total)
      ((Point.ofCapture (point.capture (.nat 2) context) view).childWith 1 exit) =
      .sync (.op (.refUpdate ⟨1⟩ (MachineWorkersWriters.appendOne 8 (.var 6))
        (bindings ++ [previous, .nat 2, exit]))) := by
  obtain ⟨previous, env⟩ := acquisition_two_env total point path lexical leading
  refine ⟨previous, ?_⟩
  have found : Node.at_ (.eff (Programs.workersProgram total))
      ((Point.ofCapture (point.capture (.nat 2) context) view).childWith 1 exit).path =
      some (.eff (.perform (.refUpdateWith (MachineWorkersWriters.appendOne 8 (.var 6))) (.var 1))) := by
    change Node.at_ _ (point.path ++ [1]) = _
    rw [path]
    exact MachineWorkersWriters.release_two total
  rw [Agreement.resolve_of_at found]
  rw [Agreement.compileEff_perform_sync _ _ (k := fuel) (by
    change point.fuel - 1 = fuel + 1
    rw [amount]
    omega) rfl]
  change (match evalTerm (point.env ++ [Val.nat 2] ++ [exit]) (.var 1) with
    | some val => match NativeOp.syncOpOf (.refUpdateWith (MachineWorkersWriters.appendOne 8 (.var 6)))
        (point.env ++ [Val.nat 2] ++ [exit]) val with
      | some operation => Prim.sync (EffThunk.op operation)
      | none => badShape
    | none => badShape) = _
  rw [env]
  kernel_rfl

/-- An actual cleanup command consumes the effective capture destination and retained slots.
The command retains every other fiber and its unfinished command suffix. -/
theorem captured_one_command (total : Nat) (table : RowTable) (machine : Api.Machine)
    (id : FiberId) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (point : Point) (context : Ctx) (exit : Val) (view : List (FiberId × ExitV))
    (fuel : Nat) (yielding : Bool) (old : List Val)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (path : point.path = Programs.crewAcquire 1)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) (amount : point.fuel = fuel + 2)
    (found : machine.fiber? id = some fiber)
    (current : fiber.frame.current = resolve (Programs.workersProgram total)
      ((Point.ofCapture (point.capture (.nat 1) context) view).childWith 1 exit))
    (read : refPeek machine.state.refs ⟨1⟩ = some (.list old))
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 1 < fiber.maxOpsBeforeYield) :
    driveStep (evaluator := evaluatorFor (Programs.workersProgram total) table)
      (interpOf (Programs.workersProgram total) table) machine (.loop id yielding) rest =
      (({machine with state := {machine.state with
          refs := refPoke machine.state.refs ⟨1⟩ (Val.list (old ++ [Val.nat 1]))}}).update
        {countOp fiber with frame := {fiber.frame with current := .success .unit}},
       [.drainDue, .deliver id yielding] ++ rest) := by
  have code := current.trans (captured_one_writer total point context exit view fuel path lexical leading amount)
  exact ControlSteps.loop_sync_op _ table machine id fiber _ _ .unit yielding rest
    found code interrupt override budget
    (MachineWorkersWriters.release_one_step machine.state (.cell ⟨0⟩) (.cell ⟨2⟩)
      (.cell ⟨3⟩) (.promise ⟨0⟩) exit ⟨1⟩ old read)

end MachineWorkersConnections

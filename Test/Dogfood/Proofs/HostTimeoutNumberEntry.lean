import Test.Dogfood.Proofs.HostTimeoutNumberState
import Test.Dogfood.Proofs.HostTimeoutEvaluation
import Effect4.Laws.Program.ControlSteps
import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Machine.Keeps

/-!
Placement: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the pre-count entry step of Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: the numeric source assertion's actual attempt-entry producer.
The equations retain symbolic stores, fibers, saved suffixes, and captured source metadata.
They establish the count prefix under explicit entry premises, not full reached history.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberEntry
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberSteps HostTimeoutNumberState
open HostTimeoutEvaluation

/-- The existing source point retains its metadata at the attempt's entry. -/
def attemptPoint (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) : Point :=
  {captured with
    path := [1,1,1,0,0,1,0,0,0,0,0,0]
    env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error
    fuel := fuel + 3}

/-- The actual update term comes from the generated count leaf. -/
def countTerm : Term :=
  match (HostTimeoutNative.performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,0]).1 with
  | .refUpdateWith term => term
  | _ => .lit .unit

/-- The count leaf compiles before either saved callback can run. -/
theorem attempt_code (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) :
    let point := attemptPoint captured fuel delay n error
    resolve HostTimeoutSource.program point =
      .onExit (.onSuccess (.sync (.op (.refUpdate ⟨0⟩ countTerm point.env)))
        (.cont (point.child 0))) (.fin point) false := by
  dsimp only
  kernel_rfl

/-- Entering the attempt installs its actual finalizer and leaves every store field unchanged. -/
theorem push_exit (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (body : NCode) (name : EffName)
    (current : fiber.frame.current = .onExit body name false) :
    evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table =
      ⟨machine.emit [.frame fiber.id (.pushed (.onExit body name false))],
        {fiber with frame := {fiber.frame with
          current := body
          stack := .onExit body name false :: fiber.frame.stack}}, yielding, .continue_, [], []⟩ := by
  have park : (interpAt HostTimeoutSource.program machine.completedExits
      Test.Dogfood.Scenario.Timeout.fetch.table).parkOf (.onExit body name false) = none := rfl
  simp only [evaluateNative, current, evaluatePrim, park,
    evaluatePrim.stepFrame, FrameFiber.step, evaluatePrim.finishFrame,
    List.map_cons, List.map_nil]

/-- Entering the count binder installs its actual return callback and leaves stores unchanged. -/
theorem push_success (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (body : NCode) (name : EffName)
    (current : fiber.frame.current = .onSuccess body name) :
    evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table =
      ⟨machine.emit [.frame fiber.id (.pushed (.onSuccess body name))],
        {fiber with frame := {fiber.frame with
          current := body
          stack := .onSuccess body name :: fiber.frame.stack}}, yielding, .continue_, [], []⟩ := by
  have park : (interpAt HostTimeoutSource.program machine.completedExits
      Test.Dogfood.Scenario.Timeout.fetch.table).parkOf (.onSuccess body name) = none := rfl
  simp only [evaluateNative, current, evaluatePrim, park,
    evaluatePrim.stepFrame, FrameFiber.step, evaluatePrim.finishFrame,
    List.map_cons, List.map_nil]

/-- The first counted frame push keeps its actual saved suffix. -/
def exitPushed (fiber : NativeFiber) (body : NCode) (name : EffName) : NativeFiber :=
  {countOp fiber with frame := {fiber.frame with
    current := body
    stack := .onExit body name false :: fiber.frame.stack}}

/-- The second counted frame push keeps the finalizer below its actual binder. -/
def successPushed (fiber : NativeFiber) (body : NCode) (name : EffName) : NativeFiber :=
  {countOp fiber with frame := {fiber.frame with
    current := body
    stack := .onSuccess body name :: fiber.frame.stack}}

/-- The first actual loop command installs the finalizer before its count binder. -/
theorem loop_push_exit (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (body : NCode) (name : EffName) (yielding : Bool) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = .onExit body name false)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 1 < fiber.maxOpsBeforeYield) :
    driveStep (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) machine
        (.loop fiber.id yielding) rest =
      ((machine.emit [.frame fiber.id (.pushed (.onExit body name false))]).update
        (exitPushed fiber body name), .loop fiber.id yielding :: rest) := by
  rw [ControlSteps.loop_of_iteration (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table) _ machine fiber.id fiber yielding rest found,
    ControlSteps.iteration_below_budget (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table) _ machine fiber yielding interrupt override budget]
  change settle fiber.id rest (evaluateNative HostTimeoutSource.program machine (countOp fiber) yielding Scenario.Timeout.fetch.table) = _
  rw [push_exit machine (countOp fiber) yielding body name current]
  rfl

/-- The second actual loop command reaches the synchronous count operation. -/
theorem loop_push_success (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (body : NCode) (name : EffName) (yielding : Bool) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = .onSuccess body name)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 1 < fiber.maxOpsBeforeYield) :
    driveStep (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) machine
        (.loop fiber.id yielding) rest =
      ((machine.emit [.frame fiber.id (.pushed (.onSuccess body name))]).update
        (successPushed fiber body name), .loop fiber.id yielding :: rest) := by
  rw [ControlSteps.loop_of_iteration (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table) _ machine fiber.id fiber yielding rest found,
    ControlSteps.iteration_below_budget (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table) _ machine fiber yielding interrupt override budget]
  change settle fiber.id rest (evaluateNative HostTimeoutSource.program machine (countOp fiber) yielding Scenario.Timeout.fetch.table) = _
  rw [push_success machine (countOp fiber) yielding body name current]
  rfl

/-- The source's concrete synchronous counter write increases the actual old counter. -/
theorem count_sync (state : Stores) (count delay : Nat) (n : Fin 4) (error : Val)
    (cleanups completed : List Val) :
    syncOpStep (.refUpdate ⟨0⟩ countTerm
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error))
        {state with refs := numberHeap count cleanups completed} =
      some ({state with refs := numberHeap (count + 1) cleanups completed}, .unit) := by
  exact count_update [] state 0 count delay n error cleanups completed

/-- The checked count prefix retains both actual saved callbacks in their source order. -/
def countedFiber (fiber : NativeFiber) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (error : Val) : NativeFiber :=
  let point := attemptPoint captured fuel delay n error
  let sync : NCode := .sync (.op (.refUpdate ⟨0⟩ countTerm point.env))
  let body : NCode := .onSuccess sync (.cont (point.child 0))
  let first := exitPushed fiber body (.fin point)
  let second := successPushed first sync (.cont (point.child 0))
  {countOp second with frame := {second.frame with current := .success .unit}}

/-- The checked count prefix records the actual two pushes and the committed reference write. -/
def countedMachine (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (captured : Point) (fuel delay count : Nat) (n : Fin 4) (error : Val)
    (cleanups completed : List Val) : Effect4.Program.NativeMachine :=
  let point := attemptPoint captured fuel delay n error
  let sync : NCode := .sync (.op (.refUpdate ⟨0⟩ countTerm point.env))
  let body : NCode := .onSuccess sync (.cont (point.child 0))
  let first := exitPushed fiber body (.fin point)
  let one := (machine.emit [.frame fiber.id (.pushed (.onExit body (.fin point) false))]).update first
  let second := successPushed first sync (.cont (point.child 0))
  let two := (one.emit [.frame first.id (.pushed (.onSuccess sync (.cont (point.child 0))))]).update second
  ({two with state := {two.state with refs := numberHeap (count + 1) cleanups completed}}).update
    (countedFiber fiber captured fuel delay n error)

/-- Three actual loop commands commit the count before the first owed resume or delivery.
The command residue remains symbolic; no later command runs inside this prefix. -/
theorem count_prefix_exact (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (captured : Point) (fuel delay count : Nat) (n : Fin 4) (error : Val)
    (cleanups completed : List Val) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (live : machine.stuck = none) (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = resolve HostTimeoutSource.program (attemptPoint captured fuel delay n error))
    (heap : machine.state.refs = numberHeap count cleanups completed)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 3 < fiber.maxOpsBeforeYield) :
    driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
      (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 3 machine
      (.loop fiber.id false :: rest) =
      (countedMachine machine fiber captured fuel delay count n error cleanups completed,
        [.drainDue, .deliver fiber.id false] ++ rest) := by
  letI := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table
  let point := attemptPoint captured fuel delay n error
  let sync : NCode := .sync (.op (.refUpdate ⟨0⟩ countTerm point.env))
  let body : NCode := .onSuccess sync (.cont (point.child 0))
  let first := exitPushed fiber body (.fin point)
  let one := (machine.emit [.frame fiber.id (.pushed (.onExit body (.fin point) false))]).update first
  let second := successPushed first sync (.cont (point.child 0))
  let two := (one.emit [.frame first.id (.pushed (.onSuccess sync (.cont (point.child 0))))]).update second
  have start : fiber.frame.current = .onExit body (.fin point) false :=
    current.trans (attempt_code captured fuel delay n error)
  have stepOne := loop_push_exit machine fiber body (.fin point) false rest found start
    interrupt override (by omega)
  have foundOne : one.fiber? first.id = some first :=
    RunMachine.fiber?_update_self first _ ⟨fiber, List.mem_of_find?_eq_some found, rfl⟩
  have stepTwo := loop_push_success one first sync (.cont (point.child 0)) false rest
    foundOne rfl interrupt override (by change fiber.currentOpCount + 1 + 1 < fiber.maxOpsBeforeYield; omega)
  have foundTwo : two.fiber? second.id = some second :=
    RunMachine.fiber?_update_self second _ ⟨first, List.mem_of_find?_eq_some foundOne, rfl⟩
  have counted : syncOpStep (.refUpdate ⟨0⟩ countTerm point.env) two.state =
      some ({two.state with refs := numberHeap (count + 1) cleanups completed}, .unit) := by
    have answer := count_sync two.state count delay n error cleanups completed
    have stored : two.state.refs = numberHeap count cleanups completed := heap
    have overwrite : {two.state with refs := numberHeap count cleanups completed} = two.state := by
      rw [← stored]
    rw [overwrite] at answer
    exact answer
  have stepThree := Effect4.Program.ControlSteps.loop_sync_op HostTimeoutSource.program
    Scenario.Timeout.fetch.table two second.id second (.refUpdate ⟨0⟩ countTerm point.env)
    {two.state with refs := numberHeap (count + 1) cleanups completed} .unit false rest
    foundTwo rfl interrupt override
    (by change fiber.currentOpCount + 1 + 1 + 1 < fiber.maxOpsBeforeYield; omega) counted
  dsimp only [countedMachine, countedFiber]
  rw [driveState_succ_cons, show machine.stuck.isSome = false by rw [live]; rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stepOne]
  change driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
    (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 2 one
      (.loop first.id false :: rest) = _
  rw [driveState_succ_cons, show one.stuck.isSome = false from (by change machine.stuck.isSome = false; rw [live]; rfl)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stepTwo]
  change driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
    (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 1 two
      (.loop second.id false :: rest) = _
  rw [driveState_succ_cons, show two.stuck.isSome = false from (by change machine.stuck.isSome = false; rw [live]; rfl)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stepThree]
  rfl

/-- Three actual loop commands commit the count before the first owed resume or delivery.
The command residue remains symbolic; no later command runs inside this prefix. -/
theorem count_prefix (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (captured : Point) (fuel delay count : Nat) (n : Fin 4) (error : Val)
    (cleanups completed : List Val) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (live : machine.stuck = none) (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = resolve HostTimeoutSource.program (attemptPoint captured fuel delay n error))
    (heap : machine.state.refs = numberHeap count cleanups completed)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 3 < fiber.maxOpsBeforeYield) :
    ∃ after,
      driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 3 machine
        (.loop fiber.id false :: rest) =
        (after, [.drainDue, .deliver fiber.id false] ++ rest) ∧
      after.state.refs = numberHeap (count + 1) cleanups completed := by
  refine ⟨countedMachine machine fiber captured fuel delay count n error cleanups completed,
    count_prefix_exact machine fiber captured fuel delay count n error cleanups completed rest
      live found current heap interrupt override budget, rfl⟩

/-- A real evaluate command resets the operation counter and commits the source count in four commands.
The source producer uses this bound under the original 2000-command budget. -/
theorem count_entry (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (captured : Point) (fuel delay count : Nat) (n : Fin 4) (error : Val)
    (cleanups completed : List Val) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (live : machine.stuck = none) (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = resolve HostTimeoutSource.program (attemptPoint captured fuel delay n error))
    (heap : machine.state.refs = numberHeap count cleanups completed)
    (idle : fiber.running = false) (parked : fiber.parked = .notParked) (unfinished : fiber.exit = none)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : 3 < fiber.maxOpsBeforeYield) :
    ∃ after,
      driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 4 machine
        (.evaluate fiber.id :: rest) =
        (after, [.drainDue, .deliver fiber.id false] ++ rest) ∧
      after.state.refs = numberHeap (count + 1) cleanups completed := by
  letI := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table
  let entered : NativeFiber := {fiber with running := true, currentOpCount := 0}
  let started := (machine.update entered).emit [.started fiber.id]
  have selected : started.fiber? entered.id = some entered := by
    rw [RunMachine.fiber?_emit]
    exact RunMachine.fiber?_update_self entered machine
      ⟨fiber, List.mem_of_find?_eq_some found, rfl⟩
  obtain ⟨after, prefixDone, counted⟩ := count_prefix started entered captured fuel delay count n error
    cleanups completed rest live selected current heap interrupt override budget
  refine ⟨after, ?_, counted⟩
  have entry : driveStep (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
      (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) machine (.evaluate fiber.id) rest =
      (started, .loop entered.id false :: rest) := by
    dsimp only [started, entered]
    simp only [driveStep, found, unfinished, idle, parked]
    rfl
  rw [driveState_succ_cons, show machine.stuck.isSome = false by rw [live]; rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [entry]
  exact prefixDone

/-- The original scenario budget executes the checked count prefix before its remaining commands. -/
theorem count_entry_budget (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (captured : Point) (fuel delay count : Nat) (n : Fin 4) (error : Val)
    (cleanups completed : List Val) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (live : machine.stuck = none) (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = resolve HostTimeoutSource.program (attemptPoint captured fuel delay n error))
    (heap : machine.state.refs = numberHeap count cleanups completed)
    (idle : fiber.running = false) (parked : fiber.parked = .notParked) (unfinished : fiber.exit = none)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : 3 < fiber.maxOpsBeforeYield) :
    ∃ after,
      driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) Scenario.Timeout.budget.fuel machine
        (.evaluate fiber.id :: rest) =
        driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
          (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 1996 after
          ([.drainDue, .deliver fiber.id false] ++ rest) ∧
      after.state.refs = numberHeap (count + 1) cleanups completed := by
  letI := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table
  obtain ⟨after, prefixDone, counted⟩ := count_entry machine fiber captured fuel delay count n error
    cleanups completed rest live found current heap idle parked unfinished interrupt override budget
  refine ⟨after, ?_, counted⟩
  change driveState (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) (4 + 1996)
    machine (.evaluate fiber.id :: rest) = _
  rw [driveState_add _ 4 1996, prefixDone]

end Test.Dogfood.Proofs.HostTimeoutNumberEntry

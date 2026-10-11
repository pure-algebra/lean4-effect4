import Test.Dogfood.Proofs.HostTimeoutNumberFinalizers

/-!
Placement: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the committed attempt-entry producer of Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: the numeric assertion at actual command and history boundaries.
The source count prefix produces its actual saved binder and finalizer, not an arbitrary numeric value.
The older suffix and source-entry premises remain explicit until the public-row producer supplies them.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberCounted
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberSteps HostTimeoutNumberState
open HostTimeoutEvaluation
open HostTimeoutNumberCallbacks HostTimeoutNumberFlow HostTimeoutNumberFinalizers HostTimeoutNumberEntry

/-- Entering an attempt consumes a complete cleanup and form prefix at the actual retry cursor. -/
def nextImage (image : Image) (n : Fin 4)
    (cleanupComplete : image.cleanups.length = image.count) (formComplete : image.exits.length = image.count)
    (cursor : image.count ≤ n.val) : Image :=
  ⟨image.count + 1, image.cleanups, image.completed, image.exits,
    count_numbers image.numbers n cleanupComplete formComplete cursor⟩

/-- The source's count callback resolves the exact HTTP body after committing the counter. -/
theorem count_callback (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) :
    let point := attemptPoint captured (fuel + 1) delay n error
    (interpreter view).contA (.cont (point.child 0)) .unit =
      resolve HostTimeoutSource.program (({point with completed := view}.child 0).childWith 1 .unit) := rfl

/-- The source body reached after the count callback registers precisely the existing HTTP row. -/
theorem attempt_body_code (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) :
    resolve HostTimeoutSource.program
      (((attemptPoint captured (fuel + 1) delay n error).child 0).childWith 1 .unit) =
      .async (.external (.external 0) (.str "EFX") [1,1,1,0,0,1,0,0,0,0,0,0,0,1]) false none := by
  kernel_rfl

/-- The count binder accepts only the committed post-count heap before entering the attempt body. -/
theorem count_saved (view : View) (state : Stores) (image : Image)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
    (count : image.count = n.val + 1) :
    let point := attemptPoint captured (fuel + 1) delay n error
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.unit image) (.at image)
      (.onSuccess (.sync (.op (.refUpdate ⟨0⟩ countTerm point.env))) (.cont (point.child 0))) := by
  dsimp only
  apply AnswerFlow.saved_success
  · intro next future value good
    change ImageAt image next ∧ value = .unit at good
    rw [good.2, count_callback]
    exact CodeAt.attemptBody image {captured with completed := view} fuel delay n error count good.1
  · intro next future cause good
    exact False.elim good

/-- The three-command prefix returns the exact saved binder and attempt finalizer in source order. -/
theorem counted_frame (view : View) (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (image : Image) (n : Fin 4) (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
    (captured : Point) (fuel delay : Nat) (error : Val) (output : HostTimeoutNumberFlow.Kind)
    (priorHeap : ImageAt image machine.state)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor))
        (by change image.count + 1 = image.cleanups.length + 1; rw [cleanupComplete]))
      output fiber.frame.stack) :
    let after := countedMachine machine fiber captured (fuel + 1) delay image.count n error image.cleanups image.completed
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp after.state output
      (countedFiber fiber captured (fuel + 1) delay n error).frame := by
  dsimp only
  let after := countedMachine machine fiber captured (fuel + 1) delay image.count n error image.cleanups image.completed
  let countedImage := nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)
  have heap : ImageAt countedImage after.state := rfl
  have future : Future machine.state after.state := by
    constructor
    · change machine.state.refs.length ≤ (numberHeap (image.count + 1) image.cleanups image.completed).length
      rw [priorHeap]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  have own : countedImage.count = countedImage.cleanups.length + 1 := by
    change image.count + 1 = image.cleanups.length + 1
    rw [cleanupComplete]
  have count : countedImage.count = n.val + 1 := by change image.count + 1 = n.val + 1; rw [cursor]
  refine ⟨.unit countedImage, CodeAt.success _ .unit ⟨heap, rfl⟩, ?_⟩
  exact .cons (count_saved view after.state countedImage captured fuel delay n error count)
    (.cons (attempt_saved view after.state countedImage own captured fuel delay n error count _)
      (AnswerFlow.stack_mono (model view) (interpreter view).toPrimInterp future stack))

/-- The actual counted machine stores exactly the fiber produced by the checked source prefix. -/
theorem counted_lookup (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (captured : Point) (fuel delay count : Nat) (n : Fin 4) (error : Val)
    (cleanups completed : List Val) (found : machine.fiber? fiber.id = some fiber) :
    (countedMachine machine fiber captured fuel delay count n error cleanups completed).fiber? fiber.id =
      some (countedFiber fiber captured fuel delay n error) := by
  let point := attemptPoint captured fuel delay n error
  let sync : NCode := .sync (.op (.refUpdate ⟨0⟩ countTerm point.env))
  let body : NCode := .onSuccess sync (.cont (point.child 0))
  let first := exitPushed fiber body (.fin point)
  let one := (machine.emit [.frame fiber.id (.pushed (.onExit body (.fin point) false))]).update first
  let second := successPushed first sync (.cont (point.child 0))
  let two := (one.emit [.frame first.id (.pushed (.onSuccess sync (.cont (point.child 0))))]).update second
  have firstFound : one.fiber? first.id = some first :=
    RunMachine.fiber?_update_self first _ ⟨fiber, List.mem_of_find?_eq_some found, rfl⟩
  have secondFound : two.fiber? second.id = some second :=
    RunMachine.fiber?_update_self second _ ⟨first, List.mem_of_find?_eq_some firstFound, rfl⟩
  exact RunMachine.fiber?_update_self (countedFiber fiber captured fuel delay n error) _
    ⟨second, List.mem_of_find?_eq_some secondFound, rfl⟩

/-- The actual three-command count prefix produces a stored numeric frame with its real saved suffix. -/
theorem count_prefix_typed (view : View) (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (image : Image) (n : Fin 4) (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
    (captured : Point) (fuel delay : Nat) (error : Val) (output : HostTimeoutNumberFlow.Kind)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (live : machine.stuck = none) (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = resolve HostTimeoutSource.program (attemptPoint captured (fuel + 1) delay n error))
    (heap : ImageAt image machine.state)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 3 < fiber.maxOpsBeforeYield)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor))
        (by change image.count + 1 = image.cleanups.length + 1; rw [cleanupComplete]))
      output fiber.frame.stack) :
    ∃ after counted,
      driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 3 machine
        (.loop fiber.id false :: rest) = (after, [.drainDue, .deliver fiber.id false] ++ rest) ∧
      after.fiber? fiber.id = some counted ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp
        after.state output counted.frame ∧
      ImageAt (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)) after.state := by
  refine ⟨countedMachine machine fiber captured (fuel + 1) delay image.count n error image.cleanups image.completed,
    countedFiber fiber captured (fuel + 1) delay n error, ?_, ?_, ?_, rfl⟩
  · exact count_prefix_exact machine fiber captured (fuel + 1) delay image.count n error image.cleanups image.completed
      rest live found current heap interrupt override budget
  · exact counted_lookup machine fiber captured (fuel + 1) delay image.count n error image.cleanups image.completed found
  · exact counted_frame view machine fiber image n cleanupComplete formComplete cursor
      captured fuel delay error output heap stack

/-- The actual evaluate command resets the counter and produces the committed numeric frame in four commands. -/
theorem count_entry_typed (view : View) (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (image : Image) (n : Fin 4) (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
    (captured : Point) (fuel delay : Nat) (error : Val) (output : HostTimeoutNumberFlow.Kind)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (live : machine.stuck = none) (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = resolve HostTimeoutSource.program (attemptPoint captured (fuel + 1) delay n error))
    (heap : ImageAt image machine.state)
    (idle : fiber.running = false) (parked : fiber.parked = .notParked) (unfinished : fiber.exit = none)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : 3 < fiber.maxOpsBeforeYield)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor))
        (by change image.count + 1 = image.cleanups.length + 1; rw [cleanupComplete]))
      output fiber.frame.stack) :
    ∃ after counted,
      driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 4 machine
        (.evaluate fiber.id :: rest) = (after, [.drainDue, .deliver fiber.id false] ++ rest) ∧
      after.fiber? fiber.id = some counted ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp
        after.state output counted.frame ∧
      ImageAt (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)) after.state := by
  letI := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table
  let entered : NativeFiber := {fiber with running := true, currentOpCount := 0}
  let started := (machine.update entered).emit [.started fiber.id]
  have selected : started.fiber? entered.id = some entered := by
    rw [RunMachine.fiber?_emit]
    exact RunMachine.fiber?_update_self entered machine
      ⟨fiber, List.mem_of_find?_eq_some found, rfl⟩
  obtain ⟨after, counted, prefixDone, held, typed, stored⟩ := count_prefix_typed view started entered
    image n cleanupComplete formComplete cursor captured fuel delay error output rest
    live selected current heap interrupt override budget stack
  refine ⟨after, counted, ?_, held, typed, stored⟩
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

/-- The original fixed budget exposes the numeric frame only after the checked pre-count source chain finishes. -/
theorem count_entry_budget_typed (view : View) (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (image : Image) (n : Fin 4) (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
    (captured : Point) (fuel delay : Nat) (error : Val) (output : HostTimeoutNumberFlow.Kind)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (live : machine.stuck = none) (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = resolve HostTimeoutSource.program (attemptPoint captured (fuel + 1) delay n error))
    (heap : ImageAt image machine.state)
    (idle : fiber.running = false) (parked : fiber.parked = .notParked) (unfinished : fiber.exit = none)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : 3 < fiber.maxOpsBeforeYield)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor))
        (by change image.count + 1 = image.cleanups.length + 1; rw [cleanupComplete]))
      output fiber.frame.stack) :
    ∃ after counted,
      driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) Scenario.Timeout.budget.fuel machine
        (.evaluate fiber.id :: rest) =
        driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
          (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) 1996 after
          ([.drainDue, .deliver fiber.id false] ++ rest) ∧
      after.fiber? fiber.id = some counted ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp
        after.state output counted.frame ∧
      ImageAt (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)) after.state := by
  letI := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table
  obtain ⟨after, counted, prefixDone, held, typed, stored⟩ := count_entry_typed view machine fiber
    image n cleanupComplete formComplete cursor captured fuel delay error output rest live found current heap
    idle parked unfinished interrupt override budget stack
  refine ⟨after, counted, ?_, held, typed, stored⟩
  change driveState (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) (4 + 1996)
    machine (.evaluate fiber.id :: rest) = _
  rw [driveState_add _ 4 1996, prefixDone]

end Test.Dogfood.Proofs.HostTimeoutNumberCounted

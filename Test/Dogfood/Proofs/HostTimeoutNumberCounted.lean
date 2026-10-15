import Test.Dogfood.Proofs.HostTimeoutNumberFinalizers
import Effect4.Laws.Program.StackRegionRun

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
  image.enter n cleanupComplete formComplete cursor

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

/-- The source count binder has its post-count class before its synchronous write runs. -/
theorem count_bind_push (view : View) (state : Stores) (image : Image) (n : Fin 4)
    (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
    (captured : Point) (fuel delay : Nat) (error : Val) (heap : ImageAt image state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.current = resolve HostTimeoutSource.program
      ((attemptPoint captured (fuel + 1) delay n error).child 0))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.at (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor))) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  let entered := nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)
  have count : entered.count = n.val + 1 := by
    change image.count + 1 = n.val + 1
    rw [cursor]
  have code : resolve HostTimeoutSource.program
      ((attemptPoint captured (fuel + 1) delay n error).child 0) =
      .onSuccess (.sync (.op (.refUpdate ⟨0⟩ countTerm
        (attemptPoint captured (fuel + 1) delay n error).env)))
        (.cont ((attemptPoint captured (fuel + 1) delay n error).child 0)) := by kernel_rfl
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.unit entered) (.at entered) output fiber _ _ (current.trans code)
    (CodeAt.count image n cleanupComplete formComplete cursor captured fuel delay error heap)
    (count_saved view state entered captured fuel delay n error count) stack

/-- Installing the attempt's finalizer requires no fabricated post-count heap before the count runs. -/
theorem count_exit_push (view : View) (state : Stores) (image : Image) (n : Fin 4)
    (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
    (captured : Point) (fuel delay : Nat) (error : Val) (heap : ImageAt image state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.current = resolve HostTimeoutSource.program
      (attemptPoint captured (fuel + 1) delay n error))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor))
        (by change image.count + 1 = image.cleanups.length + 1; rw [cleanupComplete])) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  let point := attemptPoint captured (fuel + 1) delay n error
  let entered := nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)
  have own : entered.count = entered.cleanups.length + 1 := by
    change image.count + 1 = image.cleanups.length + 1
    rw [cleanupComplete]
  have count : entered.count = n.val + 1 := by
    change image.count + 1 = n.val + 1
    rw [cursor]
  let body := resolve HostTimeoutSource.program (point.child 0)
  have code : resolve HostTimeoutSource.program point = .onExit body (.fin point) false := by
    kernel_rfl
  refine ⟨{fiber with current := body, stack := .onExit body (.fin point) false :: fiber.stack},
    [.pushed (.onExit body (.fin point) false)], ?_, .at entered,
    CodeAt.countBind image n cleanupComplete formComplete cursor captured fuel delay error heap,
    .cons (attempt_saved view state entered own captured fuel delay n error count body) stack⟩
  simp only [FrameFiber.step, show fiber.current = .onExit body (.fin point) false from current.trans code]

/-- The actual synchronous count establishes the post-count class saved by the two pushes. -/
theorem count_native_write (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : NativeFiber) (yielding : Bool) (image : Image) (n : Fin 4)
    (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
    (captured : Point) (fuel delay : Nat) (error : Val) (heap : ImageAt image machine.state)
    (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.frame.current = .sync (.op (.refUpdate ⟨0⟩ countTerm
      (attemptPoint captured (fuel + 1) delay n error).env)))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.unit (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor))) output fiber.frame.stack) :
    let entered := nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)
    let next := {machine.state with refs := entered.heap}
    evaluateNative HostTimeoutSource.program machine fiber yielding Test.Dogfood.Scenario.Timeout.fetch.table =
      ⟨{machine with state := next}, {fiber with frame := {fiber.frame with current := .success .unit}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp next output
        {fiber.frame with current := .success .unit} := by
  dsimp only
  let entered := nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)
  let operation := SyncOp.refUpdate ⟨0⟩ countTerm
    (attemptPoint captured (fuel + 1) delay n error).env
  have overwrite : {machine.state with refs := image.heap} = machine.state := by
    rw [show image.heap = machine.state.refs from heap.symm]
  have step := count_sync machine.state image.count delay n error image.cleanups image.completed
  change syncOpStep operation {machine.state with refs := image.heap} =
    some ({machine.state with refs := entered.heap}, .unit) at step
  rw [overwrite] at step
  have future : Future machine.state {machine.state with refs := entered.heap} := by
    constructor
    · change machine.state.refs.length ≤ 3
      rw [heap]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  exact ControlSteps.native_sync_answer HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    machine fiber yielding operation _ .unit id (model view) (interpreter view).toPrimInterp
    (.unit entered) output current step future ⟨rfl, rfl⟩ stack

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

/-- The attempt's exact saved onExit forms the entry suffix after the committed source count.
Consumer: the numeric region producer follows the callback above that suffix. -/
def attemptRegion (fiber : NativeFiber) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (error : Val) : List NCode :=
  let point := attemptPoint captured fuel delay n error
  let sync : NCode := .sync (.op (.refUpdate ⟨0⟩ countTerm point.env))
  .onExit (.onSuccess sync (.cont (point.child 0))) (.fin point) false :: fiber.frame.stack

/-- The checked count prefix establishes its numeric frame and actual finalizer region entry.
The remaining budget follows the shared region law up to its explicit detached-exit boundary.
This supplies no post-prefix heap preservation or reached history without those operation laws. -/
theorem count_prefix_region (view : View) (machine : Effect4.Program.NativeMachine) (fiber : NativeFiber)
    (image : Image) (n : Fin 4) (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
    (captured : Point) (fuel delay : Nat) (error : Val) (output : HostTimeoutNumberFlow.Kind)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    {bases : List Bool} (entry : LoopCut HostTimeoutSource.program Scenario.Timeout.fetch.table bases machine
      (.loop fiber.id false :: rest))
    (live : machine.stuck = none) (found : machine.fiber? fiber.id = some fiber)
    (current : fiber.frame.current = resolve HostTimeoutSource.program (attemptPoint captured (fuel + 1) delay n error))
    (heap : ImageAt image machine.state)
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 3 < fiber.maxOpsBeforeYield)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit (nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor))
        (by change image.count + 1 = image.cleanups.length + 1; rw [cleanupComplete]))
      output fiber.frame.stack)
    (remaining : Nat)
    (permitted : Lift.PrefixAllows (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
      (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table)
      (fun next head _ => StackRegion.Continues HostTimeoutSource.program Scenario.Timeout.fetch.table
        (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) fiber.id
        (attemptRegion fiber captured (fuel + 1) delay n error) next head) remaining
      (countedMachine machine fiber captured (fuel + 1) delay image.count n error image.cleanups image.completed)
      ([.drainDue, .deliver fiber.id false] ++ rest)) :
    let entered := countedMachine machine fiber captured (fuel + 1) delay image.count n error image.cleanups image.completed
    let counted := countedFiber fiber captured (fuel + 1) delay n error
    let next := nextImage image n cleanupComplete formComplete (Nat.le_of_eq cursor)
    let out := driveState (evaluator := evaluatorFor HostTimeoutSource.program Scenario.Timeout.fetch.table)
      (interpOf HostTimeoutSource.program Scenario.Timeout.fetch.table) (3 + remaining) machine (.loop fiber.id false :: rest)
    ImageAt next entered.state ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp entered.state output counted.frame ∧
      StackRegion.Held fiber.id (attemptRegion fiber captured (fuel + 1) delay n error) out.1 ∧
      ∃ laterBases, bases <+: laterBases ∧ LoopCut HostTimeoutSource.program Scenario.Timeout.fetch.table laterBases out.1 out.2 := by
  dsimp only
  have ran := count_prefix_exact machine fiber captured (fuel + 1) delay image.count n error
    image.cleanups image.completed rest live found current heap interrupt override budget
  have stored := counted_lookup machine fiber captured (fuel + 1) delay image.count n error
    image.cleanups image.completed found
  have inside : StackRegion.Inside (attemptRegion fiber captured (fuel + 1) delay n error)
      (countedFiber fiber captured (fuel + 1) delay n error) := by
    exact ⟨[.onSuccess (.sync (.op (.refUpdate ⟨0⟩ countTerm
      (attemptPoint captured (fuel + 1) delay n error).env)))
      (.cont ((attemptPoint captured (fuel + 1) delay n error).child 0))], rfl⟩
  have region := StackRegion.drive_from_prefix HostTimeoutSource.program Scenario.Timeout.fetch.table
    machine (.loop fiber.id false :: rest) 3 remaining _ _ entry ran fiber.id _ stored _ inside permitted
  exact ⟨rfl, counted_frame view machine fiber image n cleanupComplete formComplete cursor
    captured fuel delay error output heap stack, region.1, region.2⟩

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

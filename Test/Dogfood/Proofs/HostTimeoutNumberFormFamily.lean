import Test.Dogfood.Proofs.HostTimeoutNumberCounted
import Effect4.Laws.Machine.AnswerFlowCausePop

/-!
Placement: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the root's pre-race saved form finalizer of Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: race cleanup publication and the original numeric history assertion.
The saved class retains the actual attempt cleanup without choosing its interruption flag before the race settles.
It then retains the exact selected exit published by the real source form finalizer.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberFormFamily
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberSteps HostTimeoutNumberState
open HostTimeoutNumberCallbacks HostTimeoutNumberFlow HostTimeoutNumberFinalizers HostTimeoutNumberCounted

/-- The real finalizer wrapper records an already completed attempt cleanup and its own selected exit. -/
theorem wrapped_code (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (attemptExit selected : ExitV) (program : NCode)
    (cleanup : CodeAt state (.unit (image.afterForm own attemptExit selected)) program) :
    CodeAt state (.formAfterCleanup image own) (finalizerCode (interpreter view) selected program) := by
  cases selected with
  | success value => exact CodeAt.formFamilyReturn image own attemptExit _ program cleanup
  | failure cause => exact CodeAt.formFamilyReturn image own attemptExit _ _ (CodeAt.merge _ _ program cleanup)

/-- Restoring a selected form exit retains the actual published exit in the current numeric heap. -/
theorem restore_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (attemptExit selected : ExitV) (program : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.afterForm own attemptExit selected)) (.formAfterCleanup image own)
      (.onSuccess program (.restore selected)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    have heap : ImageAt (image.afterForm own attemptExit selected) next := good.1
    cases selected with
    | success saved => exact CodeAt.success _ saved ⟨attemptExit, .success saved, heap, rfl⟩
    | failure saved => exact CodeAt.failure _ saved ⟨attemptExit, .failure saved, heap, Or.inl rfl⟩
  · intro next future cause good
    exact False.elim good

/-- The actual restore push retains the source form's selected exit after its published heap write. -/
theorem restore_push (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (attemptExit selected : ExitV) (program : NCode)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.current = .onSuccess program (.restore selected))
    (body : CodeAt state (.unit (image.afterForm own attemptExit selected)) program)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.formAfterCleanup image own) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.unit (image.afterForm own attemptExit selected)) (.formAfterCleanup image own) output fiber program (.restore selected)
    current body (restore_saved view state image own attemptExit selected program) stack

/-- The root saves its form finalizer before the race chooses either exit.
Its callback consumes the actual completed attempt-cleanup image rather than predicting that exit. -/
theorem form_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
    (count : image.count = n.val + 1) (body : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) (.formAfterCleanup image own)
      (.onExit body (.fin (formPoint captured fuel delay n error)) false) := by
  refine AnswerFlow.SavedAt.mk state (HostTimeoutNumberFlow.Kind.cleanupExit image own)
    (HostTimeoutNumberFlow.Kind.formAfterCleanup image own) _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro next future value good absent
    cases absent
  · intro next future cause good absent
    cases absent
  · intro next future value provided nextCode pushed good supplied noProgram arm
    change (((interpreter view).finalizerProgram (.fin (formPoint captured fuel delay n error))
      (provided.getD (.success value))).map
        (finalizerCode (interpreter view) (provided.getD (.success value)))) = none at noProgram
    rw [form_program, Option.map_some] at noProgram
    cases noProgram
  · intro next future cause provided nextCode pushed good supplied noProgram arm
    change (((interpreter view).finalizerProgram (.fin (formPoint captured fuel delay n error))
      (provided.getD (.failure cause))).map
        (finalizerCode (interpreter view) (provided.getD (.failure cause)))) = none at noProgram
    rw [form_program, Option.map_some] at noProgram
    cases noProgram
  · intro next future selected nextCode good installed
    have prior : ∃ attemptExit, ImageAt (image.cleanup own attemptExit) next := by
      cases selected <;> exact good
    obtain ⟨attemptExit, heap⟩ := prior
    have program : (model view).finalizer next (.fin (formPoint captured fuel delay n error)) selected =
        some (finalizerCode (interpreter view) selected
          (resolve HostTimeoutSource.program
            (completedPoint {captured with completed := view} fuel delay n error selected))) := by
      change (((interpreter view).finalizerProgram (.fin (formPoint captured fuel delay n error)) selected).map
        (finalizerCode (interpreter view) selected)) = _
      rw [form_program, Option.map_some]
    have exactCode := Option.some.inj (program.symm.trans installed)
    rw [← exactCode]
    exact wrapped_code view next image own attemptExit selected _
      (CodeAt.completed (image.cleanup own attemptExit) (image.cleanup_complete own attemptExit)
        (image.form_gap own) {captured with completed := view} fuel delay n error selected count heap)
  · intro next future fiber cause delivered good arm interrupted skipped
    rw [AnswerFlow.ensure_protected_not_interrupted] at interrupted
    cases interrupted

/-- Actual native installation consumes the selected exit only after its attempt cleanup completes. -/
theorem install (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
    (count : image.count = n.val + 1) (body : NCode) (selected : ExitV)
    (good : AnswerFlow.ExitAt (model view) state (.cleanupExit image own) selected)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.formAfterCleanup image own) output fiber.stack) :
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output
      {((Prim.onExit body (.fin (formPoint captured fuel delay n error)) false).ensure fiber).1 with
        current := (finalizerCode (interpreter view) selected
          (resolve HostTimeoutSource.program
            (completedPoint {captured with completed := view} fuel delay n error selected)))} := by
  apply AnswerFlow.install_finalizer_after_ensure (model view) (interpreter view).toPrimInterp state
    (.cleanupExit image own) (.formAfterCleanup image own) output fiber body
    (.fin (formPoint captured fuel delay n error)) false selected _ good
    (form_saved view state image own captured fuel delay n error count body) ?_ stack
  change (((interpreter view).finalizerProgram (.fin (formPoint captured fuel delay n error)) selected).map
    (finalizerCode (interpreter view) selected)) = _
  rw [form_program, Option.map_some]

/-- The real native successful form exit follows actual selected-frame pop and finalizer-program installation. -/
theorem native_success (machine : Effect4.Program.NativeMachine) (fiber : HostTimeoutEvaluation.NativeFiber)
    (yielding : Bool) (input output : HostTimeoutNumberFlow.Kind) (value : Val)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (body : NCode)
    (current : fiber.frame.current = .success value)
    (good : ValueAt machine.state input value)
    (stack : AnswerFlow.StackAt (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp
      machine.state input output fiber.frame.stack)
    (chosen : (fiber.frame.getCont .contA false).answer =
      .frame (.onExit body (.fin (formPoint captured fuel delay n error)) false)) :
    let result := evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table
    result.machine.state = machine.state ∧
      AnswerFlow.FrameAt (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp
        result.machine.state output result.fiber.frame := by
  dsimp only
  have dispatch : evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table =
      evaluatePrim.finalizerOr (interpreter machine.completedExits) machine fiber yielding (.success value) := by
    rw [evaluateNative, current]
    unfold exitScoped
    dsimp only
    rw [chosen]
    rw [HostTimeoutEvaluation.evaluate_table_free]
    rw [evaluatePrim, current]
    rfl
  rw [dispatch]
  let program := resolve HostTimeoutSource.program
    (completedPoint {captured with completed := machine.completedExits} fuel delay n error (.success value))
  have installed : (model machine.completedExits).finalizer machine.state
      (.fin (formPoint captured fuel delay n error)) (.success value) =
      some (finalizerCode (interpreter machine.completedExits) (.success value) program) := by
    change (((interpreter machine.completedExits).finalizerProgram
      (.fin (formPoint captured fuel delay n error)) (.success value)).map
      (finalizerCode (interpreter machine.completedExits) (.success value))) = _
    rw [form_program, Option.map_some]
  have projected := AnswerFlow.External.finalizer_step (model machine.completedExits)
    (interpreter machine.completedExits).toPrimInterp
    (AnswerFlow.SavedAt (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp)
    (AnswerFlow.saved_family (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp)
    (fun state kind => AnswerFlow.saved_mask (model machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp state kind true)
    (interpreter machine.completedExits) machine.state input output machine fiber yielding (.success value)
    body (.fin (formPoint captured fuel delay n error)) false program good
    (AnswerFlow.stack_path (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp stack)
    chosen (form_program machine.completedExits captured fuel delay n error _) installed
  obtain ⟨stateKept, head, code, path⟩ := projected
  refine ⟨stateKept, ?_⟩
  rw [stateKept]
  exact ⟨head, code, AnswerFlow.path_stack (model machine.completedExits)
    (interpreter machine.completedExits).toPrimInterp path⟩

/-- The real native failed form exit publishes the delivered cause after actual interrupted-handler selection. -/
theorem native_failure (machine : Effect4.Program.NativeMachine) (fiber : HostTimeoutEvaluation.NativeFiber)
    (yielding : Bool) (input output : HostTimeoutNumberFlow.Kind) (cause : CauseV)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (body : NCode)
    (current : fiber.frame.current = .failure cause)
    (good : CauseAt machine.state input cause)
    (stack : AnswerFlow.StackAt (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp
      machine.state input output fiber.frame.stack)
    (chosen : (fiber.frame.getCont .contE true (some cause)).answer =
      .frame (.onExit body (.fin (formPoint captured fuel delay n error)) false)) :
    let result := evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table
    result.machine.state = machine.state ∧
      AnswerFlow.FrameAt (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp
        result.machine.state output result.fiber.frame := by
  dsimp only
  have dispatch : evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table =
      evaluatePrim.finalizerOr (interpreter machine.completedExits) machine fiber yielding (.failure cause) := by
    rw [evaluateNative, current]
    unfold exitScoped
    dsimp only
    rw [chosen]
    rw [HostTimeoutEvaluation.evaluate_table_free]
    rw [evaluatePrim, current]
    rfl
  rw [dispatch]
  let selected := (fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)
  let program := resolve HostTimeoutSource.program
    (completedPoint {captured with completed := machine.completedExits} fuel delay n error selected)
  have installed : (model machine.completedExits).finalizer machine.state
      (.fin (formPoint captured fuel delay n error)) selected =
      some (finalizerCode (interpreter machine.completedExits) selected program) := by
    change (((interpreter machine.completedExits).finalizerProgram
      (.fin (formPoint captured fuel delay n error)) selected).map
      (finalizerCode (interpreter machine.completedExits) selected)) = _
    rw [form_program, Option.map_some]
  have projected := AnswerFlow.External.finalizer_step (model machine.completedExits)
    (interpreter machine.completedExits).toPrimInterp
    (AnswerFlow.SavedAt (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp)
    (AnswerFlow.saved_family (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp)
    (fun state kind => AnswerFlow.saved_mask (model machine.completedExits)
      (interpreter machine.completedExits).toPrimInterp state kind true)
    (interpreter machine.completedExits) machine.state input output machine fiber yielding (.failure cause)
    body (.fin (formPoint captured fuel delay n error)) false program good
    (AnswerFlow.stack_path (model machine.completedExits) (interpreter machine.completedExits).toPrimInterp stack)
    chosen (form_program machine.completedExits captured fuel delay n error _) installed
  obtain ⟨stateKept, head, code, path⟩ := projected
  refine ⟨stateKept, ?_⟩
  rw [stateKept]
  exact ⟨head, code, AnswerFlow.path_stack (model machine.completedExits)
    (interpreter machine.completedExits).toPrimInterp path⟩

/-- A handled typed failure comes from the actual form entry already written in the numeric heap. -/
theorem caught_is_published (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (cause : CauseV)
    (good : CauseAt state (.formAfterCleanup image own) cause)
    (env : List Val) (test : Term) (error : Val)
    (handled : caughtErrorValue? env test cause = some error) :
    ∃ attemptExit, ImageAt (image.afterForm own attemptExit (.failure cause)) state := by
  obtain ⟨attemptExit, saved, heap, exactExit | interrupted⟩ := good
  · rw [exactExit] at heap
    exact ⟨attemptExit, heap⟩
  · have refused := no_typed_test env test cause interrupted
    rw [refused] at handled
    cases handled

/-- The real singleton-failure catch test uses the exact declared completed-form predicate. -/
theorem caught_singleton_declared (n : Fin 4) (delay : Nat) (previous : Val)
    (tag message : String) (annotations : ReasonAnnotations Ann) (value : Val)
    (handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest {reasons := [.fail (.tagged tag message) annotations]} = some value) :
    HostTimeoutNumberLedger.exitRetries (.failure {reasons := [.fail (.tagged tag message) annotations]}) = true := by
  have first : firstErrorValue? {reasons := [.fail (.tagged tag message) annotations]} =
      some (.list [.str tag, .str message]) := rfl
  unfold caughtErrorValue? at handled
  rw [first] at handled
  change (if evalTerm
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous ++ [.list [.str tag, .str message]])
      HostTimeoutSource.retryTest = some (.bool true) then some (.list [.str tag, .str message]) else none) =
      some value at handled
  have evaluates := HostTimeoutSource.retry_test_evaluates (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩)
    previous n.val delay tag message
  change evalTerm
    (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous ++ [.list [.str tag, .str message]])
    HostTimeoutSource.retryTest = some (.bool (HostTimeoutSource.declared tag message)) at evaluates
  rw [evaluates] at handled
  have declared : HostTimeoutSource.declared tag message = true := by
    split at handled
    · rename_i accepted
      have equal := Option.some.inj accepted
      cases bit : HostTimeoutSource.declared tag message with
      | false => rw [bit] at equal; cases equal
      | true => rfl
    · cases handled
  change ((tag == "NetworkError") || (tag == "Timeout") || (message == "503")) = true
  rw [Bool.or_assoc]
  exact declared

/-- An actual handled singleton failure binds the published exit and its declared retry test together. -/
theorem handled_published (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (n : Fin 4) (delay : Nat) (previous : Val)
    (tag message : String) (annotations : ReasonAnnotations Ann) (value : Val)
    (good : CauseAt state (.formAfterCleanup image own) {reasons := [.fail (.tagged tag message) annotations]})
    (handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest {reasons := [.fail (.tagged tag message) annotations]} = some value) :
    ∃ attemptExit,
      ImageAt (image.afterForm own attemptExit (.failure {reasons := [.fail (.tagged tag message) annotations]})) state ∧
      HostTimeoutNumberLedger.exitRetries (.failure {reasons := [.fail (.tagged tag message) annotations]}) = true := by
  obtain ⟨attemptExit, heap⟩ := caught_is_published state image own _ good _ _ value handled
  exact ⟨attemptExit, heap, caught_singleton_declared n delay previous tag message annotations value handled⟩

/-- Publishing the selected declared failure extends the exact completed predecessor prefix. -/
theorem declared_published (image : Image) (own : image.count = image.cleanups.length + 1)
    (attemptExit selected : ExitV) (before : Declared image.count image.exits)
    (returned : HostTimeoutNumberLedger.exitRetries selected = true) :
    (image.afterForm own attemptExit selected).exits.all HostTimeoutNumberLedger.exitRetries = true := by
  have complete := image.form_gap own
  have old : image.exits.all HostTimeoutNumberLedger.exitRetries = true := by
    unfold Declared at before
    rw [← complete, Nat.add_sub_cancel, List.take_length] at before
    exact before
  change (image.exits ++ [selected]).all HostTimeoutNumberLedger.exitRetries = true
  rw [List.all_append, old]
  change (true && (HostTimeoutNumberLedger.exitRetries selected && true)) = true
  rw [returned]
  rfl

/-- The next attempt's declared-prefix assertion consumes only a completed selected form result. -/
theorem next_declared (image : Image) (own : image.count = image.cleanups.length + 1)
    (attemptExit selected : ExitV) (before : Declared image.count image.exits)
    (returned : HostTimeoutNumberLedger.exitRetries selected = true) :
    Declared (image.count + 1) (image.afterForm own attemptExit selected).exits := by
  apply count_declared image.count (image.afterForm own attemptExit selected).exits
  · change (image.exits ++ [selected]).length = image.count
    rw [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    exact image.form_gap own
  · exact declared_published image own attemptExit selected before returned

end Test.Dogfood.Proofs.HostTimeoutNumberFormFamily

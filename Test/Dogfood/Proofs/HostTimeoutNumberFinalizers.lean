import Test.Dogfood.Proofs.HostTimeoutNumberFlow
import Effect4.Laws.Machine.AnswerFlowHooks

/-!
Placement: scope-lifetime-finalization R11 and translation-simulation R10.
Question: actual saved source finalizers of Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: the numeric frame contract over the original timeout command history.
A fixed saved-stack class retains the heap after dynamically captured cleanup or form exits.
The source and heap premises remain conditional until the command producers establish them.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberFinalizers
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberSteps HostTimeoutNumberState
open HostTimeoutNumberCallbacks HostTimeoutNumberFlow

/-- The existing timeout-form point captures the retry cursor and exact allocated handles. -/
def formPoint (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) : Point :=
  {captured with
    path := [1,1,1,0,0,1,0,0]
    env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error
    fuel := fuel + 3}

/-- The actual attempt finalizer resolves precisely its captured cleanup binder. -/
theorem attempt_program (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (error : Val) (exit : ExitV) :
    (interpreter view).finalizerProgram
      (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error)) exit =
      some (resolve HostTimeoutSource.program (cleanupPoint {captured with completed := view} fuel delay n error exit)) := by
  kernel_rfl

/-- The actual form finalizer resolves precisely its captured completed-outcome binder. -/
theorem form_program (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (error : Val) (exit : ExitV) :
    (interpreter view).finalizerProgram (.fin (formPoint captured fuel delay n error)) exit =
      some (resolve HostTimeoutSource.program (completedPoint {captured with completed := view} fuel delay n error exit)) := by
  kernel_rfl

/-- The native failure wrapper preserves the cleanup unit class; no cleanup failure is admitted here. -/
theorem merge_saved (view : View) (state : Stores) (image : Image) (exit : ExitV) (program : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.unit image) (.unit image)
      (.onFailure program (.merge exit)) := by
  apply AnswerFlow.saved_failure
  · intro next future value good
    exact good
  · intro next future cause good
    exact False.elim good
  · intro next future fiber cause delivered good interrupted skipped
    exact False.elim good

/-- The actual source cleanup wrapper keeps a fixed stack class while restoring its captured exit. -/
theorem cleanup_finalizer_code (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (exit : ExitV) (program : NCode)
    (cleanup : CodeAt state (.unit (image.cleanup own exit)) program) :
    CodeAt state (.cleanupExit image own) (finalizerCode (interpreter view) exit program) := by
  cases exit with
  | success value => exact CodeAt.cleanupReturn image own _ program cleanup
  | failure cause => exact CodeAt.cleanupReturn image own _ _ (CodeAt.merge _ _ program cleanup)

/-- The actual completed-form wrapper restores the exact exit recorded in the form log. -/
theorem form_finalizer_code (view : View) (state : Stores) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (exit : ExitV) (program : NCode)
    (cleanup : CodeAt state (.unit (image.form cleanupComplete own exit)) program) :
    CodeAt state (.formExit image cleanupComplete own) (finalizerCode (interpreter view) exit program) := by
  cases exit with
  | success value => exact CodeAt.formReturn image cleanupComplete own _ program cleanup
  | failure cause => exact CodeAt.formReturn image cleanupComplete own _ _ (CodeAt.merge _ _ program cleanup)

/-- An attempt restore consumes its captured post-cleanup image in every permitted future store. -/
theorem cleanup_restore_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (exit : ExitV) (program : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.cleanup own exit)) (.cleanupExit image own) (.onSuccess program (.restore exit)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    have heap : ImageAt (image.cleanup own exit) next := good.1
    cases exit with
    | success saved => exact CodeAt.success _ saved ⟨.success saved, heap⟩
    | failure saved => exact CodeAt.failure _ saved ⟨.failure saved, heap⟩
  · intro next future cause good
    exact False.elim good

/-- A form restore consumes the exact published exit in every permitted future store. -/
theorem form_restore_saved (view : View) (state : Stores) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (exit : ExitV) (program : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.form cleanupComplete own exit)) (.formExit image cleanupComplete own)
      (.onSuccess program (.restore exit)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    have heap : ImageAt (image.form cleanupComplete own exit) next := good.1
    cases exit with
    | success saved => exact CodeAt.success _ saved ⟨.success saved, heap, rfl⟩
    | failure saved => exact CodeAt.failure _ saved ⟨.failure saved, heap, Or.inl rfl⟩
  · intro next future cause good
    exact False.elim good

/-- The native cleanup restore push consumes the committed-cleanup callback and its actual older suffix. -/
theorem cleanup_restore_push (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (exit : ExitV) (program : NCode)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.current = .onSuccess program (.restore exit))
    (body : CodeAt state (.unit (image.cleanup own exit)) program)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.unit (image.cleanup own exit)) (.cleanupExit image own) output fiber program (.restore exit)
    current body (cleanup_restore_saved view state image own exit program) stack

/-- The native form restore push consumes the exact published-exit callback and its actual older suffix. -/
theorem form_restore_push (view : View) (state : Stores) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (exit : ExitV) (program : NCode) (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.current = .onSuccess program (.restore exit))
    (body : CodeAt state (.unit (image.form cleanupComplete own exit)) program)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.formExit image cleanupComplete own) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.unit (image.form cleanupComplete own exit)) (.formExit image cleanupComplete own) output fiber program (.restore exit)
    current body (form_restore_saved view state image cleanupComplete own exit program) stack

/-- The native cleanup failure wrapper retains the actual unit code and ordered saved suffix. -/
theorem merge_push (view : View) (state : Stores) (image : Image) (exit : ExitV)
    (program : NCode) (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.current = .onFailure program (.merge exit))
    (body : CodeAt state (.unit image) program)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state (.unit image) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  exact AnswerFlow.push_failure (model view) (interpreter view).toPrimInterp state
    (.unit image) (.unit image) output fiber program (.merge exit) current body
    (merge_saved view state image exit program) stack

/-- The actual saved attempt finalizer consumes only its committed active-attempt heap. -/
theorem attempt_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
    (count : image.count = n.val + 1) (body : NCode) :
    let point := HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.at image) (.cleanupExit image own) (.onExit body (.fin point) false) := by
  dsimp only
  refine AnswerFlow.SavedAt.mk state (HostTimeoutNumberFlow.Kind.at image) (HostTimeoutNumberFlow.Kind.cleanupExit image own) _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro next future value good absent
    cases absent
  · intro next future cause good absent
    cases absent
  · intro next future value provided nextCode pushed good supplied noProgram arm
    change (((interpreter view).finalizerProgram
      (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error))
      (provided.getD (.success value))).map
        (finalizerCode (interpreter view) (provided.getD (.success value)))) = none at noProgram
    rw [attempt_program, Option.map_some] at noProgram
    cases noProgram
  · intro next future cause provided nextCode pushed good supplied noProgram arm
    change (((interpreter view).finalizerProgram
      (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error))
      (provided.getD (.failure cause))).map
        (finalizerCode (interpreter view) (provided.getD (.failure cause)))) = none at noProgram
    rw [attempt_program, Option.map_some] at noProgram
    cases noProgram
  · intro next future exit nextCode good installed
    have heap : ImageAt image next := by cases exit <;> exact good
    have program : (model view).finalizer next
        (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error)) exit =
        some (finalizerCode (interpreter view) exit
          (resolve HostTimeoutSource.program
            (cleanupPoint {captured with completed := view} fuel delay n error exit))) := by
      change (((interpreter view).finalizerProgram
        (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error)) exit).map
        (finalizerCode (interpreter view) exit)) = _
      rw [attempt_program, Option.map_some]
    have exactCode := Option.some.inj (program.symm.trans installed)
    rw [← exactCode]
    exact cleanup_finalizer_code view next image own exit _
      (CodeAt.cleanup image own {captured with completed := view} fuel delay n error exit count heap)
  · intro next future fiber cause delivered good arm interrupted skipped
    rw [AnswerFlow.ensure_protected_not_interrupted] at interrupted
    cases interrupted

/-- The actual saved form finalizer consumes only the completed attempt-cleanup heap. -/
theorem form_saved (view : View) (state : Stores) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
    (count : image.count = n.val + 1) (body : NCode) :
    let point := formPoint captured fuel delay n error
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.at image) (.formExit image cleanupComplete own) (.onExit body (.fin point) false) := by
  dsimp only
  refine AnswerFlow.SavedAt.mk state (HostTimeoutNumberFlow.Kind.at image) (HostTimeoutNumberFlow.Kind.formExit image cleanupComplete own) _ ?_ ?_ ?_ ?_ ?_ ?_
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
  · intro next future exit nextCode good installed
    have heap : ImageAt image next := by cases exit <;> exact good
    have program : (model view).finalizer next (.fin (formPoint captured fuel delay n error)) exit =
        some (finalizerCode (interpreter view) exit
          (resolve HostTimeoutSource.program
            (completedPoint {captured with completed := view} fuel delay n error exit))) := by
      change (((interpreter view).finalizerProgram
        (.fin (formPoint captured fuel delay n error)) exit).map
        (finalizerCode (interpreter view) exit)) = _
      rw [form_program, Option.map_some]
    have exactCode := Option.some.inj (program.symm.trans installed)
    rw [← exactCode]
    exact form_finalizer_code view next image cleanupComplete own exit _
      (CodeAt.completed image cleanupComplete own {captured with completed := view} fuel delay n error exit count heap)
  · intro next future fiber cause delivered good arm interrupted skipped
    rw [AnswerFlow.ensure_protected_not_interrupted] at interrupted
    cases interrupted

/-- Actual attempt finalizer installation applies its native mask hook to the real older stack. -/
theorem attempt_install (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
    (count : image.count = n.val + 1) (body : NCode) (exit : ExitV)
    (heap : ImageAt image state) (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) output fiber.stack) :
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output
      {((Prim.onExit body
        (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error)) false).ensure fiber).1 with
        current := (finalizerCode (interpreter view) exit
        (resolve HostTimeoutSource.program
          (cleanupPoint {captured with completed := view} fuel delay n error exit)))} := by
  have good : AnswerFlow.ExitAt (model view) state (.at image) exit := by cases exit <;> exact heap
  apply AnswerFlow.install_finalizer_after_ensure (model view) (interpreter view).toPrimInterp state
    (.at image) (.cleanupExit image own) output fiber body
    (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error)) false exit _
    good (attempt_saved view state image own captured fuel delay n error count body) ?_ stack
  change (((interpreter view).finalizerProgram
        (.fin (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error)) exit).map
        (finalizerCode (interpreter view) exit)) = _
  rw [attempt_program, Option.map_some]

/-- Actual form finalizer installation retains the selected exit through its native mask hook. -/
theorem form_install (view : View) (state : Stores) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
    (count : image.count = n.val + 1) (body : NCode) (exit : ExitV)
    (heap : ImageAt image state) (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.formExit image cleanupComplete own) output fiber.stack) :
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output
      {((Prim.onExit body (.fin (formPoint captured fuel delay n error)) false).ensure fiber).1 with
        current := (finalizerCode (interpreter view) exit
        (resolve HostTimeoutSource.program
          (completedPoint {captured with completed := view} fuel delay n error exit)))} := by
  have good : AnswerFlow.ExitAt (model view) state (.at image) exit := by cases exit <;> exact heap
  apply AnswerFlow.install_finalizer_after_ensure (model view) (interpreter view).toPrimInterp state
    (.at image) (.formExit image cleanupComplete own) output fiber body
    (.fin (formPoint captured fuel delay n error)) false exit _ good
    (form_saved view state image cleanupComplete own captured fuel delay n error count body) ?_ stack
  change (((interpreter view).finalizerProgram
        (.fin (formPoint captured fuel delay n error)) exit).map
        (finalizerCode (interpreter view) exit)) = _
  rw [form_program, Option.map_some]

end Test.Dogfood.Proofs.HostTimeoutNumberFinalizers

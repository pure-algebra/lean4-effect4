import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFlow

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Question: root cancellation control can retain its source form callback across numeric writes.
Consumer: the joint native and command producer of both Timeout numeric goals.
Reach: actual park, cancellation, restore, and rethrow control above the source form finalizer.
Limit: source entry, race membership, and callback selection remain producer obligations.
This control assertion does not establish an initialized or preserved history.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberRootControl
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberPhase HostTimeoutNumberPhaseFlow

/-- These root operations read no reference cell before the source form finalizer starts. -/
inductive ReadCode : NCode → Prop
  | success (value : Val) : ReadCode (.success value)
  | failure (cause : CauseV) : ReadCode (.failure cause)
  | park (kind : ParkKind) : ReadCode (.suspend (.park kind))
  | cancel (race : Nat) : ReadCode (.withFiber (.store (.act (.cancelRace race))))
  | maskedCancel (race : Nat) :
      ReadCode (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false))))
  | restore (body : NCode) (selected : ExitV) (held : ReadCode body) :
      ReadCode (.onSuccess body (.store (.restore selected)))
  | rethrow (body : NCode) (cause : CauseV) (held : ReadCode body) :
      ReadCode (.onSuccess body (.reFail cause))
  | yielding (priority : Nat) : ReadCode (.yieldNowWith priority)
  | constant (first body : NCode) (head : ReadCode first) (next : ReadCode body) :
      ReadCode (.onSuccessConst first body)

/-- The same actual root control accepts whichever numeric phase the writer just established. -/
theorem ReadCode.classified (code : NCode) (held : ReadCode code)
    (state : Stores) (phase : Phase) (heap : At phase state) : CodeAt state (.before phase) code := by
  induction held generalizing state phase with
  | success value => exact CodeAt.success _ value heap
  | failure cause => exact CodeAt.failure _ cause heap
  | park kind => exact CodeAt.park phase kind heap
  | cancel race => exact CodeAt.cancelRace phase race heap
  | maskedCancel race => exact CodeAt.maskedCancelRace phase race heap
  | restore body selected held ih =>
      apply CodeAt.bind (.before phase) (.before phase) body _ (ih state phase heap)
      · intro next future value good view
        cases selected with
        | success saved => exact CodeAt.success _ saved good
        | failure cause => exact CodeAt.failure _ cause good
      · intro next future cause good
        exact good
  | rethrow body cause held ih =>
      apply CodeAt.bind (.before phase) (.before phase) body _ (ih state phase heap)
      · intro next future value good view
        exact CodeAt.failure _ cause good
      · intro next future delivered good
        exact good

  | yielding priority => exact CodeAt.yieldNow _ priority heap
  | constant first body head next ihFirst ihBody =>
      apply CodeAt.constant (.before phase) (.before phase) first body (ihFirst state phase heap)
      · intro after future value good
        exact ihBody after phase good
      · intro after future cause good
        exact good

/-- The concrete root control contains no synchronous reference writer. -/
theorem ReadCode.no_sync (code : NCode) (held : ReadCode code) (thunk : EffThunk) :
    code ≠ .sync thunk := by
  cases held <;> intro impossible <;> cases impossible

/-- The existing actual iteration producer proves reference stability for the root control. -/
theorem ReadCode.iteration_refs (machine : Effect4.Program.NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool)
    (held : ReadCode fiber.frame.current) :
    (iteration (evaluator := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table)
      machine fiber yielding).machine.state.refs = machine.state.refs := by
  have transfer := StoreExecution.iteration_refTransfer HostTimeoutSource.program
    Test.Dogfood.Scenario.Timeout.fetch.table machine fiber yielding
  cases transfer with
  | same after refs => exact refs
  | sync thunk after value current unparked answer =>
      exact False.elim (ReadCode.no_sync fiber.frame.current held thunk current)

/-- Saved root cancellation wrappers carry the same phase on both sides. -/
inductive ReadSaved : NCode → Prop
  | restore (body : NCode) (selected : ExitV) :
      ReadSaved (.onSuccess body (.store (.restore selected)))
  | rethrow (body : NCode) (cause : CauseV) : ReadSaved (.onSuccess body (.reFail cause))
  | cancel (race token : Nat) (owner : FiberId) :
      ReadSaved (.asyncFinalizer (.withWaiter (.store (.cancelRace race)) owner token))
  | mask (flag : Bool) : ReadSaved (.setInterruptible flag)
  | constant (first body : NCode) (next : ReadCode body) : ReadSaved (.onSuccessConst first body)

/-- Saved root contracts quantify the completed-exit view rather than fixing a stale interpreter. -/
theorem ReadSaved.classified (code : NCode) (held : ReadSaved code)
    (view : View) (state : Stores) (phase : Phase) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.before phase) (.before phase) code := by
  cases held with
  | restore body selected => exact race_restore_saved view state phase selected body
  | rethrow body cause =>
      apply AnswerFlow.saved_success
      · intro next future value good
        exact CodeAt.failure _ cause good
      · intro next future delivered good
        exact good
  | cancel race token owner => exact race_cancel_saved view state phase race token owner
  | mask flag => exact AnswerFlow.saved_mask (model view) (interpreter view).toPrimInterp state (.before phase) flag
  | constant first body next =>
      apply AnswerFlow.saved_constant
      · intro after future value good
        exact ReadCode.classified body next after phase good
      · intro after future cause good
        exact good

/-- The root's actual saved front can be rebuilt after either count or cleanup changes the heap. -/
theorem read_stack (front : List NCode) (held : ∀ code ∈ front, ReadSaved code)
    (view : View) (state : Stores) (phase : Phase) :
    AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.before phase) (.before phase) front := by
  induction front with
  | nil => exact .nil _ _
  | cons head tail ih =>
      exact .cons (ReadSaved.classified head (held head (List.mem_cons_self ..)) view state phase)
        (ih (fun code member => held code (List.mem_cons_of_mem head member)))

/-- The source form callback remains below the heap-independent cancellation control. -/
structure RootControl (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode) where
  front : List NCode
  captured : Point
  fuel : Nat
  delay : Nat
  cursor : Fin 4
  previous : Val
  body : NCode
  current : ReadCode frame.current
  saved : ∀ code ∈ front, ReadSaved code
  stack : frame.stack = front ++ [.onExit body
    (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay cursor previous)) false] ++ suffix

/-- Each numeric write reconstructs the same root region using the newly established actual heap. -/
theorem RootControl.region (frame : HostTimeoutFrames.NativeFrame) (suffix : List NCode)
    (held : RootControl frame suffix) (view : View) (state : Stores) (phase : Phase)
    (heap : At phase state) :
    ∃ above, frame.stack = above ++ suffix ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state (.published phase)
        {frame with stack := above} := by
  refine ⟨_, held.stack, .before phase, ReadCode.classified frame.current held.current state phase heap, ?_⟩
  exact AnswerFlow.stack_append (model view) (interpreter view).toPrimInterp
    (read_stack held.front held.saved view state phase)
    (.cons (form_saved view state phase held.captured held.fuel held.delay held.cursor held.previous held.body)
      (.nil _ _))

end Test.Dogfood.Proofs.HostTimeoutNumberRootControl

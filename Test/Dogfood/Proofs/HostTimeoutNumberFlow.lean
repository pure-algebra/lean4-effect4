import Test.Dogfood.Proofs.HostTimeoutNumberCallbacks
import Effect4.Laws.Machine.AnswerFlow
import Effect4.Laws.Machine.AnswerFlowHooks
import Effect4.Laws.Machine.Clauses

/-!
Placement: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the numeric saved callback assertion for Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: native numeric evaluation and actual command history.
The classes read actual reference state after the operation; saved callbacks use AnswerFlow.
This assertion supplies no public-row producer or unconditional interruption permission.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberFlow
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberSteps HostTimeoutNumberState
open HostTimeoutNumberCallbacks

/-- A proof-only image names the exact numeric cells and their checked log relation. -/
structure Image where
  count : Nat
  cleanups : List Val
  completed : List Val
  exits : List ExitV
  numbers : Numbers count cleanups completed exits

/-- The image's exact reference heap uses the existing three-cell carrier. -/
def Image.heap (image : Image) : RefHeap :=
  numberHeap image.count image.cleanups image.completed

/-- An image reads the actual three reference cells. -/
def ImageAt (image : Image) (state : Stores) : Prop :=
  state.refs = numberHeap image.count image.cleanups image.completed

/-- Finishing cleanup advances only the exact cleanup log named by its read. -/
def Image.cleanup (image : Image) (own : image.count = image.cleanups.length + 1)
    (exit : ExitV) : Image :=
  ⟨image.count, image.cleanups ++ [.list [.nat image.count, .bool (interruptionFlag exit)]],
    image.completed, image.exits, cleanup_numbers image.numbers own (interruptionFlag exit)⟩

/-- Publishing a form advances only the completed log after its attempt cleanup. -/
def Image.form (image : Image) (cleanupComplete : image.cleanups.length = image.count)
    (own : image.exits.length + 1 = image.count) (exit : ExitV) : Image :=
  ⟨image.count, image.cleanups, image.completed ++ [.list [.nat image.count, reifyExitVal exit]],
    image.exits ++ [exit], completed_numbers image.numbers cleanupComplete own image.count exit⟩

/-- Actual cleanup closes the active attempt gap before the form can publish its result. -/
theorem Image.cleanup_complete (image : Image) (own : image.count = image.cleanups.length + 1)
    (exit : ExitV) : (image.cleanup own exit).cleanups.length = (image.cleanup own exit).count := by
  change (image.cleanups ++ [Val.list [.nat image.count, .bool (interruptionFlag exit)]]).length = image.count
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  exact own.symm

/-- An active attempt has exactly one unrecorded form result. -/
theorem Image.form_gap (image : Image) (own : image.count = image.cleanups.length + 1) :
    image.exits.length + 1 = image.count := by
  have lower := image.numbers.formLower
  have upper := image.numbers.formUpper
  omega

/-- The form image follows the actual attempt cleanup, whose captured exit is still symbolic. -/
def Image.afterForm (image : Image) (own : image.count = image.cleanups.length + 1)
    (attemptExit selected : ExitV) : Image :=
  (image.cleanup own attemptExit).form (image.cleanup_complete own attemptExit) (image.form_gap own) selected

/-- The count's post-state is fixed before its saved binders are installed. -/
def Image.enter (image : Image) (n : Fin 4)
    (cleanupComplete : image.cleanups.length = image.count)
    (formComplete : image.exits.length = image.count) (cursor : image.count ≤ n.val) : Image :=
  ⟨image.count + 1, image.cleanups, image.completed, image.exits,
    count_numbers image.numbers n cleanupComplete formComplete cursor⟩

/-- The operation's returned class names the state it must establish. -/
inductive Kind
  | read (image : Image)
  | unit (image : Image)
  | restored (image : Image) (exit : ExitV)
  | at (image : Image)
  | cleanupExit (image : Image) (own : image.count = image.cleanups.length + 1)
  | formExit (image : Image) (cleanupComplete : image.cleanups.length = image.count)
      (own : image.exits.length + 1 = image.count)
  | formAfterCleanup (image : Image) (own : image.count = image.cleanups.length + 1)
  | retryResult (image : Image) (own : image.count = image.cleanups.length + 1)
  | raceWaiting (image : Image) (own : image.count = image.cleanups.length + 1)

/-- A count or cleanup answer is valid only at the exact post-operation heap. -/
def ValueAt (state : Stores) : Kind → Val → Prop
  | .read image, value => ImageAt image state ∧ value = .nat image.count
  | .unit image, value => ImageAt image state ∧ value = .unit
  | .restored image (.success saved), value => ImageAt image state ∧ value = saved
  | .restored _ (.failure _), _ => False
  | .at image, _ => ImageAt image state
  | .raceWaiting image own, _ => ∃ saved, ImageAt (image.cleanup own saved) state
  | .cleanupExit image own, _ => ∃ saved, ImageAt (image.cleanup own saved) state
  | .formExit image cleanupComplete own, value =>
    ∃ saved, ImageAt (image.form cleanupComplete own saved) state ∧ saved = .success value
  | .formAfterCleanup image own, value =>
    ∃ attemptExit saved, ImageAt (image.afterForm own attemptExit saved) state ∧ saved = .success value
  | .retryResult image own, value =>
    ∃ attemptExit saved, ImageAt (image.afterForm own attemptExit saved) state ∧
      match saved with
      | .success body => value = .list [.some body, .none]
      | .failure cause => ∃ (n : Fin 4) (delay : Nat) (previous error : Val),
          value = .list [.none, .some error] ∧
          caughtErrorValue? (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
            HostTimeoutSource.retryTest cause = some error

/-- Interruption cleanup retains no typed failure for the declared retry handler to select. -/
def NoTypedFailure (cause : CauseV) : Prop :=
  ∀ reason ∈ cause.reasons, reason.tag ≠ .fail

/-- A failure retains either the exact saved exit or the explicit interruption cleanup cut. -/
def CauseAt (state : Stores) : Kind → CauseV → Prop
  | .restored image (.failure saved), cause => ImageAt image state ∧ (cause = saved ∨ NoTypedFailure cause)
  | .restored image (.success _), cause => ImageAt image state ∧ NoTypedFailure cause
  | .at image, _ => ImageAt image state
  | .raceWaiting image own, cause =>
    (∃ saved, ImageAt (image.cleanup own saved) state) ∨
      (ImageAt image state ∧ cause.hasInterrupts = true)
  | .cleanupExit image own, _ => ∃ saved, ImageAt (image.cleanup own saved) state
  | .formExit image cleanupComplete own, cause =>
    ∃ saved, ImageAt (image.form cleanupComplete own saved) state ∧
      (saved = .failure cause ∨ NoTypedFailure cause)
  | .formAfterCleanup image own, cause =>
    ∃ attemptExit saved, ImageAt (image.afterForm own attemptExit saved) state ∧
      (saved = .failure cause ∨ NoTypedFailure cause)
  | .retryResult image own, cause =>
    ∃ attemptExit saved, ImageAt (image.afterForm own attemptExit saved) state ∧
      (saved = .failure cause ∨ NoTypedFailure cause)
  | _, _ => False

/-- The future relation retains monotone allocated storage, rather than assuming arbitrary store changes. -/
def Future (before after : Stores) : Prop :=
  before.refs.length ≤ after.refs.length ∧ before.deferreds.cells.length ≤ after.deferreds.cells.length

/-- The numeric code assertion inspects existing source primitives and their actual callbacks. -/
inductive CodeAt (state : Stores) : Kind → NCode → Prop
  | success (kind : Kind) (value : Val) (good : ValueAt state kind value) :
      CodeAt state kind (.success value)
  | failure (kind : Kind) (cause : CauseV) (good : CauseAt state kind cause) :
      CodeAt state kind (.failure cause)
  | get (image : Image) (heap : ImageAt image state) :
      CodeAt state (.read image) (.sync (.op (.refGet ⟨0⟩)))
  | count (image : Image) (n : Fin 4)
      (cleanupComplete : image.cleanups.length = image.count)
      (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
      (captured : Point) (fuel delay : Nat) (error : Val) (heap : ImageAt image state) :
      CodeAt state (.unit (image.enter n cleanupComplete formComplete (Nat.le_of_eq cursor)))
        (.sync (.op (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm
          (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error).env)))
  | countBind (image : Image) (n : Fin 4)
      (cleanupComplete : image.cleanups.length = image.count)
      (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
      (captured : Point) (fuel delay : Nat) (error : Val) (heap : ImageAt image state) :
      CodeAt state (.at (image.enter n cleanupComplete formComplete (Nat.le_of_eq cursor)))
        (resolve HostTimeoutSource.program
          ((HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error).child 0))
  | countEntry (image : Image) (n : Fin 4)
      (cleanupComplete : image.cleanups.length = image.count)
      (formComplete : image.exits.length = image.count) (cursor : image.count = n.val)
      (captured : Point) (fuel delay : Nat) (error : Val) (heap : ImageAt image state) :
      CodeAt state (.cleanupExit (image.enter n cleanupComplete formComplete (Nat.le_of_eq cursor))
        (by change image.count + 1 = image.cleanups.length + 1; rw [cleanupComplete]))
        (resolve HostTimeoutSource.program (HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error))
  | cleanup (image : Image) (own : image.count = image.cleanups.length + 1)
      (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (count : image.count = n.val + 1) (heap : ImageAt image state) :
      CodeAt state (.unit (image.cleanup own exit))
        (resolve HostTimeoutSource.program (cleanupPoint captured fuel delay n error exit))
  | cleanupBound (image : Image) (own : image.count = image.cleanups.length + 1)
      (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (count : image.count = n.val + 1) (heap : ImageAt image state) :
      CodeAt state (.unit (image.cleanup own exit))
        (resolve HostTimeoutSource.program
          ({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
            (.nat image.count)))
  | cleanupWrite (image : Image) (own : image.count = image.cleanups.length + 1)
      (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (count : image.count = n.val + 1) (heap : ImageAt image state) :
      CodeAt state (.unit (image.cleanup own exit))
        (resolve HostTimeoutSource.program
          (({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
            (.nat image.count)).child 0))
  | completed (image : Image) (cleanupComplete : image.cleanups.length = image.count)
      (own : image.exits.length + 1 = image.count)
      (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (count : image.count = n.val + 1) (heap : ImageAt image state) :
      CodeAt state (.unit (image.form cleanupComplete own exit))
        (resolve HostTimeoutSource.program (completedPoint captured fuel delay n error exit))
  | completedBound (image : Image) (cleanupComplete : image.cleanups.length = image.count)
      (own : image.exits.length + 1 = image.count)
      (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
      (count : image.count = n.val + 1) (heap : ImageAt image state) :
      CodeAt state (.unit (image.form cleanupComplete own exit))
        (resolve HostTimeoutSource.program
          ({completedPoint captured fuel delay n error exit with completed := view}.childWith 1
            (.nat image.count)))
  | attemptBody (image : Image) (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val)
      (count : image.count = n.val + 1) (heap : ImageAt image state) :
      CodeAt state (.at image)
        (resolve HostTimeoutSource.program
          (((HostTimeoutNumberEntry.attemptPoint captured (fuel + 1) delay n error).child 0).childWith 1 .unit))
  | merge (image : Image) (exit : ExitV) (program : NCode)
      (cleanup : CodeAt state (.unit image) program) :
      CodeAt state (.unit image) (.onFailure program (.merge exit))
  | cleanupReturn (image : Image) (own : image.count = image.cleanups.length + 1)
      (exit : ExitV) (program : NCode) (cleanup : CodeAt state (.unit (image.cleanup own exit)) program) :
      CodeAt state (.cleanupExit image own) (.onSuccess program (.restore exit))
  | formReturn (image : Image) (cleanupComplete : image.cleanups.length = image.count)
      (own : image.exits.length + 1 = image.count) (exit : ExitV) (program : NCode)
      (cleanup : CodeAt state (.unit (image.form cleanupComplete own exit)) program) :
      CodeAt state (.formExit image cleanupComplete own) (.onSuccess program (.restore exit))
  | formFamilyReturn (image : Image) (own : image.count = image.cleanups.length + 1)
      (attemptExit selected : ExitV) (program : NCode)
      (cleanup : CodeAt state (.unit (image.afterForm own attemptExit selected)) program) :
      CodeAt state (.formAfterCleanup image own) (.onSuccess program (.restore selected))
  | restore (image : Image) (exit : ExitV) (program : NCode)
      (cleanup : CodeAt state (.unit image) program) :
      CodeAt state (.restored image exit) (.onSuccess program (.restore exit))
  | cancelRace (image : Image) (own : image.count = image.cleanups.length + 1) (race : Nat)
      (phase : ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state) :
      CodeAt state (.cleanupExit image own) (.withFiber (.store (.act (.cancelRace race))))
  | cancelReturn (image : Image) (own : image.count = image.cleanups.length + 1)
      (cause : CauseV) (program : NCode) (body : CodeAt state (.cleanupExit image own) program) :
      CodeAt state (.cleanupExit image own) (.onSuccess program (.reFail cause))
  | raceWaiting (image : Image) (own : image.count = image.cleanups.length + 1) (race : Nat)
      (phase : ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state) :
      CodeAt state (.raceWaiting image own) (.suspend (.park (.race race)))
  | maskedCancelRace (image : Image) (own : image.count = image.cleanups.length + 1) (race : Nat)
      (phase : ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state) :
      CodeAt state (.cleanupExit image own)
        (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false))))
  | selectedRaceReturn (image : Image) (own : image.count = image.cleanups.length + 1)
      (selected : ExitV) (program : NCode) (body : CodeAt state (.cleanupExit image own) program) :
      CodeAt state (.cleanupExit image own) (.onSuccess program (.store (.restore selected)))

/-- Timeout's numeric instance reuses the shared ordered saved-answer contract. -/
def model (view : View) : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err)
    (δ := Defect) (ι := FiberId) (α := Ann) Stores Kind where
  future := Future
  future_refl := fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  future_trans := fun _ _ _ first second =>
    ⟨Nat.le_trans first.1 second.1, Nat.le_trans first.2 second.2⟩
  value := ValueAt
  cause := CauseAt
  code := CodeAt
  finalizer := fun _ name exit =>
    ((interpreter view).finalizerProgram name exit).map (finalizerCode (interpreter view) exit)
  success := fun _ => CodeAt.success
  failure := fun _ => CodeAt.failure

/-- The actual cleanup count callback supplies the precise writer code in any permitted future store. -/
theorem cleanup_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) :
    let point := cleanupPoint captured fuel delay n error exit
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.read image)
      (.unit (image.cleanup own exit)) (.onSuccess (.sync (.op (.refGet ⟨0⟩))) (.cont point)) := by
  dsimp only
  apply AnswerFlow.saved_success
  · intro next future value good
    change ImageAt image next ∧ value = .nat image.count at good
    rw [good.2, cleanup_callback view captured fuel delay n error exit image.count]
    have body := CodeAt.cleanupBound image own view captured fuel delay n error exit count good.1
    have code : resolve HostTimeoutSource.program
        ({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
          (.nat image.count)) =
        .onSuccess (resolve HostTimeoutSource.program
          (({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
            (.nat image.count)).child 0))
          (.cont ({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
            (.nat image.count))) := by kernel_rfl
    rw [← code]
    exact body
  · intro next future cause good
    exact False.elim good

/-- The actual completed-form count callback retains the saved selected exit and post-cleanup phase. -/
theorem completed_saved (view : View) (state : Stores) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count)
    (own : image.exits.length + 1 = image.count)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) :
    let point := completedPoint captured fuel delay n error exit
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.read image)
      (.unit (image.form cleanupComplete own exit))
      (.onSuccess (.sync (.op (.refGet ⟨0⟩))) (.cont point)) := by
  dsimp only
  apply AnswerFlow.saved_success
  · intro next future value good
    change ImageAt image next ∧ value = .nat image.count at good
    rw [good.2]
    exact CodeAt.completedBound image cleanupComplete own view captured fuel delay n error exit count good.1
  · intro next future cause good
    exact False.elim good

/-- The real restore callback returns the exact saved exit only after cleanup has established its image. -/
theorem restore_saved (view : View) (state : Stores) (image : Image) (exit : ExitV) (program : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state (.unit image)
      (.restored image exit) (.onSuccess program (.restore exit)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    change ImageAt image next ∧ value = .unit at good
    cases exit with
    | success saved => exact CodeAt.success _ saved ⟨good.1, rfl⟩
    | failure saved => exact CodeAt.failure _ saved ⟨good.1, Or.inl rfl⟩
  · intro next future cause good
    exact False.elim good

/-- The source's cleanup-note binder accepts only its exact committed post-write image. -/
theorem cleanup_done_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV) :
    let bound := {cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
      (.nat image.count)
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.cleanup own exit)) (.unit (image.cleanup own exit))
      (.onSuccess (resolve HostTimeoutSource.program (bound.child 0)) (.cont bound)) := by
  dsimp only
  apply AnswerFlow.saved_success
  · intro next future value good
    change ImageAt (image.cleanup own exit) next ∧ value = .unit at good
    rw [good.2]
    have code : (interpreter view).contA
        (.cont ({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
          (.nat image.count))) .unit = .success .unit := by kernel_rfl
    rw [code]
    exact CodeAt.success _ _ ⟨good.1, rfl⟩
  · intro next future cause good
    exact False.elim good

/-- The actual cleanup bind push connects the read to its saved numeric callback. -/
theorem cleanup_push (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) (heap : ImageAt image state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : Kind)
    (current : fiber.current = resolve HostTimeoutSource.program (cleanupPoint captured fuel delay n error exit))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.cleanup own exit)) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  apply AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.read image) (.unit (image.cleanup own exit)) output fiber
    (.sync (.op (.refGet ⟨0⟩))) (.cont (cleanupPoint captured fuel delay n error exit))
    (current.trans (cleanup_code captured fuel delay n error exit)) (CodeAt.get image heap)
    (cleanup_saved view state image own captured fuel delay n error exit count) stack

/-- The real cleanup count pop resolves its writer and retains the actual older suffix. -/
theorem cleanup_pop (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) (heap : ImageAt image state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : Kind) (noInterrupt : fiber.deferredInterrupt = false)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.cleanup own exit)) output fiber.stack) :
    let name := EffName.cont (cleanupPoint captured fuel delay n error exit)
    ({fiber with stack := .onSuccess (.sync (.op (.refGet ⟨0⟩))) name :: fiber.stack}).resumeValue
      (interpreter view).toPrimInterp (.nat image.count) none =
        (.running {fiber with current := (interpreter view).contA name (.nat image.count)},
          [.popped (.onSuccess (.sync (.op (.refGet ⟨0⟩))) name)]) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output
        {fiber with current := (interpreter view).contA name (.nat image.count)} := by
  dsimp only
  exact AnswerFlow.resume_success (model view) (interpreter view).toPrimInterp state
    (.read image) (.unit (image.cleanup own exit)) output fiber
    (.sync (.op (.refGet ⟨0⟩))) (.cont (cleanupPoint captured fuel delay n error exit))
    (.nat image.count) none noInterrupt ⟨heap, rfl⟩
    (fun _ member => False.elim (Option.not_mem_none _ member))
    (cleanup_saved view state image own captured fuel delay n error exit count) stack

/-- The actual cleanup-note push keeps the typed post-write class below its reference leaf. -/
theorem cleanup_note_push (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) (heap : ImageAt image state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : Kind)
    (current : fiber.current = resolve HostTimeoutSource.program
      ({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1 (.nat image.count)))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.cleanup own exit)) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  have code : resolve HostTimeoutSource.program
      ({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1 (.nat image.count)) =
      .onSuccess (resolve HostTimeoutSource.program
        (({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
          (.nat image.count)).child 0))
        (.cont ({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
          (.nat image.count))) := by kernel_rfl
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.unit (image.cleanup own exit)) (.unit (image.cleanup own exit)) output fiber _ _
    (current.trans code) (CodeAt.cleanupWrite image own view captured fuel delay n error exit count heap)
    (cleanup_done_saved view state image own captured fuel delay n error exit) stack

/-- The actual native cleanup writer establishes the image consumed by its saved return callback. -/
theorem cleanup_native_write (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (image : Image)
    (own : image.count = image.cleanups.length + 1)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) (heap : ImageAt image machine.state) (output : Kind)
    (current : fiber.frame.current = resolve HostTimeoutSource.program
      (({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
        (.nat image.count)).child 0))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.unit (image.cleanup own exit)) output fiber.frame.stack) :
    let next := {machine.state with refs := (image.cleanup own exit).heap}
    evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table =
      ⟨{machine with state := next}, {fiber with frame := {fiber.frame with current := .success .unit}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp next output
        {fiber.frame with current := .success .unit} := by
  dsimp only
  let point := ({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
    (.nat image.count)).child 0
  have numbers : Numbers (n.val + 1) image.cleanups image.completed image.exits := count ▸ image.numbers
  have gap : n.val + 1 = image.cleanups.length + 1 := count.symm.trans own
  have owned := cleanup_note_at view captured fuel delay n error exit image.cleanups image.completed image.exits numbers gap
  rw [← count] at owned
  have source := (cleanup_transfer view machine.state captured fuel delay n error exit image.cleanups image.completed image.exits
    (count ▸ heap) numbers gap).2.2.1
  rw [← count] at source
  change ReferenceAtPoint point (numberHeap image.count image.cleanups image.completed) at owned
  rw [← heap] at owned
  obtain ⟨operation, code⟩ := reference_sync point machine.state.refs owned
  unfold sourceStep at source
  change (match resolve HostTimeoutSource.program point with
    | .sync thunk => (interpreter view).syncState thunk machine.state
    | _ => none) = _ at source
  rw [code] at source
  have step : syncOpStep operation machine.state =
      some ({machine.state with refs := (image.cleanup own exit).heap}, .unit) := source
  have future : Future machine.state {machine.state with refs := (image.cleanup own exit).heap} := by
    constructor
    · change machine.state.refs.length ≤ 3
      rw [heap]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  exact ControlSteps.native_sync_answer HostTimeoutSource.program Scenario.Timeout.fetch.table machine fiber yielding
    operation _ .unit id (model view) (interpreter view).toPrimInterp (.unit (image.cleanup own exit)) output
    (current.trans code) step future ⟨rfl, rfl⟩ stack

/-- The actual restore pop consumes the committed cleanup image and keeps the exact captured exit. -/
theorem restore_pop (view : View) (state : Stores) (image : Image) (exit : ExitV) (program : NCode)
    (fiber : HostTimeoutFrames.NativeFrame) (output : Kind) (heap : ImageAt image state)
    (noInterrupt : fiber.deferredInterrupt = false)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.restored image exit) output fiber.stack) :
    ({fiber with stack := .onSuccess program (.restore exit) :: fiber.stack}).resumeValue
      (interpreter view).toPrimInterp .unit none =
        (.running {fiber with current := Prim.ofExit exit}, [.popped (.onSuccess program (.restore exit))]) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output
        {fiber with current := Prim.ofExit exit} := by
  exact AnswerFlow.resume_success (model view) (interpreter view).toPrimInterp state
    (.unit image) (.restored image exit) output fiber program (.restore exit) .unit none
    noInterrupt ⟨heap, rfl⟩ (fun _ member => False.elim (Option.not_mem_none _ member))
    (restore_saved view state image exit program) stack

/-- The actual native form writer publishes its saved selected exit after the cleanup image. -/
theorem completed_native_write (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) (heap : ImageAt image machine.state) (output : Kind)
    (current : fiber.frame.current = resolve HostTimeoutSource.program
      ({completedPoint captured fuel delay n error exit with completed := view}.childWith 1 (.nat image.count)))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.unit (image.form cleanupComplete own exit)) output fiber.frame.stack) :
    let next := {machine.state with refs := (image.form cleanupComplete own exit).heap}
    evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table =
      ⟨{machine with state := next}, {fiber with frame := {fiber.frame with current := .success .unit}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp next output
        {fiber.frame with current := .success .unit} := by
  dsimp only
  let point := {completedPoint captured fuel delay n error exit with completed := view}.childWith 1
    (.nat image.count)
  have numbers : Numbers (n.val + 1) image.cleanups image.completed image.exits := count ▸ image.numbers
  have cleanups : image.cleanups.length = n.val + 1 := cleanupComplete.trans count
  have gap : image.exits.length = n.val := by omega
  have owned := completed_note_at view captured fuel delay n error exit image.cleanups image.completed image.exits numbers cleanups gap
  rw [← count] at owned
  have source := (completed_transfer view machine.state captured fuel delay n error exit image.cleanups image.completed image.exits
    (count ▸ heap) numbers cleanups gap).2.2.1
  rw [← count] at source
  change ReferenceAtPoint point (numberHeap image.count image.cleanups image.completed) at owned
  rw [← heap] at owned
  obtain ⟨operation, code⟩ := reference_sync point machine.state.refs owned
  unfold sourceStep at source
  change (match resolve HostTimeoutSource.program point with
    | .sync thunk => (interpreter view).syncState thunk machine.state
    | _ => none) = _ at source
  rw [code] at source
  have step : syncOpStep operation machine.state =
      some ({machine.state with refs := (image.form cleanupComplete own exit).heap}, .unit) := source
  have future : Future machine.state {machine.state with refs := (image.form cleanupComplete own exit).heap} := by
    constructor
    · change machine.state.refs.length ≤ 3
      rw [heap]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  exact ControlSteps.native_sync_answer HostTimeoutSource.program Scenario.Timeout.fetch.table machine fiber yielding
    operation _ .unit id (model view) (interpreter view).toPrimInterp (.unit (image.form cleanupComplete own exit)) output
    (current.trans code) step future ⟨rfl, rfl⟩ stack

/-- The actual form bind push joins its read to the saved selected-exit writer. -/
theorem completed_push (view : View) (state : Stores) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) (heap : ImageAt image state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : Kind)
    (current : fiber.current = resolve HostTimeoutSource.program (completedPoint captured fuel delay n error exit))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.form cleanupComplete own exit)) output fiber.stack) :
    ∃ next events, fiber.step (interpreter view).toPrimInterp = (.running next, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output next := by
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.read image) (.unit (image.form cleanupComplete own exit)) output fiber
    (.sync (.op (.refGet ⟨0⟩))) (.cont (completedPoint captured fuel delay n error exit))
    (current.trans (completed_code captured fuel delay n error exit)) (CodeAt.get image heap)
    (completed_saved view state image cleanupComplete own captured fuel delay n error exit count) stack

/-- The real completed-form count pop retains the actual older suffix and exact selected exit. -/
theorem completed_pop (view : View) (state : Stores) (image : Image)
    (cleanupComplete : image.cleanups.length = image.count) (own : image.exits.length + 1 = image.count)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (count : image.count = n.val + 1) (heap : ImageAt image state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : Kind) (noInterrupt : fiber.deferredInterrupt = false)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.unit (image.form cleanupComplete own exit)) output fiber.stack) :
    let name := EffName.cont (completedPoint captured fuel delay n error exit)
    ({fiber with stack := .onSuccess (.sync (.op (.refGet ⟨0⟩))) name :: fiber.stack}).resumeValue
      (interpreter view).toPrimInterp (.nat image.count) none =
        (.running {fiber with current := (interpreter view).contA name (.nat image.count)},
          [.popped (.onSuccess (.sync (.op (.refGet ⟨0⟩))) name)]) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output
        {fiber with current := (interpreter view).contA name (.nat image.count)} := by
  dsimp only
  exact AnswerFlow.resume_success (model view) (interpreter view).toPrimInterp state
    (.read image) (.unit (image.form cleanupComplete own exit)) output fiber
    (.sync (.op (.refGet ⟨0⟩))) (.cont (completedPoint captured fuel delay n error exit))
    (.nat image.count) none noInterrupt ⟨heap, rfl⟩
    (fun _ member => False.elim (Option.not_mem_none _ member))
    (completed_saved view state image cleanupComplete own captured fuel delay n error exit count) stack

/-- The native count read returns the actual heap count and retains the ordered saved suffix. -/
theorem native_get (view : View) (machine : Effect4.Program.NativeMachine)
    (fiber : HostTimeoutEvaluation.NativeFiber) (yielding : Bool) (image : Image) (output : Kind)
    (heap : ImageAt image machine.state) (current : fiber.frame.current = .sync (.op (.refGet ⟨0⟩)))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.read image) output fiber.frame.stack) :
    evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table =
      ⟨machine, {fiber with frame := {fiber.frame with current := .success (.nat image.count)}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp machine.state output
        {fiber.frame with current := .success (.nat image.count)} := by
  have answer : syncOpStep (.refGet ⟨0⟩) {machine.state with refs := image.heap} =
      some ({machine.state with refs := image.heap}, .nat image.count) := by kernel_rfl
  have same : {machine.state with refs := image.heap} = machine.state := by
    dsimp only [Image.heap]
    rw [← heap]
  rw [same] at answer
  exact ControlSteps.native_sync_answer HostTimeoutSource.program Scenario.Timeout.fetch.table machine fiber yielding
    (.refGet ⟨0⟩) machine.state (.nat image.count) id (model view) (interpreter view).toPrimInterp
    (.read image) output current answer ((model view).future_refl machine.state) ⟨heap, rfl⟩ stack

/-- Stripping the interrupted typed failures cannot invent permission for a declared retry. -/
theorem no_typed_strip (cause : CauseV) : NoTypedFailure cause.stripFail := by
  intro reason member
  exact (Cause.mem_stripFail reason cause).mp member |>.2

/-- The actual interrupted catch cleanup retains the committed post-finalization heap. -/
theorem restored_strip (state : Stores) (image : Image) (exit : ExitV) (cause : CauseV)
    (good : CauseAt state (.restored image exit) cause) :
    CauseAt state (.restored image exit) cause.stripFail := by
  cases exit with
  | success value => exact ⟨good.1, no_typed_strip cause⟩
  | failure saved => exact ⟨good.1, Or.inr (no_typed_strip cause)⟩

/-- Combining an explicit interruption cleanup cause retains its no-typed-failure cut. -/
theorem no_typed_combine (first second : CauseV) (left : NoTypedFailure first)
    (right : NoTypedFailure second) : NoTypedFailure (Cause.combine first second) := by
  intro reason member
  rcases (Cause.mem_combine reason first second).mp member with before | after
  · exact left reason before
  · exact right reason after

/-- The actual sanitize operation retains both numeric state and the explicit interruption cut. -/
theorem restored_sanitize (state : Stores) (image : Image) (exit : ExitV) (cause interrupted : CauseV)
    (good : CauseAt state (.restored image exit) cause) (recorded : NoTypedFailure interrupted) :
    CauseAt state (.restored image exit) (Cause.sanitize cause interrupted) := by
  have cleared := no_typed_combine cause.stripFail interrupted (no_typed_strip cause) recorded
  cases exit with
  | success value => exact ⟨good.1, cleared⟩
  | failure saved => exact ⟨good.1, Or.inr cleared⟩

/-- Stripping typed failures retains the actual interruption used by the waiting cancellation class. -/
theorem waiting_interrupt_strip (cause : CauseV) (present : cause.hasInterrupts = true) :
    cause.stripFail.hasInterrupts = true := by
  obtain ⟨reason, member, tag⟩ := Cause.hasInterrupts_iff cause |>.mp present
  apply (Cause.hasInterrupts_iff cause.stripFail).mpr
  exact ⟨reason, (Cause.mem_stripFail reason cause).mpr ⟨member, by rw [tag]; decide⟩, tag⟩

/-- Actual sanitization retains the incoming interruption through the existing reason union. -/
theorem waiting_interrupt_sanitize (cause recorded : CauseV) (present : cause.hasInterrupts = true) :
    (Cause.sanitize cause recorded).hasInterrupts = true := by
  obtain ⟨reason, member, tag⟩ := (Cause.hasInterrupts_iff cause.stripFail).mp (waiting_interrupt_strip cause present)
  apply (Cause.hasInterrupts_iff (Cause.sanitize cause recorded)).mpr
  exact ⟨reason, (Cause.mem_combine reason cause.stripFail recorded).mpr (.inl member), tag⟩

/-- Every committed numeric cause class survives stripping typed failures at an actual skipped handler. -/
theorem cause_strip (state : Stores) (kind : Kind) (cause : CauseV)
    (good : CauseAt state kind cause) : CauseAt state kind cause.stripFail := by
  cases kind with
  | read image => exact False.elim good
  | unit image => exact False.elim good
  | restored image exit => exact restored_strip state image exit cause good
  | «at» image => exact good
  | raceWaiting image own =>
    rcases good with cleaned | active
    · exact .inl cleaned
    · exact .inr ⟨active.1, waiting_interrupt_strip cause active.2⟩
  | cleanupExit image own => exact good
  | formExit image cleanupComplete own =>
    obtain ⟨saved, heap, _⟩ := good
    exact ⟨saved, heap, Or.inr (no_typed_strip cause)⟩
  | formAfterCleanup image own =>
    obtain ⟨attemptExit, saved, heap, _⟩ := good
    exact ⟨attemptExit, saved, heap, Or.inr (no_typed_strip cause)⟩
  | retryResult image own =>
    obtain ⟨attemptExit, saved, heap, _⟩ := good
    exact ⟨attemptExit, saved, heap, Or.inr (no_typed_strip cause)⟩

/-- Actual handler sanitization retains committed numeric phases under the explicit recorded interruption cut. -/
theorem cause_sanitize (state : Stores) (kind : Kind) (cause interrupted : CauseV)
    (good : CauseAt state kind cause) (recorded : NoTypedFailure interrupted) :
    CauseAt state kind (Cause.sanitize cause interrupted) := by
  cases kind with
  | read image => exact False.elim good
  | unit image => exact False.elim good
  | restored image exit => exact restored_sanitize state image exit cause interrupted good recorded
  | «at» image => exact good
  | raceWaiting image own =>
    rcases good with cleaned | active
    · exact .inl cleaned
    · exact .inr ⟨active.1, waiting_interrupt_sanitize cause interrupted active.2⟩
  | cleanupExit image own => exact good
  | formExit image cleanupComplete own =>
    obtain ⟨saved, heap, _⟩ := good
    exact ⟨saved, heap, Or.inr (Cause.sanitize_clean cause interrupted recorded)⟩
  | formAfterCleanup image own =>
    obtain ⟨attemptExit, saved, heap, _⟩ := good
    exact ⟨attemptExit, saved, heap, Or.inr (Cause.sanitize_clean cause interrupted recorded)⟩
  | retryResult image own =>
    obtain ⟨attemptExit, saved, heap, _⟩ := good
    exact ⟨attemptExit, saved, heap, Or.inr (Cause.sanitize_clean cause interrupted recorded)⟩

/-- An interrupted cause has no first typed error for the concrete retry predicate to test. -/
theorem no_typed_error (cause : CauseV) (cleared : NoTypedFailure cause) :
    firstErrorValue? cause = none := by
  have missing : firstFailure? cause = none := by
    apply List.findSome?_eq_none_iff.mpr
    intro reason member
    have tag := cleared reason member
    cases reason with
    | fail error annotations => exact False.elim (tag rfl)
    | die defect annotations => rfl
    | interrupt who annotations => rfl
  unfold firstErrorValue?
  rw [missing]
  rfl

/-- The actual catch test cannot retry an explicit interruption cleanup cause. -/
theorem no_typed_test (env : List Val) (test : Term) (cause : CauseV)
    (cleared : NoTypedFailure cause) : caughtErrorValue? env test cause = none := by
  unfold caughtErrorValue?
  rw [no_typed_error cause cleared]
  rfl

/-- The source catch callback propagates the interruption cut with its committed numeric state. -/
theorem no_typed_catch (view : View) (state : Stores) (image : Image) (exit : ExitV)
    (point : Point) (test : Term) (body handler : NativeEff) (cause : CauseV)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.catchIf test body handler)))
    (good : CauseAt state (.restored image exit) cause) (cleared : NoTypedFailure cause) :
    CodeAt state (.restored image exit) ((interpreter view).contE (.caughtError point) cause) := by
  change CodeAt state (.restored image exit)
    (Effect4.Program.contEOf HostTimeoutSource.program (.caughtError {point with completed := view}) cause)
  have found : Node.at_ (.eff HostTimeoutSource.program) {point with completed := view}.path =
      some (.eff (.catchIf test body handler)) := node
  simp only [Effect4.Program.contEOf, found, no_typed_test point.env test cause cleared]
  exact CodeAt.failure _ _ good

/-- The actual native cancellation hook preserves the original cause beneath the race action. -/
theorem race_cancel_program (view : View) (race token : Nat) (owner : FiberId) (cause : CauseV) :
    (interpreter view).cancelThenFail (.withWaiter (.store (.cancelRace race)) owner token) cause =
      .onSuccess (.withFiber (.store (.act (.cancelRace race)))) (.reFail cause) := by kernel_rfl

/-- One numeric waiting class separates active cancellation input from completed cleanup output. -/
theorem race_cancel_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (race token : Nat) (owner : FiberId) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.raceWaiting image own) (.cleanupExit image own)
      (.asyncFinalizer (.withWaiter (.store (.cancelRace race)) owner token)) := by
  refine AnswerFlow.SavedAt.mk state (HostTimeoutNumberFlow.Kind.raceWaiting image own) (HostTimeoutNumberFlow.Kind.cleanupExit image own) _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro next future value good absent
    exact good
  · intro next future cause good absent
    cases absent
  · intro next future value provided code pushed good supplied noProgram arm
    cases arm
  · intro next future cause provided code pushed good supplied noProgram arm
    cases interrupted : cause.hasInterrupts with
    | false =>
      rw [Prim.armE_asyncFinalizer_no_interrupt _ _ cause provided interrupted] at arm
      cases arm
      rcases good with cleaned | active
      · exact AnswerFlow.ResultAt.mk next (HostTimeoutNumberFlow.Kind.cleanupExit image own) (HostTimeoutNumberFlow.Kind.cleanupExit image own) _ []
          (CodeAt.failure (HostTimeoutNumberFlow.Kind.cleanupExit image own) cause cleaned) (.nil next _)
      · rw [interrupted] at active
        cases active.2
    | true =>
      rw [Prim.armE_asyncFinalizer_interrupt _ _ cause provided interrupted] at arm
      cases arm
      rw [race_cancel_program]
      have phase : ImageAt image next ∨ ∃ exit, ImageAt (image.cleanup own exit) next := by
        rcases good with cleaned | active
        · exact .inr cleaned
        · exact .inl active.1
      exact AnswerFlow.ResultAt.mk next (HostTimeoutNumberFlow.Kind.cleanupExit image own) (HostTimeoutNumberFlow.Kind.cleanupExit image own) _ []
        (CodeAt.cancelReturn image own cause _ (CodeAt.cancelRace image own race phase)) (.nil next _)
  · intro next future exit code good installed
    cases installed
  · intro next future fiber cause delivered good arm interrupted skipped
    have quiet : ((Prim.asyncFinalizer (.withWaiter (.store (.cancelRace race)) owner token)).ensure fiber).1.interrupted = false := by
      cases flag : fiber.interruptible with
      | false =>
        rw [Prim.ensure_asyncFinalizer_already_masked _ fiber flag]
        change (fiber.interruptible && fiber.interruptedCause.isSome) = false
        rw [flag]
        rfl
      | true =>
        rw [Prim.ensure_asyncFinalizer_masks _ fiber flag]
        rfl
    rw [quiet] at interrupted
    cases interrupted

/-- Actual registration parking installs the waiting input above the existing completed-cleanup suffix.
The active image is an explicit producer premise; parking itself does not establish the count. -/
theorem race_cancel_registration_park (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (race token : Nat)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (pending : Pending EffName Val Err Defect FiberId Ann)
    (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.frame.current = .suspend (.park (.race race)))
    (phase : ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) output fiber.frame.stack) :
    let name := EffName.withWaiter (.store (.cancelRace race)) fiber.id token
    let waiting := ({fiber with frame := {fiber.frame with stack := .asyncFinalizer name :: fiber.frame.stack}}).park pending
    AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output waiting.frame := by
  refine ⟨HostTimeoutNumberFlow.Kind.raceWaiting image own, ?_, ?_⟩
  · change CodeAt state (.raceWaiting image own) fiber.frame.current
    rw [current]
    exact CodeAt.raceWaiting image own race phase
  · exact .cons (race_cancel_saved view state image own race token fiber.id) stack

/-- The actual re-failure callback cannot run its output permission before completed cleanup. -/
theorem cancel_restore_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (cause : CauseV) (program : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) (.cleanupExit image own) (.onSuccess program (.reFail cause)) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    exact CodeAt.failure _ cause good
  · intro next future other good
    exact good

/-- The actual cancel binder pushes only its captured-cause restore above the existing form suffix. -/
theorem race_cancel_push (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (race token : Nat) (owner : FiberId) (cause : CauseV)
    (phase : ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.current = (interpreter view).cancelThenFail
      (.withWaiter (.store (.cancelRace race)) owner token) cause)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) output fiber.stack) :
    ∃ after events, fiber.step (interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output after := by
  rw [race_cancel_program] at current
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.cleanupExit image own) (.cleanupExit image own) output fiber _ (.reFail cause) current
    (CodeAt.cancelRace image own race phase) (cancel_restore_saved view state image own cause _) stack
/-- The actual native race restoration retains its selected exit above masked cancellation. -/
theorem race_settle_program (view : View) (race : Nat) (needed : Bool) (selected : ExitV) :
    (interpreter view).raceSettle race needed selected =
      if needed then .onSuccess (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false))))
        (.store (.restore selected)) else Prim.ofExit selected := by
  cases needed <;> cases selected <;> kernel_rfl

/-- Actual settlement starts cancellation in the active heap; skipping cancellation requires completed cleanup. -/
theorem race_settle_code (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (race : Nat) (needed : Bool) (selected : ExitV)
    (phase : ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state)
    (already : needed = false → AnswerFlow.ExitAt (model view) state (.cleanupExit image own) selected) :
    CodeAt state (.cleanupExit image own) ((interpreter view).raceSettle race needed selected) := by
  rw [race_settle_program]
  cases needed with
  | true => exact CodeAt.selectedRaceReturn image own selected _ (CodeAt.maskedCancelRace image own race phase)
  | false =>
    have good := already rfl
    cases selected with
    | success value => exact CodeAt.success _ value good
    | failure cause => exact CodeAt.failure _ cause good

/-- The selected-exit callback requires completed cleanup and preserves the actual selected exit. -/
theorem race_settle_saved (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (selected : ExitV) (program : NCode) :
    AnswerFlow.SavedAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) (.cleanupExit image own) (.onSuccess program (.store (.restore selected))) := by
  apply AnswerFlow.saved_success
  · intro next future value good
    cases selected with
    | success saved => exact CodeAt.success _ saved good
    | failure cause => exact CodeAt.failure _ cause good
  · intro next future cause good
    exact good

/-- The actual accepted-settlement binder saves its selected exit above the masked cancellation body. -/
theorem race_settle_push (view : View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (race : Nat) (selected : ExitV)
    (phase : ImageAt image state ∨ ∃ exit, ImageAt (image.cleanup own exit) state)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.current = (interpreter view).raceSettle race true selected)
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp state
      (.cleanupExit image own) output fiber.stack) :
    ∃ after events, fiber.step (interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp state output after := by
  rw [race_settle_program] at current
  exact AnswerFlow.push_success (model view) (interpreter view).toPrimInterp state
    (.cleanupExit image own) (.cleanupExit image own) output fiber _ (.store (.restore selected)) current
    (CodeAt.maskedCancelRace image own race phase) (race_settle_saved view state image own selected _) stack

/-- The actual native mask starts only the same race cancellation and inserts an identity restoring frame. -/
theorem race_settle_mask_native (view : View) (machine : NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool) (image : Image)
    (own : image.count = image.cleanups.length + 1) (race : Nat)
    (phase : ImageAt image machine.state ∨ ∃ exit, ImageAt (image.cleanup own exit) machine.state)
    (output : HostTimeoutNumberFlow.Kind)
    (current : fiber.frame.current = .withFiber (.store (.act (.setInterruptible (.cancelRace race) false))))
    (stack : AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit image own) output fiber.frame.stack) :
    let result := evaluatePrim (interpreter view) machine fiber yielding
    result.machine = machine ∧ result.fiber.frame.interruptible = false ∧
      result.edits = [] ∧ result.nested = [] ∧
      AnswerFlow.FrameAt (model view) (interpreter view).toPrimInterp machine.state output result.fiber.frame := by
  have ran := evaluatePrim_withFiber_runs (interpreter view) machine fiber yielding
    (.store (.act (.setInterruptible (.cancelRace race) false)))
    (.setInterruptible (.withFiber (.store (.act (.cancelRace race)))) false) current rfl rfl
  rw [ran]
  refine ⟨rfl, ?_, rfl, rfl, HostTimeoutNumberFlow.Kind.cleanupExit image own,
    CodeAt.cancelRace image own race phase, ?_⟩
  · change fiber.frame.uninterruptible.interruptible = false
    cases flag : fiber.frame.interruptible with
    | false => rw [FrameFiber.uninterruptible_already_masked fiber.frame flag]; exact flag
    | true => rw [FrameFiber.uninterruptible_masks fiber.frame flag]
  · change AnswerFlow.StackAt (model view) (interpreter view).toPrimInterp machine.state
      (.cleanupExit image own) output fiber.frame.uninterruptible.stack
    cases flag : fiber.frame.interruptible with
    | false => rw [FrameFiber.uninterruptible_already_masked fiber.frame flag]; exact stack
    | true =>
      rw [FrameFiber.uninterruptible_masks fiber.frame flag]
      exact .cons (AnswerFlow.saved_mask (model view) (interpreter view).toPrimInterp machine.state
        (.cleanupExit image own) true) stack
end Test.Dogfood.Proofs.HostTimeoutNumberFlow

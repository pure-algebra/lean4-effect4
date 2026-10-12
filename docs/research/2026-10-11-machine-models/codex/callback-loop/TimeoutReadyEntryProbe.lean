import TimeoutNativeRootFamilyProbe
import Effect4.Laws.Machine.AnswerFlowHead

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.cleanup_keeps needs Ready entry into the actual mixed form suffix.
Consumer: actual catch, answer and form pushes before the race allocates its children.
Reach: exact Ready heap, captured source point and expected next generation.
The expected output image is not an already committed count or completed cleanup.
No current-code future weakening, source census, or reached-history premise is added.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace Test.Dogfood.Proofs.HostTimeoutReadyEntry
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts
open HostTimeoutNumberFlow HostTimeoutRootLoop HostTimeoutJointGeneration

/-- The current retry handler saves its actual catch above the answer binder. -/
theorem catch_bind (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) :
    resolve HostTimeoutSource.program (catchPoint captured (fuel + 4) n delay previous) =
      .onFailure (resolve HostTimeoutSource.program (answerBinderPoint captured fuel n delay previous))
        (.caughtError (catchPoint captured (fuel + 4) n delay previous)) := by kernel_rfl

/-- The current timeout form saves its native finalizer above its actual race body. -/
theorem form_bind (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) :
    let point := HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous
    resolve HostTimeoutSource.program point =
      .onExit (resolve HostTimeoutSource.program (point.child 0)) (.fin point) false := by
  dsimp only
  kernel_rfl

/-- The expected generation uses the existing count image without asserting its write has executed. -/
def expected (image : Image) (n : Fin 4) (ready : Complete image n.val false) : Image :=
  HostTimeoutNumberCounted.nextImage image n ready.cleanups ready.forms (Nat.le_of_eq ready.cursor)

/-- The expected next generation owns the one future cleanup slot. -/
theorem expected_own (image : Image) (n : Fin 4) (ready : Complete image n.val false) :
    (expected image n ready).count = (expected image n ready).cleanups.length + 1 := by
  change image.count + 1 = image.cleanups.length + 1
  rw [ready.cleanups]

/-- The expected count retains the source cursor's exact next generation. -/
theorem expected_count (image : Image) (n : Fin 4) (ready : Complete image n.val false) :
    (expected image n ready).count = n.val + 1 := by
  change image.count + 1 = n.val + 1
  rw [ready.cursor]

/-- Current entry permission reads Ready while its saved output classes name the future form. -/
inductive CodeAt (view : HostTimeoutFlow.View) (state : Stores) : HostTimeoutNativeRootFamily.Kind → NCode → Prop
  | base (kind : HostTimeoutNativeRootFamily.Kind) (code : NCode) (held : HostTimeoutNativeRootFamily.CodeAt state kind code) : CodeAt view state kind code
  | answer (image : Image) (n : Fin 4) (ready : Complete image n.val false) (heap : ImageAt image state)
      (captured : Point) (fuel delay : Nat) (previous : Val) :
      CodeAt view state (.inr (.published (expected image n ready) (expected_own image n ready) n delay previous))
        (resolve HostTimeoutSource.program (answerBinderPoint captured fuel n delay previous))
  | form (image : Image) (n : Fin 4) (ready : Complete image n.val false) (heap : ImageAt image state)
      (captured : Point) (fuel delay : Nat) (previous : Val) :
      CodeAt view state (.inl (.formAfterCleanup (expected image n ready) (expected_own image n ready)))
        (resolve HostTimeoutSource.program (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous))
  | race (image : Image) (n : Fin 4) (ready : Complete image n.val false) (heap : ImageAt image state)
      (captured : Point) (fuel delay : Nat) (previous : Val) :
      CodeAt view state (.inl (.cleanupExit (expected image n ready) (expected_own image n ready)))
        (resolve HostTimeoutSource.program
          ((HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous).child 0))

  | waiting (image : Image) (n : Fin 4) (ready : Complete image n.val false) (race : Nat)
      (phase : ImageAt image state ∨ ImageAt (expected image n ready) state ∨
        ∃ exit, ImageAt ((expected image n ready).cleanup (expected_own image n ready) exit) state) :
      CodeAt view state (.inl (.cleanupExit (expected image n ready) (expected_own image n ready)))
        (.suspend (.park (.race race)))

/-- Only current entry permissions extend; actual answers, causes and native hooks stay exact. -/
def model (view : HostTimeoutFlow.View) : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val)
    (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) Stores HostTimeoutNativeRootFamily.Kind :=
  { HostTimeoutNativeRootFamily.model view with
    code := CodeAt view
    success := fun state kind value good => .base kind _ ((HostTimeoutNativeRootFamily.model view).success state kind value good)
    failure := fun state kind cause good => .base kind _ ((HostTimeoutNativeRootFamily.model view).failure state kind cause good) }

/-- Existing callback results retain their actual path under the current-entry permission extension. -/
theorem result (view : HostTimeoutFlow.View) (state : Stores) (output : HostTimeoutNativeRootFamily.Kind) (code : NCode) (frames : List NCode)
    (held : AnswerFlow.FamilyResult (HostTimeoutNativeRootFamily.model view) (HostTimeoutNativeRootFamily.Edge view) state output code frames) :
    AnswerFlow.FamilyResult (model view) (HostTimeoutNativeRootFamily.Edge view) state output code frames := by
  obtain ⟨input, good, path⟩ := held
  exact ⟨input, .base input code good, path⟩

/-- The existing six callback obligations consume unchanged answers and the actual native hook. -/
theorem family (view : HostTimeoutFlow.View) :
    AnswerFlow.SavedFamily (model view) (HostTimeoutFlow.interpreter view).toPrimInterp (HostTimeoutNativeRootFamily.Edge view) where
  skip := (HostTimeoutNativeRootFamily.family view).skip
  skipCause := (HostTimeoutNativeRootFamily.family view).skipCause
  answer := by
    intro state input output frame edge next future value provided code pushed good supplied absent arm
    exact result view next output code pushed
      ((HostTimeoutNativeRootFamily.family view).answer state input output frame edge next future value provided code pushed good supplied absent arm)
  cause := by
    intro state input output frame edge next future cause provided code pushed good supplied absent arm
    exact result view next output code pushed
      ((HostTimeoutNativeRootFamily.family view).cause state input output frame edge next future cause provided code pushed good supplied absent arm)
  program := by
    intro state input output frame edge next future exit code good found
    exact .base output code ((HostTimeoutNativeRootFamily.family view).program state input output frame edge next future exit code good found)
  discard := (HostTimeoutNativeRootFamily.family view).discard

/-- The actual catch push keeps Ready and saves only the later completed-form permission. -/
theorem catch_entry (view : HostTimeoutFlow.View) (state : Stores) (image : Image)
    (n : Fin 4) (ready : Complete image n.val false) (heap : ImageAt image state)
    (captured : Point) (fuel delay : Nat) (previous : Val)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNativeRootFamily.Kind)
    (current : fiber.current = resolve HostTimeoutSource.program (catchPoint captured (fuel + 4) n delay previous))
    (stack : Path (HostTimeoutNativeRootFamily.Edge view state) (.inr (.body n delay previous)) output fiber.stack) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model view) (HostTimeoutNativeRootFamily.Edge view) state output after.current after.stack := by
  rw [catch_bind] at current
  let futureImage := expected image n ready
  let own := expected_own image n ready
  obtain ⟨after, events, ran, code, path⟩ := AnswerFlow.push_failure_path (model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp state (.inr (.published futureImage own n delay previous))
    (.inr (.body n delay previous)) output (HostTimeoutNativeRootFamily.Edge view) fiber _ _ current
    (CodeAt.answer image n ready heap captured fuel delay previous)
    (.root _ _ _ (HostTimeoutRootLoop.Edge.caught captured (fuel + 3) n delay previous futureImage own _)) stack
  exact ⟨after, events, ran, .inr (.published futureImage own n delay previous), code, path⟩

/-- The actual answer binder pushes a future return edge while its form body still reads Ready. -/
theorem answer_entry (view : HostTimeoutFlow.View) (state : Stores) (image : Image)
    (n : Fin 4) (ready : Complete image n.val false) (heap : ImageAt image state)
    (captured : Point) (fuel delay : Nat) (previous : Val)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNativeRootFamily.Kind)
    (current : fiber.current = resolve HostTimeoutSource.program (answerBinderPoint captured fuel n delay previous))
    (stack : Path (HostTimeoutNativeRootFamily.Edge view state)
      (.inr (.published (expected image n ready) (expected_own image n ready) n delay previous)) output fiber.stack) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model view) (HostTimeoutNativeRootFamily.Edge view) state output after.current after.stack := by
  rw [answer_bind] at current
  obtain ⟨after, events, ran, code, path⟩ := AnswerFlow.push_success_path (model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp state
    (.inl (.formAfterCleanup (expected image n ready) (expected_own image n ready)))
    (.inr (.published (expected image n ready) (expected_own image n ready) n delay previous))
    output (HostTimeoutNativeRootFamily.Edge view) fiber _ _ current
    (CodeAt.form image n ready heap captured fuel delay previous)
    (.answer captured fuel (expected image n ready) (expected_own image n ready) n delay previous
      (expected_count image n ready) _) stack
  exact ⟨after, events, ran, .inl (.formAfterCleanup (expected image n ready) (expected_own image n ready)), code, path⟩

/-- The actual form push saves its native callback without assuming that count or cleanup has run. -/
theorem form_entry (view : HostTimeoutFlow.View) (state : Stores) (image : Image)
    (n : Fin 4) (ready : Complete image n.val false) (heap : ImageAt image state)
    (captured : Point) (fuel delay : Nat) (previous : Val)
    (fiber : HostTimeoutFrames.NativeFrame) (output : HostTimeoutNativeRootFamily.Kind)
    (current : fiber.current = resolve HostTimeoutSource.program
      (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous))
    (stack : Path (HostTimeoutNativeRootFamily.Edge view state)
      (.inl (.formAfterCleanup (expected image n ready) (expected_own image n ready))) output fiber.stack) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model view) (HostTimeoutNativeRootFamily.Edge view) state output after.current after.stack := by
  rw [form_bind] at current
  have head : AnswerFlow.HeadAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      (HostTimeoutNativeRootFamily.Edge view) state
      (.inl (.formAfterCleanup (expected image n ready) (expected_own image n ready))) fiber.current := by
    rw [current]
    exact .onExit (.inl (.cleanupExit (expected image n ready) (expected_own image n ready))) _ _ false
      (show CodeAt view state _ _ from CodeAt.race image n ready heap captured fuel delay previous)
      (.lower _ _ _ (HostTimeoutNumberFormFamily.form_saved view state
        (expected image n ready) (expected_own image n ready) captured fuel delay n previous
        (expected_count image n ready) _))
  have stepped := AnswerFlow.frame_step (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    (HostTimeoutNativeRootFamily.Edge view) state _ output fiber head stack
    (by
      intro value provided actual good
      rcases actual with ⟨success, _⟩ | ⟨thunk, sync, _, _⟩
      · rw [current] at success; cases success
      · rw [current] at sync; cases sync)
    (by intro cause actual good; rw [current] at actual; cases actual)
  simp only [FrameFiber.step, current] at stepped ⊢
  exact ⟨_, _, rfl, stepped⟩

/-- Actual race entry installs the counted suspension above the same future form suffix.
Ready remains the current heap; this permission does not assert completed attempt cleanup. -/
theorem race_waiting (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool) (programs : List NCode)
    (site : Option (List Nat)) (image : Image) (n : Fin 4) (ready : Complete image n.val false)
    (heap : ImageAt image machine.state) (output : HostTimeoutNativeRootFamily.Kind)
    (stack : Path (HostTimeoutNativeRootFamily.Edge view machine.state)
      (.inl (.cleanupExit (expected image n ready) (expected_own image n ready))) output fiber.frame.stack) :
    let result := evaluatePrim.withFiber (HostTimeoutFlow.interpreter view) machine fiber yielding (.raceAllFirst programs site)
    AnswerFlow.FamilyResult (model view) (HostTimeoutNativeRootFamily.Edge view)
      result.machine.state output result.fiber.frame.current result.fiber.frame.stack := by
  exact ⟨.inl (.cleanupExit (expected image n ready) (expected_own image n ready)),
    CodeAt.waiting image n ready machine.nextRace (.inl heap), stack⟩

/-- The waiting suspension remains permitted after the actual count image is committed.
This is a current-state constructor; it supplies no unrestricted future-code transport. -/
theorem waiting_counted (view : HostTimeoutFlow.View) (state : Stores) (image : Image)
    (n : Fin 4) (ready : Complete image n.val false) (race : Nat)
    (heap : ImageAt (expected image n ready) state) :
    CodeAt view state (.inl (.cleanupExit (expected image n ready) (expected_own image n ready)))
      (.suspend (.park (.race race))) := CodeAt.waiting image n ready race (.inr (.inl heap))

/-- Actual race registration retains that current permission and the exact pending launch commands.
Its returned frame still awaits the assigned attempt's completed cleanup. -/
theorem race_registration (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool) (raceId : Nat)
    (race : Effect4.Program.SourceScope.SourceRace) (output : HostTimeoutNativeRootFamily.Kind)
    (current : fiber.frame.current = .suspend (.park (.race raceId)))
    (found : machine.race? raceId = some race)
    (held : AnswerFlow.FamilyResult (model view) (HostTimeoutNativeRootFamily.Edge view)
      machine.state output fiber.frame.current fiber.frame.stack) :
    let result := evaluatePrim (HostTimeoutFlow.interpreter view) machine fiber yielding
    result.machine.state = machine.state ∧ result.fiber = fiber ∧
      result.nested = [.launch raceId, .registrationDone raceId yielding] ∧ result.edits = [] ∧
      AnswerFlow.FamilyResult (model view) (HostTimeoutNativeRootFamily.Edge view)
        result.machine.state output result.fiber.frame.current result.fiber.frame.stack := by
  have registered := evaluatePrim_raceRegister (HostTimeoutFlow.interpreter view) machine fiber yielding
    (.park (.race raceId)) raceId race current rfl found
  rw [registered]
  exact ⟨rfl, rfl, rfl, rfl, held⟩
end Test.Dogfood.Proofs.HostTimeoutReadyEntry

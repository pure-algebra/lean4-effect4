import TimeoutRootLoopProbe

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.cleanup_keeps needs native form interception above its actual recursive root suffix.
Consumer: actual selected form finalization, without a new evaluator or command traversal.
Reach: one current completion view, actual cleanup permission and selected onExit evidence.
This instance grants no reached cleanup, allocation, token, or public-budget producer.
The raw cleanup lane permits arbitrary causes; the plain retry policy remains separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000


namespace Test.Dogfood.Proofs.HostTimeoutNativeRootFamily
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts
open HostTimeoutNumberFlow
abbrev Kind := Sum HostTimeoutNumberFlow.Kind HostTimeoutRootLoop.Kind

def ValueAt (state : Stores) : Kind → Val → Prop
  | .inl kind, value => HostTimeoutNumberFlow.ValueAt state kind value
  | .inr kind, value => HostTimeoutRootLoop.ValueAt false state kind value

def CauseAt (state : Stores) : Kind → CauseV → Prop
  | .inl kind, cause => HostTimeoutNumberFlow.CauseAt state kind cause
  | .inr kind, cause => HostTimeoutRootLoop.CauseAt false state kind cause

def CodeAt (state : Stores) : Kind → NCode → Prop
  | .inl kind, code => HostTimeoutNumberFlow.CodeAt state kind code
  | .inr kind, code => HostTimeoutRootLoop.CodeAt false state kind code

def model (view : HostTimeoutFlow.View) : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val)
    (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) Stores Kind where
  future := HostTimeoutNumberFlow.Future
  future_refl := (HostTimeoutNumberFlow.model view).future_refl
  future_trans := (HostTimeoutNumberFlow.model view).future_trans
  value := ValueAt
  cause := CauseAt
  code := CodeAt
  finalizer := (HostTimeoutNumberFlow.model view).finalizer
  success := by
    intro state kind value good
    cases kind with
    | inl input => exact HostTimeoutNumberFlow.CodeAt.success input value good
    | inr input => exact HostTimeoutRootLoop.CodeAt.success input value good
  failure := by
    intro state kind cause good
    cases kind with
    | inl input => exact HostTimeoutNumberFlow.CodeAt.failure input cause good
    | inr input => exact HostTimeoutRootLoop.CodeAt.failure input cause good

inductive Edge (view : HostTimeoutFlow.View) (state : Stores) : Kind → Kind → NCode → Prop
  | lower (input output : HostTimeoutNumberFlow.Kind) (code : NCode)
      (saved : AnswerFlow.SavedAt (HostTimeoutNumberFlow.model view) (HostTimeoutFlow.interpreter view).toPrimInterp
        state input output code) :
      Edge view state (.inl input) (.inl output) code
  | root (input output : HostTimeoutRootLoop.Kind) (code : NCode) (saved : HostTimeoutRootLoop.Edge false state input output code) :
      Edge view state (.inr input) (.inr output) code
  | answer (captured : Point) (fuel : Nat) (image : Image)
      (own : image.count = image.cleanups.length + 1) (n : Fin 4) (delay : Nat) (previous : Val)
      (count : image.count = n.val + 1) (body : NCode) :
      Edge view state (.inl (.formAfterCleanup image own)) (.inr (.published image own n delay previous))
        (.onSuccess body (.cont (HostTimeoutRootLoop.answerBinderPoint captured fuel n delay previous)))
  | mask (kind : Kind) (flag : Bool) : Edge view state kind kind (.setInterruptible flag)

/-- The lower result keeps its actual code and saved stack under the same kind injection. -/
theorem lower_result (view : HostTimeoutFlow.View) (state : Stores) (output : HostTimeoutNumberFlow.Kind)
    (code : NCode) (pushed : List NCode)
    (result : AnswerFlow.ResultAt (HostTimeoutNumberFlow.model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      state output code pushed) :
    AnswerFlow.FamilyResult (model view) (Edge view) state (.inl output) code pushed := by
  cases result with
  | mk _ input _ _ _ good stack =>
    exact ⟨.inl input, good, Path.map_objects Sum.inl (fun a b frame held => Edge.lower a b frame held)
      (AnswerFlow.stack_path (HostTimeoutNumberFlow.model view) (HostTimeoutFlow.interpreter view).toPrimInterp stack)⟩

/-- Root callbacks use the same native hook; their actual saved edges are not onExit frames. -/
theorem root_program_none (view : HostTimeoutFlow.View) (state : Stores) (input output : HostTimeoutRootLoop.Kind)
    (code : NCode) (saved : HostTimeoutRootLoop.Edge false state input output code) (target : Stores) (exit : ExitV) :
    AnswerFlow.programOf (model view) target code exit = none := by
  cases saved <;> rfl

/-- The root result retains its actual recursive edge path in the mixed stack. -/
theorem root_result (view : HostTimeoutFlow.View) (state : Stores) (output : HostTimeoutRootLoop.Kind)
    (code : NCode) (pushed : List NCode)
    (result : AnswerFlow.FamilyResult (HostTimeoutRootLoop.model false) (HostTimeoutRootLoop.Edge false) state output code pushed) :
    AnswerFlow.FamilyResult (model view) (Edge view) state (.inr output) code pushed := by
  obtain ⟨input, good, stack⟩ := result
  exact ⟨.inr input, good, Path.map_objects Sum.inr (fun a b frame held => Edge.root a b frame held) stack⟩

/-- A raw failed form retains its exact published heap without a plain-script failure restriction. -/
theorem published (state : Stores) (image : Image) (own : image.count = image.cleanups.length + 1)
    (n : Fin 4) (count : image.count = n.val + 1) (cause : CauseV)
    (good : HostTimeoutNumberFlow.CauseAt state (.formAfterCleanup image own) cause) :
    HostTimeoutRootLoop.Published false state image own n cause :=
  ⟨good, count, (by intro falseTrue; cases falseTrue), (by intro falseTrue; cases falseTrue)⟩

/-- Native finalizer and root callbacks share one actual ordered stack, without another pop traversal. -/
theorem family (view : HostTimeoutFlow.View) :
    AnswerFlow.SavedFamily (model view) (HostTimeoutFlow.interpreter view).toPrimInterp (Edge view) where
  skip := by
    intro state input output frame edge next future value good missing
    cases edge with
    | lower input output frame saved =>
      exact (AnswerFlow.saved_family (HostTimeoutNumberFlow.model view)
        (HostTimeoutFlow.interpreter view).toPrimInterp).skip state input output frame saved next future value good missing
    | root input output frame saved =>
      exact (HostTimeoutRootLoop.family false view).skip state input output frame saved next future value good missing
    | answer captured fuel image own n delay previous count body => cases missing
    | mask kind flag => exact good
  skipCause := by
    intro state input output frame edge next future cause good missing
    cases edge with
    | lower input output frame saved =>
      exact (AnswerFlow.saved_family (HostTimeoutNumberFlow.model view)
        (HostTimeoutFlow.interpreter view).toPrimInterp).skipCause state input output frame saved next future cause good missing
    | root input output frame saved =>
      exact (HostTimeoutRootLoop.family false view).skipCause state input output frame saved next future cause good missing
    | answer captured fuel image own n delay previous count body => exact published next image own n count cause good
    | mask kind flag => exact good
  answer := by
    intro state input output frame edge nextState future value provided next pushed good supplied absent arm
    cases edge with
    | lower input output frame saved =>
      cases saved with
      | mk _ _ _ _ _ _ answer _ _ _ =>
        exact lower_result view nextState output next pushed
          (answer nextState future value provided next pushed good supplied absent arm)
    | root input output frame saved =>
      exact root_result view nextState output next pushed
        ((HostTimeoutRootLoop.family false view).answer state input output frame saved
          nextState future value provided next pushed good supplied
          (AnswerFlow.programOf_none (HostTimeoutRootLoop.model false) nextState frame _ (fun _ => rfl)) arm)
    | answer captured fuel image own n delay previous count body =>
      obtain ⟨attemptExit, selected, heap, same⟩ := good
      rw [same] at heap
      change some ((HostTimeoutFlow.interpreter view).contA
        (.cont (HostTimeoutRootLoop.answerBinderPoint captured fuel n delay previous)) value, []) = some (next, pushed) at arm
      cases arm
      rw [HostTimeoutRootLoop.answer_callback]
      exact ⟨.inr (.published image own n delay previous),
        HostTimeoutRootLoop.CodeAt.success _ _
          (HostTimeoutRootLoop.BodyValue.answered (image.afterForm own attemptExit (.success value))
            value .none heap count), .nil _⟩
    | mask kind flag => cases arm
  cause := by
    intro state input output frame edge nextState future cause provided next pushed good supplied absent arm
    cases edge with
    | lower input output frame saved =>
      cases saved with
      | mk _ _ _ _ _ _ _ answer _ _ =>
        exact lower_result view nextState output next pushed
          (answer nextState future cause provided next pushed good supplied absent arm)
    | root input output frame saved =>
      exact root_result view nextState output next pushed
        ((HostTimeoutRootLoop.family false view).cause state input output frame saved
          nextState future cause provided next pushed good supplied
          (AnswerFlow.programOf_none (HostTimeoutRootLoop.model false) nextState frame _ (fun _ => rfl)) arm)
    | answer captured fuel image own n delay previous count body => cases arm
    | mask kind flag => cases arm
  program := by
    intro state input output frame edge nextState future exit next good found
    cases edge with
    | lower input output frame saved =>
      exact (AnswerFlow.saved_family (HostTimeoutNumberFlow.model view)
        (HostTimeoutFlow.interpreter view).toPrimInterp).program state input output frame saved
          nextState future exit next good found
    | root input output frame saved =>
      rw [root_program_none view state input output frame saved nextState exit] at found
      cases found
    | answer captured fuel image own n delay previous count body => cases found
    | mask kind flag => cases found
  discard := by
    intro state input output frame edge nextState future fiber cause delivered good armed interrupted skipped
    cases edge with
    | lower input output frame saved =>
      exact (AnswerFlow.saved_family (HostTimeoutNumberFlow.model view)
        (HostTimeoutFlow.interpreter view).toPrimInterp).discard state input output frame saved
          nextState future fiber cause delivered good armed interrupted skipped
    | root input output frame saved =>
      exact (HostTimeoutRootLoop.family false view).discard state input output frame saved
          nextState future fiber cause delivered good armed interrupted skipped
    | answer captured fuel image own n delay previous count body => cases armed
    | mask kind flag => cases armed

/-- The actual native form frame sits above the answer, catch, loop and finish suffix. -/
theorem form_stack (view : HostTimeoutFlow.View) (state : Stores) (captured : Point) (fuel : Nat)
    (n : Fin 4) (delay : Nat) (previous : Val) (image : Image)
    (own : image.count = image.cleanups.length + 1) (count : image.count = n.val + 1)
    (formBody catchBody : NCode) (loopPoint : Point) (root : HostTimeoutRootLoop.RootAt loopPoint)
    (finishPoint : Point) (source : HostTimeoutRootLoop.FinishAt finishPoint) (finishBody : NCode) :
    Path (Edge view state) (.inl (.cleanupExit image own)) (.inr .root)
      [.onExit formBody (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) false,
       .onSuccess (resolve HostTimeoutSource.program
         (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous))
         (.cont (HostTimeoutRootLoop.answerBinderPoint captured fuel n delay previous)),
       .onFailure catchBody (.caughtError (HostTimeoutRootLoop.catchPoint captured (fuel + 4) n delay previous)),
       .whileLoop (.loop loopPoint) (HostTimeoutSource.cursor n delay .none previous),
       .onSuccess finishBody (.cont finishPoint)] :=
  .cons (.lower _ _ _ (HostTimeoutNumberFormFamily.form_saved view state image own
      captured fuel delay n previous count formBody))
    (.cons (.answer captured fuel image own n delay previous count _)
      (Path.map_objects Sum.inr (fun a b frame held => Edge.root a b frame held)
        (HostTimeoutRootLoop.caught_stack false state captured (fuel + 3) n delay previous image own catchBody
          loopPoint root finishPoint source finishBody)))

/-- A restore push retains its native cleanup permission above the actual recursive root suffix. -/
theorem restore_push (view : HostTimeoutFlow.View) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (attemptExit selected : ExitV) (program : NCode)
    (fiber : HostTimeoutFrames.NativeFrame) (output : Kind)
    (current : fiber.current = .onSuccess program (.restore selected))
    (body : HostTimeoutNumberFlow.CodeAt state (.unit (image.afterForm own attemptExit selected)) program)
    (stack : Path (Edge view state) (.inl (.formAfterCleanup image own)) output fiber.stack) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model view) (Edge view) state output after.current after.stack := by
  obtain ⟨after, events, ran, code, path⟩ := AnswerFlow.push_success_path (model view)
    (HostTimeoutFlow.interpreter view).toPrimInterp state (.inl (.unit (image.afterForm own attemptExit selected)))
    (.inl (.formAfterCleanup image own)) output (Edge view) fiber program (.restore selected)
    current body (.lower _ _ _ (HostTimeoutNumberFormFamily.restore_saved view state image own attemptExit selected program)) stack
  exact ⟨after, events, ran, .inl (.unit (image.afterForm own attemptExit selected)), code, path⟩

/-- The actual native form branch installs its cleanup program above the recursive root suffix. -/
theorem native_form (machine : Effect4.Program.NativeMachine) (fiber : HostTimeoutEvaluation.NativeFiber)
    (yielding : Bool) (input output : Kind) (exit : ExitV)
    (captured : Point) (fuel delay : Nat) (n : Fin 4) (previous : Val) (body : NCode)
    (good : AnswerFlow.ExitAt (model machine.completedExits) machine.state input exit)
    (stack : Path (Edge machine.completedExits machine.state) input output fiber.frame.stack)
    (chosen : (fiber.frame.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).answer =
        .frame (.onExit body (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) false)) :
    let result := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter machine.completedExits) machine fiber yielding exit
    result.machine.state = machine.state ∧
      AnswerFlow.FamilyResult (model machine.completedExits) (Edge machine.completedExits) machine.state output
        result.fiber.frame.current result.fiber.frame.stack := by
  cases exit with
  | success value =>
    let selected := (fiber.frame.getCont .contA false).deliveredExit (.success value)
    let program := resolve HostTimeoutSource.program
      (HostTimeoutNumberCallbacks.completedPoint {captured with completed := machine.completedExits} fuel delay n previous selected)
    have hook : (HostTimeoutFlow.interpreter machine.completedExits).finalizerProgram
        (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) selected = some program :=
      HostTimeoutNumberFinalizers.form_program machine.completedExits captured fuel delay n previous selected
    have installed : (model machine.completedExits).finalizer machine.state
        (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) selected =
      some (finalizerCode (HostTimeoutFlow.interpreter machine.completedExits) selected program) := by
      change (((HostTimeoutFlow.interpreter machine.completedExits).finalizerProgram
        (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) selected).map
          (finalizerCode (HostTimeoutFlow.interpreter machine.completedExits) selected)) = _
      rw [hook, Option.map_some]
    exact AnswerFlow.External.finalizer_step (model machine.completedExits)
      (HostTimeoutFlow.interpreter machine.completedExits).toPrimInterp (Edge machine.completedExits)
      (family machine.completedExits) (fun state kind => .mask kind true)
      (HostTimeoutFlow.interpreter machine.completedExits) machine.state input output machine fiber yielding (.success value)
      body (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) false program good stack chosen hook installed
  | failure cause =>
    let selected := (fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)
    let program := resolve HostTimeoutSource.program
      (HostTimeoutNumberCallbacks.completedPoint {captured with completed := machine.completedExits} fuel delay n previous selected)
    have hook : (HostTimeoutFlow.interpreter machine.completedExits).finalizerProgram
        (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) selected = some program :=
      HostTimeoutNumberFinalizers.form_program machine.completedExits captured fuel delay n previous selected
    have installed : (model machine.completedExits).finalizer machine.state
        (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) selected =
      some (finalizerCode (HostTimeoutFlow.interpreter machine.completedExits) selected program) := by
      change (((HostTimeoutFlow.interpreter machine.completedExits).finalizerProgram
        (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) selected).map
          (finalizerCode (HostTimeoutFlow.interpreter machine.completedExits) selected)) = _
      rw [hook, Option.map_some]
    exact AnswerFlow.External.finalizer_step (model machine.completedExits)
      (HostTimeoutFlow.interpreter machine.completedExits).toPrimInterp (Edge machine.completedExits)
      (family machine.completedExits) (fun state kind => .mask kind true)
      (HostTimeoutFlow.interpreter machine.completedExits) machine.state input output machine fiber yielding (.failure cause)
      body (.fin (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous)) false program good stack chosen hook installed

end Test.Dogfood.Proofs.HostTimeoutNativeRootFamily

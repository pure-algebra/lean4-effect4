import Test.Dogfood.Scenario.Atomic.StageInterrupt
import Effect4.Laws.Machine.AnswerFlowEmpty

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Consumer: the actual request native terminal producer for `Atomic.Store.shop_stages`.
Actual recorded interruptions justify deferred and restoring-mask failures at the retained saved suffix.
The existing contextual return proof owns the continuation walk.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Generated masks retain the owner of their actual source edge's output class. -/
theorem hook_mask (root : NativeEff) (table : RowTable) (owner : Nat) :
    Contextual.HookMask (Edge root table owner) := by
  intro world input output code held fiber pushed
  exact mask_edge root table owner world output true (edge_owned root table owner world input output code held).2

/-- Actual recorded causes supply the contextual handler-discard admission. -/
theorem recorded_allowed (world : StageWorld.World)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (recorded : Recorded fiber) :
    StageFinalizer.Allowed world fiber.interruptedCause := by
  intro cause member
  exact (recorded cause (Option.mem_def.mp member)).1

/-- Adding an actual recorded interrupt retains every request cause permission. -/
theorem recorded_absorbs (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (recorded : Recorded fiber) :
    Contextual.AbsorbsInterrupt (model root table owner view) world fiber.interruptedCause := by
  intro interrupted actual kind cause good
  exact cause_combine_untyped world kind cause interrupted good (recorded interrupted actual).1

/-- An actual replacing mask uses its recorded cause and exact retained suffix for either exit arm. -/
theorem replacement_frame (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (input output : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (demand : Effect4.Arm) (skip : Bool)
    (carried : Option CauseV) (saved : Effect4.Contracts.Path (Edge root table owner world) input output fiber.stack)
    (recorded : Recorded fiber) (next : NCode)
    (found : (fiber.getCont demand skip carried).answer = .replacement next) :
    FamilyResult (model root table owner view) (Edge root table owner) world output next
      (fiber.getCont demand skip carried).fiber.stack := by
  obtain ⟨incoming, middle, head, rest, scratch, callback, suffix, incomingGood, empty, same, actual, stack⟩ :=
    External.getCont_replacement_hooked (Edge root table owner) (hook_mask root table owner)
      (fun _ => True) world demand skip (fun _ _ _ _ _ _ _ _ held => held)
      input output fiber carried True.intro saved next found
  obtain ⟨cause, mask, recordedAt, failure⟩ := External.ensure_replacement_recorded head scratch next actual
  have permitted := recorded cause (same.symm.trans recordedAt)
  refine ⟨middle, ?_, ?_⟩
  · rw [failure]
    exact .failure (untyped_marked_cause world middle cause permitted.1 permitted.2)
  · rw [stack]
    apply Effect4.Contracts.Path.append _ suffix
    exact Contextual.Hooked.ensure_path (model root table owner view) (Edge root table owner)
      world middle middle head scratch
      (hook_mask root table owner world incoming middle head callback scratch)
      (by rw [empty]; exact .nil middle)
/-- An actual deferred value return uses the recorded interruption before touching the suffix. -/
theorem value_deferred (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (input output : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (saved : Effect4.Contracts.Path (Edge root table owner world) input output fiber.stack)
    (recorded : Recorded fiber) (consistent : Guard.DeferredCause.DeferredCause fiber) (cause : CauseV)
    (found : (fiber.getCont .contA false).answer = .deferred cause) :
    FamilyResult (model root table owner view) (Edge root table owner) world output (.failure cause)
      (fiber.getCont .contA false).fiber.stack := by
  cases deferred : fiber.deferredInterrupt with
  | false => exact (FrameFiber.getCont_never_defers fiber .contA false cause deferred found).elim
  | true =>
    rw [FrameFiber.getCont_deferred fiber .contA deferred] at found ⊢
    cases found
    cases prior : fiber.interruptedCause with
    | none =>
      have present := consistent deferred
      rw [prior] at present
      cases present
    | some cause =>
      have permitted := recorded cause prior
      refine ⟨input, ?_, saved⟩
      apply CodeAt.failure
      simpa only [FrameFiber.pendingCause, prior, Option.getD_some] using
        untyped_marked_cause world input cause permitted.1 permitted.2

/-- A pure actual value return reuses the contextual shared pop proof at the same finalized path. -/
theorem resume_value (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (input output : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (good : ValueAt world input value) (saved : Effect4.Contracts.Path (Edge root table owner world) input output fiber.stack)
    (recorded : Recorded fiber) (consistent : Guard.DeferredCause.DeferredCause fiber)
    (pure : ∀ selected, (fiber.getCont .contA false).answer = .frame selected →
      programOf (model root table owner view) world selected (.success value) = none) :
    External.RunningStep (model root table owner view) (Edge root table owner) world output
      (fiber.resumeValue (interpAt root view table).toPrimInterp value (some (.success value))).1 := by
  apply External.resume_value_local (model root table owner view) (Edge root table owner)
    (interpAt root view table).toPrimInterp StageFinalizer.Allowed (family root table owner view)
    (hook_mask root table owner) world input output fiber value (some (.success value)) good saved
  · exact value_deferred root table owner view world input output fiber saved recorded consistent
  · exact replacement_frame root table owner view world input output fiber .contA false none saved recorded
  · intro incoming allowed exit member
    cases member
    exact allowed
  · exact pure

/-- A pure actual failure return uses its recorded-cause admission and contextual shared pop proof. -/
theorem resume_cause (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (input output : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (good : CauseAt world input cause) (saved : Effect4.Contracts.Path (Edge root table owner world) input output fiber.stack)
    (recorded : Recorded fiber)
    (pure : ∀ selected, (fiber.getCont .contE true (some cause)).answer = .frame selected →
      programOf (model root table owner view) world selected
        ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = none) :
    External.RunningStep (model root table owner view) (Edge root table owner) world output
      (fiber.resumeCause (interpAt root view table).toPrimInterp cause (some (.failure cause))).1 := by
  apply External.resume_cause_local (model root table owner view) (Edge root table owner)
    (interpAt root view table).toPrimInterp StageFinalizer.Allowed (family root table owner view)
    (hook_mask root table owner) world input output fiber cause (some (.failure cause)) good saved
    (recorded_absorbs root table owner view world fiber recorded) (recorded_allowed world fiber recorded)
  · intro reason found
    simp only [FrameFiber.getCont, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false] at found
    rw [FrameFiber.popFrom_answer_cause] at found
    exact (FrameFiber.popFrom_answer_ne_deferred .contE true reason _ _ found).elim
  · exact replacement_frame root table owner view world input output fiber .contE true (some cause) saved recorded
  · intro incoming delivered carried allowed exit member
    simp only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] at member
    cases member
    exact allowed
  · intro selected chosen delivered carried
    simpa only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] using pure selected chosen

/-- A whole actual value return carries the finalized permission even when its suffix drains. -/
theorem value_step (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (input output : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (good : ValueAt world input value) (saved : Effect4.Contracts.Path (Edge root table owner world) input output fiber.stack)
    (recorded : Recorded fiber) (consistent : Guard.DeferredCause.DeferredCause fiber)
    (pure : ∀ selected, (fiber.getCont .contA false).answer = .frame selected →
      programOf (model root table owner view) world selected (.success value) = none) :
    FamilyStep (model root table owner view) (Edge root table owner) world output
      (fiber.resumeValue (interpAt root view table).toPrimInterp value (some (.success value))).1 := by
  have running := resume_value root table owner view world input output fiber value good saved recorded consistent pure
  cases actual : (fiber.resumeValue (interpAt root view table).toPrimInterp value (some (.success value))).1 with
  | running frame => rw [actual] at running; exact running
  | finished exit =>
    exact Contextual.resume_value_finished (model root table owner view)
      (interpAt root view table).toPrimInterp (Edge root table owner) StageFinalizer.Allowed
      (family root table owner view) world input output fiber value good saved exit actual

/-- A whole actual failure return carries its delivered finalized permission when its suffix drains. -/
theorem cause_step (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (input output : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (good : CauseAt world input cause) (saved : Effect4.Contracts.Path (Edge root table owner world) input output fiber.stack)
    (recorded : Recorded fiber)
    (pure : ∀ selected, (fiber.getCont .contE true (some cause)).answer = .frame selected →
      programOf (model root table owner view) world selected
        ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = none) :
    FamilyStep (model root table owner view) (Edge root table owner) world output
      (fiber.resumeCause (interpAt root view table).toPrimInterp cause (some (.failure cause))).1 := by
  have running := resume_cause root table owner view world input output fiber cause good saved recorded pure
  cases actual : (fiber.resumeCause (interpAt root view table).toPrimInterp cause (some (.failure cause))).1 with
  | running frame => rw [actual] at running; exact running
  | finished exit =>
    exact Contextual.resume_cause_finished (model root table owner view)
      (interpAt root view table).toPrimInterp (Edge root table owner) StageFinalizer.Allowed
      (family root table owner view) world input output fiber cause good saved
      (recorded_absorbs root table owner view world fiber recorded) (recorded_allowed world fiber recorded) exit actual

/-- Native terminal dispatch retains the actual finalized exit or its installed finalizer frame. -/
theorem native_exit (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (input output : StageWorld.Kind)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (current : fiber.frame.current = Prim.ofExit exit) (good : ExitAt (model root table owner view) world input exit)
    (saved : Effect4.Contracts.Path (Edge root table owner world) input output fiber.frame.stack)
    (recorded : Recorded fiber.frame) (consistent : Guard.DeferredCause.DeferredCause fiber.frame) :
    External.Native.ResultAt (model root table owner view) (Edge root table owner) world output
      (evaluatePrim.finalizerOr (interpAt root view table) machine fiber yielding exit) := by
  apply External.Native.finalizer_dispatch (interpAt root view table) machine fiber yielding exit
    (External.Native.ResultAt (model root table owner view) (Edge root table owner) world output)
  · intro absent
    apply External.Native.step_frame_result (model root table owner view) (interpAt root view table)
      (Edge root table owner) world output machine fiber yielding
    cases exit with
    | success value =>
      change fiber.frame.current = .success value at current
      simp only [FrameFiber.step, current]
      apply value_step root table owner view world input output fiber.frame value good saved recorded consistent
      intro selected chosen
      cases selected
      case onExit body name flag =>
        change ((interpAt root view table).finalizerProgram name (.success value)).map _ = none
        cases actual : (interpAt root view table).finalizerProgram name (.success value) with
        | none => rfl
        | some program => exact (absent body name flag program chosen actual).elim
      all_goals rfl
    | failure cause =>
      change fiber.frame.current = .failure cause at current
      simp only [FrameFiber.step, current]
      apply cause_step root table owner view world input output fiber.frame cause good saved recorded
      intro selected chosen
      cases selected
      case onExit body name flag =>
        change ((interpAt root view table).finalizerProgram name
          ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause))).map _ = none
        cases actual : (interpAt root view table).finalizerProgram name
            ((fiber.frame.getCont .contE true (some cause)).deliveredExit (.failure cause)) with
        | none => rfl
        | some program => exact (absent body name flag program chosen actual).elim
      all_goals rfl
  · intro body name flag program chosen installed
    cases exit
    all_goals
      have result := Contextual.Hooked.finalizer_step (admitted := recorded_allowed world fiber.frame recorded)
        (model root table owner view) (interpAt root view table).toPrimInterp (Edge root table owner)
        StageFinalizer.Allowed (family root table owner view) (hook_mask root table owner)
        (interpAt root view table) world input output machine fiber yielding _ body name flag program
        good (fun _ _ => recorded_absorbs root table owner view world fiber.frame recorded) saved chosen installed
        (by change ((interpAt root view table).finalizerProgram name _).map _ = _; rw [installed]; rfl)
      unfold External.Native.ResultAt
      unfold evaluatePrim.finalizerOr at result ⊢
      dsimp only at result ⊢
      rw [chosen] at result ⊢
      dsimp only at result ⊢
      rw [installed] at result ⊢
      exact result.2

end Test.Dogfood.Scenario.Atomic.StageGraph

import Test.Dogfood.Scenario.Atomic.RootActions
import Effect4.Laws.Machine.AnswerFlowEmpty

/-!
Concept: store-typing R4.
Consumer: the actual Atomic root native terminal result and coupled stage history.
The root ignores its final result while its saved binders retain captured handles and allocation counters.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- A root hook inserts a mask only at the owned output of its actual saved edge. -/
theorem hook_mask (root : NativeEff) (table : RowTable) : Contextual.HookMask (Edge root table) := by
  intro world input output code edge fiber pushed
  cases edge with
  | saved held => exact mask_edge root table world output held.outputOwned true
  | mapped ready held => exact mask_edge root table world .ordinary True.intro true

/-- An actual replacing root hook retains the selected owned class and exact older suffix. -/
theorem replacement_frame (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (input output : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (demand : Effect4.Arm) (skip : Bool)
    (carried : Option CauseV) (saved : Effect4.Contracts.Path (Edge root table world) input output fiber.stack)
    (next : NCode) (found : (fiber.getCont demand skip carried).answer = .replacement next) :
    FamilyResult (model root table view) (Edge root table) world output next
      (fiber.getCont demand skip carried).fiber.stack := by
  obtain ⟨incoming, middle, head, rest, scratch, callback, suffix, good, empty, same, actual, stack⟩ :=
    External.getCont_replacement_hooked (Edge root table) (hook_mask root table) (fun _ => True)
      world demand skip (fun _ _ _ _ _ _ _ _ held => held) input output fiber carried True.intro saved next found
  obtain ⟨cause, failure⟩ := External.ensure_replacement_failure head scratch next actual
  refine ⟨middle, ?_, ?_⟩
  · rw [failure]
    exact .failure
  · rw [stack]
    apply Effect4.Contracts.Path.append _ suffix
    exact Contextual.Hooked.ensure_path (model root table view) (Edge root table) world middle middle head scratch
      (hook_mask root table world incoming middle head callback scratch) (by rw [empty]; exact .nil middle)

/-- Root deferred interruption retains its actual older source binders. -/
theorem value_deferred (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (input output : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (saved : Effect4.Contracts.Path (Edge root table world) input output fiber.stack)
    (cause : CauseV) (found : (fiber.getCont .contA false).answer = .deferred cause) :
    FamilyResult (model root table view) (Edge root table) world output (.failure cause)
      (fiber.getCont .contA false).fiber.stack := by
  cases deferred : fiber.deferredInterrupt with
  | false => exact (FrameFiber.getCont_never_defers fiber .contA false cause deferred found).elim
  | true =>
    rw [FrameFiber.getCont_deferred fiber .contA deferred] at found ⊢
    cases found
    exact ⟨input, .failure, saved⟩

/-- The actual root value return keeps its source binders or finishes with its ignored result. -/
theorem value_step (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (input : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val)
    (good : ValueAt world input value) (saved : Effect4.Contracts.Path (Edge root table world) input .ordinary fiber.stack)
    (pure : ∀ selected, (fiber.getCont .contA false).answer = .frame selected →
      programOf (model root table view) world selected (.success value) = none) :
    FamilyStep (model root table view) (Edge root table) world .ordinary
      (fiber.resumeValue (interpAt root view table).toPrimInterp value (some (.success value))).1 := by
  have running : External.RunningStep (model root table view) (Edge root table) world .ordinary
      (fiber.resumeValue (interpAt root view table).toPrimInterp value (some (.success value))).1 := by
    apply External.resume_value_local (model root table view) (Edge root table) (interpAt root view table).toPrimInterp
      (fun _ _ => True) (SavedFamily.contextual _ _ _ _ (family root table view)) (hook_mask root table)
      world input .ordinary fiber value (some (.success value)) good saved
    · exact value_deferred root table view world input .ordinary fiber saved
    · exact replacement_frame root table view world input .ordinary fiber .contA false none saved
    · intro incoming good exit member
      cases member
      exact good
    · exact pure
  cases actual : (fiber.resumeValue (interpAt root view table).toPrimInterp value (some (.success value))).1 with
  | running frame => rw [actual] at running; exact running
  | finished exit => cases exit <;> exact True.intro

/-- The actual root failure return keeps its source binders or finishes with its ignored failure. -/
theorem cause_step (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (input : StageWorld.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (saved : Effect4.Contracts.Path (Edge root table world) input .ordinary fiber.stack)
    (pure : ∀ selected, (fiber.getCont .contE true (some cause)).answer = .frame selected →
      programOf (model root table view) world selected
        ((fiber.getCont .contE true (some cause)).deliveredExit (.failure cause)) = none) :
    FamilyStep (model root table view) (Edge root table) world .ordinary
      (fiber.resumeCause (interpAt root view table).toPrimInterp cause (some (.failure cause))).1 := by
  have running : External.RunningStep (model root table view) (Edge root table) world .ordinary
      (fiber.resumeCause (interpAt root view table).toPrimInterp cause (some (.failure cause))).1 := by
    apply External.resume_cause_local (model root table view) (Edge root table) (interpAt root view table).toPrimInterp
      (fun _ _ => True) (SavedFamily.contextual _ _ _ _ (family root table view)) (hook_mask root table)
      world input .ordinary fiber cause (some (.failure cause)) True.intro saved (fun _ _ _ _ _ => True.intro) True.intro
    · intro reason found
      simp only [FrameFiber.getCont, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false] at found
      rw [FrameFiber.popFrom_answer_cause] at found
      exact (FrameFiber.popFrom_answer_ne_deferred .contE true reason _ _ found).elim
    · exact replacement_frame root table view world input .ordinary fiber .contE true (some cause) saved
    · intro incoming delivered carried good exit member
      simp only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] at member
      cases member
      exact True.intro
    · intro selected chosen delivered carried
      simpa only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some] using pure selected chosen
  cases actual : (fiber.resumeCause (interpAt root view table).toPrimInterp cause (some (.failure cause))).1 with
  | running frame => rw [actual] at running; exact running
  | finished exit => cases exit <;> exact True.intro
/-- Native root terminal dispatch retains its owned saved path or its ignored completed exit. -/
theorem native_exit (root : NativeEff) (table : RowTable) 
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (input : StageWorld.Kind)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (current : fiber.frame.current = Prim.ofExit exit) (good : ExitAt (model root table view) world input exit)
    (saved : Effect4.Contracts.Path (Edge root table world) input .ordinary fiber.frame.stack)
    :
    External.Native.ResultAt (model root table view) (Edge root table) world .ordinary
      (evaluatePrim.finalizerOr (interpAt root view table) machine fiber yielding exit) := by
  apply External.Native.finalizer_dispatch (interpAt root view table) machine fiber yielding exit
    (External.Native.ResultAt (model root table view) (Edge root table) world .ordinary)
  · intro absent
    apply External.Native.step_frame_result (model root table view) (interpAt root view table)
      (Edge root table) world .ordinary machine fiber yielding
    cases exit with
    | success value =>
      change fiber.frame.current = .success value at current
      simp only [FrameFiber.step, current]
      apply value_step root table view world input fiber.frame value good saved
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
      apply cause_step root table view world input fiber.frame cause saved
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
      have result := Contextual.Hooked.finalizer_step (admitted := True.intro)
        (model root table view) (interpAt root view table).toPrimInterp (Edge root table)
        (fun _ _ => True) (SavedFamily.contextual _ _ _ _ (family root table view)) (hook_mask root table)
        (interpAt root view table) world input .ordinary machine fiber yielding _ body name flag program
        good (fun _ _ _ _ _ _ _ => True.intro) saved chosen installed
        (by change ((interpAt root view table).finalizerProgram name _).map _ = _; rw [installed]; rfl)
      unfold External.Native.ResultAt
      unfold evaluatePrim.finalizerOr at result ⊢
      dsimp only at result ⊢
      rw [chosen] at result ⊢
      dsimp only at result ⊢
      rw [installed] at result ⊢
      exact result.2

end Test.Dogfood.Scenario.Atomic.RootGraph

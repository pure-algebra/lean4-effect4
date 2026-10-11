import Effect4.Laws.Program.ReleaseCustody.RuntimeShape
import Effect4.Laws.Program.NativeEvaluation
import Effect4.Laws.Machine.MaskRuns

/-!
Concept: scope-lifetime-finalization, R11.
Question: native evaluator sequencing serves Execution.history and Workers.Assertions.releases_step.
Reach: actual native evaluator outputs under existing source ownership and saved-frame sequencing.
Limit: evaluator sequencing alone establishes neither command funding nor admitted-history closure.
Unlock: the actual scheduler retains stable parked and overwrite-command stacks.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativeSequencing
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Sequencing
open Effect4.Program.ReleaseCustody.PopSequencing
open Effect4.Program.ReleaseCustody.RuntimeShape
abbrev Interp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev Action := WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- A clean residual stack retains every reply and command boundary.
Consumer: the opaque native action and park evaluator cases. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem returned_clean (it : Iteration) (held : NoAdd it.fiber.frame.stack)
    (finished : ∀ exit, it.outcome = .finished exit → it.fiber.frame.stack = []) : Returned it :=
  ⟨⟨.clean _ _ held, fun _ => .clean _ held⟩, fun _ => held, finished⟩

/-- The native frame rule consumes the source predicate's existing registration-body field.
Consumer: the primitive evaluator delegation below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem frame_step (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (fiber : Effect4.Program.ReleaseCustody.Pop.Frame)
    (held : Kept fiber.current fiber.stack) (source : SourceScope.FrameAt root fiber) :
    match (fiber.step (interpAt root completed table).toPrimInterp).1 with
    | .running next => Kept next.current next.stack
    | .finished _ => True := by
  apply FrameSequencing.step root completed table fiber held
  intro body acquired fin same
  exact SourceScope.registration_body root body acquired fin (same ▸ source.1)

/-- The actual primitive delegate retains both its running and finished boundary shapes.
Consumer: the native evaluator's ordinary cases. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem step_frame (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) (held : Kept fiber.frame.current fiber.frame.stack)
    (source : SourceScope.FrameAt root fiber.frame) :
    Returned (evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding) := by
  have sequence := frame_step root completed table fiber.frame held source
  unfold evaluatePrim.stepFrame
  cases found : fiber.frame.step (interpAt root completed table).toPrimInterp with
  | mk step events =>
    rw [found] at sequence
    cases step with
    | running next =>
      refine ⟨⟨sequence, ?_⟩, ?_, ?_⟩
      · intro parked
        exact False.elim (parked active)
      · intro wrong
        cases wrong
      · intro exit wrong
        cases wrong
    | finished exit =>
      have empty := Effect4.Machine.step_finished_stack (interpAt root completed table).toPrimInterp
        fiber.frame exit (congrArg Prod.fst found)
      apply returned_clean
      · rw [show (evaluatePrim.finishFrame m fiber yielding (.finished exit) events []).fiber.frame.stack =
            (frameExitState fiber.frame).stack from rfl, empty]
        exact noAdd_empty
      · intro _ _
        exact empty

/-- Every fiber action changes the local saved stack only by administrative frames.
Consumer: the actual opaque action evaluator's parked and command boundaries. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem action_noAdd (interp : Interp) (m : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (action : Action) (held : NoAdd fiber.frame.stack) :
    NoAdd (evaluatePrim.withFiber interp m fiber yielding action).fiber.frame.stack := by
  cases action <;>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, spawn, start, countdownParkEdits,
      beginRace, RunFiber.park, FrameFiber.uninterruptible, FrameFiber.interruptibleRegion,
      FrameFiber.setFiberInterruptible]
  all_goals repeat' split
  all_goals aesop (add safe apply [noAdd_mask, noAdd_asyncFinalizer])

/-- No fiber action returns the finished-frame boundary.
Consumer: action sequencing exposes the actual command boundary without a synthetic finish. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem action_not_finished (interp : Interp) (m : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (action : Action) (exit : ExitV) :
    (evaluatePrim.withFiber interp m fiber yielding action).outcome ≠ .finished exit := by
  cases action <;>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, spawn, start, beginRace]
  all_goals dsimp (config := { zetaDelta := true, failIfUnchanged := false }) only
  all_goals repeat' split
  all_goals dsimp (config := { zetaDelta := true, failIfUnchanged := false }) only
  all_goals aesop

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem action_returned (interp : Interp) (m : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (action : Action) (held : NoAdd fiber.frame.stack) :
    Returned (evaluatePrim.withFiber interp m fiber yielding action) :=
  returned_clean _ (action_noAdd interp m fiber yielding action held)
    (fun exit wrong => False.elim (action_not_finished interp m fiber yielding action exit wrong))

/-- Selecting an exit finalizer leaves no response-sensitive registration beneath it.
Consumer: native program finalizers and scoped-close cleanup. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem exit_pop_noAdd (fiber : Effect4.Program.ReleaseCustody.Pop.Frame)
    (held : Kept fiber.current fiber.stack) (exit : ExitV)
    (body : NCode) (name : EffName) (flag : Bool)
    (found : (fiber.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).answer =
        .frame (.onExit body name flag)) :
    NoAdd (fiber.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).fiber.stack := by
  cases exit
  · exact getCont_value_finalizer fiber held body name flag found
  · exact getCont_cause_kept fiber _ held

/-- Program finalizers run on a clean residual stack after the actual continuation pop.
Consumer: success and failure evaluation in the native interpreter. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem finalizer_returned (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (fiber : Fiber) (yielding : Bool) (exit : ExitV)
    (active : fiber.parked = .notParked) (held : Kept fiber.frame.current fiber.frame.stack)
    (source : SourceScope.FrameAt root fiber.frame) :
    Returned (evaluatePrim.finalizerOr (interpAt root completed table) m fiber yielding exit) := by
  have popClean := exit_pop_noAdd fiber.frame held exit
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · rename_i body name flag found
      have clean := popClean body name flag found
      split
      · apply returned_clean
        · exact clean
        · intro exit wrong
          cases wrong
      · exact step_frame root completed table m fiber yielding active held source
    · exact step_frame root completed table m fiber yielding active held source

/-- The stateful scoped callback also starts cleanup only after the registration is passed.
Consumer: native scoped-success and scoped-failure evaluation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scoped_exit_returned (root : NativeEff) (m : NativeMachine) (fiber : Fiber)
    (yielding : Bool) (exit : ExitV)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (fallback : Returned (evaluatePrim (interpAt root m.completedExits) m fiber yielding)) :
    Returned (exitScoped root m fiber yielding exit) := by
  have popClean := exit_pop_noAdd fiber.frame held exit
  cases exit <;> unfold exitScoped <;> dsimp only
  all_goals
    split
    · rename_i body previous scope flag found
      have clean := popClean body (.scopedExit previous scope) flag found
      split
      · apply returned_clean _ clean
        intro exit wrong
        cases wrong
      · rename_i next program found
        cases program <;> apply returned_clean _ clean
        all_goals intro exit wrong; cases wrong
    · exact fallback

/-- Countdown parks add only the actual cancellation finalizer to an already clean stack.
Consumer: suspended await-all and join evaluator cases. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem countdown_noAdd (interp : Interp) (m : NativeMachine) (fiber : Fiber)
    (targets : List FiberId) (held : NoAdd fiber.frame.stack) :
    NoAdd (countdownPark interp m fiber targets Resume.exitsValue).2.1.frame.stack :=
  action_noAdd interp m fiber false (.awaitAll targets) held

/-- A native primitive evaluation retains sequencing at every park and returned command.
Consumer: the stateful native evaluator and actual Workers command loop. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem primitive_returned (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (m : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) (held : Kept fiber.frame.current fiber.frame.stack)
    (source : SourceScope.FrameAt root fiber.frame) :
    Returned (evaluatePrim (interpAt root completed table) m fiber yielding) := by
  have ordinary := step_frame root completed table m fiber yielding active held source
  have absent {code : NCode} (same : fiber.frame.current = code)
      (notAdd : ∀ fin, ¬ AddPhase fin code) (notYield : ¬ YieldPhase code) : NoAdd fiber.frame.stack :=
    opaque_noAdd (same ▸ held) notAdd notYield
  cases current : fiber.frame.current
  case success value =>
    have park : (interpAt root completed table).parkOf (.success value) = none := rfl
    simp only [evaluatePrim, current, park]
    change Returned (evaluatePrim.finalizerOr (interpAt root completed table) m fiber yielding (.success value))
    exact finalizer_returned root completed table m fiber yielding _ active held source
  case failure cause =>
    have park : (interpAt root completed table).parkOf (.failure cause) = none := rfl
    simp only [evaluatePrim, current, park]
    change Returned (evaluatePrim.finalizerOr (interpAt root completed table) m fiber yielding (.failure cause))
    exact finalizer_returned root completed table m fiber yielding _ active held source
  case yieldNowWith priority =>
    simp only [evaluatePrim, current]
    have stable := yield_stable (current ▸ held)
    refine ⟨⟨stable_value stable _, fun _ => stable⟩, ?_, ?_⟩
    · intro wrong; cases wrong
    · intro exit wrong; cases wrong
  case async register signal cancel =>
    have clean := async_noAdd register signal cancel (current ▸ held)
    simp only [evaluatePrim, current]
    split
    · apply returned_clean _ clean
      intro exit wrong; cases wrong
    · split
      · apply returned_clean _ (noAdd_asyncFinalizer _ clean)
        intro exit wrong; cases wrong
      · apply returned_clean _ clean
        intro exit wrong; cases wrong
  case withFiber thunk =>
    have park : (interpAt root completed table).parkOf (.withFiber thunk) = none := rfl
    have clean := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [evaluatePrim, current, park]
    split
    · exact action_returned _ m fiber yielding _ clean
    · exact ordinary
  case sync thunk =>
    have park : (interpAt root completed table).parkOf (.sync thunk) = none := rfl
    simp only [evaluatePrim, current, park]
    split
    all_goals
      refine ⟨⟨value_response held _, ?_⟩, ?_, ?_⟩
      · intro parked; exact False.elim (parked active)
      · intro wrong; cases wrong
      · intro exit wrong; cases wrong
  case suspend thunk =>
    have clean := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [evaluatePrim, current]
    cases park : (interpAt root completed table).parkOf (.suspend thunk) with
    | none => simpa only [park] using ordinary
    | some result =>
      cases result with
      | error cause =>
        dsimp only
        apply returned_clean _ clean
        intro exit wrong; cases wrong
      | ok kind =>
        cases kind with
        | race rid =>
          dsimp only
          unfold registerRace
          split
          all_goals apply returned_clean _ clean
          all_goals intro exit wrong; cases wrong
        | awaitAll targets =>
          dsimp only
          apply returned_clean _ (countdown_noAdd _ m fiber targets clean)
          intro exit wrong
          split at wrong <;> cases wrong
        | join target mode =>
          dsimp only
          split
          · apply returned_clean _ clean
            intro exit wrong; cases wrong
          · split
            · apply returned_clean _ clean
              intro exit wrong; cases wrong
            · apply returned_clean _ (noAdd_asyncFinalizer _ clean)
              intro exit wrong; cases wrong
  all_goals
    simp only [evaluatePrim, current]
    exact ordinary

/-- Native scoped entry and both stateful exit routes retain the same returned shape.
Consumer: the actual command loop's evaluator premise. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem native_returned (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) (held : Kept fiber.frame.current fiber.frame.stack)
    (source : SourceScope.FrameAt root fiber.frame) :
    Returned (evaluateNative root m fiber yielding table) := by
  unfold evaluateNative
  split
  · rename_i point current
    have clean := opaque_noAdd (current ▸ held)
      (by intro fin phase; cases phase) (by intro phase; cases phase)
    split
    · apply returned_clean _ clean
      intro exit wrong; cases wrong
    · exact primitive_returned root m.completedExits table m fiber yielding active held source
  · exact scoped_exit_returned root m fiber yielding _ held
      (primitive_returned root m.completedExits [] m fiber yielding active held source)
  · exact scoped_exit_returned root m fiber yielding _ held
      (primitive_returned root m.completedExits [] m fiber yielding active held source)
  · exact primitive_returned root m.completedExits table m fiber yielding active held source

/-- Loop-top interruption retains the pending registration phase before the next operation.
Consumer: native iteration sequencing. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem loop_top (fiber : Fiber) (held : Kept fiber.frame.current fiber.frame.stack) :
    Kept (runloopTop fiber).frame.current (runloopTop fiber).frame.stack := by
  unfold runloopTop
  split
  · exact interrupt held _
  · exact held

/-- Loop-top interruption retains the shared source predicate's original saved frames.
Consumer: native iteration's source-linked primitive rule. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem loop_top_source (root : NativeEff) (fiber : Fiber) (source : SourceScope.FrameAt root fiber.frame) :
    SourceScope.FrameAt root (runloopTop fiber).frame := by
  unfold runloopTop
  split
  · exact ⟨trivial, source.2⟩
  · exact source

/-- Forced yield and the loop-top interruption cut preserve every actual evaluator boundary.
Consumer: the original Workers release history, through the actual scheduler iteration. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem iteration_returned (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) (held : Kept fiber.frame.current fiber.frame.stack)
    (source : SourceScope.FrameAt root fiber.frame) :
    Returned (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding) := by
  have top := loop_top fiber held
  have owned := loop_top_source root fiber source
  have unparked : (countOp (runloopTop fiber)).parked = .notParked := by
    unfold countOp runloopTop
    split <;> exact active
  unfold iteration
  dsimp only
  cases injected : injectYield m (countOp (runloopTop fiber)) yielding with
  | none => exact native_returned root table m _ yielding unparked top owned
  | some it =>
    unfold injectYield at injected
    split at injected
    · cases injected
      apply native_returned root table
      · exact unparked
      · exact forced_wrapper top 0
      · exact ⟨⟨trivial, owned.1⟩, owned.2⟩
    · cases injected

end Effect4.Program.ReleaseCustody.NativeSequencing

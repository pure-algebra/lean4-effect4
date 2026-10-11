import Effect4.Laws.Program.Moves
import Effect4.Laws.Machine.StackLocal

/-!
# Laws.Program.StackLocal — an evaluation that goes on is the same over more frames

The frame rule of the native evaluator: run a fiber with frames `below` under its stack, and an
evaluation that does not finish is the same evaluation, with `below` under the result's stack and
the same machine, latch, outcome and nested commands. The frames under the region are not read and
not written.

* `GoesOn`: the evaluation did not finish. Where it finishes, its pop answered nothing, and over
  more frames the pop goes on into them: the region has ended.
* The levels: `stepFrame_under`, `finalizerOr_under`, then the evaluator.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), the region bracket; the
  proposed registry claim `stack-local`, role invariant (the research note
  `docs/research/2026-10-11-machine-from-the-base/README.md`, B3);
- reach: every native evaluation that does not finish, at every machine, fiber, interpreter and
  stack of frames under it;
- it states one evaluation. Along a run, through `Machine.Lift`, it gives the shape that
  `compiled_region_bracket` takes as its premise `inside`; that lift is not here;
- consumers: that lift, then Semaphore's protected permit and Pool's `use` (R11).
-/

set_option autoImplicit false

namespace Effect4.Program.Moves

open Effect4 Effect4.Machine Effect4.Program

/-- The native iteration result. -/
abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- The run fiber with frames `below` under its stack. -/
def fiberUnder (f : NFiber) (below : List NCode) : NFiber :=
  { f with frame := f.frame.under below }

/-- An iteration result with frames `below` under its fiber's stack. -/
def iterUnder (it : NIter) (below : List NCode) : NIter :=
  { it with fiber := fiberUnder it.fiber below }

/-- An evaluation that goes on: its outcome is no exit. -/
def GoesOn (it : NIter) : Prop :=
  ∀ exit, it.outcome ≠ Outcome.finished exit

/-- The frame machine's step, delegated: where it goes on, it is the same over more frames. -/
theorem stepFrame_under (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (below : List NCode) (going : GoesOn (evaluatePrim.stepFrame interp m f yielding)) :
    evaluatePrim.stepFrame interp m (fiberUnder f below) yielding =
      iterUnder (evaluatePrim.stepFrame interp m f yielding) below := by
  unfold evaluatePrim.stepFrame at going ⊢
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events =>
    cases step with
    | running next =>
      have pair := FrameFiber.step_under_pair interp.toPrimInterp f.frame below next events hs
      simp only [fiberUnder, pair]
      rfl
    | finished exit =>
      simp only [hs, evaluatePrim.finishFrame] at going
      exact absurd rfl (going exit)

/-- An exit meeting the stack, where the fiber's code is that exit: where it goes on, its pop
answered above the frames `below`, and it is the same over them. -/
theorem finalizerOr_under (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (exit : ExitV) (below : List NCode) (current : f.frame.current = Prim.ofExit exit)
    (going : GoesOn (evaluatePrim.finalizerOr interp m f yielding exit)) :
    evaluatePrim.finalizerOr interp m (fiberUnder f below) yielding exit =
      iterUnder (evaluatePrim.finalizerOr interp m f yielding exit) below := by
  cases exit with
  | success value =>
    unfold evaluatePrim.finalizerOr at going ⊢
    dsimp only at going ⊢
    cases answered : (f.frame.getCont Arm.contA false none).answer with
    | empty =>
      simp only [answered] at going
      unfold evaluatePrim.stepFrame at going
      have finished : f.frame.step interp.toPrimInterp =
          (FrameStep.finished ((some (Exit.success value)).getD (Exit.success value)),
            (f.frame.getCont Arm.contA false).events ++
              [FrameEvent.yielded ((some (Exit.success value)).getD (Exit.success value))]) := by
        simp only [FrameFiber.step, current, Prim.ofExit]
        exact FrameFiber.resumeValue_empty _ _ _ _ answered
      simp only [finished, evaluatePrim.finishFrame] at going
      exact absurd rfl (going _)
    | deferred c =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contA false none
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered] at going
      simp only [fiberUnder, kept, answered]
      exact stepFrame_under _ _ _ _ _ going
    | replacement code =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contA false none
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered] at going
      simp only [fiberUnder, kept, answered]
      exact stepFrame_under _ _ _ _ _ going
    | frame answering =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contA false none
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered, FramePop.deliveredExit] at going
      simp only [fiberUnder, kept, answered, FramePop.deliveredExit]
      cases answering
      case onExit body fin flag =>
        cases program : interp.finalizerProgram fin (Exit.success value) with
        | some code =>
          simp only [program]
          rfl
        | none =>
          simp only [program] at going ⊢
          exact stepFrame_under _ _ _ _ _ going
      all_goals exact stepFrame_under _ _ _ _ _ going
  | failure cause =>
    unfold evaluatePrim.finalizerOr at going ⊢
    dsimp only at going ⊢
    cases answered : (f.frame.getCont Arm.contE true (some cause)).answer with
    | empty =>
      simp only [answered] at going
      unfold evaluatePrim.stepFrame at going
      have finished : f.frame.step interp.toPrimInterp =
          (FrameStep.finished ((f.frame.getCont Arm.contE true (some cause)).deliveredExit
              ((some (Exit.failure cause)).getD (Exit.failure cause))),
            (f.frame.getCont Arm.contE true (some cause)).events ++
              [FrameEvent.yielded ((f.frame.getCont Arm.contE true (some cause)).deliveredExit
                ((some (Exit.failure cause)).getD (Exit.failure cause)))]) := by
        simp only [FrameFiber.step, current, Prim.ofExit]
        exact FrameFiber.resumeCause_empty _ _ _ _ answered
      simp only [finished, evaluatePrim.finishFrame] at going
      exact absurd rfl (going _)
    | deferred c =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contE true (some cause)
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered] at going
      simp only [fiberUnder, kept, answered]
      exact stepFrame_under _ _ _ _ _ going
    | replacement code =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contE true (some cause)
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered] at going
      simp only [fiberUnder, kept, answered]
      exact stepFrame_under _ _ _ _ _ going
    | frame answering =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contE true (some cause)
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered, FramePop.deliveredExit] at going
      simp only [fiberUnder, kept, answered, FramePop.deliveredExit]
      cases answering
      case onExit body fin flag =>
        cases program : interp.finalizerProgram fin
            (Exit.failure ((f.frame.getCont Arm.contE true (some cause)).carriedCause.getD cause)) with
        | some code =>
          simp only [program]
          rfl
        | none =>
          simp only [program] at going ⊢
          exact stepFrame_under _ _ _ _ _ going
      all_goals exact stepFrame_under _ _ _ _ _ going

/-- The parallel close's forks read the host's mask and context, never its stack. -/
theorem forkFinalizers_under (interp : NInterp) (host : NFiber) (below : List NCode) :
    ∀ (m : NativeMachine) (programs : List NCode),
      forkFinalizers interp m (fiberUnder host below) programs = forkFinalizers interp m host programs
  | m, [] => rfl
  | m, program :: rest => by
    simp only [forkFinalizers]
    rw [forkFinalizers_under interp host below _ rest]
    rfl

/-- Every `withFiber` action is the same over more frames: none reads the stack, and the mask and
the unmask push their restoring frame on top. -/
theorem withFiber_under (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) (below : List NCode) :
    evaluatePrim.withFiber interp m (fiberUnder f below) yielding action =
      iterUnder (evaluatePrim.withFiber interp m f yielding action) below := by
  cases action with
  | fork program options site =>
    cases now : options.startImmediately <;>
      simp only [evaluatePrim.withFiber, spawn, start, now, fiberUnder, iterUnder] <;> rfl
  | forkIn program options scope site =>
    cases now : options.startImmediately <;>
      simp only [evaluatePrim.withFiber, spawn, start, now, fiberUnder, iterUnder] <;> rfl
  | forkScoped program options site =>
    cases scope : interp.ambientScope f.context with
    | none => simp only [evaluatePrim.withFiber, fiberUnder, iterUnder, scope]; rfl
    | some s =>
      cases now : options.startImmediately <;>
        simp only [evaluatePrim.withFiber, spawn, start, now, fiberUnder, iterUnder, scope] <;> rfl
  | ambientScope =>
    cases scope : interp.ambientScope f.context <;>
      simp only [evaluatePrim.withFiber, fiberUnder, iterUnder, scope] <;> rfl
  | runIn target scope => rfl
  | interrupt target => rfl
  | interruptAs target who =>
    cases found : m.fiber? target <;>
      simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, fiberUnder, iterUnder, found]
    all_goals rfl
  | interruptScoped target =>
    rcases Decidable.em (target = f.id) with same | other
    · have same' : target = (fiberUnder f below).id := same
      simp only [evaluatePrim.withFiber, if_pos same', if_pos same]
      rfl
    · have other' : ¬target = (fiberUnder f below).id := other
      simp only [evaluatePrim.withFiber, if_neg other', if_neg other]
      rfl
  | interruptAll targets interruptor => rfl
  | awaitAll targets =>
    cases walk : countdownWalk { m with nextToken := m.nextToken + 1 } targets [] with
    | mk exits rest =>
      cases rest <;> simp only [evaluatePrim.withFiber, countdownPark, fiberUnder, iterUnder, walk,
        RunFiber.park] <;> rfl
  | awaitAllFailFast targets =>
    cases walk : countdownWalk { m with nextToken := m.nextToken + 1 } targets [] with
    | mk exits rest =>
      cases rest <;> simp only [evaluatePrim.withFiber, countdownPark, fiberUnder, iterUnder, walk,
        RunFiber.park] <;> rfl
  | snapshotChildren => rfl
  | awaitNewChildren snapshot =>
    cases walk : countdownWalk { m with nextToken := m.nextToken + 1 }
        (f.children.filter fun c => !(snapshot.contains c)) [] with
    | mk exits rest =>
      cases rest <;> simp only [evaluatePrim.withFiber, countdownPark, fiberUnder, iterUnder, walk,
        RunFiber.park] <;> rfl
  | raceAll entrants site => rfl
  | setInterruptible body flag =>
    cases flag <;> cases mask : f.frame.interruptible <;>
      simp only [evaluatePrim.withFiber, fiberUnder, iterUnder, FrameFiber.uninterruptible,
        FrameFiber.interruptibleRegion, FrameFiber.setFiberInterruptible, FrameFiber.under, mask,
        ↓reduceIte, Bool.false_eq_true]
    all_goals rfl
  | setContext context => rfl
  | getContext => rfl
  | getId => rfl
  | closeScope scope exit =>
    cases closed : interp.closeScope scope exit f.frame.interruptible f.id m.state <;>
      simp only [evaluatePrim.withFiber, fiberUnder, iterUnder, FrameFiber.under, closed]
  | closePar finalizers =>
    simp only [evaluatePrim.withFiber]
    rw [forkFinalizers_under]
    rfl
  | refuse cause => rfl
  | dropObservers token => rfl
  | cancelRace race =>
    cases found : m.race? race <;>
      simp only [evaluatePrim.withFiber, fiberUnder, iterUnder, found]
    all_goals rfl
  | getInterruptible =>
    cases mask : f.frame.interruptible <;>
      simp only [evaluatePrim.withFiber, fiberUnder, iterUnder, FrameFiber.uninterruptible,
        FrameFiber.under, mask, ↓reduceIte, Bool.false_eq_true]
    all_goals rfl

/-- **One primitive evaluation that goes on is the same over more frames.** -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem evaluatePrim_under (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (below : List NCode) (going : GoesOn (evaluatePrim interp m f yielding)) :
    evaluatePrim interp m (fiberUnder f below) yielding =
      iterUnder (evaluatePrim interp m f yielding) below := by
  have current : (fiberUnder f below).frame.current = f.frame.current := rfl
  unfold evaluatePrim at going ⊢
  rw [current]
  split
  · rfl
  · rename_i register withSignal cancel hc
    cases reg : interp.registerAsync register f.id m.nextToken m.state with
    | mk state immediate =>
      cases immediate with
      | some next =>
        simp only [fiberUnder, iterUnder, reg]
        rfl
      | none =>
        cases signal : (withSignal || cancel.isSome) <;>
          simp only [fiberUnder, iterUnder, reg, RunFiber.park, FrameFiber.under,
            ↓reduceIte, Bool.false_eq_true]
        all_goals rfl
  · rename_i notYield notAsync
    cases park : interp.parkOf f.frame.current with
    | none =>
      simp only [park] at going ⊢
      cases hc : f.frame.current
      case withFiber thunk =>
        cases action : interp.withFiberOf thunk with
        | some act =>
          simp only [action]
          exact withFiber_under _ _ _ _ _ _
        | none =>
          simp only [hc, action] at going ⊢
          exact stepFrame_under _ _ _ _ _ going
      case sync thunk =>
        cases st : interp.syncState thunk m.state <;> simp only [st]
        all_goals rfl
      case success value =>
        simp only [hc] at going
        exact finalizerOr_under _ _ _ _ _ _ hc going
      case failure cause =>
        simp only [hc] at going
        exact finalizerOr_under _ _ _ _ _ _ hc going
      case yieldNowWith priority => exact absurd hc (notYield priority)
      case async register withSignal cancel => exact absurd hc (notAsync register withSignal cancel)
      all_goals
        simp only [hc] at going
        exact stepFrame_under _ _ _ _ _ going
    | some result =>
      cases result with
      | error cause =>
        simp only []
        rfl
      | ok kind =>
        cases kind with
        | race raceId =>
          cases found : m.race? raceId <;> simp only [registerRace, found]
          all_goals rfl
        | awaitAll targets =>
          cases walk : countdownWalk { m with nextToken := m.nextToken + 1 } targets [] with
          | mk exits rest =>
            cases rest <;> simp only [countdownPark, walk, fiberUnder, iterUnder, RunFiber.park]
            all_goals rfl
        | join target mode =>
          cases found : m.fiber? target with
          | none =>
            simp only [found]
            rfl
          | some t =>
            cases ex : t.exit <;> simp only [found, ex, fiberUnder, iterUnder, RunFiber.park]
            all_goals rfl

/-- An evaluation of an exit whose pop answers nothing finishes, at the native interpreter: an exit
is no park, so it meets the stack, and an unanswered pop yields. A step of `exitScoped_under`. -/
theorem evaluatePrim_exit_unanswered (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) (exit : ExitV) (current : f.frame.current = Prim.ofExit exit)
    (unanswered : (f.frame.getCont (match exit with | .success _ => Arm.contA | .failure _ => Arm.contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).answer =
        ContAnswer.empty) :
    ¬GoesOn (evaluatePrim (interpAt root m.completedExits table) m f yielding) := by
  intro going
  cases exit with
  | success value =>
    have notPark : (interpAt root m.completedExits table).parkOf (Prim.success value) = none := rfl
    unfold evaluatePrim at going
    simp only [current, Prim.ofExit, notPark] at going
    unfold evaluatePrim.finalizerOr at going
    simp only [unanswered] at going
    unfold evaluatePrim.stepFrame at going
    have finished : f.frame.step (interpAt root m.completedExits table).toPrimInterp =
        (FrameStep.finished ((some (Exit.success value)).getD (Exit.success value)),
          (f.frame.getCont Arm.contA false).events ++
            [FrameEvent.yielded ((some (Exit.success value)).getD (Exit.success value))]) := by
      simp only [FrameFiber.step, current, Prim.ofExit]
      exact FrameFiber.resumeValue_empty _ _ _ _ unanswered
    simp only [finished, evaluatePrim.finishFrame] at going
    exact absurd rfl (going _)
  | failure cause =>
    have notPark : (interpAt root m.completedExits table).parkOf (Prim.failure cause) = none := rfl
    unfold evaluatePrim at going
    simp only [current, Prim.ofExit, notPark] at going
    unfold evaluatePrim.finalizerOr at going
    simp only [unanswered] at going
    unfold evaluatePrim.stepFrame at going
    have finished : f.frame.step (interpAt root m.completedExits table).toPrimInterp =
        (FrameStep.finished ((f.frame.getCont Arm.contE true (some cause)).deliveredExit
            ((some (Exit.failure cause)).getD (Exit.failure cause))),
          (f.frame.getCont Arm.contE true (some cause)).events ++
            [FrameEvent.yielded ((f.frame.getCont Arm.contE true (some cause)).deliveredExit
              ((some (Exit.failure cause)).getD (Exit.failure cause)))]) := by
      simp only [FrameFiber.step, current, Prim.ofExit]
      exact FrameFiber.resumeCause_empty _ _ _ _ unanswered
    simp only [finished, evaluatePrim.finishFrame] at going
    exact absurd rfl (going _)

/-- The scoped exit, where the fiber's code is that exit: where it goes on, its pop answered above
the frames `below`, and it is the same over them. -/
theorem exitScoped_under (root : NativeEff) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (exit : ExitV) (below : List NCode) (current : f.frame.current = Prim.ofExit exit)
    (going : GoesOn (exitScoped root m f yielding exit)) :
    exitScoped root m (fiberUnder f below) yielding exit =
      iterUnder (exitScoped root m f yielding exit) below := by
  cases exit with
  | success value =>
    unfold exitScoped at going ⊢
    dsimp only at going ⊢
    cases answered : (f.frame.getCont Arm.contA false none).answer with
    | empty =>
      simp only [answered] at going
      exact absurd going (evaluatePrim_exit_unanswered root [] m f yielding (.success value) current
        answered)
    | deferred c =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contA false none
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered] at going
      simp only [fiberUnder, kept, answered]
      exact evaluatePrim_under _ _ _ _ _ going
    | replacement code =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contA false none
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered] at going
      simp only [fiberUnder, kept, answered]
      exact evaluatePrim_under _ _ _ _ _ going
    | frame answering =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contA false none
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered, FramePop.deliveredExit] at going
      simp only [fiberUnder, kept, answered, FramePop.deliveredExit]
      cases answering
      case onExit body fin flag =>
        cases fin
        case scopedExit previous scope =>
          have emitted : ∀ events, (m.emit events).state = m.state := fun _ => rfl
          simp only [FrameFiber.under, emitted]
          cases close : storesCloseScopeUnsafe scope (Exit.success value)
              (f.frame.getCont Arm.contA false none).fiber.interruptible m.state with
          | none => rfl
          | some result =>
            obtain ⟨state, program⟩ := result
            cases program <;> rfl
        all_goals exact evaluatePrim_under _ _ _ _ _ going
      all_goals exact evaluatePrim_under _ _ _ _ _ going
  | failure cause =>
    unfold exitScoped at going ⊢
    dsimp only at going ⊢
    cases answered : (f.frame.getCont Arm.contE true (some cause)).answer with
    | empty =>
      simp only [answered] at going
      exact absurd going (evaluatePrim_exit_unanswered root [] m f yielding (.failure cause) current
        answered)
    | deferred c =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contE true (some cause)
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered] at going
      simp only [fiberUnder, kept, answered]
      exact evaluatePrim_under _ _ _ _ _ going
    | replacement code =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contE true (some cause)
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered] at going
      simp only [fiberUnder, kept, answered]
      exact evaluatePrim_under _ _ _ _ _ going
    | frame answering =>
      have kept := FrameFiber.getCont_under_answered f.frame below Arm.contE true (some cause)
        (by rw [answered]; exact fun h => nomatch h)
      simp only [answered, FramePop.deliveredExit] at going
      simp only [fiberUnder, kept, answered, FramePop.deliveredExit]
      cases answering
      case onExit body fin flag =>
        cases fin
        case scopedExit previous scope =>
          have emitted : ∀ events, (m.emit events).state = m.state := fun _ => rfl
          simp only [FrameFiber.under, emitted]
          cases close : storesCloseScopeUnsafe scope
              (Exit.failure ((f.frame.getCont Arm.contE true (some cause)).carriedCause.getD cause))
              (f.frame.getCont Arm.contE true (some cause)).fiber.interruptible m.state with
          | none => rfl
          | some result =>
            obtain ⟨state, program⟩ := result
            cases program <;> rfl
        all_goals exact evaluatePrim_under _ _ _ _ _ going
      all_goals exact evaluatePrim_under _ _ _ _ _ going

/-- **One native evaluation that goes on is the same over more frames.** -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem evaluateNative_under (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (below : List NCode) (going : GoesOn (evaluateNative root m f yielding table)) :
    evaluateNative root m (fiberUnder f below) yielding table =
      iterUnder (evaluateNative root m f yielding table) below := by
  have current : (fiberUnder f below).frame.current = f.frame.current := rfl
  unfold evaluateNative at going ⊢
  rw [current]
  cases hc : f.frame.current
  case withFiber thunk =>
    cases thunk
    case act p =>
      simp only [hc] at going ⊢
      split
      · unfold enterScoped
        rfl
      · rename_i notScoped
        split at going
        · rename_i body isScoped
          exact absurd isScoped (notScoped body)
        · exact evaluatePrim_under _ _ _ _ _ going
    all_goals
      simp only [hc] at going ⊢
      exact evaluatePrim_under _ _ _ _ _ going
  case success value =>
    simp only [hc] at going ⊢
    exact exitScoped_under _ _ _ _ _ _ hc going
  case failure cause =>
    simp only [hc] at going ⊢
    exact exitScoped_under _ _ _ _ _ _ hc going
  all_goals
    simp only [hc] at going ⊢
    exact evaluatePrim_under _ _ _ _ _ going

/-- The loop's top and its op count do not read the stack. -/
theorem countOp_runloopTop_under (f : NFiber) (below : List NCode) :
    countOp (runloopTop (fiberUnder f below)) = fiberUnder (countOp (runloopTop f)) below := by
  unfold countOp runloopTop
  cases deferred : f.frame.deferredInterrupt
  · simp only [fiberUnder, FrameFiber.under, deferred, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [fiberUnder, FrameFiber.under, deferred, ↓reduceIte]
    rfl

/-- The yield injection does not read the stack. -/
theorem injectYield_under (m : NativeMachine) (f : NFiber) (yielding : Bool) (below : List NCode) :
    injectYield m (fiberUnder f below) yielding =
      (injectYield m f yielding).map fun it => iterUnder it below := by
  unfold injectYield
  rcases Decidable.em ((!yielding && !f.preventYield && yieldVerdict f) = true) with inject | quiet
  · have inject' : (!yielding && !(fiberUnder f below).preventYield &&
        yieldVerdict (fiberUnder f below)) = true := inject
    rw [if_pos inject', if_pos inject]
    rfl
  · have quiet' : ¬(!yielding && !(fiberUnder f below).preventYield &&
        yieldVerdict (fiberUnder f below)) = true := quiet
    rw [if_neg quiet', if_neg quiet]
    rfl

/-- **One iteration of the native loop that goes on is the same over more frames**: the frame rule
of the fiber machine at one command. The pointer of the evaluation's half of the proposed claim
`stack-local`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem iteration_under (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (below : List NCode)
    (going : GoesOn (iteration (evaluator := evaluatorFor root table) interp m f yielding)) :
    iteration (evaluator := evaluatorFor root table) interp m (fiberUnder f below) yielding =
      iterUnder (iteration (evaluator := evaluatorFor root table) interp m f yielding) below := by
  unfold iteration at going ⊢
  dsimp only at going ⊢
  rw [countOp_runloopTop_under, injectYield_under]
  cases injected : injectYield m (countOp (runloopTop f)) yielding with
  | some it =>
    simp only [injected] at going
    exact evaluateNative_under root table it.machine it.fiber it.yielding below going
  | none =>
    simp only [injected] at going
    exact evaluateNative_under root table m _ yielding below going

end Effect4.Program.Moves

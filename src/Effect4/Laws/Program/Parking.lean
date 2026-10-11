import Effect4.Laws.Program.Footprint

/-!
Concept: reactive-scheduling; the outcome part of the proposed `evaluation-moves` claim.
Question: one evaluation either keeps the waiting fields or installs its fresh pending entry.
This is a step of registry claim `stepped-fiber-live`, through guard state and queue preservation.
Reach: every native evaluator and iteration, at arbitrary input fibers and row tables.
Consumers: the guard's pending shape, ready outcome, and fresh park chains.
A completed outcome retains the exact finishing frame step and its returned frame.
Limits: this classification proves no command closure or progress.
The finishing witness serves `compiled_mask_chain_runs` and the region bracket, R11.
-/
set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program

abbrev ParkIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- A completed evaluation comes from a finishing frame step.
The witness retains the exact interpreter, events and returned frame.
Consumer: the completed-stack part of `compiled_mask_chain_runs`, then the region bracket. -/
def FinishOrigin (it : ParkIter) : Prop :=
  ∀ exit, it.outcome = .finished exit → ∃ interp frame events,
    frame.step interp = (FrameStep.finished exit, events) ∧
    it.fiber.frame = frameExitState frame

/-- The waiting fields and outcome share one classification.
A newly installed park holds the exact pending entry and the minted token. -/
inductive Parking (m : NativeMachine) (f : NFiber) (it : ParkIter) : Prop
  | kept (park : it.fiber.parked = f.parked) (pending : it.fiber.pending = f.pending)
      (outcome : it.outcome ≠ .parked) (finished : FinishOrigin it) : Parking m f it
  | installed (wait : Pending EffName Val Err Defect FiberId Ann)
      (token : wait.token = m.nextToken) (fresh : m.nextToken < it.machine.nextToken)
      (park : it.fiber.parked = .withGuard wait.token)
      (pending : it.fiber.pending = f.pending ++ [wait])
      (outcome : it.outcome = .parked ∨ ∃ why, it.outcome = .stuck why) : Parking m f it

/-- Every completed outcome retains its finishing step; an installed park cannot finish. -/
theorem Parking.finished {m : NativeMachine} {f : NFiber} {it : ParkIter}
    (held : Parking m f it) : FinishOrigin it := by
  cases held with
  | kept _ _ _ origin => exact origin
  | installed _ _ _ _ _ outcome =>
    intro exit finished
    rcases outcome with parked | ⟨why, stuck⟩
    · rw [parked] at finished
      cases finished
    · rw [stuck] at finished
      cases finished

/-- Preparatory edits with unchanged waiting fields and token counter transport the classification. -/
theorem Parking.before {m n : NativeMachine} {f g : NFiber} {it : ParkIter}
    (held : Parking n g it) (token : n.nextToken = m.nextToken)
    (park : g.parked = f.parked) (pending : g.pending = f.pending) : Parking m f it := by
  cases held with
  | kept hp hn ho hf => exact .kept (hp.trans park) (hn.trans pending) ho hf
  | installed wait ht hf hp hn ho =>
    exact .installed wait (ht.trans token) (token ▸ hf) hp
      (hn.trans (congrArg (fun xs => xs ++ [wait]) pending)) ho

/-- The frame step keeps the waiting fields, whether it continues or finishes. -/
theorem stepFrame_parking (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Parking m f (evaluatePrim.stepFrame interp m f yielding) := by
  unfold evaluatePrim.stepFrame
  cases stepped : f.frame.step interp.toPrimInterp with
  | mk step events =>
    cases step with
    | running next => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
    | finished exit =>
      refine .kept rfl rfl (by intro h; cases h) ?_
      intro result ended
      cases ended
      exact ⟨interp.toPrimInterp, f.frame, events, stepped, rfl⟩

/-- A finalizer entry keeps waiting fields; its fallback uses the frame step. -/
theorem finalizerOr_parking (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Parking m f (evaluatePrim.finalizerOr interp m f yielding exit) := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
      · exact stepFrame_parking _ _ _ _
    · exact stepFrame_parking _ _ _ _

/-- A completed countdown answers; a live countdown installs its one pending entry. -/
theorem countdown_parking (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    let result := countdownParkEdits interp m f targets resume failFast
    Parking m f ⟨result.1, result.2.1, yielding,
      if result.2.2.1 then .parked else .continue_, [], result.2.2.2⟩ := by
  unfold countdownParkEdits
  dsimp only
  split
  · exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  · refine .installed _ rfl ?_ rfl rfl (.inl rfl)
    exact Nat.lt_succ_self _

/-- A stuck machine reports its refusal while retaining the same installed park. -/
theorem countdown_parkingOf (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    let result := countdownParkEdits interp m f targets resume failFast
    Parking m f ⟨result.1, result.2.1, yielding,
      FiberAction.outcomeOf result.1 result.2.2.1, [], result.2.2.2⟩ := by
  have held := countdown_parking interp m f yielding targets resume failFast
  cases stuck : (countdownParkEdits interp m f targets resume failFast).1.stuck with
  | none => simpa only [FiberAction.outcomeOf, stuck] using held
  | some why =>
    cases held with
    | kept hp hn _ _ =>
      exact .kept hp hn
        (by simp only [FiberAction.outcomeOf, stuck]; intro h; cases h)
        (by intro _ h; simp only [FiberAction.outcomeOf, stuck] at h; cases h)
    | installed wait ht hf hp hn _ =>
      exact .installed wait ht hf hp hn (.inr ⟨why, by simp only [FiberAction.outcomeOf, stuck]⟩)

/-- Each fiber action shares the same waiting-field classification. -/
theorem withFiber_parking (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) : Parking m f (evaluatePrim.withFiber interp m f yielding action) := by
  cases action with
  | fork program options site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split <;> split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | forkIn program options scope site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | forkScoped program options site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split
    · split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
    · exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | runIn target scope =>
    refine .kept rfl rfl ?_ ?_
    · simp only [evaluatePrim.withFiber]
      split <;> intro h <;> cases h
    · intro _ h
      simp only [evaluatePrim.withFiber] at h
      split at h <;> cases h
  | interrupt target => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | interruptAs target who =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | interruptAll targets who => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | awaitAll targets => exact countdown_parkingOf _ _ _ _ _ _ _
  | awaitAllFailFast targets => exact countdown_parkingOf _ _ _ _ _ _ _
  | snapshotChildren => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | awaitNewChildren snapshot => exact countdown_parkingOf _ _ _ _ _ _ _
  | raceAll entrants site => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | raceAllFirst entrants site => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | setInterruptible body flag =>
    cases flag <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | setContext context => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | getContext => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | getId => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | closePar finalizers => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | refuse cause => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | dropObservers token => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  | getInterruptible => exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)

/-- One primitive evaluation keeps its waiting fields or installs the fresh park. -/
@[semantics "reactive-scheduling"]
theorem evaluatePrim_parking (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) : Parking m f (evaluatePrim interp m f yielding) := by
  unfold evaluatePrim
  split
  · exact .installed _ rfl (Nat.lt_succ_self _) rfl rfl (.inl rfl)
  · dsimp only
    split
    · exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
    · split <;> exact .installed _ rfl (Nat.lt_succ_self _) rfl rfl (.inl rfl)
  · split
    · exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
    · unfold registerRace
      split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
    · exact countdown_parking _ _ _ _ _ _ _
    · split
      · exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
      · split
        · exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
        · exact .installed _ rfl (Nat.lt_succ_self _) rfl rfl (.inl rfl)
    · split
      · split
        · exact withFiber_parking _ _ _ _ _
        · exact stepFrame_parking _ _ _ _
      · split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
      · exact finalizerOr_parking _ _ _ _ _
      · exact finalizerOr_parking _ _ _ _ _
      · exact stepFrame_parking _ _ _ _

/-- A scoped exit keeps waiting fields, or delegates to the primitive evaluator. -/
theorem exitScoped_parking (root : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) : Parking m f (exitScoped root m f yielding exit) := by
  unfold exitScoped
  dsimp only
  split
  · split <;> exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
  · exact evaluatePrim_parking _ _ _ _

/-- The complete native evaluator has the same waiting-field classification. -/
@[semantics "reactive-scheduling"]
theorem evaluateNative_parking (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) : Parking m f (evaluateNative root m f yielding table) := by
  unfold evaluateNative
  split
  · split
    · exact .kept rfl rfl (by intro h; cases h) (by intro _ h; cases h)
    · exact evaluatePrim_parking _ _ _ _
  · exact exitScoped_parking _ _ _ _ _
  · exact exitScoped_parking _ _ _ _ _
  · exact evaluatePrim_parking _ _ _ _

/-- Loop preparation changes neither pending entries nor the token counter. -/
@[semantics "reactive-scheduling"]
theorem iteration_parking (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Parking m f (iteration (evaluator := evaluatorFor root table) interp m f yielding) := by
  have topPark : (countOp (runloopTop f)).parked = f.parked := by
    unfold countOp runloopTop
    split <;> rfl
  have topPending : (countOp (runloopTop f)).pending = f.pending := by
    unfold countOp runloopTop
    split <;> rfl
  unfold iteration
  dsimp only
  split
  · rename_i it injected
    unfold injectYield at injected
    split at injected
    · cases injected
      exact (evaluateNative_parking _ _ _ _ _).before rfl topPark topPending
    · cases injected
  · exact (evaluateNative_parking _ _ _ _ _).before rfl topPark topPending

end Effect4.Program.Moves

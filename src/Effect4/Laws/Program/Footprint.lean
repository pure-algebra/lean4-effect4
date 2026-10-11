import Effect4.Laws.Program.FrameMoves

/-!
# Laws.Program.Footprint — the footprint of one evaluation on the evaluated run fiber

`Laws/Program/Moves.lean` classifies an evaluation's edits of the evaluated fiber's frame part.
This module states its footprint on the whole run fiber (`RunFiber`): the frame part moves by a word
of frame moves, and the id, the exit, the running bit, the finalizing exit, the fiber's own
observers and its children are untouched. The fields an evaluation may write besides the frame are
the park, the dispatcher, the context with its budget caches, the op count and the yield override.

* **The footprint** (`Footprint`, `Footprint.trans`).
* **The classification** (`evaluatePrim_footprint`, `exitScoped_footprint`,
  `evaluateNative_footprint`, `iteration_footprint`).
* **Connectors** to three run-fiber chains of the guard bundle (`iteration_id`, `iteration_exit`,
  `iteration_running`).

Placement (AGENTS.md, Trust):

- concept `reactive-scheduling` (`docs/core/semantics.md` §2.4); the proposed registry claim
  `evaluation-moves`, role structure, of which this is the run fiber's half;
- reach: every native evaluation and iteration, at every machine, fiber, interpreter, row table and
  latch. It states the evaluated fiber only: the machine and the other fibers are outside it, and
  so is the outcome;
- it does not establish which word an evaluation takes, any invariant, or progress;
- consumers: the guard bundle's run-fiber chains (`Guard.Interruption`'s `id` and `exit` chains,
  `Guard.ReturnFields`'s `running` chain), replaced by these instances in a later cleanup (the
  research note `docs/research/2026-10-11-machine-from-the-base/README.md`, §5).
-/

set_option autoImplicit false

namespace Effect4.Program.Moves

open Effect4 Effect4.Machine Effect4.Program

/-- **The footprint of one evaluation on the evaluated run fiber**: its frame part moves by a word
of frame moves, and six fields are untouched. The fields it may write besides the frame are the
park (`parked`, `pending`), the dispatcher, the context with its budget caches, the op count and
the yield override. -/
structure Footprint (f g : NFiber) : Prop where
  /-- The frame part moves by a word of frame moves. -/
  frame : Moves f.frame g.frame
  /-- The id is kept. -/
  id : g.id = f.id
  /-- The exit is kept. -/
  exit : g.exit = f.exit
  /-- The running bit is kept. -/
  running : g.running = f.running
  /-- The finalizing exit is kept. -/
  finalizing : g.finalizing = f.finalizing
  /-- The fiber's own observers are kept. -/
  observers : g.observers = f.observers
  /-- The fiber's children are kept. -/
  children : g.children = f.children

/-- The empty footprint. -/
theorem Footprint.refl (f : NFiber) : Footprint f f :=
  ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Footprints compose. -/
theorem Footprint.trans {f g h : NFiber} (a : Footprint f g) (b : Footprint g h) : Footprint f h :=
  ⟨a.frame.trans b.frame, b.id.trans a.id, b.exit.trans a.exit, b.running.trans a.running,
    b.finalizing.trans a.finalizing, b.observers.trans a.observers, b.children.trans a.children⟩

/-! ## The classification -/

/-- The frame machine's step, delegated, edits the frame alone. -/
theorem stepFrame_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Footprint f (evaluatePrim.stepFrame interp m f yielding).fiber := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step events =>
    cases step with
    | running next => exact ⟨.single (.step _ _ _ _ hs), rfl, rfl, rfl, rfl, rfl, rfl⟩
    | finished exit => exact ⟨.single (.finish _ _ _ _ hs), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An exit meeting the stack edits the frame alone. -/
theorem finalizerOr_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Footprint f (evaluatePrim.finalizerOr interp m f yielding exit).fiber := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · split
      · exact ⟨.two (.pop _ _ _ _) (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact stepFrame_footprint _ _ _ _
    · exact stepFrame_footprint _ _ _ _

/-- The countdown park answers, or pushes its cancel frame and parks. -/
theorem countdownPark_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    Footprint f (countdownPark interp m f targets resumeWith failFast).2.1 := by
  unfold countdownPark
  dsimp only
  split
  · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨.single (.push _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every `withFiber` action, on the run fiber. -/
theorem withFiber_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) :
    Footprint f (evaluatePrim.withFiber interp m f yielding action).fiber := by
  cases action with
  | fork program options site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split <;> split <;> exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | forkIn program options scope site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split <;> exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | forkScoped program options site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split
    · split <;> exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | runIn target scope => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | interrupt target => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | interruptAs target who =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split <;> exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | interruptAll targets interruptor => exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | awaitAll targets => exact countdownPark_footprint _ _ _ _ _ _
  | awaitAllFailFast targets => exact countdownPark_footprint _ _ _ _ _ _
  | snapshotChildren => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | awaitNewChildren snapshot => exact countdownPark_footprint _ _ _ _ _ _
  | raceAll entrants site => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | raceAllFirst entrants site => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | setInterruptible body flag =>
    cases flag
    · exact ⟨.two (.mask _) (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨.two (.unmask _) (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | setContext context => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | getContext => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | getId => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | closePar finalizers => exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | refuse cause => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | dropObservers token => exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | getInterruptible => exact ⟨.two (.mask _) (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **One primitive evaluation**'s footprint on the evaluated run fiber. -/
@[semantics "reactive-scheduling"]
theorem evaluatePrim_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    Footprint f (evaluatePrim interp m f yielding).fiber := by
  unfold evaluatePrim
  split
  · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only
    split
    · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split
      · exact ⟨.single (.push _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · unfold registerRace
      split <;> exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact countdownPark_footprint _ _ _ _ _ _
    · split
      · exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · split
        · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨.single (.push _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split
      · split
        · exact withFiber_footprint _ _ _ _ _
        · exact stepFrame_footprint _ _ _ _
      · split <;> exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact finalizerOr_footprint _ _ _ _ _
      · exact finalizerOr_footprint _ _ _ _ _
      · exact stepFrame_footprint _ _ _ _

/-- The scoped exit pops, restores the context and answers. -/
theorem exitScoped_footprint (root : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Footprint f (exitScoped root m f yielding exit).fiber := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact ⟨.two (.pop _ _ _ _) (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨.tail (.two (.pop _ _ _ _) (.answer _ _)) (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact evaluatePrim_footprint _ _ _ _

/-- **One native evaluation**'s footprint on the evaluated run fiber. -/
@[semantics "reactive-scheduling"]
theorem evaluateNative_footprint (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    Footprint f (evaluateNative root m f yielding table).fiber := by
  unfold evaluateNative
  split
  · split
    · exact ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact evaluatePrim_footprint _ _ _ _
  · exact exitScoped_footprint _ _ _ _ _
  · exact exitScoped_footprint _ _ _ _ _
  · exact evaluatePrim_footprint _ _ _ _

/-- **One iteration of the native loop**'s footprint on the run fiber. -/
@[semantics "reactive-scheduling"]
theorem iteration_footprint (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Footprint f (iteration (evaluator := evaluatorFor root table) interp m f yielding).fiber := by
  have top : Footprint f (countOp (runloopTop f)) := by
    unfold countOp runloopTop
    split
    · exact ⟨.single (.pendingFailure _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold iteration
  dsimp only
  split
  · rename_i it h
    have injected : Footprint f it.fiber := by
      unfold injectYield at h
      split at h
      · cases h
        exact top.trans ⟨.single (.answer _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    exact injected.trans (evaluateNative_footprint _ _ _ _ _)
  · exact top.trans (evaluateNative_footprint _ _ _ _ _)

/-! ## Connectors -/

/-- Connector of `Guard.Interruption.iteration_id`: an iteration keeps the fiber's id. -/
@[semantics "reactive-scheduling"]
theorem iteration_id (p : NativeEff) (table : RowTable) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.id = f.id :=
  (iteration_footprint p table (interpOf p table) m f yielding).id

/-- Connector of `Guard.Interruption.iteration_exit`: an iteration keeps the fiber's exit. -/
@[semantics "reactive-scheduling"]
theorem iteration_exit (p : NativeEff) (table : RowTable) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.exit = f.exit :=
  (iteration_footprint p table (interpOf p table) m f yielding).exit

/-- Connector of `Guard.ReturnFields.iteration_running`: an iteration keeps the running bit. -/
@[semantics "reactive-scheduling"]
theorem iteration_running (p : NativeEff) (table : RowTable) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    letI := evaluatorFor p table
    (iteration (interpOf p table) m f yielding).fiber.running = f.running :=
  (iteration_footprint p table (interpOf p table) m f yielding).running

end Effect4.Program.Moves

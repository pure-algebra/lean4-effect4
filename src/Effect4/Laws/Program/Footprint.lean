import Effect4.Laws.Program.TracedMoves

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
- the labelled refinement records the word and exact trace extension; it establishes no invariant or progress;
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

/-- The footprint with one exact event-labelled word. -/
structure TracedFootprint (m : NativeMachine) (f : NFiber) (n : NativeMachine) (g : NFiber) : Prop where
  frame : TracedMoves m f.frame n g.frame
  id : g.id = f.id
  exit : g.exit = f.exit
  running : g.running = f.running
  finalizing : g.finalizing = f.finalizing
  observers : g.observers = f.observers
  children : g.children = f.children

/-- Erasure retains every original footprint field. -/
theorem TracedFootprint.shape {m n : NativeMachine} {f g : NFiber}
    (footprint : TracedFootprint m f n g) : Footprint f g :=
  ⟨footprint.frame.shape, footprint.id, footprint.exit, footprint.running, footprint.finalizing,
    footprint.observers, footprint.children⟩

/-- Exact footprints compose in trace order. -/
theorem TracedFootprint.trans {m n o : NativeMachine} {f g h : NFiber}
    (a : TracedFootprint m f n g) (b : TracedFootprint n g o h) : TracedFootprint m f o h :=
  ⟨a.frame.trans b.frame, b.id.trans a.id, b.exit.trans a.exit, b.running.trans a.running,
    b.finalizing.trans a.finalizing, b.observers.trans a.observers, b.children.trans a.children⟩

/-- Delegated stepping records exactly the frame machine's events. -/
theorem stepFrame_tracedFootprint (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    TracedFootprint m f (evaluatePrim.stepFrame interp m f yielding).machine
      (evaluatePrim.stepFrame interp m f yielding).fiber := by
  unfold evaluatePrim.stepFrame
  cases hs : f.frame.step interp.toPrimInterp with
  | mk step emitted =>
    cases step with
    | running next =>
      exact ⟨.single (.step f.id _ _ _ _ hs) (RunMachine.emit_trace _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
    | finished exit =>
      exact ⟨.single (.finish f.id _ _ _ _ hs) (RunMachine.emit_trace _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A native finalizer's pop and start are one accounting operation. -/
theorem finalizerOr_tracedFootprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    TracedFootprint m f (evaluatePrim.finalizerOr interp m f yielding exit).machine
      (evaluatePrim.finalizerOr interp m f yielding exit).fiber := by
  let originalExit := exit
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · rename_i body fin flag answered
      split
      · rename_i program _
        have move := LabelledMove.popAnswer f.id f.frame originalExit
          (finalizerCode interp ((popExit f.frame originalExit).deliveredExit originalExit) program)
          (some fin) (by
            intro name same
            cases same
            exact ⟨body, flag, answered⟩)
        exact ⟨.single move (RunMachine.emit_trace _ _), rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact stepFrame_tracedFootprint _ _ _ _
    · exact stepFrame_tracedFootprint _ _ _ _

/-- Countdown parking emits only its administrative park event. -/
theorem countdownParkEdits_tracedFootprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    TracedFootprint m f (countdownParkEdits interp m f targets resumeWith failFast).1
      (countdownParkEdits interp m f targets resumeWith failFast).2.1 := by
  unfold countdownParkEdits
  dsimp only
  split
  · exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨AdministrativeTrace.push ?_ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨[.parkedOn f.id m.nextToken], rfl, ?_⟩
    simp only [RunMachine.emit_trace]
    rfl

/-- The eager countdown view retains the same local footprint and trace. -/
theorem countdownPark_tracedFootprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    TracedFootprint m f (countdownPark interp m f targets resumeWith failFast).1
      (countdownPark interp m f targets resumeWith failFast).2.1 := by
  obtain ⟨⟨events, word, trace⟩, id, exit, running, finalizing, observers, children⟩ :=
    countdownParkEdits_tracedFootprint interp m f targets resumeWith failFast
  exact ⟨⟨events, word, (RunMachine.applyFiberEdits_trace _ _).trans trace⟩,
    id, exit, running, finalizing, observers, children⟩

/-- Spawning leaves the parent fields and frame unchanged. -/
theorem spawn_tracedFootprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (code : NCode) (options : Supervision.ForkOptions) (site : List Nat) :
    TracedFootprint m f (spawn interp m f code options site).1
      (spawn interp m f code options site).2.1 :=
  ⟨(spawn_administrative interp m f code options site).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Starting changes the dispatcher's scheduling state, with an administrative trace. -/
theorem start_tracedFootprint (m : NativeMachine) (f : NFiber) (child : FiberId) (now : Bool) :
    TracedFootprint m f (start m f child now).1 (start m f child now).2.1 := by
  cases now <;> exact ⟨(start_administrative _ _ _ _).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Each fiber action records its exact frame and administrative events. -/
theorem withFiber_tracedFootprint (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) :
    TracedFootprint m f (evaluatePrim.withFiber interp m f yielding action).machine
      (evaluatePrim.withFiber interp m f yielding action).fiber := by
  cases action with
  | fork program options site =>
    have beforeSpawn : TracedFootprint m f (if options.daemon then m else {m with middlewareInstalled := true}) f := by
      split <;> exact ⟨(AdministrativeTrace.of_eq rfl).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    apply beforeSpawn.trans
    apply (spawn_tracedFootprint interp _ f program options site).trans
    apply (start_tracedFootprint _ _ _ options.startImmediately).trans
    exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | forkIn program options scope site =>
    apply (spawn_tracedFootprint interp m f program {options with daemon := true} site).trans
    apply (start_tracedFootprint _ _ _ options.startImmediately).trans
    exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | forkScoped program options site =>
    simp only [evaluatePrim.withFiber]
    split
    · apply (spawn_tracedFootprint interp m f program {options with daemon := true} site).trans
      apply (start_tracedFootprint _ _ _ options.startImmediately).trans
      exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | runIn target scope =>
    exact ⟨(linkScopeEdits_administrative interp m _ scope target _ _).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | interrupt target =>
    exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | interruptAs target who =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split
    · exact ⟨(AdministrativeTrace.of_eq rfl).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · refine ⟨AdministrativeTrace.idle ?_ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨[.interruptRecorded (some who) target], rfl, ?_⟩
      simp only [RunMachine.emit_trace]
  | interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | interruptAll targets interruptor =>
    exact ⟨(AdministrativeTrace.of_eq rfl).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | awaitAll targets => exact countdownParkEdits_tracedFootprint _ _ _ _ _ _
  | awaitAllFailFast targets => exact countdownParkEdits_tracedFootprint _ _ _ _ _ _
  | snapshotChildren =>
    exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | awaitNewChildren snapshot => exact countdownParkEdits_tracedFootprint _ _ _ _ _ _
  | raceAll entrants site =>
    refine ⟨AdministrativeTrace.answer ?_ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨[.raceStarted m.nextRace f.id entrants.length], rfl, RunMachine.emit_trace _ _⟩
  | raceAllFirst entrants site =>
    refine ⟨AdministrativeTrace.answer ?_ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨[.raceStarted m.nextRace f.id entrants.length], rfl, RunMachine.emit_trace _ _⟩
  | setInterruptible body flag =>
    cases flag
    · exact ⟨⟨_, .two (.mask _) (.answer _ _ [] rfl), (List.append_nil _).symm⟩,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨⟨_, .two (.unmask _) (.answer _ _ [] rfl), (List.append_nil _).symm⟩,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
  | setContext context =>
    refine ⟨AdministrativeTrace.answer ?_ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨[.contextSet f.id context], rfl, RunMachine.emit_trace _ _⟩
  | getContext =>
    exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | getId =>
    exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨(AdministrativeTrace.of_eq rfl).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | closePar finalizers =>
    exact ⟨(forkFinalizers_administrative interp m f finalizers).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | refuse cause =>
    exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | dropObservers token =>
    exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨(AdministrativeTrace.of_eq rfl).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | getInterruptible =>
    exact ⟨⟨_, .two (.mask _) (.answer _ _ [] rfl), (List.append_nil _).symm⟩,
      rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A primitive evaluation has one exact labelled word. -/
@[semantics "reactive-scheduling"]
theorem evaluatePrim_tracedFootprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    TracedFootprint m f (evaluatePrim interp m f yielding).machine
      (evaluatePrim interp m f yielding).fiber := by
  unfold evaluatePrim
  split
  · refine ⟨AdministrativeTrace.answer ?_ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨[.parkedOn f.id m.nextToken], rfl, ?_⟩
    simp only [RunMachine.emit_trace, RunMachine.arm_trace]
    rfl
  · dsimp only
    split
    · exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · split
      · refine ⟨AdministrativeTrace.push ?_ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨[.parkedOn f.id m.nextToken], rfl, RunMachine.emit_trace _ _⟩
      · refine ⟨AdministrativeTrace.idle ?_ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨[.parkedOn f.id m.nextToken], rfl, RunMachine.emit_trace _ _⟩
  · split
    · exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · unfold registerRace
      split <;> exact ⟨(AdministrativeTrace.of_eq rfl).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact countdownParkEdits_tracedFootprint _ _ _ _ _ _
    · split
      · exact ⟨(AdministrativeTrace.of_eq rfl).idle _, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · split
        · exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · refine ⟨AdministrativeTrace.push ?_ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
          refine ⟨[.parkedOn f.id m.nextToken], rfl, ?_⟩
          simp only [RunMachine.emit_trace]
          rfl
    · split
      · split
        · exact withFiber_tracedFootprint _ _ _ _ _
        · exact stepFrame_tracedFootprint _ _ _ _
      · split <;> exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact finalizerOr_tracedFootprint _ _ _ _ _
      · exact finalizerOr_tracedFootprint _ _ _ _ _
      · exact stepFrame_tracedFootprint _ _ _ _

/-- A scoped exit retains the pop events and the optional finalizer start. -/
theorem exitScoped_tracedFootprint (root : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    TracedFootprint m f (exitScoped root m f yielding exit).machine
      (exitScoped root m f yielding exit).fiber := by
  let originalExit := exit
  cases exit <;> unfold exitScoped <;> dsimp only
  all_goals
    split
    · rename_i body previous scope flag answered
      split
      · have move := LabelledMove.popAnswer f.id f.frame originalExit
          (Prim.ofExit ((popExit f.frame originalExit).deliveredExit originalExit)) none
          (by intro name impossible; cases impossible)
        refine ⟨.single move ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
        simp only [RunMachine.emit_trace, exitEvents, List.append_nil]
        rfl
      · rename_i state program _
        cases program with
        | none =>
          have move := LabelledMove.popAnswer f.id f.frame originalExit
            (Prim.ofExit ((popExit f.frame originalExit).deliveredExit originalExit)) none
            (by intro name impossible; cases impossible)
          refine ⟨.single move ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
          simp only [RunMachine.emit_trace, exitEvents, List.append_nil]
          rfl
        | some code =>
          have move := LabelledMove.popAnswer f.id f.frame originalExit
            (finalizerCode (interpAt root m.completedExits)
              ((popExit f.frame originalExit).deliveredExit originalExit) (embed code))
            (some (.scopedExit previous scope)) (by
              intro name same
              cases same
              exact ⟨body, flag, answered⟩)
          refine ⟨.single move ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
          simp only [RunMachine.emit_trace, exitEvents, List.append_assoc]
          rfl
    · exact evaluatePrim_tracedFootprint _ _ _ _

/-- One native evaluation records exactly the labelled word's events. -/
@[semantics "reactive-scheduling"]
theorem evaluateNative_tracedFootprint (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    TracedFootprint m f (evaluateNative root m f yielding table).machine
      (evaluateNative root m f yielding table).fiber := by
  unfold evaluateNative
  split
  · split
    · exact ⟨(AdministrativeTrace.of_eq rfl).answer _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact evaluatePrim_tracedFootprint _ _ _ _
  · exact exitScoped_tracedFootprint _ _ _ _ _
  · exact exitScoped_tracedFootprint _ _ _ _ _
  · exact evaluatePrim_tracedFootprint _ _ _ _

/-- The native loop's exact word includes a possible yield injection. -/
@[semantics "reactive-scheduling"]
theorem iteration_tracedFootprint (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    TracedFootprint m f (iteration (evaluator := evaluatorFor root table) interp m f yielding).machine
      (iteration (evaluator := evaluatorFor root table) interp m f yielding).fiber := by
  have top : TracedFootprint m f m (countOp (runloopTop f)) := by
    unfold countOp runloopTop
    split
    · exact ⟨.single (.pendingFailure _) (List.append_nil _).symm, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold iteration
  dsimp only
  split
  · rename_i it found
    have injected : TracedFootprint m f it.machine it.fiber := by
      unfold injectYield at found
      split at found
      · cases found
        apply top.trans
        refine ⟨AdministrativeTrace.answer ?_ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨[.yieldInjected _ _], rfl, RunMachine.emit_trace _ _⟩
      · cases found
    exact injected.trans (evaluateNative_tracedFootprint _ _ _ _ _)
  · exact top.trans (evaluateNative_tracedFootprint _ _ _ _ _)

/-! ## The classification -/

/-- The frame machine's step, delegated, edits the frame alone. -/
theorem stepFrame_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Footprint f (evaluatePrim.stepFrame interp m f yielding).fiber :=
  (stepFrame_tracedFootprint interp m f yielding).shape

/-- An exit meeting the stack edits the frame alone. -/
theorem finalizerOr_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Footprint f (evaluatePrim.finalizerOr interp m f yielding exit).fiber :=
  (finalizerOr_tracedFootprint interp m f yielding exit).shape

/-- The countdown park answers, or pushes its cancel frame and parks. -/
theorem countdownPark_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resumeWith : Resume EffName) (failFast : Bool) :
    Footprint f (countdownParkEdits interp m f targets resumeWith failFast).2.1 :=
  (countdownParkEdits_tracedFootprint interp m f targets resumeWith failFast).shape

/-- Every `withFiber` action, on the run fiber. -/
theorem withFiber_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool)
    (action : NAction) :
    Footprint f (evaluatePrim.withFiber interp m f yielding action).fiber :=
  (withFiber_tracedFootprint interp m f yielding action).shape

/-- **One primitive evaluation**'s footprint on the evaluated run fiber. -/
@[semantics "reactive-scheduling"]
theorem evaluatePrim_footprint (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) :
    Footprint f (evaluatePrim interp m f yielding).fiber :=
  (evaluatePrim_tracedFootprint interp m f yielding).shape

/-- The scoped exit pops, restores the context and answers. -/
theorem exitScoped_footprint (root : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Footprint f (exitScoped root m f yielding exit).fiber :=
  (exitScoped_tracedFootprint root m f yielding exit).shape

/-- **One native evaluation**'s footprint on the evaluated run fiber. -/
@[semantics "reactive-scheduling"]
theorem evaluateNative_footprint (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    Footprint f (evaluateNative root m f yielding table).fiber :=
  (evaluateNative_tracedFootprint root table m f yielding).shape

/-- **One iteration of the native loop**'s footprint on the run fiber. -/
@[semantics "reactive-scheduling"]
theorem iteration_footprint (root : NativeEff) (table : RowTable) (interp : NInterp)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Footprint f (iteration (evaluator := evaluatorFor root table) interp m f yielding).fiber :=
  (iteration_tracedFootprint root table interp m f yielding).shape

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

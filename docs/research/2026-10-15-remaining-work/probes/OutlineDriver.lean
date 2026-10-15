import Effect4.Laws.Machine.Lift
import Effect4.Laws.Run.Frame
import Test.Dogfood.Scenario.Atomic.StageObservation
import Test.Dogfood.Scenario.Atomic.Store
import ProofGraph.GoalTag

/-!
# Probe: the outline driver, stated, and probed on `Atomic.Store.shop_stages`

Concepts: store-typing R4, scope-lifetime-finalization R11, reactive-scheduling R12. Question:
the five whole-history goals on concrete programs (`Timeout.cleanup_keeps`,
`Timeout.retries_declared`, `QueueWorkers.Assertions.jobs_step`, `rest_step`,
`Atomic.Store.shop_stages`). Consumer: their scenario claims.

**The schema.** An outline of a program is an external proof world with its order, a machine
assertion `J`, and three classes: the code a resume may install at a parked token, the exit a
finish may publish, and the outline a live fiber keeps while it runs. The command and snapshot
assertions are derived from the classes (`CmdAt`, `TaskAt`); no program writes its own. The
driver (`outline_driver`, proved) turns the per-program obligations into a decision lift.
`history_of_lift` (proved) then carries `J` along every control history.

**The probe on one goal.** `shop_stages_of_lift` (proved) derives the goal's statement, word for
word, from any decision lift whose `J` reads to the stage observation. `configured_reads`
(proved) is that reading for the configured phase, from the existing `observation_fit`. So the
goal needs exactly one decision lift; the receipts name its three missing parts, which are the
driver's derived assertions.

Reach. Every compile budget and every control history, with any command budget per decision.
Does not establish: the generic layer under `stable` and `taskStable`, any per-program obligation
of Atomic, Timeout or the queue crew, progress, or anything of an unfunded host history.
-/

set_option autoImplicit false

namespace Effect4.Program.RemainingWork.OutlineDriver

open Effect4 Effect4.Machine Effect4.Program Effect4.Run

/-! ## 1. The schema -/

/-- **The classes of an outline**, at a proof world. -/
structure Classes (World : Type) where
  /-- The code a resume may install at a fiber parked at a token. -/
  reply : World → FiberId → Nat → NCode → Prop
  /-- The exit a finish may publish for a fiber. -/
  final : World → FiberId → ExitV → Prop
  /-- The outline a live fiber's record keeps while its loop or delivery is queued. -/
  live : World → SourceScope.SourceFiber → Prop

/-- **The derived command assertion.** Each queued command is read off the classes: a queued loop
or delivery names a live fiber in its outline, a resume installs a classed code at its parked
token, and a finish publishes a classed exit from an empty stack. The empty stack is the first of
the program-independent structural clauses (`Initialized.FinishEmpty`, `StageConfiguration.FinishAt`
state it per program today); the runtime layer proves them once. Every other command carries no
program fact here. -/
def CmdAt {World : Type} (C : Classes World) (w : World) (m : NativeMachine) :
    SourceScope.SourceCommand → Prop
  | .loop owner _ => ∀ f, m.fiber? owner = some f → C.live w f
  | .deliver owner _ => ∀ f, m.fiber? owner = some f → C.live w f
  | .resume owner token code => ∀ f, m.fiber? owner = some f → f.parked = .withGuard token →
      C.reply w owner token code
  | .finish owner exit => C.final w owner exit ∧ ∀ f, m.fiber? owner = some f → f.frame.stack = []
  | _ => True

/-- **The derived snapshot assertion**: each drained resume installs a classed code. -/
def TaskAt {World : Type} (C : Classes World) (w : World) (m : NativeMachine) :
    SourceScope.SourceTask → Prop
  | .resume owner token code => ∀ f, m.fiber? owner = some f → f.parked = .withGuard token →
      C.reply w owner token code
  | _ => True

/-- **An outline**: the world and its order, the machine assertion, the classes, and the answers
a session admits. -/
structure Outline (World : Type) where
  order : Effect4.Laws.Effects.WorldOrder World
  J : World → NativeMachine → Prop
  classes : Classes World
  admits : World → NativeMachine → NativeDecision → Prop

/-- **The per-program obligations of the driver.** Each is local: one command with its own
derived entry, one edit outside the loop, or one law of the classes. The command obligation
reads only the commands the step emits (`driveStep … []`); the frame law
`Lift.driveStep_append` carries the suffix, so no obligation names a pending suffix or a
detached snapshot. -/
structure Obligations (root : NativeEff) (table : RowTable) {World : Type} (O : Outline World) :
    Prop where
  /-- The load meets `J`. -/
  load : ∀ compileFuel, ∃ w, O.J w (Api.load root compileFuel)
  /-- One command, read with its own derived entry, keeps `J` at a later world and classes every
  command it emits. Native steps (loop, deliver) carry the write sites and births. -/
  command : letI := evaluatorFor root table
    ∀ w (m : NativeMachine) (c : SourceScope.SourceCommand), m.stuck = none → O.J w m →
      CmdAt O.classes w m c →
      ∃ w', O.order.le w w' ∧ O.J w' (driveStep (interpOf root table) m c []).1 ∧
        ∀ c' ∈ (driveStep (interpOf root table) m c []).2,
          CmdAt O.classes w' (driveStep (interpOf root table) m c []).1 c'
  /-- A step that moves another fiber keeps a queued entry's class, at the later world. -/
  stable : letI := evaluatorFor root table
    ∀ w w' (m : NativeMachine) (c c' : SourceScope.SourceCommand), m.stuck = none → O.J w m →
      CmdAt O.classes w m c → O.order.le w w' → CmdAt O.classes w m c' →
        CmdAt O.classes w' (driveStep (interpOf root table) m c []).1 c'
  /-- A step keeps a drained snapshot task's class, at the later world. Its program part is the
  classes' monotonicity; its generic part is the guard's token freshness. -/
  taskStable : letI := evaluatorFor root table
    ∀ w w' (m : NativeMachine) (c : SourceScope.SourceCommand) (t : SourceScope.SourceTask),
      m.stuck = none → O.J w m → CmdAt O.classes w m c → O.order.le w w' → TaskAt O.classes w m t →
        TaskAt O.classes w' (driveStep (interpOf root table) m c []).1 t
  /-- A drained dispatcher's tasks are classed, and the drain keeps `J`. -/
  drain : ∀ w (m : NativeMachine) owner (f : SourceScope.SourceFiber), O.J w m →
    m.fiber? owner = some f →
    O.J w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner) ∧
      ∀ t ∈ (f.dispatcher.drain).1,
        TaskAt O.classes w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner) t
  /-- The edits outside the loop keep `J`: the `ranTask` event, the yield verdict, the interrupt
  record, the middleware latch and the clock. -/
  edits : letI := evaluatorFor root table
    (∀ w (m : NativeMachine) owner (t : SourceScope.SourceTask), O.J w m →
      O.J w (m.emit [RunEvent.ranTask owner t])) ∧
    (∀ w (m : NativeMachine) id (v : Bool), O.J w m →
      O.J w (m.modify id fun f => { f with yieldOverride := some v })) ∧
    (∀ w (m : NativeMachine) who extra target (t : SourceScope.SourceFiber), O.J w m →
      m.fiber? target = some t → O.J w (Lift.interruptEdit (interpOf root table) m who extra target t)) ∧
    (∀ w (m : NativeMachine), O.J w m → O.J w { m with middlewareInstalled := true }) ∧
    (∀ w (m : NativeMachine) millis owed st, O.J w m → m.stuck = none →
      (interpOf root table).clockStep millis m.state = (owed, st) →
      ∃ w', O.order.le w w' ∧ O.J w' (drainOwed { m with state := st } owed.toList).1 ∧
        ∀ c ∈ (drainOwed { m with state := st } owed.toList).2,
          CmdAt O.classes w' (drainOwed { m with state := st } owed.toList).1 c)
  /-- An admitted host answer installs a classed code and keeps `J`. -/
  answer : letI := evaluatorFor root table
    ∀ w (m : NativeMachine) id token answer, O.J w m → m.stuck = none →
      O.admits w m (.answerAsync id token answer) →
      O.J w { m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1 } ∧
        CmdAt O.classes w
          { m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1 }
          (.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2)

/-- One command's step from a configuration whose whole queue and snapshot carry their classes:
the emitted commands by `command`, the suffix by `stable` and the frame law, the snapshot by
`taskStable`. The step shared by the driver's `step` and `answer` fields. -/
theorem step_of (root : NativeEff) (table : RowTable) {World : Type} (O : Outline World)
    (ob : Obligations root table O) :
    letI := evaluatorFor root table
    ∀ (ts : List SourceScope.SourceTask) w (m : NativeMachine) (c : SourceScope.SourceCommand)
      (rest : List SourceScope.SourceCommand),
      m.stuck = none → O.J w m → (∀ c' ∈ c :: rest, CmdAt O.classes w m c') →
      (∀ t ∈ ts, TaskAt O.classes w m t) →
      ∃ w', O.order.le w w' ∧
        Lift.Guarded O.J (fun w m commands => ∀ c ∈ commands, CmdAt O.classes w m c)
          (fun w m tasks => ∀ t ∈ tasks, TaskAt O.classes w m t) ts w'
          (driveStep (interpOf root table) m c rest).1 (driveStep (interpOf root table) m c rest).2 := by
  letI := evaluatorFor root table
  intro ts w m c rest running held queued snapshot
  obtain ⟨w', later, kept, emitted⟩ := ob.command w m c running held (queued c (.head _))
  have framed := Lift.driveStep_append (interpOf root table) m c [] rest
  rw [List.nil_append] at framed
  obtain ⟨same, shape⟩ := framed
  refine ⟨w', later, same ▸ kept, fun _ => ⟨?_, ?_⟩⟩
  · intro c' member
    rw [same]
    rcases shape with appended | ⟨_, empty, _⟩
    · rw [appended] at member
      rcases List.mem_append.mp member with here | there
      · exact emitted c' here
      · exact ob.stable w w' m c c' running held (queued c (.head _)) later (queued c' (.tail _ there))
    · rw [empty] at member
      cases member
  · intro t member
    rw [same]
    exact ob.taskStable w w' m c t running held (queued c (.head _)) later (snapshot t member)

/-- **The outline driver.** The derived command and snapshot assertions are carried through every
command and decision, so the per-program obligations give a decision lift. This is the outer
layer of the four existing drivers' transports, proved once. Its premises `stable` and
`taskStable` are local; their generic part (the guard's token freshness, the fibers a command does
not touch) is the next layer and is not proved here. -/
theorem outline_driver (root : NativeEff) (table : RowTable) {World : Type} (O : Outline World)
    (obligations : Obligations root table O) :
    letI := evaluatorFor root table
    Lift.DecisionLift O.order (interpOf root table) O.J
      (fun w m commands => ∀ c ∈ commands, CmdAt O.classes w m c)
      (fun w m tasks => ∀ t ∈ tasks, TaskAt O.classes w m t) O.admits := by
  letI := evaluatorFor root table
  have stepped := step_of root table O obligations
  refine {
    step := ?_, nil := ?_, evaluate := ?_, drain := ?_, ran := ?_, task := ?_, skip := ?_,
    yield := ?_, interrupt := ?_, middleware := ?_, clockNone := ?_, clockSome := ?_, answer := ?_ }
  · intro ts w m c rest running guarded
    exact stepped ts w m c rest running guarded.1 (guarded.2 running).1 (guarded.2 running).2
  · intro w m t member
    cases member
  · intro w m id held running c member
    rcases List.mem_cons.mp member with same | later
    · rw [same]
      trivial
    · rw [List.mem_singleton.mp later]
      trivial
  · intro w m owner f held found
    exact obligations.drain w m owner f held found
  · intro w m owner t held
    exact obligations.edits.1 w m owner t held
  · intro w m owner t ts held running snapshot
    refine ⟨?_, fun t' member => snapshot t' (.tail _ member)⟩
    intro c member
    cases t with
    | start child =>
      rcases List.mem_cons.mp member with same | later
      · rw [same]
        trivial
      · rw [List.mem_singleton.mp later]
        trivial
    | resume target token answer =>
      rcases List.mem_cons.mp member with same | later
      · rw [same]
        exact snapshot (.resume target token answer) (.head _)
      · rw [List.mem_singleton.mp later]
        trivial
    | wake list phase =>
      rcases List.mem_cons.mp member with same | later
      · rw [same]
        trivial
      · rw [List.mem_singleton.mp later]
        trivial
  · intro w m t ts snapshot t' member
    exact snapshot t' (.tail _ member)
  · intro w m id v held
    exact obligations.edits.2.1 w m id v held
  · intro w m who extra target t held found
    exact obligations.edits.2.2.1 w m who extra target t held found
  · intro w m held
    exact obligations.edits.2.2.2.1 w m held
  · intro w m millis st held running found
    obtain ⟨w', later, kept, _⟩ := obligations.edits.2.2.2.2 w m millis none st held running found
    exact ⟨w', later, kept⟩
  · intro w m millis owed st held running found
    obtain ⟨w', later, kept, emitted⟩ :=
      obligations.edits.2.2.2.2 w m millis (some owed) st held running found
    refine ⟨w', later, kept, fun _ c member => ?_⟩
    rcases List.mem_append.mp member with here | there
    · exact emitted c here
    · rw [List.mem_singleton.mp there]
      trivial
  · intro w m id token answer held running admitted
    obtain ⟨prepared, resumed⟩ := obligations.answer w m id token answer held running admitted
    refine stepped [] w { m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1 }
      (.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2) [Cmd.drainDue]
      running prepared ?_ ?_
    · intro c member
      rcases List.mem_cons.mp member with same | later
      · rw [same]
        exact resumed
      · rw [List.mem_singleton.mp later]
        trivial
    · intro t member
      cases member

/-! ## 2. The history lift (proved) -/

/-- **Any decision lift of a program carries its assertion along every control history**, at
every command budget of every decision. -/
theorem history_of_lift (b : Api.Built) (compileFuel : Nat) {World : Type}
    (order : Effect4.Laws.Effects.WorldOrder World) (J : World → NativeMachine → Prop)
    (I : World → NativeMachine → List SourceScope.SourceCommand → Prop)
    (O : World → NativeMachine → List SourceScope.SourceTask → Prop)
    (lift : letI := evaluatorFor b.program b.table
      Lift.DecisionLift order (interpOf b.program b.table) J I O (fun _ _ d => IsControl d))
    (load : ∃ w, J w (Api.load b.program compileFuel)) :
    ∀ m, ControlHistory b compileFuel m → ∃ w, J w m := by
  letI := evaluatorFor b.program b.table
  rintro m ⟨rows, controls, rfl⟩
  have fold : ∀ (rows : List (Nat × NativeDecision)) (before : NativeMachine),
      (∀ row ∈ rows, IsControl row.2) → (∃ w, J w before) →
      ∃ w, J w (rows.foldl (stepBy b) before) := by
    intro rows
    induction rows with
    | nil => intro before _ held; exact held
    | cons row rest ih =>
      intro before allowed held
      obtain ⟨w, holds⟩ := held
      obtain ⟨w', _, next⟩ := Lift.stepDecisionState_lift lift row.1 w before row.2 holds
        (allowed row (.head _))
      exact ih (stepBy b before row) (fun x member => allowed x (.tail _ member)) ⟨w', next⟩
  exact fold rows _ controls load

/-- The driver's lift, carried along every control history. -/
theorem outline_history (b : Api.Built) (compileFuel : Nat) {World : Type} (O : Outline World)
    (control : ∀ w m d, IsControl d → O.admits w m d)
    (obligations : Obligations b.program b.table O) :
    ∀ m, ControlHistory b compileFuel m → ∃ w, O.J w m := by
  letI := evaluatorFor b.program b.table
  have driven := outline_driver b.program b.table O obligations
  have lift : Lift.DecisionLift O.order (interpOf b.program b.table) O.J
      (fun w m commands => ∀ c ∈ commands, CmdAt O.classes w m c)
      (fun w m tasks => ∀ t ∈ tasks, TaskAt O.classes w m t) (fun _ _ d => IsControl d) :=
    { driven with
      answer := fun w m id token answer held running admitted =>
        driven.answer w m id token answer held running (control w m _ admitted) }
  exact history_of_lift b compileFuel O.order O.J _ _ lift (obligations.load compileFuel)

/-! ## 3. The probe on `Atomic.Store.shop_stages` -/

open Test.Dogfood.Scenario Test.Dogfood.Scenario.Atomic

/-- **The goal from one decision lift** (proved). Any decision lift at the stage world whose
assertion reads to the stage observation gives `shop_stages`'s statement, word for word. -/
theorem shop_stages_of_lift (b : Api.Built) (compileFuel : Nat)
    (J : StageWorld.World → NativeMachine → Prop)
    (I : StageWorld.World → NativeMachine → List SourceScope.SourceCommand → Prop)
    (O : StageWorld.World → NativeMachine → List SourceScope.SourceTask → Prop)
    (lift : letI := evaluatorFor b.program b.table
      Lift.DecisionLift StageWorld.order (interpOf b.program b.table) J I O (fun _ _ d => IsControl d))
    (load : ∃ w, J w (Api.load b.program compileFuel))
    (reads : ∀ w m, J w m → ∃ g, Store.StagesFit g (Store.observeM m)) :
    ∀ m, ControlHistory b compileFuel m → ∃ g, Store.StagesFit g (Store.observeM m) := by
  intro m history
  obtain ⟨w, held⟩ := history_of_lift b compileFuel StageWorld.order J I O lift load m history
  exact reads w m held

/-- The configured phase reads to the stage observation: the existing `observation_fit`. -/
theorem configured_reads (w : StageWorld.World) (m : NativeMachine)
    (heap : StageWorld.HeapAt w m.state) (published : StageWorld.Published w m) :
    ∃ g, Store.StagesFit g (Store.observeM m) :=
  ⟨w.stages, StageWorld.observation_fit w m heap published⟩

/-- The statement `shop_stages_of_lift` concludes is the planned goal's. -/
theorem same_statement (b : Api.Built) (hb : Effect4.Api.Author.build (shop .none) = .ok b)
    (compileFuel : Nat) :
    (∀ m, ControlHistory b compileFuel m → ∃ g, Store.StagesFit g (Store.observeM m)) =
      type_of% (Store.shop_stages b hb compileFuel) := rfl

end Effect4.Program.RemainingWork.OutlineDriver

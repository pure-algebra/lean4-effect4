import Effect4.Laws.Program.AnswerSlots.InitializedCommands
import Effect4.Laws.Program.ParkedShapeRun

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Question: the crew initializer reaches tracked-child cleanup only after its allocations.
Reach: every actual command, allocation growth, and the source action's track permission.
Consumer: the initialized terminal-demand producer and the crew log histories.
This invariant supplies no child completion or cleanup progress.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program
namespace ChildrenReady

theorem fields {spec : Spec} {first last : NativeMachine} (held : ChildrenReady spec first)
    (fibers : last.fibers = first.fibers) (state : last.state = first.state) : ChildrenReady spec last := by
  intro fiber member nonempty
  rw [state]
  exact held fiber (fibers ▸ member) nonempty

theorem found {spec : Spec} {machine : NativeMachine} (held : ChildrenReady spec machine)
    {id : FiberId} {fiber : SourceScope.SourceFiber} (lookup : machine.fiber? id = some fiber) :
    fiber.children ≠ [] → Ready spec ⟨fiber.id, machine.state⟩ :=
  held fiber (RunMachine.mem_of_fiber? lookup)

theorem state {spec : Spec} {machine : NativeMachine} (held : ChildrenReady spec machine) (next : Stores)
    (growth : Bounds machine.state.refs.length machine.state.deferreds.cells.length next) :
    ChildrenReady spec {machine with state := next} := by
  intro fiber member nonempty
  have before := held fiber member nonempty
  exact ⟨Nat.le_trans before.1 growth.1, Nat.le_trans before.2 growth.2⟩

theorem update {spec : Spec} {machine : NativeMachine} (held : ChildrenReady spec machine)
    (fiber : SourceScope.SourceFiber) (good : fiber.children ≠ [] → Ready spec ⟨fiber.id, machine.state⟩) :
    ChildrenReady spec (machine.update fiber) := ChildrenReady.install spec machine fiber held good

theorem modify {spec : Spec} {machine : NativeMachine} (held : ChildrenReady spec machine)
    (id : FiberId) (edit : SourceScope.SourceFiber → SourceScope.SourceFiber)
    (empty : ∀ fiber, fiber.children = [] → (edit fiber).children = []) :
    ChildrenReady spec (machine.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact held
  · rename_i fiber lookup
    apply held.update
    intro nonempty
    exact held.found (fiber := fiber) lookup (fun absent => nonempty (empty fiber absent))

theorem update_found {spec : Spec} {machine : NativeMachine} (held : ChildrenReady spec machine)
    {id : FiberId} {fiber : SourceScope.SourceFiber} (lookup : machine.fiber? id = some fiber)
    (next : SourceScope.SourceFiber) (children : next.children = fiber.children) :
    ChildrenReady spec (machine.update next) :=
  held.update next (fun nonempty => held.found (fiber := fiber) lookup (fun absent => nonempty (children.trans absent)))

theorem fiberEdits (spec : Spec) (machine : NativeMachine) (edits : List (FiberEdit Err Defect FiberId Ann))
    (held : ChildrenReady spec machine) : ChildrenReady spec (applyFiberEdits edits machine).1 := by
  apply ChildrenReady.interferes spec machine _ held (Moves.InterferesWithLookup.fiberEdits edits machine).backward
  all_goals rw [RunMachine.applyFiberEdits_state]
  all_goals exact Nat.le_refl _

theorem fiberEdit (spec : Spec) (machine : NativeMachine) (edit : FiberEdit Err Defect FiberId Ann)
    (held : ChildrenReady spec machine) : ChildrenReady spec (applyFiberEdit edit machine).1 := by
  apply ChildrenReady.interferes spec machine _ held (Moves.InterferesWithLookup.fiberEdit edit machine).backward
  all_goals rw [RunMachine.applyFiberEdit_state]
  all_goals exact Nat.le_refl _

theorem settle (spec : Spec) (id : FiberId) (rest : List Guard.NCmd) (next : SourceScope.SourceIteration)
    (held : ChildrenReady spec next.machine)
    (good : next.fiber.children ≠ [] → Ready spec ⟨next.fiber.id, next.machine.state⟩) :
    ChildrenReady spec (Machine.settle id rest next).1 := by
  have outcome (next : SourceScope.SourceIteration) (held : ChildrenReady spec next.machine)
      (good : next.fiber.children ≠ [] → Ready spec ⟨next.fiber.id, next.machine.state⟩) :
      ChildrenReady spec (settleOutcome id rest next).1 := by
    unfold settleOutcome
    split
    · exact held.update _ good
    · exact held.update _ good
    · split
      · exact held.update _ good
      · exact held.update _ good
    · exact held.update _ good
    · exact held.update _ good
    · exact (held.update {next.fiber with running := false} good).fields rfl rfl
  unfold Machine.settle
  split
  · exact outcome next held good
  · dsimp only
    have changed := fiberEdits spec _ next.edits (held.update next.fiber good)
    split
    · exact changed.fields rfl rfl
    · rename_i owner lookup
      exact outcome _ changed (changed.found (fiber := owner) lookup)

theorem settle_one {spec : Spec} {machine : NativeMachine} (held : ChildrenReady spec machine)
    (id : FiberId) (rest : List Guard.NCmd) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann)
    (good : fiber.children ≠ [] → Ready spec ⟨fiber.id, machine.state⟩) :
    ChildrenReady spec (Machine.settle id rest ⟨machine, fiber, yielding, outcome, [], []⟩).1 :=
  ChildrenReady.settle spec id rest _ held good

theorem interruptEach (spec : Spec) (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId) :
    ∀ acc : NativeMachine × List Guard.NCmd, ChildrenReady spec acc.1 →
      ChildrenReady spec (Machine.interruptEach (interpOf spec.root spec.table) who extra targets acc).1 := by
  induction targets with
  | nil => intro acc held; exact held
  | cons target rest ih =>
    intro acc held
    unfold Machine.interruptEach
    rw [List.foldl_cons]
    split
    · exact ih acc held
    · rename_i fiber lookup
      apply ih
      have children := otherEdit_children (Moves.OtherEdit.interrupted (interpOf spec.root spec.table) fiber (some who) extra)
      generalize interruptRecord (interpOf spec.root spec.table) (some who) extra fiber = pair at children ⊢
      obtain ⟨next, immediate⟩ := pair
      exact (held.update_found lookup next children).fields rfl rfl

theorem fireObserver (spec : Spec) (id : FiberId) (exit : ExitV) (acc : NativeMachine × List Guard.NCmd)
    (observer : Observer) (held : ChildrenReady spec acc.1) :
    ChildrenReady spec (Machine.fireObserver (interpOf spec.root spec.table) id exit acc observer).1 := by
  have base : ChildrenReady spec (acc.1.emit [.observerFired id observer]) := held.fields rfl rfl
  unfold Machine.fireObserver
  dsimp only
  split
  · exact base
  · exact base.modify _ _ (fun _ empty => by rw [empty]; rfl)
  · split
    · exact base.fields rfl rfl
    · rename_i state actual
      have counts := (count_hooks spec [] _ _).drop _ _ acc.1.state state ⟨rfl, rfl⟩ actual
      exact base.state state ⟨Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩
  · rename_i waiter token
    split
    · exact base
    · split
      · exact base
      · rename_i pending _
        split
        · have changed : ChildrenReady spec (if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
              Machine.interruptEach (interpOf spec.root spec.table) waiter ((interpOf spec.root spec.table).stackAnnotations waiter)
                pending.remaining (acc.1.emit [.observerFired id (.countdown waiter token)], [])
              else (acc.1.emit [.observerFired id (.countdown waiter token)], [])).1 := by
            split
            · exact interruptEach spec waiter _ pending.remaining _ base
            · exact base
          split
          · exact changed
          · rename_i current lookup
            split
            · exact changed
            · split
              · exact changed.update_found lookup _ rfl
              · apply fiberEdit spec
                apply changed.update_found lookup
                rfl
        · exact base
  · split
    · exact base
    · split <;> exact base.fields rfl rfl
  · exact base.fields rfl rfl

theorem exitFiber (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (exit : ExitV)
    (held : ChildrenReady spec machine) (good : fiber.children ≠ [] → Ready spec ⟨fiber.id, machine.state⟩) :
    ChildrenReady spec (Machine.exitFiber (interpOf spec.root spec.table) machine fiber exit).1 := by
  unfold Machine.exitFiber
  split
  · unfold Machine.exitFiber.exitInterruptChildren
    change ChildrenReady spec (machine.update _)
    apply held.update
    exact good
  · unfold Machine.exitFiber.exitStore
    dsimp only
    have published : ChildrenReady spec ((machine.update (fiber.publish exit)).emit [.exited fiber.id exit]) :=
      (held.update (fiber.publish exit) good).fields rfl rfl
    split
    · exact published.update _ (fun nonempty => (nonempty rfl).elim)
    · exact published

theorem drainOwed (spec : Spec) (machine : NativeMachine) (held : ChildrenReady spec machine) :
    ∀ owed : List (Owed NCode), ChildrenReady spec (Machine.drainOwed machine owed).1
  | [] => held
  | first :: rest => by
    simp only [Machine.drainOwed]
    cases first.mode with
    | now => exact drainOwed spec machine held rest
    | scheduled owner priority =>
      apply drainOwed spec
      unfold RunMachine.postTask
      split
      · exact held.fields rfl rfl
      · rename_i fiber lookup
        change ChildrenReady spec (machine.update _)
        apply held.update_found lookup
        rfl

/-- Only tracking adds a child; its actual source action supplies readiness. -/
theorem command (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd) (rest : List Guard.NCmd)
    (held : ChildrenReady spec machine) (track : TrackDemand spec machine command) :
    letI := evaluatorFor spec.root spec.table
    ChildrenReady spec (driveStep (interpOf spec.root spec.table) machine command rest).1 := by
  letI := evaluatorFor spec.root spec.table
  cases command with
  | loop id yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      apply ChildrenReady.settle spec id rest _ (iteration_children spec machine fiber yielding held)
      intro nonempty
      have footprint := Moves.iteration_footprint spec.root spec.table (interpOf spec.root spec.table) machine fiber yielding
      have ready := held.found (fiber := fiber) lookup (fun empty => nonempty (footprint.children.trans empty))
      have growth := iteration_growth spec machine fiber yielding
      exact ⟨Nat.le_trans ready.1 growth.1, Nat.le_trans ready.2 growth.2⟩
  | deliver id yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      apply ChildrenReady.settle spec id rest _ (native_children spec machine fiber yielding held)
      intro nonempty
      have footprint := Moves.evaluateNative_footprint spec.root spec.table machine fiber yielding
      have ready := held.found (fiber := fiber) lookup (fun empty => nonempty (footprint.children.trans empty))
      have growth := native_growth spec machine fiber yielding
      exact ⟨Nat.le_trans ready.1 growth.1, Nat.le_trans ready.2 growth.2⟩
  | evaluate id =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      split
      · exact held
      · change ChildrenReady spec (machine.update _)
        apply held.update_found lookup
        rfl
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      split
      · split
        · change ChildrenReady spec (machine.update _)
          apply held.update_found lookup
          rfl
        · exact held
      · exact held
  | launch raceId =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · split
        · exact held
        · split
          · exact held
          · intro fiber member nonempty
            rcases List.mem_append.mp member with old | fresh
            · exact held fiber old nonempty
            · rw [List.mem_singleton.mp fresh] at nonempty
              exact (nonempty rfl).elim
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · rename_i race fiber raceFound lookup
      split
      · rename_i exit exited
        have next := fireObserver spec child exit
          (machine.updateRace {race with state := {race.state with live := race.state.live ++ [child]}}, [])
          (.raceCallback raceId) (held.fields rfl rfl)
        generalize Machine.fireObserver (interpOf spec.root spec.table) child exit
          (machine.updateRace {race with state := {race.state with live := race.state.live ++ [child]}}, [])
          (.raceCallback raceId) = pair at next ⊢
        obtain ⟨changed, nested⟩ := pair
        exact next
      · apply ChildrenReady.modify
        · exact held.fields rfl rfl
        · intro fiber empty
          exact empty
    · exact held
  | registrationDone raceId yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i race raceFound
      split
      · exact held.fields rfl rfl
      · rename_i fiber lookup
        have original : machine.fiber? race.host = some fiber := lookup
        split
        · apply settle_one
          · exact held.fields rfl rfl
          · exact held.found (fiber := fiber) original
        · apply settle_one
          · exact held.fields rfl rfl
          · exact held.found (fiber := fiber) original
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      have children := otherEdit_children (Moves.OtherEdit.interrupted (interpOf spec.root spec.table) fiber who extra)
      generalize interruptRecord (interpOf spec.root spec.table) who extra fiber = pair at children ⊢
      obtain ⟨next, immediate⟩ := pair
      exact (held.update_found lookup next children).fields rfl rfl
  | afterInterrupt host yielding kind =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      apply settle_one held
      exact held.found (fiber := fiber) lookup
  | closeParAwait host yielding fibers =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      apply settle_one held
      exact held.found (fiber := fiber) lookup
  | raceCancel raceId host yielding remaining visited =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · split <;> exact held
  | trackChild parent child =>
    change Ready spec ⟨⟨0⟩, machine.state⟩ at track
    simp only [driveStep]
    split
    · intro fiber member nonempty
      exact track
    · split
      · intro fiber member nonempty
        exact track
      · intro fiber member nonempty
        simpa only [Ready, StatePreservation.modify_state] using track
  | observe id exit observer =>
    simp only [driveStep]
    have next := fireObserver spec id exit (machine, []) observer held
    generalize Machine.fireObserver (interpOf spec.root spec.table) id exit (machine, []) observer = pair at next ⊢
    obtain ⟨changed, nested⟩ := pair
    exact next
  | exitDone id =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      exact held.update _ (fun nonempty => (nonempty rfl).elim)
  | link mode scope target who extra =>
    have counts := StatePreservation.link_with (interpOf spec.root spec.table)
      (Counts machine.state.refs.length machine.state.deferreds.cells.length)
      (by
        have hooks := count_hooks spec [] machine.state.refs.length machine.state.deferreds.cells.length
        exact ⟨hooks.link, hooks.drop, hooks.due, hooks.wake⟩) machine mode scope target who extra ⟨rfl, rfl⟩
    exact ChildrenReady.interferes spec machine _ held
      (Moves.Interferes.linkScope (interpOf spec.root spec.table) machine mode scope target who extra)
      (Nat.le_of_eq counts.1.symm) (Nat.le_of_eq counts.2.symm)
  | finish id exit =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber lookup
      have next := exitFiber spec machine {fiber with running := false} exit held (held.found (fiber := fiber) lookup)
      generalize Machine.exitFiber (interpOf spec.root spec.table) machine {fiber with running := false} exit = pair at next ⊢
      obtain ⟨changed, nested⟩ := pair
      exact next
  | drainDue =>
    simp only [driveStep]
    apply drainOwed spec
    exact held.state _ ⟨Nat.le_refl _, Nat.le_refl _⟩
  | wake key phase =>
    have counts := (count_hooks spec [] _ _).wake key phase machine.state ⟨rfl, rfl⟩
    exact held.state _ ⟨Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩
end ChildrenReady
end Effect4.Program.AnswerSlots.Initialized

namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Outside decisions retain tracked-child readiness through their actual allocation counts. -/
theorem ChildrenReady.machine_edits (spec : Spec) :
    Lift.MachineEdits (interpOf spec.root spec.table) (ChildrenReady spec) where
  drain := by
    intro machine owner fiber held lookup
    exact (held.update_found lookup {fiber with dispatcher := fiber.dispatcher.drain.2} rfl).fields rfl rfl
  ran := fun _ _ _ held => held.fields rfl rfl
  yield := fun _ id _ held => held.modify id _ (fun _ empty => empty)
  interrupt := by
    intro machine who extra target fiber held lookup
    have children := otherEdit_children (Moves.OtherEdit.interrupted (interpOf spec.root spec.table) fiber who extra)
    unfold Lift.interruptEdit
    dsimp only
    split
    · exact (held.fields rfl rfl).update_found lookup _ children
    · exact (held.fields rfl rfl).update_found lookup _ children
  middleware := fun _ held => held.fields rfl rfl
  clock := fun _ _ held _ => held.state _ ⟨Nat.le_refl _, Nat.le_refl _⟩
  owed := fun machine owed held => ChildrenReady.drainOwed spec machine held [owed]
  prepare := by
    intro machine id token answer held
    have counts := prepare_counts spec machine id token answer
    exact held.state _ ⟨Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩
end Effect4.Program.AnswerSlots.Initialized

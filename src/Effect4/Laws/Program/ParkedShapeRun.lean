import Effect4.Laws.Program.ParkedShape
import Effect4.Laws.Program.Guard.Lift
import Effect4.Laws.Machine.LiftMachineFact

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Question: parked heads retain the reply class consumed by the shared crew history.
Reach: every native command under the existing command authority and every decision edit.
Consumer: the initialized crew command producer derives its parked demand from current code.
The observation establishes no progress or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Program.ParkedShape
open Effect4 Effect4.Machine Effect4.Program
abbrev Command := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev Interp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev Iteration := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

theorem Configuration.fields {first last : NativeMachine} (held : Configuration first)
    (same : last.fibers = first.fibers) : Configuration last := fun fiber member => held fiber (same ▸ member)

theorem Configuration.found {machine : NativeMachine} (held : Configuration machine)
    {id : FiberId} {fiber : Fiber} (found : machine.fiber? id = some fiber) : Held fiber :=
  held fiber (List.mem_of_find?_eq_some found)

theorem Configuration.update {machine : NativeMachine} (held : Configuration machine)
    (fiber : Fiber) (good : Held fiber) : Configuration (machine.update fiber) := by
  intro next member
  obtain ⟨old, present, same⟩ := List.mem_map.mp member
  rw [← same]
  change Held (if old.id = fiber.id then fiber else old)
  split
  · exact good
  · exact held old present

theorem Configuration.modify {machine : NativeMachine} (held : Configuration machine)
    (id : FiberId) (change : Fiber → Fiber) (kept : ∀ fiber, Held fiber → Held (change fiber)) :
    Configuration (machine.modify id change) := by
  unfold RunMachine.modify
  split
  · exact held
  · rename_i fiber found
    exact held.update _ (kept fiber (held.found found))

theorem Configuration.update_found {machine : NativeMachine} (held : Configuration machine)
    {id : FiberId} {fiber : Fiber} (found : machine.fiber? id = some fiber) (next : Fiber)
    (park : next.parked = fiber.parked) (current : next.frame.current = fiber.frame.current) :
    Configuration (machine.update next) := held.update next (ParkedShape.fields (held.found found) park current)

theorem Configuration.fiberEdit (edit : FiberEdit Err Defect FiberId Ann)
    (machine : NativeMachine) (held : Configuration machine) :
    Configuration (applyFiberEdit edit machine).1 :=
  interferes (Moves.InterferesWithLookup.fiberEdit edit machine).backward held

theorem Configuration.fiberEdits (edits : List (FiberEdit Err Defect FiberId Ann))
    (machine : NativeMachine) (held : Configuration machine) :
    Configuration (applyFiberEdits edits machine).1 :=
  interferes (Moves.InterferesWithLookup.fiberEdits edits machine).backward held

/-- Settlement only clears a park or retains its current head after the shared edit word. -/
theorem Configuration.settle (id : FiberId) (rest : List Command) (next : Iteration)
    (held : Configuration next.machine) (good : Held next.fiber) :
    Configuration (Machine.settle id rest next).1 := by
  have outcome (next : Iteration) (held : Configuration next.machine)
      (good : Held next.fiber) : Configuration (settleOutcome id rest next).1 := by
    unfold settleOutcome
    split
    · exact held.update next.fiber good
    · exact held.update next.fiber good
    · split
      · exact held.update {next.fiber with parked := .notParked, pending := []} (unparked rfl)
      · exact held.update {next.fiber with running := false} (ParkedShape.fields good rfl rfl)
    · exact held.update next.fiber good
    · exact held.update next.fiber good
    · exact (held.update {next.fiber with running := false} (ParkedShape.fields good rfl rfl)).fields rfl
  unfold Machine.settle
  split
  · exact outcome next held good
  · dsimp only
    have changed := Configuration.fiberEdits next.edits _ (held.update next.fiber good)
    split
    · exact changed.fields rfl
    · rename_i owner found
      exact outcome _ changed (changed.found found)

theorem Configuration.settle_one {machine : NativeMachine} (held : Configuration machine)
    (id : FiberId) (rest : List Command) (fiber : Fiber) (yielding : Bool)
    (outcome : Outcome EffName EffThunk Val Err Defect FiberId Ann) (good : Held fiber) :
    Configuration (Machine.settle id rest ⟨machine, fiber, yielding, outcome, [], []⟩).1 :=
  Configuration.settle id rest _ held good

/-- The fail-fast countdown uses the existing interruption operation at each target. -/
theorem Configuration.interruptEach (interp : Interp) (who : FiberId) (extra : ReasonAnnotations Ann)
    (targets : List FiberId) : ∀ (acc : NativeMachine × List Command), Configuration acc.1 →
      Configuration (Machine.interruptEach interp who extra targets acc).1 := by
  induction targets with
  | nil => intro acc held; exact held
  | cons target rest ih =>
    intro acc held
    unfold Machine.interruptEach
    rw [List.foldl_cons]
    split
    · exact ih acc held
    · rename_i fiber found
      apply ih
      have recorded := interruption (interruptCause interp (some who) extra fiber.id) fiber (held.found found)
      change Held (interruptRecord interp (some who) extra fiber).1 at recorded
      generalize interruptRecord interp (some who) extra fiber = result at recorded ⊢
      obtain ⟨next, immediate⟩ := result
      exact (held.update next recorded).fields rfl

/-- Observer delivery retains heads; only its actual interruption word can replace code. -/
theorem Configuration.fireObserver (interp : Interp) (id : FiberId) (exit : ExitV)
    (acc : NativeMachine × List Command) (observer : Observer) (held : Configuration acc.1) :
    Configuration (Machine.fireObserver interp id exit acc observer).1 := by
  have base : Configuration (acc.1.emit [.observerFired id observer]) := held.fields rfl
  unfold Machine.fireObserver
  dsimp only
  split
  · exact base
  · exact base.modify _ _ (fun _ good => ParkedShape.fields good rfl rfl)
  · split <;> exact base.fields rfl
  · rename_i waiter token
    split
    · exact base
    · split
      · exact base
      · rename_i pending _
        split
        · have changed : Configuration (if pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess then
              Machine.interruptEach interp waiter (interp.stackAnnotations waiter) pending.remaining
                (acc.1.emit [.observerFired id (.countdown waiter token)], [])
              else (acc.1.emit [.observerFired id (.countdown waiter token)], [])).1 := by
            split
            · exact Configuration.interruptEach interp waiter _ pending.remaining _ base
            · exact base
          split
          · exact changed
          · rename_i current found
            split
            · exact changed
            · split
              · exact changed.update_found found _ rfl rfl
              · exact Configuration.fiberEdit _ _ (changed.update_found found _ rfl rfl)
        · exact base
  · split
    · exact base
    · split <;> exact base.fields rfl
  · exact base.fields rfl

/-- Exit publication clears the park, including when it clears the final saved stack. -/
theorem Configuration.exitFiber (interp : Interp) (machine : NativeMachine) (fiber : Fiber)
    (exit : ExitV) (held : Configuration machine) (active : fiber.parked = .notParked) :
    Configuration (Machine.exitFiber interp machine fiber exit).1 := by
  unfold Machine.exitFiber
  split
  · unfold Machine.exitFiber.exitInterruptChildren
    change Configuration (machine.update _)
    apply held.update
    exact unparked active
  · unfold Machine.exitFiber.exitStore
    dsimp only
    have published : Configuration ((machine.update (fiber.publish exit)).emit [.exited fiber.id exit]) :=
      (held.update _ (unparked rfl)).fields rfl
    split
    · exact published.update _ (unparked rfl)
    · exact published

/-- An owed resume only updates a dispatcher before its later command clears the park. -/
theorem Configuration.drainOwed (machine : NativeMachine) (held : Configuration machine) :
    ∀ owed : List (Owed NCode), Configuration (Machine.drainOwed machine owed).1
  | [] => held
  | first :: rest => by
    simp only [Machine.drainOwed]
    cases first.mode with
    | now => exact Configuration.drainOwed machine held rest
    | scheduled owner priority =>
      apply Configuration.drainOwed
      unfold RunMachine.postTask
      split
      · exact held.fields rfl
      · rename_i fiber found
        let task : Machine.Task EffName EffThunk Val Err Defect FiberId Ann := .resume first.waiter first.token first.code
        exact (held.update {fiber with dispatcher := fiber.dispatcher.enqueue priority task}
          (ParkedShape.fields (held.found found) rfl rfl)).fields rfl

/-- Command authority identifies the addressed unparked fiber through its actual lookup. -/
theorem active_unparked {machine : NativeMachine} {id : FiberId} {fiber : Fiber}
    (authority : Guard.ActiveAt machine id) (found : machine.fiber? id = some fiber) :
    fiber.parked = .notParked := by
  obtain ⟨other, lookup, running, parked⟩ := authority
  have same := Option.some.inj (lookup.symm.trans found)
  cases same
  exact parked

/-- Every command retains parked heads under the existing driver's command authority. -/
theorem Configuration.command (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (command : Command) (rest : List Command) (held : Configuration machine)
    (authority : Guard.CommandAuthority root table machine command) :
    letI := evaluatorFor root table
    Configuration (driveStep (interpOf root table) machine command rest).1 := by
  letI := evaluatorFor root table
  cases command with
  | evaluate id =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      split
      · exact held
      · exact (held.update {fiber with running := true, currentOpCount := 0}
          (ParkedShape.fields (held.found found) rfl rfl)).fields rfl
  | loop id yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have good := iteration root table machine fiber yielding (active_unparked authority found)
      have rows := interferes (Moves.iteration_interferes root table (interpOf root table) machine fiber yielding) held
      exact Configuration.settle id rest _ rows good
  | deliver id yielding =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have good := native root table machine fiber yielding (active_unparked authority found)
      have rows := interferes (Moves.evaluateNative_interferes root table machine fiber yielding) held
      exact Configuration.settle id rest _ rows good
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      split
      · split
        · change Configuration (machine.update _)
          exact held.update _ (unparked rfl)
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
          · intro fiber member
            rcases List.mem_append.mp member with old | fresh
            · exact held fiber old
            · rw [List.mem_singleton.mp fresh]
              exact unparked rfl
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · rename_i race fiber raceFound found
      split
      · rename_i exit exited
        have next := Configuration.fireObserver (interpOf root table) child exit
          (machine.updateRace {race with state := {race.state with live := race.state.live ++ [child]}}, [])
          (.raceCallback raceId) (held.fields rfl)
        generalize Machine.fireObserver (interpOf root table) child exit
          (machine.updateRace {race with state := {race.state with live := race.state.live ++ [child]}}, [])
          (.raceCallback raceId) = pair at next ⊢
        obtain ⟨changed, nested⟩ := pair
        exact next
      · apply Configuration.modify
        · exact held.fields rfl
        · intro fiber good
          exact ParkedShape.fields good rfl rfl
    · exact held
  | registrationDone raceId yielding =>
    obtain ⟨ownedRace, ownedFiber, raceLookup, fiberLookup, running, active, current⟩ := authority
    simp only [driveStep, raceLookup]
    simp only [RunMachine.fiber?] at fiberLookup
    simp only [RunMachine.fiber?, RunMachine.updateRace, fiberLookup]
    split
    · apply Configuration.settle_one
      · exact held.fields rfl
      · exact unparked active
    · apply Configuration.settle_one
      · exact held.fields rfl
      · exact fun _ => park_head root [] table ownedFiber.frame.current (by
          have same : (interpAt root [] table).parkOf ownedFiber.frame.current = some (.ok (.race raceId)) := current
          rw [same]
          intro wrong
          cases wrong)
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have good := interruption (interruptCause (interpOf root table) who extra fiber.id) fiber (held.found found)
      change Held (interruptRecord (interpOf root table) who extra fiber).1 at good
      generalize interruptRecord (interpOf root table) who extra fiber = pair at good ⊢
      obtain ⟨next, immediate⟩ := pair
      exact (held.update next good).fields rfl
  | afterInterrupt host yielding kind =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have active := active_unparked authority found
      apply Configuration.settle_one held
      exact unparked active
  | raceCancel raceId host yielding remaining visited =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · split <;> exact held
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · apply Configuration.modify
        · apply Configuration.modify held
          intro fiber good
          exact ParkedShape.fields good rfl rfl
        · intro fiber good
          exact ParkedShape.fields good rfl rfl
  | observe id exit observer =>
    simp only [driveStep]
    have next := Configuration.fireObserver (interpOf root table) id exit (machine, []) observer held
    generalize Machine.fireObserver (interpOf root table) id exit (machine, []) observer = pair at next ⊢
    obtain ⟨changed, nested⟩ := pair
    exact next
  | exitDone id =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      exact held.update _ (ParkedShape.fields (held.found found) rfl rfl)
  | closeParAwait host yielding fibers =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have active := active_unparked authority found
      apply Configuration.settle_one held
      exact unparked active
  | link mode scope target who extra =>
    simp only [driveStep]
    have next := interferes (Moves.Interferes.linkScope (interpOf root table) machine mode scope target who extra) held
    generalize Machine.linkScope (interpOf root table) machine mode scope target who extra = pair at next ⊢
    obtain ⟨changed, nested⟩ := pair
    exact next
  | finish id exit =>
    simp only [driveStep]
    split
    · exact held
    · rename_i fiber found
      have active := active_unparked authority found
      have next := Configuration.exitFiber (interpOf root table) machine {fiber with running := false} exit held active
      generalize Machine.exitFiber (interpOf root table) machine {fiber with running := false} exit = pair at next ⊢
      obtain ⟨changed, nested⟩ := pair
      exact next
  | drainDue =>
    simp only [driveStep]
    apply Configuration.drainOwed
    exact held.fields rfl
  | wake key phase => exact held.fields rfl

/-- Decisions outside the command loop retain the same parked-head observation. -/
theorem machine_edits (root : NativeEff) (table : RowTable) :
    Lift.MachineEdits (interpOf root table) Configuration where
  drain := by
    intro machine owner fiber held found
    exact (held.update {fiber with dispatcher := fiber.dispatcher.drain.2}
      (ParkedShape.fields (held.found found) rfl rfl)).fields rfl
  ran := fun _ _ _ held => held.fields rfl
  yield := fun _ id _ held => held.modify id _ (fun _ good => ParkedShape.fields good rfl rfl)
  interrupt := by
    intro machine who extra target fiber held found
    have good := interruption (interruptCause (interpOf root table) who extra fiber.id) fiber (held.found found)
    unfold Lift.interruptEdit
    dsimp only
    split
    · exact (held.fields rfl).update _ good
    · exact (held.fields rfl).update _ good
  middleware := fun _ held => held.fields rfl
  clock := fun _ _ held _ => held.fields rfl
  owed := fun machine owed held => Configuration.drainOwed machine held [owed]
  prepare := fun _ _ _ _ held => held.fields rfl

/-- The existing guard lift carries parked heads without adding a new queue assertion. -/
theorem decision_lift (root : NativeEff) (table : RowTable) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ machine => Guard.GuardState machine ∧ Configuration machine)
      (fun _ machine commands => Guard.DriverQueue root table machine commands)
      (fun _ machine tasks => Guard.DriverTasks machine tasks) (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  apply (Guard.state_decision_lift root table).withMachineFact Configuration
  · intro tasks world machine command rest running before held
    exact held.command root table machine command rest ((before.2 running).1.1.authority command (List.mem_cons_self ..))
  · exact machine_edits root table
  · intro world machine id token value before held running admitted
    exact Configuration.command root table _ _ _ (held.fields rfl) trivial

end Effect4.Program.ParkedShape

import Effect4.Laws.Program.AnswerSlots.InitializedQueueTransport
import Effect4.Laws.Program.AnswerSlots.InitializedDriver
import Effect4.Laws.Program.Guard.CommandControlEdits
import Effect4.Laws.Program.NativeSettlementCommands

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: the initialized queue retains its demands through administrative commands.
Consumer: the initialized decision lift and both crew log histories.
The existing guard controls and settlement word supply the actual addressed changes.
The two evaluator cases remain the native producer's obligations.
No progress or host agreement follows.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program
open Guard.NativeStateLinks

/-- A command prefix joins its actual demand to the pending suffix. -/
theorem QueueAt.cons {spec : Spec} {machine : NativeMachine} {command : Guard.NCmd} {rest : List Guard.NCmd}
    (head : CommandDemand spec machine command) (tail : QueueAt spec machine rest) :
    QueueAt spec machine (command :: rest) := by
  intro next member
  rcases List.mem_cons.mp member with same | later
  · subst next; exact head
  · exact tail next later

/-- Observer-produced evaluations and replies have no extra initialized demand. -/
theorem ordinary_observer (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd)
    (ordinary : Guard.CommandControl.Ordinary command) : CommandDemand spec machine command := by
  rcases ordinary with ⟨id, rfl⟩ | ⟨id, token, code, rfl⟩
  all_goals exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩

/-- A continuing administrative result introduces only loop, deliver and evaluate commands. -/
theorem QueueAt.settle_continue (spec : Spec) (machine : NativeMachine) (fiber : Guard.NFiber)
    (yielding : Bool) (rest : List Guard.NCmd) (state : Guard.GuardState machine)
    (held : QueueAt spec machine rest)
    (guard : Guard.GuardQueue spec.root spec.table machine rest)
    (fresh : fiber.id ∉ rest.filterMap (Guard.commandOwner machine)) :
    QueueAt spec (settle fiber.id rest ⟨machine, fiber, yielding, .continue_, [], []⟩).1
      (settle fiber.id rest ⟨machine, fiber, yielding, .continue_, [], []⟩).2 := by
  let next : Moves.NIteration := ⟨machine, fiber, yielding, .continue_, [], []⟩
  have old := QueueAt.settle_rest spec machine fiber.id rest next held guard fresh
    (Guard.NativeState.StateStep.refl state) (Links.refl machine) (Nat.le_refl _) (Nat.le_refl _)
  intro command member
  rcases NativeSettlementCommands.member fiber.id rest next command member with prior | produced
  · exact old command prior
  · rcases produced with nested | ⟨target, rfl⟩ | rfl | rfl | ⟨exit, impossible, equal⟩
    · cases nested
    · exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
    · exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
    · exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
    · cases impossible

/-- Publishing an exit introduces no new source head, finish suffix or child-readiness demand. -/
theorem exit_demand (spec : Spec) (machine : NativeMachine) (fiber : Guard.NFiber) (exit : ExitV) :
    QueueAt spec (exitFiber (interpOf spec.root spec.table) machine fiber exit).1
      (exitFiber (interpOf spec.root spec.table) machine fiber exit).2 := by
  unfold exitFiber
  split
  · intro command member
    rw [List.mem_singleton.mp member]
    exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
  · unfold exitFiber.exitStore
    dsimp only
    split
    · intro command member
      rw [List.mem_singleton.mp member]
      exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
    · intro command member
      rcases List.mem_append.mp member with observer | tail
      · obtain ⟨observer, _, rfl⟩ := List.mem_map.mp observer
        exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
      · rcases List.mem_cons.mp tail with rfl | tail
        · exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
        · rw [List.mem_singleton.mp tail]
          exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩

/-- Administrative commands consume the same actual queue facts as the evaluator cases.
The two supplied producers are the actual native and charged evaluation conclusions. -/
theorem QueueAt.command_of_evaluation (spec : Spec) (raceFree : SourceScope.RaceFreeSource spec.root)
    (machine : NativeMachine) (command : Guard.NCmd) (rest : List Guard.NCmd)
    (source : SourceScope.ConfigurationAt spec.root machine) (state : Guard.GuardState machine)
    (guard : Guard.GuardQueue spec.root spec.table machine (command :: rest))
    (held : QueueAt spec machine (command :: rest))
    (loop : letI := evaluatorFor spec.root spec.table
      ∀ id yielding, command = .loop id yielding →
        QueueAt spec (driveStep (interpOf spec.root spec.table) machine (.loop id yielding) rest).1
          (driveStep (interpOf spec.root spec.table) machine (.loop id yielding) rest).2)
    (deliver : letI := evaluatorFor spec.root spec.table
      ∀ id yielding, command = .deliver id yielding →
        QueueAt spec (driveStep (interpOf spec.root spec.table) machine (.deliver id yielding) rest).1
          (driveStep (interpOf spec.root spec.table) machine (.deliver id yielding) rest).2) :
    letI := evaluatorFor spec.root spec.table
    QueueAt spec (driveStep (interpOf spec.root spec.table) machine command rest).1
      (driveStep (interpOf spec.root spec.table) machine command rest).2 := by
  letI := evaluatorFor spec.root spec.table
  have growth := command_growth spec machine command rest
  have tail := held.tail
  have tailGuard := Guard.guardQueue_tail spec.root spec.table guard
  have transport (after : NativeMachine) (controls : Guard.CommandControlsPreserved machine after)
      (bounds : Bounds machine.state.refs.length machine.state.deferreds.cells.length after.state) :
      QueueAt spec after rest :=
    QueueAt.transport spec machine after rest tail tailGuard controls bounds.1 bounds.2
  have same (after : NativeMachine) (fibers : after.fibers = machine.fibers)
      (bounds : Bounds machine.state.refs.length machine.state.deferreds.cells.length after.state) :
      QueueAt spec after rest := transport after (Guard.CommandControl.same fibers) bounds
  have fresh (id : FiberId) (owner : Guard.commandOwner machine command = some id) :
      id ∉ rest.filterMap (Guard.commandOwner machine) := by
    have distinct := guard.owners
    rw [List.filterMap_cons, owner] at distinct
    exact (List.nodup_cons.mp distinct).1
  have noRace (id : Nat) : machine.race? id = none := by
    unfold RunMachine.race?
    rw [SourceScope.Opportunities.races_nil spec.root machine raceFree source]
    rfl
  cases command with
  | loop id yielding => exact loop id yielding rfl
  | deliver id yielding => exact deliver id yielding rfl
  | evaluate id =>
    simp only [driveStep] at growth ⊢
    split
    · exact tail
    · rename_i fiber found
      split
      · exact tail
      · apply QueueAt.cons
        · exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
        · apply transport
          · apply Guard.NativeStateLinks.controls_of_full
            · exact Guard.controlsPreserved_setRunning
                (by simpa only [Guard.fiber_id_of_lookup found] using found) 0
            · exact Guard.NativeStateLinks.emptyStacks_update (m := machine) (f := fiber)
                (by simpa only [Guard.fiber_id_of_lookup found] using found) _ rfl (fun h => h)
          · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | resume id token answer =>
    simp only [driveStep] at growth ⊢
    split
    · exact tail
    · rename_i fiber found
      split
      · rename_i offered parked
        split
        · apply QueueAt.cons
          · exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
          · apply transport
            · let next : Guard.NFiber := { fiber with
                  parked := .notParked
                  pending := fiber.pending.filter (fun p => p.token ≠ token)
                  frame := { fiber.frame with current := answer } }
              apply Guard.CommandControl.trans (middle := machine.update next)
              · exact Guard.commandControls_update_inactive (m := machine) (f := fiber)
                  (by simpa only [Guard.fiber_id_of_lookup found] using found) next rfl
                  (state.parkedIdle fiber (RunMachine.mem_of_fiber? found)
                    (by rw [parked]; intro impossible; cases impossible)) rfl
              · exact Guard.CommandControl.same rfl
            · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
        · exact tail
      · exact tail
  | launch id => simpa only [driveStep, noRace id] using tail
  | enrollRace id child => simpa only [driveStep, noRace id] using tail
  | registrationDone id yielding => simpa only [driveStep, noRace id] using tail
  | interruptTarget target who extra =>
    simp only [driveStep] at growth ⊢
    split
    · exact tail
    · rename_i fiber found
      have found' : machine.fiber? fiber.id = some fiber := by
        simpa only [Guard.fiber_id_of_lookup found] using found
      have controls := Guard.commandControls_interruptRecord spec.root spec.table found' who extra
      have kept := transport _ controls ⟨Nat.le_refl _, Nat.le_refl _⟩
      split
      · exact QueueAt.cons ⟨(by intro host impossible; cases impossible), trivial, trivial⟩ kept
      · exact kept
  | afterInterrupt host yielding kind =>
    simp only [driveStep]
    split
    · exact tail
    · rename_i fiber found
      apply QueueAt.settle_continue spec machine _ yielding rest state tail tailGuard
      simpa only [Guard.fiber_id_of_lookup found] using fresh host rfl
  | closeParAwait host yielding fibers =>
    simp only [driveStep]
    split
    · exact tail
    · rename_i fiber found
      apply QueueAt.settle_continue spec machine _ yielding rest state tail tailGuard
      simpa only [Guard.fiber_id_of_lookup found] using fresh host rfl
  | raceCancel race host yielding remaining visited =>
    have demand := held (.raceCancel race host yielding remaining visited) (List.mem_cons_self ..)
    have next : CommandDemand spec machine (.afterInterrupt host yielding (.awaitAll visited)) := by
      refine ⟨?_, trivial, trivial⟩
      intro target isLocal fiber found
      exact demand.1 target isLocal fiber found
    cases remaining <;> simpa only [driveStep, noRace race] using QueueAt.cons next tail
  | trackChild parent child =>
    simp only [driveStep] at growth ⊢
    split
    · exact tail
    · split
      · exact tail
      · apply transport
        · exact Guard.CommandControl.trans
            (Links.modifyFields machine parent (fun parent => { parent with children := parent.children ++ [child] }) (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => rfl)
              (fun _ => rfl) (fun _ h => h) (fun _ h => h)).controls
            (Links.observer _ child (.untrackChild parent)).controls
        · simp only [StatePreservation.modify_state]
          exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | observe id exit observer =>
    have actual := Guard.CommandControl.observer spec.root spec.table id exit (machine, []) observer
    apply QueueAt.append
    · intro command member
      rcases actual.2 command member with impossible | ordinary
      · cases impossible
      · exact ordinary_observer spec _ command ordinary
    · exact transport _ actual.1 growth
  | exitDone id =>
    simp only [driveStep] at growth ⊢
    split
    · exact tail
    · rename_i fiber found
      apply transport
      · apply Guard.NativeStateLinks.controls_of_full
        · exact Guard.controlsPreserved_cleared spec.root spec.table
            (by simpa only [Guard.fiber_id_of_lookup found] using found)
        · exact Guard.NativeStateLinks.emptyStacks_update (m := machine) (f := fiber)
            (by simpa only [Guard.fiber_id_of_lookup found] using found) _ rfl (fun _ => rfl)
      · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | link mode scope target who extra =>
    apply QueueAt.append
    · intro command member
      obtain ⟨id, rfl⟩ := (RunMachine.applyFiberEdits_shape
        (linkScopeEdits (interpOf spec.root spec.table) machine mode scope target who extra).2
        (linkScopeEdits (interpOf spec.root spec.table) machine mode scope target who extra).1).2 command member
      exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
    · exact transport _ (Links.linkScope spec.root spec.table [] machine mode scope target who extra).controls growth
  | finish id exit =>
    simp only [driveStep] at growth ⊢
    split
    · exact tail
    · rename_i fiber found
      simp only [found] at growth
      apply QueueAt.append (exit_demand spec machine {fiber with running := false} exit)
      apply QueueAt.transport_away spec machine _ rest fiber.id tail tailGuard
      · simpa only [Guard.fiber_id_of_lookup found] using fresh id rfl
      · exact Guard.FinishQueue.controlsAway_exitFiber spec.root spec.table machine fiber exit
      · exact growth.1
      · exact growth.2
  | drainDue =>
    simp only [driveStep] at growth ⊢
    apply QueueAt.append
    · intro command member
      obtain ⟨owed, present, rfl⟩ := Guard.drainOwed_commands _ _ command member
      exact ⟨(by intro host impossible; cases impossible), trivial, trivial⟩
    · apply transport _ _ growth
      apply Guard.CommandControl.trans (middle := { machine with state := ((interpOf spec.root spec.table).dueResumes machine.state).2 })
      · exact Guard.CommandControl.same rfl
      · exact Guard.CommandControl.drain _ _
  | wake key phase => exact same _ rfl growth

end Effect4.Program.AnswerSlots.Initialized

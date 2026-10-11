import Effect4.Laws.Program.ReleaseCustody.CommandStacks
import Effect4.Laws.Program.Guard.Observer

/-!
Concept: scope-lifetime-finalization R11, serving `ReleaseCustody.Execution.history`.
Consumers: native command custody and queue-tail preservation.
Administrative commands retain every old saved stack; exit clearing changes an inactive owner only.
These facts inspect actual machine records and do not assert history closure or progress.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Effect4.Program.ReleaseCustody.CommandStacks
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

theorem StackLinks.emit {m n : NativeMachine} (links : StackLinks m n) (events) :
    StackLinks m (n.emit events) := links.trans (.of_fibers rfl)

theorem StackLinks.update_from {m n : NativeMachine} (links : StackLinks m n)
    (old next : NFiber) (found : m.fiber? old.id = some old)
    (key : next.id = old.id) (stack : next.frame.stack = old.frame.stack) :
    StackLinks m (n.update next) := by
  obtain ⟨middle, seen, same⟩ := links old.id old found
  apply links.trans
  apply update_links n middle next
  · rw [key]
    exact seen
  · exact stack.trans same.symm

/-- Recording any finite list of interrupts preserves every saved continuation. -/
theorem interruptEach_links (root : NativeEff) (table : RowTable) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId)
    (m : NativeMachine) (commands : List NCmd) :
    StackLinks m (interruptEach (interpOf root table) who extra targets (m, commands)).1 := by
  induction targets generalizing m commands with
  | nil => exact .refl m
  | cons target targets ih =>
    cases found : m.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, found] using ih m commands
    | some fiber =>
      have first := (interrupt_links root table m fiber
        (by simpa only [fiber_id_of_lookup found] using found) (some who) extra).emit
          [RunEvent.interruptRecorded (some who) target]
      simpa only [interruptEach, List.foldl_cons, found] using
        first.trans (ih _ _)

/-- Scope linking edits observers or records an interrupt, retaining every saved stack. -/
theorem linkScope_links (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    StackLinks m (linkScope (interpOf root table) m mode scope target who extra).1 := by
  unfold Effect4.Machine.linkScope
  cases statusEq : (interpOf root table).scopeStatus scope m.state with
  | none => exact .of_fibers rfl
  | some status =>
    cases status with
    | some exit =>
      simp only []
      cases found : m.fiber? target with
      | none => exact .of_fibers rfl
      | some fiber =>
        exact (interrupt_links root table m fiber
          (by simpa only [fiber_id_of_lookup found] using found) who extra).emit _
    | none =>
      simp only []
      cases found : m.fiber? target with
      | none => exact .of_fibers rfl
      | some fiber =>
        simp only []
        split
        · exact .refl m
        · cases linked : (interpOf root table).scopeLinkFiber mode scope target m.state with
          | none => exact .of_fibers rfl
          | some result =>
            obtain ⟨stores, key⟩ := result
            exact (StackLinks.of_fibers (m := m) (n := {m with state := stores}) rfl |>.trans
              (modify_links _ target (fun f =>
                {f with observers := f.observers ++ [.dropScopeFinalizer scope key]})
                (fun _ => rfl) (fun _ => rfl))).emit _

/-- Posting an owed resume changes its dispatcher's task list, never a saved stack. -/
theorem postTask_links (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : NTask) : StackLinks m (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact .of_fibers rfl
  · rename_i fiber found
    exact (update_links m fiber {fiber with dispatcher := fiber.dispatcher.enqueue priority task}
      (by simpa only [fiber_id_of_lookup found] using found) rfl).trans (.of_fibers rfl)

/-- Draining stored resumes retains every saved stack until those resumes run. -/
theorem drainOwed_links (m : NativeMachine) (due : List (Owed NCode)) :
    StackLinks m (drainOwed m due).1 := by
  induction due generalizing m with
  | nil => exact .refl m
  | cons owed rest ih =>
    cases mode : owed.mode with
    | now => simpa only [drainOwed, mode] using ih m
    | scheduled owner priority =>
      simpa only [drainOwed, mode] using
        (postTask_links m owner priority (.resume owed.waiter owed.token owed.code)).trans (ih _)

/-- A countdown observer retains the waiter's saved stack even after nested interrupts. -/
theorem countdownObserver_links (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (commands : List NCmd) (waiter : FiberId) (token : Nat) :
    StackLinks m (fireObserver (interpOf root table) id exit (m, commands) (.countdown waiter token)).1 := by
  let base := m.emit [RunEvent.observerFired id (.countdown waiter token)]
  have emitted : StackLinks m base := .of_fibers rfl
  simp only [fireObserver, show m.emit _ = base from rfl]
  cases found : base.fiber? waiter with
  | none => exact emitted
  | some fiber =>
    simp only []
    cases pending : fiber.pending.find? (fun p => p.token = token) with
    | none => exact emitted
    | some park =>
      simp only []
      let collected := park.collected ++ [exit]
      let firstFailure := park.failFast && !exit.isSuccess && park.collected.all Exit.isSuccess
      generalize result : (if firstFailure then
          interruptEach (interpOf root table) waiter ((interpOf root table).stackAnnotations waiter)
            park.remaining (base, []) else (base, [])) = out
      have middle : StackLinks base out.1 := by
        rw [← result]
        split
        · exact interruptEach_links root table waiter _ park.remaining base []
        · exact .refl base
      have original : base.fiber? fiber.id = some fiber := by
        simpa only [fiber_id_of_lookup found] using found
      obtain ⟨outMachine, nested⟩ := out
      dsimp only at middle ⊢
      cases walked : countdownWalk outMachine park.remaining collected with
      | mk exits next =>
        cases next with
        | none =>
          exact emitted.trans (middle.update_from fiber
            {fiber with pending := fiber.pending.map (fun p => if p.token = token then
              {p with waitingOn := none, remaining := [], collected := exits} else p)}
            original rfl rfl)
        | some pair =>
          obtain ⟨next, rest⟩ := pair
          have observed := middle.trans (modify_links outMachine next (fun f =>
            {f with observers := f.observers ++ [.countdown waiter token]}) (fun _ => rfl) (fun _ => rfl))
          exact emitted.trans (observed.update_from fiber
            {fiber with pending := fiber.pending.map (fun p => if p.token = token then
              {p with waitingOn := some next, remaining := rest, collected := exits} else p)}
            original rfl rfl)

/-- Every observer is administrative with respect to saved continuations. -/
theorem fireObserver_links (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (commands : List NCmd) (observer : Observer) :
    StackLinks m (fireObserver (interpOf root table) id exit (m, commands) observer).1 := by
  cases observer with
  | countdown waiter token => exact countdownObserver_links root table m id exit commands waiter token
  | resumeAwait waiter token mode => exact .of_fibers rfl
  | callback key => exact .of_fibers rfl
  | untrackChild parent =>
    exact (StackLinks.of_fibers (m := m) (n := m.emit _) rfl).trans
      (modify_links _ parent (fun f => {f with children := f.children.filter (fun child => child ≠ id)})
        (fun _ => rfl) (fun _ => rfl))
  | dropScopeFinalizer scope key =>
    simp only [fireObserver]
    split <;> exact .of_fibers rfl
  | raceCallback raceId =>
    simp only [fireObserver]
    split
    · exact .of_fibers rfl
    · split <;> exact .of_fibers rfl

/-- Commands without an active owner preserve all stacks, except explicit exit clearing. -/
theorem unowned_command_links (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : NCmd) (rest : List NCmd) (unowned : commandOwner m command = none)
    (notExit : ∀ id, command ≠ .exitDone id) :
    letI := evaluatorFor root table
    StackLinks m (driveStep (interpOf root table) m command rest).1 := by
  letI := evaluatorFor root table
  cases command with
  | loop id yielding => cases unowned
  | deliver id yielding => cases unowned
  | finish id exit => cases unowned
  | afterInterrupt id yielding kind => cases unowned
  | raceCancel race id yielding remaining visited => cases unowned
  | closeParAwait id yielding fibers => cases unowned
  | exitDone id => exact False.elim (notExit id rfl)
  | evaluate id =>
    simp only [driveStep]
    split
    · exact .refl m
    · rename_i fiber found
      split
      · exact .refl m
      · exact (update_links m fiber {fiber with running := true, currentOpCount := 0}
          (by simpa only [fiber_id_of_lookup found] using found) rfl).emit _
  | resume id token answer =>
    simp only [driveStep]
    split
    · exact .refl m
    · rename_i fiber found
      split
      · split
        · exact (update_links m fiber
            {fiber with
              parked := .notParked
              pending := fiber.pending.filter (fun p => p.token ≠ token)
              frame := {fiber.frame with current := answer}}
            (by simpa only [fiber_id_of_lookup found] using found) rfl).emit _
        · exact .refl m
      · exact .refl m
  | registrationDone race yielding =>
    cases found : m.race? race with
    | none => simp only [driveStep, found]; exact .refl m
    | some entry =>
      change (m.race? race).map Race.host = none at unowned
      rw [found] at unowned
      cases unowned
  | launch race =>
    simp only [driveStep]
    split
    · exact .refl m
    · rename_i entry found
      split
      · exact .refl m
      · rename_i code more programs
        split
        · exact .refl m
        · split
          · exact .refl m
          · rename_i host lookup
            exact (append_links m (spawnedChild root table m host code
              ⟨true, true, .interruptible⟩ (entry.nextSite.getD []))).trans (.of_fibers rfl)
  | enrollRace race child =>
    simp only [driveStep]
    split
    · rename_i entry fiber raceFound fiberFound
      split
      · exact (StackLinks.of_fibers (m := m) (n := m.updateRace
          {entry with state := {entry.state with live := entry.state.live ++ [child]}}) rfl).trans
          (fireObserver_links root table _ child _ [] (.raceCallback race))
      · exact (StackLinks.of_fibers (m := m) (n := m.updateRace
          {entry with state := {entry.state with live := entry.state.live ++ [child]}}) rfl).trans
          (modify_links _ child (fun f => {f with observers := f.observers ++ [.raceCallback race]})
            (fun _ => rfl) (fun _ => rfl))
    · exact .refl m
  | interruptTarget id who extra =>
    simp only [driveStep]
    split
    · exact .refl m
    · rename_i fiber found
      exact (interrupt_links root table m fiber
        (by simpa only [fiber_id_of_lookup found] using found) who extra).emit _
  | trackChild parent child =>
    simp only [driveStep]
    split
    · exact .refl m
    · split
      · exact .refl m
      · exact (modify_links m parent (fun f => {f with children := f.children ++ [child]})
          (fun _ => rfl) (fun _ => rfl)).trans
          (modify_links _ child (fun f => {f with observers := f.observers ++ [.untrackChild parent]})
            (fun _ => rfl) (fun _ => rfl))
  | observe id exit observer => exact fireObserver_links root table m id exit [] observer
  | link mode scope target who extra => exact linkScope_links root table m mode scope target who extra
  | drainDue =>
    exact (StackLinks.of_fibers (m := m) (n := {m with state := ((interpOf root table).dueResumes m.state).2}) rfl).trans
      (drainOwed_links _ ((interpOf root table).dueResumes m.state).1)
  | wake list phase => exact .of_fibers rfl

/-- An exited fiber cannot own an outstanding active command. -/
theorem exited_not_owner (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (state : GuardState m) (commands : List NCmd) (queue : GuardQueue root table m commands)
    (fiber : NFiber) (found : m.fiber? fiber.id = some fiber) (exited : fiber.exit.isSome = true)
    (command : NCmd) (member : command ∈ commands) (target : FiberId)
    (owns : commandOwner m command = some target) : target ≠ fiber.id := by
  intro same
  subst target
  obtain ⟨old, seen, running, _⟩ := commandAuthority_owner_active root table m command fiber.id
    (queue.authority command member) owns
  have equal : old = fiber := Option.some.inj (seen.symm.trans found)
  subst old
  have idle := (state.exited fiber (List.mem_of_find?_eq_some found) exited).2
  rw [idle] at running
  cases running

/-- Clearing an exited fiber leaves every queued owner's saved stack intact. -/
theorem queue_cleared (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (state : GuardState m) (commands : List NCmd) (queue : GuardQueue root table m commands)
    (held : QueueStable m commands) (fiber : NFiber) (found : m.fiber? fiber.id = some fiber)
    (exited : fiber.exit.isSome = true) :
    QueueStable (m.update (fiber.cleared (interpOf root table))) commands := by
  intro command member target owns next seen
  have races : RaceHostsPreserved m (m.update (fiber.cleared (interpOf root table))) :=
    fun _ race present => ⟨race, present, rfl⟩
  rw [commandOwner_transport root table races command (queue.authority command member)] at owns
  obtain ⟨old, oldSeen, _, _⟩ := commandAuthority_owner_active root table m command target
    (queue.authority command member) owns
  obtain ⟨same, present, stack⟩ := update_away m (fiber.cleared (interpOf root table)) target old
    (exited_not_owner root table m state commands queue fiber found exited command member target owns) oldSeen
  have equal : same = next := Option.some.inj (present.symm.trans seen)
  subst next
  rw [stack]
  exact held command member target owns old oldSeen

end Effect4.Program.ReleaseCustody.CommandStacks

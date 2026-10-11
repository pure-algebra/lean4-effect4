import Effect4.Laws.Program.ReleaseCustody.CommandDebit

/-!
Concept: scope-lifetime-finalization R11, serving `ReleaseCustody.Execution.history`.
Consumers: race command clauses of the admitted release-custody invariant.
Launching transfers pending program credit into the actual child; race metadata carries no credit.
These local bounds establish no whole-history closure, source uniqueness or progress.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Effect4.Program.ReleaseCustody.CommandDebit
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Control Effect4.Program.ReleaseCustody.Sequencing

/-- A distinct race replacement changes only the selected unlaunched program credit. -/
theorem update_race_credits (q : List Nat) (m : NativeMachine) (old next : NRace)
    (unique : (m.races.map Race.id).Nodup) (found : m.race? old.id = some old)
    (key : next.id = old.id) :
    machineCredits q (m.updateRace next) + (old.programs.map (currentCredits q)).sum =
      machineCredits q m + (next.programs.map (currentCredits q)).sum := by
  have changed := ControlWeights.replace_sum Race.id
    (fun race : NRace => (race.programs.map (currentCredits q)).sum)
    old next key m.races unique (List.mem_of_find?_eq_some found)
  simpa only [machineCredits, RunMachine.updateRace, Nat.add_assoc] using
    congrArg (fun n => (m.state.scopes.entries.map fun e => scopeCredits q e.scope).sum +
      (m.fibers.map (fiberCredits q)).sum + n) changed

/-- Race metadata edits retain funding when their unlaunched programs remain unchanged. -/
theorem update_race (q : List Nat) (m : NativeMachine) (old next : NRace)
    (commands : List Command) (held : Funded q m commands)
    (unique : (m.races.map Race.id).Nodup) (found : m.race? old.id = some old)
    (key : next.id = old.id) (programs : next.programs = old.programs) :
    Funded q (m.updateRace next) commands := by
  have changed := update_race_credits q m old next unique found key
  rw [programs] at changed
  have equal := Nat.add_right_cancel changed
  unfold Funded at held ⊢
  change m.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (m.updateRace next) +
    (commands.map (commandCredits q)).sum ≤ m.trace.countP (ReleaseTrace.registeredAt q)
  rw [equal]
  exact held

/-- Replacing a race by an equal identity retains the list of race identities. -/
theorem update_race_ids (m : NativeMachine) (next : NRace) :
    (m.updateRace next).races.map Race.id = m.races.map Race.id := by
  simp only [RunMachine.updateRace, List.map_map]
  apply List.map_congr_left
  intro race _
  dsimp only [Function.comp_def]
  split
  · rename_i equal
    exact equal.symm
  · rfl

/-- A new child owns exactly its initial program credit. -/
theorem spawn_credits (root : NativeEff) (table : RowTable) (q : List Nat)
    (m : NativeMachine) (host : Fiber) (code : NCode) (options : Supervision.ForkOptions)
    (site : List Nat) :
    machineCredits q (spawn (interpOf root table) m host code options site).1 =
      machineCredits q m + currentCredits q code := by
  rw [spawn_machine (site := site), emit_credits]
  simp only [machineCredits, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, spawnedChild, fiberCredits,
    RunFiber.make, FrameFiber.start, stackCredits, Dispatcher.empty, Nat.add_zero]
  omega

/-- The native race-settle program contains no foreign release credit. -/
theorem race_settle_zero (root : NativeEff) (table : RowTable) (q : List Nat)
    (race : Nat) (cleanup : Bool) (exit : ExitV) :
    currentCredits q ((interpOf root table).raceSettle race cleanup exit) = 0 := by
  change currentCredits q (embed (raceSettleProgram race cleanup exit)) = 0
  unfold raceSettleProgram
  split
  · rfl
  · cases exit <;> rfl

/-- Launching removes precisely the credit transferred into the actual entrant. -/
theorem launch (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (raceId : Nat) (rest : List Command) (unique : (m.races.map Race.id).Nodup)
    (held : Funded q m (.launch raceId :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.launch raceId) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  cases found : m.race? raceId with
  | none => simpa only [driveStep, found] using tail q m _ rest held
  | some race =>
    cases programs : race.programs with
    | nil => simpa only [driveStep, found, programs] using tail q m _ rest held
    | cons code more =>
      simp only [driveStep, found, programs]
      split
      · exact tail q m _ rest held
      · cases lookup : m.fiber? race.host with
        | none => exact tail q m _ rest held
        | some host =>
          let born := launchEntrant (interpOf root table) raceId m host code (race.nextSite.getD [])
          let next : NRace := {race with programs := more, nextSite := race.nextSite.map (fun site => site ++ [1])}
          apply emit q _ _ _ _ rfl rfl
          have raceFound : born.1.race? race.id = some race := by
            change m.race? race.id = some race
            simpa only [race_id_of_lookup found] using found
          have changed := update_race_credits q born.1 race next unique raceFound rfl
          have added := spawn_credits root table q m host code
            ⟨true, true, .interruptible⟩ (race.nextSite.getD [])
          change machineCredits q born.1 = machineCredits q m + currentCredits q code at added
          rw [programs, show next.programs = more from rfl, List.map_cons, List.sum_cons] at changed
          have equal : machineCredits q (born.1.updateRace next) = machineCredits q m := by omega
          unfold Funded at held ⊢
          rw [equal]
          have trace : (born.1.updateRace next).trace = m.trace ++
              [RunEvent.forked host.id ⟨m.nextId⟩ true] := by
            change (spawn (interpOf root table) m host code ⟨true, true, .interruptible⟩ _).1.trace = _
            rw [spawn_machine (site := race.nextSite.getD []), RunMachine.emit_trace]
          rw [trace, List.countP_append, List.countP_append]
          simpa only [List.map_cons, List.sum_cons, commandCredits, List.countP_cons,
            List.countP_nil, ReleaseTrace.releaseAt, ReleaseTrace.registeredAt, Nat.add_zero,
            Nat.zero_add, Bool.false_eq_true, if_false] using held

/-- Race registration either installs its zero-credit settle program or parks its host. -/
theorem registration_done (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (raceId : Nat) (yielding : Bool) (rest : List Command)
    (fibers : (m.fibers.map RunFiber.id).Nodup) (races : (m.races.map Race.id).Nodup)
    (noAdd : ∀ race, m.race? raceId = some race → ∀ fiber,
      m.fiber? race.host = some fiber → NoAdd fiber.frame.stack)
    (held : Funded q m (.registrationDone raceId yielding :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.registrationDone raceId yielding) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  cases found : m.race? raceId with
  | none => simpa only [driveStep, found] using tail q m _ rest held
  | some race =>
    let base := m.updateRace {race with registering := false}
    have baseFunded : Funded q base rest := update_race q m race _ rest
      (tail q m _ rest held) races (by simpa only [race_id_of_lookup found] using found) rfl rfl
    simp only [driveStep, found]
    cases lookup : m.fiber? race.host with
    | none =>
      have baseLookup : base.fiber? race.host = none := lookup
      simp only [show (m.updateRace {race with registering := false}).fiber? race.host =
        base.fiber? race.host from rfl, baseLookup]
      exact baseFunded
    | some fiber =>
      have baseLookup : base.fiber? race.host = some fiber := lookup
      simp only [show (m.updateRace {race with registering := false}).fiber? race.host =
        base.fiber? race.host from rfl, baseLookup]
      have own : base.fiber? fiber.id = some fiber := by
        simpa only [fiber_id_of_lookup lookup] using baseLookup
      have stack := noAdd race found fiber lookup
      cases accepted : race.state.accepted with
      | some exit =>
        simp only [settle, List.nil_append, List.cons_append]
        apply update q base fiber
          {fiber with frame := {fiber.frame with current := (interpOf root table).raceSettle raceId race.state.cleanupNeeded exit}}
          rest _ baseFunded fibers own rfl
        simpa only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add] using
          Nat.add_le_add_right (replace_code q fiber _ stack (race_settle_zero root table q _ _ _))
            ((rest.map (commandCredits q)).sum)
      | none =>
        simp only [settle, FiberCore.deferredInterrupt, RunFiber.park, List.nil_append,
          List.cons_append]
        by_cases deferred : fiber.frame.deferredInterrupt = true
        all_goals
          simp only [deferred, if_true]
          refine update q (base.emit [RunEvent.parkedOn fiber.id race.token]) fiber _ rest _
            (emit q base rest baseFunded [RunEvent.parkedOn fiber.id race.token] rfl rfl) fibers own ?_ ?_
          · rfl
          · simp only [fiberCredits, FiberCore.pushAsyncFinalizer, stackCredits,
              futureCredits, Nat.zero_add, List.map_cons, List.sum_cons, commandCredits,
              noAdd_full q fiber.frame.current _ stack]
            exact Nat.le_refl _

/-- Race observers buffer or deliver exits without manufacturing foreign release credit. -/
theorem race_observer (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (raceId : Nat) (commands rest : List Command)
    (unique : (m.races.map Race.id).Nodup) (held : Funded q m (commands ++ rest)) :
    let out := fireObserver (interpOf root table) id exit (m, commands) (.raceCallback raceId)
    Funded q out.1 (out.2 ++ rest) := by
  let base := m.emit [RunEvent.observerFired id (.raceCallback raceId)]
  have before : Funded q base (commands ++ rest) := emit q m _ held _ rfl rfl
  cases found : base.race? raceId with
  | none => simpa only [fireObserver, show m.emit _ = base from rfl, found] using before
  | some race =>
    have own : base.race? race.id = some race := by simpa only [race_id_of_lookup found] using found
    let next : NRace := race.afterExit id exit
    have updated : Funded q (base.updateRace next) (commands ++ rest) :=
      update_race q base race next _ before unique own rfl rfl
    have nextFound : (base.updateRace next).race? next.id = some next := by
      simp only [race_lookup_updateRace, show next.id = race.id from rfl, own,
        Option.map_some, if_true]
    have nextUnique : ((base.updateRace next).races.map Race.id).Nodup := by
      rw [update_race_ids]
      exact unique
    simp only [fireObserver, show m.emit _ = base from rfl, found]
    split
    · rename_i accepted _ _
      have settled := emit q _ _
        (update_race q (base.updateRace next) next {next with settled := true}
          _ updated nextUnique nextFound rfl rfl) [RunEvent.raceSettled raceId accepted] rfl rfl
      apply queue q _ (commands ++ rest) _ settled
      by_cases registering : race.registering = true
      · simp only [registering, if_true, List.append_nil]
        exact Nat.le_refl _
      · simp only [registering, Bool.false_eq_true, if_false, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, commandCredits, race_settle_zero,
          Nat.add_zero]
        exact Nat.le_refl _
    · exact updated

/-- Enrolling an entrant edits only race metadata and its exit observer. -/
theorem enroll (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (raceId : Nat) (child : FiberId) (rest : List Command)
    (fibers : (m.fibers.map RunFiber.id).Nodup) (races : (m.races.map Race.id).Nodup)
    (held : Funded q m (.enrollRace raceId child :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.enrollRace raceId child) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · rename_i race fiber found lookup
    let next : NRace := {race with state := {race.state with live := race.state.live ++ [child]}}
    have before := update_race q m race next rest (tail q m _ rest held) races
      (by simpa only [race_id_of_lookup found] using found) rfl rfl
    cases exited : fiber.exit with
    | some exit =>
      exact race_observer root table q (m.updateRace next) child exit raceId [] rest
        (by rw [update_race_ids]; exact races) before
    | none =>
      exact modify q (m.updateRace next) child
        (fun f => {f with observers := f.observers ++ [.raceCallback raceId]}) rest before fibers
        (fun _ => rfl) (fun _ => Nat.le_refl _)
  · exact tail q m _ rest held

end Effect4.Program.ReleaseCustody.CommandDebit

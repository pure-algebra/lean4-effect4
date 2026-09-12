import Effect4.Laws.Program.Guard.RegistrationQueue
import Effect4.Laws.Program.Guard.Finish
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.FinishQueue
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard Effect4.Program.Guard.Finish
open Effect4.Program.Guard.RegistrationQueue

theorem controlsAway_trans {m n o : NativeMachine} {target : FiberId}
    (first : ControlsAway m n target) (second : ControlsAway n o target) :
    ControlsAway m o target := by
  intro fiber f lookup other eligible
  obtain ⟨g, hg, current, parked, exited, running⟩ := first fiber f lookup other eligible
  have eligible' : g.parked = .notParked ∨ g.exit.isSome = true := by
    rcases eligible with hp | he
    · exact Or.inl (parked.trans hp)
    · exact Or.inr (exited ▸ he)
  obtain ⟨h, hh, current', parked', exited', running'⟩ := second fiber g hg other eligible'
  exact ⟨h, hh, current'.trans current, parked'.trans parked, exited'.trans exited,
    fun hr => running' (running hr)⟩

theorem controlsAway_exitFiber (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) :
    ControlsAway m (exitFiber (interpOf p table) m { f with running := false } exit).1 f.id := by
  unfold exitFiber
  split
  · exact controlsAway_update m (childExitFiber p table f exit)
  · cases ho : f.observers with
    | nil =>
      have first : ControlsAway m ((m.update (f.publish exit)).emit [RunEvent.exited f.id exit]) f.id :=
        controlsAway_update m (f.publish exit)
      have second := controlsAway_update ((m.update (f.publish exit)).emit [RunEvent.exited f.id exit])
        ((f.publish exit).cleared (interpOf p table))
      simpa only [exitFiber.exitStore, RunFiber.publish, ho] using controlsAway_trans first second
    | cons o os =>
      simpa only [exitFiber.exitStore, RunFiber.publish, ho, ControlsAway, RunMachine.emit,
        RunMachine.fiber?] using controlsAway_update m (f.publish exit)

theorem races_exitFiber (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) :
    (exitFiber (interpOf p table) m f exit).1.races = m.races := by
  unfold exitFiber
  split
  · rfl
  · cases ho : f.observers <;> simp only [exitFiber.exitStore, RunFiber.publish, ho] <;> rfl

theorem raceHostsPreserved_exitFiber (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) :
    RaceHostsPreserved m (exitFiber (interpOf p table) m f exit).1 := by
  intro raceId race hr
  refine ⟨race, ?_, rfl⟩
  simpa only [RunMachine.race?, races_exitFiber] using hr

theorem guardQueue_exitFiber_rest (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (fresh : f.id ∉ rest.filterMap (commandOwner m)) :
    GuardQueue p table (exitFiber (interpOf p table) m { f with running := false } exit).1 rest := by
  apply guardQueue_transport_away p table state ⟨f, lookup, running, park⟩ queue registration fresh
    (controlsAway_exitFiber p table m f exit)
    (raceHostsPreserved_exitFiber p table m { f with running := false } exit)
  · rw [nextToken_exitFiber]; exact Nat.le_refl _
  · intro fiber token request hr
    rw [requestOf_exitFiber p table lookup park exit] at hr
    exact hr

theorem guardQueue_cons_observe (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {rest : List NCmd} (fiber : FiberId) (exit : ExitV) (observer : Observer)
    (queue : GuardQueue p table m rest) (reserved : ReservedKeys m (observerKeys observer)) :
    GuardQueue p table m (.observe fiber exit observer :: rest) := by
  refine ⟨?_, queue.owners, reservedKeys_append reserved queue.keys, ?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | h
    · trivial
    · exact queue.authority c h
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | h
    · rfl
    · exact queue.codeSites c h

theorem guardQueue_observe_list (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {rest : List NCmd} (fiber : FiberId) (exit : ExitV) (observers : List Observer)
    (queue : GuardQueue p table m rest) (reserved : ReservedKeys m (observers.flatMap observerKeys)) :
    GuardQueue p table m (observers.map (.observe fiber exit) ++ rest) := by
  induction observers with
  | nil => exact queue
  | cons observer tail ih =>
    have headKeys : ReservedKeys m (observerKeys observer) :=
      reservedKeys_subset reserved (List.subset_append_left ..)
    have tailKeys : ReservedKeys m (tail.flatMap observerKeys) :=
      reservedKeys_subset reserved (List.subset_append_right ..)
    exact guardQueue_cons_observe p table fiber exit observer (ih tailKeys) headKeys

theorem guardQueue_exitDone_drainDue (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (lookup : m.fiber? f.id = some f)
    (exited : f.exit.isSome = true) : GuardQueue p table m [.exitDone f.id, .drainDue] := by
  refine ⟨?_, List.nodup_nil, reservedKeys_nil m, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨f, lookup, exited⟩
    · trivial
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl

theorem observeList_noOwners (m : NativeMachine) (fiber : FiberId) (exit : ExitV)
    (observers : List Observer) :
    (observers.map (.observe fiber exit)).filterMap (commandOwner m) = [] := by
  induction observers with
  | nil => rfl
  | cons o os ih => simpa only [List.map_cons, List.filterMap_cons, commandOwner] using ih

theorem exitFiber_noOwners (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) :
    let result := exitFiber (interpOf p table) m f exit
    result.2.filterMap (commandOwner result.1) = [] := by
  unfold exitFiber
  split
  · rfl
  · cases ho : f.observers with
    | nil => simp only [exitFiber.exitStore, RunFiber.publish, ho]; rfl
    | cons o os =>
      simp only [exitFiber.exitStore, RunFiber.publish, ho, List.filterMap_append,
        observeList_noOwners, List.nil_append]
      rfl

theorem guardQueue_drainDue_single (p : NativeEff) (table : RowTable) (m : NativeMachine) :
    GuardQueue p table m [.drainDue] := by
  refine ⟨?_, List.nodup_nil, reservedKeys_nil m, ?_⟩
  · intro c hc
    cases List.mem_singleton.mp hc
    trivial
  · intro c hc
    cases List.mem_singleton.mp hc
    rfl

theorem guardQueue_exitFiber_nested (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (exit : ExitV)
    (state : GuardState m) (lookup : m.fiber? f.id = some f) :
    let result := exitFiber (interpOf p table) m { f with running := false } exit
    GuardQueue p table result.1 result.2 := by
  unfold exitFiber
  split
  · exact guardQueue_cons_evaluate p table f.id (guardQueue_nil p table _)
  · cases ho : f.observers with
    | nil => simpa only [exitFiber.exitStore, RunFiber.publish, ho] using guardQueue_drainDue_single p table _
    | cons o os =>
      let n := (m.update (f.publish exit)).emit [RunEvent.exited f.id exit]
      have after : GuardState n := guardState_emit (guardState_publish state lookup exit) _
      have lookup' : n.fiber? (f.publish exit).id = some (f.publish exit) :=
        fiber_lookup_update_self lookup _ rfl
      have reserved : ReservedKeys n (f.observers.flatMap observerKeys) :=
        reservedKeys_subset (reservedKeys_fiber (f := f.publish exit) after
          (List.mem_of_find?_eq_some lookup')) (List.subset_append_left ..)
      have queue := guardQueue_observe_list p table f.id exit f.observers
        (guardQueue_exitDone_drainDue p table lookup' rfl) reserved
      simpa only [exitFiber.exitStore, RunFiber.publish, ho, n] using queue

theorem guardQueue_driveStep_finish (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (exit : ExitV) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.finish target exit :: rest))
    (registration : RegistrationQueue rest) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.finish target exit) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  obtain ⟨f, lookup, running, park⟩ := queue.authority (.finish target exit) (List.mem_cons_self ..)
  have lookup' : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
  have fresh : f.id ∉ rest.filterMap (commandOwner m) := by
    have owners := queue.owners
    simp only [List.filterMap_cons, commandOwner] at owners
    simpa only [fiber_id_of_lookup lookup] using (List.nodup_cons.mp owners).1
  have tail := guardQueue_exitFiber_rest p table m f exit rest state lookup' running park
    (guardQueue_tail p table queue) registration fresh
  have front := guardQueue_exitFiber_nested p table m f exit state lookup'
  have joined := guardQueue_append_noOwners p table front tail
    (exitFiber_noOwners p table m { f with running := false } exit)
  simpa only [driveStep, lookup] using joined

theorem registrationQueue_observe_list (fiber : FiberId) (exit : ExitV)
    (observers : List Observer) {rest : List NCmd} (queue : RegistrationQueue rest) :
    RegistrationQueue (observers.map (.observe fiber exit) ++ rest) := by
  induction observers with
  | nil => exact queue
  | cons observer tail ih => exact ⟨True.intro, ih⟩

theorem registrationQueue_exitFiber (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) :
    RegistrationQueue (exitFiber (interpOf p table) m f exit).2 := by
  unfold exitFiber
  split
  · exact ⟨True.intro, True.intro⟩
  · cases ho : f.observers with
    | nil =>
      simp only [exitFiber.exitStore, RunFiber.publish, ho]
      exact ⟨True.intro, True.intro⟩
    | cons o os =>
      have queue := registrationQueue_observe_list f.id exit f.observers
        (rest := [.exitDone f.id, .drainDue]) ⟨True.intro, True.intro, True.intro⟩
      simpa only [exitFiber.exitStore, RunFiber.publish, ho] using queue

theorem registrationQueue_driveStep_finish (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (exit : ExitV) (rest : List NCmd)
    (registration : RegistrationQueue rest) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.finish target exit) rest).2 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using registration
  | some f =>
    simpa only [driveStep, hf] using registrationQueue_append
      (registrationQueue_exitFiber p table m { f with running := false } exit) registration


end Effect4.Program.Guard.FinishQueue

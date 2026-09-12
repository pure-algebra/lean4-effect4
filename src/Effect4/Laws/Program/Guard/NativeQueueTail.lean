import Effect4.Laws.Program.Guard.NativeState
import Effect4.Laws.Program.Guard.NativeStateLinks
import Effect4.Laws.Program.Guard.SettleQueue

/-!
Existing command-queue tail preservation through native evaluation and settlement.
First move the old queue through local evaluation using command controls;
then move it through the single-fiber settle update using ControlsAway.
The final key reservation uses the ORIGINAL machine's token bounds.
No driver induction and no construction of the newly emitted queue prefix.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Effect4.Program.Guard.NativeQueueTail
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.NativeState Effect4.Program.Guard.NativeStateLinks
open Effect4.Program.Guard.RegistrationQueue Effect4.Program.Guard.ReturnFields

abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

theorem queue_owners_transport (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} {commands : List NCmd}
    (queue : GuardQueue p table m commands) (races : RaceHostsPreserved m n) :
    commands.filterMap (commandOwner n) = commands.filterMap (commandOwner m) := by
  have aux : ∀ cs : List NCmd,
      (∀ c ∈ cs, commandOwner n c = commandOwner m c) →
      cs.filterMap (commandOwner n) = cs.filterMap (commandOwner m) := by
    intro cs
    induction cs with
    | nil => intro _; rfl
    | cons c cs ih =>
      intro h
      simp only [List.filterMap_cons, h c (List.mem_cons_self ..),
        ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]
  exact aux commands (fun c hc => commandOwner_transport p table races c (queue.authority c hc))

/-- Stage one requires preservation only of active/exited command controls,
not equality of the current code of an idle, unparked fiber. -/
theorem guardQueue_transport_commands (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} {commands : List NCmd}
    (queue : GuardQueue p table m commands) (controls : CommandControlsPreserved m n)
    (races : RaceHostsPreserved m n) (keys : ReservedKeys n (commands.flatMap commandKeys)) :
    GuardQueue p table n commands := by
  refine ⟨fun c hc => commandAuthority_transport_commands p table controls races c (queue.authority c hc),
    ?_, keys, queue.codeSites⟩
  rw [queue_owners_transport p table queue races]
  exact queue.owners

theorem guardQueue_evaluated_rest (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} {rest : List NCmd} (queue : GuardQueue p table m rest)
    (step : StateStep m n) (links : Links m n) : GuardQueue p table n rest :=
  guardQueue_transport_commands p table queue links.controls links.races (step.reserved queue.keys)

theorem controlsAway_refl (m : NativeMachine) (target : FiberId) : ControlsAway m m target := by
  intro fiber f lookup _ _
  exact ⟨f, lookup, rfl, rfl, rfl, fun h => h⟩

/-- Stage two uses the after-evaluation state, active owner and old tail, but
reserves the tail's keys from the original machine through the fresh park. -/
theorem guardQueue_settle_rest (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (rest : List NCmd) (it : NIter)
    (executing : ActiveAt m it.fiber.id)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (freshOwner : it.fiber.id ∉ rest.filterMap (commandOwner m))
    (step : StateStep m it.machine) (links : Links m it.machine) (freshPark : FreshPark m it) :
    GuardQueue p table (settle id rest it).1 rest := by
  have midQueue := guardQueue_evaluated_rest p table queue step links
  have midActive : ActiveAt it.machine it.fiber.id := commandControls_activeAt links.controls executing
  have midFresh : it.fiber.id ∉ rest.filterMap (commandOwner it.machine) := by
    rw [queue_owners_transport p table queue links.races]
    exact freshOwner
  have keysFinal := Effect4.Program.Guard.SettleQueue.reservedKeys_settle m id rest it _ queue.keys
    step.tokens freshPark step.requests
  exact Effect4.Program.Guard.SettleQueue.guardQueue_transport_away_reserved p table step.state midActive
    midQueue registration midFresh
    (Effect4.Program.Guard.SettleQueue.controlsAway_settle id rest it it.fiber.id rfl
      (controlsAway_refl it.machine it.fiber.id))
    (Effect4.Program.Guard.SettleQueue.raceHostsPreserved_settle id rest it
      (fun _ race hr => ⟨race, hr, rfl⟩)) keysFinal

/-- A supplied, separately proved new prefix can be joined to the transported
old tail when every owner in that prefix is the local returned fiber. -/
theorem guardQueue_settle (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (rest : List NCmd) (it : NIter)
    (executing : ActiveAt m it.fiber.id)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (freshOwner : it.fiber.id ∉ rest.filterMap (commandOwner m))
    (step : StateStep m it.machine) (links : Links m it.machine) (freshPark : FreshPark m it)
    (front : GuardQueue p table (settle id [] it).1 (settle id [] it).2)
    (owns : ∀ owner ∈ (settle id [] it).2.filterMap (commandOwner (settle id [] it).1),
      owner = it.fiber.id) :
    GuardQueue p table (settle id rest it).1 (settle id rest it).2 := by
  have tail := guardQueue_settle_rest p table m id rest it executing queue registration freshOwner
    step links freshPark
  have front' : GuardQueue p table (settle id rest it).1 (settle id [] it).2 :=
    (Effect4.Program.Guard.SettleQueue.settle_machine_rest id rest it) ▸ front
  have owns' : ∀ owner ∈ (settle id [] it).2.filterMap (commandOwner (settle id rest it).1),
      owner = it.fiber.id := (Effect4.Program.Guard.SettleQueue.settle_machine_rest id rest it) ▸ owns
  have fresh := Effect4.Program.Guard.SettleQueue.guardQueue_fresh_transport p table queue
    (Effect4.Program.Guard.SettleQueue.raceHostsPreserved_settle id rest it links.races) freshOwner
  have joined := Effect4.Program.Guard.SettleQueue.guardQueue_append_owned p table it.fiber.id front' tail owns' fresh
  rw [Effect4.Program.Guard.SettleQueue.settle_commands_rest]
  cases ho : it.outcome <;> try exact joined
  exact guardQueue_nil p table _

theorem native_settle_rest (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (rest : List NCmd) (f : NFiber) (yielding : Bool)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (freshOwner : f.id ∉ rest.filterMap (commandOwner m)) :
    GuardQueue p table (settle id rest (evaluateNative p m f yielding table)).1 rest := by
  have hid := Effect4.Program.Guard.Interruption.evaluateNative_id p table m f yielding
  apply guardQueue_settle_rest p table m id rest (evaluateNative p m f yielding table)
  · rw [hid]; exact ⟨f, lookup, running, park⟩
  · exact queue
  · exact registration
  · rw [hid]; exact freshOwner
  · exact evaluateNative_state p table state f yielding ⟨f, lookup⟩
  · exact evaluateNative_links p table m f yielding
  · exact evaluateNative_freshPark p table m f yielding park

theorem iteration_settle_rest (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (rest : List NCmd) (f : NFiber) (yielding : Bool)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (freshOwner : f.id ∉ rest.filterMap (commandOwner m)) :
    letI := evaluatorFor p table
    GuardQueue p table (settle id rest (iteration (interpOf p table) m f yielding)).1 rest := by
  letI := evaluatorFor p table
  have hid := Effect4.Program.Guard.Interruption.iteration_id p table m f yielding
  apply guardQueue_settle_rest p table m id rest (iteration (interpOf p table) m f yielding)
  · rw [hid]; exact ⟨f, lookup, running, park⟩
  · exact queue
  · exact registration
  · rw [hid]; exact freshOwner
  · exact iteration_state p table state f yielding ⟨f, lookup⟩
  · exact iteration_links p table m f yielding
  · exact iteration_freshPark p table m f yielding park

end Effect4.Program.Guard.NativeQueueTail

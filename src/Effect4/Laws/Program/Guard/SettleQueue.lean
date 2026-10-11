import Effect4.Laws.Program.Guard.RegistrationQueue
import Effect4.Laws.Program.Guard.Settle
import Effect4.Laws.Program.Guard.ReturnFields
import Effect4.Laws.Program.Guard.FinishQueue
import Effect4.Laws.Program.Guard.Messages
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.SettleQueue
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue Effect4.Program.Guard.Settle Effect4.Program.Guard.ReturnFields

theorem settledFiber_park (it : NIter) (token : Nat)
    (park : (settledFiber it).parked = .withGuard token) :
    it.fiber.parked = .withGuard token := by
  cases outcome : it.outcome with
  | parked =>
    simp only [settledFiber, outcome] at park
    split at park
    · cases park
    · exact park
  | _ => simpa only [settledFiber, outcome] using park

theorem updated_same_request {m : NativeMachine} {g : NFiber} {fiber : FiberId}
    {token : Nat} {request : NativeOp × Val} (same : g.id = fiber)
    (hr : requestOf (m.update g) fiber token = some request) : g.parked = .withGuard token := by
  obtain ⟨found, lookup, park, _⟩ := requestOf_shape hr
  rw [fiber_lookup_update] at lookup
  cases old : m.fiber? fiber with
  | none => simp only [old, Option.map_none] at lookup; cases lookup
  | some f =>
    simp only [old, Option.map_some, fiber_id_of_lookup old, same, ↓reduceIte,
      Option.some.injEq] at lookup
    exact lookup ▸ park

/-- The shared settlement word leaves queue reservation counters and race ownership unchanged. -/
theorem settle_queue_fields (id : FiberId) (rest : List NCmd) (it : NIter) :
    ((settle id rest it).1.nextToken, (settle id rest it).1.races) =
      (it.machine.nextToken, it.machine.races) := by
  apply Edits.settle_keeps (fun held : NativeMachine => (held.nextToken, held.races))
    (fun _ _ => rfl) (fun _ _ => rfl) _ (fun _ _ => rfl)
  intro target observer held
  simp only [Edit.apply, RunMachine.modify]
  split <;> rfl

theorem nextToken_settle (id : FiberId) (rest : List NCmd) (it : NIter) :
    (settle id rest it).1.nextToken = it.machine.nextToken :=
  congrArg Prod.fst (settle_queue_fields id rest it)

/-- Disposition of a currently stored owner introduces no external request. -/
theorem requestOf_settleOutcome_current (id : FiberId) (rest : List NCmd) (it : NIter)
    (current : it.machine.fiber? it.fiber.id = some it.fiber)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (offered : requestOf (settleOutcome id rest it).1 fiber token = some request) :
    requestOf it.machine fiber token = some request := by
  cases outcome : it.outcome with
  | parked =>
    simp only [settleOutcome, outcome] at offered
    split at offered
    · exact requestOf_update_unparked_subset it.machine _ rfl fiber token request offered
    · exact (requestOf_update_view current {it.fiber with running := false}
        ⟨rfl, rfl, rfl⟩ fiber token).symm.trans offered
  | stuck why =>
    simp only [settleOutcome, outcome] at offered
    exact (requestOf_update_view current {it.fiber with running := false}
      ⟨rfl, rfl, rfl⟩ fiber token).symm.trans offered
  | _ =>
    simp only [settleOutcome, outcome] at offered
    exact (requestOf_update_view current it.fiber ⟨rfl, rfl, rfl⟩ fiber token).symm.trans offered

theorem reservedKeys_settle (m : NativeMachine) (id : FiberId) (rest : List NCmd) (it : NIter)
    (keys : List GuardKey) (reserved : ReservedKeys m keys)
    (next : m.nextToken ≤ it.machine.nextToken) (fresh : FreshPark m it)
    (requests : ∀ fiber token request, requestOf it.machine fiber token = some request →
      requestOf m fiber token = some request) :
    ReservedKeys (settle id rest it).1 keys := by
  have install (g : NFiber) (key : g.id = it.fiber.id)
      (parked : ∀ token, g.parked = .withGuard token → it.fiber.parked = .withGuard token) :
      ReservedKeys (it.machine.update g) keys := by
    constructor
    · intro key hk
      exact Nat.lt_of_lt_of_le (reserved.below key hk) next
    · intro fiber token request hr hk
      by_cases same : g.id = fiber
      · have park := parked token (updated_same_request same hr)
        have eq := (fresh token park).1
        exact Nat.lt_irrefl _ (eq ▸ reserved.below (fiber, token) hk)
      · rw [requestOf_update_other _ _ _ _ same] at hr
        exact reserved.disjoint fiber token request (requests fiber token request hr) hk
  cases edits : it.edits with
  | nil =>
    simp only [settle, edits, settleOutcome_machine]
    have updated := install (settledFiber it) (settledFiber_id it) (settledFiber_park it)
    cases it.outcome with
    | stuck why => exact reservedKeys_halt updated why
    | _ => exact updated
  | cons edit tail =>
    have updated := install it.fiber rfl (fun _ h => h)
    have after : ReservedKeys (applyFiberEdits (edit :: tail) (it.machine.update it.fiber)).1 keys :=
      reservedKeys_of_requests_subset updated
        (Nat.le_of_eq (congrArg (fun held : NativeMachine => held.nextToken)
          (RunMachine.applyFiberEdits_shape (edit :: tail) (it.machine.update it.fiber)).1).symm)
        (Messages.requestOf_fiberEdits_subset (edit :: tail) _)
    simp only [settle, edits]
    split
    · exact reservedKeys_halt after _
    · next owner found =>
      apply reservedKeys_of_requests_subset after
      · rw [settleOutcome_machine]
        cases it.outcome <;> exact Nat.le_refl _
      · apply requestOf_settleOutcome_current
        simpa only [fiber_id_of_lookup found] using found

theorem guardQueue_transport_away_reserved (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} {target : FiberId} {commands : List NCmd}
    (state : GuardState m) (executing : ActiveAt m target)
    (queue : GuardQueue p table m commands) (registration : RegistrationQueue commands)
    (fresh : target ∉ commands.filterMap (commandOwner m))
    (controls : ControlsAway m n target) (races : RaceHostsPreserved m n)
    (keys : ReservedKeys n (commands.flatMap commandKeys)) :
    GuardQueue p table n commands := by
  refine ⟨fun c hc => commandAuthority_transport_away p table state executing queue registration
    fresh controls races c hc, ?_, keys, queue.codeSites⟩
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
  rw [aux commands (fun c hc => commandOwner_transport p table races c (queue.authority c hc))]
  exact queue.owners

/-- The outcome changes only its owner's control fields. -/
theorem controlsAway_settleOutcome {m : NativeMachine} (id : FiberId) (rest : List NCmd)
    (it : NIter) (target : FiberId) (hid : it.fiber.id = target)
    (controls : ControlsAway m it.machine target) :
    ControlsAway m (settleOutcome id rest it).1 target := by
  have updated : ControlsAway m (it.machine.update (settledFiber it)) target :=
    Effect4.Program.Guard.FinishQueue.controlsAway_trans controls
      (by simpa only [settledFiber_id, hid] using controlsAway_update it.machine (settledFiber it))
  rw [settleOutcome_machine]
  cases it.outcome <;> exact updated

/-- Messages retain the fields read by commands away from the local owner. -/
theorem controlsAway_fiberEdits (m : NativeMachine)
    (edits : List (FiberEdit Err Defect FiberId Ann)) (target : FiberId) :
    ControlsAway m (applyFiberEdits edits m).1 target := by
  intro fiber f found _ eligible
  obtain ⟨g, lookup, word⟩ := (Moves.InterferesWithLookup.fiberEdits edits m).lookup fiber f found
  exact ⟨g, lookup, word.controls (eligible.elim (fun h => Or.inl h.1) Or.inr)⟩

theorem controlsAway_settle {m : NativeMachine} (id : FiberId) (rest : List NCmd)
    (it : NIter) (target : FiberId) (hid : it.fiber.id = target)
    (controls : ControlsAway m it.machine target) :
    ControlsAway m (settle id rest it).1 target := by
  cases edits : it.edits with
  | nil =>
    simp only [settle, edits]
    exact controlsAway_settleOutcome id rest it target hid controls
  | cons edit tail =>
    have installed := Effect4.Program.Guard.FinishQueue.controlsAway_trans controls
      (hid ▸ controlsAway_update it.machine it.fiber)
    have changed := Effect4.Program.Guard.FinishQueue.controlsAway_trans installed
      (controlsAway_fiberEdits (it.machine.update it.fiber) (edit :: tail) target)
    simp only [settle, edits]
    split
    · exact changed
    · next owner found =>
      exact controlsAway_settleOutcome id rest _ target
        ((fiber_id_of_lookup found).trans hid) changed

theorem races_settle (id : FiberId) (rest : List NCmd) (it : NIter) :
    (settle id rest it).1.races = it.machine.races :=
  congrArg Prod.snd (settle_queue_fields id rest it)

theorem raceHostsPreserved_settle {m : NativeMachine} (id : FiberId) (rest : List NCmd)
    (it : NIter) (races : RaceHostsPreserved m it.machine) :
    RaceHostsPreserved m (settle id rest it).1 := by
  intro raceId race hr
  obtain ⟨next, lookup, host⟩ := races raceId race hr
  refine ⟨next, ?_, host⟩
  simpa only [RunMachine.race?, races_settle] using lookup

theorem guardQueue_settle_rest (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (rest : List NCmd) (it : NIter)
    (state : GuardState m) (executing : ActiveAt m it.fiber.id)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (freshOwner : it.fiber.id ∉ rest.filterMap (commandOwner m))
    (controls : ControlsAway m it.machine it.fiber.id)
    (races : RaceHostsPreserved m it.machine) (next : m.nextToken ≤ it.machine.nextToken)
    (freshPark : FreshPark m it)
    (requests : ∀ fiber token request, requestOf it.machine fiber token = some request →
      requestOf m fiber token = some request) :
    GuardQueue p table (settle id rest it).1 rest := by
  exact guardQueue_transport_away_reserved p table state executing queue registration freshOwner
    (controlsAway_settle id rest it it.fiber.id rfl controls)
    (raceHostsPreserved_settle id rest it races)
    (reservedKeys_settle m id rest it _ queue.keys next freshPark requests)

theorem guardQueue_fresh_transport (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} {commands : List NCmd} {target : FiberId}
    (queue : GuardQueue p table m commands) (races : RaceHostsPreserved m n)
    (fresh : target ∉ commands.filterMap (commandOwner m)) :
    target ∉ commands.filterMap (commandOwner n) := by
  intro member
  obtain ⟨command, hc, owner⟩ := List.mem_filterMap.mp member
  rw [commandOwner_transport p table races command (queue.authority command hc)] at owner
  exact fresh (List.mem_filterMap.mpr ⟨command, hc, owner⟩)

theorem guardQueue_append_owned (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {front rest : List NCmd} (target : FiberId)
    (left : GuardQueue p table m front) (right : GuardQueue p table m rest)
    (owns : ∀ owner ∈ front.filterMap (commandOwner m), owner = target)
    (fresh : target ∉ rest.filterMap (commandOwner m)) :
    GuardQueue p table m (front ++ rest) := by
  constructor
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact left.authority c h
    · exact right.authority c h
  · rw [List.filterMap_append, List.nodup_append]
    refine ⟨left.owners, right.owners, ?_⟩
    intro owner ho target' ht same
    exact fresh ((owns owner ho) ▸ (same ▸ ht))
  · simpa only [List.flatMap_append] using reservedKeys_append left.keys right.keys
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact left.codeSites c h
    · exact right.codeSites c h

theorem settle_machine_rest (id : FiberId) (rest : List NCmd) (it : NIter) :
    (settle id rest it).1 = (settle id [] it).1 := by
  rw [Edits.settle_word, Edits.settle_word]

/-- Settlement either halts or appends the old command tail to its new prefix. -/
theorem settle_commands_rest_cases (id : FiberId) (rest : List NCmd) (it : NIter) :
    (settle id rest it).2 = [] ∨ (settle id rest it).2 = (settle id [] it).2 ++ rest := by
  have outcome (next : NIter) :
      (settleOutcome id rest next).2 = [] ∨
        (settleOutcome id rest next).2 = (settleOutcome id [] next).2 ++ rest := by
    cases result : next.outcome with
    | stuck why => exact Or.inl (by simp only [settleOutcome, result])
    | parked =>
      simp only [settleOutcome, result]
      split <;> exact Or.inr (by simp only [List.append_nil, List.append_assoc])
    | _ => exact Or.inr (by simp only [settleOutcome, result, List.append_nil, List.append_assoc])
  cases edits : it.edits with
  | nil => simpa only [settle, edits] using outcome it
  | cons edit tail =>
    simp only [settle, edits]
    split
    · exact Or.inl rfl
    · exact outcome _

/-- The old precise tail equation requires retention of the selected owner for nonempty messages. -/
theorem settle_commands_rest (id : FiberId) (rest : List NCmd) (it : NIter)
    (retained : it.edits ≠ [] → ∃ f, it.machine.fiber? it.fiber.id = some f) :
    (settle id rest it).2 =
      match it.outcome with
      | .stuck _ => []
      | _ => (settle id [] it).2 ++ rest := by
  have outcome (next : NIter) :
      (settleOutcome id rest next).2 = match next.outcome with
      | .stuck _ => []
      | _ => (settleOutcome id [] next).2 ++ rest := by
    cases result : next.outcome with
    | parked =>
      simp only [settleOutcome, result]
      split <;> simp only [List.append_nil, List.append_assoc]
    | _ => simp only [settleOutcome, result, List.append_nil, List.append_assoc]
  cases edits : it.edits with
  | nil => simpa only [settle, edits] using outcome it
  | cons edit tail =>
    obtain ⟨old, found⟩ := retained (by intro empty; rw [edits] at empty; cases empty)
    have installed := fiber_lookup_update_self found it.fiber rfl
    obtain ⟨owner, lookup, _⟩ :=
      (Moves.InterferesWithLookup.fiberEdits (edit :: tail) (it.machine.update it.fiber)).lookup
        it.fiber.id it.fiber installed
    simp only [settle, edits, lookup]
    exact outcome _

theorem guardQueue_settle (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (id : FiberId) (rest : List NCmd) (it : NIter)
    (state : GuardState m) (executing : ActiveAt m it.fiber.id)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (freshOwner : it.fiber.id ∉ rest.filterMap (commandOwner m))
    (controls : ControlsAway m it.machine it.fiber.id)
    (races : RaceHostsPreserved m it.machine) (next : m.nextToken ≤ it.machine.nextToken)
    (freshPark : FreshPark m it)
    (requests : ∀ fiber token request, requestOf it.machine fiber token = some request →
      requestOf m fiber token = some request)
    (front : GuardQueue p table (settle id [] it).1 (settle id [] it).2)
    (owns : ∀ owner ∈ (settle id [] it).2.filterMap (commandOwner (settle id [] it).1),
      owner = it.fiber.id) :
    GuardQueue p table (settle id rest it).1 (settle id rest it).2 := by
  have tail := guardQueue_settle_rest p table m id rest it state executing queue registration
    freshOwner controls races next freshPark requests
  have front' : GuardQueue p table (settle id rest it).1 (settle id [] it).2 :=
    (settle_machine_rest id rest it) ▸ front
  have owns' : ∀ owner ∈ (settle id [] it).2.filterMap (commandOwner (settle id rest it).1),
      owner = it.fiber.id := (settle_machine_rest id rest it) ▸ owns
  have fresh := guardQueue_fresh_transport p table queue
    (raceHostsPreserved_settle id rest it races) freshOwner
  have joined := guardQueue_append_owned p table it.fiber.id front' tail owns' fresh
  rcases settle_commands_rest_cases id rest it with stopped | continues
  · rw [stopped]; exact guardQueue_nil p table _
  · rw [continues]; exact joined

end Effect4.Program.Guard.SettleQueue

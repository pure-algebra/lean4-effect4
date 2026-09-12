import Effect4.Laws.Program.Guard.RegistrationQueue
import Effect4.Laws.Program.Guard.Settle
import Effect4.Laws.Program.Guard.ReturnFields
import Effect4.Laws.Program.Guard.FinishQueue
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.SettleQueue
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue Effect4.Program.Guard.Settle Effect4.Program.Guard.ReturnFields

theorem settledFiber_park (it : NIter) (token : Nat)
    (park : (settledFiber it).parked = .withGuard token) :
    it.fiber.parked = .withGuard token := by
  cases ho : it.outcome <;> simp only [settledFiber, ho] at park
  all_goals try exact park
  split at park
  · cases park
  · exact park

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

theorem nextToken_settle (id : FiberId) (rest : List NCmd) (it : NIter) :
    (settle id rest it).1.nextToken = it.machine.nextToken := by
  cases ho : it.outcome <;> simp only [settle, ho]
  all_goals repeat' first | rfl | split

theorem reservedKeys_settle (m : NativeMachine) (id : FiberId) (rest : List NCmd) (it : NIter)
    (keys : List GuardKey) (reserved : ReservedKeys m keys)
    (next : m.nextToken ≤ it.machine.nextToken) (fresh : FreshPark m it)
    (requests : ∀ fiber token request, requestOf it.machine fiber token = some request →
      requestOf m fiber token = some request) :
    ReservedKeys (settle id rest it).1 keys := by
  have updated : ReservedKeys (it.machine.update (settledFiber it)) keys := by
    constructor
    · intro key hk
      exact Nat.lt_of_lt_of_le (reserved.below key hk) next
    · intro fiber token request hr hk
      by_cases same : (settledFiber it).id = fiber
      · have park := settledFiber_park it token (updated_same_request same hr)
        have eq := (fresh token park).1
        have bound := reserved.below (fiber, token) hk
        exact Nat.lt_irrefl _ (eq ▸ bound)
      · rw [requestOf_update_other _ _ _ _ same] at hr
        exact reserved.disjoint fiber token request (requests fiber token request hr) hk
  cases ho : it.outcome <;> simp only [settle, ho, settledFiber] at updated ⊢
  all_goals try exact updated
  case parked => split at updated <;> simp_all
  case stuck why => exact reservedKeys_halt updated why

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

theorem controlsAway_settle {m : NativeMachine} (id : FiberId) (rest : List NCmd)
    (it : NIter) (target : FiberId) (hid : it.fiber.id = target)
    (controls : ControlsAway m it.machine target) :
    ControlsAway m (settle id rest it).1 target := by
  have updated : ControlsAway m (it.machine.update (settledFiber it)) target :=
    Effect4.Program.Guard.FinishQueue.controlsAway_trans controls
      (by simpa only [settledFiber_id, hid] using controlsAway_update it.machine (settledFiber it))
  cases ho : it.outcome <;> simp only [settle, ho, settledFiber] at updated ⊢
  all_goals try exact updated
  split at updated <;> simp_all

theorem races_settle (id : FiberId) (rest : List NCmd) (it : NIter) :
    (settle id rest it).1.races = it.machine.races := by
  cases ho : it.outcome <;> simp only [settle, ho]
  all_goals repeat' first | rfl | split

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
  cases ho : it.outcome <;> simp only [settle, ho]
  all_goals repeat' first | rfl | split

theorem settle_commands_rest (id : FiberId) (rest : List NCmd) (it : NIter) :
    (settle id rest it).2 =
      match it.outcome with
      | .stuck _ => []
      | _ => (settle id [] it).2 ++ rest := by
  cases ho : it.outcome <;> simp only [settle, ho, List.append_nil, List.append_assoc]
  all_goals repeat' first | rfl | split
  all_goals simp_all only [List.append_assoc]

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
  rw [settle_commands_rest]
  cases ho : it.outcome <;> try exact joined
  exact guardQueue_nil p table _


end Effect4.Program.Guard.SettleQueue

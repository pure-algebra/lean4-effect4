import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.Settle
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.RegistrationQueue
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

/-- Race registration work is followed by the command that returns to its host. -/
def RegistrationTail (command : NCmd) (rest : List NCmd) : Prop :=
  match command with
  | .launch race | .enrollRace race _ => ∃ yielding, .registrationDone race yielding ∈ rest
  | _ => True

def RegistrationQueue : List NCmd → Prop
  | [] => True
  | command :: rest => RegistrationTail command rest ∧ RegistrationQueue rest

theorem registrationTail_mono (command : NCmd) {left right : List NCmd}
    (subset : left ⊆ right) (h : RegistrationTail command left) :
    RegistrationTail command right := by
  cases command <;> try trivial
  all_goals obtain ⟨yielding, hy⟩ := h
  all_goals exact ⟨yielding, subset hy⟩

theorem registrationQueue_tail {command : NCmd} {rest : List NCmd}
    (queue : RegistrationQueue (command :: rest)) : RegistrationQueue rest := queue.2

theorem registrationQueue_member {commands : List NCmd} (queue : RegistrationQueue commands)
    {command : NCmd} (member : command ∈ commands) : RegistrationTail command commands := by
  induction commands with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact registrationTail_mono _ (fun _ h => List.mem_cons_of_mem _ h) queue.1
    · exact registrationTail_mono _ (fun _ h => List.mem_cons_of_mem _ h) (ih queue.2 tail)

theorem registrationQueue_append {left right : List NCmd}
    (hl : RegistrationQueue left) (hr : RegistrationQueue right) :
    RegistrationQueue (left ++ right) := by
  induction left with
  | nil => exact hr
  | cons first rest ih =>
    exact ⟨registrationTail_mono _ (List.subset_append_left ..) hl.1, ih hl.2⟩

theorem registration_owner_mem {m : NativeMachine} {commands : List NCmd}
    {raceId : Nat} {race : NRace} (lookup : m.race? raceId = some race)
    (pending : RegistrationTail (.launch raceId) commands) :
    race.host ∈ commands.filterMap (commandOwner m) := by
  obtain ⟨yielding, member⟩ := pending
  refine List.mem_filterMap.mpr ⟨.registrationDone raceId yielding, member, ?_⟩
  simp only [commandOwner, lookup, Option.map_some]

/-- Replacing the currently executing fiber may change its own frame and flags. -/
def ControlsAway (m n : NativeMachine) (target : FiberId) : Prop :=
  ∀ fiber f, m.fiber? fiber = some f → fiber ≠ target →
    (f.parked = .notParked ∨ f.exit.isSome = true) → ∃ g, n.fiber? fiber = some g ∧
    g.frame.current = f.frame.current ∧ g.parked = f.parked ∧ g.exit = f.exit ∧
    (f.running = true → g.running = true)

theorem controlsAway_update (m : NativeMachine) (f : NFiber) :
    ControlsAway m (m.update f) f.id := by
  intro fiber old lookup other _
  refine ⟨old, ?_, rfl, rfl, rfl, fun h => h⟩
  simp only [fiber_lookup_update, lookup, Option.map_some, fiber_id_of_lookup lookup,
    other, ↓reduceIte]

theorem activeAt_transport_away {m n : NativeMachine} {target fiber : FiberId}
    (controls : ControlsAway m n target) (other : fiber ≠ target) (active : ActiveAt m fiber) :
    ActiveAt n fiber := by
  obtain ⟨f, lookup, running, park⟩ := active
  obtain ⟨g, after, _, park', _, running'⟩ := controls fiber f lookup other (Or.inl park)
  exact ⟨g, after, running' running, park'.trans park⟩

theorem commandAuthority_transport_away (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} {target : FiberId} {commands : List NCmd}
    (state : GuardState m) (executing : ActiveAt m target)
    (queue : GuardQueue p table m commands) (registration : RegistrationQueue commands)
    (fresh : target ∉ commands.filterMap (commandOwner m))
    (controls : ControlsAway m n target) (races : RaceHostsPreserved m n)
    (command : NCmd) (member : command ∈ commands) : CommandAuthority p table n command := by
  have authority := queue.authority command member
  have pending := registrationQueue_member registration member
  have owner_other {fiber : FiberId} (owner : commandOwner m command = some fiber) :
      fiber ≠ target := by
    intro same
    apply fresh
    exact same ▸ List.mem_filterMap.mpr ⟨command, member, owner⟩
  cases command <;> try exact True.intro
  all_goals try exact activeAt_transport_away controls (owner_other rfl) authority
  case launch raceId =>
    obtain ⟨race, hr, active⟩ := authority
    obtain ⟨next, hn, host⟩ := races raceId race hr
    have other : race.host ≠ target := fun same =>
      fresh (same ▸ registration_owner_mem hr pending)
    exact ⟨next, hn, host ▸ activeAt_transport_away controls other active⟩
  case enrollRace raceId child =>
    obtain ⟨race, hr, active⟩ := authority
    obtain ⟨next, hn, host⟩ := races raceId race hr
    have other : race.host ≠ target := fun same =>
      fresh (same ▸ registration_owner_mem hr pending)
    exact ⟨next, hn, host ▸ activeAt_transport_away controls other active⟩
  case registrationDone raceId yielding =>
    obtain ⟨race, f, hr, hf, running, park, code⟩ := authority
    have other : race.host ≠ target := owner_other (by simp only [commandOwner, hr, Option.map_some])
    obtain ⟨next, hn, host⟩ := races raceId race hr
    obtain ⟨g, hg, current, park', _, running'⟩ := controls race.host f hf other (Or.inl park)
    exact ⟨next, g, hn, host ▸ hg, running' running, park'.trans park, current ▸ code⟩
  case exitDone fiber =>
    obtain ⟨f, hf, exited⟩ := authority
    have other : fiber ≠ target := by
      intro same
      obtain ⟨g, hg, running, _⟩ := executing
      have eq : f = g := Option.some.inj ((same ▸ hf).symm.trans hg)
      have stopped := (state.exited f (List.mem_of_find?_eq_some hf) exited).2
      exact Bool.noConfusion (stopped.symm.trans (eq ▸ running))
    obtain ⟨g, hg, _, _, exit', _⟩ := controls fiber f hf other (Or.inr exited)
    exact ⟨g, hg, exit' ▸ exited⟩

theorem guardQueue_transport_away (p : NativeEff) (table : RowTable)
    {m n : NativeMachine} {target : FiberId} {commands : List NCmd}
    (state : GuardState m) (executing : ActiveAt m target)
    (queue : GuardQueue p table m commands) (registration : RegistrationQueue commands)
    (fresh : target ∉ commands.filterMap (commandOwner m))
    (controls : ControlsAway m n target) (races : RaceHostsPreserved m n)
    (next : m.nextToken ≤ n.nextToken)
    (requests : ∀ fiber token request, requestOf n fiber token = some request →
      requestOf m fiber token = some request) :
    GuardQueue p table n commands := by
  refine ⟨fun c hc => commandAuthority_transport_away p table state executing queue registration
    fresh controls races c hc, ?_, reservedKeys_of_requests_subset queue.keys next requests,
    queue.codeSites⟩
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


end Effect4.Program.Guard.RegistrationQueue

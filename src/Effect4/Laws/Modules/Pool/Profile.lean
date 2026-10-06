import Effect4.Laws.Modules.Pool.Model
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Pool's first profile: its states, their closure, and the model's facts

`Profile` is the predicate of the first profile's states (decisions rows 267 to 269): the
stamps, the idle items, the leases and the waiters. `profile_closed`: each transition of the
model (`src/Effect4/Laws/Modules/Pool/Model.lean`) keeps the predicate, with no premise on its
request. No term, no cell and no machine occurs in this file.

| Statement | What it says |
| --- | --- |
| `profile_closed` | each of the six transitions keeps the profile |
| `initial_profile` | the pool as it is made is of the profile, and its idle stamps are the numbers below its size |
| `step_items` | no transition adds an item, removes one or changes a resource |
| `lease_enrols_iff` | lease or enrol adds a waiter only when the pool is open and no item is idle |
| `select_takes_first` | a selection takes the first waiters, at most its count, and exactly those |
| `giveBack_front` | a return puts its item at the front, and it keeps every item |
| `giveBack_once` | a lease that returned holds nothing: its second return changes nothing |
| `close_refuses` | after the close's first step no lease begins |
| `drain_waits` | the closer's step answers true exactly where no lease is outstanding |

**An idle item beside enrolled waiters is a state of the profile.** No part of `Profile`
relates `available` to `waiters`. A return makes its item idle at once, and the selection of
its helper comes later. The rule is on the step, and `lease_enrols_iff` states it.

Placement.

- **The closure.** Concept `store-typing`, requirement R4: the model's half of the proposed
  claim `pool-profile-preserved`. Consumer: the public law, along a run. Reach: every
  transition of the model, on the profile's states. It establishes nothing about a program,
  and no progress of a waiter.
- **The enrolment rule.** Concept `store-typing`, requirement R4, beside the closure. Its
  consumers are the lease step's agreement (requirement R10) and then the public waiting
  wrapper. Reach: one transition of the model, on the profile's states. It states no fairness
  and no liveness, and nothing about a later selection.
- **The selection's fact.** Concept `reactive-scheduling`, requirement R12. Its consumer is the
  proposed claim `pool-wake-selection`. Reach: one selection of the model. It states nothing
  about a run, and no liveness.
- **The facts of a return, of the close's first step and of the closer's step.** Concept
  `scope-lifetime-finalization`, requirement R11. Their consumers are the proposed claims
  `pool-lease-return` and `pool-close-waits`. Reach: one transition of the model, and for the
  close every later transition. They state nothing about a finalizer's run, and no completed
  close. The closer's fact states one step: it gives no wait along a run.

The pinned axiom and plan outputs and the finite controls are in
`Test/Program/PoolContract.lean`.
-/

set_option autoImplicit false

namespace Effect4.Pool.Model

/-- **The states of the first profile.** Four parts: the items' stamps, the idle items, the
leases' stamps and the waiters' identities. -/
structure Profile (s : State) : Prop where
  /-- The items' stamps are distinct. -/
  stamps : (s.items.map (·.stamp)).Nodup
  /-- An idle item is an item that no lease holds: each idle stamp names an item that is not
  borrowed. -/
  idle : ∀ i ∈ s.available, ∃ it ∈ s.items, it.stamp = i ∧ it.borrowed = false
  /-- The idle items and the leased items together are the items: an item that no lease holds
  is idle. -/
  unheld : ∀ it ∈ s.items, it.borrowed = false → it.stamp ∈ s.available
  /-- No stamp is idle twice. -/
  once : s.available.Nodup
  /-- The leases' stamps are distinct: no two borrowed items share one. -/
  apart : s.items.Pairwise fun a b => a.borrowed = true → b.borrowed = true → a.lease ≠ b.lease
  /-- Each lease's stamp is below the stamp of the next lease. -/
  below : ∀ it ∈ s.items, it.borrowed = true → it.lease < s.next
  /-- No two waiters share an identity. -/
  distinct : s.waiters.Nodup

/-! ## The removal by identity -/

theorem mem_without {w : Nat} {waiters : List Nat} {id : Nat} :
    w ∈ without waiters id ↔ w ∈ waiters ∧ w ≠ id := by
  unfold without
  rw [List.mem_filter, bne_iff_ne]

theorem without_sublist (waiters : List Nat) (id : Nat) :
    (without waiters id).Sublist waiters :=
  List.filter_sublist

/-- A request enrols at the list's end, after its own entry left: the identities stay
distinct. -/
theorem enrol_nodup {waiters : List Nat} (distinct : waiters.Nodup) (id : Nat) :
    (without waiters id ++ [id]).Nodup := by
  refine List.pairwise_append.mpr
    ⟨distinct.sublist (without_sublist _ _), List.pairwise_singleton _ _, ?_⟩
  intro a ha b hb
  rw [List.mem_singleton.mp hb]
  exact (mem_without.mp ha).2

/-! ## The items: a stamp names one item -/

/-- Two items of one stamp, in a list of distinct stamps, are one item. -/
theorem eq_of_stamp : ∀ {items : List Item}, (items.map (·.stamp)).Nodup →
    ∀ {a b : Item}, a ∈ items → b ∈ items → a.stamp = b.stamp → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, distinct, a, b, ha, hb, same => by
    rw [List.map_cons, List.nodup_cons] at distinct
    obtain ⟨fresh, rest⟩ := distinct
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨b, hb', same.symm⟩) fresh
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (List.mem_map.mpr ⟨a, ha', same⟩) fresh
      · exact eq_of_stamp rest ha' hb' same

/-- A map that keeps each stamp and each resource keeps the items' stamps and resources. -/
theorem map_keeps {items : List Item} {f : Item → Item}
    (keeps : ∀ it, ((f it).stamp, (f it).resource) = (it.stamp, it.resource)) :
    (items.map f).map (fun it => (it.stamp, it.resource)) =
      items.map (fun it => (it.stamp, it.resource)) := by
  rw [List.map_map]
  exact List.map_congr_left fun it _ => keeps it

/-- A map that keeps each stamp keeps the stamps. -/
theorem map_stamps {items : List Item} {f : Item → Item} (keeps : ∀ it, (f it).stamp = it.stamp) :
    (items.map f).map (·.stamp) = items.map (·.stamp) := by
  rw [List.map_map]
  exact List.map_congr_left fun it _ => keeps it

theorem leasedAs_stamp (it : Item) (i l : Nat) :
    (if it.stamp = i then it.leasedAs l else it).stamp = it.stamp := by
  split <;> rfl

theorem heldBy_iff {it : Item} {i l : Nat} :
    it.heldBy i l = true ↔ it.stamp = i ∧ it.borrowed = true ∧ it.lease = l := by
  unfold Item.heldBy
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]

theorem freed_stamp (it : Item) (i l : Nat) :
    (if it.heldBy i l = true then { it with borrowed := false } else it).stamp = it.stamp := by
  split <;> rfl

/-- An item that a return leaves borrowed was borrowed, at the same lease. -/
theorem freed_borrowed {it : Item} {i l : Nat}
    (held : (if it.heldBy i l = true then { it with borrowed := false } else it).borrowed = true) :
    it.borrowed = true ∧
      (if it.heldBy i l = true then { it with borrowed := false } else it).lease = it.lease := by
  by_cases holds : it.heldBy i l = true
  · rw [if_pos holds] at held
    exact absurd held Bool.false_ne_true
  · rw [if_neg holds] at held ⊢
    exact ⟨held, rfl⟩

/-! ## Three ways a transition changes a state -/

/-- A state that differs in its waiters alone, with distinct identities, is of the profile. -/
theorem Profile.waiters {s : State} (h : Profile s) {waiters : List Nat}
    (distinct : waiters.Nodup) : Profile { s with waiters := waiters } :=
  ⟨h.stamps, h.idle, h.unheld, h.once, h.apart, h.below, distinct⟩

/-- **A lease of the front idle item.** The item of the front stamp becomes borrowed at the
stamp `next`, the stamp leaves `available`, and `next` gains one. -/
theorem Profile.leaseFront {s : State} (h : Profile s) {i : Nat} {rest : List Nat}
    (front : s.available = i :: rest) {waiters : List Nat} (distinct : waiters.Nodup) :
    Profile
      { s with
        items := mark s.items i s.next, available := rest, waiters := waiters,
        next := s.next + 1 } := by
  have once := h.once
  rw [front] at once
  obtain ⟨fresh, restOnce⟩ := List.nodup_cons.mp once
  refine ⟨?_, ?_, ?_, restOnce, ?_, ?_, distinct⟩
  · show ((mark s.items i s.next).map (·.stamp)).Nodup
    unfold mark
    rw [map_stamps fun it => leasedAs_stamp it i s.next]
    exact h.stamps
  · intro j member
    obtain ⟨it, inside, named, idleNow⟩ :=
      h.idle j (by rw [front]; exact List.mem_cons_of_mem i member)
    have other : ¬ it.stamp = i := fun same => fresh (by rw [← same, named]; exact member)
    exact ⟨it, List.mem_map.mpr ⟨it, inside, if_neg other⟩, named, idleNow⟩
  · intro it' member idleNow
    obtain ⟨it, inside, rfl⟩ := List.mem_map.mp member
    by_cases same : it.stamp = i
    · rw [if_pos same] at idleNow
      exact absurd idleNow (Bool.noConfusion)
    · rw [if_neg same] at idleNow ⊢
      have was := h.unheld it inside idleNow
      rw [front] at was
      rcases List.mem_cons.mp was with head | tail
      · exact absurd head same
      · exact tail
  · show (mark s.items i s.next).Pairwise _
    unfold mark
    rw [List.pairwise_map]
    have stampsApart : s.items.Pairwise (fun a b => a.stamp ≠ b.stamp) :=
      List.pairwise_map.mp h.stamps
    refine List.Pairwise.imp_of_mem ?_ (stampsApart.and h.apart)
    intro a b ha hb both heldA heldB
    obtain ⟨differ, old⟩ := both
    by_cases sa : a.stamp = i
    · by_cases sb : b.stamp = i
      · exact absurd (sa.trans sb.symm) differ
      · rw [if_pos sa]
        rw [if_neg sb] at heldB ⊢
        exact Nat.ne_of_gt (h.below b hb heldB)
    · by_cases sb : b.stamp = i
      · rw [if_neg sa] at heldA ⊢
        rw [if_pos sb]
        exact Nat.ne_of_lt (h.below a ha heldA)
      · rw [if_neg sa] at heldA ⊢
        rw [if_neg sb] at heldB ⊢
        exact old heldA heldB
  · intro it' member held
    obtain ⟨it, inside, rfl⟩ := List.mem_map.mp member
    by_cases same : it.stamp = i
    · rw [if_pos same]
      exact Nat.lt_succ_self _
    · rw [if_neg same] at held ⊢
      exact Nat.lt_succ_of_lt (h.below it inside held)

/-- **A return of a lease that holds its item.** The item is idle again, and its stamp joins
the front of `available`. -/
theorem Profile.returnFront {s : State} (h : Profile s) {i l : Nat} {it0 : Item}
    (inside0 : it0 ∈ s.items) (holds0 : it0.heldBy i l = true) :
    Profile { s with items := freed s.items i l, available := i :: s.available } := by
  obtain ⟨stamp0, borrowed0, -⟩ := heldBy_iff.mp holds0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.distinct⟩
  · show ((freed s.items i l).map (·.stamp)).Nodup
    unfold freed
    rw [map_stamps fun it => freed_stamp it i l]
    exact h.stamps
  · intro j member
    rcases List.mem_cons.mp member with head | tail
    · exact ⟨{ it0 with borrowed := false },
        List.mem_map.mpr ⟨it0, inside0, if_pos holds0⟩, stamp0.trans head.symm, rfl⟩
    · obtain ⟨it, inside, named, idleNow⟩ := h.idle j tail
      have notHeld : ¬ it.heldBy i l = true := fun holds => by
        rw [(heldBy_iff.mp holds).2.1] at idleNow
        exact Bool.noConfusion idleNow
      exact ⟨it, List.mem_map.mpr ⟨it, inside, if_neg notHeld⟩, named, idleNow⟩
  · intro it' member idleNow
    obtain ⟨it, inside, rfl⟩ := List.mem_map.mp member
    by_cases holds : it.heldBy i l = true
    · rw [if_pos holds]
      exact List.mem_cons.mpr (Or.inl (heldBy_iff.mp holds).1)
    · rw [if_neg holds] at idleNow ⊢
      exact List.mem_cons_of_mem i (h.unheld it inside idleNow)
  · refine List.nodup_cons.mpr ⟨fun already => ?_, h.once⟩
    obtain ⟨it, inside, named, idleNow⟩ := h.idle i already
    have same : it = it0 := eq_of_stamp h.stamps inside inside0 (named.trans stamp0.symm)
    rw [same, borrowed0] at idleNow
    exact Bool.noConfusion idleNow
  · show (freed s.items i l).Pairwise _
    unfold freed
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ h.apart
    intro a b old heldA heldB
    obtain ⟨wasA, leaseA⟩ := freed_borrowed heldA
    obtain ⟨wasB, leaseB⟩ := freed_borrowed heldB
    rw [leaseA, leaseB]
    exact old wasA wasB
  · intro it' member held
    obtain ⟨it, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨was, leaseSame⟩ := freed_borrowed held
    rw [leaseSame]
    exact h.below it inside was

/-! ## The six transitions -/

theorem withdraw_profile {s : State} (h : Profile s) (id : Nat) : Profile (withdraw s id) :=
  h.waiters (h.distinct.sublist (without_sublist _ _))

theorem lease_profile {s : State} (h : Profile s) (id : Nat) : Profile (lease s id).1 := by
  unfold lease
  split
  · exact withdraw_profile h id
  · split
    · exact h.waiters (enrol_nodup h.distinct id)
    · next i rest front =>
      exact h.leaseFront front (h.distinct.sublist (without_sublist _ _))

theorem giveBack_profile {s : State} (h : Profile s) (i l : Nat) :
    Profile (giveBack s i l).1 := by
  unfold giveBack
  split
  · next held =>
    obtain ⟨it0, inside0, holds0⟩ := List.any_eq_true.mp held
    exact h.returnFront inside0 holds0
  · exact h

theorem select_profile {s : State} (h : Profile s) (count : Nat) :
    Profile (select s count).1 :=
  h.waiters (h.distinct.sublist (List.drop_sublist _ _))

theorem close_profile {s : State} (h : Profile s) : Profile (close s).1 :=
  ⟨h.stamps, h.idle, h.unheld, h.once, h.apart, h.below, h.distinct⟩

theorem drain_profile {s : State} (h : Profile s) (id : Nat) : Profile (drain s id).1 := by
  unfold drain
  split
  · exact h.waiters (enrol_nodup h.distinct id)
  · exact withdraw_profile h id

/-! ## The closure -/

/-- **The first profile is closed.** Each transition of the model leaves a state of the
profile. No premise names the request: a lease removes its own entry first, and a return of a
lease that holds nothing changes nothing. Consumer: the public law, along a run. It establishes
nothing about a program, and no progress of a waiter. -/
@[semantics "store-typing" (requirement := R4)]
theorem profile_closed (s : State) (op : Op) (h : Profile s) : Profile (step s op) := by
  cases op with
  | lease id => exact lease_profile h id
  | giveBack item l => exact giveBack_profile h item l
  | select count => exact select_profile h count
  | withdraw id => exact withdraw_profile h id
  | close => exact close_profile h
  | drain id => exact drain_profile h id

/-! ## The pool as it is made -/

theorem itemsFrom_stamps : ∀ (stamp : Nat) (resources : List Nat),
    (itemsFrom stamp resources).map (·.stamp) = List.range' stamp resources.length
  | _, [] => rfl
  | stamp, _ :: rest => by
    show stamp :: (itemsFrom (stamp + 1) rest).map (·.stamp) = _
    rw [itemsFrom_stamps (stamp + 1) rest]
    rfl

theorem itemsFrom_idle : ∀ (stamp : Nat) (resources : List Nat),
    ∀ it ∈ itemsFrom stamp resources, it.borrowed = false
  | _, [], _, member => absurd member List.not_mem_nil
  | stamp, _ :: rest, it, member => by
    rcases List.mem_cons.mp member with rfl | tail
    · rfl
    · exact itemsFrom_idle (stamp + 1) rest it tail

/-- Each item's stamp is at or after the first stamp. -/
theorem itemsFrom_from : ∀ (stamp : Nat) (resources : List Nat),
    ∀ it ∈ itemsFrom stamp resources, stamp ≤ it.stamp
  | _, [], _, member => absurd member List.not_mem_nil
  | stamp, _ :: rest, it, member => by
    rcases List.mem_cons.mp member with rfl | tail
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (itemsFrom_from (stamp + 1) rest it tail)

/-- The stamps of a pool as it is made are distinct. -/
theorem itemsFrom_nodup : ∀ (stamp : Nat) (resources : List Nat),
    ((itemsFrom stamp resources).map (·.stamp)).Nodup
  | _, [] => List.Pairwise.nil
  | stamp, _ :: rest => by
    show (stamp :: (itemsFrom (stamp + 1) rest).map (·.stamp)).Nodup
    refine List.nodup_cons.mpr ⟨fun inside => ?_, itemsFrom_nodup (stamp + 1) rest⟩
    obtain ⟨it, member, same⟩ := List.mem_map.mp inside
    have bound := itemsFrom_from (stamp + 1) rest it member
    rw [same] at bound
    exact Nat.not_succ_le_self stamp bound

/-- Among items that no lease holds, no two leases share a stamp. -/
theorem apart_of_idle : ∀ {items : List Item}, (∀ it ∈ items, it.borrowed = false) →
    items.Pairwise fun a b => a.borrowed = true → b.borrowed = true → a.lease ≠ b.lease
  | [], _ => List.Pairwise.nil
  | x :: xs, idle => by
    refine List.pairwise_cons.mpr ⟨fun b _ heldX => ?_, apart_of_idle fun it member =>
      idle it (List.mem_cons_of_mem x member)⟩
    rw [idle x List.mem_cons_self] at heldX
    exact Bool.noConfusion heldX

/-- The idle stamps of a pool as it is made are the numbers below its size, in order: each
resource has the stamp of its position. -/
theorem initial_available (resources : List Nat) :
    (initial resources).available = List.range resources.length := by
  show (itemsFrom 0 resources).map (·.stamp) = _
  rw [itemsFrom_stamps, List.range_eq_range']

/-- The pool as it is made is of the profile, at every list of resources. -/
theorem initial_profile (resources : List Nat) : Profile (initial resources) where
  stamps := itemsFrom_nodup 0 resources
  idle := by
    intro i member
    obtain ⟨it, inside, rfl⟩ := List.mem_map.mp member
    exact ⟨it, inside, rfl, itemsFrom_idle 0 resources it inside⟩
  unheld := fun it inside _ => List.mem_map.mpr ⟨it, inside, rfl⟩
  once := itemsFrom_nodup 0 resources
  apart := apart_of_idle (itemsFrom_idle 0 resources)
  below := by
    intro it inside held
    rw [itemsFrom_idle 0 resources it inside] at held
    exact Bool.noConfusion held
  distinct := List.Pairwise.nil

/-! ## The fixed size: no transition adds or removes an item -/

/-- **The items are fixed** (decisions row 267): no transition adds an item, removes one or
changes a resource. So a return finalizes nothing, and no acquisition runs after the pool is
made. -/
theorem step_items (s : State) (op : Op) :
    (step s op).items.map (fun it => (it.stamp, it.resource)) =
      s.items.map (fun it => (it.stamp, it.resource)) := by
  cases op with
  | lease id =>
    show (lease s id).1.items.map _ = _
    unfold lease
    split
    · rfl
    · split
      · rfl
      · exact map_keeps fun it => by split <;> rfl
  | giveBack item l =>
    show (giveBack s item l).1.items.map _ = _
    unfold giveBack
    split
    · exact map_keeps fun it => by split <;> rfl
    · rfl
  | select count => rfl
  | withdraw id => rfl
  | close => rfl
  | drain id =>
    show (drain s id).1.items.map _ = _
    unfold drain
    split
    · rfl
    · rfl

/-! ## The enrolment rule -/

/-- On a state of the profile, no stamp is idle exactly when a lease holds every item. -/
theorem Profile.none_idle_iff {s : State} (h : Profile s) :
    s.available = [] ↔ ∀ it ∈ s.items, it.borrowed = true := by
  constructor
  · intro none it inside
    cases held : it.borrowed with
    | true => rfl
    | false =>
      have isIdle := h.unheld it inside held
      rw [none] at isIdle
      exact absurd isIdle List.not_mem_nil
  · intro all
    cases front : s.available with
    | nil => rfl
    | cons i rest =>
      obtain ⟨it, inside, -, idleNow⟩ := h.idle i (by rw [front]; exact List.mem_cons_self)
      rw [all it inside] at idleNow
      exact Bool.noConfusion idleNow

/-- A lease that does not enrol leaves the waiters without its request. -/
theorem lease_waiters (s : State) (id : Nat) :
    (lease s id).1.waiters =
      if s.closing = false ∧ s.available = [] then without s.waiters id ++ [id]
      else without s.waiters id := by
  unfold lease
  cases closed : s.closing with
  | true =>
    rw [if_pos rfl, if_neg fun both => Bool.noConfusion both.1]
    rfl
  | false =>
    rw [if_neg Bool.false_ne_true]
    cases front : s.available with
    | nil => rw [if_pos ⟨rfl, rfl⟩]
    | cons i rest => rw [if_neg fun both => List.cons_ne_nil i rest both.2]

/-- **The enrolment rule.** Lease or enrol adds a waiter only when the pool is open and no
item is idle: on a state of the profile, the request is enrolled after the step exactly when
the pool is open and a lease holds every item. The request's own entry leaves first, so an
entry after the step is this step's enrolment. Consumers: the lease step's agreement, and then
the public waiting wrapper. It is a fact of this one transition. It states no fairness and no
liveness, and nothing about a later selection. -/
@[semantics "store-typing" (requirement := R4)]
theorem lease_enrols_iff {s : State} (h : Profile s) (id : Nat) :
    id ∈ (lease s id).1.waiters ↔ s.closing = false ∧ ∀ it ∈ s.items, it.borrowed = true := by
  rw [lease_waiters, ← h.none_idle_iff]
  by_cases enrols : s.closing = false ∧ s.available = []
  · rw [if_pos enrols]
    exact ⟨fun _ => enrols, fun _ => List.mem_append_right _ List.mem_cons_self⟩
  · rw [if_neg enrols]
    exact ⟨fun member => absurd rfl (mem_without.mp member).2, fun both => absurd both enrols⟩

/-- A lease that enrols changes the waiters alone, and it answers neither a refusal nor an
item. -/
theorem lease_enrolled {s : State} {id : Nat} (enrolled : id ∈ (lease s id).1.waiters) :
    lease s id = ({ s with waiters := without s.waiters id ++ [id] }, false, none) := by
  rw [lease_waiters] at enrolled
  by_cases enrols : s.closing = false ∧ s.available = []
  · unfold lease
    rw [enrols.1, if_neg Bool.false_ne_true, enrols.2]
  · rw [if_neg enrols] at enrolled
    exact absurd rfl (mem_without.mp enrolled).2

/-! ## One selection -/

/-- **A selection takes the first waiters of the state that it finds, at most its count, and
exactly those.** The selected identities are a prefix of the waiters, in the order of
enrolment. They are as many as the count, or every waiter where fewer wait. They leave the
list, and nothing else changes: a wake reserves nothing. Consumer: the proposed claim
`pool-wake-selection`. It states one selection, and nothing about a run. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem select_takes_first (s : State) (count : Nat) :
    (select s count).2 ++ (select s count).1.waiters = s.waiters ∧
      (select s count).2.length = min count s.waiters.length ∧
      (select s count).1 = { s with waiters := s.waiters.drop count } :=
  ⟨List.take_append_drop count s.waiters, List.length_take, rfl⟩

/-! ## A return -/

/-- After a return, the lease holds no item. -/
theorem freed_not_held (items : List Item) (i l : Nat) :
    (freed items i l).any (·.heldBy i l) = false := by
  unfold freed
  rw [List.any_map]
  refine List.any_eq_false.mpr fun it _ => ?_
  show ¬ (if it.heldBy i l = true then { it with borrowed := false } else it).heldBy i l = true
  by_cases holds : it.heldBy i l = true
  · rw [if_pos holds]
    intro again
    exact Bool.noConfusion (heldBy_iff.mp again).2.1
  · rw [if_neg holds]
    exact holds

/-- **A return puts its item at the front, and it keeps every item.** Where the lease holds
the item, the item's stamp joins the front of the idle stamps, the lease returned, and a wake
is owed exactly when a waiter is enrolled. Every item stays, with its resource: a return
finalizes nothing. After it the lease holds no item. Consumer: the proposed claim
`pool-lease-return`. It states one transition, and nothing about a finalizer's run. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem giveBack_front {s : State} {i l : Nat} (held : s.items.any (·.heldBy i l) = true) :
    (giveBack s i l).1.available = i :: s.available ∧
      (giveBack s i l).2 = (true, !s.waiters.isEmpty) ∧
      (giveBack s i l).1.items.map (fun it => (it.stamp, it.resource)) =
        s.items.map (fun it => (it.stamp, it.resource)) ∧
      (giveBack s i l).1.items.any (·.heldBy i l) = false := by
  unfold giveBack
  rw [if_pos held]
  exact ⟨rfl, rfl, map_keeps fun it => by split <;> rfl, freed_not_held s.items i l⟩

/-- A return of a lease that holds nothing changes nothing, and it owes no wake. -/
theorem giveBack_stale {s : State} {i l : Nat} (none : s.items.any (·.heldBy i l) = false) :
    giveBack s i l = (s, false, false) := by
  unfold giveBack
  rw [if_neg (by rw [none]; exact Bool.false_ne_true)]

/-- **A lease returns at most once.** After a return of a lease, a second return of the same
lease changes nothing and owes no wake, whatever the first one did. Consumer: the proposed
claim `pool-lease-return`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem giveBack_once (s : State) (i l : Nat) :
    giveBack (giveBack s i l).1 i l = ((giveBack s i l).1, false, false) := by
  refine giveBack_stale ?_
  by_cases held : s.items.any (·.heldBy i l) = true
  · exact (giveBack_front held).2.2.2
  · rw [Bool.not_eq_true] at held
    rw [giveBack_stale held]
    exact held

/-! ## The close's first step -/

/-- At a closing pool a lease is refused: the request's entry leaves, and nothing else
changes. -/
theorem lease_closed {s : State} (closed : s.closing = true) (id : Nat) :
    lease s id = (withdraw s id, true, none) := by
  unfold lease
  rw [if_pos closed]

/-- No transition opens a closing pool. -/
theorem step_closing (s : State) (op : Op) (closed : s.closing = true) :
    (step s op).closing = true := by
  cases op with
  | lease id =>
    show (lease s id).1.closing = true
    rw [lease_closed closed]
    exact closed
  | giveBack item l =>
    show (giveBack s item l).1.closing = true
    unfold giveBack
    split
    · exact closed
    · exact closed
  | select count => exact closed
  | withdraw id => exact closed
  | close => rfl
  | drain id =>
    show (drain s id).1.closing = true
    unfold drain
    split
    · exact closed
    · exact closed

/-- **After the close's first step no lease begins.** The step leaves a closing pool, it tells
whether it began the close, and its count is the count of the waiters. At a closing pool every
lease is refused, and a refused lease changes no item, no idle stamp and no stamp of a lease.
No transition opens the pool again (`step_closing`). Consumer: the proposed claim
`pool-close-waits`. It states no wait for a lease, no finalizer's run and no completed
close. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem close_refuses (s : State) :
    (close s).1.closing = true ∧ (close s).2 = (!s.closing, s.waiters.length) ∧
      ∀ id, lease (close s).1 id = (withdraw (close s).1 id, true, none) :=
  ⟨rfl, rfl, fun id => lease_closed rfl id⟩

/-! ## The closer's step -/

/-- The borrowed items of a list are none exactly where no item is borrowed. The proof follows
the list: the core lemma of `filter` at the empty list, `List.filter_eq_nil_iff`, reaches
`Classical.choice` (measured at Lean v4.33.1). -/
theorem borrowed_nil_iff : ∀ (items : List Item),
    ((items.filter (·.borrowed)).map fun it => (it.stamp, it.lease)) = [] ↔
      items.any (·.borrowed) = false
  | [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | x :: xs => by
    cases held : x.borrowed with
    | true =>
      rw [List.filter_cons_of_pos held, List.map_cons, List.any_cons, held, Bool.true_or]
      exact ⟨fun wrong => absurd wrong (List.cons_ne_nil _ _),
        fun wrong => Bool.noConfusion wrong⟩
    | false =>
      rw [List.filter_cons_of_neg (by rw [held]; exact Bool.false_ne_true), List.any_cons, held,
        Bool.false_or]
      exact borrowed_nil_iff xs

/-- No lease is outstanding exactly where no item is borrowed. -/
theorem leases_nil_iff (s : State) : leases s = [] ↔ s.items.any (·.borrowed) = false :=
  borrowed_nil_iff s.items

/-- Where a lease is outstanding, the closer's step enrols the closer, and it answers false. -/
theorem drain_enrols {s : State} (id : Nat) (held : s.items.any (·.borrowed) = true) :
    drain s id = ({ s with waiters := without s.waiters id ++ [id] }, false) := by
  unfold drain
  rw [if_pos held]

/-- Where no lease is outstanding, the closer's step answers true, and no entry of the closer
stays. -/
theorem drain_drained {s : State} (id : Nat) (none : s.items.any (·.borrowed) = false) :
    drain s id = (withdraw s id, true) := by
  unfold drain
  rw [if_neg (by rw [none]; exact Bool.false_ne_true)]

/-- **The closer's step answers true exactly where no lease is outstanding** (decisions rows
268 and 276, point 2). It enrols the closer exactly otherwise: the closer's own entry leaves
first, so an entry after the step is this step's enrolment. The check and the enrolment are one
transition, so each later return finds a waiter. The step changes the waiters alone: it frees no
item, and it finalizes none. Consumer: the proposed claim `pool-close-waits`. It states one
transition. It states no wait along a run, no progress of the closer and no finalizer's run. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem drain_waits (s : State) (id : Nat) :
    ((drain s id).2 = true ↔ leases s = []) ∧
      (id ∈ (drain s id).1.waiters ↔ leases s ≠ []) ∧
      (drain s id).1 = { s with waiters := (drain s id).1.waiters } := by
  cases held : s.items.any (·.borrowed) with
  | true =>
    have some : leases s ≠ [] := fun none => by
      rw [(leases_nil_iff s).mp none] at held
      exact Bool.false_ne_true held
    rw [drain_enrols id held]
    exact ⟨⟨fun wrong => absurd wrong Bool.false_ne_true, fun none => absurd none some⟩,
      ⟨fun _ => some, fun _ => List.mem_append_right _ List.mem_cons_self⟩, rfl⟩
  | false =>
    have none : leases s = [] := (leases_nil_iff s).mpr held
    rw [drain_drained id held]
    exact ⟨⟨fun _ => none, fun _ => rfl⟩,
      ⟨fun member => absurd rfl (mem_without.mp member).2, fun some => absurd none some⟩, rfl⟩

/-! ## The predicate decides -/

instance (s : State) : Decidable (Profile s) :=
  decidable_of_iff
    ((s.items.map (·.stamp)).Nodup ∧
      (∀ i ∈ s.available, ∃ it ∈ s.items, it.stamp = i ∧ it.borrowed = false) ∧
      (∀ it ∈ s.items, it.borrowed = false → it.stamp ∈ s.available) ∧ s.available.Nodup ∧
      (s.items.Pairwise fun a b => a.borrowed = true → b.borrowed = true → a.lease ≠ b.lease) ∧
      (∀ it ∈ s.items, it.borrowed = true → it.lease < s.next) ∧ s.waiters.Nodup)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
      fun h => ⟨h.stamps, h.idle, h.unheld, h.once, h.apart, h.below, h.distinct⟩⟩

end Effect4.Pool.Model

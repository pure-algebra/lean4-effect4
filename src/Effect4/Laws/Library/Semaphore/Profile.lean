import Effect4.Library.Semaphore.Model
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Semaphore's first profile: its states, their closure, and two facts of a visit

`Profile` is the predicate of the first profile's states (decisions rows 259 to 261): the
accounting, the stamps and the identities of the waiters. `profile_closed`: each transition of
the model (`src/Effect4/Library/Semaphore/Model.lean`) keeps the predicate, with no
premise on its request. No term, no cell and no machine occurs in this file.

| Statement | What it says |
| --- | --- |
| `profile_closed` | each of the five transitions keeps the profile |
| `step_permits` | no transition changes the total |
| `initial_profile` | the semaphore as it is made is of the profile |
| `visit_selects_earliest` | a visit selects the earliest fitting waiter at or after its cursor, and that waiter leaves |
| `visit_stops_iff` | a visit selects nobody exactly when no permit is free or no such waiter fits, and then nothing changes |
| `visit_reserves_nothing` | a visit keeps the total, what is taken and the next stamp |

Placement.

- **The closure.** Concept `store-typing`, requirement R4: the model's half of the proposed
  claim `semaphore-accounting-preserved`. Consumer: the public law, along a run. Reach: every
  transition of the model, on the profile's states. It establishes nothing about a program,
  and no progress of a waiter.
- **The two facts of a visit.** Concept `reactive-scheduling`, requirement R12. Consumer: the
  waiting clauses of the proposed claim `semaphore-expansion-agrees` (requirement R10). Reach:
  one visit of the model. They state nothing about a whole walk, and no liveness: a waiter that
  no visit selects stays, and no statement here says that some visit selects it.

The pinned axiom and plan outputs and the finite controls are in
`Test/Program/SemaphoreContract.lean`.
-/

set_option autoImplicit false

namespace Effect4.Semaphore.Model

/-- **The states of the first profile.** Three parts: the accounting, the stamps and the
identities. -/
structure Profile (s : State) : Prop where
  /-- The accounting: no more is taken than the total. -/
  bounded : s.taken ≤ s.permits
  /-- The stamps rise along the list: the list is in the order of enrolment. -/
  rising : s.waiters.Pairwise (fun a b => a.stamp < b.stamp)
  /-- Each stamp is below the stamp of the next enrolment. -/
  below : ∀ w ∈ s.waiters, w.stamp < s.next
  /-- No two waiters share an identity. -/
  distinct : (s.waiters.map (·.id)).Nodup

/-! ## The removal by identity -/

theorem mem_without {w : Waiter} {waiters : List Waiter} {id : Nat} :
    w ∈ without waiters id ↔ w ∈ waiters ∧ w.id ≠ id := by
  unfold without
  rw [List.mem_filter, bne_iff_ne]

theorem without_sublist (waiters : List Waiter) (id : Nat) :
    (without waiters id).Sublist waiters :=
  List.filter_sublist

/-! ## Two ways a transition changes a state -/

/-- A state with the same total, no more taken than the total, a sublist of the waiters and a
next stamp that did not fall is of the profile. -/
theorem Profile.shrink {s s' : State} (h : Profile s) (permits : s'.permits = s.permits)
    (bounded : s'.taken ≤ s.permits) (waiters : s'.waiters.Sublist s.waiters)
    (next : s.next ≤ s'.next) : Profile s' where
  bounded := by
    rw [permits]
    exact bounded
  rising := h.rising.sublist waiters
  below := fun w member => Nat.lt_of_lt_of_le (h.below w (waiters.subset member)) next
  distinct := h.distinct.sublist (waiters.map _)

/-- A request enrols at the list's end, at the next stamp, after its own entry left. -/
theorem Profile.enrol {s : State} (h : Profile s) (id n : Nat) :
    Profile
      { s with waiters := without s.waiters id ++ [⟨id, n, s.next⟩], next := s.next + 1 } where
  bounded := h.bounded
  rising := by
    show (without s.waiters id ++ [(⟨id, n, s.next⟩ : Waiter)]).Pairwise _
    refine List.pairwise_append.mpr
      ⟨h.rising.sublist (without_sublist _ _), List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton.mp hb]
    exact h.below a (mem_without.mp ha).1
  below := fun w member => by
    rcases List.mem_append.mp member with old | new
    · exact Nat.lt_succ_of_lt (h.below w (mem_without.mp old).1)
    · rw [List.mem_singleton.mp new]
      exact Nat.lt_succ_self _
  distinct := by
    show ((without s.waiters id ++ [(⟨id, n, s.next⟩ : Waiter)]).map (·.id)).Nodup
    rw [List.map_append]
    refine List.pairwise_append.mpr
      ⟨h.distinct.sublist ((without_sublist _ _).map _), List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    obtain ⟨w, member, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_singleton.mp hb]
    exact (mem_without.mp member).2

/-! ## The five transitions -/

theorem take_profile {s : State} (h : Profile s) (id n : Nat) : Profile (take s id n).1 := by
  unfold take
  split
  · next fitsNow =>
    refine h.shrink rfl ?_ (without_sublist _ _) (Nat.le_refl _)
    have room : n ≤ s.permits - s.taken := fitsNow
    have bounded := h.bounded
    show s.taken + n ≤ s.permits
    omega
  · exact h.enrol id n

theorem takeIfAvailable_profile {s : State} (h : Profile s) (n : Nat) :
    Profile (takeIfAvailable s n).1 := by
  unfold takeIfAvailable
  split
  · next fitsNow =>
    refine h.shrink rfl ?_ (List.Sublist.refl _) (Nat.le_refl _)
    have room : n ≤ s.permits - s.taken := fitsNow
    have bounded := h.bounded
    show s.taken + n ≤ s.permits
    omega
  · exact h

theorem release_profile {s : State} (h : Profile s) (n : Nat) : Profile (release s n).1 :=
  h.shrink rfl (Nat.le_trans (Nat.sub_le _ _) h.bounded) (List.Sublist.refl _) (Nat.le_refl _)

theorem visit_profile {s : State} (h : Profile s) (cursor : Nat) :
    Profile (visit s cursor).1 := by
  unfold visit
  split
  · exact h
  · split
    · exact h
    · exact h.shrink rfl h.bounded List.erase_sublist (Nat.le_refl _)

theorem withdraw_profile {s : State} (h : Profile s) (id : Nat) : Profile (withdraw s id) :=
  h.shrink rfl h.bounded (without_sublist _ _) (Nat.le_refl _)

/-! ## The closure -/

/-- **The first profile is closed.** Each transition of the model leaves a state of the
profile. No premise names the request: a take removes its own entry first, and a release is
total. Consumer: the public law, along a run. It establishes nothing about a program, and no
progress of a waiter. -/
@[semantics "store-typing" (requirement := R4)]
theorem profile_closed (s : State) (op : Op) (h : Profile s) : Profile (step s op) := by
  cases op with
  | take id n => exact take_profile h id n
  | takeIfAvailable n => exact takeIfAvailable_profile h n
  | release n => exact release_profile h n
  | visit cursor => exact visit_profile h cursor
  | withdraw id => exact withdraw_profile h id

/-- **The total is fixed** (decisions row 260): no transition changes it. -/
theorem step_permits (s : State) (op : Op) : (step s op).permits = s.permits := by
  cases op with
  | take id n =>
    show (take s id n).1.permits = s.permits
    unfold take
    split <;> rfl
  | takeIfAvailable n =>
    show (takeIfAvailable s n).1.permits = s.permits
    unfold takeIfAvailable
    split <;> rfl
  | release n => rfl
  | visit cursor =>
    show (visit s cursor).1.permits = s.permits
    unfold visit
    split
    · rfl
    · split <;> rfl
  | withdraw id => rfl

/-- The semaphore as it is made is of the profile, at every total. -/
theorem initial_profile (permits : Nat) : Profile (initial permits) where
  bounded := Nat.zero_le _
  rising := List.Pairwise.nil
  below := fun _ member => absurd member List.not_mem_nil
  distinct := List.Pairwise.nil

/-! ## One visit, in its three forms -/

/-- A visit where no permit is free. -/
theorem visit_none_free {s : State} (cursor : Nat) (noneFree : free s = 0) :
    visit s cursor = (s, none) := by
  unfold visit
  rw [if_pos noneFree]

/-- A visit where a permit is free and no waiter at or after the cursor fits. -/
theorem visit_none_fits {s : State} {cursor : Nat} (someFree : free s ≠ 0)
    (found : s.waiters.find? (fits cursor (free s)) = none) : visit s cursor = (s, none) := by
  unfold visit
  rw [if_neg someFree, found]

/-- A visit that selects a waiter. -/
theorem visit_some {s : State} {cursor : Nat} {w : Waiter} (someFree : free s ≠ 0)
    (found : s.waiters.find? (fits cursor (free s)) = some w) :
    visit s cursor = ({ s with waiters := s.waiters.erase w }, some w) := by
  unfold visit
  rw [if_neg someFree, found]

theorem fits_iff {cursor free : Nat} {w : Waiter} :
    fits cursor free w = true ↔ cursor ≤ w.stamp ∧ w.need ≤ free := by
  unfold fits
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]

/-! ## The two facts of a visit -/

/-- **A visit resumes the earliest fitting waiter at or after its cursor.** On a profile
state, the selected waiter is enrolled, its stamp is at or after the cursor, and its count fits
the free count. Its stamp is the least among the waiters that are at or after the cursor and
fit. The selected waiter leaves the list, and nothing else changes. Consumer: the waiting
clauses of the proposed claim `semaphore-expansion-agrees`. It states one visit, and nothing
about a whole walk. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem visit_selects_earliest {s : State} (h : Profile s) {cursor : Nat} {w : Waiter}
    (selected : (visit s cursor).2 = some w) :
    w ∈ s.waiters ∧ cursor ≤ w.stamp ∧ w.need ≤ free s ∧
      (∀ u ∈ s.waiters, cursor ≤ u.stamp → u.need ≤ free s → w.stamp ≤ u.stamp) ∧
      (visit s cursor).1 = { s with waiters := s.waiters.erase w } := by
  by_cases noneFree : free s = 0
  · rw [visit_none_free cursor noneFree] at selected
    cases selected
  · cases found : s.waiters.find? (fits cursor (free s)) with
    | none =>
      rw [visit_none_fits noneFree found] at selected
      cases selected
    | some v =>
      rw [visit_some noneFree found] at selected ⊢
      obtain rfl : v = w := Option.some.inj selected
      obtain ⟨atCursor, fitsNow⟩ := fits_iff.mp (List.find?_some found)
      obtain ⟨-, before, after, split, passed⟩ := List.find?_eq_some_iff_append.mp found
      refine ⟨List.mem_of_find?_eq_some found, atCursor, fitsNow, ?_, rfl⟩
      intro u member uAtCursor uFits
      rw [split] at member
      rcases List.mem_append.mp member with early | late
      · have refused : (!fits cursor (free s) u) = true := passed u early
        rw [fits_iff.mpr ⟨uAtCursor, uFits⟩] at refused
        cases refused
      · rcases List.mem_cons.mp late with same | later
        · rw [same]
          exact Nat.le_refl _
        · have rising := h.rising
          rw [split] at rising
          exact Nat.le_of_lt
            ((List.pairwise_cons.mp (List.pairwise_append.mp rising).2.1).1 u later)

/-- **A visit stops only when no permit is free or no such waiter fits.** A visit selects
nobody exactly when the free count is zero, or each waiter at or after the cursor needs more
than the free count. It then changes nothing. Consumer: the waiting clauses of the proposed
claim `semaphore-expansion-agrees`. It states one visit, and no liveness. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem visit_stops_iff (s : State) (cursor : Nat) :
    ((visit s cursor).2 = none ↔
        free s = 0 ∨ ∀ u ∈ s.waiters, cursor ≤ u.stamp → free s < u.need) ∧
      ((visit s cursor).2 = none → (visit s cursor).1 = s) := by
  by_cases noneFree : free s = 0
  · rw [visit_none_free cursor noneFree]
    exact ⟨⟨fun _ => Or.inl noneFree, fun _ => rfl⟩, fun _ => rfl⟩
  · cases found : s.waiters.find? (fits cursor (free s)) with
    | none =>
      rw [visit_none_fits noneFree found]
      refine ⟨⟨fun _ => Or.inr fun u member atCursor => ?_, fun _ => rfl⟩, fun _ => rfl⟩
      exact Nat.lt_of_not_le fun fitsNow =>
        List.find?_eq_none.mp found u member (fits_iff.mpr ⟨atCursor, fitsNow⟩)
    | some v =>
      rw [visit_some noneFree found]
      obtain ⟨atCursor, fitsNow⟩ := fits_iff.mp (List.find?_some found)
      refine ⟨⟨fun stopped => absurd stopped (Option.some_ne_none v), fun reason => ?_⟩,
        fun stopped => absurd stopped (Option.some_ne_none v)⟩
      rcases reason with zero | none
      · exact absurd zero noneFree
      · exact absurd fitsNow
          (Nat.not_le_of_lt (none v (List.mem_of_find?_eq_some found) atCursor))

/-- **A wake reserves nothing** (decisions row 259): a visit keeps the total, what is taken and
the next stamp. A permit commits in the waiter's own take. -/
theorem visit_reserves_nothing (s : State) (cursor : Nat) :
    (visit s cursor).1.permits = s.permits ∧ (visit s cursor).1.taken = s.taken ∧
      (visit s cursor).1.next = s.next := by
  unfold visit
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl⟩

/-! ## The predicate decides -/

instance (s : State) : Decidable (Profile s) :=
  decidable_of_iff
    (s.taken ≤ s.permits ∧ s.waiters.Pairwise (fun a b => a.stamp < b.stamp) ∧
      (∀ w ∈ s.waiters, w.stamp < s.next) ∧ (s.waiters.map (·.id)).Nodup)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
      fun h => ⟨h.bounded, h.rising, h.below, h.distinct⟩⟩

end Effect4.Semaphore.Model

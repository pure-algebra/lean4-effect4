import Effect4.Laws.Modules.Queue.Model
import Effect4.Laws.Auto.Semantics

/-!
# The Queue's abstract capacity invariant (decisions rows 219, 233 and 255)

`positive_suspend_step_capacity`: one abstract step of the first profile keeps the configuration
and the buffer's bound. Its steps are `acceptLoop_length_le`, through `accept` and
`afterConsume`, and one lemma for each operation of the model
(`src/Effect4/Laws/Modules/Queue/Model.lean`). `acceptLoop_length_le` says that pending offers
add at most the finite room to the buffer.

Placement. Concept `reactive-scheduling`. Requirement R10, as a helper of the proposed claim
`queue-expansion-agrees`, on the side of its abstract client. Consumer: the later refinement from
the Queue's `Ref.modify` term to the abstract step. The statements are about lengths in the
natural-number model. They establish no typed store preservation, no signal delivery, no order of
service, no cancellation law and no agreement with a target.

Codex prepared the statements and the proof's route (the packet `Test/contracts/queue.contract.md`).
The coordinator compiled them on 2026-10-05, rewrote the helper's proof and proved the step's
statement. The step's proof does not use its premise of a positive capacity: the bound holds at
capacity zero too. The premise stays in the statement, which the packet froze. The pinned axiom
and plan outputs and the finite controls are in `Test/Program/QueueCapacity.lean`.
-/

namespace Effect4.Queue.Model

/-- Pending offers add at most the finite room to the buffer.
A helper of `positive_suspend_step_capacity`, through `accept` and `afterConsume`.
The statement concerns lengths, not request identities, signal delivery or store membership. -/
@[semantics "reactive-scheduling" (requirement := R10)]
theorem acceptLoop_length_le (r : Nat) (ms : List Nat) (os : List Offer) :
    (acceptLoop (some r) ms os).1.length ≤ ms.length + r := by
  induction os generalizing r ms with
  | nil =>
    simp only [acceptLoop]
    omega
  | cons o os ih =>
    rw [acceptLoop]
    by_cases hr : (some r : Option Nat) = some 0
    · rw [if_pos hr]
      exact Nat.le_add_right _ _
    · rw [if_neg hr]
      dsimp only
      have hfit : fit (some r) o.rest.length ≤ r := Nat.min_le_left r o.rest.length
      generalize fit (some r) o.rest.length = k at hfit ⊢
      have takeBound := List.length_take_le k o.rest
      by_cases hl : (List.drop k o.rest).isEmpty = true
      · rw [if_pos hl]
        dsimp only [Option.map_some]
        have bound := ih (r - k) (ms ++ o.rest.take k)
        rw [List.length_append] at bound
        omega
      · rw [if_neg hl, List.length_append]
        omega

/-! ## One step keeps the configuration and the bound

Each lemma of this section is a step of `positive_suspend_step_capacity`, its one consumer: an
operation of the model keeps `Kept c`. -/

/-- What one step keeps: the capacity `c`, the `suspend` strategy, and a buffer inside the
bound. -/
abbrev Kept (c : Nat) (s : State) : Prop :=
  s.capacity = some c ∧ s.strategy = .suspend ∧ s.messages.length ≤ c

theorem room_of {c : Nat} {s : State} (h : Kept c s) :
    room s = some (c - s.messages.length) := by
  unfold room
  rw [h.1]
  rfl

theorem settle_kept {c : Nat} {s : State} (h : Kept c s) : Kept c (settle s).1 := by
  unfold settle
  split
  · split
    · exact h
    · exact h
  · exact h

theorem accept_kept {c : Nat} {s : State} (h : Kept c s) : Kept c (accept s).1 := by
  refine ⟨h.1, h.2.1, ?_⟩
  show (acceptLoop (room s) s.messages s.offers).1.length ≤ c
  have bound := acceptLoop_length_le (c - s.messages.length) s.messages s.offers
  have within := h.2.2
  rw [room_of h]
  omega

theorem afterConsume_kept {c : Nat} {s : State} (h : Kept c s) : Kept c (afterConsume s).1 :=
  settle_kept (accept_kept h)

theorem pull_kept {c : Nat} {s : State} (max : Nat) (h : Kept c s) :
    Kept c (pull s max).2.1 := by
  unfold pull
  split
  · split
    · split
      · split
        · exact h
        · exact h
      · exact h
    · exact h
  · refine ⟨h.1, h.2.1, ?_⟩
    show (s.messages.drop max).length ≤ c
    have within := h.2.2
    rw [List.length_drop]
    omega

theorem take_kept {c : Nat} {s : State} (t : Taker) (h : Kept c s) : Kept c (take s t).1 := by
  unfold take
  split
  · exact h
  · split
    · exact h
    · split
      · exact afterConsume_kept (pull_kept t.max (show Kept c (removeTaker s t.id) from h))
      · split
        · exact h
        · exact h

theorem poll_kept {c : Nat} {s : State} (h : Kept c s) : Kept c (poll s).1 := by
  unfold poll
  split
  · exact h
  · exact afterConsume_kept (pull_kept 1 h)

theorem clear_kept {c : Nat} {s : State} (h : Kept c s) : Kept c (clear s).1 := by
  unfold clear
  split
  · exact h
  · exact h
  · split
    · exact h
    · exact afterConsume_kept (pull_kept s.messages.length h)

theorem peek_kept {c : Nat} {s : State} (id : Nat) (h : Kept c s) : Kept c (peek s id).1 := by
  unfold peek
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · exact h

/-- An offer enters the buffer only into room. The other strategies' arms keep the state, or are
not this configuration's. -/
theorem offer_kept {c : Nat} {s : State} (id a : Nat) (h : Kept c s) :
    Kept c (offer s id a).1 := by
  unfold offer
  split
  · exact h
  · split
    · exact h
    · split
      · next hasRoom_s =>
        refine ⟨h.1, h.2.1, ?_⟩
        show (s.messages ++ [a]).length ≤ c
        have free : 0 < c - s.messages.length := by
          unfold hasRoom at hasRoom_s
          rw [room_of h] at hasRoom_s
          exact of_decide_eq_true hasRoom_s
        rw [List.length_append, List.length_singleton]
        omega
      · split
        · exact h
        · next sliding => exact absurd (h.2.1.symm.trans sliding) (by decide)
        · exact h

/-- A batch enters the buffer as far as the room goes. -/
theorem offerAll_kept {c : Nat} {s : State} (id : Nat) (ms : List Nat) (h : Kept c s) :
    Kept c (offerAll s id ms).1 := by
  have fits : (s.messages ++ ms.take (fit (room s) ms.length)).length ≤ c := by
    rw [room_of h, List.length_append]
    have taken := List.length_take_le (fit (some (c - s.messages.length)) ms.length) ms
    have fitted : fit (some (c - s.messages.length)) ms.length ≤ c - s.messages.length :=
      Nat.min_le_left _ _
    have within := h.2.2
    omega
  unfold offerAll
  split
  · exact h
  · split
    · exact h
    · split
      · next sliding => exact absurd (h.2.1.symm.trans sliding) (by decide)
      · next dropping => exact absurd (h.2.1.symm.trans dropping) (by decide)
      · split
        · exact h
        · dsimp only
          split
          · exact ⟨h.1, h.2.1, fits⟩
          · exact ⟨h.1, h.2.1, fits⟩

theorem close_kept {c : Nat} {s : State} (e : End) (h : Kept c s) : Kept c (close s e).1 := by
  unfold close
  split
  · exact h
  · exact settle_kept (s := { s with phase := .closing e }) h

theorem shutdown_kept {c : Nat} {s : State} (h : Kept c s) : Kept c (shutdown s).1 := by
  unfold shutdown
  split
  · exact h
  · exact ⟨h.1, h.2.1, Nat.zero_le c⟩

theorem awaitQ_kept {c : Nat} {s : State} (id : Nat) (h : Kept c s) :
    Kept c (awaitQ s id).1 := by
  unfold awaitQ
  split
  · exact h
  · split
    · exact h
    · exact h

theorem withdrawOffer_kept {c : Nat} {s : State} (id : Nat) (h : Kept c s) :
    Kept c (withdrawOffer s id).1 := by
  unfold withdrawOffer
  split
  · exact h
  · exact settle_kept (s := { s with offers := s.offers.filter (fun o => o.id != id) }) h

/-- Abstract positive-capacity suspend steps keep the configuration and buffer bound.
Consumer: the later Queue term-to-model refinement. No wrapper or host claim. The proof does not
use `_hpos`. -/
@[semantics "reactive-scheduling" (requirement := R10)]
theorem positive_suspend_step_capacity
    (c : Nat) (s : State) (op : Op)
    (_hpos : 0 < c) (hcap : s.capacity = some c)
    (hstrategy : s.strategy = .suspend)
    (hwithin : s.messages.length ≤ c) :
  let next := (step .none { s := s } op).s
  next.capacity = some c ∧ next.strategy = .suspend ∧ next.messages.length ≤ c := by
  intro next
  have h : Kept c s := ⟨hcap, hstrategy, hwithin⟩
  show Kept c (step .none { s := s } op).s
  cases op with
  | take id min max => exact take_kept ⟨id, min, max⟩ h
  | poll => exact poll_kept h
  | peek id => exact peek_kept id h
  | offer id a =>
    simp only [step]
    split
    · exact h
    · exact offer_kept id a h
  | offerAll id ms =>
    simp only [step]
    split
    · exact h
    · exact offerAll_kept id ms h
  | clear => exact clear_kept h
  | close e => exact close_kept e h
  | shutdown => exact shutdown_kept h
  | await id => exact awaitQ_kept id h
  | dropTake id => exact h
  | dropOffer id => exact withdrawOffer_kept id h
  | dropPeek id => exact h
  | dropAwait id => exact h

end Effect4.Queue.Model

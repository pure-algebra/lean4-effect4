import Test.Program.QueueModel
import ProofGraph.Plan
import Effect4.Laws.Auto.Semantics
import Lean.Elab.Tactic.Omega

/-!
# The Queue's abstract capacity invariant: the first general statement (decisions rows 219, 233)

`positive_suspend_step_capacity` is proved here: one abstract step of the first profile keeps the
configuration and the buffer's bound. Its steps are `acceptLoop_length_le`, through `accept` and
`afterConsume`, and one lemma for each operation of the model (`Test/Program/QueueModel.lean`).
`acceptLoop_length_le` says that pending offers add at most the finite room to the buffer.

Placement. Concept `reactive-scheduling`. Requirement R10, as a helper of the proposed claim
`queue-expansion-agrees`, on the side of its abstract client. Consumer: the later refinement from
the Queue's `Ref.modify` term to the abstract step. The statements are about lengths in the
natural-number model. They establish no typed store preservation, no signal delivery, no order of
service, no cancellation law and no agreement with a target.

Codex prepared the statements and the proof's route (the packet `Test/contracts/queue.contract.md`).
The coordinator compiled them on 2026-10-05 and rewrote the helper's proof: the draft unfolded
`fit` under the conditional's instance. The coordinator proved the step's statement the same day.

The step's proof does not use its premise of a positive capacity: the bound holds at capacity
zero too, and a control below shows one such step. The premise stays in the statement, which the
packet froze.
-/

namespace Test.Program.QueueCapacity
open QueueContract

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

/-- info: 'Test.Program.QueueCapacity.acceptLoop_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms acceptLoop_length_le

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

/-- info: 'Test.Program.QueueCapacity.positive_suspend_step_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms positive_suspend_step_capacity

/--
info: Test.Program.QueueCapacity.positive_suspend_step_capacity: proved; nearest []; 18 lemmas, 70 definitions
next goals: 0
-/
#guard_msgs in
#plan_status positive_suspend_step_capacity

/-! ## Controls of the step's statement: finite checks, one input each -/

/-- The step's conclusion on one input, as a Boolean. -/
def keeps (c : Nat) (s : State) (op : Op) : Bool :=
  let next := (step .none { s := s } op).s
  next.capacity == some c && next.strategy == .suspend && decide (next.messages.length ≤ c)

-- A take at a full buffer frees one place, and one of two pending offers enters.
#guard keeps 2
  { capacity := some 2, messages := [1, 2], offers := [⟨7, false, [3]⟩, ⟨8, false, [4]⟩] }
  (.take 1 1 1)
-- A batch enters as far as the room goes.
#guard keeps 2 { capacity := some 2, messages := [1] } (.offerAll 7 [3, 4, 5])
-- Capacity zero: the offer waits, and the buffer stays empty. The positive premise is not used.
#guard keeps 0 { capacity := some 0 } (.offer 7 5)
-- Red control: a buffer above its bound stays above it.
#guard !keeps 1 { capacity := some 1, messages := [1, 2] } (.peek 1)
-- Red control: outside `suspend`, the unformed configuration `sliding` at capacity zero grows.
#guard !keeps 0 { capacity := some 0, strategy := .sliding } (.offer 7 5)

/-! ## Controls of the helper: finite checks, one input each -/

/-- The helper's bound on one input, as a Boolean. -/
def within (r : Nat) (ms : List Nat) (os : List Offer) : Bool :=
  decide ((acceptLoop (some r) ms os).1.length ≤ ms.length + r)

-- No pending offer: the buffer is unchanged.
#guard (acceptLoop (some 3) [1] []).1 = [1] && within 3 [1] []
-- No room: nothing is accepted, and the offer stays.
#guard (acceptLoop (some 0) [1] [⟨7, false, [9]⟩]) = ([1], [⟨7, false, [9]⟩], [])
-- A part of a batch fits: the buffer takes it, and the rest stays pending.
#guard (acceptLoop (some 1) [1] [⟨7, true, [9, 8]⟩]).1 = [1, 9]
#guard (acceptLoop (some 1) [1] [⟨7, true, [9, 8]⟩]).2.1 = [⟨7, true, [8]⟩]
-- Several offers fit whole, in arrival order, and each is answered.
#guard (acceptLoop (some 3) [1] [⟨7, false, [5]⟩, ⟨8, false, [6]⟩]).1 = [1, 5, 6]
#guard (acceptLoop (some 3) [1] [⟨7, false, [5]⟩, ⟨8, false, [6]⟩]).2.2.length = 2
-- A full buffer at its bound, and the bound on each input above.
#guard within 0 [1, 2, 3] [⟨7, false, [9]⟩] && within 1 [1] [⟨7, true, [9, 8]⟩] &&
  within 3 [1] [⟨7, false, [5]⟩, ⟨8, false, [6]⟩]

/-- Red control: a loop that accepts every pending message whatever the room. -/
def acceptAll (ms : List Nat) (os : List Offer) : List Nat := ms ++ os.flatMap (·.rest)

-- It leaves the bound at room zero, where `acceptLoop` keeps it.
#guard !decide ((acceptAll [1] [⟨7, false, [9]⟩]).length ≤ [1].length + 0)

end Test.Program.QueueCapacity

import Test.Program.QueueModel
import ProofGraph.Plan
import Effect4.Laws.Auto.Semantics
import Lean.Elab.Tactic.Omega

/-!
# The Queue's abstract capacity invariant: the first general statement (decisions rows 219, 233)

`acceptLoop_length_le` is proved here: pending offers add at most the finite room to the buffer.
`positive_suspend_step_capacity` is a planned goal: one abstract step of the first profile keeps
the configuration and the buffer's bound. The helper is a step of that goal, through `accept` and
`afterConsume` (`Test/Program/QueueModel.lean`).

Placement. Concept `reactive-scheduling`. Requirement R10, as a helper of the proposed claim
`queue-expansion-agrees`, on the side of its abstract client. Consumer: the later refinement from
the Queue's `Ref.modify` term to the abstract step. The statements are about lengths in the
natural-number model. They establish no typed store preservation, no signal delivery, no order of
service, no cancellation law and no agreement with a target.

Codex prepared the statements and the proof's route (the packet `Test/contracts/queue.contract.md`).
The coordinator compiled them on 2026-10-05 and rewrote the helper's proof: the draft unfolded
`fit` under the conditional's instance.
-/

namespace Test.Program.QueueCapacity
open QueueContract

/-- Abstract positive-capacity suspend steps keep the configuration and buffer bound.
Consumer: the later Queue term-to-model refinement. No wrapper or host claim. -/
@[semantics "reactive-scheduling" (requirement := R10)]
proof_goal positive_suspend_step_capacity
    (c : Nat) (s : State) (op : Op)
    (hpos : 0 < c) (hcap : s.capacity = some c)
    (hstrategy : s.strategy = .suspend)
    (hwithin : s.messages.length ≤ c) :
  let next := (step .none { s := s } op).s
  next.capacity = some c ∧ next.strategy = .suspend ∧ next.messages.length ≤ c

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

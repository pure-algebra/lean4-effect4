import Effect4.Laws.Modules.Queue.Capacity
import ProofGraph.Plan

/-!
# The Queue's capacity statements: their pinned outputs and their finite controls

The statements and their proofs are in `src/Effect4/Laws/Modules/Queue/Capacity.lean`. This
battery pins each statement's axioms and its plan status, and holds the finite controls of the
packet `Test/contracts/queue.contract.md`, one input each.
-/

namespace Test.Program.QueueCapacity
open Effect4.Queue.Model

/-- info: 'Effect4.Queue.Model.acceptLoop_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms acceptLoop_length_le

/-- info: 'Effect4.Queue.Model.positive_suspend_step_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms positive_suspend_step_capacity

-- The standing is derived from the proof. The counts are of this battery's tree, which holds
-- no step of the proof: the steps are in the law graph.
/--
info: Effect4.Queue.Model.positive_suspend_step_capacity: proved; nearest []; 0 lemmas, 0 definitions
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

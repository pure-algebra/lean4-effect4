import Test.Program.QueueScenarios
import Effect4.Laws.Modules.Queue.Ops
import ProofGraph.Plan

/-!
# The Queue's operations: the finite controls of the library module (rows 233, 242 and 255)

The module is `src/Effect4/Modules/Queue/Ops.lean`, over the shared waiting wrapper
(`src/Effect4/Modules/Waiting.lean`). The eight scenarios and the masked caller are
`Test/Program/QueueScenarios.lean` and `Test/Program/QueueMask.lean`. This battery holds the
controls of the operations that those do not run, and of the module's laws.

1. **The construction refuses a capacity of zero** where an author writes the queue.
2. **`Queue.poll`** on the machine: an empty queue, a buffered message, a waiting taker
   (decisions row 242) and a pending offer that the poll's step accepts.
3. **Scope.** A client's program over the operations keeps the authoring scope judgment, by
   `authoring_scoped`: each operation's law is found by its name.

Placement. Each run is a finite control of the proposed claim `queue-expansion-agrees` (concept
`translation-simulation`, requirement R10), on the side of the operations' use in a program.
Every guard is one run on one schedule. None proves delivery, a cancellation law or liveness,
and none is a host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueOps

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.QueueScenarios (mk verdict exitOf exitAt typesOf bytesOf)
open Effect4.Modules

/-! ## 1. The construction: a positive capacity -/

-- A positive capacity is written as a literal, and the proof is found by `decide`.
#guard verdict (Queue.bounded .nat 1) = "built"
#guard typesOf (Queue.bounded .nat 3) = some (.refOf (Queue.cellTy .nat), .never)

/--
error: could not synthesize default value for parameter '_positive' using tactics
---
error: Tactic `decide` proved that the proposition
  0 < 0
is false
-/
#guard_msgs in
example : Src NativeOp := Queue.bounded .nat 0

/-! ## 2. `Queue.poll` on the machine -/

/-- An empty queue: the poll answers nothing. -/
def pollEmpty : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let x ← Queue.poll .nat q
  return x

/-- One buffered message and no taker: the first poll takes it, and the second finds nothing. -/
def pollOne : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let _ ← Queue.offer .nat q (nat 4)
  let x ← Queue.poll .nat q
  let y ← Queue.poll .nat q
  return tuple [x, y]

/-- **A poll passes no waiting taker** (decisions row 242). A taker waits. An offer buffers the
message 1 and posts the taker's wake. Before the helper runs, the root polls: the taker is still
enrolled, so the poll takes nothing, and the buffer still holds one message. The taker then
takes it. The answer: the poll, the size after it, the taker's message, and a last poll. -/
def pollBehindTaker : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let f ← fork (Queue.take .nat q)
  let _ ← Queue.offer .nat q (nat 1)
  let x ← Queue.poll .nat q
  let n ← Queue.size .nat q
  let y ← join f
  let z ← Queue.poll .nat q
  return tuple [x, n, y, z]

/-- **A poll that frees room accepts a pending offer**, and the offer's answer is posted.
Capacity one: a first offer is accepted, and a second waits. The poll takes the first message
and accepts the second offer. The offerer's answer is `true`, the buffer then holds one message,
and a last poll takes it. -/
def pollAccepts : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let a ← Queue.offer .nat q (nat 1)
  let f ← fork (Queue.offer .nat q (nat 2))
  let x ← Queue.poll .nat q
  let b ← join f
  let n ← Queue.size .nat q
  let y ← Queue.poll .nat q
  return tuple [a, x, b, n, y]

#guard [pollEmpty, pollOne, pollBehindTaker, pollAccepts].map verdict =
  List.replicate 4 "built"
-- A poll answers an option of a message, and it cannot fail.
#guard typesOf pollEmpty = some (.option .nat, .never)

#guard exitOf pollEmpty = some (.success .none)
#guard exitOf pollOne = some (.success (.list [.some (.nat 4), .none]))
-- The poll behind a waiting taker takes nothing, and the message stays for the taker.
#guard exitOf pollBehindTaker = some (.success (.list [.none, .nat 1, .nat 1, .none]))
#guard exitOf pollAccepts =
  some (.success (.list [.bool true, .some (.nat 1), .bool true, .nat 1, .some (.nat 2)]))
-- The ordinary run gives each answer at the truth lane's fuel.
#guard [pollEmpty, pollOne, pollBehindTaker, pollAccepts].all fun src =>
  (exitAt 1000 src).isSome && exitAt 1000 src == exitOf src

-- The model answers the same at the two states of `pollBehindTaker` and `pollOne`: with a
-- waiting taker the poll takes nothing, and with none it takes the message.
#guard (Queue.Model.poll
  { capacity := some 2, messages := [1], takers := [⟨7, 1, 1⟩] }).2.1 = none
#guard (Queue.Model.poll { capacity := some 2, messages := [1] }).2.1 = some 1
-- Red control of the pins: the same poll with no taker waiting takes the message.
#guard exitOf pollBehindTaker != some (.success (.list [.some (.nat 1), .nat 0, .nat 1, .none]))

/-! ## 3. Scope: a client's program over the operations -/

open Test.Program.QueueScenarios (r4 r4With library) in
/-- R4 keeps the scope judgment: `authoring_scoped` finds each operation's law by its name. -/
theorem r4_scoped : (r4 : Src NativeOp).Scoped := by
  unfold r4 r4With library
  authoring_scoped

/-- A program that polls and reads the size keeps the scope judgment. -/
theorem pollAccepts_scoped : (pollAccepts : Src NativeOp).Scoped := by
  unfold pollAccepts
  authoring_scoped

/-- So the tree that R4 elaborates to is closed (`elaborate_scoped`). -/
example (e : Eff NativeOp) (h : elaborate Test.Program.QueueScenarios.r4 = .ok e) :
    Eff.scopedAt 0 e = true :=
  elaborate_scoped r4_scoped h

/--
info: 'Effect4.Queue.take_scoped' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Effect4.Queue.take_scoped

/--
info: 'Effect4.Queue.offer_scoped' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Effect4.Queue.offer_scoped

/--
info: 'Effect4.Modules.waitRetry_scoped' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Effect4.Modules.waitRetry_scoped

end Test.Program.QueueOps

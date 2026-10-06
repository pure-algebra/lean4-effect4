module

public import Effect4.Modules.Queue.Steps
public import Effect4.Modules.Waiting

/-!
# Modules.Queue.Ops — the Queue's first operations (decisions rows 219 to 222, 233, 238, 240)

The operations of the Queue's first profile, as library programs over the step terms of
`src/Effect4/Modules/Queue/Steps.lean`. The first profile is a positive capacity, the `suspend`
strategy, and one message for each request. The names are the pin's
(`vendor/effect-4.0.0-rc.112/src/Queue.ts`).

| Operation | The pin's export | Where the first profile is narrower |
| --- | --- | --- |
| `bounded A capacity` | `bounded<A, E>(capacity)` | a positive literal; `suspend`; no `E` |
| `offer A q message` | `offer(self, message)` | one message; `true` or a wait; no terminal state |
| `take A q` | `take(self)` | one message; its error type is `never` |
| `poll A q` | `poll(self)` | it passes no waiting taker (decisions row 242) |
| `size A q` | `size(self)` | the buffer's length of an opened queue |

**The handle is the cell's `Ref`** (decisions row 255): `q` is a term that reads it, and no
handle type hides the cell. A cell that an author writes by hand is outside every law of the
module: each law takes a state of the first profile.

**A capacity of zero is refused where an author writes the queue.** `bounded` takes a proof
that the capacity is positive, by `decide`. Rendezvous at capacity zero is another profile
(decisions row 219).

**Each operation that waits is the shared wrapper** (`src/Effect4/Modules/Waiting.lean`). `take`
is `waitRetry`: a wake is a hint, and the taker runs its step again. `offer` is `waitAnswer`: the
step that frees room accepts the offer, and the posted helper carries the decided answer
(decisions row 240). The Queue supplies each attempt and each withdrawal: one step of the cell,
and one posted helper for each request that the step names, in the model's order.

**`poll` and `size` never wait.** `poll` is one step and its posts under `uninterruptible`: an
interruption between the step and a post would lose an accepted offer's answer. `size` is one
read of the cell, and a term over its value.

**Every binder is minted**, here and in the wrapper. So a variable that a caller reads through
`var`, for the handle or for a message, keeps its reading under each of them: a minted name is
reserved, and an author's name is not (`var_push_minted`,
`src/Effect4/Laws/Program/Author.lean`). That is no promise for an arbitrary source term, which
is a function of its scope. The fixtures of the earlier slices wrote the names `id`, `hint`,
`r`, `e` and `s` around such a variable (`Test/Program/QueueScenarios.lean` keeps their form as
the red controls).

The laws are in `src/Effect4/Laws/Modules/Queue/Ops.lean`: scope, typing and the attempt laws.
No run-level law is stated: no delivery, no order across steps, no cancellation law and no
budget. Batches, the other strategies, the terminal operations, `peek` and `clear` are later
slices.
-/

@[expose] public section

namespace Effect4.Queue

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- **`Queue.bounded`: a queue of a positive capacity under `suspend`.** It answers the cell's
`Ref`, the queue's handle. The capacity is a literal, and `positive` refuses zero where the
queue is written: `bounded A 0` does not elaborate in Lean. -/
def bounded (A : Ty) (capacity : Nat) (_positive : 0 < capacity := by decide) : Src NativeOp :=
  Ref.make (empty A capacity)

/-- **`Queue.take`: one message, in strict request order** (decisions row 219). It consumes in
its own atomic step, where a message is buffered and no earlier taker waits. Otherwise it enrols
with a fresh hint and waits. A step's notifications are posted in the model's order: the answers
of the offers that the step accepted, then the wake of the next taker. An interrupted wait
withdraws the request, and the withdrawal's step names the taker to wake. -/
def take (A : Ty) (q : TermSrc) : Src NativeOp :=
  waitRetry A "queue: the loop ended without a message"
    { hint := .unit
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (takeStep A id hint)) fun reply =>
          andThen (postAll (tupleAt reply 1) (bool true))
            (andThen (postAll (tupleAt reply 2) unit)
              (selectOptionWith (tupleAt reply 0) wait done))
      withdraw := fun id =>
        bindWith (Ref.modifyWith q (withdrawTake A id)) fun woken => postAll woken unit }

/-- **`Queue.offer`: one message, under `suspend`.** With room and no pending offer the step
accepts it, and the operation answers `true`. Otherwise the offer waits behind the pending ones.
The step that frees room accepts it and decides its answer, and a posted helper resolves the
offerer's hint with that answer (decisions row 240). An interrupted wait withdraws what is
still pending: a message that a step accepted stays accepted (decisions row 222). -/
def offer (A : Ty) (q message : TermSrc) : Src NativeOp :=
  waitAnswer
    { hint := .bool
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (offerStep A id hint message)) fun reply =>
          andThen (postAll (tupleAt reply 1) unit)
            (selectOptionWith (tupleAt reply 0) wait done)
      withdraw := fun id =>
        bindWith (Ref.modifyWith q (withdrawOffer A id)) fun woken => postAll woken unit }

/-- **`Queue.poll`: one message if it is there, and it never waits.** It consumes nothing while
a taker waits, so its empty answer does not say that the buffer is empty (decisions row 242). A
consuming step accepts the pending offers that fit, and each answer is posted. -/
def poll (A : Ty) (q : TermSrc) : Src NativeOp :=
  uninterruptible
    (bindWith (Ref.modifyWith q (pollStep A)) fun reply =>
      andThen (postAll (tupleAt reply 1) (bool true)) (succeed (tupleAt reply 0)))

/-- **`Queue.size`: the buffer's length.** One read of the cell, and the size step over its
value. It writes nothing. -/
def size (A : Ty) (q : TermSrc) : Src NativeOp :=
  bindWith (Ref.get q) fun cell => succeed (sizeStep A cell)

end Effect4.Queue

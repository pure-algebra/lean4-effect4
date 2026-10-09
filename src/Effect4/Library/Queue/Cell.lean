module

public import Effect4.Library.Words

/-!
# Modules.Queue.Cell — the Queue's cell: its type and its initial value (decisions row 255)

The Queue is the first composed module: a program over the authoring surface, in the `Modules`
layer above `Program`. Its state is one `Ref` at one record type, the cell. This file holds the
cell's type at a message type `A`, and the initial value at a capacity. The steps that read and
write the cell are in `src/Effect4/Library/Queue/Steps.lean`. The laws are in
`src/Effect4/Laws/Library/Queue/`, beside the abstract model.

The first cell holds the fields that the first steps read or write, and no other (the design's
F1, `docs/research/2026-10-05-claude-lead/queue-readiness/queue-steps-design.md`).

| Field | Type | The model's field |
| --- | --- | --- |
| `msgs` | a list of `A` | `messages` |
| `cap` | a number | `capacity`, positive in the first profile |
| `takers` | a list of records: identity, hint | `takers`, each at the bounds one and one |
| `offers` | a list of records: identity, hint, batch flag, messages not yet accepted | `offers` |

A request's identity is a `Deferred` that nobody resolves. Two identities are compared by
`sameHandle`, and never by a number. A hint is a `Deferred`: a taker's carries nothing, and an
offerer's carries its decided answer (decisions row 240). The type of an identity and of a
taker's hint is the shared `idTy` (`src/Effect4/Library/Words.lean`). An offer's batch flag is
false in the first profile, and its list holds one message.

**The cell's type is private to the module, and a later slice changes it.** A field's name does
not keep a `Ref`'s or a `Deferred`'s type. Three changes are known.

- The batches change an offer's answer: the hint carries a Boolean here, and a batch's answer is
  the list of the messages left. A stored taker gains its bounds then.
- The terminal operations add the phase with its end, and the awaiters. The end holds a
  failure's cause, so the module gains the failure type `E` beside `A`.
- `peek` adds the peekers, and the other strategies add the strategy. An unbounded queue makes
  the capacity an option.

Each change is a new cell type, a wider profile predicate and a wider relation. The handle is
the cell's `Ref` in this slice (decisions row 230). Nothing here performs an effect.
-/

@[expose] public section

namespace Effect4.Queue

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- An offerer's hint: a `Deferred` of its decided answer (decisions row 240). -/
def answerTy : Ty := .deferredOf .bool .never

/-- A waiting taker as a step writes it: its identity, then its hint. -/
def takerFields : List (String × Bool × Ty) := [("id", false, idTy), ("hint", false, idTy)]

/-- The type of a waiting taker: `takerFields` in the canonical field order. -/
def takerRecord : List (String × Bool × Ty) := [("hint", false, idTy), ("id", false, idTy)]

def takerTy : Ty := .record takerRecord

/-- A pending offer as a step writes it: its identity, its hint, the batch flag, and the
messages not yet accepted. The flag is false in the first profile, and the list holds one
message. -/
def offerFields (A : Ty) : List (String × Bool × Ty) :=
  [("id", false, idTy), ("hint", false, answerTy), ("batch", false, .bool),
   ("rest", false, .list A)]

/-- The type of a pending offer: `offerFields A` in the canonical field order. -/
def offerRecord (A : Ty) : List (String × Bool × Ty) :=
  [("batch", false, .bool), ("hint", false, answerTy), ("id", false, idTy),
   ("rest", false, .list A)]

def offerTy (A : Ty) : Ty := .record (offerRecord A)

/-- The cell as the initial value writes it: the buffer, the capacity, the waiting takers and
the pending offers, in the order of the design's F1. -/
def cellFields (A : Ty) : List (String × Bool × Ty) :=
  [("msgs", false, .list A), ("cap", false, .nat), ("takers", false, .list takerTy),
   ("offers", false, .list (offerTy A))]

/-- The cell's fields at the message type `A`: `cellFields A` in the canonical field order. A
step written as data names its fields against this list (`src/Effect4/Library/Queue/Data.lean`). -/
def cellRecord (A : Ty) : List (String × Bool × Ty) :=
  [("cap", false, .nat), ("msgs", false, .list A), ("offers", false, .list (offerTy A)),
   ("takers", false, .list takerTy)]

/-- **The cell's type at the message type `A`**: `cellFields A` in the canonical field order.
It is the type that the checker answers for `empty A capacity`, where `A` is its own normal
form. -/
def cellTy (A : Ty) : Ty := .record (cellRecord A)

/-- **The initial value at a capacity**: no message, no waiting taker and no pending offer. The
capacity is a literal, so a caller states a positive one where it writes the queue. -/
def empty (A : Ty) (capacity : Nat) : TermSrc :=
  record (cellFields A)
    [("msgs", app "nil" []), ("cap", nat capacity), ("takers", app "nil" []),
     ("offers", app "nil" [])]

end Effect4.Queue

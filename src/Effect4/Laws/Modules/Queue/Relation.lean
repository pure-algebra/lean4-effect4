import Effect4.Modules.Queue.Steps
import Effect4.Laws.Modules.Queue.Profile
import Effect4.Laws.Modules.Table

/-!
# The relation between the Queue's cell and the abstract model (decisions row 255)

The model (`src/Effect4/Laws/Modules/Queue/Model.lean`) names a request by a number, and a
signal by that number. The cell (`src/Effect4/Modules/Queue/Cell.lean`) names a request by a
`Deferred` handle, and a signal by a hint. So the connector is a relation, and no function of
the state alone. This file writes it (the design's F3,
`docs/research/2026-10-05-claude-lead/queue-readiness/queue-steps-design.md`).

- **The encoding table** is shared (`Table`, `src/Effect4/Laws/Modules/Table.lean`). It gives
  each model identity its identity handle and its current hint. `Table.Injective` says that no
  two identities share a handle.
- **The message map** gives each of the model's messages, a number, a value of the cell's
  message type. It keeps the order and the count of the messages.
- **The cell's value** (`cellVal`) is a function of the table, the map and a model state. On
  the first profile it loses nothing of the state: the phase, the strategy, a stored taker's
  bounds and the two empty lists are fixed there (`FirstProfile`).
- **A step changes the table in one way, and frames the rest** (`Table.renew`): it sets the
  hint of the step's own request, which it enrols or whose hint it replaces. Every other entry
  stays. The table after a take and after an offer reads the model's reply
  (`Table.afterTake`, `Table.afterOffer`), so the two are here.
- **A step's notifications** (`Notified`) are the model's signals, every signal and no other:
  the answers of offers that were pending before the step, then the wakes of takers that are
  stored after it.

A source term reads a value at a scope (`Reads`, `src/Effect4/Laws/Modules/Reading.lean`): a
step goal is stated for every scope and every caller's term that reads the step's arguments.

Placement. These are definitions, with no statement. Concept `translation-simulation`,
requirement R10: they are the vocabulary of the six step goals
(`src/Effect4/Laws/Modules/Queue/Steps.lean`), which are parts of the proposed claim
`queue-expansion-agrees`. The relation says nothing of a wrapper: a helper that was posted for
a hint since replaced belongs to the wrapper's relation, which counts each occurrence.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The table after a step -/

/-- The table after a take: the request's hint is the step's, where the request waits. -/
def Table.afterTake (tb : Table) (id : Nat) (hint : DeferredKey) : TakeReply → Table
  | .wait => tb.renew id hint
  | .got _ | .stopped _ => tb

/-- The table after an offer: the request's hint is the step's, where the request waits. -/
def Table.afterOffer (tb : Table) (id : Nat) (hint : DeferredKey) : OfferReply → Table
  | .wait => tb.renew id hint
  | .accepted _ => tb

end Effect4.Queue.Model

/-! The two functions above read the Queue's replies, so they are declared in the Queue's
namespace, and the shared table's namespace holds no declaration of a module. A statement writes
`tb.afterTake id hint reply` on a shared table: the field notation finds the two through these
aliases. -/
namespace Effect4.Modules.Table
export Effect4.Queue.Model.Table (afterTake afterOffer)
end Effect4.Modules.Table

namespace Effect4.Queue.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The cell's value -/

/-- A waiting taker's record: its hint and its identity, in the canonical field order. -/
def takerOf (hint id : Val) : Val :=
  .ctor 0 [.list [.str "hint", .str "id"], .list [hint, id]]

/-- A pending offer's record, in the canonical field order. -/
def offerOf (batch hint id rest : Val) : Val :=
  .ctor 0 [.list [.str "batch", .str "hint", .str "id", .str "rest"],
    .list [batch, hint, id, rest]]

/-- The cell's record, in the canonical field order. -/
def cellOf (cap msgs offers takers : Val) : Val :=
  .ctor 0 [.list [.str "cap", .str "msgs", .str "offers", .str "takers"],
    .list [cap, msgs, offers, takers]]

/-- A stored taker, through the table. -/
def takerVal (tb : Table) (t : Taker) : Val :=
  takerOf (Val.promise (tb.hint t.id)) (Val.promise (tb.handle t.id))

/-- A pending offer, through the table and the message map. -/
def offerVal (tb : Table) (msg : Nat → Val) (o : Offer) : Val :=
  offerOf (.bool o.batch) (Val.promise (tb.hint o.id)) (Val.promise (tb.handle o.id))
    (.list (o.rest.map msg))

/-- **The cell's value for a model state**: the capacity, the buffer through the message map,
and the waiting requests through the table. An unbounded queue has no cell in this slice, and
its capacity reads as zero. -/
def cellVal (tb : Table) (msg : Nat → Val) (s : State) : Val :=
  cellOf (.nat (s.capacity.getD 0)) (.list (s.messages.map msg))
    (.list (s.offers.map (offerVal tb msg))) (.list (s.takers.map (takerVal tb)))

/-! ## The replies -/

/-- A take's reply as the step answers it: one message, or none where the request waits. A
first-profile take answers no other reply, and none has an encoding. -/
def takeReplyVal (msg : Nat → Val) : TakeReply → Option Val
  | .got [m] => some (Store.Val.some (msg m))
  | .wait => some Store.Val.none
  | .got _ | .stopped _ => none

/-- An offer's reply as the step answers it: the decided answer, or none where it waits. -/
def offerReplyVal : OfferReply → Val
  | .accepted ok => Store.Val.some (.bool ok)
  | .wait => Store.Val.none

/-- A poll's reply as the step answers it. -/
def pollReplyVal (msg : Nat → Val) : Option Nat → Val
  | some m => Store.Val.some (msg m)
  | none => Store.Val.none

/-! ## The notifications -/

/-- **The signals of a first-profile step, read as the step's two lists.** The signals are the
answers `offered true` of the offers `entered`, in order, and then the wakes of the takers
`woken`: every signal, and no other. Each offer that entered was pending before the step, and
each taker to wake is stored after it. -/
structure Notified (before after : State) (signals : List Signal) (entered : List Offer)
    (woken : List Taker) : Prop where
  signals : signals =
    entered.map (fun o => (⟨o.id, .offered true⟩ : Signal)) ++
      woken.map (fun t => (⟨t.id, .again⟩ : Signal))
  entered : ∀ o ∈ entered, o ∈ before.offers
  woken : ∀ t ∈ woken, t ∈ after.takers

end Effect4.Queue.Model

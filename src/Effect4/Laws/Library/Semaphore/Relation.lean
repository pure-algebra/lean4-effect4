import Effect4.Library.Semaphore.Steps
import Effect4.Laws.Library.Semaphore.Profile
import Effect4.Laws.Step.Table

/-!
# The relation between Semaphore's cell and the abstract model (decisions row 265)

The model (`src/Effect4/Library/Semaphore/Model.lean`) names a request by a number. The
cell (`src/Effect4/Library/Semaphore/Cell.lean`) names a request by a `Deferred` handle, and it
holds each waiter's hint, which the model does not hold. So the connector is a relation, and no
function of the state alone.

- **The encoding table** is shared (`Table`, `src/Effect4/Laws/Step/Table.lean`): each
  model identity's handle, and its current hint. `Table.Injective` says that no two identities
  share a handle.
- **The cell's value** (`cellVal`) is a function of the table and a model state. It loses
  nothing of the state: the total, the permits taken, the next stamp, and each waiter's
  identity, count and stamp. A waiter's count and stamp are numbers, so they need no entry of
  the table.
- **A step changes the table in one way** (`Table.renew`): a take sets the hint of its own
  request. Every other entry stays. A visit, a release and a withdrawal leave the table.
- **The replies**: a Boolean for the two takes; the free count and a Boolean for a release;
  the selected waiter's record through the table for a visit (`visitReplyVal`); nothing for a
  withdrawal.

`Reads` and `Captured` are shared too (`src/Effect4/Laws/Step/Reading.lean`): a source term
reads a value at a scope, and a caller's term keeps its value under a fold's two binders.

Placement. These are definitions, with no statement. Concept `translation-simulation`,
requirement R10: they are the vocabulary of the five step goals
(`src/Effect4/Laws/Library/Semaphore/Steps.lean`), parts of the proposed claim
`semaphore-expansion-agrees`. The relation says nothing of a wrapper: which request waits on
which hint, and which helper holds which cursor, belong to the wrapper's relation.
-/

set_option autoImplicit false

namespace Effect4.Semaphore.Model

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Modules

/-! ## The cell's value -/

/-- A waiter's record: its hint, its identity, its count and its stamp, in the canonical field
order. -/
def waiterOf (hint id need stamp : Val) : Val :=
  .ctor 0 [.list [.str "hint", .str "id", .str "need", .str "stamp"],
    .list [hint, id, need, stamp]]

/-- The cell's record, in the canonical field order. -/
def cellOf (next permits taken waiters : Val) : Val :=
  .ctor 0 [.list [.str "next", .str "permits", .str "taken", .str "waiters"],
    .list [next, permits, taken, waiters]]

/-- A stored waiter, through the table. -/
def waiterVal (tb : Table) (w : Waiter) : Val :=
  waiterOf (Val.promise (tb.hint w.id)) (Val.promise (tb.handle w.id)) (.nat w.need)
    (.nat w.stamp)

/-- **The cell's value for a model state**: the four fields, with the waiters through the
table. -/
def cellVal (tb : Table) (s : State) : Val :=
  cellOf (.nat s.next) (.nat s.permits) (.nat s.taken) (.list (s.waiters.map (waiterVal tb)))

/-! ## The replies -/

/-- A release's reply as the step answers it: the free count, and whether a waiter is
enrolled. -/
def releaseReplyVal (reply : Nat × Bool) : Val := Val.tuple [.nat reply.1, .bool reply.2]

/-- A visit's reply as the step answers it: the selected waiter's record through the table, or
nothing. The record holds the hint that the helper resolves and the stamp that the walk
continues after. -/
def visitReplyVal (tb : Table) : Option Waiter → Val
  | some w => Store.Val.some (waiterVal tb w)
  | none => Store.Val.none

end Effect4.Semaphore.Model

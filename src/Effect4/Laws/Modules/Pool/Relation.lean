import Effect4.Modules.Pool.Steps
import Effect4.Laws.Modules.Pool.Profile
import Effect4.Laws.Modules.Table

/-!
# The relation between Pool's cell and the abstract model (decisions rows 267 to 269)

The model (`src/Effect4/Laws/Modules/Pool/Model.lean`) names a request by a number and a
resource by a number. The cell (`src/Effect4/Modules/Pool/Cell.lean`) names a request by a
`Deferred` handle, it holds each waiter's hint, and it holds each resource's value. So the
connector is a relation, and no function of the state alone.

- **The encoding table** is shared (`Table`, `src/Effect4/Laws/Modules/Table.lean`): each
  model identity's handle, and its current hint. It serves as it is. `Table.Injective` says
  that no two identities share a handle.
- **The resources' values** are one more map, from a model resource to its value, as the
  Queue's relation maps a model message. Two items may hold one resource, so the map needs no
  injectivity: no step compares two resources.
- **The cell's value** (`cellVal`) is a function of the table, that map and a model state. It
  loses nothing of the state: the idle stamps, the flag, the next stamp, each item's four
  fields and each waiter's identity. The stamps and the flags are numbers and Booleans, so
  they need no entry of the table.
- **A step changes the table in one way** (`Table.renew`): a lease sets the hint of its own
  request, and the closer's step sets the closer's. Every other entry stays. A return, a
  selection, a withdrawal and the close's first step leave the table.
- **The replies**: a Boolean and an option of the leased item's record for a lease
  (`leaseReplyVal`); two Booleans for a return; the selected waiters' records through the table
  for a selection (`selectReplyVal`); nothing for a withdrawal; a Boolean and a number for the
  close's first step; a Boolean for the closer's step.

`Reads` and `Captured` are shared too (`src/Effect4/Laws/Modules/Reading.lean`): a source term
reads a value at a scope, and a caller's term keeps its value under a fold's two binders.

Placement. These are definitions, with no statement. Concept `translation-simulation`,
requirement R10: they are the vocabulary of the six step goals
(`src/Effect4/Laws/Modules/Pool/Steps.lean`), parts of the proposed claim
`pool-expansion-agrees`. The relation says nothing of a wrapper: which fiber holds which lease,
which request waits on which hint, and which helper holds which selected records belong to the
wrapper's relation.
-/

set_option autoImplicit false

namespace Effect4.Pool.Model

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Modules

/-! ## The cell's value -/

/-- An item's record: whether a lease holds it, its latest lease's stamp, its resource and its
stamp, in the canonical field order. -/
def itemOf (borrowed lease resource stamp : Val) : Val :=
  .ctor 0 [.list [.str "borrowed", .str "lease", .str "resource", .str "stamp"],
    .list [borrowed, lease, resource, stamp]]

/-- A waiter's record: its hint and its identity, in the canonical field order. -/
def waiterOf (hint id : Val) : Val :=
  .ctor 0 [.list [.str "hint", .str "id"], .list [hint, id]]

/-- The cell's record, in the canonical field order. -/
def cellOf (available closing items next waiters : Val) : Val :=
  .ctor 0
    [.list [.str "available", .str "closing", .str "items", .str "next", .str "waiters"],
      .list [available, closing, items, next, waiters]]

/-- A stored item, through the resources' values. -/
def itemVal (res : Nat → Val) (it : Item) : Val :=
  itemOf (.bool it.borrowed) (.nat it.lease) (res it.resource) (.nat it.stamp)

/-- A stored waiter, through the table. -/
def waiterVal (tb : Table) (id : Nat) : Val :=
  waiterOf (Val.promise (tb.hint id)) (Val.promise (tb.handle id))

/-- **The cell's value for a model state**: the five fields, with the items through the
resources' values and the waiters through the table. -/
def cellVal (tb : Table) (res : Nat → Val) (s : State) : Val :=
  cellOf (.list (s.available.map Val.nat)) (.bool s.closing) (.list (s.items.map (itemVal res)))
    (.nat s.next) (.list (s.waiters.map (waiterVal tb)))

/-! ## The replies -/

/-- The leased item of a lease's reply as the step answers it: the item's record, or
nothing. -/
def leasedVal (res : Nat → Val) : Option Item → Val
  | some it => Store.Val.some (itemVal res it)
  | none => Store.Val.none

/-- A lease's reply as the step answers it: whether the pool refused, and the leased item's
record, if any. -/
def leaseReplyVal (res : Nat → Val) (reply : Bool × Option Item) : Val :=
  Val.tuple [.bool reply.1, leasedVal res reply.2]

/-- A return's reply as the step answers it: whether the lease returned, and whether a wake is
owed. -/
def returnReplyVal (reply : Bool × Bool) : Val := Val.tuple [.bool reply.1, .bool reply.2]

/-- A selection's reply as the step answers it: the selected waiters' records through the
table, in order. Each record holds the identity and the hint that the helper resolves. -/
def selectReplyVal (tb : Table) (selected : List Nat) : Val :=
  Val.list (selected.map (waiterVal tb))

/-- The reply of the close's first step as the step answers it: whether it began the close,
and the count of the waiters. -/
def closeReplyVal (reply : Bool × Nat) : Val := Val.tuple [.bool reply.1, .nat reply.2]

end Effect4.Pool.Model

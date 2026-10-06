module

public import Effect4.Modules.Words

/-!
# Modules.Pool.Cell — Pool's cell: its type and its initial value (decisions rows 267 to 269)

Pool is the third composed module: a program over the authoring surface, in the `Modules`
layer above `Program`. Its state is one `Ref` at one record type, the cell. This file holds
the cell's type at a resource type `A`, and the initial value at the acquired resources. The
steps that read and write the cell are in `src/Effect4/Modules/Pool/Steps.lean`. The laws are in
`src/Effect4/Laws/Modules/Pool/`, beside the abstract model.

The cell holds five fields, an item four and a waiter two (the card's section 3,
`docs/research/2026-10-05-claude-lead/module-cards/pool.md`).

| Record | Field | Type | The model's field |
| --- | --- | --- | --- |
| cell | `items` | a list of items | `items`, in the order of acquisition: no step adds or removes one |
| cell | `available` | a list of numbers | `available`, the stamps of the idle items, the front first |
| cell | `waiters` | a list of waiters, oldest first | `waiters` |
| cell | `closing` | a Boolean | `closing`: the close has begun |
| cell | `next` | a number | `next`, the stamp of the next lease |
| item | `stamp` | a number | the item's identity: its place in the order of acquisition |
| item | `resource` | `A` | the acquired value, which the model names by a number |
| item | `borrowed` | a Boolean | a lease holds the item |
| item | `lease` | a number | the stamp of the item's latest lease |
| waiter | `id` | a `Deferred` of nothing | the request's identity |
| waiter | `hint` | a `Deferred` of nothing | no field: the table of the relation gives it |

**A lease in the cell** is an item's record whose `borrowed` is true: its `stamp` and its
`lease` are the card's pair of an item's stamp and a lease's stamp. The field `lease` has a
meaning only while `borrowed` is true. An idle item keeps the stamp of its last lease there,
and no step reads it. Two items may hold equal resources, so a resource's value is no item's
identity: the stamp is.

**Outside the cell** stay the borrower's fiber, the body, the return's hook and the item's
finalizer. A helper's count and the waiters that it selected stay in the helper. The cell
holds no lease that returned.

A request's identity is a `Deferred` that nobody resolves, as in the Queue's cell: its type is
the shared `idTy` (`src/Effect4/Modules/Words.lean`). Two identities are compared by
`sameHandle`, and never by a number. A hint is a `Deferred` of nothing: the wake's helper
resolves it, and the borrower then runs its own lease step again.

The cell's type is private to the module. The close that waits adds no field to it: the closer
waits as a request, an entry of `waiters` (decisions row 276, point 2). The handle is the cell's
`Ref` in this slice (decisions row 230). Nothing here performs an effect.
-/

@[expose] public section

namespace Effect4.Pool

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- An item as the initial value writes it: its stamp, its resource, whether a lease holds it,
and the stamp of its latest lease. -/
def itemFields (A : Ty) : List (String × Bool × Ty) :=
  [("stamp", false, .nat), ("resource", false, A), ("borrowed", false, .bool),
   ("lease", false, .nat)]

/-- The type of an item at the resource type `A`: `itemFields A` in the canonical field
order. -/
def itemTy (A : Ty) : Ty := .record
  [("borrowed", false, .bool), ("lease", false, .nat), ("resource", false, A),
   ("stamp", false, .nat)]

/-- A waiter as a step writes it: its identity, then its hint. -/
def waiterFields : List (String × Bool × Ty) := [("id", false, idTy), ("hint", false, idTy)]

/-- The type of a waiter: `waiterFields` in the canonical field order. -/
def waiterTy : Ty := .record [("hint", false, idTy), ("id", false, idTy)]

/-- The cell as the initial value writes it: the items, the idle stamps, the waiters, whether
the pool is closing, and the stamp of the next lease. -/
def cellFields (A : Ty) : List (String × Bool × Ty) :=
  [("items", false, .list (itemTy A)), ("available", false, .list .nat),
   ("waiters", false, .list waiterTy), ("closing", false, .bool), ("next", false, .nat)]

/-- **The cell's type at the resource type `A`**: `cellFields A` in the canonical field order.
It is the type that the checker answers for `initial A resources`, where `A` is its own normal
form and at least one resource is given. -/
def cellTy (A : Ty) : Ty := .record
  [("available", false, .list .nat), ("closing", false, .bool),
   ("items", false, .list (itemTy A)), ("next", false, .nat),
   ("waiters", false, .list waiterTy)]

/-- An idle item's record, at a stamp and a resource. -/
def mkItem (A : Ty) (stamp resource : TermSrc) : TermSrc :=
  record (itemFields A)
    [("stamp", stamp), ("resource", resource), ("borrowed", bool false), ("lease", nat 0)]

/-- The items of the initial value, from a stamp on: each resource has the next stamp. -/
def itemsFrom (A : Ty) (stamp : Nat) : List TermSrc → List TermSrc
  | [] => []
  | resource :: rest => mkItem A (nat stamp) resource :: itemsFrom A (stamp + 1) rest

/-- The stamps of the initial value's items, from a stamp on. -/
def stampsFrom (stamp : Nat) : List TermSrc → List TermSrc
  | [] => []
  | _ :: rest => nat stamp :: stampsFrom (stamp + 1) rest

/-- **The initial value at the acquired resources**: each resource has the stamp of its
position, every item is idle in the order of acquisition, no request waits, the pool is open,
and the next lease's stamp is zero. The resources are a list of terms, so the size is stated
where the program is written (decisions row 267). -/
def initial (A : Ty) (resources : List TermSrc) : TermSrc :=
  record (cellFields A)
    [("items", listOf (itemsFrom A 0 resources)),
     ("available", listOf (stampsFrom 0 resources)),
     ("waiters", nilT), ("closing", bool false), ("next", nat 0)]

end Effect4.Pool

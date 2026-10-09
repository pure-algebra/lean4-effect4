module

/-!
# Pool's abstract transition model (decisions rows 267 to 269)

The model of the packet `Test/contracts/pool.contract.md`: the state of one pool and its six
transitions. No effect, no wrapper, no fiber and no delivery of a wake occurs here: a transition
answers a state and a reply.

| Transition | What it is | The ruling |
| --- | --- | --- |
| `lease` | lease or enrol: one atomic step, so no gap exists between the check and the enrolment | rows 267 and 268 |
| `giveBack` | a return: the item joins the front of the idle items | row 269 |
| `select` | one selection of the wake at a count: the first waiters leave the list | the card's sections 1 and 4 |
| `withdraw` | a waiting request leaves | the card's section 4 |
| `close` | the close's first step: the pool refuses new leases from now on | row 268 |
| `drain` | the closer's step: it tells whether no lease is outstanding, and it enrols the closer otherwise | rows 268 and 276, point 2 |

An item is its stamp, the name of its resource, whether a lease holds it, and the stamp of its
latest lease (the card's section 3,
`docs/research/2026-10-05-claude-lead/module-cards/pool.md`). A resource is a number that names
its value: two items may hold one resource, so the stamp is the item's identity. A waiter is
its request's identity.

**A lease in the state** is an item with `borrowed` true: its `stamp` and its `lease` are the
card's pair. The field `lease` has a meaning only while `borrowed` is true. An idle item keeps
the stamp of its last lease there, and no transition reads it.

Six properties of the ruled profile are visible in the definitions.

- **The rule of enrolment is on the step.** `lease` adds a waiter only when the pool is open
  and no stamp is idle. An idle item beside enrolled waiters is a state of the model: a return
  makes its item idle at once, and the selection of its helper comes later.
- **A wake reserves nothing.** `select` changes the waiters alone. A lease commits in the
  borrower's own `lease`, which checks again.
- **A return names its lease.** `giveBack` frees the item only where that lease holds it. A
  return of a lease that holds nothing changes nothing, so a stale lease frees no item that was
  leased again.
- **A returned item joins the front** of the idle items (decisions row 269), and `lease` takes
  the front. No transition adds or removes an item: a return finalizes nothing.
- **A lease removes its own request's entry first.** On every state that the wrapper reaches a
  selection has already removed a resumed borrower, so the removal changes nothing there. It is
  in the model so that no transition has a premise on its request.
- **The closer waits as a request.** `drain` enrols the closer only where a lease is
  outstanding, in the step that reads it. So no gap exists between that check and the enrolment,
  and each later return finds a waiter. The cell gains no field (decisions row 276, point 2).

Placement. These are definitions, with no statement. Concept `reactive-scheduling`: they are
the abstract client of the proposed claim `pool-expansion-agrees` (requirement R10). The profile
and its closure are `src/Effect4/Laws/Library/Pool/Profile.lean`. The model states no order of
the wake across helpers, no fairness, no progress of a waiter or of the closer, no finalizer's
run and no completed close.
-/

@[expose] public section

namespace Effect4.Pool.Model

/-- An item of the pool. -/
structure Item where
  /-- The item's identity: its place in the order of acquisition. -/
  stamp : Nat
  /-- The name of the item's resource. Two items may hold one resource. -/
  resource : Nat
  /-- A lease holds the item. -/
  borrowed : Bool := false
  /-- The stamp of the item's latest lease. It has a meaning only while `borrowed` is true. -/
  lease : Nat := 0
  deriving DecidableEq, Repr

structure State where
  /-- Every item, in the order of acquisition. No transition adds or removes one. -/
  items : List Item
  /-- The stamps of the idle items, in the order of reuse: the front first. -/
  available : List Nat := []
  /-- The identities of the requests that wait, in the order of enrolment. -/
  waiters : List Nat := []
  /-- The close has begun. -/
  closing : Bool := false
  /-- The stamp of the next lease. -/
  next : Nat := 0
  deriving DecidableEq, Repr

/-- The items of a pool as it is made, from a stamp on: each resource has the next stamp, and
every item is idle. -/
def itemsFrom (stamp : Nat) : List Nat → List Item
  | [] => []
  | resource :: rest => ⟨stamp, resource, false, 0⟩ :: itemsFrom (stamp + 1) rest

/-- The pool as it is made, at its acquired resources: every item idle, in the order of
acquisition, no waiter, open, and the stamp zero. The idle stamps are the items' stamps: the
numbers below the size, in order (`initial_available`,
`src/Effect4/Laws/Library/Pool/Profile.lean`). -/
def initial (resources : List Nat) : State :=
  { items := itemsFrom 0 resources, available := (itemsFrom 0 resources).map (·.stamp) }

/-- The outstanding leases: the item's stamp and the lease's stamp of each borrowed item. -/
def leases (s : State) : List (Nat × Nat) :=
  (s.items.filter (·.borrowed)).map fun it => (it.stamp, it.lease)

/-- The waiters without the request `id`. -/
def without (waiters : List Nat) (id : Nat) : List Nat := waiters.filter (· != id)

/-- **Withdraw.** The request's entry leaves. A waiter holds nothing, so nothing else
changes. -/
def withdraw (s : State) (id : Nat) : State := { s with waiters := without s.waiters id }

/-- An item as the lease `l` holds it. -/
def Item.leasedAs (it : Item) (l : Nat) : Item := { it with borrowed := true, lease := l }

/-- The items, with the item `i` leased at the stamp `l`. -/
def mark (items : List Item) (i l : Nat) : List Item :=
  items.map fun it => if it.stamp = i then it.leasedAs l else it

/-- The item `i` as the lease `l` holds it, if the pool has such an item. -/
def leased (items : List Item) (i l : Nat) : Option Item :=
  ((items.filter fun it => decide (it.stamp = i)).map (·.leasedAs l))[0]?

/-- **Lease or enrol.** The request's own entry leaves first. At a closing pool nothing else
changes, and the answer says that the pool refused. With no idle stamp the request enrols at
the list's end. Otherwise the front idle item leaves `available`, the lease `next` holds it, and
`next` gains one. The answer: the next state, whether the pool refused, and the leased item. -/
def lease (s : State) (id : Nat) : State × Bool × Option Item :=
  if s.closing then (withdraw s id, true, none)
  else
    match s.available with
    | [] => ({ s with waiters := without s.waiters id ++ [id] }, false, none)
    | i :: rest =>
      ({ s with
          items := mark s.items i s.next, available := rest,
          waiters := without s.waiters id, next := s.next + 1 },
        false, leased s.items i s.next)

/-- Whether the lease `l` holds the item `i`, at one item. -/
def Item.heldBy (it : Item) (i l : Nat) : Bool :=
  decide (it.stamp = i) && (it.borrowed && decide (it.lease = l))

/-- The items, with the item that the lease `l` holds at the stamp `i` idle again. -/
def freed (items : List Item) (i l : Nat) : List Item :=
  items.map fun it => if it.heldBy i l then { it with borrowed := false } else it

/-- **Return.** Where the lease `l` holds the item `i`, the item is idle again and its stamp
joins the front of `available` (decisions row 269). Otherwise nothing changes. The answer: the
next state, whether the lease returned, and whether a wake is owed. A wake is owed where the
lease returned and a waiter is enrolled: the wrapper posts one helper at the count 1 then. -/
def giveBack (s : State) (i l : Nat) : State × Bool × Bool :=
  if s.items.any (·.heldBy i l) then
    ({ s with items := freed s.items i l, available := i :: s.available }, true,
      !s.waiters.isEmpty)
  else (s, false, false)

/-- **One selection of the wake at a count.** The first `count` waiters leave the list, in the
order of enrolment, and they are the answer. Nothing else changes: a wake reserves nothing. -/
def select (s : State) (count : Nat) : State × List Nat :=
  ({ s with waiters := s.waiters.drop count }, s.waiters.take count)

/-- **The close's first step.** The pool refuses new leases from now on (decisions row 268).
The answer: the next state, whether this step began the close, and the count of the waiters,
which is the count of the helper that the close posts. -/
def close (s : State) : State × Bool × Nat :=
  ({ s with closing := true }, !s.closing, s.waiters.length)

/-- **The closer's step** (decisions row 276, point 2). The closer's own entry leaves first.
Where a lease is outstanding, the closer enrols at the list's end, and the answer says that the
pool is not drained. Otherwise nothing else changes, and the answer says that it is. The
answer: the next state, and whether no lease is outstanding. -/
def drain (s : State) (id : Nat) : State × Bool :=
  if s.items.any (·.borrowed) then ({ s with waiters := without s.waiters id ++ [id] }, false)
  else (withdraw s id, true)

/-! ## The transitions as one alphabet -/

/-- The model's operations, one for each transition. -/
inductive Op
  | lease (id : Nat)
  | giveBack (item lease : Nat)
  | select (count : Nat)
  | withdraw (id : Nat)
  | close
  | drain (id : Nat)
  deriving DecidableEq, Repr

/-- The state after one operation. -/
def step (s : State) : Op → State
  | .lease id => (lease s id).1
  | .giveBack item l => (giveBack s item l).1
  | .select count => (select s count).1
  | .withdraw id => withdraw s id
  | .close => (close s).1
  | .drain id => (drain s id).1

end Effect4.Pool.Model

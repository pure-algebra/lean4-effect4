module

public import Effect4.Modules.Queue.Cell

/-!
# Modules.Semaphore.Cell — Semaphore's cell: its type and its initial value (rows 260, 265)

Semaphore is the second composed module: a program over the authoring surface, in the
`Modules` layer above `Program`. Its state is one `Ref` at one record type, the cell. This file
holds the cell's type and the initial value at a total. The steps that read and write the cell
are in `src/Effect4/Modules/Semaphore/Steps.lean`. The laws are in
`src/Effect4/Laws/Modules/Semaphore/`, beside the abstract model.

The cell holds four fields, and a waiter four (the card's section 3,
`docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`).

| Record | Field | Type | The model's field |
| --- | --- | --- | --- |
| cell | `permits` | a number | `permits`, the total: no step changes it |
| cell | `taken` | a number | `taken`, the permits held |
| cell | `waiters` | a list of waiters, oldest first | `waiters` |
| cell | `next` | a number | `next`, the stamp of the next enrolment |
| waiter | `id` | a `Deferred` of nothing | the request's identity |
| waiter | `need` | a number | the count that the request needs |
| waiter | `hint` | a `Deferred` of nothing | no field: the table of the relation gives it |
| waiter | `stamp` | a number | the enrolment's stamp |

A request's identity is a `Deferred` that nobody resolves, as in the Queue's cell: its type is
`Queue.idTy`. Two identities are compared by `sameHandle`, and never by a number. A hint is a
`Deferred` of nothing: a visit of the wake's walk resolves it, and the waiter then runs its own
take step again (decisions row 259). The free count is no field: each step derives it as the
total less what is taken.

The cell has no type parameter, so its type is closed. The cell's type is private to the
module. The handle is the cell's `Ref` in this slice (decisions row 230). Nothing here performs
an effect.
-/

@[expose] public section

namespace Effect4.Semaphore

open Effect4.Program Effect4.Program.Authoring

/-- A waiter as a step writes it: its identity, the count that it needs, its hint and its
stamp. -/
def waiterFields : List (String × Bool × Ty) :=
  [("id", false, Queue.idTy), ("need", false, .nat), ("hint", false, Queue.idTy),
   ("stamp", false, .nat)]

/-- The type of a waiter: `waiterFields` in the canonical field order. -/
def waiterTy : Ty := .record
  [("hint", false, Queue.idTy), ("id", false, Queue.idTy), ("need", false, .nat),
   ("stamp", false, .nat)]

/-- The cell as the initial value writes it: the total, the permits taken, the waiters and the
stamp of the next enrolment. -/
def cellFields : List (String × Bool × Ty) :=
  [("permits", false, .nat), ("taken", false, .nat), ("waiters", false, .list waiterTy),
   ("next", false, .nat)]

/-- **The cell's type**: `cellFields` in the canonical field order. It is the type that the
checker answers for `empty permits`. -/
def cellTy : Ty := .record
  [("next", false, .nat), ("permits", false, .nat), ("taken", false, .nat),
   ("waiters", false, .list waiterTy)]

/-- **The initial value at a total**: nothing taken, no waiter and the stamp zero. The total is
a literal, so a caller states a total of at least 1 where it writes the semaphore (decisions
row 260). -/
def empty (permits : Nat) : TermSrc :=
  record cellFields
    [("permits", nat permits), ("taken", nat 0), ("waiters", app "nil" []), ("next", nat 0)]

end Effect4.Semaphore

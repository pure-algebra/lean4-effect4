import Effect4.Laws.Modules.Table

/-!
# The Latch's abstract model

The model of rc.112's `class Latch` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`), its
pure transitions only. A waiter is named by a number; the table (`Table`,
`src/Effect4/Laws/Modules/Table.lean`) gives its identity's handle and its hint.

- `_isOpen` is `isOpen`; `waiters` is `waiters`.
- rc.112's `scheduled` batch is `pending` and `scheduled`: the batch is `undefined` exactly when
  `scheduled` is false.
- **`wake`** is `open` (with `setOpen`) and `release` (without), each followed by
  `scheduleUnsafe`. An open latch answers false. Otherwise, with no waiter, the answer is true
  and nothing is posted. With waiters and no batch scheduled, the waiters become the batch and
  one flush is posted. With a batch scheduled, the waiters join its end and nothing is posted.
- **`flush`** is `flushScheduled`: the batch, and no batch scheduled.
- **`close`** is `closeUnsafe`: whether it closed the latch.

Placement: concept `translation-simulation`, requirement R10. The model is the other side of the
claim `latch-steps-agree` (`src/Effect4/Laws/Modules/Latch/Steps.lean`). It models no `await`,
no interruption and no fiber: the wrapper's relation owns them.
-/

set_option autoImplicit false

namespace Effect4.Latch.Model

/-- The Latch's state. -/
structure State where
  /-- rc.112's `_isOpen`. -/
  isOpen : Bool
  /-- The waiters not yet in a batch, in the order of enrolment. -/
  waiters : List Nat := []
  /-- The waiters of the scheduled batch, in order. -/
  pending : List Nat := []
  /-- Whether a flush is scheduled: rc.112's `scheduled !== undefined`. -/
  scheduled : Bool := false
  deriving DecidableEq, Repr

/-- The state after a wake: opened for `open`, as it is for `release`. -/
def opened (setOpen : Bool) (s : State) : State := if setOpen then { s with isOpen := true } else s

/-- **`open` and `release`, each with `scheduleUnsafe`.** The answer: the next state, the reply,
and whether a flush is posted. -/
def wake (setOpen : Bool) (s : State) : State × Bool × Bool :=
  if s.isOpen then (s, false, false)
  else if s.waiters.length = 0 then (opened setOpen s, true, false)
  else if s.scheduled then
    (opened setOpen { s with pending := s.pending ++ s.waiters, waiters := [] }, true, false)
  else (opened setOpen { s with pending := s.waiters, scheduled := true, waiters := [] }, true, true)

/-- **`flushScheduled`**: the next state and the batch, in order. -/
def flush (s : State) : State × List Nat :=
  if s.scheduled then ({ s with pending := [], scheduled := false }, s.pending) else (s, [])

/-- **`closeUnsafe`**: the next state, and whether it closed the latch. -/
def close (s : State) : State × Bool :=
  if s.isOpen then ({ s with isOpen := false }, true) else (s, false)

end Effect4.Latch.Model

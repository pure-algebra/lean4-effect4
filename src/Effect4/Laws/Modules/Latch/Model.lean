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
claim `latch-steps-agree` (`src/Effect4/Laws/Modules/Latch/Steps.lean`). Await enrolment and
withdrawal are pure transitions. The wrapper owns interruption delivery and fiber scheduling.
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

/-- The initial state, with the chosen open flag and no registrations or scheduled batch. -/
def initial (isOpen : Bool) : State := { isOpen }

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

/-- **The callback registration of `await`** (rc.112, `internal/effect.ts`, lines 5624–5629).
An open latch answers immediately. A closed latch appends this registration to the waiters.
The reply states whether the callback answers immediately. -/
def awaitLatch (s : State) (id : Nat) : State × Bool :=
  if s.isOpen then (s, true) else ({ s with waiters := s.waiters ++ [id] }, false)

/-- **The cleanup of one registration** (rc.112, `internal/effect.ts`, lines 5629–5639).
It removes the first matching waiter. Only if no waiter matches does it inspect the scheduled
batch. A batch detached by `flush` is no longer in this state. The operation does not cancel
the scheduled flush, even when its batch becomes empty. -/
def withdraw (s : State) (id : Nat) : State × Unit :=
  if s.waiters.contains id then ({ s with waiters := s.waiters.erase id }, ())
  else if s.scheduled then ({ s with pending := s.pending.erase id }, ())
  else (s, ())

end Effect4.Latch.Model

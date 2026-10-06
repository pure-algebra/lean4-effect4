/-!
# Semaphore's abstract transition model (decisions rows 259 to 261 and 265)

The model of the packet `Test/contracts/semaphore.contract.md`: the state of one semaphore and
its five transitions. No effect, no wrapper, no fiber and no delivery of a wake occurs here: a
transition answers a state and a reply.

| Transition | What it is | The ruling |
| --- | --- | --- |
| `take` | take or enrol: one atomic step, so no gap exists between the check and the enrolment | rows 259 and 260 |
| `takeIfAvailable` | take where the count fits, and never enrol | row 260 |
| `release` | release at most what is taken; it answers the free count and whether a waiter is enrolled | row 261 |
| `visit` | one visit of the walk: the next waiter whose count fits leaves the list | row 259 |
| `withdraw` | a waiting request leaves | row 259 |

A waiter is a request's identity, the count that it needs and the stamp of its enrolment. The
stamp is the walk's cursor (the card's section 3,
`docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`): a walk continues at the
selected waiter's stamp plus one. So a walk visits each enrolment at most once, in the order of
enrolment. It skips a waiter that left before its visit, and it reaches a waiter that enrolled
during the walk.

Three properties of the ruled profile are visible in the definitions.

- **A wake reserves nothing.** `visit` leaves `taken` as it is. A permit commits in the
  waiter's own `take`, which checks the count again.
- **A release is total.** `release` subtracts by the truncated subtraction, so it releases at
  most what is taken. This is a stated difference from the pin, where the free count can exceed
  the total. The premise that a release asks for at most `taken` belongs to the public law.
- **A take removes its own request's entry first.** On every state that the wrapper reaches a
  visit has already removed a resumed waiter, so the removal changes nothing there. It is in the
  model so that no transition has a premise on its request.

Placement. These are definitions, with no statement. Concept `reactive-scheduling`: they are
the abstract client of the proposed claim `semaphore-expansion-agrees` (requirement R10). The
profile and its closure are `src/Effect4/Laws/Modules/Semaphore/Profile.lean`. The model states
no order of service across walks, no fairness and no progress of a waiter.
-/

namespace Effect4.Semaphore.Model

/-- A request that waits: its identity, the count that it needs, and the stamp of its
enrolment. -/
structure Waiter where
  id : Nat
  need : Nat
  stamp : Nat
  deriving DecidableEq, Repr

structure State where
  /-- The total. No transition changes it. -/
  permits : Nat
  /-- The permits held. -/
  taken : Nat := 0
  /-- The requests that wait, in the order of enrolment. -/
  waiters : List Waiter := []
  /-- The stamp of the next enrolment. -/
  next : Nat := 0
  deriving DecidableEq, Repr

/-- The semaphore as it is made: nothing taken, no waiter, the stamp zero. -/
def initial (permits : Nat) : State := { permits := permits }

/-- The free count: the total less what is taken. -/
def free (s : State) : Nat := s.permits - s.taken

/-- The waiters without the request `id`. -/
def without (waiters : List Waiter) (id : Nat) : List Waiter :=
  waiters.filter (fun w => w.id != id)

/-- **Take or enrol.** The request's own entry leaves first. Where the count fits the free
count, `taken` gains it, and the answer is `true`. Otherwise the request enrols at the list's
end, at the stamp `next`, and the answer is `false`. -/
def take (s : State) (id n : Nat) : State × Bool :=
  if n ≤ free s then
    ({ s with taken := s.taken + n, waiters := without s.waiters id }, true)
  else
    ({ s with waiters := without s.waiters id ++ [⟨id, n, s.next⟩], next := s.next + 1 }, false)

/-- **Take if available.** Where the count fits, `taken` gains it. It never enrols. -/
def takeIfAvailable (s : State) (n : Nat) : State × Bool :=
  if n ≤ free s then ({ s with taken := s.taken + n }, true) else (s, false)

/-- **Release.** `taken` loses the count, by the truncated subtraction: at most what is taken
(decisions row 261). The answer is the free count after the release, and whether a waiter is
enrolled: the wrapper posts one helper exactly then. -/
def release (s : State) (n : Nat) : State × Nat × Bool :=
  ({ s with taken := s.taken - n }, free { s with taken := s.taken - n }, !s.waiters.isEmpty)

/-- Whether a visit at a cursor may select a waiter: its stamp is at or after the cursor, and
its count fits the free count. -/
def fits (cursor free : Nat) (w : Waiter) : Bool :=
  decide (cursor ≤ w.stamp) && decide (w.need ≤ free)

/-- **One visit of the walk.** Where no permit is free, the visit selects nobody. Otherwise it
selects the first waiter, in the order of enrolment, that is at or after the cursor and whose
count fits. The selected waiter leaves the list: its own `take` follows. `taken` stays. -/
def visit (s : State) (cursor : Nat) : State × Option Waiter :=
  if free s = 0 then (s, none)
  else
    match s.waiters.find? (fits cursor (free s)) with
    | none => (s, none)
    | some w => ({ s with waiters := s.waiters.erase w }, some w)

/-- **Withdraw.** The request's entry leaves. A waiter holds nothing, so nothing else
changes. -/
def withdraw (s : State) (id : Nat) : State := { s with waiters := without s.waiters id }

/-! ## The transitions as one alphabet -/

/-- The model's operations, one for each transition. -/
inductive Op
  | take (id n : Nat)
  | takeIfAvailable (n : Nat)
  | release (n : Nat)
  | visit (cursor : Nat)
  | withdraw (id : Nat)
  deriving DecidableEq, Repr

/-- The state after one operation. -/
def step (s : State) : Op → State
  | .take id n => (take s id n).1
  | .takeIfAvailable n => (takeIfAvailable s n).1
  | .release n => (release s n).1
  | .visit cursor => (visit s cursor).1
  | .withdraw id => withdraw s id

end Effect4.Semaphore.Model

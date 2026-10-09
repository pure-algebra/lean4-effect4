import Effect4.Laws.Library.Semaphore.Profile

/-!
# Semaphore's abstract contract: the named controls and the falsifiers

Finite controls of `src/Effect4/Library/Semaphore/Model.lean` and
`src/Effect4/Laws/Library/Semaphore/Profile.lean`, one input each. They are the executable
falsifiers of the packet `Test/contracts/semaphore.contract.md`.

- The probe's cases P1 to P4, P7 and P9 as traces of the model. The model has no fiber, so a
  trace writes the schedule: which transition runs after which. Each trace ends in the counts
  that the machine gives on the same case (`Test/Program/SemaphoreScenarios.lean`).
- The stated difference from the pin: a release of more than is taken (decisions row 261).
- The profile: one red state for each condition, each transition on one input, and a take by a
  request whose entry is present.
- The faults of the card's section 9 that a transition can show, each red at its own property.

A request is named by a number: A is 1, B is 2 and C is 3. A waiter reads
`(identity, count, stamp)`. Every guard is a finite check of the model. None is a run of a
program, and none states delivery, an order across walks or liveness.
-/

-- A trace's answer is one tuple, and the decision of its equality is one long instance.
set_option synthInstance.maxSize 1024

namespace Test.Program.SemaphoreContract

open Effect4.Semaphore.Model

/-- What a trace reads of a state: what is taken, and each waiter. -/
def view (s : State) : Nat × List (Nat × Nat × Nat) :=
  (s.taken, s.waiters.map fun w => (w.id, w.need, w.stamp))

/-- A total of 2, A holds 2, and B and C wait for 2 and for 1: the state of P1, P4 and P9
before the release. -/
def held : State :=
  let s := (take (initial 2) 1 2).1
  let s := (take s 2 2).1
  (take s 3 1).1

#guard view held = (2, [(2, 2, 0), (3, 1, 1)]) && held.next = 2

/-! ## The cases as traces of the model -/

/-- P1, the protected case. A's hook releases 2. The first visit selects B. B's own take runs
before the next visit, and it takes 2. The next visit finds no free permit. -/
def p1 : (Nat × Bool) × Option Waiter × Bool × Option Waiter × (Nat × List (Nat × Nat × Nat)) :=
  let r := release held 2
  let v1 := visit r.1 0
  let b := take v1.1 2 2
  let v2 := visit b.1 1
  (r.2, v1.2, b.2, v2.2, view v2.1)

-- The release answers 2 free and a waiter enrolled. B is selected and takes. C waits with its
-- first entry.
#guard p1 = ((2, true), some ⟨2, 2, 0⟩, true, none, (2, [(3, 1, 1)]))

/-- P9: P1 where B yields between its resume and its own take. The walk goes on: the second
visit selects C, which takes 1. B's later take does not fit, and B enrols again. -/
def p9 : Option Waiter × Option Waiter × Bool × Option Waiter × Bool ×
    (Nat × List (Nat × Nat × Nat)) :=
  let r := release held 2
  let v1 := visit r.1 0
  let v2 := visit v1.1 1
  let c := take v2.1 3 1
  let v3 := visit c.1 2
  let b := take v3.1 2 2
  (v1.2, v2.2, c.2, v3.2, b.2, view b.1)

-- B's second enrolment has a new stamp: the walk that selected B does not visit it again.
#guard p9 = (some ⟨2, 2, 0⟩, some ⟨3, 1, 1⟩, true, none, false, (1, [(2, 2, 2)]))

/-- P2, the scan case. The requests 10 and 11 hold 1 each. B asks for 2, then C for 1. A release
of 1 follows. The visit passes B and selects C. -/
def p2 : (Nat × Bool) × Option Waiter × Bool × Option Waiter × (Nat × List (Nat × Nat × Nat)) :=
  let s := (take (initial 2) 10 1).1
  let s := (take s 11 1).1
  let s := (take s 2 2).1
  let s := (take s 3 1).1
  let r := release s 1
  let v1 := visit r.1 0
  let c := take v1.1 3 1
  let v2 := visit c.1 2
  (r.2, v1.2, c.2, v2.2, view v2.1)

-- A later smaller request proceeds, and B's entry stays in its place.
#guard p2 = ((1, true), some ⟨3, 1, 1⟩, true, none, (2, [(2, 2, 0)]))

/-- P3, the overtaking case. The request 10 holds 2. B asks for 1, then C for 1. A release of 2
follows. The visit selects B. B takes 1, and B's next request, 4, takes 1 too, before the next
visit. -/
def p3 : Option Waiter × Bool × Bool × Option Waiter × (Nat × List (Nat × Nat × Nat)) :=
  let s := (take (initial 2) 10 2).1
  let s := (take s 2 1).1
  let s := (take s 3 1).1
  let r := release s 2
  let v1 := visit r.1 0
  let b := take v1.1 2 1
  let again := take b.1 4 1
  let v2 := visit again.1 1
  (v1.2, b.2, again.2, v2.2, view v2.1)

-- C waits while B's two requests hold both permits.
#guard p3 = (some ⟨2, 1, 0⟩, true, true, none, (2, [(3, 1, 1)]))

/-- P4, two protected waiters. B's take, body and release run before the next visit. That
visit selects C. -/
def p4 : Option Waiter × (Nat × Bool) × Option Waiter × (Nat × Bool) × Option Waiter ×
    (Nat × List (Nat × Nat × Nat)) :=
  let r := release held 2
  let v1 := visit r.1 0
  let b := take v1.1 2 2
  let rb := release b.1 2
  let v2 := visit rb.1 1
  let c := take v2.1 3 1
  let rc := release c.1 1
  let v3 := visit rc.1 2
  (v1.2, rb.2, v2.2, rc.2, v3.2, view v3.1)

-- B's release still sees C enrolled, so it posts a helper. C's release sees nobody.
#guard p4 = (some ⟨2, 2, 0⟩, (2, true), some ⟨3, 1, 1⟩, (2, false), none, (0, []))

/-- P7, the withdrawal. The request 10 holds the one permit. B waits and withdraws. A request
that is not enrolled withdraws too. -/
def p7 : (Nat × List (Nat × Nat × Nat)) × (Nat × List (Nat × Nat × Nat)) × Bool :=
  let s := (take (initial 1) 10 1).1
  let waiting := (take s 2 1).1
  let gone := withdraw waiting 2
  (view waiting, view gone, decide (withdraw gone 2 = gone))

-- A waiter holds nothing: `taken` does not change.
#guard p7 = ((1, [(2, 1, 0)]), (1, []), true)

/-! ## The stated difference from the pin: a release of more than is taken (row 261) -/

-- P5. A release of 1 with nothing taken, at a total of 2. The pin answers 3 free, and three
-- takers of 1 then proceed. The model releases at most what is taken: it answers 2.
#guard (release (initial 2) 1).2 = (2, false) && (release (initial 2) 1).1 = initial 2
-- Two takers of 1 then proceed, and the third waits.
#guard
  let a := take (initial 2) 1 1
  let b := take a.1 2 1
  let c := take b.1 3 1
  (a.2, b.2, c.2) = (true, true, false)
-- A release within what is taken is the pin's subtraction.
#guard (release held 1).2 = (1, true) && (release held 2).2 = (2, true)

/-! ## The other transitions, one input each -/

-- `takeIfAvailable` takes where the count fits, and it never enrols.
#guard (takeIfAvailable (initial 2) 2).2 = true &&
  view (takeIfAvailable (initial 2) 2).1 = (2, [])
#guard takeIfAvailable held 1 = (held, false)
-- A request for more than the total never fits: it enrols, and no visit selects it.
#guard (take (initial 2) 1 3).2 = false && (visit (take (initial 2) 1 3).1 0).2 = none
-- A visit at a cursor after a waiter's stamp passes that waiter.
#guard (visit (release held 2).1 1).2 = some ⟨3, 1, 1⟩
-- A visit where no permit is free selects nobody, whatever waits.
#guard (visit held 0) = (held, none)

/-! ## The profile -/

/-- The profile on one state, as a Boolean. -/
def inProfile (s : State) : Bool := decide (Profile s)

-- The semaphore as it is made, and a state that the transitions reach.
#guard inProfile (initial 2) && inProfile held
-- Red controls, one for each condition: the accounting; a stamp that does not rise; a stamp
-- that is not below the next stamp; one identity for two waiters.
#guard !inProfile { permits := 2, taken := 3 }
#guard !inProfile { permits := 2, waiters := [⟨1, 1, 1⟩, ⟨2, 1, 0⟩], next := 2 }
#guard !inProfile { permits := 2, waiters := [⟨1, 1, 5⟩], next := 2 }
#guard !inProfile { permits := 2, waiters := [⟨1, 1, 0⟩, ⟨1, 1, 1⟩], next := 2 }

-- Each transition keeps the profile on one input, and it keeps the total.
def ops : List Op :=
  [.take 2 2, .take 4 1, .take 4 3, .takeIfAvailable 1, .release 1, .release 5, .visit 0,
   .visit 1, .withdraw 2, .withdraw 9]

#guard ops.all fun op => inProfile (step held op) && inProfile (step (release held 2).1 op)
#guard ops.all fun op => (step held op).permits = held.permits

-- A take by a request whose entry is present. B takes again while it is enrolled: its first
-- entry leaves, and its new entry joins the end with a new stamp.
#guard view (take held 2 2).1 = (2, [(3, 1, 1), (2, 2, 2)]) && inProfile (take held 2 2).1

/-- Red control of the removal: a take that keeps its request's entry. -/
def takeKeeping (s : State) (id n : Nat) : State × Bool :=
  if n ≤ free s then ({ s with taken := s.taken + n }, true)
  else ({ s with waiters := s.waiters ++ [⟨id, n, s.next⟩], next := s.next + 1 }, false)

-- With the entry kept, the same take leaves two waiters of one identity.
#guard view (takeKeeping held 2 2).1 = (2, [(2, 2, 0), (3, 1, 1), (2, 2, 2)]) &&
  !inProfile (takeKeeping held 2 2).1
-- On a request with no entry the two takes are one.
#guard takeKeeping held 4 1 = take held 4 1

/-! ## The faults of the card's section 9 that a transition can show

Each fault is a changed transition, and it is red at its own property. The other three faults
of that section are faults of the protected form: a take with no hook installed in the same
region, `interruptible` in place of the restore, and a cleanup reported as finished at a
frontier. No transition of this model shows them. They wait for the protected form's slice. -/

/-- Fault: the head of the list alone is woken. -/
def visitHead (s : State) (cursor : Nat) : State × Option Waiter :=
  if free s = 0 then (s, none)
  else
    match s.waiters.head? with
    | some w =>
      if fits cursor (free s) w then ({ s with waiters := s.waiters.erase w }, some w)
      else (s, none)
    | none => (s, none)

/-- The scan case's state at the visit: B waits for 2, C for 1, and 1 permit is free. -/
def scan : State :=
  let s := (take (initial 2) 10 1).1
  let s := (take s 11 1).1
  let s := (take s 2 2).1
  let s := (take s 3 1).1
  (release s 1).1

/-- The right side of `visit_stops_iff`, decided: no permit is free, or no waiter at or after
the cursor fits. -/
def mayStop (s : State) (cursor : Nat) : Bool :=
  decide (free s = 0) ||
    s.waiters.all fun u => !decide (cursor ≤ u.stamp) || decide (free s < u.need)

-- The property: a visit selects nobody exactly when it may stop (`visit_stops_iff`). The
-- head-only visit stops on the scan case, where C fits: C must proceed.
#guard !mayStop scan 0 && (visit scan 0).2 = some ⟨3, 1, 1⟩
#guard (visitHead scan 0).2 = none
-- On the protected case the head fits, and the two visits agree: the scan case tells them
-- apart.
#guard visitHead (release held 2).1 0 = visit (release held 2).1 0

/-- Fault: a resumed request takes without a second check. -/
def takeBlind (s : State) (id n : Nat) : State :=
  { s with taken := s.taken + n, waiters := without s.waiters id }

-- The property: the accounting. On P9's path C took 1 while B yielded. B's blind take then
-- takes 3 of 2 permits, and the state leaves the profile.
#guard
  let r := release held 2
  let v1 := visit r.1 0
  let v2 := visit v1.1 1
  let c := take v2.1 3 1
  view (takeBlind c.1 2 2) = (3, []) && !inProfile (takeBlind c.1 2 2) &&
    inProfile (take c.1 2 2).1
-- On P1's path the blind take finds the permits free, and it is the checked take.
#guard takeBlind (visit (release held 2).1 0).1 2 2 = (take (visit (release held 2).1 0).1 2 2).1

/-- Fault: the wake commits a count for the waiter that it selects, before that waiter runs:
the grant at the wake. -/
def visitGrant (s : State) (cursor : Nat) : State × Option Waiter :=
  match visit s cursor with
  | (next, some w) => ({ next with taken := next.taken + w.need }, some w)
  | stopped => stopped

/-- The overtaking case's state at the first visit: B and C wait for 1 each, and 2 are free. -/
def overtaking : State :=
  let s := (take (initial 2) 10 2).1
  let s := (take s 2 1).1
  let s := (take s 3 1).1
  (release s 2).1

-- The property: a wake reserves nothing (`visit_reserves_nothing`). The grant changes `taken`.
#guard (visit overtaking 0).1.taken = overtaking.taken
#guard (visitGrant overtaking 0).1.taken != overtaking.taken
-- On the overtaking case two granting visits commit B's and C's permits before either runs.
-- B's next request, 4, then waits, and C holds a permit. The model's answer is P3's: C waits.
#guard
  let v1 := visitGrant overtaking 0
  let v2 := visitGrant v1.1 1
  let again := take v2.1 4 1
  (v1.2, v2.2, again.2, view again.1) =
    (some ⟨2, 1, 0⟩, some ⟨3, 1, 1⟩, false, (2, [(4, 1, 2)]))

end Test.Program.SemaphoreContract

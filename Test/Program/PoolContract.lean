import Effect4.Laws.Modules.Pool.Profile
import ProofGraph.Plan

/-!
# Pool's abstract contract: the named controls and the falsifiers

Finite controls of `src/Effect4/Laws/Modules/Pool/Model.lean` and
`src/Effect4/Laws/Modules/Pool/Profile.lean`, one input each. They are the executable
falsifiers of the packet `Test/contracts/pool.contract.md`.

- The probe's cases PP1 to PP5, PP7 and PP8 as traces of the model. The model has no fiber, so
  a trace writes the schedule: which transition runs after which. Each trace reads the cell's
  lists that the machine gives on the same case (`Test/Program/PoolScenarios.lean`).
- PP5 in its two forms: the low-level control at the count 2, and the public retry case.
- PP7 with the close that waits: the close's first step, and the lease that the close waits
  for. The model holds the close's first step alone.
- The profile: one red state for each condition, each transition on one input, and a lease by
  a request whose entry is present.
- A stale lease's return, after the item was leased again.
- The faults of the card's section 9 that a transition or a trace of the model can show, each
  red at its own property.
- The pinned axiom and plan outputs of the proved statements.

A request is named by a number: H is 9, A is 1, B is 2, C is 3 and D is 4. An item reads
`⟨stamp, resource, borrowed, lease⟩`. Every guard is a finite check of the model. None is a run
of a program, and none states delivery, an order across helpers or liveness.
-/

namespace Test.Program.PoolContract

open Effect4.Pool.Model

/-- What a trace reads of a state: the idle stamps, the outstanding leases as pairs of an
item's stamp and a lease's stamp, the waiters, whether the pool is closing, and the next
stamp. -/
def view (s : State) : List Nat × List (Nat × Nat) × List Nat × Bool × Nat :=
  (s.available, leases s, s.waiters, s.closing, s.next)

/-- Each item's stamp and resource: what no transition changes. -/
def kept (s : State) : List (Nat × Nat) := s.items.map fun it => (it.stamp, it.resource)

/-- A pool of one item, at the resource 1. H holds it, and A and then B wait: the state of
PP3 and of PP4 before H's return. -/
def held : State :=
  let s := (lease (initial [1]) 9).1
  let s := (lease s 1).1
  (lease s 2).1

#guard view held = ([], [(0, 0)], [1, 2], false, 1)

/-! ## The cases as traces of the model -/

-- PP1. A leases the item and returns it, then B. B gets the same item, at the next lease's
-- stamp, and the item keeps its resource: no transition removed it.
#guard
  let a := lease (initial [1]) 1
  let ra := giveBack a.1 0 0
  let b := lease ra.1 2
  let rb := giveBack b.1 0 1
  a.2 = (false, some ⟨0, 1, true, 0⟩) && ra.2 = (true, false) &&
    b.2 = (false, some ⟨0, 1, true, 1⟩) && rb.2 = (true, false) &&
    view rb.1 = ([0], [], [], false, 2) && kept rb.1 = [(0, 1)]

-- PP2. Two items, at the resources 1 and 2. A and B hold them. A returns, then B: the idle
-- stamps are `[1, 0]`, B's item at the front. C gets the resource 2, then D the resource 1.
#guard
  let a := lease (initial [1, 2]) 1
  let b := lease a.1 2
  let ra := giveBack b.1 0 0
  let rb := giveBack ra.1 1 1
  let c := lease rb.1 3
  let d := lease c.1 4
  a.2.2 = some ⟨0, 1, true, 0⟩ && b.2.2 = some ⟨1, 2, true, 1⟩ &&
    view rb.1 = ([1, 0], [], [], false, 2) && c.2.2 = some ⟨1, 2, true, 2⟩ &&
    d.2.2 = some ⟨0, 1, true, 3⟩ && view d.1 = ([], [(0, 3), (1, 2)], [], false, 4)

-- PP3. H returns. The item is idle beside two waiters: a state of the profile. One selection
-- at the count 1 takes A. A's own lease takes the item, and B still waits. After A's return
-- the next selection takes B.
#guard
  let rh := giveBack held 0 0
  let s1 := select rh.1 1
  let a := lease s1.1 1
  let ra := giveBack a.1 0 1
  let s2 := select ra.1 1
  let b := lease s2.1 2
  rh.2 = (true, true) && view rh.1 = ([0], [], [1, 2], false, 1) && s1.2 = [1] &&
    view a.1 = ([], [(0, 1)], [2], false, 2) && ra.2 = (true, true) && s2.2 = [2] &&
    view b.1 = ([], [(0, 2)], [], false, 3)

-- PP4. H returns, and A withdraws before the selection. The selection takes the first waiter
-- of the state that it finds: B.
#guard
  let rh := giveBack held 0 0
  let gone := withdraw rh.1 1
  let s1 := select gone 1
  let b := lease s1.1 2
  view gone = ([0], [], [2], false, 1) && s1.2 = [2] &&
    view b.1 = ([], [(0, 1)], [], false, 2)

-- PP8. H holds, and A waits and withdraws. H's return owes no wake. B leases at once.
#guard
  let s := (lease (initial [1]) 9).1
  let waiting := (lease s 1).1
  let gone := withdraw waiting 1
  let rh := giveBack gone 0 0
  let b := lease rh.1 2
  view waiting = ([], [(0, 0)], [1], false, 1) && view gone = ([], [(0, 0)], [], false, 1) &&
    rh.2 = (true, false) && b.2 = (false, some ⟨0, 1, true, 1⟩) &&
    view b.1 = ([], [(0, 1)], [], false, 2)

/-- **The premise state of PP5's low-level control**: the pool is open, the item is idle, and
A and then B wait. No public schedule reaches it: lease or enrol adds a waiter only when no
item is idle, and a return's helper has the count 1. Here it is built by a return whose wake
is not posted. -/
def premise : State := (giveBack held 0 0).1

#guard view premise = ([0], [], [1, 2], false, 1)

-- PP5, the low-level control. One selection at the count 2 removes A and B, in that order,
-- and it reserves nothing: the item is idle after it. A's own lease takes the item, and A
-- returns it. B's own lease then takes it.
#guard
  let s1 := select premise 2
  let a := lease s1.1 1
  let ra := giveBack a.1 0 1
  let b := lease ra.1 2
  s1.2 = [1, 2] && view s1.1 = ([0], [], [], false, 1) && a.2.2 = some ⟨0, 1, true, 1⟩ &&
    ra.2 = (true, false) && b.2.2 = some ⟨0, 1, true, 2⟩ &&
    view b.1 = ([], [(0, 2)], [], false, 3)

-- The control where A holds. B's own lease finds no idle item: a wake reserves nothing. B
-- enrols again.
#guard
  let s1 := select premise 2
  let a := lease s1.1 1
  let b := lease a.1 2
  b.2 = (false, none) && view b.1 = ([], [(0, 1)], [2], false, 2)

-- PP5, the public retry case. H holds and A waits. H returns, and the selection at the count
-- 1 takes A. After it the item is idle, no waiter is enrolled, and no lease is outstanding.
-- A's own lease then takes the item.
#guard
  let s := (lease (initial [1]) 9).1
  let waiting := (lease s 1).1
  let rh := giveBack waiting 0 0
  let s1 := select rh.1 1
  let a := lease s1.1 1
  rh.2 = (true, true) && s1.2 = [1] && view s1.1 = ([0], [], [], false, 1) &&
    a.2.2 = some ⟨0, 1, true, 1⟩ && view a.1 = ([], [(0, 1)], [], false, 2)

-- PP7, with the close that waits (decisions row 268). H holds and W, the request 1, waits.
-- The close's first step begins the close and counts one waiter. The selection at that count
-- takes W, and W's lease is refused. The lease of H is still outstanding: the close waits for
-- it. After H's return no lease is outstanding, and the item is idle in a closing pool. A
-- second close begins nothing.
#guard
  let s := (lease (initial [1]) 9).1
  let waiting := (lease s 1).1
  let c := close waiting
  let s1 := select c.1 c.2.2
  let w := lease s1.1 1
  let rh := giveBack w.1 0 0
  c.2 = (true, 1) && s1.2 = [1] && w.2 = (true, none) && leases w.1 = [(0, 0)] &&
    rh.2 = (true, false) && leases rh.1 = [] && view rh.1 = ([0], [], [], true, 1) &&
    (close rh.1).2 = (false, 0)

/-! ## The profile -/

/-- The profile on one state, as a Boolean. -/
def inProfile (s : State) : Bool := decide (Profile s)

-- The pool as it is made, at three sizes, and three states that the transitions reach.
#guard inProfile (initial [1]) && inProfile (initial [1, 2]) && inProfile (initial [5, 5, 5])
#guard inProfile held && inProfile premise && inProfile (close held).1
-- An idle item beside enrolled waiters is a state of the profile.
#guard premise.available = [0] && premise.waiters = [1, 2] && !premise.closing

-- Red controls, one for each condition. Two items of one stamp.
#guard !inProfile { items := [⟨0, 1, false, 0⟩, ⟨0, 2, false, 0⟩], available := [0] }
-- An idle stamp that names a borrowed item, and an idle stamp that names no item.
#guard !inProfile { items := [⟨0, 1, true, 0⟩], available := [0], next := 1 }
#guard !inProfile { items := [⟨0, 1, false, 0⟩], available := [0, 7] }
-- An item that no lease holds, and that is not idle.
#guard !inProfile { items := [⟨0, 1, false, 0⟩], available := [] }
-- One stamp idle twice.
#guard !inProfile { items := [⟨0, 1, false, 0⟩], available := [0, 0] }
-- Two borrowed items at one lease's stamp.
#guard !inProfile { items := [⟨0, 1, true, 0⟩, ⟨1, 2, true, 0⟩], next := 1 }
-- A lease's stamp that is not below the next stamp.
#guard !inProfile { items := [⟨0, 1, true, 3⟩], next := 2 }
-- One identity for two waiters.
#guard !inProfile { items := [⟨0, 1, true, 0⟩], waiters := [1, 1], next := 1 }
-- An idle item's stale stamp is no lease: two idle items may keep one stamp of a last lease.
#guard inProfile { items := [⟨0, 1, false, 4⟩, ⟨1, 2, false, 4⟩], available := [0, 1], next := 2 }

-- Each transition keeps the profile on one input, and it keeps the items.
def ops : List Op :=
  [.lease 1, .lease 4, .giveBack 0 0, .giveBack 0 5, .giveBack 3 0, .select 0, .select 1,
   .select 5, .withdraw 2, .withdraw 9, .close]

#guard ops.all fun op =>
  inProfile (step held op) && inProfile (step premise op) && inProfile (step (close held).1 op)
#guard ops.all fun op => kept (step held op) = kept held && kept (step premise op) = kept premise

-- A lease by a request whose entry is present. A asks again while it is enrolled, and no item
-- is idle: its first entry leaves, and its new entry joins the end.
#guard view (lease held 1).1 = ([], [(0, 0)], [2, 1], false, 1) && inProfile (lease held 1).1

/-- Red control of the removal: a lease that keeps its request's entry. -/
def leaseKeeping (s : State) (id : Nat) : State × Bool × Option Item :=
  if s.closing then (s, true, none)
  else
    match s.available with
    | [] => ({ s with waiters := s.waiters ++ [id] }, false, none)
    | i :: rest =>
      ({ s with items := mark s.items i s.next, available := rest, next := s.next + 1 }, false,
        leased s.items i s.next)

-- With the entry kept, the same lease leaves two waiters of one identity.
#guard view (leaseKeeping held 1).1 = ([], [(0, 0)], [1, 2, 1], false, 1) &&
  !inProfile (leaseKeeping held 1).1
-- On a request with no entry the two leases are one.
#guard leaseKeeping held 4 = lease held 4

/-! ## The enrolment rule (`lease_enrols_iff`) -/

/-- The right side of `lease_enrols_iff`, decided: the pool is open, and a lease holds every
item. -/
def mayEnrol (s : State) : Bool := !s.closing && s.items.all (·.borrowed)

-- The request is enrolled after the step exactly when the pool is open and no item is idle:
-- at the three states, and for a request that waits already and one that does not.
#guard [held, premise, (close held).1, initial [1, 2]].all fun s =>
  [1, 4].all fun id => decide (id ∈ (lease s id).1.waiters) == mayEnrol s
-- At the premise state an item is idle beside two waiters, and a new request does not enrol:
-- it takes the item.
#guard !mayEnrol premise && (lease premise 4).2 = (false, some ⟨0, 1, true, 1⟩) &&
  (lease premise 4).1.waiters = [1, 2]

/-! ## A stale lease's return -/

-- The lease 0 returns. The item is leased again, at the stamp 1. A second return of the lease
-- 0 changes nothing, and the lease 1 still holds the item (`giveBack_once`, and the frame of a
-- return that holds nothing). The lease 1 then returns.
#guard
  let a := lease (initial [1]) 1
  let ra := giveBack a.1 0 0
  let b := lease ra.1 2
  let stale := giveBack b.1 0 0
  let rb := giveBack stale.1 0 1
  ra.2 = (true, false) && stale = (b.1, false, false) && rb.2 = (true, false) &&
    view rb.1 = ([0], [], [], false, 2)
-- A second return at once changes nothing either.
#guard giveBack (giveBack held 0 0).1 0 0 = ((giveBack held 0 0).1, false, false)

/-! ## The faults of the card's section 9 that the model can show

Each fault is a changed transition or a changed trace, and it is red at its own property. Two
more faults of that section are faults of the close that waits: a close that does not wait,
and a cleanup reported as finished at a frontier. The model holds the close's first step
alone, so they wait for the close's slice. -/

/-- Fault: a return that runs the item's finalizer. The item leaves the pool. -/
def giveBackFinalizing (s : State) (i l : Nat) : State × Bool × Bool :=
  if s.items.any (·.heldBy i l) then
    ({ s with items := s.items.filter fun it => !it.heldBy i l }, true, !s.waiters.isEmpty)
  else (s, false, false)

-- The property: a return keeps every item, and its item is idle at the front
-- (`giveBack_front`). The finalizing return drops the item, and PP1's second borrower gets no
-- item: it enrols.
#guard
  let a := lease (initial [1]) 1
  kept (giveBack a.1 0 0).1 = [(0, 1)] && (giveBack a.1 0 0).1.available = [0] &&
    kept (giveBackFinalizing a.1 0 0).1 = [] &&
    (lease (giveBackFinalizing a.1 0 0).1 2).2 = (false, none)
-- Typing does not tell them apart: both answer the same reply.
#guard (giveBackFinalizing held 0 0).2 = (giveBack held 0 0).2

/-- Fault: a wake that hands an item to each selected waiter. The selection also leases the
front idle item, before any selected waiter runs. -/
def selectHanding (s : State) (count : Nat) : State × List Nat :=
  match s.waiters.take count, s.available with
  | [], _ => select s count
  | _ :: _, [] => select s count
  | selected, i :: rest =>
    ({ s with
        items := mark s.items i s.next, available := rest, waiters := s.waiters.drop count,
        next := s.next + selected.length }, selected)

-- The property: a selection changes the waiters alone (`select_takes_first`). At the premise
-- state the handing selection leaves the item borrowed, and no stamp idle: after it the item
-- is not idle, in both forms of PP5.
#guard (select premise 2).1 = { premise with waiters := [] } && (select premise 2).2 = [1, 2]
#guard (selectHanding premise 2).2 = [1, 2] &&
  view (selectHanding premise 2).1 = ([], [(0, 1)], [], false, 3)
#guard view (selectHanding premise 1).1 = ([], [(0, 1)], [2], false, 2)
-- With no idle item the two selections are one: the fault needs an idle item beside waiters.
#guard selectHanding held 2 = select held 2

-- Fault: a selection made when the wake is posted. On PP4 the selection then runs before A
-- withdraws. It takes A, who leaves, and B is never selected: the item stays idle while B
-- waits. The property: the selection takes the first waiter of the state that the helper
-- finds, which is B.
#guard
  let rh := giveBack held 0 0
  let early := select rh.1 1
  let gone := withdraw early.1 1
  early.2 = [1] && view gone = ([0], [], [2], false, 1)
#guard (select (withdraw (giveBack held 0 0).1 1) 1).2 = [2]

/-- Three requests wait beside an idle item. -/
def three : State := { premise with waiters := [1, 2, 3] }

-- Fault: a selection that reads the list again after each notification. One selection at the
-- count 2 takes A and B: a prefix of the waiters that it finds. Under the changed selection A
-- is taken first. B withdraws during A's work, and the second reading takes C. The requests
-- `[1, 3]` are no prefix of `[1, 2, 3]`.
#guard (select three 2).2 = [1, 2] && (select three 2).1.waiters = [3]
#guard
  let first := select three 1
  let gone := withdraw first.1 2
  let second := select gone 1
  first.2 ++ second.2 = [1, 3] && !([1, 3] : List Nat).isPrefixOf three.waiters
-- With the fixed selection B's withdrawal after the selection changes nothing: C still waits.
#guard (withdraw (select three 2).1 2).waiters = [3]

/-! ## The pinned outputs

Each proved statement's axioms, and its standing as the plan derives it from the proof. The
counts are of this battery's tree, which holds no step of a proof. -/

/-- info: 'Effect4.Pool.Model.profile_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms profile_closed

/-- info: 'Effect4.Pool.Model.lease_enrols_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lease_enrols_iff

/-- info: 'Effect4.Pool.Model.select_takes_first' depends on axioms: [propext] -/
#guard_msgs in
#print axioms select_takes_first

/-- info: 'Effect4.Pool.Model.giveBack_front' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms giveBack_front

/-- info: 'Effect4.Pool.Model.giveBack_once' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms giveBack_once

/-- info: 'Effect4.Pool.Model.close_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms close_refuses

/-- info: 'Effect4.Pool.Model.step_closing' depends on axioms: [propext] -/
#guard_msgs in
#print axioms step_closing

/-- info: 'Effect4.Pool.Model.step_items' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_items

/-- info: 'Effect4.Pool.Model.initial_profile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_profile

/--
info: Effect4.Pool.Model.profile_closed: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.lease_enrols_iff: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.select_takes_first: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.giveBack_front: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.Model.giveBack_once: proved; nearest [Effect4.Pool.Model.giveBack_front]; 0 lemmas, 0 definitions
Effect4.Pool.Model.close_refuses: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status profile_closed lease_enrols_iff select_takes_first giveBack_front giveBack_once
  close_refuses

end Test.Program.PoolContract

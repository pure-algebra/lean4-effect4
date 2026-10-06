import Effect4.Laws.Modules.Queue.Invariant
import ProofGraph.Plan

/-!
# The Queue model's run invariant: its pinned outputs and its finite controls

The invariant `FirstRunInv`, the step law `first_step_inv` and the run law `first_run_inv` are in
`src/Effect4/Laws/Modules/Queue/Invariant.lean`. This battery pins each placed statement's axioms
and its plan status, and holds the finite controls. Each red control keeps every premise but
one, and it has a positive control beside it:

- one red control for each of the six parts of the invariant. Five are Codex's witnesses
  (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-1336-qinv-pool-maskpop/next/review.md`);
- one for each other premise of the step law, `firstOp` and `Requested`, and one for the run
  law's premise at a later prefix;
- the two mutations of the broader model, with the checked reason why neither is a falsifier
  of the step law;
- the step law's conclusion on a finite universe of runs: every step that keeps both premises.

The controls are finite checks of the model's half of two open parts of the semantics registry:
`wait-registration-no-gap` (the part `quiet`) and `waiting-request-obligation-preserved` (the
flag `named`). They run no program, and they deliver no signal.
-/

namespace Test.Program.QueueInvariant
open Effect4.Queue.Model

/-- info: 'Effect4.Queue.Model.first_step_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms first_step_inv

/-- info: 'Effect4.Queue.Model.first_run_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms first_run_inv

/-- info: 'Effect4.Queue.Model.first_run_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms first_run_flags

-- The standing is derived from the proof. The counts are of this battery's tree, which holds
-- no step of the proof: the steps are in the law graph.
/--
info: Effect4.Queue.Model.first_step_inv: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Queue.Model.first_run_inv: proved; nearest [Effect4.Queue.Model.first_step_inv]; 0 lemmas, 0 definitions
Effect4.Queue.Model.first_run_flags: proved; nearest [Effect4.Queue.Model.first_run_inv]; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status first_step_inv first_run_inv first_run_flags

/-! ## The readings of the controls -/

/-- The six parts of the invariant on one run, in the structure's order: the profile, `within`,
`tidy`, `quiet`, and the flags `ok` and `named`. -/
def parts (r : Run) : List Bool :=
  [decide (FirstProfile r.s), within r.s, tidy r.s, quiet r.s r.signalled, r.ok, r.named]

/-- The invariant on one run, as a Boolean. -/
def holds (r : Run) : Bool := decide (FirstRunInv r)

/-- The run's two flags. -/
def flags (r : Run) : Bool × Bool := (r.ok, r.named)

/-- The step law's two premises on one operation: `firstOp` and `Requested`. -/
def requested (r : Run) (op : Op) : Bool := firstOp op && decide (Requested r.s op)

/-- One fault-free step of the model. -/
def next (r : Run) (op : Op) : Run := step .none r op

/-- A positive control: the run holds the invariant, the operation keeps both premises, and the
next run holds the invariant. -/
def kept (r : Run) (op : Op) : Bool := holds r && requested r op && holds (next r op)

def T (id : Nat) : Taker := ⟨id, 1, 1⟩

/-! ## Controls: each part of the invariant is a premise

Each red run holds every part but one. Its step keeps `firstOp` and `Requested`, and the next
run loses a flag. The first five are Codex's witnesses. -/

/-- `within`: a buffer above its capacity. -/
def overfull : Run := { s := { capacity := some 1, messages := [7, 8] } }

#guard parts overfull = [true, false, true, true, true, true]
#guard requested overfull (.dropTake 99) && flags (next overfull (.dropTake 99)) = (false, true)
-- Positive control: the buffer at its capacity.
#guard kept { s := { capacity := some 1, messages := [7] } } (.dropTake 99)

/-- `tidy`: a pending offer beside free room. -/
def untidy : Run := { s := { capacity := some 2, offers := [⟨2, false, [8]⟩] } }

#guard parts untidy = [true, true, false, true, true, true]
#guard requested untidy (.dropTake 99) && flags (next untidy (.dropTake 99)) = (false, true)
-- Positive control: the same offer beside a full buffer.
#guard kept { s := { capacity := some 2, messages := [7, 9], offers := [⟨2, false, [8]⟩] } }
  (.dropTake 99)

/-- `quiet`: a taker stands ready, and no signal named it. A poll passes no waiting taker, so it
changes nothing. -/
def unquiet : Run := { s := { capacity := some 1, messages := [7], takers := [T 5] } }

#guard parts unquiet = [true, true, true, false, true, true]
#guard requested unquiet .poll && flags (next unquiet .poll) = (false, true)
-- Positive control: a signal named the taker.
#guard kept { unquiet with signalled := [5] } .poll

/-- The empty queue of capacity one. -/
def empty : Run := { s := { capacity := some 1 } }

-- `ok` and `named`: a flag is a run's history, and a step never raises one.
#guard parts { empty with ok := false } = [true, true, true, true, false, true]
#guard flags (next { empty with ok := false } (.dropTake 99)) = (false, true)
#guard parts { empty with named := false } = [true, true, true, true, true, false]
#guard flags (next { empty with named := false } (.dropTake 99)) = (true, false)
-- Positive control of both: the same step from the run with both flags.
#guard kept empty (.dropTake 99)

/-- The profile, first control: at capacity zero a pending offer holds no message. The take is
served at the rendezvous, and `pull` drops the offer with no signal. No arm of the model stores
such an offer. -/
def spentOffer : Run := { s := { capacity := some 0, offers := [⟨7, false, []⟩] } }

#guard parts spentOffer = [false, true, true, true, true, true]
#guard requested spentOffer (.take 1 1 1) && flags (next spentOffer (.take 1 1 1)) = (true, false)
-- Positive control: a positive capacity, and a pending offer of one message. The take answers
-- the offerer.
#guard kept { s := { capacity := some 1, messages := [5], offers := [⟨7, false, [8]⟩] } }
  (.take 1 1 1)
#guard (take { capacity := some 1, messages := [5], offers := [⟨7, false, [8]⟩] } (T 1)).2 =
  (.got [5], [⟨7, .offered true⟩])

/-- The profile, second control: a peeker waits, and a take arrives under the peeker's
identity. The take is not served, so `bump` drops the identity from `signalled`, and the peeker
stands beside a message without a signal. -/
def peeked : Run :=
  { s := { capacity := some 1, messages := [7], takers := [T 1], peekers := [5] },
    signalled := [1, 5] }

#guard parts peeked = [false, true, true, true, true, true]
#guard requested peeked (.take 5 1 1) && flags (next peeked (.take 5 1 1)) = (false, true)
-- Positive control: the same take with no peeker.
#guard kept { s := { capacity := some 1, messages := [7], takers := [T 1] }, signalled := [1] }
  (.take 5 1 1)

/-! ## Controls: the other premises of the step law -/

/-- A stored taker of the bounds one and one, ready and signalled. -/
def stored : Run :=
  { s := { capacity := some 2, messages := [7], takers := [T 1] }, signalled := [1] }

-- `firstOp`: the stored request runs again at the minimum two. Its retry is not served, and its
-- stored record is ready: the run loses `ok`. The bounds of a request do not change.
#guard holds stored && !firstOp (.take 1 2 3) && flags (next stored (.take 1 2 3)) = (false, true)
-- Positive control: the request runs again at its own bounds, and it is served.
#guard kept stored (.take 1 1 1) && (take stored.s (T 1)).2.1 = .got [7]

/-- A full buffer and a waiting taker, signalled. -/
def full : Run :=
  { s := { capacity := some 1, messages := [1], takers := [T 1] }, signalled := [1] }

-- `Requested`: an offer under the waiting taker's identity. It pends, and the next state leaves
-- the profile. Both flags stay: this premise guards the profile alone.
#guard holds full && firstOp (.offer 1 5) && !requested full (.offer 1 5)
#guard parts (next full (.offer 1 5)) = [false, true, true, true, true, true]
-- Positive control: an offer under a fresh identity.
#guard kept full (.offer 100 5)

/-! ## Controls: the run law -/

/-- Eight first operations from the empty queue of capacity one: a taker waits, two offers
arrive, a second taker waits behind the first, the first is served, and both leave. -/
def served : List Op :=
  [.take 1 1 1, .offer 100 1, .offer 101 2, .take 2 1 1, .take 1 1 1, .poll, .dropOffer 101,
   .dropTake 2]

#guard decide (FirstOps empty served) && holds (served.foldl (step .none) empty)
#guard (served.foldl (step .none) empty).s.messages = [2]

-- The run law, applied to this list: `decide` proves its premise, and the law gives both flags.
-- Its red control is the guard on `clashing` below: there the premise is false.
example : (served.foldl (step .none) empty).ok = true ∧
    (served.foldl (step .none) empty).named = true :=
  first_run_flags 0 served (by decide)

/-- Red control of the premise at a prefix. Each operation keeps `firstOp` and `Requested` at
the empty queue. The third does not keep `Requested` at the run before it: the taker 1 waits
there. -/
def clashing : List Op := [.take 1 1 1, .offer 100 1, .offer 1 5]

#guard clashing.all (requested empty)
#guard !decide (FirstOps empty clashing)
#guard parts (clashing.foldl (step .none) empty) = [false, true, true, true, true, true]
-- Positive control: the first two operations keep the premise, and the run holds the invariant.
#guard decide (FirstOps empty (clashing.take 2)) && holds ((clashing.take 2).foldl (step .none) empty)

/-! ## Controls: the two mutations of the broader model are no falsifiers of the step law

`Fault.closing` and `Fault.shutdown` stay red controls of the broader model. Each drops the
signals of one operation, and `firstOp` refuses both operations. -/

/-- A fault changes no first operation. So no fault makes a step of the step law lose a flag.
Without the premise the equation is false at `close` and at `shutdown`: the guards below. -/
example (fault : Fault) (r : Run) (op : Op) (first : firstOp op = true) :
    step fault r op = step .none r op := by
  cases op with
  | close e => exact absurd first Bool.false_ne_true
  | shutdown => exact absurd first Bool.false_ne_true
  | _ => rfl

/-- A taker of the bounds two and two behind one message. Closing lowers its threshold. -/
def closingRun : Run := { s := { capacity := some 2, messages := [7], takers := [⟨5, 2, 2⟩] } }

-- `Fault.closing`: the close names nobody, and the run loses `ok`. Positive control: `Fault.none`.
#guard flags (step .closing closingRun (.close .ended)) = (false, true)
#guard flags (step .none closingRun (.close .ended)) = (true, true)
-- It is outside the step law twice: the operation, and the taker's bounds.
#guard !firstOp (.close .ended) && parts closingRun = [false, true, true, true, true, true]

/-- A full buffer with a pending offer. The state is of the profile. -/
def shutdownRun : Run :=
  { s := { capacity := some 1, messages := [7], offers := [⟨2, false, [8]⟩] } }

-- `Fault.shutdown`: the shutdown names nobody. The three properties of the state hold, and the
-- run loses `named`. Positive control: `Fault.none`.
#guard flags (step .shutdown shutdownRun .shutdown) = (true, false)
#guard flags (step .none shutdownRun .shutdown) = (true, true)
-- It is outside the step law once: the operation.
#guard !firstOp .shutdown && holds shutdownRun

/-! ## Controls: the step law on a finite universe of runs

The universe holds runs that no list of operations reaches: the step law quantifies over every
run of the invariant. -/

/-- Every ordered list of distinct elements of a list, by fuel. -/
def arrange : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, xs => [] :: xs.flatMap fun x => (arrange n (xs.filter (· != x))).map (x :: ·)

def sublists : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (sublists xs).flatMap fun l => [l, x :: l]

/-- Capacities one and two; four buffers, one above each capacity; every order of the takers 1
to 3 and of the offers 4 and 5; sixteen signal histories. -/
def runs : List Run := Id.run do
  let mut out := []
  for c in [1, 2] do
    for ms in [[], [7], [7, 8], [7, 8, 9]] do
      for ts in arrange 3 [1, 2, 3] do
        for os in arrange 2 [4, 5] do
          for sig in sublists [1, 2, 3, 4] do
            out := { s := { capacity := some c, messages := ms, takers := ts.map T,
                            offers := os.map (⟨·, false, [10]⟩) },
                     signalled := sig } :: out
  return out

/-- The first operations over the identities 1 to 6: the takers' 1 to 3, the offers' 4 and 5,
and the fresh 6. -/
def ops : List Op :=
  .poll :: [1, 2, 3, 4, 5, 6].flatMap fun id =>
    [.take id 1 1, .offer id 20, .dropTake id, .dropOffer id]

/-- The runs of the universe; those that hold the invariant; the steps from them that keep both
premises; and the steps among these that leave the invariant. -/
def census : Nat × Nat × Nat × Nat := Id.run do
  let mut held := 0
  let mut steps := 0
  let mut left := 0
  for r in runs do
    if holds r then
      held := held + 1
      for op in ops do
        if requested r op then
          steps := steps + 1
          if !holds (next r op) then left := left + 1
  return (runs.length, held, steps, left)

#guard census = (10240, 2008, 44608, 0)

-- Red control of the census: with the part `quiet` dropped from the premise, steps lose a flag.
#guard runs.any fun r =>
  parts r == [true, true, true, false, true, true] &&
    ops.any fun op => requested r op && flags (next r op) != (true, true)

-- The Boolean reading agrees with the six parts, on every run of the universe.
#guard runs.all fun r => holds r == (parts r).all id

end Test.Program.QueueInvariant

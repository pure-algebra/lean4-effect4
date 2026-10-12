import Effect4.Api
import Effect4.Api.Frontier
import Effect4.Laws.Machine.Behaviour

/-!
Finite evaluations of schedule independence (decisions row 361): every tape of enabled `fire`
decisions to a depth bound, on small programs, read through the machine's observation `obs`
(`src/Effect4/Laws/Machine/Behaviour.lean`): every fiber's exit and the whole store. No theorem
covers them; the checked fragment's proof is slice D2 of Codex's review
(`docs/research/2026-10-10-deterministic-fragment-review/REVIEW.md`).

A fire is enabled when its owner is armed and its budget suffices. A tape ends finished (every
fiber has exited), stuck, waiting (nothing armed, a fiber unexited: DET-OW-03), at a fuel
frontier, or at the depth bound. Controls: two programs whose finished tapes end at two
observations; nested forks, whose ids follow the schedule (DET-OW-05); an update whose answers
differ by schedule though the root's exit and the cells agree (DET-OW-04); a wait that the old
reading called complete; and the two orders of one diamond, which differ in the minted token and
the trace.
-/
set_option autoImplicit false

namespace Test.Machine.Runtime.ScheduleIndependence
open Effect4 Effect4.Machine Effect4.Program

abbrev M := Api.Machine
abbrev Dn := Api.Decision

def fuel : Nat := 400

def n (i : Nat) : Term := .lit (.nat i)
def v (i : Nat) : Term := .var i
def pair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))
def app1 (f : String) (a : Term) : Term := .app f (.cons a .nil)
def app2 (f : String) (a b : Term) : Term := .app f (.cons a (.cons b .nil))
/-- A forked child that the dispatcher starts later. -/
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def fork (p : NativeEff) : NativeEff := .withFiber (.fork p later)
def join (i : Nat) : NativeEff := .awaitFiber (v i) .joinEffect
def seq : List NativeEff → NativeEff
  | [] => .succeed (.lit .unit)
  | [p] => p
  | p :: ps => .bind p (seq ps)

/-- Why an explored tape stops. -/
inductive Ending | depth | stuck | finished | waiting | fuel
  deriving DecidableEq

/-- One decision, with its sufficiency receipt. -/
def stepD (p : NativeEff) (m : M) (d : Dn) : M × Bool :=
  letI := evaluatorFor p []
  stepDecisionState (interpOf p []) fuel m d

/-- The root started. -/
def start (p : NativeEff) : M := (stepD p (Api.load p fuel) Api.evaluate).1

/-- A narrower reading, for the control of DET-OW-04: the root's exit and the reference heap. -/
def rootObs (m : M) := ((m.fiber? Api.root).bind RunFiber.exit, m.state.refs)

/-- How a tape with nothing armed ends: stuck, finished, or waiting on something no fire gives. -/
def ending (m : M) : Ending :=
  if m.stuck.isSome then .stuck else if m.finished then .finished else .waiting

/-- Every tape of enabled `fire` decisions to depth `k`: its length, the machine it ends at and why
it stops. -/
def explore (p : NativeEff) : Nat → M → List (Nat × M × Ending)
  | 0, m => [(0, m, .depth)]
  | k + 1, m =>
    match m.armed with
    | [] => [(0, m, ending m)]
    | owners =>
      owners.flatMap fun o =>
        let r := stepD p m (.fire o)
        if r.2 then (explore p k r.1).map fun (t, mf, why) => (t + 1, mf, why)
        else [(1, r.1, .fuel)]

/-- The tapes to depth 12. -/
def tapes (p : NativeEff) : List (Nat × M × Ending) := explore p 12 (start p)

/-- How the tapes end, without repeats. -/
def endings (p : NativeEff) : List Ending := ((tapes p).map fun (_, _, why) => why).eraseDups

/-- The finished tapes. -/
def finishedTapes (p : NativeEff) : List (Nat × M × Ending) :=
  (tapes p).filter fun (_, _, why) => why == .finished

/-- The distinct observations of the finished tapes. -/
def observations (p : NativeEff) := ((finishedTapes p).map fun (_, m, _) => obs m).eraseDups

/-- The distinct root readings of the finished tapes. -/
def rootObservations (p : NativeEff) := ((finishedTapes p).map fun (_, m, _) => rootObs m).eraseDups

/-- The distinct lengths of the finished tapes. -/
def lengths (p : NativeEff) : List Nat := ((finishedTapes p).map fun (t, _, _) => t).eraseDups

/-- Two children each yield first, then write their own cell. -/
def pIndepY : NativeEff := seq
  [ .perform .refMake (n 0)
  , .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 0) (n 1))])
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 1) (n 2))])
  , join 2, join 3
  , .perform .refGet (v 0), .perform .refGet (v 1)
  , .succeed (pair (v 6) (v 7)) ]

/-- Two children each yield first, then update one cell by commuting functions. -/
def pCommuteY : NativeEff := seq
  [ .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, .perform (.refUpdateWith (app1 "succ" (v 2))) (v 0)])
  , fork (seq [.yieldNow 0, .perform (.refUpdateWith (app1 "succ" (v 3))) (v 0)])
  , join 1, join 2
  , .perform .refGet (v 0) ]

/-- A child yields, then completes a promise; the root awaits it. -/
def pKahnY : NativeEff := seq
  [ .perform (.deferredMakeOf .nat .never) (.lit .unit)
  , fork (seq [.yieldNow 0, .perform .deferredSucceed (pair (v 0) (n 5))])
  , .perform .deferredAwait (v 0)
  , join 1
  , .succeed (v 2) ]

/-- Two children each yield, then fork a grandchild and join it: ids are minted in the order of
the schedule. -/
def pForkInChild : NativeEff := seq
  [ .perform .refMake (n 0)
  , .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, fork (.perform .refSet (pair (v 0) (n 1))), join 3])
  , fork (seq [.yieldNow 0, fork (.perform .refSet (pair (v 1) (n 2))), join 4])
  , join 2, join 3
  , .perform .refGet (v 0), .perform .refGet (v 1)
  , .succeed (pair (v 6) (v 7)) ]

/-- Two children each yield first, then write the same cell. -/
def pRaceY : NativeEff := seq
  [ .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 0) (n 1))])
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 0) (n 2))])
  , join 1, join 2
  , .perform .refGet (v 0) ]

/-- Two children each yield first, then update one cell by functions that do not commute. -/
def pNoCommuteY : NativeEff := seq
  [ .perform .refMake (n 1)
  , fork (seq [.yieldNow 0, .perform (.refUpdateWith (app1 "succ" (v 2))) (v 0)])
  , fork (seq [.yieldNow 0, .perform (.refUpdateWith (app2 "mul" (v 3) (n 2))) (v 0)])
  , join 1, join 2
  , .perform .refGet (v 0) ]

/-- Two children each yield, then add one to one cell and answer the new value: the cell ends
alike on every schedule, and the answers do not. -/
def pReturned : NativeEff := seq
  [ .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, .perform (.refUpdateAndGetWith (app1 "succ" (v 2))) (v 0)])
  , fork (seq [.yieldNow 0, .perform (.refUpdateAndGetWith (app1 "succ" (v 3))) (v 0)])
  , join 1, join 2
  , .perform .refGet (v 0) ]

/-- The root awaits a promise that nothing completes. -/
def pWait : NativeEff := seq
  [ .perform (.deferredMakeOf .nat .never) (.lit .unit)
  , .perform .deferredAwait (v 0) ]

-- Every tape of enabled fires finishes within the bound, at one observation and one length; the
-- root reads the value of that one observation.
#guard endings pIndepY = [.finished]
#guard (observations pIndepY).length = 1
#guard rootObservations pIndepY = [(some (.success (.list [.nat 1, .nat 2])), [.nat 1, .nat 2])]
#guard lengths pIndepY = [3]
#guard endings pCommuteY = [.finished]
#guard (observations pCommuteY).length = 1
#guard rootObservations pCommuteY = [(some (.success (.nat 2)), [.nat 2])]
#guard lengths pCommuteY = [3]
#guard endings pKahnY = [.finished]
#guard (observations pKahnY).length = 1
#guard rootObservations pKahnY = [(some (.success (.nat 5)), [])]
#guard lengths pKahnY = [2]

-- Red controls: two writes of one cell, and two updates that do not commute, end at two
-- observations, so the exploration tells schedules apart.
#guard (observations pRaceY).length = 2
#guard (observations pNoCommuteY).length = 2

-- Control of minted names (DET-OW-05): each child forks a grandchild after its yield, so the
-- grandchildren's ids follow the schedule. The root and the cells agree on every schedule, and
-- the exits, read by id, do not. Exact `obs` excludes nested forks from the first fragment, and
-- a comparison up to a renaming of names waits (decisions row 361, point 2).
#guard endings pForkInChild = [.finished]
#guard rootObservations pForkInChild = [(some (.success (.list [.nat 1, .nat 2])), [.nat 1, .nat 2])]
#guard (observations pForkInChild).length = 2
#guard lengths pForkInChild = [5]

-- Control of the observation (DET-OW-04): the root's exit and the cells agree on every schedule,
-- and the children's answers do not. So a reading of the root and the cells alone would call
-- this program independent of its schedule.
#guard (rootObservations pReturned).length = 1
#guard (observations pReturned).length = 2

-- Control of the ending (DET-OW-03): nothing is armed and the root has not exited. The reading
-- that called every unarmed machine complete called this one complete. Its frontier is empty,
-- so it is deadlocked (`frontier_empty_iff_deadlocked`, `src/Effect4/Laws/Api/Frontier.lean`).
#guard endings pWait = [.waiting]
#guard (tapes pWait).all fun (_, m, _) => Api.frontierReasons .tape m == []

/-- The two orders of `pIndepY`'s first diamond: its two children fired after the root. -/
def orders (p : NativeEff) : M × M :=
  let m := (stepD p (start p) (.fire Api.root)).1
  ((stepD p (stepD p m (.fire ⟨1⟩)).1 (.fire ⟨2⟩)).1,
    (stepD p (stepD p m (.fire ⟨2⟩)).1 (.fire ⟨1⟩)).1)

-- Control of what is observed: the two orders have one `obs`, and differ in the minted token and
-- the trace's length. So `obs` leaves out the trace and the token supply, and an observation
-- that kept them would tell these schedules apart.
#guard obs (orders pIndepY).1 == obs (orders pIndepY).2
#guard (orders pIndepY).1.nextToken != (orders pIndepY).2.nextToken
#guard (orders pIndepY).1.trace.length != (orders pIndepY).2.trace.length

end Test.Machine.Runtime.ScheduleIndependence

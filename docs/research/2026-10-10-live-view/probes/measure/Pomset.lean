import Effect4.Api

/-!
# Probe: is a run's per-fiber history schedule-invariant?

For a program run to the end under two orders of `fire` decisions, the probe projects the
machine's trace onto each fiber: the frame events of that fiber (`RunEvent.frame`), its fork and
its exit. It compares the two runs' histories as multisets of per-fiber sequences (fiber ids
forgotten), and the whole traces' lengths.
-/

open Effect4 Effect4.Machine Effect4.Program

namespace PomsetProbe

abbrev M := Api.Machine
abbrev Dn := Api.Decision
def fuel : Nat := 400
def n (i : Nat) : Term := .lit (.nat i)
def v (i : Nat) : Term := .var i
def pair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))
def app1 (f : String) (a : Term) : Term := .app f (.cons a .nil)
def app2 (f : String) (a b : Term) : Term := .app f (.cons a (.cons b .nil))
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def fork (p : NativeEff) : NativeEff := .withFiber (.fork p later)
def join (i : Nat) : NativeEff := .awaitFiber (v i) .joinEffect
def seq : List NativeEff → NativeEff
  | [] => .succeed (.lit .unit)
  | [p] => p
  | p :: ps => .bind p (seq ps)

def stepD (p : NativeEff) (m : M) (d : Dn) : M :=
  letI := evaluatorFor p []
  (stepDecisionState (interpOf p []) fuel m d).1
def start (p : NativeEff) : M := stepD p (Api.load p fuel) Api.evaluate

/-- Run to the end, firing the armed owner that `pick` chooses each time. -/
def runWith (p : NativeEff) (pick : List FiberId → FiberId) : Nat → M → M
  | 0, m => m
  | k + 1, m => match m.armed with
    | [] => m
    | os => runWith p pick k (stepD p m (.fire (pick os)))

/-- The kind of each event, by name. -/
def kindsOf (m : M) : List String := m.trace.map fun
  | .forked .. => "forked" | .started .. => "started" | .scheduledTask .. => "scheduledTask"
  | .ranTask .. => "ranTask" | .yieldInjected .. => "yieldInjected" | .parkedOn .. => "parkedOn"
  | .resumedWith .. => "resumedWith" | .observerFired .. => "observerFired" | .frame .. => "frame"
  | .exited .. => "exited" | _ => "other"

/-- Each fiber's frame events, in order. -/
def histories (m : M) := m.fibers.map fun f => m.trace.filterMap fun
    | .frame g e => if g == f.id then some e else none
    | _ => none

def sameMultiset {α : Type} [DecidableEq α] (a b : List α) : Bool :=
  a.length == b.length && a.all fun x => a.count x == b.count x

def kinds (m : M) : List (String × Nat) :=
  let ks := kindsOf m
  ks.eraseDups.map fun k => (k, ks.count k)

def compareOrders (name : String) (p : NativeEff) : IO Unit := do
  let a := runWith p (fun os => os.headD ⟨0⟩) 20 (start p)
  let b := runWith p (fun os => os.getLastD ⟨0⟩) 20 (start p)
  IO.println s!"{name}: trace lengths {a.trace.length} and {b.trace.length}; per-fiber histories equal as multisets: {sameMultiset (histories a) (histories b)}; frame events {(histories a).map (·.length)} and {(histories b).map (·.length)}"
  IO.println s!"    kinds, first order:  {kinds a}"
  IO.println s!"    kinds, second order: {kinds b}"

def pIndepY : NativeEff := seq
  [ .perform .refMake (n 0), .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 0) (n 1))])
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 1) (n 2))])
  , join 2, join 3
  , .perform .refGet (v 0), .perform .refGet (v 1)
  , .succeed (pair (v 6) (v 7)) ]
def pRaceY : NativeEff := seq
  [ .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 0) (n 1))])
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 0) (n 2))])
  , join 1, join 2
  , .perform .refGet (v 0) ]
def pCommuteY : NativeEff := seq
  [ .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, .perform (.refUpdateWith (app1 "succ" (v 2))) (v 0)])
  , fork (seq [.yieldNow 0, .perform (.refUpdateWith (app1 "succ" (v 3))) (v 0)])
  , join 1, join 2
  , .perform .refGet (v 0) ]

end PomsetProbe

open PomsetProbe in
#eval show IO Unit from do
  compareOrders "pIndepY" pIndepY
  compareOrders "pCommuteY" pCommuteY
  compareOrders "pRaceY" pRaceY

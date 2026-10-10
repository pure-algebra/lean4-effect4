import Effect4.Api

/-!
# Probe: do the machine's scheduling decisions commute?

A finite probe against the real machine (`Api.load`, `stepDecisionState`). For a few small
programs it starts the root (`Api.evaluate`) and then explores every tape of `fire` decisions,
one per armed owner, to a depth bound. It reports:

- the distinct observations of the complete tapes: the root's exit and the reference heap;
- the lengths of the complete tapes;
- at each reachable machine, for each two different armed owners, whether firing them in the
  two orders reaches the same machine, read component by component.
-/

open Effect4 Effect4.Machine Effect4.Program

namespace TapeProbe

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

/-- One decision, with its sufficiency receipt. -/
def stepD (p : NativeEff) (m : M) (d : Dn) : M × Bool :=
  letI := evaluatorFor p []
  stepDecisionState (interpOf p []) fuel m d

def start (p : NativeEff) : M := (stepD p (Api.load p fuel) Api.evaluate).1

def renderExit : Option Api.ExitV → String
  | none => "live"
  | some (.success x) => s!"success {toString (repr x)}"
  | some (.failure _) => "failure"

/-- What a complete tape is read as: the root's exit and the reference heap. -/
def obs (m : M) : String :=
  s!"{renderExit ((m.fiber? Api.root).bind RunFiber.exit)} | refs {(m.state.refs.map fun x => toString (repr x))}"

/-- Every tape of `fire` decisions to depth `k`, with the machine it ends at. A tape stops when
nothing is armed (complete), at a fuel frontier, or at the depth bound. -/
def explore (p : NativeEff) : Nat → M → List (List Dn × M × String)
  | 0, m => [([], m, "depth")]
  | k + 1, m =>
    match m.armed with
    | [] => [([], m, if m.stuck.isSome then "stuck" else "complete")]
    | owners =>
      owners.flatMap fun o =>
        let r := stepD p m (.fire o)
        if r.2 then (explore p k r.1).map fun (t, mf, why) => (.fire o :: t, mf, why)
        else [([.fire o], r.1, "fuel")]

def ids (t : List Dn) : List String := t.filterMap fun
  | .fire o => some s!"f{o.value}"
  | .yieldVerdict o b => some s!"y{o.value}{if b then "" else "-"}"
  | _ => none

/-- The live fibers that have not exited. -/
def live (m : M) : List FiberId := (m.fibers.filter fun f => f.exit.isNone).map (·.id)

/-- Tapes of `fire` decisions and, at most `ys` times, a `yieldVerdict f true` for a live fiber
`f`: the host's preemption point. -/
def exploreY (p : NativeEff) : Nat → Nat → M → List (List Dn × M × String)
  | 0, _, m => [([], m, "depth")]
  | k + 1, ys, m =>
    match m.armed with
    | [] => [([], m, if m.stuck.isSome then "stuck" else "complete")]
    | owners =>
      let fires := owners.flatMap fun o =>
        let r := stepD p m (.fire o)
        if r.2 then (exploreY p k ys r.1).map fun (t, mf, why) => (.fire o :: t, mf, why)
        else [([.fire o], r.1, "fuel")]
      let yields := match ys with
        | 0 => []
        | ys + 1 => (live m).flatMap fun f =>
          let r := stepD p m (.yieldVerdict f true)
          (exploreY p k ys r.1).map fun (t, mf, why) => (.yieldVerdict f true :: t, mf, why)
      fires ++ yields

/-- The distinct observations of complete tapes with preemption, with their tape lengths. -/
def summaryY (p : NativeEff) (depth ys : Nat) : List (String × List Nat) :=
  let done := (exploreY p depth ys (start p)).filter fun (_, _, why) => why == "complete"
  let keys := (done.map fun (_, m, _) => obs m).eraseDups
  keys.map fun key => (key, ((done.filter fun (_, m, _) => obs m == key).map fun (t, _, _) =>
    t.length).eraseDups)

/-- The distinct observations of complete tapes, each with the tape lengths that reach it. -/
def summary (p : NativeEff) (depth : Nat) : List (String × List Nat) :=
  let runs := explore p depth (start p)
  let done := runs.filter fun (_, _, why) => why == "complete"
  let keys := (done.map fun (_, m, _) => obs m).eraseDups
  keys.map fun key => (key, ((done.filter fun (_, m, _) => obs m == key).map fun (t, _, _) =>
    t.length).eraseDups)

def endings (p : NativeEff) (depth : Nat) : List String :=
  ((explore p depth (start p)).map fun (_, _, why) => why).eraseDups

/-! ## The local diamond, component by component -/

/-- Which components of two machines differ. -/
def diff (a b : M) : List String :=
  (if a.state == b.state then [] else ["stores"]) ++
  (if a.armed == b.armed then [] else
    if a.armed.length == b.armed.length && a.armed.all (b.armed.contains ·) then ["armed order"]
    else ["armed set"]) ++
  (if a.nextId == b.nextId then [] else ["nextId"]) ++
  (if (a.fibers.map (·.id)) == (b.fibers.map (·.id)) then [] else ["fiber ids"]) ++
  (if (a.fibers.map (·.exit)) == (b.fibers.map (·.exit)) then [] else ["exits"]) ++
  (if (a.fibers.map fun f => (f.id, f.exit, f.parked, f.dispatcher.buckets.length)) ==
      (b.fibers.map fun f => (f.id, f.exit, f.parked, f.dispatcher.buckets.length)) then []
    else ["fiber records"]) ++
  (if a.races.length == b.races.length then [] else ["races"]) ++
  (if a.nextToken == b.nextToken then [] else [s!"nextToken {a.nextToken} vs {b.nextToken}"]) ++
  (if a.nextRace == b.nextRace then [] else ["nextRace"]) ++
  (if a.stuck.isSome == b.stuck.isSome then [] else ["stuck"]) ++
  (if a.forks.length == b.forks.length then [] else ["forks"]) ++
  (if (a.fibers.map fun f => (f.id, f.parked)) == (b.fibers.map fun f => (f.id, f.parked)) then []
    else [s!"parks {a.fibers.map fun f => (f.id.value, repr f.parked)} vs {b.fibers.map fun f => (f.id.value, repr f.parked)}"]) ++
  (if a.trace.length == b.trace.length then [] else ["trace length"])

/-- At every machine the exploration reaches, every two armed owners fired in both orders. -/
def diamonds (p : NativeEff) (depth : Nat) : List (List String × Nat × Nat × List String) :=
  let reach : List (List Dn × M) := (List.range (depth + 1)).flatMap fun k =>
    (explore p k (start p)).map fun (t, m, _) => (t, m)
  let reach := reach.filter fun (_, m) => m.armed.length ≥ 2
  reach.flatMap fun (t, m) =>
    m.armed.flatMap fun o1 => m.armed.filterMap fun o2 =>
      if o1.value < o2.value then
        let a := (stepD p (stepD p m (.fire o1)).1 (.fire o2)).1
        let b := (stepD p (stepD p m (.fire o2)).1 (.fire o1)).1
        some (ids t, o1.value, o2.value, diff a b)
      else none

/-! ## The programs -/

/-- Two children write different cells; the root joins both and reads both. -/
def pIndep : NativeEff := seq
  [ .perform .refMake (n 0)                                   -- r0 at 0
  , .perform .refMake (n 0)                                   -- r1 at 1
  , fork (.perform .refSet (pair (v 0) (n 1)))                -- f0 at 2
  , fork (.perform .refSet (pair (v 1) (n 2)))                -- f1 at 3
  , join 2, join 3                                            -- 4, 5
  , .perform .refGet (v 0), .perform .refGet (v 1)            -- 6, 7
  , .succeed (pair (v 6) (v 7)) ]

/-- Two children write the same cell. -/
def pRace : NativeEff := seq
  [ .perform .refMake (n 0)
  , fork (.perform .refSet (pair (v 0) (n 1)))
  , fork (.perform .refSet (pair (v 0) (n 2)))
  , join 1, join 2
  , .perform .refGet (v 0) ]

/-- Two children update the same cell by the same function: the updates commute. -/
def pCommute : NativeEff := seq
  [ .perform .refMake (n 0)
  , fork (.perform (.refUpdateWith (app1 "succ" (v 1))) (v 0))   -- f0 at 1: current at 1
  , fork (.perform (.refUpdateWith (app1 "succ" (v 2))) (v 0))   -- f1 at 2: current at 2
  , join 1, join 2
  , .perform .refGet (v 0) ]

/-- Two children update the same cell by functions that do not commute. -/
def pNoCommute : NativeEff := seq
  [ .perform .refMake (n 1)
  , fork (.perform (.refUpdateWith (app1 "succ" (v 1))) (v 0))
  , fork (.perform (.refUpdateWith (app2 "mul" (v 2) (n 2))) (v 0))
  , join 1, join 2
  , .perform .refGet (v 0) ]

/-- A child completes a promise; the root awaits it: a monotone read. -/
def pKahn : NativeEff := seq
  [ .perform (.deferredMakeOf .nat .never) (.lit .unit)       -- d at 0
  , fork (.perform .deferredSucceed (pair (v 0) (n 5)))       -- f at 1
  , .perform .deferredAwait (v 0)                             -- x at 2
  , join 1
  , .succeed (v 2) ]

/-- A child completes a promise; the root polls it: a read that is not monotone. -/
def pPoll : NativeEff := seq
  [ .perform (.deferredMakeOf .nat .never) (.lit .unit)
  , fork (.perform .deferredSucceed (pair (v 0) (n 5)))
  , .perform .deferredPoll (v 0) ]

/-- Two children each yield first, then write the same cell. -/
def pRaceY : NativeEff := seq
  [ .perform .refMake (n 0)
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 0) (n 1))])
  , fork (seq [.yieldNow 0, .perform .refSet (pair (v 0) (n 2))])
  , join 1, join 2
  , .perform .refGet (v 0) ]

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

/-- Two children each yield first, then update one cell by functions that do not commute. -/
def pNoCommuteY : NativeEff := seq
  [ .perform .refMake (n 1)
  , fork (seq [.yieldNow 0, .perform (.refUpdateWith (app1 "succ" (v 2))) (v 0)])
  , fork (seq [.yieldNow 0, .perform (.refUpdateWith (app2 "mul" (v 3) (n 2))) (v 0)])
  , join 1, join 2
  , .perform .refGet (v 0) ]

/-- A child yields, then completes a promise; the root awaits it. -/
def pKahnY : NativeEff := seq
  [ .perform (.deferredMakeOf .nat .never) (.lit .unit)
  , fork (seq [.yieldNow 0, .perform .deferredSucceed (pair (v 0) (n 5))])
  , .perform .deferredAwait (v 0)
  , join 1
  , .succeed (v 2) ]

/-- Two children each yield, then fork a grandchild and join it: ids are minted by order. -/
def pForkInChild : NativeEff := seq
  [ .perform .refMake (n 0)                                   -- r0 at 0
  , .perform .refMake (n 0)                                   -- r1 at 1
  , fork (seq [.yieldNow 0, fork (.perform .refSet (pair (v 0) (n 1))), join 3])   -- at 2
  , fork (seq [.yieldNow 0, fork (.perform .refSet (pair (v 1) (n 2))), join 4])   -- at 3
  , join 2, join 3
  , .perform .refGet (v 0), .perform .refGet (v 1)
  , .succeed (pair (v 6) (v 7)) ]

/-- The root's start, preempted at once by the tape, before it polls. -/
def startPreempted (p : NativeEff) : M :=
  let m := (stepD p (Api.load p fuel) (.yieldVerdict Api.root true)).1
  (stepD p m Api.evaluate).1

/-- One child writes twice around a yield; another reads the cell into a second cell. -/
def pYield : NativeEff := seq
  [ .perform .refMake (n 0)                                   -- r0 at 0
  , .perform .refMake (n 0)                                   -- r1 at 1
  , fork (seq [.perform .refSet (pair (v 0) (n 1)), .yieldNow 0,
               .perform .refSet (pair (v 0) (n 3))])          -- at 2
  , fork (.bind (.perform .refGet (v 0)) (.perform .refSet (pair (v 1) (v 3))))  -- at 3
  , join 2, join 3
  , .perform .refGet (v 1) ]

#eval ("pIndep", summary pIndep 12, endings pIndep 12)
#eval ("pIndep diamonds", (diamonds pIndep 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pIndep preempt", summaryY pIndep 12 2)
#eval ("pRace", summary pRace 12, endings pRace 12)
#eval ("pRace diamonds", (diamonds pRace 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pRace preempt", summaryY pRace 12 2)
#eval ("pCommute", summary pCommute 12, endings pCommute 12)
#eval ("pCommute diamonds", (diamonds pCommute 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pCommute preempt", summaryY pCommute 12 2)
#eval ("pNoCommute", summary pNoCommute 12, endings pNoCommute 12)
#eval ("pNoCommute diamonds", (diamonds pNoCommute 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pNoCommute preempt", summaryY pNoCommute 12 2)
#eval ("pKahn", summary pKahn 12, endings pKahn 12)
#eval ("pKahn diamonds", (diamonds pKahn 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pKahn preempt", summaryY pKahn 12 2)
#eval ("pPoll", summary pPoll 12, endings pPoll 12)
#eval ("pPoll diamonds", (diamonds pPoll 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pPoll preempt", summaryY pPoll 12 2)
#eval ("pYield", summary pYield 12, endings pYield 12)
#eval ("pYield diamonds", (diamonds pYield 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pYield preempt", summaryY pYield 12 2)
#eval ("pRaceY", summary pRaceY 12, endings pRaceY 12)
#eval ("pRaceY diamonds", (diamonds pRaceY 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pRaceY preempt", summaryY pRaceY 12 2)
#eval ("pIndepY", summary pIndepY 12, endings pIndepY 12)
#eval ("pIndepY diamonds", (diamonds pIndepY 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pIndepY preempt", summaryY pIndepY 12 2)
#eval ("pCommuteY", summary pCommuteY 12, endings pCommuteY 12)
#eval ("pCommuteY diamonds", (diamonds pCommuteY 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pCommuteY preempt", summaryY pCommuteY 12 2)
#eval ("pNoCommuteY", summary pNoCommuteY 12, endings pNoCommuteY 12)
#eval ("pNoCommuteY diamonds", (diamonds pNoCommuteY 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pNoCommuteY preempt", summaryY pNoCommuteY 12 2)
#eval ("pKahnY", summary pKahnY 12, endings pKahnY 12)
#eval ("pKahnY diamonds", (diamonds pKahnY 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pKahnY preempt", summaryY pKahnY 12 2)

#eval ("pForkInChild", summary pForkInChild 12)
#eval ("pForkInChild diamonds", (diamonds pForkInChild 12).filter fun (_, _, _, d) => !d.isEmpty)
#eval ("pPoll, root preempted", (exploreY pPoll 12 0 (startPreempted pPoll)).map fun (t, m, why) =>
  (ids t, why, obs m))
#eval ("pKahn, root preempted", ((exploreY pKahn 12 0 (startPreempted pKahn)).map fun (_, m, why) =>
  (why, obs m)).eraseDups)
/-- The trace of each order at the first diamond of `pIndepY`. -/
def traces (p : NativeEff) : Nat × Nat :=
  let m := (stepD p (start p) (.fire Api.root)).1
  let a := (stepD p (stepD p m (.fire ⟨1⟩)).1 (.fire ⟨2⟩)).1
  let b := (stepD p (stepD p m (.fire ⟨2⟩)).1 (.fire ⟨1⟩)).1
  (a.trace.length - m.trace.length, b.trace.length - m.trace.length)
#eval ("pIndepY trace growth, 1 then 2 and 2 then 1", traces pIndepY)

end TapeProbe

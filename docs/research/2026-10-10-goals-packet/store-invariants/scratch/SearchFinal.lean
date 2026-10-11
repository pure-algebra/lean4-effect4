import Test.Dogfood.Scenario.Atomic

/-!
# Search: a bounded search of the shop's scripts (finite probes)

The search counts of `README.md` come from this file: `lake env lean` on it prints them. Each
line is a finite probe on the Lean machine, outside any proof.

A shop's machine moves only by control decisions (`scenario_control`, `Probe.lean`), so the
search plays control decisions only. Each move goes through the scenario's own `step`, at the
battery's budget. Every node of the search is a script, so a run against a goal at any prefix
counts.

1. Every script of at most five moves over a 13-move alphabet, from the opened run.
2. Every script of at most four moves over the same alphabet, after `started` and after
   `refilled`.
3. Random walks after `start` over a 64-move alphabet: every fiber of the shop and one more, both
   verdicts, four clock steps. A fixed seed makes them repeatable.
4. Red controls: the search of depth 4 on the racy, erased and undone shops.

Each report gives the nodes, the runs against each goal, and how often each goal's premise or
edge is met: request 2's planted failure, six completed requests, a full window, an interruption,
a rejection. The per-move tally gives each move's verdicts: progressed, frontier, refused.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Probe.StoreInvariants.Search

open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario.Atomic
open Test.Dogfood.Scenario (Move)

/-! ## The alphabets -/

/-- The exhaustive search's moves. -/
def alphabet : List (String × Move) :=
  [ ("start", Move.start), ("flush", Move.flush), ("tick1000", Move.tick 1000),
    ("tick500", Move.tick 500), ("cancel0", Move.cancel ⟨0⟩), ("cancel1", Move.cancel ⟨1⟩),
    ("cancel2", Move.cancel ⟨2⟩), ("cancel3", Move.cancel ⟨3⟩),
    ("yield3", .control (.yieldVerdict ⟨3⟩ true)), ("eval3", .control (.evaluate ⟨3⟩)),
    ("fire0", .control (.fire ⟨0⟩)), ("middleware", .control .installMiddleware),
    ("interrupt3by5", .control (.interruptFrom (some ⟨5⟩) .empty ⟨3⟩)) ]

/-- The random walks' moves: every fiber of the shop and one more, both verdicts, four clock
steps. The moves that make progress come six times, so a walk runs its requests. -/
def wide : List (String × Move) :=
  let fibers : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  let progress : List (String × Move) :=
    [("flush", Move.flush), ("fire0", .control (.fire ⟨0⟩)), ("tick500", Move.tick 500),
     ("tick1000", Move.tick 1000)]
  progress ++ progress ++ progress ++ progress ++ progress ++ progress ++
  [("start", Move.start), ("middleware", .control .installMiddleware),
   ("tick1", Move.tick 1), ("tick1500", Move.tick 1500)] ++
  fibers.map (fun f => (s!"cancel{f}", Move.cancel ⟨f⟩)) ++
  fibers.map (fun f => (s!"yield{f}", .control (.yieldVerdict ⟨f⟩ true))) ++
  fibers.map (fun f => (s!"noyield{f}", .control (.yieldVerdict ⟨f⟩ false))) ++
  fibers.map (fun f => (s!"eval{f}", .control (.evaluate ⟨f⟩))) ++
  fibers.map (fun f => (s!"fire{f}", .control (.fire ⟨f⟩))) ++
  fibers.map (fun f => (s!"interrupt{f}by{(f + 1) % 8}",
    .control (.interruptFrom (some ⟨(f + 1) % 8⟩) .empty ⟨f⟩)))

/-! ## The tally -/

structure Tally where
  nodes : Nat := 0
  boundedFails : Nat := 0
  countedFails : Nat := 0
  committedFails : Nat := 0
  firstFails : List (String × List String) := []
  premise : Nat := 0
  allSix : Nat := 0
  fullWindow : Nat := 0
  interrupted : Nat := 0
  rejected : Nat := 0
  distinct : List Observation := []
  /-- Per move: progressed, frontier, refused. -/
  acts : List (String × Nat × Nat × Nat) := []

def isInterrupted : RequestOutcome → Bool
  | .interrupted _ => true
  | _ => false

def bump (b : Bool) (n : Nat) : Nat := if b then n + 1 else n

/-- One node's observation, against the three goals. -/
def note (keep : Bool) (t : Tally) (path : List String) (o : Observation) : Tally :=
  let okB := decide (o.used ≤ 3)
  let okC := o.counted
  let okM := o.decisions[1]? != some .failedBehind || o.committed
  let first :=
    if t.firstFails.length < 3 then
      (if okB then [] else [("bounded", path)]) ++ (if okC then [] else [("counted", path)]) ++
        (if okM then [] else [("committed", path)])
    else []
  { t with
    nodes := t.nodes + 1
    boundedFails := bump (!okB) t.boundedFails
    countedFails := bump (!okC) t.countedFails
    committedFails := bump (!okM) t.committedFails
    firstFails := t.firstFails ++ first
    premise := bump (o.decisions[1]? == some .failedBehind) t.premise
    allSix := bump (o.completed == 6) t.allSix
    fullWindow := bump (o.used == 3) t.fullWindow
    interrupted := bump (o.decisions.any isInterrupted) t.interrupted
    rejected := bump (o.decisions.contains .rejected) t.rejected
    distinct := if !keep || t.distinct.contains o then t.distinct else o :: t.distinct }

/-- 0 progressed, 1 frontier, 2 refused or preflight. -/
def phaseKind : Option Api.HostSession.Phase → Nat
  | some .progressed => 0
  | some .frontier => 1
  | _ => 2

/-- One move's verdict, by its name. -/
def act (t : Tally) (name : String) (s : Run) : Tally :=
  let k := phaseKind s.phases.getLast?
  let add := fun (e : String × Nat × Nat × Nat) =>
    if e.1 == name then
      (e.1, e.2.1 + bump (k == 0) 0, e.2.2.1 + bump (k == 1) 0, e.2.2.2 + bump (k == 2) 0)
    else e
  if t.acts.any (·.1 == name) then { t with acts := t.acts.map add }
  else { t with acts := t.acts ++ [add (name, 0, 0, 0)] }

/-! ## The searches -/

/-- Every script of at most `depth` moves over `alphabet`, each child stepped from its parent. -/
def explore : Nat → List String → Run → Tally → Tally
  | 0, path, s, t => note true t path (observe s)
  | d + 1, path, s, t =>
    alphabet.foldl (fun t (name, m) =>
      let s' := Test.Dogfood.Scenario.step s m
      explore d (path ++ [name]) s' (act t name s')) (note true t path (observe s))

def lcg (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

def walkLoop : Nat → Run → List String → UInt64 → Tally → Tally × UInt64
  | 0, _, _, x, t => (t, x)
  | k + 1, s, path, x, t =>
    let x' := lcg x
    let (name, m) := wide[(x' >>> 33).toNat % wide.length]?.getD ("flush", Move.flush)
    let s' := Test.Dogfood.Scenario.step s m
    let path' := path ++ [name]
    walkLoop k s' path' x' (note false (act t name s') path' (observe s'))

/-- `count` random walks of `len` moves after `start`. -/
def walks (b : Api.Built) (count len : Nat) (seed : UInt64) : Tally :=
  ((List.range count).foldl (fun (acc : Tally × UInt64) _ =>
    let s := Test.Dogfood.Scenario.step (opened b) Move.start
    walkLoop len s ["start"] acc.2 acc.1) ({}, seed)).1

def report (label : String) (t : Tally) : String :=
  s!"{label}: nodes {t.nodes}, runs against bounded {t.boundedFails}, counted {t.countedFails}, committed {t.committedFails}; request 2 failed behind {t.premise}, six completed {t.allSix}, used 3 {t.fullWindow}, an interruption {t.interrupted}, a rejection {t.rejected}, distinct observations {t.distinct.length}; first runs against a goal {t.firstFails}"

def built (fault : Fault) : Option Api.Built := (Effect4.Api.Author.build (shop fault)).toOption

/-! ## 1. Every script of at most five moves -/

#eval (built .none).map fun b =>
  let t := explore 5 [] (opened b) {}
  (report "depth 5 from the opened run" t, t.acts)

/-! ## 2. Every script of at most four moves after two battery states -/

#eval (built .none).map fun b =>
  report "depth 4 after started" (explore 4 [] (Test.Dogfood.Scenario.play (opened b) started) {})

#eval (built .none).map fun b =>
  report "depth 4 after refilled" (explore 4 [] (Test.Dogfood.Scenario.play (opened b) refilled) {})

/-! ## 3. Random walks -/

#eval (built .none).map fun b =>
  let t := walks b 20000 24 0x2545F4914F6CDD1D
  (report "20000 walks of 24 moves after start" t, t.acts)

/-! ## 4. Red controls: the faulty shops -/

#eval (built .racy).map fun b => report "racy, depth 4" (explore 4 [] (opened b) {})
#eval (built .erased).map fun b => report "erased, depth 4" (explore 4 [] (opened b) {})
#eval (built .undone).map fun b => report "undone, depth 4" (explore 4 [] (opened b) {})

end Probe.StoreInvariants.Search

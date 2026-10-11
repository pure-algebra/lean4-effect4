import Test.Dogfood.Scenario.Workers

/-! Scratch: a bounded search for a repeated identity in the crew's `released` cell. A finite
probe. Every prefix of every script is checked, since the goal ranges over all scripts. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Test.Dogfood.Scenario
open Test.Dogfood.Scenario.Workers

namespace Scratch.SearchWorkers

/-- The goal's reading: the released cell holds no identity twice. -/
def releasedOnly (s : Run) : Bool := decide (observe s).cleanups.Nodup

abbrev NEvent := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

def registersAt (q : List Nat) : NEvent → Bool
  | .frame _ (.pushed (.onSuccess _ (.afterScopeAdd _ (.foreign c)))) => c.path == q
  | _ => false

def releaseStartsAt (q : List Nat) : NEvent → Bool
  | .frame _ (.pushed (.onSuccess _ (.releaseUnder p _ _))) => p.path == q
  | _ => false

def crewAcquire : Nat → List Nat
  | 1 => [1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0]

/-- The planned goals' inequalities at a run: R11 per registration, the once-placed count, and
the bridge, for both workers. -/
def planned (s : Run) : Bool :=
  let tr := s.machine.trace
  let log := entries (cell s 1)
  log.all (fun v => v == .nat 1 || v == .nat 2) &&
  [1, 2].all fun i =>
    decide (tr.countP (releaseStartsAt (crewAcquire i)) ≤ tr.countP (registersAt (crewAcquire i))) &&
    decide (tr.countP (registersAt (crewAcquire i)) ≤ 1) &&
    decide (log.count (.nat i) ≤ tr.countP (releaseStartsAt (crewAcquire i)))

/-- The goal's reading and the planned goals' inequalities. -/
def released (s : Run) : Bool := releasedOnly s && planned s

/-- Play a script, checking the reading after every move. The first failing prefix's length, or
`none`. -/
def firstBad (check : Run → Bool) (s : Run) (moves : List Move) : Option Nat :=
  (moves.foldl (fun (acc : Run × Nat × Option Nat) mv =>
    match acc.2.2 with
    | some n => (acc.1, acc.2.1, some n)
    | none =>
      let s' := Test.Dogfood.Scenario.step acc.1 mv
      (s', acc.2.1 + 1, if check s' then none else some (acc.2.1 + 1))) (s, 0, if check s then none else some 0)).2.2

/-- The moves of the search: host acts and raw controls. -/
def alphabet : List Move :=
  [ .start, .flush, .hold w1, .hold w2
  , .receive w1 (ok (.nat 1)), .receive w2 (ok (.nat 2)), .apply w1, .apply w2
  , .receive w1 (ok .unit), .receive w2 (failed "JobFailed" "x")
  , .cancel ⟨0⟩, .cancel ⟨1⟩, .cancel ⟨2⟩, .tick 1000
  , .row (.control (.yieldVerdict ⟨1⟩ true)), .row (.control (.evaluate ⟨1⟩))
  , .row (.control (.fire ⟨0⟩)), .row (.control (.interruptFrom (some ⟨1⟩) .empty ⟨2⟩))
  , .row (.control .installMiddleware) ]

/-- Every script of `depth` moves over the alphabet. -/
def scripts : Nat → List (List Move)
  | 0 => [[]]
  | n + 1 => (scripts n).flatMap fun ms => alphabet.map fun mv => ms ++ [mv]

def build? (m : Module NativeOp) : Option Api.Built := (Effect4.Api.Author.build m).toOption

/-- The search: from a base script, every extension of `depth` moves, at a budget. The failing
scripts' count and the first one. -/
def search (b : Api.Built) (budget : Api.Budget) (base : List Move) (depth : Nat) :
    Nat × Nat × Option (List Move) :=
  let s0 := Test.Dogfood.Scenario.play (Run.open b "workers" budget) base
  (scripts depth).foldl (fun (acc : Nat × Nat × Option (List Move)) ms =>
    match firstBad released s0 ms with
    | none => (acc.1 + 1, acc.2.1, acc.2.2)
    | some _ => (acc.1 + 1, acc.2.1 + 1, acc.2.2.orElse fun _ => some ms)) (0, 0, none)

def timed (label : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{label}: {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  ({t1 - t0} ms)"

/-- Scripts of the lowest-fiber schedule and the cancellations, cut short at every length: the
fuel sweep plays them at each command budget. -/
def sweepScripts : List (List Move) :=
  [lowest, script [running, [.cancel ⟨2⟩], finish], script [parked, [.cancel ⟨0⟩]],
   script [running, [.cancel ⟨2⟩, .cancel ⟨2⟩, .cancel ⟨1⟩, .cancel ⟨0⟩]],
   script [parked, takes, [.apply w1, .cancel ⟨1⟩, .apply w2, .cancel ⟨0⟩, .flush]]]

/-- A fuel sweep: every budget in a range, every sweep script, checked at every prefix. -/
def sweep (b : Api.Built) (fuels : List Nat) (compileFuel : Nat) : Nat × Nat × Option (Nat × Nat) :=
  fuels.foldl (fun (acc : Nat × Nat × Option (Nat × Nat)) fuel =>
    let s0 := Run.open b "workers" { fuel := fuel, compileFuel := compileFuel }
    (sweepScripts.zipIdx).foldl (fun (acc : Nat × Nat × Option (Nat × Nat)) (ms, i) =>
      match firstBad released s0 ms with
      | none => (acc.1 + 1, acc.2.1, acc.2.2)
      | some _ => (acc.1 + 1, acc.2.1 + 1, acc.2.2.orElse fun _ => some (fuel, i))) acc) (0, 0, none)

#eval show IO Unit from do
  for total in [0, 1, 2, 3] do
    match build? (crew total) with
    | none => IO.println s!"total {total}: no build"
    | some b =>
      timed s!"total {total}: depth 3 from parked" fun _ =>
        let (n, bad, ex) := search b Workers.budget parked 3
        s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
      timed s!"total {total}: depth 3 from running" fun _ =>
        let (n, bad, ex) := search b Workers.budget running 3
        s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
      timed s!"total {total}: depth 3 from the cancelled run" fun _ =>
        let (n, bad, ex) := search b Workers.budget (script [running, [.cancel ⟨2⟩]]) 3
        s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
      timed s!"total {total}: fuel 0..300, compile fuel 2000" fun _ =>
        let (n, bad, ex) := sweep b (List.range 301) 2000
        s!"{n} runs, {bad} failing, first {repr ex}"
      timed s!"total {total}: compile fuel 0..120, fuel 1000" fun _ =>
        let (n, bad, ex) := (List.range 121).foldl (fun (acc : Nat × Nat × Option Nat) cf =>
          let (n, bad, _) := sweep b [1000] cf
          (acc.1 + n, acc.2.1 + bad, if bad > 0 then acc.2.2.orElse fun _ => some cf else acc.2.2)) (0, 0, none)
        s!"{n} runs, {bad} failing, first {repr ex}"
  -- the red control: the crew that registers each release twice
  match build? (crewWith true 2) with
  | none => IO.println "twice: no build"
  | some faulty =>
    timed "red control, twice crew: depth 2 from parked" fun _ =>
      let (n, bad, ex) := search faulty Workers.budget parked 2
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "red control, twice crew: fuel 0..300" fun _ =>
      let (n, bad, ex) := sweep faulty (List.range 301) 2000
      s!"{n} runs, {bad} failing, first {repr ex}"

end Scratch.SearchWorkers

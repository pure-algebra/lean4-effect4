import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch: a bounded search for a repeated identity in the queue crew's `released` cell, with
no `funded` premise: every prefix of every script is checked, funded or cut. A finite probe. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Test.Dogfood.Scenario
open Test.Dogfood.Scenario.QueueWorkers

namespace Scratch.SearchQueueSmall

def releasedOnly (s : Run) : Bool := (observe s).releasedOnce

abbrev NEvent := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

def registersAt (q : List Nat) : NEvent → Bool
  | .frame _ (.pushed (.onSuccess _ (.afterScopeAdd _ (.foreign c)))) => c.path == q
  | _ => false

def releaseStartsAt (q : List Nat) : NEvent → Bool
  | .frame _ (.pushed (.onSuccess _ (.releaseUnder p _ _))) => p.path == q
  | _ => false

def queueAcquire : Nat → List Nat
  | 1 => [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]

def planned (s : Run) : Bool :=
  let tr := s.machine.trace
  let log := entries (cell s 2)
  log.all (fun v => v == .nat 1 || v == .nat 2 || v == .nat 3) &&
  [1, 2, 3].all fun i =>
    decide (tr.countP (releaseStartsAt (queueAcquire i)) ≤ tr.countP (registersAt (queueAcquire i))) &&
    decide (tr.countP (registersAt (queueAcquire i)) ≤ 1) &&
    decide (log.count (.nat i) ≤ tr.countP (releaseStartsAt (queueAcquire i)))

def released (s : Run) : Bool := releasedOnly s && planned s

def firstBad (check : Run → Bool) (s : Run) (moves : List Move) : Option Nat :=
  (moves.foldl (fun (acc : Run × Nat × Option Nat) mv =>
    match acc.2.2 with
    | some n => (acc.1, acc.2.1, some n)
    | none =>
      let s' := Test.Dogfood.Scenario.step acc.1 mv
      (s', acc.2.1 + 1, if check s' then none else some (acc.2.1 + 1))) (s, 0, if check s then none else some 0)).2.2

def alphabet : List Move :=
  [ .start, .flush, .hold feederCall, .hold w1, .hold w2
  , .receive feederCall (ok (.nat 7)), .apply feederCall
  , .receive w1 (ok .unit), .receive w2 (failed "JobFailed" "x"), .apply w1, .apply w2
  , .cancel ⟨0⟩, .cancel ⟨1⟩, .cancel ⟨2⟩, .cancel ⟨3⟩
  , .row (.control (.yieldVerdict ⟨1⟩ true)), .row (.control (.evaluate ⟨2⟩))
  , .row (.control (.fire ⟨3⟩)), .row (.control (.interruptFrom (some ⟨1⟩) .empty ⟨3⟩)) ]

def scripts : Nat → List (List Move)
  | 0 => [[]]
  | n + 1 => (scripts n).flatMap fun ms => alphabet.map fun mv => ms ++ [mv]

def build? (m : Module NativeOp) : Option Api.Built := (Effect4.Api.Author.build m).toOption

def search (b : Api.Built) (fuel : Nat) (base : List Move) (depth : Nat) :
    Nat × Nat × Option (List Move) :=
  let s0 := Test.Dogfood.Scenario.play (openedAt fuel b) base
  (scripts depth).foldl (fun (acc : Nat × Nat × Option (List Move)) ms =>
    match firstBad released s0 ms with
    | none => (acc.1 + 1, acc.2.1, acc.2.2)
    | some _ => (acc.1 + 1, acc.2.1 + 1, acc.2.2.orElse fun _ => some ms)) (0, 0, none)

def sweepScripts : List (List Move) :=
  [ script [running, cancelWaiting, afterWaiting]
  , script [blocked, closing]
  , script [running, [.cancel ⟨2⟩], afterRunning]
  , script [blocked, [.cancel ⟨0⟩]]
  , script [blocked, [.cancel ⟨3⟩, .cancel ⟨1⟩, .cancel ⟨2⟩, .cancel ⟨0⟩, .flush]] ]

/-- A fuel sweep: how many runs, how many are cut (not funded), how many fail the reading. -/
def sweep (b : Api.Built) (fuels : List Nat) : Nat × Nat × Nat × Option (Nat × Nat) :=
  fuels.foldl (fun (acc : Nat × Nat × Nat × Option (Nat × Nat)) fuel =>
    (sweepScripts.zipIdx).foldl (fun (acc : Nat × Nat × Nat × Option (Nat × Nat)) (ms, i) =>
      let played := Test.Dogfood.Scenario.play (openedAt fuel b) ms
      let cut := if funded played then 0 else 1
      match firstBad released (openedAt fuel b) ms with
      | none => (acc.1 + 1, acc.2.1 + cut, acc.2.2.1, acc.2.2.2)
      | some _ => (acc.1 + 1, acc.2.1 + cut, acc.2.2.1 + 1,
          acc.2.2.2.orElse fun _ => some (fuel, i))) acc) (0, 0, 0, none)

def timed (label : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.eprintln s!"{label}: {r}"
  let t1 ← IO.monoMsNow
  IO.eprintln s!"  ({t1 - t0} ms)"

/-- A smaller set of budget-sweep scripts: the whole run with a cancellation, and the root's
cancellation at the full buffer. -/
def smallSweepScripts : List (List Move) :=
  [ script [running, cancelWaiting, afterWaiting]
  , script [blocked, [.cancel ⟨0⟩]] ]

def smallSweep (b : Api.Built) (fuels : List Nat) : Nat × Nat × Nat × Option (Nat × Nat) :=
  fuels.foldl (fun (acc : Nat × Nat × Nat × Option (Nat × Nat)) fuel =>
    (smallSweepScripts.zipIdx).foldl (fun (acc : Nat × Nat × Nat × Option (Nat × Nat)) (ms, i) =>
      let played := Test.Dogfood.Scenario.play (openedAt fuel b) ms
      let cut := if funded played then 0 else 1
      match firstBad released (openedAt fuel b) ms with
      | none => (acc.1 + 1, acc.2.1 + cut, acc.2.2.1, acc.2.2.2)
      | some _ => (acc.1 + 1, acc.2.1 + cut, acc.2.2.1 + 1,
          acc.2.2.2.orElse fun _ => some (fuel, i))) acc) (0, 0, 0, none)

#eval show IO Unit from do
  match build? (crew 3) with
  | none => IO.println "no build"
  | some b =>
    timed "one script from parked: a flush" fun _ =>
      let s0 := Test.Dogfood.Scenario.play (openedAt budget.fuel b) parked
      s!"{repr (firstBad released s0 [.flush])}"
    timed "one script from parked: a cancellation of worker 1" fun _ =>
      let s0 := Test.Dogfood.Scenario.play (openedAt budget.fuel b) parked
      s!"{repr (firstBad released s0 [.cancel ⟨1⟩])}"
    timed "the named run closed, checked at every prefix" fun _ =>
      s!"{repr (firstBad released (opened b) (script [blocked, closing]))}"

#eval show IO Unit from do
  match build? (crew 3) with
  | none => IO.println "no build"
  | some b =>
    timed "total 3: depth 1 from parked, running and blocked" fun _ =>
      let (n1, bad1, _) := search b budget.fuel parked 1
      let (n2, bad2, _) := search b budget.fuel running 1
      let (n3, bad3, _) := search b budget.fuel blocked 1
      s!"{n1 + n2 + n3} scripts, {bad1 + bad2 + bad3} failing"

#eval show IO Unit from do
  match build? (crew 3) with
  | none => IO.println "no build"
  | some b =>
    timed "total 3: fuel 0, 8, .., 200 on two scripts, every run checked, funded or cut" fun _ =>
      let (n, cut, bad, ex) := smallSweep b ((List.range 26).map (· * 8))
      s!"{n} runs, {cut} cut, {bad} failing, first {repr ex}"

#eval show IO Unit from do
  match build? (crewWith .twice 3) with
  | none => IO.println "twice: no build"
  | some faulty =>
    timed "red control, twice crew: fuel 0, 8, .., 200 on two scripts" fun _ =>
      let (n, cut, bad, ex) := smallSweep faulty ((List.range 26).map (· * 8))
      s!"{n} runs, {cut} cut, {bad} failing, first {repr ex}"

end Scratch.SearchQueueSmall

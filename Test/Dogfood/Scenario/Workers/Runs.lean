import Test.Dogfood.Scenario.Workers.Program

/-! Data shared by the scenario battery and fixture writers. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Workers

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession (Key Reply)
open Test.Dogfood.P3WorkerQueue (take runJob)

/-! ## 2. The scripts -/

/-- The budgets of every run of this battery, the ones `P3WorkerQueue.runPool` plays at. -/
def budget : Api.Budget := { fuel := 1000, compileFuel := 2000 }

/-- A built program opened under the scenario's name. -/
def opened (b : Api.Built) : Run := Run.open b "workers" budget

/-- Worker 1 and worker 2, by the fibers the root forks them as. -/
def w1 : Sel := .fiber ⟨1⟩
def w2 : Sel := .fiber ⟨2⟩

/-- Both workers park on `Jobs.take`, and the host holds both calls. -/
def parked : List Move := [.start, .flush, .hold w1, .hold w2]

/-- The session receives both replies: job 1 for worker 1, job 2 for worker 2. -/
def takes : List Move := [.receive w1 (ok (.nat 1)), .receive w2 (ok (.nat 2))]

/-- Both replies applied, worker 1's first, and the host holds both `Jobs.run` calls. -/
def running : List Move := script [parked, takes, [.apply w1, .apply w2, .hold w1, .hold w2]]

/-- The lowest-fiber schedule of today, as moves: the host holds every call, and it answers
worker 1's calls only. Job 2 fails, as the fixture of `P3WorkerQueue.hostAnswer` fails it. -/
def lowest : List Move :=
  script [parked, answer w1 (ok (.nat 1)), [.hold w1], answer w1 (ok .unit), [.hold w1],
    answer w1 (ok (.nat 2)), [.hold w1], answer w1 (failed "JobFailed" "bad payload")]

/-- After worker 2's cancellation, worker 1 finishes job 1, takes job 2 and finishes it. -/
def finish : List Move :=
  script [answer w1 (ok .unit), [.hold w1], answer w1 (ok (.nat 2)), [.hold w1],
    answer w1 (ok .unit)]

/-- A reply written by hand, for a red control: the session's name, a call's number and a key.
A driven reply is never written by hand: `Rows.reply` builds it from the call's claim. -/
def forged (callId fiber token : Nat) (completion : Api.HostSession.Answer) : Reply :=
  ⟨Api.HostSession.version, "workers", callId, ⟨⟨fiber⟩, token⟩, completion⟩

/-- The scenario's named runs: each script of a control, once, from one build of each program.
Every run but the last is on the crew. The last plays the lowest-fiber schedule on the crew that
registers each release twice. The order is the order in which the controls first read the runs,
and the host lane performs them in it. -/
def runsOf (b faulty : Api.Built) : List NamedRun :=
  let run := fun (name : String) (parts : List (List Move)) =>
    (⟨name, opened b, script parts⟩ : NamedRun)
  [ run "parked" [parked]
  , run "received" [parked, takes]
  , run "received-reversed" [parked, takes.reverse]
  , run "duplicate" [parked, takes, [.receive w1 (ok (.nat 1))]]
  , run "applied-2" [parked, takes, [.apply w2]]
  , run "applied-1-2" [parked, takes, [.apply w1, .apply w2]]
  , run "applied-2-1" [parked, takes, [.apply w2, .apply w1]]
  , run "crossed" [parked, [.wire (.submit (forged 0 2 2 (ok (.nat 1))))]]
  , run "unreceived" [parked, [.apply w2]]
  , run "applied-1" [parked, takes, [.apply w1]]
  , run "stale" [parked, takes,
      [.apply w1, .wire (.submit (forged 0 1 1 (ok (.nat 1)))), .wire (.apply ⟨⟨1⟩, 1⟩)]]
  , run "cancelled-running" [running, [.cancel ⟨2⟩]]
  , run "cancelled-early" [parked, [.cancel ⟨2⟩, .receive w2 (ok (.nat 2))]]
  , run "cancelled-between" [parked, takes, [.cancel ⟨2⟩, .apply w2, .apply w1]]
  , run "cancelled-root" [parked, [.cancel ⟨0⟩]]
  , run "lowest" [lowest]
  , run "cancelled" [running, [.cancel ⟨2⟩], finish]
  , ⟨"twice", opened faulty, lowest⟩ ]


/-- The programs of this scenario, each admitted once. -/
def builtInputs : Option (Api.Built × Api.Built) := do
  let b ← P3WorkerQueue.built? (crew 2)
  let faulty ← P3WorkerQueue.built? (crewWith true 2)
  pure (b, faulty)

/-- One inventory of the named scripts, read by every lane. -/
def runSet : RunSet :=
  { name := "workers"
    runs := match builtInputs with
      | some (b, faulty) => runsOf b faulty
      | none => [] }

end Test.Dogfood.Scenario.Workers

import Test.Dogfood.P3WorkerQueue
import Test.Dogfood.Scenario.Workers.Runs
import Test.Dogfood.Scenario
import Test.Dogfood.Scenario.Workers.Program

/-!
# The workers scenario: two stored replies, both orders, one cancellation

Decisions row 254. The scenario extends the consumer of `Test/Dogfood/P3WorkerQueue.lean`: its
two host rows, and its worker with a connection that a scope releases. It composes five features:
a scope with a release, a fork into a scope, a loop, a handled failure, and calls that the host
answers by key.

* **Program.** `crew`: two workers, each with an identity. A worker opens its connection, then
  takes a job, notes the assignment in a shared cell, runs the job and counts it. The job that
  makes the count `total` completes the gate, and the gate's completion ends the pool's scope.
* **Script.** Both workers park on `Jobs.take`, and the host holds both calls. The session
  receives both replies and applies them in both orders. Then the host cancels one worker.
  `runsOf` lists each script once, as a named run.
* **Observation.** `Observation`, seven fields: the assignment of jobs to workers, the accepted
  reply receipts, the reply applications, the retired calls, the cleanup identities, the root's
  exit and the work left.
* **Controls.** `controlsOf`: for each entry a green control and at least one red control. A
  control names the runs that its comparison reads. One green control of the cleanup clause is
  the lowest-fiber schedule of today: the driver of `P3WorkerQueue.lean` plays it on the same
  program, and the journals agree row for row.
* **Lowered runs.** The crew's logs are `Ref.update` rows whose binder terms no name images. The
  program prints and reads back since the state plan's T5, part A
  (`Test/Dogfood/Scenario/Faces.lean`). The host lane and the engine's lane take their scripts
  from `runsOf`: the keyed lane performs each named run that a host can perform, and
  `Test/Dogfood/Scenario/TapeData.lean` names the runs of the engine's fixture.
  `Observation.machine` is the machine's part of the observation.

Each run is a finite probe: one script on the Lean machine. The claim's standing is derived from
its proof: `#plan_status workers` prints it.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Workers

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession (Key Reply)
open Test.Dogfood.P3WorkerQueue (take runJob)

/-! ## 1. The observation -/

/-- The entries of a log cell. -/
def entries : Option Val → List Val
  | some (.list values) => values
  | _ => []

/-- The scenario's one observation. -/
structure Observation where
  /-- The assignment of jobs to workers: each `[job, worker]` the `assigned` cell holds, in the
  order the takes were applied. -/
  assignment : List Val
  /-- The accepted reply receipts, in order. -/
  receipts : List Seen
  /-- The reply applications the session applied, in order. -/
  applications : List Seen
  /-- The retired calls, each with whether a reply waited for it. -/
  retired : List (Seen × Bool)
  /-- The cleanup identities: the connections the `released` cell holds, in release order. -/
  cleanups : List Val
  /-- The root's exit, or `none` while it is live. -/
  rootExit : Option ExitV
  /-- The work left: runnable fibers, armed owners, live calls, stored replies and timers. -/
  workLeft : Run.Work
deriving DecidableEq

/-- The observation of a run. -/
def observe (s : Run) : Observation :=
  { assignment := entries (cell s 2)
    receipts := receipts s
    applications := applications s
    retired := retired s
    cleanups := entries (cell s 1)
    rootExit := s.exit
    workLeft := s.work }

/-- The machine's part of the observation: what a replay of the machine alone can show. The
reply receipts, the reply applications, the retired calls and the stored replies are the
session's. -/
structure MachineView where
  assignment : List Val
  cleanups : List Val
  rootExit : Option ExitV
  runnable : List FiberId
  queued : List FiberId
  awaiting : List Await
  timers : List (FiberId × ClockMillis)
deriving DecidableEq

/-- The named projection of the observation onto the machine. -/
def Observation.machine (o : Observation) : MachineView :=
  ⟨o.assignment, o.cleanups, o.rootExit, o.workLeft.runnable, o.workLeft.queued,
    o.workLeft.awaiting, o.workLeft.timers⟩

/-! ## 2. The runs and the controls -/

/-- A `Jobs.take` call and a `Jobs.run` call, as the host sees them at a key. -/
def takeAt (fiber token : Nat) : Seen := ⟨"Jobs.take", .unit, ⟨⟨fiber⟩, token⟩⟩
def runAt (job fiber token : Nat) : Seen := ⟨"Jobs.run", .nat job, ⟨⟨fiber⟩, token⟩⟩

/-- The same calls as the machine waits on them: row 0 is `Jobs.take`, row 1 is `Jobs.run`. -/
def waitTake (fiber token : Nat) : Await := ⟨⟨fiber⟩, token, .external 0, .unit⟩
def waitRun (job fiber token : Nat) : Await := ⟨⟨fiber⟩, token, .external 1, .nat job⟩

/-- A `[job, worker]` entry of the `assigned` cell. -/
def gave (job worker : Nat) : Val := .list [.nat job, .nat worker]

/-- Both workers parked on `Jobs.take`: nothing assigned, received, applied, retired or released. -/
def atParked : Observation :=
  { assignment := [], receipts := [], applications := [], retired := [], cleanups := []
    rootExit := none
    workLeft := ⟨[], [], [waitTake 1 1, waitTake 2 2], [], []⟩ }

/-- Both replies stored and none applied. -/
def atReceived : Observation :=
  { atParked with
    receipts := [takeAt 1 1, takeAt 2 2]
    workLeft := ⟨[], [], [waitTake 1 1, waitTake 2 2], [⟨⟨1⟩, 1⟩, ⟨⟨2⟩, 2⟩], []⟩ }

/-- Both replies applied, worker 1's first: each worker waits on its `Jobs.run` call. -/
def atRunning : Observation :=
  { atReceived with
    assignment := [gave 1 1, gave 2 2]
    applications := [takeAt 1 1, takeAt 2 2]
    workLeft := ⟨[], [], [waitRun 1 1 3, waitRun 2 2 4], [], []⟩ }

/-- The root's answer when both jobs are counted: the released connections and the count. -/
def done (released : List Val) : Option ExitV := some (.success (.list [.list released, .nat 2]))

/-- Whether a run shows an observation. -/
def shows (s : Run) (expected : Observation) : Bool := observe s == expected

/-- The controls. Each names the runs of `runsOf` that its comparison reads, and the gate hands
them over as played. Every control compares `observe`. A control of a refusal compares the
refused rows beside it. Three comparisons need the crew's build: one makes the run that
`P3WorkerQueue.drive` drives, and two play a journal again from the opened program. -/
def controlsOf (b : Api.Built) : List Control :=
  [ -- a reply receipt does not advance the machine
    green "receipt" "two reply receipts store two replies and move nothing else"
      ["parked", "received"] fun
      | [waiting, received] =>
        shows received atReceived && received.machine.state == waiting.machine.state
      | _ => false
  , green "receipt" "the other order of the reply receipts stores the same replies"
      ["received-reversed"] fun
      | [reversed] => shows reversed { atReceived with receipts := [takeAt 2 2, takeAt 1 1] }
      | _ => false
  , red "receipt" "a duplicate reply is refused and changes nothing" ["duplicate"] fun
      | [duplicate] => refused duplicate [("submit", .pendingReply)] && shows duplicate atReceived
      | _ => false
    -- a reply application consumes the selected call only
  , green "selection" "the reply application at worker 2's key advances worker 2 alone"
      ["applied-2"] fun
      | [applied] =>
        shows applied
          { atReceived with
            assignment := [gave 2 2]
            applications := [takeAt 2 2]
            workLeft := ⟨[], [], [waitTake 1 1, waitRun 2 2 3], [⟨⟨1⟩, 1⟩], []⟩ }
      | _ => false
  , red "selection" "the two orders of the reply applications leave different assignments"
      ["applied-1-2", "applied-2-1"] fun
      | [oneFirst, twoFirst] =>
        shows oneFirst atRunning &&
          shows twoFirst
            { atRunning with
              assignment := [gave 2 2, gave 1 1]
              applications := [takeAt 2 2, takeAt 1 1]
              workLeft := ⟨[], [], [waitRun 1 1 4, waitRun 2 2 3], [], []⟩ }
      | _ => false
  , red "selection" "worker 1's reply under worker 2's key is refused" ["crossed"] fun
      | [crossed] => refused crossed [("submit", .callOrder)] && shows crossed atParked
      | _ => false
  , red "selection" "a reply application with no stored reply is refused" ["unreceived"] fun
      | [unreceived] => refused unreceived [("apply", .noCall)] && shows unreceived atParked
      | _ => false
  , red "selection" "a stale reply and a second reply application are refused"
      ["applied-1", "stale"] fun
      | [applied, stale] =>
        refused stale [("submit", .noCall), ("apply", .noCall)] && shows stale (observe applied)
      | _ => false
    -- a control retires the held calls whose guard it removed
  , green "retirement" "cancelled after the reply applications, worker 2's call is retired alone"
      ["cancelled-running"] fun
      | [cancelled] =>
        shows cancelled
          { atRunning with
            retired := [(runAt 2 2 4, false)]
            cleanups := [.nat 2]
            workLeft := ⟨[], [], [waitRun 1 1 3], [], []⟩ }
      | _ => false
  , green "retirement"
      "cancelled before the reply receipt, the call is retired and a late reply is refused"
      ["cancelled-early"] fun
      | [early] =>
        refused early [("submit", .noCall)] &&
          shows early
            { atParked with
              retired := [(takeAt 2 2, false)]
              cleanups := [.nat 2]
              workLeft := ⟨[], [], [waitTake 1 1], [], []⟩ }
      | _ => false
  , green "retirement"
      "cancelled between reply receipt and reply application, the reply is kept and never applied"
      ["cancelled-between"] fun
      | [between] =>
        refused between [("apply", .noCall)] &&
          shows between
            { atReceived with
              assignment := [gave 1 1]
              applications := [takeAt 1 1]
              retired := [(takeAt 2 2, true)]
              cleanups := [.nat 2]
              workLeft := ⟨[], [], [waitRun 1 1 3], [], []⟩ }
      | _ => false
  , red "retirement" "cancelling the root retires both workers' calls" ["cancelled-root"] fun
      | [cancelled] =>
        (observe cancelled).retired == [(takeAt 1 1, false), (takeAt 2 2, false)]
      | _ => false
    -- each registration cleans up at most once
  , green "cleanup" "the lowest-fiber schedule of today releases each connection once"
      ["lowest"] fun
      | [scripted] =>
        let driven := (P3WorkerQueue.drive 300 { run := (opened b).play Rows.start }).run
        shows scripted
            { assignment := [gave 1 1, gave 2 1]
              receipts := [takeAt 1 1, runAt 1 1 3, takeAt 1 4, runAt 2 1 5]
              applications := [takeAt 1 1, runAt 1 1 3, takeAt 1 4, runAt 2 1 5]
              retired := [(takeAt 2 2, false)]
              cleanups := [.nat 2, .nat 1]
              rootExit := done [.nat 2, .nat 1]
              workLeft := ⟨[], [], [], [], []⟩ } &&
          driven.journal.take scripted.journal.length == scripted.journal &&
          shows driven (observe scripted)
      | _ => false
  , green "cleanup"
      "a cancelled worker's connection stays released once when the pool closes"
      ["cancelled"] fun
      | [closed] =>
        shows closed
          { assignment := [gave 1 1, gave 2 2, gave 2 1]
            receipts := [takeAt 1 1, takeAt 2 2, runAt 1 1 3, takeAt 1 5, runAt 2 1 6]
            applications := [takeAt 1 1, takeAt 2 2, runAt 1 1 3, takeAt 1 5, runAt 2 1 6]
            retired := [(runAt 2 2 4, false)]
            cleanups := [.nat 2, .nat 1]
            rootExit := done [.nat 2, .nat 1]
            workLeft := ⟨[], [], [], [], []⟩ }
      | _ => false
  , red "cleanup" "a crew that registers each release twice releases each connection twice"
      ["twice"] fun
      | [twice] => (observe twice).cleanups == [.nat 2, .nat 2, .nat 1, .nat 1]
      | _ => false
    -- a script's run replays from its journal
  , green "journal" "the journal alone reaches the scripted run again, verdict for verdict"
      ["lowest"] fun
      | [scripted] =>
        shows ((opened b).play scripted.journal) (observe scripted) &&
          ((opened b).play scripted.journal).phases == scripted.phases
      | _ => false
  , red "journal" "a journal that drops one reply application reaches another run"
      ["lowest"] fun
      | [scripted] => !shows ((opened b).play (scripted.journal.eraseIdx 5)) (observe scripted)
      | _ => false ]

/-- The scenario's runs and its controls: the crew and its faulty twin, each built once. A
program that does not build leaves no run and one failing control. -/
def runsAndControls : List NamedRun × List Control :=
  match builtInputs with
  | some (b, _faulty) => (runSet.runs, controlsOf b)
  | none => ([], [green "receipt" "the crew and its faulty twin build" [] fun _ => false])

/-! ## 3. The record -/

/-- The workers scenario. The claim assembles the four clauses. The driver's law `replays` is an
associated law: the record claims no dependency of `workers` on it. -/
def scenario : Scenario :=
  { name := runSet.name
    program := ``crew
    observation := ``observe
    runs := runsAndControls.1
    controls := runsAndControls.2 }

end Test.Dogfood.Scenario.Workers


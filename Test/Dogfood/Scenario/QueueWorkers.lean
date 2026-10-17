import Test.Dogfood.Scenario.QueueWorkers.Runs
import Test.Dogfood.Scenario
import Test.Dogfood.Scenario.QueueWorkers.Model
import Test.Dogfood.P3WorkerQueue
import Test.Program.QueueTraces
import Effect4.Library.Queue.Ops

/-!
# The queue-workers scenario: the two-worker crew over the public Queue

Decisions rows 254 and 275. The first scenario's workers take their jobs from a host row
(`Test/Dogfood/Scenario/Workers.lean`). Here the Queue's public operations stand between the two
host rows of p3's consumer (`Test/Dogfood/P3WorkerQueue.lean`). The first scenario stays as the
control of the host protocol.

* **Program.** `crew`: a feeder calls the host row `Jobs.take` and offers each job to a queue of
  capacity 1. Two workers take from the queue. Each notes its assignment and runs its job on the
  host row `Jobs.run`. The root reads the queue's size and polls once at its exit. So the five
  public operations stand in one program: `Queue.bounded`, `offer`, `take`, `size` and `poll`
  (`src/Effect4/Library/Queue/Ops.lean`). Each of the three crew members holds a connection that
  its scope releases.
* **Script.** The host feeds a job by a reply to the feeder's call, and it ends a job by a reply
  to a worker's call. A reply application does not drain a posted helper, so a flush follows
  each one (section 2). `runsOf` lists each script once, as a named run.
* **Observation.** `Observation`, eleven fields: the assignment, the queue's cell up to its
  handles, the resolved jobs entering feeder offers, the reply receipts, the reply applications, the retired calls, the
  opened and the released connections, the count of finished jobs, the root's exit and the work
  left.
* **Premises.** A goal's budget premise is `funded` (`src/Effect4/Run/Tape.lean`): no task of
  the run was cut by its budget. The mask is a premise of the program: each worker takes, and
  the feeder offers, outside every mask. A red control breaks each premise.
* **Controls.** `controlsOf`: for each entry a green control and at least one red control. A
  fault is a variant of the crew with one changed part (`Fault`).
* **Lowered runs.** The program prints and reads back (`Test/Dogfood/Scenario/Faces.lean`). The
  host lane and the engine's lane take their scripts from `runsOf`.

Each run is a finite probe: one script on the Lean machine. The claim's standing is derived from
its proof: the gate at the foot measures it. The statements establish no law of the Queue's
whole run, no fairness, no starvation freedom and no liveness.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Dogfood.Scenario.QueueWorkers

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession (Key Reply)
open Effect4.Modules
open Test.Dogfood.P3WorkerQueue (take runJob)
open Test.Program.QueueTraces (takeOf offerOf takesBack)

/-! ## 1. The runs and the controls -/

/-- The feeder's `Jobs.take` call and a worker's `Jobs.run` call, as the host sees them at a
key. The feeder is fiber 3. -/
def takeAt (token : Nat) : Seen := ⟨"Jobs.take", .unit, ⟨⟨3⟩, token⟩⟩
def runAt (job fiber token : Nat) : Seen := ⟨"Jobs.run", .nat job, ⟨⟨fiber⟩, token⟩⟩

/-- The same calls as the machine waits on them: row 0 is `Jobs.take`, row 1 is `Jobs.run`. -/
def waitTake (token : Nat) : Await := ⟨⟨3⟩, token, .external 0, .unit⟩
def waitRun (job fiber token : Nat) : Await := ⟨⟨fiber⟩, token, .external 1, .nat job⟩

/-- Jobs, or identities, as values. -/
def numbers (ns : List Nat) : List Val := ns.map Val.nat

/-- The queue's cell with these buffered jobs, these pending offers of one job each, and this
count of waiting takers. -/
def queueOf (buffered pending : List Nat) (takers : Nat) : QueueCell :=
  .holds ⟨capacity, numbers buffered, pending.map fun job => (false, [.nat job]), takers⟩

/-- Both workers wait at the empty queue, and the host holds the feeder's call. -/
def atParked : Observation :=
  { assignment := [], queue := queueOf [] [] 2, fed := [], receipts := [], applications := []
    retired := [], opened := numbers [1, 2, 3], cleanups := [], finished := some (.nat 0)
    rootExit := none
    workLeft := ⟨[], [], [waitTake 3], [], []⟩ }

/-- Each worker runs a job, and the feeder asks for the next one. -/
def atRunning : Observation :=
  { atParked with
    assignment := [gave 1 1, gave 2 2]
    queue := queueOf [] [] 0
    fed := numbers [1, 2]
    receipts := [takeAt 3, takeAt 4]
    applications := [takeAt 3, takeAt 4]
    workLeft := ⟨[], [], [waitRun 1 1 5, waitRun 2 2 7, waitTake 6], [], []⟩ }

/-- Job 3 is buffered, and job 4's offer pends: the feeder waits at no host call. -/
def atBlocked : Observation :=
  { atRunning with
    queue := queueOf [3] [4] 0
    fed := numbers [1, 2, 3, 4]
    receipts := [takeAt 3, takeAt 4, takeAt 6, takeAt 8]
    applications := [takeAt 3, takeAt 4, takeAt 6, takeAt 8]
    workLeft := ⟨[], [], [waitRun 1 1 5, waitRun 2 2 7], [], []⟩ }

/-- The root's answer when the pool closed after three finished jobs: the released connections,
the count, the queue's size and what the poll found. -/
def closedWith (released : List Nat) : Option ExitV :=
  some (.success (.list [.list (numbers released), .nat 3, .nat 0, .none]))

/-- Whether a run shows an observation. -/
def shows (s : Run) (expected : Observation) : Bool := observe s == expected

/-- The machine's view that the raw frame replay shows on the decisions of a run's tape, from
the program's own load: the right side of `funded_replays`. -/
def replayedView (s : Run) : MachineView :=
  machineViewOf (Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
    (tapeOf s) (Api.load s.built.program s.budget.compileFuel)))

/-- The controls. Each names the runs of `runsOf` that its comparison reads, and the gate hands
them over as played. Every control compares `observe`, or a reading of it. A control of a
refusal compares the refused rows beside it. Two comparisons need the crew's build: they play a
journal again from the opened program. -/
def controlsOf (b : Api.Built) : List Control :=
  [ -- a reply receipt does not advance the machine
    green "receipt" "two reply receipts of two jobs' replies store two replies and move no machine"
      ["running", "received"] fun
      | [waiting, received] =>
        shows waiting atRunning &&
          shows received
            { atRunning with
              receipts := [takeAt 3, takeAt 4, runAt 1 1 5, runAt 2 2 7]
              workLeft := ⟨[], [], [waitRun 1 1 5, waitRun 2 2 7, waitTake 6],
                [⟨⟨1⟩, 5⟩, ⟨⟨2⟩, 7⟩], []⟩ } &&
          received.machine.state == waiting.machine.state
      | _ => false
  , red "receipt" "a duplicate reply is refused and changes nothing" ["received", "duplicate"] fun
      | [received, duplicate] =>
        refused duplicate [("submit", .pendingReply)] && shows duplicate (observe received)
      | _ => false
    -- a reply application consumes the selected call only
  , green "selection"
      "the reply application at worker 2's key advances worker 2 alone: it counts its job and waits at the queue"
      ["applied-2"] fun
      | [applied] =>
        shows applied
          { atRunning with
            queue := queueOf [] [] 1
            receipts := [takeAt 3, takeAt 4, runAt 1 1 5, runAt 2 2 7]
            applications := [takeAt 3, takeAt 4, runAt 2 2 7]
            finished := some (.nat 1)
            workLeft := ⟨[], [], [waitRun 1 1 5, waitTake 6], [⟨⟨1⟩, 5⟩], []⟩ }
      | _ => false
  , red "selection"
      "the two orders of the reply applications give the buffered job and the pending job to different workers"
      ["applied-1-2", "applied-2-1"] fun
      | [oneFirst, twoFirst] =>
        let both : Observation :=
          { atBlocked with
            queue := queueOf [] [] 0
            receipts := atBlocked.receipts ++ [runAt 1 1 5, runAt 2 2 7]
            finished := some (.nat 2) }
        shows oneFirst
            { both with
              assignment := [gave 1 1, gave 2 2, gave 3 1, gave 4 2]
              applications := atBlocked.applications ++ [runAt 1 1 5, runAt 2 2 7]
              workLeft := ⟨[], [], [waitRun 3 1 10, waitRun 4 2 12, waitTake 11], [], []⟩ } &&
          shows twoFirst
            { both with
              assignment := [gave 1 1, gave 2 2, gave 3 2, gave 4 1]
              applications := atBlocked.applications ++ [runAt 2 2 7, runAt 1 1 5]
              workLeft := ⟨[], [], [waitRun 4 1 12, waitRun 3 2 10, waitTake 11], [], []⟩ }
      | _ => false
  , red "selection" "worker 1's reply under worker 2's key is refused" ["running", "crossed"] fun
      | [waiting, crossed] =>
        refused crossed [("submit", .callOrder)] && shows crossed (observe waiting)
      | _ => false
  , red "selection" "a reply application with no stored reply is refused"
      ["running", "unreceived"] fun
      | [waiting, unreceived] =>
        refused unreceived [("apply", .noCall)] && shows unreceived (observe waiting)
      | _ => false
    -- a control retires the held calls whose guard it removed
  , green "retirement"
      "cancelled while it runs its job, worker 2's call is retired alone, and its job stays assigned"
      ["cancelled-running"] fun
      | [cancelled] =>
        shows cancelled
          { atRunning with
            retired := [(runAt 2 2 7, false)]
            cleanups := numbers [2]
            workLeft := ⟨[], [], [waitRun 1 1 5, waitTake 6], [], []⟩ }
      | _ => false
  , green "retirement"
      "cancelled while it waits at the queue, worker 2 holds no call: no call is retired"
      ["cancelled-waiting"] fun
      | [cancelled] =>
        shows cancelled
          { atRunning with
            receipts := [takeAt 3, takeAt 4, runAt 2 2 7]
            applications := [takeAt 3, takeAt 4, runAt 2 2 7]
            cleanups := numbers [2]
            finished := some (.nat 1)
            workLeft := ⟨[], [], [waitRun 1 1 5, waitTake 6], [], []⟩ }
      | _ => false
  , red "retirement" "the root's cancellation retires every held call, and the pool closes"
      ["cancelled-root"] fun
      | [cancelled] =>
        (observe cancelled).retired == [(runAt 1 1 5, false), (runAt 2 2 7, false)] &&
          (observe cancelled).cleanups == numbers [3, 2, 1] &&
          (observe cancelled).queue == queueOf [3] [] 0 &&
          (observe cancelled).workLeft == ⟨[], [], [], [], []⟩
      | _ => false
    -- no job is held more often than the host fed it
  , green "once"
      "the whole run: four fed jobs, each held once; job 2 fails after its take and still counts"
      ["closed"] fun
      | [closed] =>
        shows closed
            { atBlocked with
              assignment := [gave 1 1, gave 2 2, gave 3 1, gave 4 2]
              queue := queueOf [] [] 0
              receipts := atBlocked.receipts ++ [runAt 1 1 5, runAt 2 2 7, runAt 3 1 10]
              applications := atBlocked.applications ++ [runAt 1 1 5, runAt 2 2 7, runAt 3 1 10]
              retired := [(takeAt 11, false), (runAt 4 2 12, false)]
              cleanups := numbers [3, 2, 1]
              finished := some (.nat 3)
              rootExit := closedWith [3, 2, 1]
              workLeft := ⟨[], [], [], [], []⟩ } &&
          (observe closed).heldWithin && (observe closed).held == numbers [1, 2, 3, 4]
      | _ => false
  , red "once" "a take that leaves its job in the buffer gives one job to its worker twice"
      ["kept"] fun
      | [kept] =>
        !(observe kept).heldWithin && (observe kept).assignment == [gave 1 1, gave 1 1] &&
          (observe kept).queue == queueOf [1] [] 2 && (observe kept).fed == numbers [1]
      | _ => false
    -- each fed job is held, but for one job of a feeder that is gone
  , green "accounted"
      "a worker cancelled after its take commits: its job stays assigned, and it is never finished"
      ["cancelled-running-closed"] fun
      | [closed] =>
        shows closed
            { atRunning with
              assignment := [gave 1 1, gave 2 2, gave 3 1, gave 4 1]
              fed := numbers [1, 2, 3, 4]
              receipts := [takeAt 3, takeAt 4, runAt 1 1 5, takeAt 6, runAt 3 1 10, takeAt 9,
                runAt 4 1 13]
              applications := [takeAt 3, takeAt 4, runAt 1 1 5, takeAt 6, runAt 3 1 10, takeAt 9,
                runAt 4 1 13]
              retired := [(runAt 2 2 7, false), (takeAt 12, false)]
              cleanups := numbers [2, 3, 1]
              finished := some (.nat 3)
              rootExit := closedWith [2, 3, 1]
              workLeft := ⟨[], [], [], [], []⟩ } &&
          (observe closed).accounted && (observe closed).held == numbers [1, 2, 3, 4]
      | _ => false
  , green "accounted"
      "the feeder cancelled before its offer is accepted: one job is dropped, and no other"
      ["cancelled-offer"] fun
      | [cancelled] =>
        shows cancelled { atBlocked with queue := queueOf [3] [] 0, cleanups := numbers [3] } &&
          (observe cancelled).accounted && (observe cancelled).held == numbers [3, 1, 2]
      | _ => false
  , green "accounted"
      "the feeder cancelled after the acceptance, before its answer: the job stays buffered"
      ["cancelled-accepted"] fun
      | [cancelled] =>
        shows cancelled
            { atBlocked with
              assignment := [gave 1 1, gave 2 2, gave 3 1]
              queue := queueOf [4] [] 0
              receipts := atBlocked.receipts ++ [runAt 1 1 5]
              applications := atBlocked.applications ++ [runAt 1 1 5]
              cleanups := numbers [3]
              finished := some (.nat 1)
              workLeft := ⟨[], [], [waitRun 3 1 10, waitRun 2 2 7], [], []⟩ } &&
          (observe cancelled).accounted && (observe cancelled).held == numbers [4, 1, 2, 3]
      | _ => false
  , red "accounted"
      "a take under a mask: the cancelled worker takes the next job and exits before its note, and the job is in no cell"
      ["masked"] fun
      | [lost] =>
        !(observe lost).accounted && (observe lost).fed == numbers [1, 2, 3] &&
          (observe lost).held == numbers [1, 2] && (observe lost).queue == queueOf [] [] 0 &&
          (observe lost).cleanups == numbers [2] && atRest lost && funded lost
      | _ => false
  , red "accounted" "a withdrawal that takes a buffered job back loses two jobs" ["taken-back"] fun
      | [lost] =>
        !(observe lost).accounted && (observe lost).fed == numbers [1, 2, 3, 4] &&
          (observe lost).held == numbers [1, 2] && (observe lost).queue == queueOf [] [] 0
      | _ => false
    -- at rest the queue is settled
  , green "settled" "both workers wait at the empty queue: two takers, and the feeder calls"
      ["parked"] fun
      | [waiting] => shows waiting atParked && (observe waiting).settled
      | _ => false
  , green "settled" "an offer pends at the full buffer, and the feeder waits at no host call"
      ["blocked"] fun
      | [full] => shows full atBlocked && (observe full).settled
      | _ => false
  , green "settled"
      "a worker cancelled while it waits: its request is withdrawn, and the next job goes to the other worker"
      ["cancelled-waiting", "cancelled-waiting-closed"] fun
      | [cancelled, closed] =>
        (observe cancelled).queue == queueOf [] [] 0 && (observe cancelled).settled &&
          shows closed
            { atRunning with
              assignment := [gave 1 1, gave 2 2, gave 3 1]
              fed := numbers [1, 2, 3]
              receipts := [takeAt 3, takeAt 4, runAt 2 2 7, takeAt 6, runAt 1 1 5, runAt 3 1 10]
              applications := [takeAt 3, takeAt 4, runAt 2 2 7, takeAt 6, runAt 1 1 5,
                runAt 3 1 10]
              retired := [(takeAt 9, false)]
              cleanups := numbers [2, 3, 1]
              finished := some (.nat 3)
              rootExit := closedWith [2, 3, 1]
              workLeft := ⟨[], [], [], [], []⟩ } &&
          (observe closed).settled
      | _ => false
  , green "settled"
      "a worker cancelled after its selection, before the delivery: the signal passes on, and worker 2 takes the job"
      ["cancelled-selected"] fun
      | [passed] =>
        shows passed
            { atParked with
              assignment := [gave 1 2]
              queue := queueOf [] [] 0
              fed := numbers [1]
              receipts := [takeAt 3]
              applications := [takeAt 3]
              cleanups := numbers [1]
              workLeft := ⟨[], [], [waitRun 1 2 5, waitTake 4], [], []⟩ } &&
          (observe passed).settled
      | _ => false
  , green "settled"
      "the cell is read up to its handles: two runs with two waiting takers show one queue, and the next fed job goes to the earliest taker"
      ["parked", "rewaiting", "fed", "rewaiting-fed"] fun
      | [first, second, firstFed, secondFed] =>
        cell first 0 != cell second 0 && (observe first).queue == (observe second).queue &&
          (observe second).settled &&
          (observe firstFed).assignment == [gave 1 1] &&
          (observe secondFed).assignment == [gave 1 1, gave 2 2]
      | _ => false
  , red "settled" "a take with no withdrawal leaves a taker with no worker, and the next job is stranded"
      ["unwithdrawn"] fun
      | [stranded] =>
        !(observe stranded).settled && (observe stranded).queue == queueOf [3] [] 2 &&
          (observe stranded).cleanups == numbers [2] &&
          (observe stranded).assignment == [gave 1 1, gave 2 2] && atRest stranded &&
          funded stranded
      | _ => false
  , red "settled" "a withdrawal that posts nothing strands a job beside a waiting taker"
      ["silent"] fun
      | [stranded] =>
        !(observe stranded).settled && (observe stranded).queue == queueOf [1] [] 1 &&
          (observe stranded).assignment == [] && atRest stranded && funded stranded
      | _ => false
  , red "settled" "an offer with no withdrawal leaves an offer with no feeder" ["stays"] fun
      | [left] =>
        !(observe left).settled && (observe left).queue == queueOf [3] [4] 0 &&
          (observe left).cleanups == numbers [3] && atRest left && funded left
      | _ => false
  , red "settled"
      "a budget that cuts the pool's close: the journal has a stopped row, and the queue is not settled"
      ["starved", "cancelled-waiting-closed"] fun
      | [starved, closed] =>
        !funded starved && !(observe starved).settled &&
          (observe starved).cleanups == numbers [2, 3] && (observe starved).rootExit == none &&
          funded closed && (observe closed).settled && starved.journal == closed.journal
      | _ => false
  , red "settled"
      "the same journal holds no frontier verdict, and its verdicts are the funded run's: its stopped row is a reply application that the session applied"
      ["starved", "cancelled-waiting-closed"] fun
      | [starved, closed] =>
        starved.phases.all (· != .frontier) && starved.phases == closed.phases &&
          (tapeFrom (openedOf starved) starved.journal).2.take 1 == [.apply ⟨⟨1⟩, 10⟩] &&
          (tapeFrom (openedOf starved) starved.journal).2.length == 2 &&
          !atRest starved && (observe starved).workLeft.runnable == [⟨1⟩]
      | _ => false
    -- each registration cleans up at most once
  , green "cleanup" "each connection is released once when the pool closes" ["closed"] fun
      | [closed] =>
        (observe closed).cleanups == numbers [3, 2, 1] && (observe closed).releasedOnce
      | _ => false
  , green "cleanup"
      "after a worker's cancellation each connection is still released once"
      ["cancelled-waiting-closed", "cancelled-running-closed"] fun
      | [waiting, running] =>
        (observe waiting).cleanups == numbers [2, 3, 1] && (observe waiting).releasedOnce &&
          (observe running).cleanups == numbers [2, 3, 1] && (observe running).releasedOnce
      | _ => false
  , red "cleanup" "a crew that registers each release twice releases each connection twice"
      ["twice"] fun
      | [twice] =>
        (observe twice).cleanups == numbers [3, 3, 2, 2, 1, 1] && !(observe twice).releasedOnce
      | _ => false
    -- a script's run replays from its journal
  , green "journal" "the journal alone reaches the whole run again, verdict for verdict"
      ["closed"] fun
      | [closed] =>
        shows ((opened b).play closed.journal) (observe closed) &&
          ((opened b).play closed.journal).phases == closed.phases
      | _ => false
  , red "journal" "a journal that drops one reply application reaches another run" ["closed"] fun
      | [closed] => !shows ((opened b).play (closed.journal.eraseIdx 4)) (observe closed)
      | _ => false
    -- the machine of a funded run is the raw replay of its tape's decisions
  , green "funded"
      "each run on the crew at the battery's budgets is funded, and the whole run's machine is the raw replay of its tape"
      ["parked", "fed", "running", "received", "duplicate", "applied-2", "blocked",
        "applied-1-2", "applied-2-1", "crossed", "unreceived", "cancelled-running",
        "cancelled-running-closed", "cancelled-waiting", "cancelled-waiting-closed",
        "cancelled-offer", "cancelled-accepted", "cancelled-selected", "cancelled-root",
        "closed", "rewaiting", "rewaiting-fed"] fun runs =>
        runs.length == 22 && runs.all funded &&
          runs.all fun run => machineView run == replayedView run
  , green "funded"
      "the least command budget of the script that the starved run plays: funded at 119, and not at 118"
      [] fun _ =>
        let script := script [running, cancelWaiting, afterWaiting]
        funded (Scenario.play (openedAt 119 b) script) &&
          !funded (Scenario.play (openedAt 118 b) script)
  , red "funded"
      "a journal with a stopped row: the raw replay of its tape shows another machine"
      ["starved"] fun
      | [starved] => !funded starved && machineView starved != replayedView starved
      | _ => false
  , red "funded"
      "a budget's cut that leaves the machine at rest: each connection is released, no work is left and the root has no exit, under the funded run's journal and verdicts"
      ["dropped", "cancelled-waiting-closed"] fun
      | [dropped, closed] =>
        !funded dropped && atRest dropped && funded closed &&
          dropped.journal == closed.journal && dropped.phases == closed.phases &&
          (observe dropped).rootExit == none &&
          (observe closed).rootExit == closedWith [2, 3, 1] &&
          (observe dropped).cleanups == numbers [2, 3, 1] &&
          (observe dropped).workLeft == ⟨[], [], [], [], []⟩ &&
          machineView dropped != replayedView dropped
      | _ => false ]

/-- The scenario's runs and its controls: the crew and its seven faulty twins, each built once.
A program that does not build leaves no run and one failing control. -/
def runsAndControls : List NamedRun × List Control :=
  match builtInputs with
  | some (b, _unwithdrawn, _silent, _keeps, _masked, _takesBack, _stays, _twice) => (runSet.runs, controlsOf b)
  | none => ([], [green "receipt" "the crew and its faulty twins build" [] fun _ => false])

/-! ## 2. The record -/

/-- The queue-workers scenario. The claim assembles the seven clauses. Two laws stand beside
them as associated laws: the driver's `replays`, and `funded_replays`
(`src/Effect4/Laws/Run/Tape.lean`), the proved statement that the goals' budget premise is tied
to. -/
def scenario : Scenario :=
  { name := runSet.name
    program := ``crew
    observation := ``observe
    runs := runsAndControls.1
    controls := runsAndControls.2 }

end Test.Dogfood.Scenario.QueueWorkers


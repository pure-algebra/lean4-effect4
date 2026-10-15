import Test.Dogfood.Scenario.QueueWorkers.Model

/-! Data shared by the scenario battery and fixture writers. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Dogfood.Scenario.QueueWorkers

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession (Key Reply)
open Effect4.Modules
open Test.Dogfood.P3WorkerQueue (take runJob)
open Test.Program.QueueTraces (takeOf offerOf takesBack)

/-! ## 1. The program -/

/-! ## 2. The scripts

**A reply application does not drain a posted helper.** The Queue delivers each signal by a
posted helper: a detached fork with a deferred start, posted on the signalling fiber's
dispatcher (decisions rows 238 and 240). The session's reply application runs the fiber that it
resumes, and it leaves a helper that this fiber posted as posted work. So a flush follows each
reply application of a script. A host does the same by itself: it lets every dispatcher run
after each act but the root's start. -/

/-- Worker 1, worker 2 and the feeder, by the fibers the root forks them as. -/
def w1 : Sel := .fiber ⟨1⟩
def w2 : Sel := .fiber ⟨2⟩
def feederCall : Sel := .fiber ⟨3⟩

/-- Both workers wait at the empty queue, and the host holds the feeder's `Jobs.take` call. -/
def parked : List Move := [.start, .flush, .hold feederCall]

/-- The host feeds one job: the reply receipt, the reply application, and the flush that runs
the helpers that the feeder's offer posted. -/
def feed (job : Nat) : List Move := answer feederCall (ok (.nat job)) ++ [.flush]

/-- The host ends a worker's job with success, and the dispatchers drain. -/
def done (worker : Sel) : List Move := answer worker (ok .unit) ++ [.flush]

/-- The host fails a worker's job with the failure that the worker handles. -/
def failJob (worker : Sel) : List Move :=
  answer worker (failed "JobFailed" "bad payload") ++ [.flush]

/-- Each worker runs a job: the host fed the jobs 1 and 2, each worker took one by a wake, and
the host holds each call. -/
def running : List Move :=
  script [parked, feed 1, [.hold feederCall, .hold w1], feed 2, [.hold feederCall, .hold w2]]

/-- From `running` the host feeds the jobs 3 and 4. Job 3 is buffered, and job 4's offer pends
at the full buffer: the feeder waits at no host call. -/
def blocked : List Move := script [running, feed 3, [.hold feederCall], feed 4]

/-- The session receives a successful reply for each worker's job. -/
def replies : List Move := [.receive w1 (ok .unit), .receive w2 (ok .unit)]

/-- From `blocked`, the whole run to the root's exit. Worker 1 ends job 1 and takes job 3. Job 2
fails at worker 2, which handles it and takes job 4. Worker 1 ends job 3: the third finished job
closes the pool. -/
def closing : List Move :=
  script [done w1, [.hold w1, .hold feederCall], failJob w2, [.hold w2], done w1]

/-- From `running`: worker 2 ends job 2, waits at the empty queue, and the host cancels it. -/
def cancelWaiting : List Move := script [done w2, [.cancel ⟨2⟩]]

/-- After worker 2's cancellation while it waits: the host feeds job 3, and worker 1 ends its
two jobs. The third finished job closes the pool. -/
def afterWaiting : List Move :=
  script [feed 3, [.hold feederCall], done w1, [.hold w1], done w1]

/-- After worker 2's cancellation while it runs job 2: worker 1 ends job 1 and the jobs 3 and
4, which the host feeds one by one. Job 2 is never finished. -/
def afterRunning : List Move :=
  script [done w1, feed 3, [.hold feederCall, .hold w1], done w1, feed 4,
    [.hold feederCall, .hold w1], done w1]

/-- A reply written by hand, for a red control: the session's name, a call's number and a key.
A driven reply is never written by hand: `Rows.reply` builds it from the call's claim. -/
def forged (callId fiber token : Nat) (completion : Api.HostSession.Answer) : Reply :=
  ⟨Api.HostSession.version, "queue-workers", callId, ⟨⟨fiber⟩, token⟩, completion⟩

/-- The command budget of the starved run. It covers the root's start, each flush and each
reply application of the script but the last one, whose step closes the pool. A control pins
the script's least command budget: the run is funded at 119 and not at 118. -/
def starvedFuel : Nat := 60

/-- The command budget of the dropped run, on the starved run's script. The script's last reply
application runs the pool's close through its three releases. At this budget its command loop
stops before an exit observer of worker 1's fiber, and before the root's exit.
`stepDecisionState` (`src/Effect4/Machine/Fibers.lean`) keeps the loop's machine and drops the
commands that the loop leaves. So no fiber is runnable and no owner is armed: the machine is at
rest, and the root has no exit. In the seat's probes no later act of a host gives the root an
exit: five flushes, a clock step, and a cancellation of each fiber and of the root. A sweep of
the seat's receipt finds this ending at the command budgets 79 to 81. -/
def droppedFuel : Nat := 80

/-- The scenario's named runs: each script of a control, once. The first twenty-two are on the
crew, at the battery's budgets. Then one run is on each faulty crew. The last two are on the
crew at two small command budgets, the starved one and the dropped one. The order is the order
in which the host lane performs them. -/
def runsOf (b unwithdrawn silent keeps masked takesBack stays twice : Api.Built) :
    List NamedRun :=
  let run := fun (name : String) (parts : List (List Move)) =>
    (⟨name, opened b, script parts⟩ : NamedRun)
  let selected : List Move :=
    [.receive feederCall (ok (.nat 1)), .apply feederCall, .cancel ⟨1⟩, .flush]
  [ run "parked" [parked]
  , run "fed" [parked, feed 1]
  , run "running" [running]
  , run "received" [running, replies]
  , run "duplicate" [running, replies, [.receive w1 (ok .unit)]]
  , run "applied-2" [running, replies, [.apply w2, .flush]]
  , run "blocked" [blocked]
  , run "applied-1-2" [blocked, replies, [.apply w1, .flush, .apply w2, .flush]]
  , run "applied-2-1" [blocked, replies, [.apply w2, .flush, .apply w1, .flush]]
  , run "crossed" [running, [.wire (.submit (forged 2 2 7 (ok .unit)))]]
  , run "unreceived" [running, [.apply w2]]
  , run "cancelled-running" [running, [.cancel ⟨2⟩]]
  , run "cancelled-running-closed" [running, [.cancel ⟨2⟩], afterRunning]
  , run "cancelled-waiting" [running, cancelWaiting]
  , run "cancelled-waiting-closed" [running, cancelWaiting, afterWaiting]
  , run "cancelled-offer" [blocked, [.cancel ⟨3⟩]]
  , run "cancelled-accepted" [blocked, [.receive w1 (ok .unit), .apply w1, .cancel ⟨3⟩, .flush]]
  , run "cancelled-selected" [parked, selected]
  , run "cancelled-root" [blocked, [.cancel ⟨0⟩]]
  , run "closed" [blocked, closing]
  , run "rewaiting" [parked, feed 1, [.hold feederCall, .hold w1], done w1]
  , run "rewaiting-fed" [parked, feed 1, [.hold feederCall, .hold w1], done w1, feed 2]
  , ⟨"unwithdrawn", opened unwithdrawn,
      script [running, cancelWaiting, feed 3, [.hold feederCall], done w1]⟩
  , ⟨"silent", opened silent, script [parked, selected]⟩
  , ⟨"kept", opened keeps, script [parked, feed 1, [.hold feederCall, .hold w1], done w1]⟩
  , ⟨"masked", opened masked, script [running, cancelWaiting, feed 3]⟩
  , ⟨"taken-back", opened takesBack, script [blocked, [.cancel ⟨3⟩]]⟩
  , ⟨"stays", opened stays, script [blocked, [.cancel ⟨3⟩]]⟩
  , ⟨"twice", opened twice, script [blocked, closing]⟩
  , ⟨"starved", openedAt starvedFuel b, script [running, cancelWaiting, afterWaiting]⟩
  , ⟨"dropped", openedAt droppedFuel b, script [running, cancelWaiting, afterWaiting]⟩ ]


/-- The programs of this scenario, each admitted once. -/
def builtInputs : Option (Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built × Api.Built) := do
  let build := fun (fault : Fault) => (Effect4.Api.Author.build (crewWith fault 3)).toOption
  let b ← build .none
  let unwithdrawn ← build .unwithdrawn
  let silent ← build .silent
  let keeps ← build .keeps
  let masked ← build .masked
  let takesBack ← build .takesBack
  let stays ← build .stays
  let twice ← build .twice
  pure (b, unwithdrawn, silent, keeps, masked, takesBack, stays, twice)

/-- One inventory of the named scripts, read by every lane. -/
def runSet : RunSet :=
  { name := "queue-workers"
    runs := match builtInputs with
      | some (b, unwithdrawn, silent, keeps, masked, takesBack, stays, twice) => runsOf b unwithdrawn silent keeps masked takesBack stays twice
      | none => [] }

end Test.Dogfood.Scenario.QueueWorkers

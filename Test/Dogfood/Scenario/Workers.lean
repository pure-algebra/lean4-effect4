import Test.Dogfood.Scenario
import Test.Dogfood.P3WorkerQueue

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
* **Claim.** `workers` assembles four clauses. Three are laws of the driver and the session,
  proved in `Test/Dogfood/Scenario.lean`. The fourth, `releases_once`, is a planned goal: under
  every script the crew releases no connection twice. The driver's law `replays` stands beside
  them as an associated law: it has controls, and the claim's proof does not use it.
* **Controls.** `controlsOf`: for each entry a green control and at least one red control. A
  control names the runs that its comparison reads. One green control of the cleanup clause is
  the lowest-fiber schedule of today: the driver of `P3WorkerQueue.lean` plays it on the same
  program, and the journals agree row for row.
* **Lowered runs.** The crew's logs are `Ref.update` rows whose binder terms no name images. The
  program prints and reads back since the state plan's T5, part A
  (`Test/Dogfood/Scenario/Faces.lean`). The host run waits on the keyed lane.
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
open Test.Dogfood.P3WorkerQueue (take runJob ascribe)

/-! ## 1. The program -/

/-- `Ref.update(log, xs => [...xs, x])`: one entry appended to a log cell. -/
def note (log x : TermSrc) : Src NativeOp :=
  Ref.update "xs" (app "append" [var "xs", app "cons" [x, app "nil" []]]) log

/-- One worker with an identity. Its connection carries the identity: the acquisition notes it in
`opened` and answers it, and the release notes the acquired value in `released`. Then the worker
takes jobs forever. It notes each job with its own identity in `assigned`, runs the job, handles
a failed job and counts it. With `twice`, the worker registers the same release a second time:
the fault of the cleanup clause's red control. -/
def worker (twice : Bool) (id : Nat) (opened released assigned count gate : TermSrc)
    (total : Nat) : Src NativeOp :=
  scope (eff do
    let _conn ← acquireRelease "conn" "exit"
      (andThen (note opened (nat id)) (succeed (nat id)))
      (note released (var "conn"))
    let _again ← (if twice then
        acquireRelease "conn" "exit" (succeed (nat id)) (note released (var "conn"))
      else succeed (nat id))
    iterateWith (bool true)
      { while_ := fun _ => bool true
        body := fun _ => eff do
          let job ← Row.call take unit
          let _ ← note assigned (app "pair" [job, nat id])
          let _ ← catchIf "e" (app "tagIs" [str "JobFailed", var "e"])
            (Row.call runJob job) (succeed unit)
          let n ← Ref.updateAndGet "n" (app "succ" [var "n"]) count
          ifElse (app "eq" [n, nat total])
            (Deferred.succeed gate (nat 0)) (succeed (bool false))
        step := fun c _ => c })

/-- Two workers forked into a scope with rc.112's `Effect.forkScoped` options. The cells are, in
allocation order: `opened`, `released`, `assigned` and `count`. The root answers the released
connections and the count. -/
def crewWith (twice : Bool) (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let opened ← Ref.make (ascribe (.list .nat) (app "nil" []))
      let released ← Ref.make (ascribe (.list .nat) (app "nil" []))
      let assigned ← Ref.make (ascribe (.list (.prod .nat .nat)) (app "nil" []))
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make .nat .nat
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped
          (worker twice 1 opened released assigned count gate total)
          (Effect4.Codegen.Forms.defaults true))
        let _w2 ← withFiber (Action.forkScoped
          (worker twice 2 opened released assigned count gate total)
          (Effect4.Codegen.Forms.defaults true))
        Deferred.await gate)
      let closed ← Ref.get released
      let n ← Ref.get count
      return app "pair" [closed, n] }

/-- The scenario's program: the crew, each release registered once. -/
def crew (total : Nat) : Module NativeOp := crewWith false total

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

/-! ## 3. The observation -/

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

/-! ## 4. The claim -/

/-- The proposition of `releases_once`: under every script, every budget and every job count, the
crew's `released` cell holds no connection twice. -/
def ReleasesOnce : Prop :=
  ∀ (total : Nat) (budget : Api.Budget) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b →
    (observe (Scenario.play (Run.open b "workers" budget) moves)).cleanups.Nodup

/-- **Each registration cleans up at most once**, on the crew. Reach: the program `crew`, every
script of the driver's alphabet (every control decision, reply receipt, reply application and
raw row) and every budget. It is R11's whole-run clause "at most once per registration, counted
by identity", stated on one program and one observation. It does not establish the clause for
another program, the order of the releases, or that a release runs at all. The scope's own law is
proved (`Effect4.Scope.close_twice`, `src/Effect4/Machine/Scope.lean`). Its lift to a whole run
is open (`docs/core/system-map.md` §8, R11). Consumer: the workers scenario. Its controls are
finite runs. A bounded search over every script of 23 moves up to length 4, from three states,
found no repeated identity: a finite probe, recorded in the seat's receipt. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal releases_once : ReleasesOnce

/-- **The workers scenario's claim.** A reply receipt does not advance the machine. A reply
application consumes the selected call only. A control retires the held calls whose guard it
removed. The crew releases no connection twice. The first three are proved for every run and
every session. The fourth is the planned goal `releases_once`, so this theorem is proved modulo
it. It does not establish Queue backpressure or fairness, reply admission at the application, or
the retirement edge of the host protocol (R6). -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem workers : ReceiptInert ∧ AppliedSelects ∧ ControlRetires ∧ ReleasesOnce :=
  ⟨receipt_inert, applied_selects, control_retires, releases_once⟩

/-! ## 5. The runs and the controls -/

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
  , run "crossed" [parked, [.row (.submit (forged 0 2 2 (ok (.nat 1))))]]
  , run "unreceived" [parked, [.apply w2]]
  , run "applied-1" [parked, takes, [.apply w1]]
  , run "stale" [parked, takes,
      [.apply w1, .row (.submit (forged 0 1 1 (ok (.nat 1)))), .row (.apply ⟨⟨1⟩, 1⟩)]]
  , run "cancelled-running" [running, [.cancel ⟨2⟩]]
  , run "cancelled-early" [parked, [.cancel ⟨2⟩, .receive w2 (ok (.nat 2))]]
  , run "cancelled-between" [parked, takes, [.cancel ⟨2⟩, .apply w2, .apply w1]]
  , run "cancelled-root" [parked, [.cancel ⟨0⟩]]
  , run "lowest" [lowest]
  , run "cancelled" [running, [.cancel ⟨2⟩], finish]
  , ⟨"twice", opened faulty, lowest⟩ ]

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
  match P3WorkerQueue.built? (crew 2), P3WorkerQueue.built? (crewWith true 2) with
  | some b, some faulty => (runsOf b faulty, controlsOf b)
  | _, _ => ([], [green "receipt" "the crew and its faulty twin build" [] fun _ => false])

/-! ## 6. The record -/

/-- The workers scenario. The claim assembles the four clauses. The driver's law `replays` is an
associated law: the record claims no dependency of `workers` on it. -/
def scenario : Scenario :=
  { name := "workers"
    program := ``crew
    observation := ``observe
    claim := ``workers
    clauses :=
      [ ⟨"receipt", ``receipt_inert⟩
      , ⟨"selection", ``applied_selects⟩
      , ⟨"retirement", ``control_retires⟩
      , ⟨"cleanup", ``releases_once⟩ ]
    laws := [⟨"journal", ``replays⟩]
    runs := runsAndControls.1
    controls := runsAndControls.2 }

/-- Red control of the gate's dependency check (decisions rows 203 and 254): the workers record
under a claim that assembles none of its other clauses. Each placement and each control of the
record still passes. -/
def wrongTop : Scenario :=
  { scenario with name := "workers under receipt_inert", claim := ``receipt_inert }

-- One run of the gate over both records. The green control is that no finding names `workers`.
-- The red control names each clause that the wrong claim's proof does not reach.
/--
error: workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "selection" (Test.Dogfood.Scenario.applied_selects)
workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "retirement" (Test.Dogfood.Scenario.control_retires)
workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "cleanup" (Test.Dogfood.Scenario.Workers.releases_once)
-/
#guard_msgs (error) in
#scenario_gate scenario wrongTop

end Test.Dogfood.Scenario.Workers

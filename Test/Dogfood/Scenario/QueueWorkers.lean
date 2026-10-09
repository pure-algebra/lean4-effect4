import Test.Dogfood.Scenario
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
  handles, the fed jobs, the reply receipts, the reply applications, the retired calls, the
  opened and the released connections, the count of finished jobs, the root's exit and the work
  left.
* **Claim.** `queueWorkers` assembles seven clauses. Three are proved laws: `receipt_inert`,
  the driver's (`Test/Dogfood/Scenario.lean`), and `applied_selects` and `control_retires`, the
  session's (`src/Effect4/Laws/Run/Rows.lean`). Four are planned goals over scripts:
  `held_within_fed`, `fed_accounted`, `queue_settled` and `releases_once`. Each is an instance,
  on this one program, of a proposed claim of the Queue's law of a whole run. The driver's law
  `replays` stands beside them as an associated law.
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

/-! ## 1. The program -/

/-- The fault that a red control plants in the crew. Each changes one part, and each faulty crew
builds: the checker types it. So a fault fails a clause, and not typing. -/
inductive Fault
  /-- The scenario's program. -/
  | none
  /-- A take whose interrupted wait leaves its request in the queue's cell. -/
  | unwithdrawn
  /-- A take whose withdrawal posts no wake. -/
  | silent
  /-- A take whose step answers the buffered job and leaves it buffered. -/
  | keeps
  /-- A worker that takes under `uninterruptible`: the mask's premise, broken. -/
  | masked
  /-- An offer whose withdrawal also drops the newest buffered job. -/
  | takesBack
  /-- An offer whose interrupted wait leaves its pending offer in the queue's cell. -/
  | stays
  /-- A crew member that registers its release a second time. -/
  | twice
deriving DecidableEq

/-- The queue's capacity. At 1 a second fed job makes the feeder's offer wait while a job is
buffered. -/
def capacity : Nat := 1

/-- The step of the fault `keeps`: where a job is buffered it answers the job and writes the
cell as it was. Elsewhere it is the library's step. -/
def keepsStep (A : Ty) (id hint s : TermSrc) : TermSrc :=
  ifT (notT (isEmpty (field s "msgs")))
    (app "pair" [tuple [app "get" [field s "msgs", nat 0], noneOf (field s "offers"),
      noneOf (field s "takers")], s])
    (Queue.takeStep A id hint s)

/-- `take` over the step of the fault `keeps`: the library's wrapper, posts and withdrawal. -/
def keepsTake (A : Ty) (q : TermSrc) : Src NativeOp :=
  waitRetry A "queue: the loop ended without a message"
    { hint := .unit
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (keepsStep A id hint)) fun reply =>
          andThen (postAll (tupleAt reply 1) (bool true))
            (andThen (postAll (tupleAt reply 2) unit)
              (selectOptionWith (tupleAt reply 0) wait done))
      withdraw := fun id =>
        bindWith (Ref.modifyWith q (Queue.withdrawTake A id)) fun woken => postAll woken unit }

/-- A worker's take under a fault. With no fault of a take it is the library's `Queue.take`. -/
def takeFor (fault : Fault) (q : TermSrc) : Src NativeOp :=
  match fault with
  | .unwithdrawn => takeOf { withdraws := false } .nat q
  | .silent => takeOf { withdrawalPosts := false } .nat q
  | .keeps => keepsTake .nat q
  | .masked => uninterruptible (Queue.take .nat q)
  | _ => Queue.take .nat q

/-- The feeder's offer under a fault. With no fault of an offer it is the library's
`Queue.offer`. -/
def offerFor (fault : Fault) (q job : TermSrc) : Src NativeOp :=
  match fault with
  | .takesBack => offerOf { withdrawOffer := takesBack } .nat q job
  | .stays => offerOf { withdraws := false } .nat q job
  | _ => Queue.offer .nat q job

/-- A crew member's connection. It carries the member's identity: the acquisition notes it in
`opened` and answers it, and the release notes the acquired value in `released`. With `twice`
the member registers the same release a second time. -/
def connection (twice : Bool) (id : Nat) (opened released : TermSrc) : Src NativeOp := eff do
  let _conn ← acquireRelease "conn" "exit"
    (andThen (note opened (nat id)) (succeed (nat id)))
    (note released (var "conn"))
  (if twice then
      acquireRelease "conn" "exit" (succeed (nat id)) (note released (var "conn"))
    else succeed (nat id))

/-- One worker with an identity. It opens its connection. Then it takes jobs from the queue
forever: it notes each job with its own identity in `assigned`, runs the job on the host,
handles a failed job and counts it. The job that makes the count `total` completes the gate. -/
def worker (fault : Fault) (id : Nat) (q opened released assigned count gate : TermSrc)
    (total : Nat) : Src NativeOp :=
  scope (eff do
    let _ ← connection (fault == .twice) id opened released
    iterateWith (bool true)
      { while_ := fun _ => bool true
        body := fun _ => eff do
          let job ← takeFor fault q
          let _ ← note assigned (app "pair" [job, nat id])
          let _ ← catchIf "e" (app "tagIs" [str "JobFailed", var "e"])
            (Row.call runJob job) (succeed unit)
          let n ← Ref.updateAndGet "n" (app "succ" [var "n"]) count
          ifElse (app "eq" [n, nat total])
            (Deferred.succeed gate (nat 0)) (succeed (bool false))
        step := fun c _ => c })

/-- The feeder, with the identity `id`. It opens its connection. Then it takes each job from
the host and offers it to the queue, forever. An offer into a full queue waits. -/
def feeder (fault : Fault) (id : Nat) (q opened released : TermSrc) : Src NativeOp :=
  scope (eff do
    let _ ← connection (fault == .twice) id opened released
    iterateWith (bool true)
      { while_ := fun _ => bool true
        body := fun _ => eff do
          let job ← Row.call take unit
          offerFor fault q job
        step := fun c _ => c })

/-- The crew under a fault. The root makes the queue and four cells: in allocation order the
queue's cell, `opened`, `released`, `assigned` and `count`. It forks the two workers and the
feeder into a scope with rc.112's `Effect.forkScoped` options, as the fibers 1, 2 and 3, and it
awaits the gate. After the scope closes it answers the released connections, the count, the
queue's size, and what one `poll` finds. -/
def crewWith (fault : Fault) (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let q ← Queue.bounded .nat capacity
      let opened ← Ref.make (ascribe (.list .nat) (app "nil" []))
      let released ← Ref.make (ascribe (.list .nat) (app "nil" []))
      let assigned ← Ref.make (ascribe (.list (.prod .nat .nat)) (app "nil" []))
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make .nat .nat
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped
          (worker fault 1 q opened released assigned count gate total)
          (Effect4.Codegen.Forms.defaults true))
        let _w2 ← withFiber (Action.forkScoped
          (worker fault 2 q opened released assigned count gate total)
          (Effect4.Codegen.Forms.defaults true))
        let _f ← withFiber (Action.forkScoped (feeder fault 3 q opened released)
          (Effect4.Codegen.Forms.defaults true))
        Deferred.await gate)
      let closed ← Ref.get released
      let n ← Ref.get count
      let left ← Queue.size .nat q
      let last ← Queue.poll .nat q
      return tuple [closed, n, left, last] }

/-- The scenario's program: the crew with no fault. Each worker takes, and the feeder offers,
outside every mask. -/
def crew (total : Nat) : Module NativeOp := crewWith .none total

/-! ## 2. The scripts

**A reply application does not drain a posted helper.** The Queue delivers each signal by a
posted helper: a detached fork with a deferred start, posted on the signalling fiber's
dispatcher (decisions rows 238 and 240). The session's reply application runs the fiber that it
resumes, and it leaves a helper that this fiber posted as posted work. So a flush follows each
reply application of a script. A host does the same by itself: it lets every dispatcher run
after each act but the root's start. -/

/-- The budgets of every run of this battery but the starved one: the first scenario's. -/
def budget : Api.Budget := { fuel := 1000, compileFuel := 2000 }

/-- A built program opened under the scenario's name, at a command budget and the battery's
compile budget. -/
def openedAt (fuel : Nat) (b : Api.Built) : Run :=
  Run.open b "queue-workers" { budget with fuel := fuel }

/-- A built program opened under the scenario's name and the battery's budgets. -/
def opened (b : Api.Built) : Run := openedAt budget.fuel b

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

/-- A move of a host: the root's start, a flush, a clock step, a cancellation, a held call, a
reply receipt of a completion, and a reply application. A raw row is none, and no other control
is one. -/
def Move.hostAct : Move → Bool
  | .control (.evaluate fiber) => fiber == Api.root
  | .control .flush => true
  | .control (.advance _) => true
  | .control (.interruptFrom none _ _) => true
  | .control _ => false
  | .hold _ => true
  | .receive _ (.ofExit _) => true
  | .receive _ _ => false
  | .apply _ => true
  | .row _ => false

/-! ## 3. The observation -/

/-- The entries of a log cell. -/
def entries : Option Val → List Val
  | some (.list values) => values
  | _ => []

/-- The queue's cell up to its handles. A waiting taker's identity and its hint are `Deferred`
handles, and so are a pending offer's. The view keeps how many stand in the cell, and it leaves
out which handle stands where. -/
structure QueueView where
  /-- The capacity. -/
  capacity : Nat
  /-- The buffered jobs, the earliest first. -/
  buffered : List Val
  /-- Each pending offer, the earliest first: its batch flag, and the jobs not yet accepted. -/
  offers : List (Bool × List Val)
  /-- The count of the waiting takers. -/
  takers : Nat
deriving DecidableEq

/-- Whether a value is a `Deferred` handle. -/
def isDeferred : Val → Bool
  | .handle 3 _ => true
  | _ => false

/-- A pending offer's record up to its handles: its identity and its hint are `Deferred`
handles, and it holds a batch flag and a list. `none` for any other value. -/
def offerView (offer : Val) : Option (Bool × List Val) :=
  match Machine.Record.read false offer "batch", Machine.Record.read false offer "hint",
      Machine.Record.read false offer "id", Machine.Record.read false offer "rest" with
  | some (.bool batch), some hint, some id, some (.list rest) =>
    if isDeferred hint && isDeferred id then some (batch, rest) else none
  | _, _, _, _ => none

/-- Whether a value is a waiting taker's record: an identity and a hint, both `Deferred`
handles. -/
def isTaker (taker : Val) : Bool :=
  match Machine.Record.read false taker "hint", Machine.Record.read false taker "id" with
  | some hint, some id => isDeferred hint && isDeferred id
  | _, _ => false

/-- The view of a value that has the shape of the queue's cell. `none` for any other value. -/
def queueView (cell : Val) : Option QueueView :=
  match Machine.Record.read false cell "cap", Machine.Record.read false cell "msgs",
      Machine.Record.read false cell "offers", Machine.Record.read false cell "takers" with
  | some (.nat capacity), some (.list buffered), some (.list offers), some (.list takers) =>
    if takers.all isTaker then
      (offers.mapM offerView).map fun pending => ⟨capacity, buffered, pending, takers.length⟩
    else none
  | _, _, _, _ => none

/-- What a run shows of the queue's cell. -/
inductive QueueCell
  /-- The root has not made the cell. -/
  | unmade
  /-- The cell, up to its handles. -/
  | holds (view : QueueView)
  /-- A value that has not the shape of the queue's cell. -/
  | malformed
deriving DecidableEq

/-- The reading of the queue's cell, by its allocation index. -/
def queueCell : Option Val → QueueCell
  | none => .unmade
  | some cell =>
    match queueView cell with
    | some view => .holds view
    | none => .malformed

/-- The view that the clauses read. A cell that is not made holds nothing. -/
def QueueCell.view : QueueCell → Option QueueView
  | .unmade => some ⟨capacity, [], [], 0⟩
  | .holds view => some view
  | .malformed => none

/-- The jobs that the host fed: the success value of each applied reply on `Jobs.take`, in the
order of the reply applications. The value is the stored reply's, read at the accepted reply
receipt of the same key. -/
def fedOf (s : Run) : List Val :=
  (rows s).filterMap fun
    | (.apply key, .applied) =>
      match seenAt s key with
      | some seen =>
        if seen.row == "Jobs.take" then
          (rows s).findSome? fun
            | (.submit reply, .preflight) =>
              if reply.key == key then
                match reply.completion with
                | .ofExit (.success value) => some value
                | _ => none
              else none
            | _ => none
        else none
      | none => none
    | _ => none

/-- The scenario's one observation. -/
structure Observation where
  /-- The assignment of jobs to workers: each `[job, worker]` the `assigned` cell holds, in the
  order the workers noted them. -/
  assignment : List Val
  /-- The queue's cell, up to its handles. -/
  queue : QueueCell
  /-- The jobs that the host fed, in the order of the reply applications. -/
  fed : List Val
  /-- The accepted reply receipts, in order, on both host rows. -/
  receipts : List Seen
  /-- The reply applications the session applied, in order, on both host rows. -/
  applications : List Seen
  /-- The retired calls, each with whether a reply waited for it. -/
  retired : List (Seen × Bool)
  /-- The identities of the opened connections, in opening order. -/
  opened : List Val
  /-- The cleanup identities: the connections the `released` cell holds, in release order. -/
  cleanups : List Val
  /-- The count of finished jobs: the `count` cell. -/
  finished : Option Val
  /-- The root's exit, or `none` while it is live. -/
  rootExit : Option ExitV
  /-- The work left: runnable fibers, armed owners, live calls, stored replies and timers. -/
  workLeft : Run.Work
deriving DecidableEq

/-- The observation of a run. -/
def observe (s : Run) : Observation :=
  { assignment := entries (cell s 3)
    queue := queueCell (cell s 0)
    fed := fedOf s
    receipts := receipts s
    applications := applications s
    retired := retired s
    opened := entries (cell s 1)
    cleanups := entries (cell s 2)
    finished := cell s 4
    rootExit := s.exit
    workLeft := s.work }

/-! ### The readings of the clauses -/

/-- The job of an entry of the `assigned` cell. -/
def jobOf : Val → Option Val
  | .list [job, _] => some job
  | _ => none

/-- The job that the root's poll took at its exit: the last part of the root's answer. -/
def Observation.leftover (o : Observation) : List Val :=
  match o.rootExit with
  | some (.success (.list [_, _, _, .some job])) => [job]
  | _ => []

/-- The jobs that the queue or a worker holds or held: the buffered jobs, the jobs of the
pending offers, the assigned jobs, and the job that the root's poll took. -/
def Observation.held (o : Observation) : List Val :=
  (match o.queue.view with
    | some q => q.buffered ++ q.offers.flatMap (·.2)
    | none => []) ++ o.assignment.filterMap jobOf ++ o.leftover

/-- Whether the crew member with an identity is alive: its connection is opened and not
released. -/
def Observation.live (o : Observation) (id : Nat) : Bool :=
  o.opened.contains (.nat id) && !o.cleanups.contains (.nat id)

/-- Whether the crew member with an identity waits on a host call. A member's identity is its
fiber's number. -/
def Observation.calling (o : Observation) (id : Nat) : Bool :=
  o.workLeft.awaiting.any fun call => call.fiber == ⟨id⟩

/-- Whether the crew member with an identity is idle: alive, and waiting on no host call. At
rest an idle worker waits at the queue, and an idle feeder waits in its offer. -/
def Observation.idle (o : Observation) (id : Nat) : Bool := o.live id && !o.calling id

/-- Whether no job is held more often than the host fed it. -/
def Observation.heldWithin (o : Observation) : Bool :=
  o.held.all fun job => decide (o.held.count job ≤ o.fed.count job)

/-- Whether each fed job is held, but for one job of a feeder that is gone: the count of the
fed jobs is at most the count of the held ones, plus one where the feeder is not alive. -/
def Observation.accounted (o : Observation) : Bool :=
  decide (o.fed.length ≤ o.held.length + (if o.live 3 then 0 else 1))

/-- Whether the queue is settled. Five parts.

1. The cell is not made, or it has the first profile's shape at the scenario's capacity: each
   pending offer holds one job and no batch.
2. The waiting takers are the idle workers, by their count.
3. One offer pends where the feeder is idle, and none otherwise.
4. No job is buffered while a taker waits.
5. An offer pends only at a full buffer, and the buffer is within its capacity. -/
def Observation.settled (o : Observation) : Bool :=
  match o.queue.view with
  | none => false
  | some q =>
    q.capacity == capacity && q.offers.all (fun offer => !offer.1 && offer.2.length == 1) &&
    q.takers == ([1, 2].filter o.idle).length &&
    q.offers.length == (if o.idle 3 then 1 else 0) &&
    (q.buffered.isEmpty || q.takers == 0) &&
    (q.offers.isEmpty || q.buffered.length == q.capacity) &&
    decide (q.buffered.length ≤ q.capacity)

/-- Whether no connection is released twice. -/
def Observation.releasedOnce (o : Observation) : Bool := decide o.cleanups.Nodup

/-! ## 4. The claim

Each of the four planned goals is an instance, on this one program, of a proposed claim of the
semantics registry (`tools/Tools/SemanticsRegistry.lean`, the open parts of R10 to R12). The
Queue's law of a whole run is not stated (decisions row 275, point 2), so each goal's docstring
says what the goal would follow from. Those lists are what this scenario needs from that law.

Two premises stand in each statement, and a third in two of them.

* **The budget**: `funded` (`src/Effect4/Run/Tape.lean`). No task of the run was cut by its
  budget. The statement ranges over every command budget, at the battery's compile budget.
* **The mask**: the program is `crew`. Each worker takes, and the feeder offers, outside every
  mask. So an interruption at a wait is taken at the wait.
* **Rest**, for the two statements about a state between two acts of a host: `atRest`, on a
  script of host acts (`Move.hostAct`). -/

/-- The proposition of `held_within_fed`. -/
def HeldWithinFed : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).heldWithin = true

/-- **No job is held more often than the host fed it.** Under every script of a funded run, each
job stands among the held jobs at most as often as among the fed ones. The held jobs are the
buffered ones, the jobs of the pending offers, the assigned ones, and the job that the root's
poll took. So the queue and the workers duplicate no job and invent none: a take delivers its
job to one worker, once.

It is an instance of the proposed claims `queue-expansion-agrees` (R10) and
`waiting-request-obligation-preserved` (R10 to R12) on the program `crew`. It would follow from
three things.

1. In a funded run each step of the queue's cell starts at a cell that encodes a state of the
   first profile, for a request that keeps `Requested`. The attempt laws then give the model's
   reply and the model's next state (`take_attempt`, `offer_attempt`, `poll_attempt` and the
   two withdrawals, `src/Effect4/Laws/Library/Queue/Ops.lean`).
2. No other step writes the queue's cell, and only a worker's note writes `assigned`.
3. A take that exits with a job enters its caller's continuation once with that job.

Reach: the program `crew`, every script of the driver's alphabet with its raw rows, every command
budget at the battery's compile budget, under `funded`. It is safety. It does not establish that
a fed job is ever assigned, the order of two deliveries, fairness, or anything of another client.
Consumer: the scenario's claim `queueWorkers`. Its controls are finite runs, and the seat's
receipt records a bounded search. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal held_within_fed : HeldWithinFed

/-- The proposition of `fed_accounted`. -/
def FedAccounted : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b → moves.all Move.hostAct = true →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    atRest (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).accounted = true

/-- **Each fed job is held, but for one job of a feeder that is gone.** Under every script of
host acts, where the run is funded and at rest, the fed jobs are no more than the held ones. They
may be one more where the feeder's connection is released. With `held_within_fed` that is the
exact account. A take that commits keeps its job when its worker is cancelled. A request that is
withdrawn consumes nothing. An accepted offer stays accepted. The one job that may be missing is
the job of a pending offer that an interruption withdrew.

It is an instance of the proposed claims `waiting-request-obligation-preserved` (R10 to R12) and
`queue-expansion-agrees` (R10) on the program `crew`. It would follow from the three things of
`held_within_fed` and from two more.

4. A request's end is one of two. A take commits in its own step, or its interrupted wait runs
   its withdrawal step before its fiber exits, and the withdrawal consumes nothing. An offer is
   accepted by a step, or its interrupted wait withdraws what is still pending (decisions row
   222).
5. At rest no worker stands between its take's commit and its note. The commit and the note run
   in one task, and no interruption is taken between them, because the caller holds no mask.

Reach: the program `crew`, whose callers hold no mask. Scripts of host acts, every command
budget, under `funded` and `atRest`. It does not establish that a fed job is ever assigned or
finished, and it says nothing of a state that is not at rest. Under a masked take it fails: a red
control. Consumer: `queueWorkers`. Its controls are finite runs, and the seat's receipt records a
bounded search. -/
@[semantics "reactive-scheduling" (requirement := R12)]
proof_goal fed_accounted : FedAccounted

/-- The proposition of `queue_settled`. -/
def QueueSettled : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b → moves.all Move.hostAct = true →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    atRest (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).settled = true

/-- **At rest the queue is settled.** Under every script of host acts, where the run is funded
and at rest, the observation satisfies `Observation.settled`. The cell has the first profile's
shape. The waiting takers are the idle workers, and an offer pends exactly where the feeder is
idle. No job is buffered while a taker waits, and an offer pends only at a full buffer.

It is an instance of the proposed claim `wait-registration-no-gap` (R12) with the Queue's
profile, and of the delivery clause of `waiting-request-obligation-preserved`, on the program
`crew`. It would follow from the first, second and fourth things of the goals above, and from
two more.

6. Each posted helper runs once. It resolves its hint, and the request that awaits the hint
   runs its next attempt inside the helper's task (decisions rows 238 and 240). So at rest no
   posted signal is outstanding.
7. The model's run invariant holds along the run's steps: the first profile, the buffer's
   bound, and `quiet` at the requests that were signalled (`first_run_inv`,
   `src/Effect4/Laws/Library/Queue/Invariant.lean`, proved for the model alone).

Reach: as `fed_accounted`. Its first part is the premise of the attempt laws, read at the run's
end. It is an invariant at rest, and an invariant is not progress. It does not establish that a
waiting worker ever takes, the order of two takers, fairness or starvation freedom. The cell is
read up to its handles: the statement does not say which taker is the earliest. Consumer:
`queueWorkers`. Its controls are finite runs, and the seat's receipt records a bounded search. -/
@[semantics "reactive-scheduling" (requirement := R12)]
proof_goal queue_settled : QueueSettled

/-- The proposition of `releases_once`. -/
def ReleasesOnce : Prop :=
  ∀ (total fuel : Nat) (b : Api.Built) (moves : List Move),
    Effect4.Api.Author.build (crew total) = .ok b →
    funded (Scenario.play (openedAt fuel b) moves) = true →
    (observe (Scenario.play (openedAt fuel b) moves)).releasedOnce = true

/-- **Each registration cleans up at most once**, on the crew over the queue. Under every script
of a funded run, the `released` cell holds no connection twice. It is the first scenario's
clause on this program (`Test/Dogfood/Scenario/Workers.lean`). Here an interrupted worker runs
its take's withdrawal before its scope's release, and the feeder its offer's.

It is an instance of R11's first whole-run clause, "at most once per registration, counted by
identity", on the program `crew`. It would follow from that clause for the crew's three scopes
(`Effect4.Scope.close_twice`, `src/Effect4/Machine/Scope.lean`, is the scope's own law). It
needs nothing of the Queue beyond a frame fact: a withdrawal writes the queue's cell and no
scope.

Reach: the program `crew`, every script of the driver's alphabet, every command budget, under
`funded`. It does not establish the order of the releases, that a release runs, or the clause
for another program. Consumer: `queueWorkers`. Its controls are finite runs, and the seat's
receipt records a bounded search. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal releases_once : ReleasesOnce

/-- **The queue-workers scenario's claim.** A reply receipt does not advance the machine. A
reply application consumes the selected call only. A control retires the held calls whose guard
it removed. No job is held more often than the host fed it. Each fed job is held, but for one
job of a feeder that is gone. At rest the queue is settled. No connection is released twice. The
first three are proved for every run and every session. The other four are planned goals, so
this theorem is proved modulo them. It does not establish the Queue's law of a whole run,
fairness, starvation freedom or liveness. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem queueWorkers :
    ReceiptInert ∧ AppliedSelects ∧ ControlRetires ∧ HeldWithinFed ∧ FedAccounted ∧
      QueueSettled ∧ ReleasesOnce :=
  ⟨receipt_inert, applied_selects, control_retires, held_within_fed, fed_accounted,
    queue_settled, releases_once⟩

/-! ## 5. The runs and the controls -/

/-- The feeder's `Jobs.take` call and a worker's `Jobs.run` call, as the host sees them at a
key. The feeder is fiber 3. -/
def takeAt (token : Nat) : Seen := ⟨"Jobs.take", .unit, ⟨⟨3⟩, token⟩⟩
def runAt (job fiber token : Nat) : Seen := ⟨"Jobs.run", .nat job, ⟨⟨fiber⟩, token⟩⟩

/-- The same calls as the machine waits on them: row 0 is `Jobs.take`, row 1 is `Jobs.run`. -/
def waitTake (token : Nat) : Await := ⟨⟨3⟩, token, .external 0, .unit⟩
def waitRun (job fiber token : Nat) : Await := ⟨⟨fiber⟩, token, .external 1, .nat job⟩

/-- A `[job, worker]` entry of the `assigned` cell. -/
def gave (job worker : Nat) : Val := .list [.nat job, .nat worker]

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
  , run "crossed" [running, [.row (.submit (forged 2 2 7 (ok .unit)))]]
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
  let build := fun (fault : Fault) => (Effect4.Api.Author.build (crewWith fault 3)).toOption
  match build .none, build .unwithdrawn, build .silent, build .keeps, build .masked,
      build .takesBack, build .stays, build .twice with
  | some b, some unwithdrawn, some silent, some keeps, some masked, some takesBack, some stays,
      some twice =>
    (runsOf b unwithdrawn silent keeps masked takesBack stays twice, controlsOf b)
  | _, _, _, _, _, _, _, _ =>
    ([], [green "receipt" "the crew and its faulty twins build" [] fun _ => false])

/-! ## 6. The record -/

/-- The queue-workers scenario. The claim assembles the seven clauses. Two laws stand beside
them as associated laws: the driver's `replays`, and `funded_replays`
(`src/Effect4/Laws/Run/Tape.lean`), the proved statement that the goals' budget premise is tied
to. -/
def scenario : Scenario :=
  { name := "queue-workers"
    program := ``crew
    observation := ``observe
    claim := ``queueWorkers
    clauses :=
      [ ⟨"receipt", ``receipt_inert⟩
      , ⟨"selection", ``applied_selects⟩
      , ⟨"retirement", ``control_retires⟩
      , ⟨"once", ``held_within_fed⟩
      , ⟨"accounted", ``fed_accounted⟩
      , ⟨"settled", ``queue_settled⟩
      , ⟨"cleanup", ``releases_once⟩ ]
    laws := [⟨"journal", ``replays⟩, ⟨"funded", ``funded_replays⟩]
    runs := runsAndControls.1
    controls := runsAndControls.2 }

/-- Red control of the gate's dependency check (decisions rows 203 and 254): the record under a
claim that assembles none of its other clauses. Each placement and each control of the record
still passes, so the gate reads it with the dependency check alone (`#scenario_reach`). -/
def wrongTop : Scenario :=
  { scenario with name := "queue-workers under receipt_inert", claim := ``receipt_inert }

-- The green control: the gate passes the record. The red control reads the record under the
-- wrong claim, with the dependency check only (its runs are judged above), and names each clause
-- that the wrong claim's proof does not reach.
#scenario_gate scenario

/--
error: queue-workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "selection" (Effect4.Run.applied_selects)
queue-workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "retirement" (Effect4.Run.control_retires)
queue-workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "once" (Test.Dogfood.Scenario.QueueWorkers.held_within_fed)
queue-workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "accounted" (Test.Dogfood.Scenario.QueueWorkers.fed_accounted)
queue-workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "settled" (Test.Dogfood.Scenario.QueueWorkers.queue_settled)
queue-workers under receipt_inert: the proof of Test.Dogfood.Scenario.receipt_inert does not reach the clause "cleanup" (Test.Dogfood.Scenario.QueueWorkers.releases_once)
-/
#guard_msgs (error) in
#scenario_reach wrongTop

end Test.Dogfood.Scenario.QueueWorkers

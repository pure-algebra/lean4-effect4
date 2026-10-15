import Test.Dogfood.Scenario.Data
import Test.Dogfood.P3WorkerQueue.Data
import Test.Program.QueueTracesData
import Effect4.Library.Queue.Ops

/-!
# The queue crew's authored program

Decisions rows 254 and 275. The scenario and its proof modules import this program.
The definitions retain their names and bodies from `Test/Dogfood/Scenario/QueueWorkers.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Dogfood.Scenario.QueueWorkers

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Test.Dogfood.P3WorkerQueue (take runJob)
open Test.Program.QueueTraces (takeOf offerOf takesBack)

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

end Test.Dogfood.Scenario.QueueWorkers

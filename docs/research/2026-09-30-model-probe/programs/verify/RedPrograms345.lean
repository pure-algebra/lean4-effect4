import Effect4.Api.Author
import Effect4.Api.HostSession
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.DenoteB

/-! Seat PROGRAMS (2026-09-30), probe 3 of 3: the expressible parts of programs 4, 2 and 3.

* Program 4, dogfood 1's rate limiter, at HEAD. The dogfood battery (`Test/Dogfood/
  RateLimiter.lean`) was never committed and is not on disk; this re-runs its design on the
  current authoring surface: three number cells, a refill daemon, five forked requests that
  read then update (the atomic `Ref.modify` of `ts/p4-rate-limiter.ts` has no spelling: `Ref.update`
  takes one of five named functions).
* Program 2's capture question, the data half: a layer that reads a service at build time and
  provides the value answers what rc.112 answers (`ts/capture-control.ts`).
* Program 3's worker pool with the queue as a host service (DI-11's external route): three
  workers in a scope, each holding a resource whose release counts closes; the scope's close
  interrupts the workers parked on the host.

Scratch, not in the tree. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Probe.P345
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession

/-! ## Program 4: the rate limiter -/

/-- The refill daemon: forever, sleep a window, then reset the count. -/
def refill (used : TermSrc) : Src NativeOp :=
  iterateWith (bool true)
    { while_ := fun _ => bool true
      body := fun _ => andThen (Effect.sleep (nat 1000)) (Ref.set used (nat 0))
      step := fun c _ => c }

/-- One request: read, (optionally yield), then admit or reject. Not atomic: the read and the
write are two store steps. -/
def request (yielding : Bool) (used admitted rejected : TermSrc) : Src NativeOp :=
  bindName "current" (Ref.get used) fun current =>
    andThen (if yielding then yieldNow 0 else succeed unit)
      (ifElse (app "lt" [current, nat 3])
        (andThen (Ref.update .incr used) (Ref.update .incr admitted))
        (Ref.update .incr rejected))

def limiter (yielding : Bool) : Src NativeOp := eff do
  let used ← Ref.make (nat 0)
  let admitted ← Ref.make (nat 0)
  let rejected ← Ref.make (nat 0)
  let daemonFiber ← daemon (refill used)
  let f1 ← fork (request yielding used admitted rejected)
  let f2 ← fork (request yielding used admitted rejected)
  let f3 ← fork (request yielding used admitted rejected)
  let f4 ← fork (request yielding used admitted rejected)
  let f5 ← fork (request yielding used admitted rejected)
  let _ ← join f1
  let _ ← join f2
  let _ ← join f3
  let _ ← join f4
  let _ ← join f5
  let _ ← withFiber (Action.interrupt daemonFiber)
  let a ← Ref.get admitted
  let r ← Ref.get rejected
  return app "pair" [a, r]

def limiterProgram (yielding : Bool) : Option Effect4.Api.Program :=
  (elaborate (limiter yielding)).toOption

-- Both variants type at `nat × nat` and need nothing.
#guard (limiterProgram false).bind (Effect4.Api.typeOf ·) = some ⟨.prod .nat .nat, .never, .empty⟩
#guard (limiterProgram true).bind (Effect4.Api.typeOf ·) = some ⟨.prod .nat .nat, .never, .empty⟩

/-- Run with the ordinary decisions: evaluate the root, then flush. -/
def answer (yielding : Bool) : Option ExitV :=
  (limiterProgram yielding).bind fun p => (Effect4.Api.run p 4000).exit

-- Dogfood 1's two answers, at HEAD: `[3, 2]` without the yield, `[5, 0]` with it (all five read
-- 0 before any write), as the dogfood receipt recorded on both faces in 2026-09
-- (`2026-09-15-dogfood-1-receipt.md` §2 L3, §4.3).
#guard answer false = some (.success (.list [.nat 3, .nat 3]))
#guard answer true = some (.success (.list [.nat 5, .nat 0]))

/-! ## Program 2: a captured value -/

def N : ServiceDef := { key := ⟨⟨15⟩, ⟨4⟩⟩, carrier := .nat }
/-- The service a layer builds over `N`: it captures `N`'s value at build time, as data. -/
def Svc : ServiceDef := { key := ⟨⟨16⟩, ⟨4⟩⟩, carrier := .nat }

def captureControl : Module NativeOp :=
  { services := [N, Svc]
    layers := [("svc", Svc.layer N.use)]
    main := N.give (nat 1) (provide (Layer.ref "svc") (eff do
      let captured ← N.give (nat 2) Svc.use   -- the value read when the layer was built
      let atCall ← N.give (nat 2) N.use       -- a method body that reads `N` when called
      return app "pair" [captured, atCall])) }

-- The model answers rc.112's `[1, 2]` (`ts/hostruns.log`, capture control) when what the layer
-- captured is data. A captured *code* value has no spelling; see the note, finding F2.
#guard ((Effect4.Api.Author.build captureControl).toOption.map fun b =>
    (Effect4.Api.run b.program 4000).exit) = some (some (.success (.list [.nat 1, .nat 2])))

/-! ## Program 3: workers over a host queue, cleanup on interruption -/

/-- `Queue.take` answered by the host: the next job id. -/
def take : RowDef := Row.host "Jobs.take" .unit .nat
/-- Run one job on the host; it may fail with (tag, message). -/
def runJob : RowDef := Row.host "Jobs.run" .nat .unit (.prod .string .string)

/-- One worker: hold a connection (a release that counts closes) for its whole life; take
jobs forever; a failed job is handled; each finished job bumps the count, and the job that
makes it `total` completes the gate. -/
def worker (closes count gate : TermSrc) (total : Nat) : Src NativeOp :=
  scope (eff do
    let _conn ← acquireRelease "conn" "exit" (succeed unit) (Ref.update .incr closes)
    iterateWith (bool true)
      { while_ := fun _ => bool true
        body := fun _ => eff do
          let job ← Row.call take unit
          let _ ← catchIf "e" (app "tagIs" [str "JobFailed", var "e"])
            (Row.call runJob job) (succeed unit)
          let n ← Ref.updateAndGet .incr count
          ifElse (app "eq" [n, nat total])
            (Deferred.succeed gate (nat 0)) (succeed (bool false))
        step := fun c _ => c })

def pool (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let closes ← Ref.make (nat 0)
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped (worker closes count gate total) childOptions)
        let _w2 ← withFiber (Action.forkScoped (worker closes count gate total) childOptions)
        let _w3 ← withFiber (Action.forkScoped (worker closes count gate total) childOptions)
        Deferred.await gate)
      -- the scope has closed: every worker was interrupted and released its connection
      let c ← Ref.get closes
      let n ← Ref.get count
      return app "pair" [c, n] }

def poolBuilt? : Option Effect4.Api.Built := (Effect4.Api.Author.build (pool 5)).toOption

#guard poolBuilt?.isSome
-- The error column is `nat`, not `never`: the gate is the native `Deferred<number, number>`,
-- whose `await` row fails with a number (`Native.lean:205-207`). rc.112's `Deferred<void>`
-- (`ts/p3-worker-queue.ts`) cannot fail. Generic cells (rows 42-43 steps 3-5) remove it.
#guard (poolBuilt?.map fun b => (b.ty.answer, b.ty.error, b.closed)) =
  some (.prod .nat .nat, .nat, true)

/-- The host: `take` answers 1..5 and then never again; job 2 fails. -/
def hostAnswer (b : Effect4.Api.Built) (takes : Nat) (op : NativeOp) (request : Val) :
    Option (Completion Val Err Defect FiberId Ann) :=
  match op with
  | .external i =>
    if some i = b.positionOf "Jobs.take" then
      if takes < 5 then some (.ofExit (.success (.nat (takes + 1)))) else none
    else if some i = b.positionOf "Jobs.run" then
      if request = .nat 2 then some (.ofExit (.failure (Cause.fail (.tagged "JobFailed" "bad payload"))))
      else some (.ofExit (.success .unit))
    else none
  | _ => none

structure Driver (b : Effect4.Api.Built) where
  session : Session b.program b.table
  takes : Nat := 0
  /-- Calls the host received (bound in the session), by key. -/
  received : List Key := []
  hanging : List Key := []

/-- One step. The host receives every outstanding call at once (each is bound in the session);
then it answers the first received call its script answers; with nothing to answer, the
scheduler runs. -/
def step (b : Effect4.Api.Built) (d : Driver b) : Driver b :=
  let s := d.session
  let unbound := (outstanding s).filter fun (fiber, token, _, _) => !(d.received.contains ⟨fiber, token⟩)
  match unbound with
  | (fiber, token, op, request) :: _ =>
    let call : Call := ⟨version, "p3", b.table, s.nextCall, fiber, op, request⟩
    { d with session := (bindCall s call token).session, received := d.received ++ [⟨fiber, token⟩] }
  | [] =>
    let answerable := (outstanding s).filter fun (fiber, token, _, _) => !(d.hanging.contains ⟨fiber, token⟩)
    match answerable with
    | (fiber, token, op, request) :: _ =>
      let isTake : Bool := (match op with | .external i => some i == b.positionOf "Jobs.take" | _ => false)
      match hostAnswer b d.takes op request with
      | none => { d with hanging := d.hanging ++ [⟨fiber, token⟩] }
      | some answer =>
        let callId := ((s.active.find? fun bound => bound.key == ⟨fiber, token⟩).map (·.call.callId)).getD 0
        let reply : Reply := ⟨version, "p3", callId, ⟨fiber, token⟩, answer⟩
        let s3 := (applyReply (submit s reply).session reply.key 1000).session
        { d with session := s3, takes := if isTake then d.takes + 1 else d.takes }
    | [] => { d with session := (advance s 1000 Api.flush).session }

def drive (b : Effect4.Api.Built) : Nat → Driver b → Driver b
  | 0, d => d
  | n + 1, d => drive b n (step b d)

def runPool : Option (Option ExitV × Nat × Nat × Nat) :=
  poolBuilt?.bind fun b =>
    match start b.program b.table "p3" ⟨version, "p3", "p3", b.table⟩ 2000 with
    | .error _ => none
    | .ok s0 =>
      let d := drive b 300 { session := (advance s0 2000 Api.evaluate).session }
      some ((d.session.machine.fiber? Api.root).bind (·.exit), d.takes, d.session.applied,
        d.session.retired.length)

-- Five jobs taken and finished (job 2's failure handled), then the gate opens, the scope
-- closes, and all three releases run: the root answers `[3, 5]`. The host answered the calls of
-- the lowest fiber first, so worker 1 did every job; workers 2 and 3 were still waiting on
-- their first `take` when the scope interrupted them. The session retired those two calls and
-- the host was told nothing (`Api/HostSession.lean:191-199`). In rc.112 `Queue.take` is
-- in-process; a host-backed take would need its cancellation delivered.
#guard runPool.map (·.1) = some (some (.success (.list [.nat 3, .nat 5])))
#guard runPool.map (fun r => (r.2.1, r.2.2.1, r.2.2.2)) = some (5, 10, 0)

/-! ## Which theorem could reach each program

`Straight` and `Looped` are the fragments of `run_eq_meaning` and `loopAgreement`;
`run_eq_ref` holds at the empty table only (`Laws/Program/RuntimeR.lean:197-216`). -/

open Effect4.Program.Denote in
#guard (limiterProgram false).map (fun p => (Straight p, Looped p)) = some (false, false)
-- the limiter's request body alone (dogfood 1's L2 lane) is straight
open Effect4.Program.Denote in
#guard ((request false (var "u") (var "a") (var "r")) { names := ["u", "a", "r"] } []).toOption.map
    (fun e => (Straight e, Looped e)) = some (true, true)
-- the refill daemon parks on the clock: in neither fragment
open Effect4.Program.Denote in
#guard ((refill (var "u")) { names := ["u"] } []).toOption.map (fun e => (Straight e, Looped e))
  = some (false, false)
-- the pool calls host rows: its table is not empty, so `run_eq_ref` does not reach it
#guard poolBuilt?.map (fun b => b.table.isEmpty) = some false
-- the capture control and the limiter use no host row: `run_eq_ref` reaches them
#guard (Effect4.Api.Author.build captureControl).toOption.map (fun b => b.table.isEmpty) = some true

end Probe.P345


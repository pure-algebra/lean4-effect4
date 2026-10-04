import Test.Dogfood.Stage
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.DenoteB

/-!
# p3: workers draining a queue, with cleanup on interruption

The rc.112 source is `Test/Dogfood/rc112/p3-worker-queue.ts`. Three workers take jobs from a
`Queue.bounded`, each holding a connection that `acquireRelease` closes on any exit. `catchTag`
catches a failed job, a `Ref.modify` counts finished jobs, and the last one completes a
`Deferred<void>` gate. Then the program interrupts the pool. `run-p3.ts` ran it on effect 4.0.0-rc.112
under bun 1.4.2. It answered a fourteen-line log: three opens, the five jobs, then each worker's
close with a `Failure` exit and its stop (`Test/Dogfood/rc112/hostruns.log`).

This battery ports the model probe's program 3
(`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/ProbePrograms345.lean`, "Program 3"),
with the verifier's checks of `verify/VerifyPrograms.lean` §1 and §3 at the same revision. The
queue is a pair of host rows (DI-11's external route), so the queue lives at the host and the
program is a different one: the encoding counts closes and finished jobs instead of logging.

**Changes since 2026-09-30.**
* `outstanding` answers `Await` records (row 16), not tuples. The scripted host keeps the probe's
  policy (bind every call first, then answer the lowest fiber's) and plays it over `Run`
  (`src/Effect4/Run.lean`). Every row runs at a command budget of 1000, where the probe gave the
  first evaluation 2000. The observations are the probe's (section 2).
* The measured pool forks its workers with rc.112's `Effect.forkScoped` options, a daemon at the
  scope, as the verifier proposed. The probe forked them with `childOptions`, a child fork into a
  scope. rc.112 has no spelling for that fork, and the printer refuses it
  (`internalAction "forkScoped:child"`, `src/Effect4/Codegen/Templates.lean`, the owner's ruling of
  2026-09-17, before the probe). Both spellings run to the same observations. The verifier read
  the refusal as a dropped flag, from `Api.readable`'s note in `src/Effect4/Api.lean`, which still
  says so.

**What the language refuses** (section 6): the log, a `Ref` holding a list (`requestNotSubtype`);
`JobFailed{id, reason}` as a typed failure (`errorNotAdmitted`); `Deferred<void>`, since the
native deferred is `Deferred<number, number>`, whose `await` fails with a number (so the pool's
error column is `nat` where rc.112's is `never`); the forms `forEach` and `catchTag`. A queue has
no spelling inside a program: DI-11 rules it a composite over `Ref`, `Deferred` and a wait list.
When the scope interrupts a worker parked on the host's `take`, the session retires the call;
rc.112's take is in-process.

**Waits on:** R4 with rows 42–43 steps 3–5 (a list cell, `Deferred<void>`, `Ref.modify` with a
binder); R10 with DI-11 (the queue composite) and DI-89 (`forEach`); R3 and row 120 (the
payload); row 131 (the log lines interpolate numbers); R11 (release on interruption, the whole
run). The slices of row 204 that move it: state at any type, then queues.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.P3WorkerQueue

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The program -/

/-- `Queue.take` answered by the host: the next job's id. -/
def take : RowDef := Row.host "Jobs.take" .unit .nat
/-- Run one job on the host; it may fail with (tag, message). -/
def runJob : RowDef := Row.host "Jobs.run" .nat .unit (.prod .string .string)

/-- One worker: hold a connection for its whole life (a release that counts closes), take jobs
forever, handle a failed job, and count each finished job. The job that makes the count `total`
completes the gate. -/
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

/-- Three workers forked into a scope with the given options. The gate's completion ends the scope,
which interrupts every worker and runs its release. -/
def poolWith (options : Effect4.Supervision.ForkOptions) (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let closes ← Ref.make (nat 0)
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped (worker closes count gate total) options)
        let _w2 ← withFiber (Action.forkScoped (worker closes count gate total) options)
        let _w3 ← withFiber (Action.forkScoped (worker closes count gate total) options)
        Deferred.await gate)
      -- the scope has closed: it interrupted every worker, and each released its connection
      let c ← Ref.get closes
      let n ← Ref.get count
      return app "pair" [c, n] }

/-- The pool, its workers forked with rc.112's `Effect.forkScoped` options (`forkScopedDefault`). -/
def pool (total : Nat) : Module NativeOp := poolWith (Effect4.Codegen.Forms.defaults true) total

/-- The probe's spelling: the workers forked with `childOptions` (started at once, not daemons). -/
def poolChild (total : Nat) : Module NativeOp := poolWith childOptions total

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

#guard verdict (pool 5) = "built"
#guard verdict (poolChild 5) = "built"
-- The error column is `nat`, not `never`: the gate is the native `Deferred<number, number>`,
-- whose `await` row fails with a number. rc.112's `Deferred<void>` cannot fail.
#guard (built? (pool 5)).map (fun b => (b.ty.answer, b.ty.error, b.closed)) =
  some (.prod .nat .nat, .nat, true)

/-- Red control (the verifier's): the pool's main without awaiting the gate types at `never`, so
the `nat` column above comes from the gate. -/
def poolNoGate (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let closes ← Ref.make (nat 0)
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped (worker closes count gate total)
          (Effect4.Codegen.Forms.defaults true))
        succeed unit)
      let c ← Ref.get closes
      return c }

#guard (built? (poolNoGate 5)).map (fun b => b.ty.error) = some .never

/-! ## 2. The run under a scripted host -/

/-- The host: `take` answers 1 to 5 and then never again; job 2 fails. -/
def hostAnswer (b : Effect4.Api.Built) (takes : Nat) (op : NativeOp) (request : Val) :
    Option Effect4.Api.HostSession.Answer :=
  match op with
  | .external i =>
    if some i = b.positionOf "Jobs.take" then
      if takes < 5 then some (.ofExit (.success (.nat (takes + 1)))) else none
    else if some i = b.positionOf "Jobs.run" then
      if request = .nat 2 then some (.ofExit (.failure (Cause.fail (.tagged "JobFailed" "bad payload"))))
      else some (.ofExit (.success .unit))
    else none
  | _ => none

structure Driver where
  run : Run
  takes : Nat := 0
  /-- Calls the host received: bound in the session. -/
  received : List Effect4.Api.HostSession.Key := []
  /-- Received calls the host does not answer. -/
  hanging : List Effect4.Api.HostSession.Key := []

/-- One step of the probe's policy. The host receives every outstanding call first, binding one
per step. Then it answers the first received call it answers, lowest fiber first. With nothing
to answer, the run flushes. -/
def step (d : Driver) : Driver :=
  let s := d.run
  match s.outstanding.filter (fun a => !(d.received.contains ⟨a.fiber, a.token⟩)) with
  | a :: _ =>
    let key : Effect4.Api.HostSession.Key := ⟨a.fiber, a.token⟩
    let bindOnly := match Effect4.Api.HostSession.Call.at s key with
      | some call => [Effect4.Api.Runner.Command.bind call key.token]
      | none => []
    { d with run := s.play bindOnly, received := d.received ++ [key] }
  | [] =>
    match s.outstanding.filter (fun a => !(d.hanging.contains ⟨a.fiber, a.token⟩)) with
    | a :: _ =>
      let key : Effect4.Api.HostSession.Key := ⟨a.fiber, a.token⟩
      let isTake : Bool := match a.op with
        | .external i => some i == s.built.positionOf "Jobs.take"
        | _ => false
      match hostAnswer s.built d.takes a.op a.request,
          s.session.active.find? (fun bound => bound.key == key) with
      | some answer, some bound =>
        { d with
          run := s.play [.submit (Rows.reply s bound.call key answer), .apply key]
          takes := if isTake then d.takes + 1 else d.takes }
      | _, _ => { d with hanging := d.hanging ++ [key] }
    | [] => { d with run := s.control Effect4.Api.flush }

def drive : Nat → Driver → Driver
  | 0, d => d
  | n + 1, d => drive n (step d)

/-- The root's exit, the takes the host answered, the replies applied and the calls retired. -/
def runPool (m : Module NativeOp) : Option (Option ExitV × Nat × Nat × Nat) :=
  (built? m).map fun b =>
    let d := drive 300 { run := (Run.open b "p3" { fuel := 1000, compileFuel := 2000 }).play Rows.start }
    (d.run.exit, d.takes, d.run.session.applied, d.run.session.retired.length)

-- Five jobs taken and finished (job 2's failure handled), then the gate opens, the scope closes,
-- and all three releases run: the root answers `[3, 5]`. The host answered the lowest fiber's
-- calls first, so worker 1 did every job; workers 2 and 3 were still waiting on their first
-- `take` when the scope interrupted them. The session retired those two calls.
#guard (runPool (pool 5)).map (·.1) = some (some (.success (.list [.nat 3, .nat 5])))
#guard (runPool (pool 5)).map (fun r => (r.2.1, r.2.2.1, r.2.2.2)) = some (5, 10, 2)
-- The probe's spelling runs to the same observations.
#guard runPool (poolChild 5) = runPool (pool 5)

/-- rc.112's answer: the log of `hostruns.log`. Its lines interpolate numbers, and the log is a
list in a `Ref`; the encoding counts instead (section 6). -/
def rc112 : ExitV := .success (.list (["open 1", "open 2", "open 3", "done 1 by 1",
  "failed 2: bad payload", "done 3 by 3", "done 4 by 1", "done 5 by 2", "close 1 Failure",
  "stopped 1", "close 3 Failure", "stopped 3", "close 2 Failure", "stopped 2"].map Val.str))

/-! ## 3. Printing -/

-- The pool prints as TypeScript and reads back as itself.
#guard (built? (pool 5)).map (fun b => printedOf b) = some (true, true)
-- Red control: the probe's child fork into a scope has no rc.112 spelling, and the printer refuses it.
#guard (built? (poolChild 5)).map (fun b => match Effect4.Api.print b.program b.table with
    | .error refusal => refusal == .internalAction "forkScoped:child"
    | .ok _ => false) = some true

/-! ## 4. Which theorem reaches the program -/

-- The pool calls host rows: its row table is not empty, so `run_eq_ref` does not reach it.
open Effect4.Program.Denote in
#guard (built? (pool 5)).map (fun b => (Straight b.program, Looped b.program, b.table.isEmpty)) =
  some (false, false, false)

/-! ## 5. The forms -/

-- The form table admits rc.112's fork spellings and neither `forEach` (DI-89) nor `catchTag`.
#guard ["Effect.forkChild", "Effect.forkScoped"].all formAdmits
#guard ["Effect.forEach", "Effect.catchTag"].filter formAdmits = []

/-! ## 6. What the language refuses -/

/-- `Ref.make<ReadonlyArray<string>>([])`: the log. -/
def logCell : Module NativeOp := program (Ref.make (app "nil" []))

/-- `new JobFailed({ id, reason })`: a payload with a number and a string. -/
def jobFailedModule : Module NativeOp :=
  program (fail (record
    [("_tag", false, .lit "JobFailed"), ("id", false, .nat), ("reason", false, .string)]
    [("_tag", str "JobFailed"), ("id", nat 2), ("reason", str "bad payload")]))

-- A cell holds a number only: the checker refuses the list at the cell's request (rows 42–43).
#guard typingReason? logCell = some (.requestNotSubtype "refMake" (.list .never) .nat)
#guard typingReason? (program (Ref.make (app "cons" [str "open 1", app "nil" []]))) =
  some (.requestNotSubtype "refMake" (.list .string) .nat)
-- A typed failure carries no number (row 120); the tag with a string message types.
#guard verdict jobFailedModule = "typing: errorNotAdmitted"
#guard verdict (program (fail (app "pair" [str "JobFailed", str "bad payload"]))) = "built"
-- `Deferred.make` answers the one native deferred, `Deferred<number, number>`.
#guard (built? (program Deferred.make)).map (fun b => b.ty.answer) =
  some (.handle "Deferred.Deferred<number, number>")

/-! ## 7. The stage -/

def measured : Reach :=
  { refused :=
      [ ("the log as a Ref of a list", verdict logCell)
      , ("JobFailed{id, reason} as a typed failure", verdict jobFailedModule) ]
    admitted := verdict (pool 5) == "built"
    answer := match runPool (pool 5) with
      | some r => answerOf r.1 rc112
      | none => .notRun
    printed := ((built? (pool 5)).map fun b => (printedOf b).1) == some true
    readBack := ((built? (pool 5)).map fun b => (printedOf b).2) == some true }

/-- The stage p3 reaches today, as `Test/Dogfood/README.md` quotes it: admitted and run under the
scripted host, with counts where rc.112 answers the log; printed and read back. -/
def stage : Reach :=
  { refused :=
      [ ("the log as a Ref of a list", "typing: requestNotSubtype")
      , ("JobFailed{id, reason} as a typed failure", "typing: errorNotAdmitted") ]
    admitted := true, answer := .differs, printed := true, readBack := true }

#guard measured = stage

end Test.Dogfood.P3WorkerQueue

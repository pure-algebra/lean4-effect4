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
* The error payload landed (decisions row 120, parts E1 and E2). `JobFailed{id, reason}` builds
  as a typed failure and runs to `Err.payload`. It prints as a module that declares its
  `Data.TaggedError` class and fails with `new JobFailed({ … })`, and the module reads back
  (section 7). The worker still catches the host's pair.

**Changes in the state plan's T3a.** `Ref` and `Deferred` are templates over their types. The log
`Ref.make([])` builds at `Ref<never[]>`, and its first append is refused, since the cell is
invariant. `Deferred.make` carries its type arguments, so the gate builds at `Deferred<void, never>`,
runs, and its `await` cannot fail; the printer refuses it by name until T5 spells the type
arguments. The measured pool keeps today's instance, `Deferred<number, number>`, so it still prints
and reads back.

**Changes in the state plan's T3b.** A read-modify-write row carries a binder term. The log's
append is rc.112's `Ref.update(log, lines => [...lines, line])`: with the cell ascribed at
`ReadonlyArray<string>` it builds and runs to its lines, and at `Ref<never[]>` the checker refuses
the term's result (`resultNotSubtype`). rc.112's `finish`, one `Ref.modify` that counts and decides
"last" in one store step, builds and answers a boolean over a number cell. Neither term is a name's
image, so the printer refuses both rows by name until the state plan's T5. The measured pool keeps
its counters at `n => succ(n)`, the image of `incr`, so its stage does not move.

**What the language refuses** (section 6): the log's append at `Ref<never[]>`
(`resultNotSubtype`); the gate `Deferred<void, never>` in TypeScript (the printer, by name); the
forms `forEach` and `catchTag`. A queue has no spelling inside a program: DI-11 rules it a composite
over `Ref`, `Deferred` and a wait list. When the scope interrupts a worker parked on the host's
`take`, the session retires the call; rc.112's take is in-process.

**Waits on:** R4, the faces' part (the log's element type as a type argument, the gate's printing,
and a binder term printed as a lambda: the state plan's T5); R10 with DI-11 (the queue composite)
and DI-89 (`forEach`); R3 with row 130 (`catchTag`'s residual over records); row 131 (the log lines
interpolate numbers); R11 (release on interruption, the whole run). The slice of row 204 that
moves it next: queues.
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
    let _conn ← acquireRelease "conn" "exit" (succeed unit) (Ref.update "n" (app "succ" [var "n"]) closes)
    iterateWith (bool true)
      { while_ := fun _ => bool true
        body := fun _ => eff do
          let job ← Row.call take unit
          let _ ← catchIf "e" (app "tagIs" [str "JobFailed", var "e"])
            (Row.call runJob job) (succeed unit)
          let n ← Ref.updateAndGet "n" (app "succ" [var "n"]) count
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
      let gate ← Deferred.make .nat .nat
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
-- The error column is `nat`, not `never`: the measured gate is `Deferred<number, number>`, whose
-- `await` fails with a number, the instance the printer spells today. rc.112's `Deferred<void>`
-- cannot fail; it builds since T3a (section 6).
#guard (built? (pool 5)).map (fun b => (b.ty.answer, b.ty.error, b.closed)) =
  some (.prod .nat .nat, .nat, true)

/-- Red control (the verifier's): the pool's main without awaiting the gate types at `never`, so
the `nat` column above comes from the gate. -/
def poolNoGate (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let closes ← Ref.make (nat 0)
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make .nat .nat
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

/-- `Ref.make<ReadonlyArray<string>>([])`: the log. With no type argument the empty list types at
`never[]`. -/
def logCell : Module NativeOp := program (Ref.make (app "nil" []))

/-- `note(log, line)`, rc.112's append: `Ref.update(log, lines => [...lines, line])`. -/
def note (log : TermSrc) (line : String) : Src NativeOp :=
  Ref.update "lines" (app "append" [var "lines", app "cons" [str line, app "nil" []]]) log

/-- The log's first append at the bare cell, `Ref<never[]>`. -/
def logAppend : Module NativeOp :=
  program (bindName "log" (Ref.make (app "nil" [])) fun log => note log "open 1")

/-- The same append by a whole-value write, `Ref.set(log, ["open 1"])`. -/
def logSet : Module NativeOp :=
  program (bindName "log" (Ref.make (app "nil" [])) fun log =>
    Ref.set log (app "cons" [str "open 1", app "nil" []]))

/-- `e : T`, written with the language's one written term type, a record's declared field (seat
T3a's measured ascription; `Ref.make<A>` lands at the state plan's T5). -/
def ascribe (ty : Ty) (e : TermSrc) : TermSrc := field (record [("v", false, ty)] [("v", e)]) "v"

/-- `Ref.make<ReadonlyArray<string>>([])`, two appends, then the log. -/
def logAscribed : Module NativeOp :=
  program (bindName "log" (Ref.make (ascribe (.list .string) (app "nil" []))) fun log =>
    andThen (note log "open 1") (andThen (note log "done 1 by 1") (Ref.get log)))

/-- rc.112's `finish`: `Ref.modify(count, n => [n + 1 === total, n + 1])`, one store step that
counts and decides "last". The module answers the decision and the count it left. -/
def finishModule (start total : Nat) : Module NativeOp :=
  program (bindName "count" (Ref.make (nat start)) fun count =>
    bindName "last" (Ref.modify "n"
        (app "pair" [app "eq" [app "succ" [var "n"], nat total], app "succ" [var "n"]]) count)
      fun last => bindName "n" (Ref.get count) fun n => succeed (app "pair" [last, n]))

/-- rc.112's gate, `Deferred.make<void>()`, completed and awaited. -/
def gateModule : Module NativeOp :=
  program (bindName "g" (Deferred.make .unit .never) fun g =>
    andThen (Deferred.succeed g unit) (Deferred.await g))

/-- `new JobFailed({ id, reason })`: a payload with a number and a string. -/
def jobFailedModule : Module NativeOp :=
  program (fail (record
    [("_tag", false, .lit "JobFailed"), ("id", false, .nat), ("reason", false, .string)]
    [("_tag", str "JobFailed"), ("id", nat 2), ("reason", str "bad payload")]))

-- A cell holds any type (the state plan's T3a): the empty log builds at `Ref<never[]>`, and a cell
-- is invariant. Its first append is refused at the term's result: the term answers `string[]`,
-- and the cell holds `never[]` (the state plan's T3b).
#guard (built? logCell).map (fun b => b.ty.answer) = some (.refOf (.list .never))
#guard typingReason? logAppend = some (.resultNotSubtype "refUpdateWith"
  (.list .string) (.list .never))
-- The whole-value write is refused at `Ref.set`'s request, as before T3b.
#guard typingReason? logSet = some (.requestNotSubtype "refSet"
  (.prod (.refOf (.list .never)) (.list .string)) (.prod (.refOf (.var 0)) (.var 0)))
-- With the cell ascribed at its element type the append builds and runs to its lines.
#guard (built? logAscribed).map (fun b => (b.ty.answer, b.runSync)) =
  some (.list .string, .success (.list [.str "open 1", .str "done 1 by 1"]))
-- The append's term is no name's image: the printer refuses the row by name until T5.
#guard (built? logAscribed).map printVerdict = some "refused: binderTerm Ref.update"
-- rc.112's `finish` builds: over a number cell the row answers a boolean, `B` is not `A`. The
-- fifth job of five is the last, and the fourth is not.
#guard (built? (finishModule 4 5)).map (fun b => (b.ty.answer, b.runSync)) =
  some (.prod .bool .nat, .success (.list [.bool true, .nat 5]))
#guard (built? (finishModule 3 5)).map (·.runSync) = some (.success (.list [.bool false, .nat 4]))
#guard (built? (finishModule 4 5)).map printVerdict = some "refused: binderTerm Ref.modify"
-- Green control: a log made with a line types at its element.
#guard (built? (program (Ref.make (app "cons" [str "open 1", app "nil" []])))).map
  (fun b => b.ty.answer) = some (.refOf (.list .string))
-- The gate at `Deferred<void, never>` builds and runs: its `await` cannot fail.
#guard (built? gateModule).map (fun b => (b.ty.answer, b.ty.error)) = some (.unit, .never)
#guard (built? gateModule).map (·.runSync) = some (.success .unit)
-- The printer refuses it by name: the faces spell `Deferred.make` at one instance until T5.
#guard (built? gateModule).map printVerdict = some "refused: typeSpelling Deferred.make"
-- The error payload carrier (row 120, part E1): the record is a typed failure (section 7); the
-- tag with a string message still types as the pair.
#guard verdict jobFailedModule = "built"
#guard verdict (program (fail (app "pair" [str "JobFailed", str "bad payload"]))) = "built"
-- The worker's `catchTag("JobFailed", …)` catches the payload by its `_tag`.
#guard (built? (program (catchIf "e" (app "tagIs" [str "JobFailed", var "e"])
    (fail (record [("_tag", false, .lit "JobFailed"), ("id", false, .nat), ("reason", false, .string)]
      [("_tag", str "JobFailed"), ("id", nat 2), ("reason", str "bad payload")]))
    (succeed (field (var "e") "reason"))))).map (·.runSync) = some (.success (.str "bad payload"))
-- `Deferred.make` at the faces' instance answers `Deferred<number, number>`, prints and reads back.
#guard (built? (program (Deferred.make .nat .nat))).map (fun b => b.ty.answer) =
  some (.deferredOf .nat .nat)
#guard (built? (program (Deferred.make .nat .nat))).map printedOf = some (true, true)

/-! ## 7. The stage -/

def measured : Reach :=
  { refused :=
      [ ("the log's append at Ref<never[]>", verdict logAppend)
      , ("the gate as Deferred<void> in TypeScript",
          ((built? gateModule).map printVerdict).getD "not built") ]
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
      [ ("the log's append at Ref<never[]>", "typing: resultNotSubtype")
      , ("the gate as Deferred<void> in TypeScript", "refused: typeSpelling Deferred.make") ]
    admitted := true, answer := .differs, printed := true, readBack := true }

#guard measured = stage

/-- The failure `run-p3.ts` raises for job 2: `JobFailed{id: 2, reason: "bad payload"}`, which
`hostruns.log` records as its log line `failed 2: bad payload`. -/
def jobFailed2 : Val :=
  recordOf ["_tag", "id", "reason"] [.str "JobFailed", .nat 2, .str "bad payload"]

/-- How far the payload part gets (decisions row 120, parts E1 and E2). -/
def payloadMeasured : List (String × PartReach) :=
  [("JobFailed{id, reason} as a typed failure", partReach jobFailedModule jobFailed2)]

/-- The payload part's stage, as `Test/Dogfood/README.md` quotes it: built, run to `Err.payload`,
printed as a module that declares its `JobFailed` class and fails with `new JobFailed({ … })`, and
read back. -/
def payloadStage : List (String × PartReach) :=
  [("JobFailed{id, reason} as a typed failure", ⟨"built", true, "printed", true⟩)]

#guard payloadMeasured = payloadStage

/-- The requirements of the system map's §8 that this program waits on, as its row in
`Test/Dogfood/README.md` explains them. The semantics report lists the program under each and
prints `stage` beside it (decisions row 206). -/
def waitsOn : List String := ["R3", "R4", "R10", "R11"]

end Test.Dogfood.P3WorkerQueue

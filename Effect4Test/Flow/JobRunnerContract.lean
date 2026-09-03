/-
Contract packet: the job runner, the first harness program written the way an
Effect user would write one (`docs/research/2026-09-03-job-runner.md`).

The six goldens of `generated/traces/job/` as `#guard` receipts over the Lean
runners, the admission and site-separation receipts, the refusals the
program ran into, and the axiom report. `harness/trace/Generate.lean` is a
script, not a library, so the family, the queue handler and the two graphs are
restated here and the goldens are the join of the two copies -- the same
arrangement `Effect4Test/Flow/InterruptContract.lean` uses. Doc comments cannot
precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Flow.Interrupt
import Effect4.Meta.Derive

namespace Effect4Test.Flow.JobRunnerContract

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

#check @Effect4.Flow.runRegionsDefault
#check @Effect4.Flow.runInterruptsDefault
#check @Effect4.Flow.sitesSeparated

effect_signature Jobs where
  | connect : Handle "JobQueue" ⟪ "open a connection to the job queue", "the connection" ⟫
  | next (conn : Handle "JobQueue") : Handle "JobQueue" × Nat
      ⟪ "dequeue the next job", "a ticket: the connection and the job id, 0 when empty" ⟫
  | run (conn : Handle "JobQueue") (job : Nat) : Nat !! String
      ⟪ "run a job on its connection", "aborts with the job's error" ⟫
  | attempt (job : Nat) : Except String Nat
      ⟪ "run a job, reporting its error as data", "the flow has no failure handler" ⟫
  | ack (conn : Handle "JobQueue") (job : Nat) : Unit
      ⟪ "acknowledge a finished job on its connection" ⟫
  | requeue (conn : Handle "JobQueue") (job : Nat) : Unit
      ⟪ "put a job back at the end of its connection's queue" ⟫
  | disconnect (conn : Handle "JobQueue") : Unit ⟪ "close the connection" ⟫

/-- The queue state, as `harness/trace/Generate.lean` and
`harness/trace/job-queue.ts` both keep it. -/
structure Queue where
  pending : List Nat
  acked : List Nat
  requeued : List Nat
  failures : List (Nat × Nat)
deriving DecidableEq, Repr, Inhabited

namespace Queue

def failuresLeft (queue : Queue) (job : Nat) : Nat :=
  match queue.failures.find? (·.1 == job) with
  | some entry => entry.2
  | none => 0

def consumeFailure (queue : Queue) (job : Nat) : Queue :=
  { queue with failures := queue.failures.map fun entry =>
      if entry.1 == job then (entry.1, entry.2 - 1) else entry }

def seed (pending : List Nat) (failures : List (Nat × Nat) := []) : Queue :=
  { pending := pending, acked := [], requeued := [], failures := failures }

end Queue

def jobError (job : Nat) : String := "job " ++ toString job ++ " failed"

def jobsFamily : String → Val → StateT Queue Id (Except Val Val)
  | "connect", _ => pure (.ok (.nat 0))
  | "next", conn => do
      let queue ← get
      match queue.pending with
      | [] => pure (.ok (.pair conn (.nat 0)))
      | job :: rest => do
          set { queue with pending := rest }
          pure (.ok (.pair conn (.nat job)))
  | "run", .pair _ (.nat job) => do
      let queue ← get
      if queue.failuresLeft job == 0 then pure (.ok (.nat job))
      else do
        set (queue.consumeFailure job)
        pure (.error (.str (jobError job)))
  | "attempt", .nat job => do
      let queue ← get
      if queue.failuresLeft job == 0 then pure (.ok (.pair (.bool true) (.nat job)))
      else do
        set (queue.consumeFailure job)
        pure (.ok (.pair (.bool false) (.str (jobError job))))
  | "ack", .pair _ (.nat job) => do
      modify fun queue => { queue with acked := queue.acked ++ [job] }
      pure (.ok .unit)
  | "requeue", .pair _ (.nat job) => do
      modify fun queue =>
        { queue with pending := queue.pending ++ [job], requeued := queue.requeued ++ [job] }
      pure (.ok .unit)
  | "disconnect", _ => pure (.ok .unit)
  | _, _ => pure (.ok .unit)

def jobAtom : String → Val → Val
  | "succ", .nat n => .nat (n + 1)
  | "dec", .nat n => .nat (n - 1)
  | "snd", .pair _ (.nat job) => .nat job
  | "nonEmpty", .pair _ (.nat job) => .bool (job != 0)
  | "positive", .nat n => .bool (n != 0)
  | _, _ => .unit

def handleTy : String := "JobQueue"

/-- What `next` answers and what the three two-parameter operations take: one
right-nested product, so one block slot serves both readings. -/
def ticketTy : String := "readonly [" ++ handleTy ++ ", number]"

def table : List OpSpec := familyTable Jobs.rows ++
  [ { name := "unit", kind := .lit .unit, requestTy := "number", answerTy := "void" }
  , { name := "zero", kind := .lit (.nat 0), requestTy := "number", answerTy := "number" }
  , { name := "succ", kind := .atom, requestTy := "number", answerTy := "number" }
  , { name := "dec", kind := .atom, requestTy := "number", answerTy := "number" }
  , { name := "snd", kind := .atom, requestTy := ticketTy, answerTy := "number" }
  , { name := "nonEmpty", kind := .atom, requestTy := ticketTy, answerTy := "boolean" }
  , { name := "positive", kind := .atom, requestTy := "number", answerTy := "boolean" } ]

def opConnect : OperationId := ⟨0⟩
def opNext : OperationId := ⟨1⟩
def opRun : OperationId := ⟨2⟩
def opAttempt : OperationId := ⟨3⟩
def opAck : OperationId := ⟨4⟩
def opRequeue : OperationId := ⟨5⟩
def opDisconnect : OperationId := ⟨6⟩
def opUnit : OperationId := ⟨7⟩
def opZero : OperationId := ⟨8⟩
def opSucc : OperationId := ⟨9⟩
def opDec : OperationId := ⟨10⟩
def opSnd : OperationId := ⟨11⟩
def opNonEmpty : OperationId := ⟨12⟩
def opPositive : OperationId := ⟨13⟩

def resultTy : String := "Result.Result<number, string>"

def jblock (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) :
    RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

def jregion (id : Nat) (parent : Option Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := parent.map RegionId.mk, continue_ := ⟨continue_⟩, resultTy := "number" }

def vars (n : Nat) : List Var := (List.range n).map Var.mk

/-- `generated/traces/job/jobRunner.*.tsv` and `jobRunnerMasked.masked.tsv`. -/
def runnerFlow : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := [jregion 1 none 17],
    blocks :=
      [ jblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
      , jblock 1 (some 1) ["number"] (.plain (.perform opUnit ⟨0⟩ ⟨2⟩ (vars 1)))
      , jblock 2 (some 1) ["number", "void"] (.acquire opConnect ⟨1⟩ opDisconnect ⟨3⟩ (vars 1))
      , jblock 3 (some 1) ["number", handleTy] (.plain (.perform opZero ⟨0⟩ ⟨4⟩ [⟨1⟩, ⟨0⟩]))
      , jblock 4 (some 1) [handleTy, "number", "number"]
          (.plain (.perform opNext ⟨0⟩ ⟨5⟩ (vars 3)))
      , jblock 5 (some 1) [handleTy, "number", "number", ticketTy]
          (.plain (.perform opNonEmpty ⟨3⟩ ⟨6⟩ (vars 4)))
      , jblock 6 (some 1) [handleTy, "number", "number", ticketTy, "boolean"]
          (.plain (.branch ⟨4⟩ ⟨1⟩ ⟨8⟩ ⟨7⟩ (vars 4)))
      , jblock 7 (some 1) [handleTy, "number", "number", ticketTy] (.leave ⟨2⟩)
      , jblock 8 (some 1) [handleTy, "number", "number", ticketTy]
          (.plain (.performCatch opRun ⟨3⟩ ⟨10⟩ (vars 4) ⟨12⟩ (vars 4)))
      , jblock 9 (some 1) [handleTy, "number", "number", ticketTy, "boolean"]
          (.plain (.branch ⟨4⟩ ⟨3⟩ ⟨13⟩ ⟨14⟩ (vars 4)))
      , jblock 10 (some 1) [handleTy, "number", "number", ticketTy, "number"]
          (.plain (.perform opAck ⟨3⟩ ⟨11⟩ (vars 3)))
      , jblock 11 (some 1) [handleTy, "number", "number", "void"]
          (.plain (.perform opSucc ⟨2⟩ ⟨4⟩ (vars 2)))
      , jblock 12 (some 1) [handleTy, "number", "number", ticketTy, "string"]
          (.plain (.perform opPositive ⟨1⟩ ⟨9⟩ (vars 4)))
      , jblock 13 (some 1) [handleTy, "number", "number", ticketTy]
          (.plain (.perform opDec ⟨1⟩ ⟨15⟩ [⟨0⟩, ⟨2⟩, ⟨3⟩]))
      , jblock 14 (some 1) [handleTy, "number", "number", ticketTy]
          (.plain (.perform opRequeue ⟨3⟩ ⟨16⟩ (vars 3)))
      , jblock 15 (some 1) [handleTy, "number", ticketTy, "number"]
          (.plain (.jump ⟨8⟩ [⟨0⟩, ⟨3⟩, ⟨1⟩, ⟨2⟩]))
      , jblock 16 (some 1) [handleTy, "number", "number", "void"]
          (.plain (.jump ⟨4⟩ (vars 3)))
      , jblock 17 none ["number"] (.plain (.ret ⟨0⟩)) ] }

/-- `generated/traces/job/jobPoison.poison.tsv`: the packet's aborting `run`. -/
def poisonFlow : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := [jregion 1 none 6],
    blocks :=
      [ jblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
      , jblock 1 (some 1) ["number"] (.plain (.perform opUnit ⟨0⟩ ⟨2⟩ (vars 1)))
      , jblock 2 (some 1) ["number", "void"] (.acquire opConnect ⟨1⟩ opDisconnect ⟨3⟩ (vars 1))
      , jblock 3 (some 1) ["number", handleTy] (.plain (.perform opNext ⟨1⟩ ⟨4⟩ []))
      , jblock 4 (some 1) [ticketTy] (.plain (.perform opRun ⟨0⟩ ⟨5⟩ []))
      , jblock 5 (some 1) ["number"] (.leave ⟨0⟩)
      , jblock 6 none ["number"] (.plain (.ret ⟨0⟩)) ] }

def choice (site : Nat) (branch : Bool) : Decision := ⟨⟨site⟩, branch⟩
def more (b : Bool) : Decision := choice 1 b
def retried (b : Bool) : Decision := choice 3 b
def deliverAtPerform (block : Nat) (b : Bool) : Decision := ⟨(Point.perform ⟨block⟩).site, b⟩

def service : RegionService (tableAlphabet ⟨0⟩ table) (StateT Queue Id) :=
  Flow.tableRegionService ⟨0⟩ table jobsFamily jobAtom

def named : (tableAlphabet ⟨0⟩ table).Op → String := tableNameOf ⟨0⟩ table

/-- The interrupted run of the drain: its result, its log and the queue it
leaves behind. -/
def runInterrupted (masked : List RegionId) (tape itape : Tape) (queue : Queue) :
    Option (InterruptResult × Effect4.Trace.Log × Queue) :=
  match admitRegions (tableAlphabet ⟨0⟩ table) runnerFlow with
  | .ok flow =>
      let r := ((Flow.runInterruptsDefault flow masked service named tape itape (.nat 2)).run
        []).run queue
      some (r.1.1.1, r.1.2, r.2)
  | .error _ => none

/-- The plain region run of the poison job. -/
def runPoison (queue : Queue) : Option (RunResult × Effect4.Trace.Log × Queue) :=
  match admitRegions (tableAlphabet ⟨0⟩ table) poisonFlow with
  | .ok flow =>
      let r := ((Flow.runRegionsDefault flow service named [] (.nat 2)).run []).run queue
      some (r.1.1.1, r.1.2, r.2)
  | .error _ => none

/-! ## 1. Admission, separation and the interrupt sites -/

-- Both graphs are admitted region flows: the entry is outside every region, no
-- `ret` sits inside one, the release takes the acquired answer, the region's
-- `continue_` block is outside it and takes exactly the result, and every cycle
-- of the drain passes a `choose`.
#guard (admitRegions (tableAlphabet ⟨0⟩ table) runnerFlow).isOk
#guard (admitRegions (tableAlphabet ⟨0⟩ table) poisonFlow).isOk

-- Every `choose` site the author wrote lies below `interruptBase`, so one wire
-- tape can carry both the choices and the interrupts without either answering
-- the other's question. This is what lets a job golden's `tape` header be one
-- list that `harness/trace/job-tail.ts` splits by site.
#guard sitesSeparated runnerFlow && sitesSeparated poisonFlow
#guard Effect4.Flow.interruptBase = 1000000

-- The interrupt sites the goldens name: the queue test, the caught `run` the
-- drain is interrupted before, and the region's own `leave`.
#guard (Point.perform ⟨5⟩).site = ⟨1000011⟩
#guard (Point.perform ⟨8⟩).site = ⟨1000017⟩
#guard (Point.leave ⟨1⟩).site = ⟨1000002⟩

-- The release is one operation of the alphabet and it takes what `connect`
-- answered: this is the region contract's `acquireRelease` clause, and it is
-- why the connection can be closed from the finalizer at all.
#guard (tableAlphabet ⟨0⟩ table).requestTy ⟨6, by decide⟩ =
  (tableAlphabet ⟨0⟩ table).answerTy ⟨0, by decide⟩

/-! ## 2. The six goldens -/

def cleanTape : Tape := [more true, more true, more true, more false]

def retryTape : Tape := [more true, more true, retried true, more false]

def requeueTape : Tape :=
  [more true, retried true, retried true, retried false, more true, more false]

def interruptTape : Tape := [more true, more true]

def interruptITape : Tape := [deliverAtPerform 8 false, deliverAtPerform 8 true]

def maskedTape : Tape := [more true, more true, more false]

-- Golden 1, a clean run of three jobs. The connection is acquired inside
-- region 1; three tickets are dequeued, each `nonEmpty` branch reports `true`,
-- each caught `run` takes its value edge and is acknowledged; the fourth
-- ticket is empty, the branch reports `false`, the region closes with the
-- acknowledged count and its release closes the connection.
#guard (runInterrupted [] cleanTape [] (Queue.seed [1, 2, 3])).map (fun r => (r.1, r.2.1)) =
  some (Effect4.Flow.InterruptResult.done (Effects.Trace.Val.nat 3),
   [Effects.Trace.Event.enter 1,
    Effects.Trace.Event.decide 1000003 false,
    Effects.Trace.Event.op "connect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.answer "connect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.decide 1000007 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 1),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 2),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 3)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 3)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 3),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 3)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 0)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 false,
    Effects.Trace.Event.decide 1000002 false,
    Effects.Trace.Event.leave 1 (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 3)),
    Effects.Trace.Event.finalizer 1 (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 3)),
    Effects.Trace.Event.op "disconnect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "disconnect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.done (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 3))])

-- Golden 2, a job that fails once and succeeds on the retry. The caught `run`
-- writes its `failed` row and continues on the failure edge; `positive` of the
-- budget (2) is `true`, the branch reports it, `dec` spends one attempt (no row:
-- an atom is pure), and the second `run` of the same ticket succeeds.
#guard (runInterrupted [] retryTape [] (Queue.seed [1, 2] [(2, 1)])).map (fun r => (r.1, r.2.1)) =
  some (Effect4.Flow.InterruptResult.done (Effects.Trace.Val.nat 2),
   [Effects.Trace.Event.enter 1,
    Effects.Trace.Event.decide 1000003 false,
    Effects.Trace.Event.op "connect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.answer "connect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.decide 1000007 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 1),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.failed "run" (Effects.Trace.Val.str "job 2 failed"),
    Effects.Trace.Event.decide 1000025 false,
    Effects.Trace.Event.decide 3 true,
    Effects.Trace.Event.decide 1000027 false,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 2),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 0)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 false,
    Effects.Trace.Event.decide 1000002 false,
    Effects.Trace.Event.leave 1 (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.finalizer 1 (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.op "disconnect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "disconnect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.done (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 2))])

-- Golden 3, a job requeued after its retries are exhausted. Three scheduled
-- failures against a budget of 2: two retries, then `positive 0` reports
-- `false` and the job is put back; the drain dequeues it again, it succeeds,
-- and the region closes with one job acknowledged.
#guard (runInterrupted [] requeueTape [] (Queue.seed [2] [(2, 3)])).map (fun r => (r.1, r.2.1)) =
  some (Effect4.Flow.InterruptResult.done (Effects.Trace.Val.nat 1),
   [Effects.Trace.Event.enter 1,
    Effects.Trace.Event.decide 1000003 false,
    Effects.Trace.Event.op "connect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.answer "connect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.decide 1000007 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.failed "run" (Effects.Trace.Val.str "job 2 failed"),
    Effects.Trace.Event.decide 1000025 false,
    Effects.Trace.Event.decide 3 true,
    Effects.Trace.Event.decide 1000027 false,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.failed "run" (Effects.Trace.Val.str "job 2 failed"),
    Effects.Trace.Event.decide 1000025 false,
    Effects.Trace.Event.decide 3 true,
    Effects.Trace.Event.decide 1000027 false,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.failed "run" (Effects.Trace.Val.str "job 2 failed"),
    Effects.Trace.Event.decide 1000025 false,
    Effects.Trace.Event.decide 3 false,
    Effects.Trace.Event.decide 1000029 false,
    Effects.Trace.Event.op "requeue" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "requeue" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 2),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 0)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 false,
    Effects.Trace.Event.decide 1000002 false,
    Effects.Trace.Event.leave 1 (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.finalizer 1 (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.op "disconnect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "disconnect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.done (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 1))])

-- Golden 4, an interrupt delivered mid-queue. Job 1 is acknowledged; the
-- interrupt is delivered at the point before the second job's caught `run`,
-- the region closes `interrupted`, and the release still runs.
#guard (runInterrupted [] interruptTape interruptITape (Queue.seed [1, 2, 3])).map (fun r => (r.1, r.2.1)) =
  some (Effect4.Flow.InterruptResult.interrupted,
   [Effects.Trace.Event.enter 1,
    Effects.Trace.Event.decide 1000003 false,
    Effects.Trace.Event.op "connect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.answer "connect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.decide 1000007 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 1),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 true,
    Effects.Trace.Event.leave 1 (Effects.Trace.Outcome.interrupted),
    Effects.Trace.Event.finalizer 1 (Effects.Trace.Outcome.interrupted),
    Effects.Trace.Event.op "disconnect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "disconnect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.done (Effects.Trace.Outcome.interrupted)])

-- Golden 5, an interrupt requested inside the masked critical section. The
-- request at the second job's point defers, the region's own `leave` point is
-- masked too, the region closes cleanly with both jobs acknowledged, the
-- release runs with that success exit, and the pending interrupt is delivered
-- at the restoration (the M2 repair).
#guard (runInterrupted [⟨1⟩] maskedTape interruptITape (Queue.seed [1, 2])).map (fun r => (r.1, r.2.1)) =
  some (Effect4.Flow.InterruptResult.interrupted,
   [Effects.Trace.Event.enter 1,
    Effects.Trace.Event.decide 1000003 false,
    Effects.Trace.Event.op "connect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.answer "connect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.decide 1000007 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 false,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 1),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 1)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 true,
    Effects.Trace.Event.decide 1000017 true,
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "run" (Effects.Trace.Val.nat 2),
    Effects.Trace.Event.decide 1000021 false,
    Effects.Trace.Event.op "ack" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.answer "ack" (Effects.Trace.Val.unit),
    Effects.Trace.Event.decide 1000023 false,
    Effects.Trace.Event.decide 1000009 false,
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 0)),
    Effects.Trace.Event.decide 1000011 false,
    Effects.Trace.Event.decide 1 false,
    Effects.Trace.Event.decide 1000002 false,
    Effects.Trace.Event.leave 1 (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.finalizer 1 (Effects.Trace.Outcome.success (Effects.Trace.Val.nat 2)),
    Effects.Trace.Event.op "disconnect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "disconnect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.done (Effects.Trace.Outcome.interrupted)])

-- Golden 6, the packet's aborting `run`, *uncaught*: the poison job's `perform`
-- is plain, its abort closes region 1 with the failure, the release runs on
-- that path, and the run ends `failed`.
#guard (runPoison (Queue.seed [7] [(7, 1)])).map (fun r => (r.1, r.2.1)) =
  some (Effect4.Flow.RunResult.failed (Effects.Trace.Val.str "job 7 failed"),
   [Effects.Trace.Event.enter 1,
    Effects.Trace.Event.op "connect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.answer "connect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.op "next" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "next" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 7)),
    Effects.Trace.Event.op "run" (Effects.Trace.Val.pair (Effects.Trace.Val.nat 0) (Effects.Trace.Val.nat 7)),
    Effects.Trace.Event.failed "run" (Effects.Trace.Val.str "job 7 failed"),
    Effects.Trace.Event.leave 1 (Effects.Trace.Outcome.failure (Effects.Trace.Val.str "job 7 failed")),
    Effects.Trace.Event.finalizer 1 (Effects.Trace.Outcome.failure (Effects.Trace.Val.str "job 7 failed")),
    Effects.Trace.Event.op "disconnect" (Effects.Trace.Val.nat 0),
    Effects.Trace.Event.answer "disconnect" (Effects.Trace.Val.unit),
    Effects.Trace.Event.done (Effects.Trace.Outcome.failure (Effects.Trace.Val.str "job 7 failed"))])

/-! ## 3. What the runs left behind

The queue is real state on both faces: the Lean handler threads it, the host
tail keeps the same four fields in a JSON file. These are the Lean face's; the
host's `disconnect` deletes the file, and the tail reports `released` for every
golden -- the interrupted and the failing ones included.
-/

-- The clean run acknowledged all three jobs and emptied the queue.
#guard (runInterrupted [] cleanTape [] (Queue.seed [1, 2, 3])).map (·.2.2) =
  some { pending := [], acked := [1, 2, 3], requeued := [], failures := [] }

-- The retry run spent job 2's one scheduled failure and acknowledged both jobs.
#guard (runInterrupted [] retryTape [] (Queue.seed [1, 2] [(2, 1)])).map (·.2.2) =
  some { pending := [], acked := [1, 2], requeued := [], failures := [(2, 0)] }

-- The requeue run spent all three of job 2's failures, put it back once, took
-- it again and acknowledged it: the drain now reads what `next` answers
-- (`E4-FLOW-CE-027`, repaired), so the queue is empty because it was drained.
#guard (runInterrupted [] requeueTape [] (Queue.seed [2] [(2, 3)])).map (·.2.2) =
  some { pending := [], acked := [2], requeued := [2], failures := [(2, 0)] }

-- The interrupted run acknowledged only the first job; the rest of the queue is
-- untouched, and the connection was still released (the `disconnect` rows above).
#guard (runInterrupted [] interruptTape interruptITape (Queue.seed [1, 2, 3])).map (·.2.2) =
  some { pending := [3], acked := [1], requeued := [], failures := [] }

/-! ## 4. The refusals this program ran into

Each is a fact about the pipeline, stated over the actual declarations. The
full account is `docs/research/2026-09-03-job-runner.md`; the register rows are
`E4-FLOW-CE-026`, `E4-FLOW-CE-027` and `E4-FLOW-CE-028`, with their attack
batteries under `Effect4Test/Counterexamples/`. `E4-TARGET-CE-022` -- a
two-parameter operation has no flow request spelling -- is repaired: the row
below is the repair, not the refusal.
-/

-- The packet's `run : Handle × Nat → Nat !! String`, performed. Its request is
-- the right-nested product spelling, its arity is two, and the lowering
-- destructures the one request slot at the call.
#guard ((familyTable Jobs.rows).find? (·.name == "run")).map (·.requestTy) =
  some "readonly [JobQueue, number]"
#guard ((familyTable Jobs.rows).find? (·.name == "run")).map OpSpec.arity = some 2
#guard ((familyTable Jobs.rows).find? (·.name == "attempt")).map (·.requestTy) = some "number"

-- `E4-FLOW-CE-028`. The pair is not *built* by the flow: `plan` hands a service
-- one `Val`, so a two-parameter request can only occupy a slot some answer
-- already filled. `next` is that answer, and its spelling is exactly `run`'s
-- request -- which is why one slot serves both.
#guard ((familyTable Jobs.rows).find? (·.name == "next")).map (·.answerTy) =
  ((familyTable Jobs.rows).find? (·.name == "run")).map (·.requestTy)

-- `E4-FLOW-CE-026`, repaired by Flow v3. An *uncaught* abort still ends the
-- run: the poison golden's `run` is a plain `perform`, its `failed` row is
-- followed only by the region's close, and the result is `failed`.
#guard (runPoison (Queue.seed [7] [(7, 1)])).map (·.1) = some (.failed (.str "job 7 failed"))

-- The drain's `run` is *caught*: after its `failed` row the run continues on
-- the failure edge, decides the retry, and performs `run` again.
#guard (runInterrupted [] retryTape [] (Queue.seed [1, 2] [(2, 1)])).map
    (fun r => r.2.1.count (.op "run" (.pair (.nat 0) (.nat 2)))) = some 2
#guard (runInterrupted [] retryTape [] (Queue.seed [1, 2] [(2, 1)])).map
    (fun r => r.2.1.count (.failed "run" (.str "job 2 failed"))) = some 1

-- `E4-FLOW-CE-027`, repaired by Flow v3. The drain reads `next`'s answer: on
-- an empty queue the `nonEmpty` branch takes the leave, nothing is run, and the
-- region closes with no job acknowledged.
#guard (runInterrupted [] [more false] [] (Queue.seed [])).map
    (fun r => (r.1, r.2.1.any fun event => match event with | .op "run" _ => true | _ => false))
  = some (.done (.nat 0), false)

-- And a branch is still a decision site: a tape that says "another job" when
-- the value says the queue is empty is refused, never followed.
#guard (runInterrupted [] [more true] [] (Queue.seed [])).map (·.1) = some (.refused ⟨1⟩ ⟨1⟩)

-- The packet's third predicted gap, "the interrupt tape is per program not per
-- job", is half refuted. A tape whose only entry names the `attempt` point does
-- deliver at the *first* visit, so no job is ever acknowledged...
#guard (runInterrupted [] [more true] [deliverAtPerform 8 true] (Queue.seed [1, 2, 3])).map
    (fun r => r.2.1.any fun event => event == .op "ack" (.pair (.nat 0) (.nat 1))) = some false
-- ...but `interruptRead` consumes the head only when it names the site, so a
-- non-delivering entry at the same site moves delivery to the next occurrence.
-- That is how the mid-queue golden interrupts the second job after the first is
-- acknowledged. Occurrences are addressable; the job at an occurrence is not,
-- because a tape entry is a site and a bit and never sees a value. No register
-- row: the tape does what it says it does.
#guard (runInterrupted [] interruptTape interruptITape (Queue.seed [1, 2, 3])).map
    (fun r => r.2.1.any fun event => event == .op "ack" (.pair (.nat 0) (.nat 1))) = some true

/-! ## 5. Axiom report

Expected union: `propext` and `Quot.sound`. Every receipt above is a `#guard`
over an evaluated run; the laws the runs rest on are proved in
`Effect4/Flow/Region.lean` and `Effect4/Flow/Interrupt.lean`.
-/

#print axioms Effect4.Flow.closeFrame_log
#print axioms Effect4.Flow.closeFrame_failure
#print axioms Effect4.Flow.closeFrame_failure_closeResult
#print axioms Effect4.Flow.closeFrame_interrupted_log
#print axioms Effect4.Flow.interruptPoint_masked_defers
#print axioms Effect4.Flow.interruptPoint_unmasked_delivers
#print axioms Effect4.Flow.Point.site_ne_choose
#print axioms Effect4.Flow.Point.site_inj

end Effect4Test.Flow.JobRunnerContract

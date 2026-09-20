import Effect4.Api.Built
import Effect4.Api.Runner
import Effect4.Api.TestClock
import Effect4.Api.Supervision

/-!
# Run — one value a caller holds while a built program runs

`Api.Built` is a program with its table and its certificate. A `Run` is that value opened for
running: the checked session of `Api.HostSession`, the budget every row is played at, and the
rows played so far with the verdict of each.

* **Opening cannot refuse.** `Run.open` takes a `Built`, so the evidence `HostSession.start`
  re-derives is already in hand; the only thing left to choose is the name of the run
  (`Laws/Run.lean`, `open_total`).
* **Everything a caller does is rows.** `Rows.start`, `Rows.flush`, `Rows.clock`,
  `Rows.receive` and `Rows.answer` are functions into `List Api.Runner.Command`. The alphabet
  on the wire does not change, so every law of `Laws/Api/Runner.lean` — a refused row changes
  nothing, a journal splits anywhere, journals are the free monoid on rows — holds of them
  with no new proof.
* **A run records itself.** `play` keeps the rows and the verdicts, so the run is its own
  journal: replaying that journal from a fresh `open` reaches the same run
  (`Laws/Run.lean`, `journal_replays`).
* **The host is a function, and it is not in the journal.** A `Reactor` answers a row's
  request from its own state. `drive` binds, receives and applies every call the session has
  no record of yet, flushes, and repeats. The rows it chose are what was recorded; replay
  plays them and never calls the reactor.

The claims a call and a reply restate are built here from what the machine holds
(`Call.at`), so a caller never writes a fiber number, a guard token or a call id.

This module owns no byte codec and no host: `Observation` is first-order so that a generated
`Canonical` instance can be written for it, and the codec is the generator's.
-/

set_option autoImplicit false

namespace Effect4

open Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Session Header Call Reply Key Answer Phase BoundCall ReplySlot)
open Effect4.Api.Runner (Command)

/-- A built program being run: the session that checks every transition, the budget its rows
are played at, and the rows played so far with the verdict of each.

The name of the run and the machine are read off the session, so they cannot drift from what
the session checks a call against (`Run.id`, `Run.machine`). -/
structure Run where
  /-- The program, its table and its certificate. -/
  built : Api.Built
  /-- The command and compile budgets of this run; every row is played at `budget.fuel`. -/
  budget : Api.Budget := {}
  /-- The checked session: the machine and the ledger of calls, receipts and retirements. -/
  session : Session built.program built.table
  /-- Every row played, in order. -/
  journal : List Command := []
  /-- The verdict of every row played, in order. -/
  phases : List Phase := []

namespace Run

/-! ## Reading a run -/

/-- The name this run was opened under. It is the session's, so a call built for this run is
the call the session accepts. -/
def id (s : Run) : String := s.session.header.session

/-- The profile named in the run's header. -/
def profile (s : Run) : String := s.session.header.profile

/-- The row table the program's host calls are positions in. -/
def table (s : Run) : RowTable := s.built.table

/-- The program being run. -/
def program (s : Run) : Api.Program := s.built.program

/-- The machine the session is holding. -/
def machine (s : Run) : Api.Machine := s.session.machine

/-- The calls the machine is waiting on. -/
def outstanding (s : Run) : List Await := Api.HostSession.outstanding s.session

/-- The frontier reading of the machine: outcome, machine and live reasons. -/
def inspect (s : Run) : Api.Inspection := Api.HostSession.inspect s.session

/-- The root's exit, or `none` while it is still live. -/
def exit (s : Run) : Option ExitV := s.inspect.exit

/-- The row a native operation names, when it is a host row of this run's table. -/
def rowOf (s : Run) : NativeOp → Option Program.Row
  | .external i => externalRow s.built.table i
  | _ => none

/-! ## Opening and playing -/

/-- Open a built program under a name. Nothing here can refuse: the certificate is the
evidence `HostSession.start` re-derives, the header is built from the `Built` rather than
supplied beside it, and the machine is loaded at the budget's compile fuel. -/
def «open» (b : Api.Built) (id : String) (budget : Api.Budget := {})
    (profile : String := "") : Run :=
  { built := b
    budget := budget
    session :=
      { admitted := b.admitted
        header := ⟨Api.HostSession.version, id, profile, b.table⟩
        machine := Api.load b.program budget.compileFuel } }

/-- The run as the runner that plays rows: the program, the table and the job's fuel beside
the session they index. -/
def runner (s : Run) : Api.Runner.Runner :=
  { program := s.built.program, table := s.built.table, fuel := s.budget.fuel,
    session := s.session }

/-- One row played, recorded with its verdict. -/
def step (s : Run) (c : Command) : Run :=
  let r := Api.Runner.step s.runner c
  { s with
    session := r.1.session
    journal := s.journal ++ [c]
    phases := s.phases ++ [r.2] }

/-- Rows played in order, each recorded with its verdict. -/
def play (s : Run) (rows : List Command) : Run := rows.foldl step s

end Run

/-! ## The claims a row carries

`bindCall` refuses a call that does not restate what the machine holds, and that restatement
is the point: a claim arriving from somewhere else is checked against the machine before it
can become an answer. For the local case the claim is not the caller's to invent, so it is
built here from `requestOf` — the same function `bindCall` checks it against. -/

namespace Api.HostSession.Call

/-- The claim a run makes for a call on a row: everything but the row and the request is the
run's own — its name, its table and its next call id. (`Program.requestOf` is spelled in full
because `Api.requestOf` is the nearer name inside this namespace.) -/
def claim (s : Run) (key : Key) (op : NativeOp) (request : Val) : Call :=
  { version := Api.HostSession.version
    session := s.id
    table := s.built.table
    callId := s.session.nextCall
    fiber := key.fiber
    op := op
    request := request }

/-- The call the machine is holding at this key, as the claim a `bind` row carries. `none`
when the machine holds no call at that key. -/
def «at» (s : Run) (key : Key) : Option Call :=
  (Program.requestOf s.machine key.fiber key.token).map fun request =>
    claim s key request.1 request.2

end Api.HostSession.Call

/-! ## Rows

Every convenience is a function into `List Command`. -/

namespace Rows

open Effect4.Api.Runner (Command)

/-- A decision tape as control rows. -/
def tape (decisions : List Api.Decision) : List Command := decisions.map .control

/-- One control decision as a row. -/
def control (d : Api.Decision) : List Command := tape [d]

/-- The row that starts a run: the root evaluated. -/
def start : List Command := control Api.evaluate

/-- The row that drains every armed dispatcher. -/
def flush : List Command := control Api.flush

/-- The row that advances the test clock, `TestClock.adjust` (`Api/TestClock.lean`). -/
def clock (millis : ClockMillis) : List Command := control (Api.TestClock.adjust millis)

/-- The receipt of a completion for this key, as the claim a `submit` row carries. -/
def reply (s : Run) (call : Call) (key : Key) (c : Answer) : Reply :=
  { version := Api.HostSession.version, session := s.id, callId := call.callId,
    key := key, completion := c }

/-- Receive a completion for an outstanding call: the call bound to its guard, then the
completion received against it. Receipt stores; it does not run the machine.

A key the machine holds no call at has nothing to receive, so the rows are empty. -/
def receive (s : Run) (key : Key) (c : Answer) : List Command :=
  match Call.at s key with
  | none => []
  | some call => [.bind call key.token, .submit (reply s call key c)]

/-- Answer an outstanding call: receive the completion, then apply it. -/
def answer (s : Run) (key : Key) (c : Answer) : List Command :=
  match Call.at s key with
  | none => []
  | some call => [.bind call key.token, .submit (reply s call key c), .apply key]

end Rows

namespace Run

/-- Answer an outstanding call and play the rows it takes. -/
def answer (s : Run) (key : Key) (c : Answer) : Run := s.play (Rows.answer s key c)

/-- Receive a completion for an outstanding call, without applying it. -/
def receive (s : Run) (key : Key) (c : Answer) : Run := s.play (Rows.receive s key c)

/-- Play one control decision. -/
def control (s : Run) (d : Api.Decision) : Run := s.play (Rows.control d)

/-! ## What a holder reads -/

/-- What happened, as first-order content: the protocol state a holder schedules by, how the
replay ended, the root's exit, the calls the machine is waiting on, the keys with a receipt
waiting and the keys that were retired, how many completions were applied, and the live
frontier reasons. Nothing here holds a machine, so it is the reading that crosses a
boundary. -/
structure Observation where
  /-- The protocol state: idle, awaiting a host, parked, or terminated. -/
  state : Api.HostProtocol.State
  /-- Finished, a live frontier, or a state the runtime cannot reach. -/
  outcome : Api.Outcome
  /-- The root's exit, or `none` while it is still live. -/
  exit : Option ExitV
  /-- The calls the machine is waiting on. -/
  awaiting : List Await
  /-- The keys holding a receipt that has not been applied. -/
  pending : List Key
  /-- The keys whose call was retired, in retirement order. -/
  retired : List Key
  /-- How many completions were applied. -/
  applied : Nat
  /-- Why the run is still live. -/
  reasons : List Api.FrontierReason
  /-- Every fiber with what holds it (`Api.Supervision`): a tracked child, a daemon at a pin,
  a daemon nobody holds, the root, or an exit — in creation order. -/
  fibers : List (FiberId × Api.FiberStatus)
deriving DecidableEq

/-- The run as content. -/
def observe (s : Run) : Observation :=
  let read := s.inspect
  { state := Api.HostProtocol.observe s.machine
    outcome := read.outcome
    exit := read.exit
    awaiting := s.outstanding
    pending := (Api.HostSession.pendingReplies s.session).map Reply.key
    retired := s.session.retired.map (·.bound.key)
    applied := s.session.applied
    reasons := read.reasons
    fibers := Api.fiberStatuses s.machine }

/-- The live fibers nobody holds: a function of `fibers`, never a second field. -/
def Observation.daemons (o : Observation) : List FiberId :=
  o.fibers.filterMap fun entry => if entry.2 = Api.FiberStatus.daemon then some entry.1 else none

/-- No unpinned daemon is alive (`Api.daemonsQuiet` of the machine the observation read). -/
def Observation.daemonsQuiet (o : Observation) : Bool := o.daemons.isEmpty

/-! ## The host as a function

The executable half of a host specification: the row, the request it was called with, and
the host's own state in; the completion and the next state out, or `none` for a request this
host does not answer. It is the shape `Profile.Scalar.step?` already has. -/

/-- A host as a pure function of the row, the request and its own state. -/
abbrev Reactor (σ : Type) := Program.Row → Val → σ → Option (Answer × σ)

/-- The first call the machine is waiting on that this session has no record of: not bound,
and with no slot waiting for a completion. A call already recorded is the driver's to finish
by key, not to answer again. -/
def freshCall (s : Run) : Option Await :=
  s.outstanding.find? fun await =>
    !(s.session.active.any fun bound => bound.key == ⟨await.1, await.2.1⟩) &&
      !(s.session.pending.any fun slot => slot.key == ⟨await.1, await.2.1⟩)

/-- Answer every call the session has no record of, flush, and repeat, keeping the rows.

One round is either an answer — the first fresh call bound, received and applied — or a
flush. The drive stops when a flush reveals no call to answer, when the reactor declines a
request, when the only calls outstanding are ones the session already recorded, or when the
rounds run out. This is the driver loop every host lane writes by hand
(`harness/truth/session/Keyed.lean`, `planRun`). -/
def driveFrom {σ : Type} (r : Reactor σ) : Nat → Run → σ → Run × List Command × σ
  | 0, s, st => (s, [], st)
  | rounds + 1, s, st =>
    match freshCall s with
    | some await =>
      match s.rowOf await.2.2.1 with
      | none => (s, [], st)
      | some row =>
        match r row await.2.2.2 st with
        | none => (s, [], st)
        | some (c, next) =>
          let rows := Rows.answer s ⟨await.1, await.2.1⟩ c
          let after := driveFrom r rounds (s.play rows) next
          (after.1, rows ++ after.2.1, after.2.2)
    | none =>
      if !s.outstanding.isEmpty then (s, [], st)
      else
        let rows := Rows.flush
        let played := s.play rows
        if played.outstanding.isEmpty then (played, rows, st)
        else
          let after := driveFrom r rounds played st
          (after.1, rows ++ after.2.1, after.2.2)

/-- Drive the run with a host: the run it reaches and the host's state at the end. -/
def drive {σ : Type} (s : Run) (r : Reactor σ) (st : σ) (rounds : Nat := 64) : Run × σ :=
  let after := driveFrom r rounds s st
  (after.1, after.2.2)

end Run

namespace Rows

/-- The rows a host chose, and its state at the end: what `Run.drive` played. Replay plays
these rows and calls no host. -/
def answerAll {σ : Type} (s : Run) (r : Run.Reactor σ) (st : σ) (rounds : Nat := 64) :
    List Command × σ :=
  let after := Run.driveFrom r rounds s st
  (after.2.1, after.2.2)

end Rows

namespace Run

/-! ## Three named runs -/

/-- The ordinary run: the root evaluated, then the dispatcher flushed. The journal
`Api.run` would have played, with the session checking every row. -/
def runPure (b : Api.Built) (id : String := "run") (budget : Api.Budget := {}) : Run :=
  (Run.open b id budget).play (Rows.tape [Api.evaluate, Api.flush])

/-- The run under the test clock: the root evaluated, the clock adjusted in order, the
dispatcher flushed (`Api/TestClock.lean`, `tape`). -/
def runClock (b : Api.Built) (adjusts : List ClockMillis) (id : String := "run")
    (budget : Api.Budget := {}) : Run :=
  (Run.open b id budget).play (Rows.tape (Api.TestClock.tape adjusts))

/-- The run under a host: the root evaluated, then every call the host answers, flushing
between rounds. -/
def runWith {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ) (id : String := "run")
    (budget : Api.Budget := {}) (rounds : Nat := 64) : Run × σ :=
  ((Run.open b id budget).play Rows.start).drive r st rounds

end Run

end Effect4

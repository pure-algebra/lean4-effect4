import Lean.Data.Json
import Tools.ProfileJson
import Effect4.Api.HostSession
import Effect4.Program.Profile
import Effect4.Laws.Program.Validated
import Tools.RunRecord

/-!
# Tools.RunChecks — a recorded run's wire, and Lean's checks of the run

Two lanes hand Lean a run that a host recorded. Lean decides on it the premises of the to-do's
claims (the lowering note's §6.1, `docs/research/2026-10-13-lowering-vertical-slice/README.md`).

* The keyed lane replays each scripted run of the to-do's emitted service from its records
  (`git:38b94bdec:harness/truth/session/Keyed.lean`, the subcommand `service-checks`; decisions row 378 (20)).
* The to-do application records each request that it serves (`git:38b94bdec:apps/todo/`, decisions row 378
  (16), slice V4). `git:38b94bdec:apps/todo/Check.lean` rebuilds each request's program and decides its checks.

This module holds what both read. It is tooling over the law graph: it states no theorem.

* **The wire.** Values, host answers and exits as JSON, in the images of the keyed recorder
  (`git:38b94bdec:harness/truth/session/keyed-recorder.ts`: `valueJson`, `exitJson`). These definitions came
  here from `Keyed.lean` with their bodies unchanged.
* **The decisions on one run** (`decided`): funded, at rest, driven by a host, and conforming to
  the declared protocols.
* **The model threaded** (`threaded`): the reference model's state after each run of a sequence,
  as `Effect4.Run.agrees` decides it, each run starting where the model left the one before.
* **A recorded request** (`Record`): the entry, its arguments, each host call with its row, its
  request and the host's completion, and the root's exit. `recorded` answers each call from the
  record, so `Run.runWith` rebuilds the request's run with no host (`runOf`). `checkSession`
  decides the five checks of each request of a session.

Placement (AGENTS.md, Trust): each decision is graded `validated` in the claim record
(`git:451b05e15:Test/Dogfood/Application.lean`, retired by row 410). Its consumers are `Effect4.Run.conforms_sat` and
`Effect4.Run.agrees_hostRun` (`src/Effect4/Laws/Program/Validated.lean`). What a decision does not
establish: anything of a run that no check read; the host's behaviour beyond the recorded
completions; concurrency between requests.
-/

set_option autoImplicit false

namespace Tools.RunChecks

open Lean Effect4 Effect4.Machine Effect4.Program Effect4.Api.HostSession

abbrev J := Lean.Json

/-! ## The wire -/

def keys (j : J) (wanted : List String) : Except String Unit := do
  let actual := (← j.getObj?).toList.map Prod.fst
  unless actual.length = wanted.length && actual.all (wanted.contains ·) do throw "missing or extra fields"
def field := Json.getObjVal?
def text (j : J) : Except String String := do
  let s ← j.getStr?
  if s.length ≤ 4096 then return s else throw "text bound"
def nat (j : J) : Except String Nat := do
  let n ← j.getNat?
  if n ≤ rc112.natBound then return n else throw "unsafe natural"
def strField (j : J) (k : String) := field j k >>= text
def natField (j : J) (k : String) := field j k >>= nat

def decodeVal : Nat → J → Except String Val
  | 0, _ => .error "value depth"
  | fuel + 1, j => do
    match j with
    | .null => return .unit
    | .bool b => return .bool b
    | .num _ => return .nat (← nat j)
    | .str _ => return .str (← text j)
    | .arr vs => return .list (← vs.toList.mapM (decodeVal fuel))
    | .obj _ =>
      if (field j "none").isOk then
        keys j ["none"]
        unless (← field j "none") == .bool true do throw "invalid none"
        return .none
      else if (field j "some").isOk then
        keys j ["some"]
        return .some (← decodeVal fuel (← field j "some"))
      else if (field j "ctor").isOk then
        keys j ["ctor", "args"]
        return .ctor (← natField j "ctor") (← (← (← field j "args").getArr?).toList.mapM (decodeVal fuel))
      else
        keys j ["handle"]
        return Value.external (← natField j "handle")

mutual
  def valJson : Val → J
    | .unit => .null | .nat n => toJson n | .bool b => toJson b | .str s => .str s
    | .none => Json.mkObj [("none", .bool true)]
    | .some v => Json.mkObj [("some", valJson v)]
    | .list vs => .arr (valsJson vs).toArray
    | .ctor n vs => Json.mkObj [("ctor", toJson n), ("args", .arr (valsJson vs).toArray)]
    | .handle _ n => Json.mkObj [("handle", toJson n)]
    | _ => Json.mkObj [("unsupported", .bool true)]
  def valsJson : List Val → List J
    | [] => [] | v :: vs => valJson v :: valsJson vs
end

def reasonJson : Reason Err Defect FiberId Ann → J
  | .fail (.tagged tag msg) _ => Json.mkObj [("fail", toJson [tag, msg])]
  | .fail (.text msg) _ => Json.mkObj [("fail", toJson msg)]
  | .fail (.tag n) _ => Json.mkObj [("fail", toJson n)]
  -- a record payload (decisions row 120): its frame through the structural value wire
  | .fail (.payload p) _ => Json.mkObj [("fail", valJson p.val)]
  | .die (.user n) _ => Json.mkObj [("die", toJson n)]
  | .die (.error (.text msg)) _ => Json.mkObj [("die", toJson msg)]
  | .interrupt fiber _ => Json.mkObj [("interrupt", toJson (fiber.map FiberId.value))]
  | _ => Json.mkObj [("unsupported", .bool true)]

def exitJson : ExitV → J
  | .success v => Json.mkObj [("success", valJson v)]
  | .failure cause => Json.mkObj [("failure", toJson (cause.reasons.map reasonJson))]

def decodeReason (j : J) : Except String (Reason Err Defect FiberId Ann) := do
  if (field j "fail").isOk then
    keys j ["fail"]
    match ← decodeVal 32 (← field j "fail") with
    | .str s => return .fail (.text s) .empty
    | .nat n => return .fail (.tag n) .empty
    | .list [.str a, .str b] => return .fail (.tagged a b) .empty
    | v =>
      match Effect4.Machine.Payload.image.ofVal v with
      | some p => return .fail (.payload p) .empty
      | none => throw "unsupported error shape"
  else if (field j "die").isOk then
    keys j ["die"]
    match ← decodeVal 32 (← field j "die") with
    | .str s => return .die (.error (.text s)) .empty
    | .nat n => return .die (.user n) .empty
    | _ => throw "unsupported defect shape"
  else
    keys j ["interrupt"]
    let f ← field j "interrupt"
    let who ← if f == .null then pure none else do pure (some ⟨← nat f⟩)
    return .interrupt who .empty

def decodeAnswer (j : J) : Except String Answer := do
  if (field j "success").isOk then
    keys j ["success"]
    return .ofExit (.success (← decodeVal 64 (← field j "success")))
  else
    keys j ["failure"]
    return .ofExit (.failure ⟨← (← (← field j "failure").getArr?).toList.mapM decodeReason⟩)

def answerJson (answer : Answer) : J := match answer with
  | .ofExit exit => exitJson exit
  | _ => Json.mkObj [("unsupported", .bool true)]

/-! ## The decisions on one run -/

/-- The decisions of the lowering note's §6.1, steps 4 and 5, on one run: the three premises of
the host's meaning (`denoteRows_eq_session_host`), and conformance to the declared protocols. -/
structure Decided where
  /-- No row of the run was cut by its budget (`Effect4.Run.funded`). -/
  funded : Bool
  /-- No fiber is runnable and no dispatcher is armed (`Effect4.Run.atRest`). -/
  atRest : Bool
  /-- Each decision of the run's tape is a host's (`Effect4.Run.hostDriven`). -/
  hostDriven : Bool
  /-- Each held call meets its row's demand, and each applied answer keeps its row's promise
  (`Effect4.Run.conforms`). -/
  conforming : Bool
deriving DecidableEq, Repr

/-- The decisions on one run, under the application's declared protocols. -/
def decided (protocols : RowProtocols) (s : Run) : Decided :=
  { funded := Effect4.Run.funded s, atRest := Effect4.Run.atRest s,
    hostDriven := Effect4.Run.hostDriven s, conforming := Effect4.Run.conforms protocols s }

/-- The three premises of the host's meaning hold: the run is funded, at rest and driven by a
host. -/
def Decided.settled (d : Decided) : Bool := d.funded && d.atRest && d.hostDriven

/-- **The reference model's state threaded along a sequence of runs** (the lowering note's §6.1,
step 5): the model's state after each run, each run starting where the model left the one before.
An entry is `none` where the model does not give that run's answers (`Effect4.Run.agrees`), and
every entry after it is `none` too. A run that is `none` breaks the thread in the same way. -/
def threaded {σ : Type} (model : Run.Reactor σ) (start : σ) (runs : List (Option Run)) :
    List (Option σ) :=
  (runs.scanl (fun state run => state.bind fun st => run.bind fun s => Effect4.Run.agrees model s st)
    (some start)).tail

/-! ## A recorded request -/

-- One host call of a recorded request is `Call`, beside `literal` (`tools/Tools/RunRecord.lean`).

/-- **The record of one request** (the lowering note's §6.1): the entry, its arguments, each host
call in the order that the face made them, and the root's exit. -/
structure Record where
  entry : String
  args : List Val
  calls : List Call
  exit : ExitV

def decodeCall (j : J) : Except String Call := do
  keys j ["row", "request", "completion"]
  return ⟨← natField j "row", ← decodeVal 64 (← field j "request"),
    ← decodeAnswer (← field j "completion")⟩

def decodeRecord (j : J) : Except String Record := do
  keys j ["entry", "args", "calls", "exit"]
  let exit ← match ← decodeAnswer (← field j "exit") with
    | .ofExit exit => pure exit
    | _ => throw "an exit outside the wire"
  return ⟨← strField j "entry", ← (← (← field j "args").getArr?).toList.mapM (decodeVal 64),
    ← (← (← field j "calls").getArr?).toList.mapM decodeCall, exit⟩

/-- The format of a session's file: a header line, then one record a line. -/
def sessionFormat : String := "effect4-app-session-v1"

/-- A session's header: the application's name, the session's name, the row table on the wire
(`Tools.ProfileJson.tableJson`), the model's start state as the face read it, and the versions of
the face's runtime. Lean reads the versions nowhere. -/
structure Header where
  application : String
  session : String
  table : J
  start : J

def decodeHeader (j : J) : Except String Header := do
  keys j ["format", "application", "session", "table", "start", "versions"]
  unless (← strField j "format") = sessionFormat do throw s!"the format {sessionFormat} is required"
  return ⟨← strField j "application", ← strField j "session", ← field j "table", ← field j "start"⟩

/-- A session's lines: the header, then each record. An empty line is skipped. -/
def decodeSession (lines : List String) : Except String (Header × List Record) := do
  let header :: records := (lines.filter (· != "")).map Json.parse
    | throw "a session with no header"
  return (← decodeHeader (← header), ← records.mapM fun record => do decodeRecord (← record))

/-- **A host that answers from a record** (the lowering note's §6.1, step 2). At each call it
gives the record's next completion, where the record's row is the machine's row and its request
the machine's request. It answers nothing otherwise, so the drive stops at the first call that the
record does not hold. -/
def recorded (table : RowTable) : Run.Reactor (List Call) := fun row request calls =>
  match calls with
  | call :: rest =>
    if externalRow table call.row = some row ∧ call.request = request then some (call.completion, rest)
    else none
  | [] => none

/-- **Lean's run of a recorded request** (the lowering note's §6.1, steps 1 and 2): the entry built
at the record's arguments (`build`), driven by the host that answers from the record. Beside the
run stand the calls that the host did not answer. `none` where the entry does not build. -/
def runOf (build : String → List Val → Option Api.Built) (id : String) (record : Record) :
    Option (Run × List Call) :=
  (build record.entry record.args).map fun b => Run.runWith b (recorded b.table) record.calls id

/-- The verdict of one recorded request: the five checks of the lowering note's §6.1. -/
structure Verdict where
  /-- Step 1: the entry builds at the arguments. -/
  built : Bool
  /-- Step 2: the host answered every call of Lean's run from the record, in order, and the
  record holds no call more. -/
  replayed : Bool
  /-- Step 3: the root's exit of Lean's run is the face's exit. -/
  exit : Bool
  /-- Steps 4 and 5: the decisions on Lean's run. -/
  decided : Decided
  /-- Step 5: the reference model gives the run's answers, from the state where the session's
  run before it left the model. -/
  agrees : Bool

/-- Every check of a request passes. -/
def Verdict.passed (v : Verdict) : Bool :=
  v.built && v.replayed && v.exit && v.decided.settled && v.decided.conforming && v.agrees

def Verdict.json (v : Verdict) : J :=
  Json.mkObj [("built", toJson v.built), ("replayed", toJson v.replayed), ("exit", toJson v.exit),
    ("funded", toJson v.decided.funded), ("atRest", toJson v.decided.atRest),
    ("hostDriven", toJson v.decided.hostDriven), ("conforming", toJson v.decided.conforming),
    ("agrees", toJson v.agrees), ("passed", toJson v.passed)]

/-- **The checks of a session's requests**, in the session's order. Each request's run is Lean's
run of its record (`runOf`). The reference model is threaded across the requests from `start`
(`threaded`). A request that does not build fails every check. -/
def checkSession {σ : Type} (build : String → List Val → Option Api.Built) (id : String)
    (protocols : RowProtocols) (model : Run.Reactor σ) (start : σ) (records : List Record) :
    List Verdict :=
  let runs := records.map (runOf build id)
  let states := threaded model start (runs.map (·.map (·.1)))
  (records.zip (runs.zip states)).map fun (record, run, state) =>
    match run with
    | none =>
      { built := false, replayed := false, exit := false, decided := ⟨false, false, false, false⟩,
        agrees := false }
    | some (s, rest) =>
      { built := true, replayed := rest.isEmpty && s.outstanding.isEmpty,
        exit := s.exit == some record.exit, decided := decided protocols s,
        agrees := state.isSome }

end Tools.RunChecks

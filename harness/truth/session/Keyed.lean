import Effect4.Api.HostSession
import Effect4.Program.Profile
import Effect4.Program.Stream
import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.Routing
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Timeout
import Tools.ProfileJson
import TypeScript.Render
import Lean.Data.Json

/-! Strict v3 decision-tape tool. The runtime session is the semantic owner; this is
only fixture construction, JSON transport, and rendering of the same admitted Eff program.
No legacy tape inference, oracle answer queue, or implicit pending-reply scheduler.

The last section holds the scenarios' host runs (decisions row 254): one fixture for each script
of a battery of `Test/Dogfood/Scenario/` that a host can perform, and Lean's replay of each
recording that the host writes. -/
open Lean Effect4 Effect4.Machine Effect4.Program Effect4.Api.HostSession
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace KeyedTool
abbrev J := Lean.Json

def pair (a b : Effect4.Program.Term) : Effect4.Program.Term := .app "pair" (.cons a (.cons b .nil))
def opts : Supervision.ForkOptions := { daemon := false, startImmediately := true, maskMode := .inherit }
def forkPair (left right : Api.Program) (env : Nat) : Api.Program :=
  .bind (.withFiber (.fork left opts))
    (.bind (.withFiber (.fork (right.weaken env) opts))
      (.bind (.awaitFiber (.var env) .awaitValue)
        (.bind (.awaitFiber (.var (env + 1)) .awaitValue)
          (.succeed (pair (.var (env + 2)) (.var (env + 3)))))))
def two : Api.Program := forkPair (.perform (.external 0) (.lit (.nat 2)))
  (.perform (.external 0) (.lit (.nat 3))) 0

def sharedChild (value : Nat) : Api.Program :=
  .bind (.perform (.external 0) (.lit (.nat value)))
    (.perform .refSet (pair (.var 0) (.lit (.nat value))))
def shared : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (forkPair (sharedChild 1) (sharedChild 2) 1) (.perform .refGet (.var 0)))

def kv : Api.Program :=
  .bind (.perform (.external 0) (.lit .unit))
    (.bind (.perform (.external 2) (pair (.var 0) (pair (.lit (.str "a")) (.lit (.str "A")))))
      (.bind (.perform (.external 2) (pair (.var 0) (pair (.lit (.str "b")) (.lit (.str "B")))))
        (forkPair (.perform (.external 1) (pair (.var 0) (.lit (.str "a"))))
          (.perform (.external 1) (pair (.var 0) (.lit (.str "b")))) 3)))

def streamTarget : String := "Host.Stream"
def streamTable : RowTable := Stream.table streamTarget .nat (.prod .string .string)
def concurrentStreams : Api.Program := forkPair (Stream.scopedPulls 0 3) (Stream.scopedPulls 1 3) 0

def scalarTable : RowTable := [Profile.Scalar.waitRow]
structure Fixture where
  name : String
  program : Api.Program
  table : RowTable
  source : J := .null

def fixture (name : String) : Except String Fixture := do
  if name = "two" then return ⟨name, two, scalarTable, .null⟩
  if name = "shared" then return ⟨name, shared, scalarTable, .null⟩
  if name = "kv" then return ⟨name, kv, Packages.keyValueStoreMemory, .null⟩
  if name = "concurrentStreams" then return ⟨name, concurrentStreams, streamTable, .null⟩
  if name.startsWith "stream-" then
    let some n := (name.drop 7).toString.toNat? | throw "bad stream fixture"
    if n ≥ 48 then throw "unknown stream fixture"
    return ⟨name, Stream.scopedPulls 0 (n % 4), streamTable,
      Json.mkObj [("variant", toJson (n / 4)), ("pulls", toJson (n % 4))]⟩
  throw "unknown fixture"

def tableJson (table : RowTable) : J := toJson (table.map Tools.ProfileJson.rowJson)
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
def clockField (j : J) (k : String) : Except String ClockMillis := do
  let text ← (← field j k).getStr?
  match ClockMillis.ofDecimal text with
  | some millis => pure millis
  | none => throw "clock milliseconds require canonical decimal text"

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

def keyOf (j : J) : Except String Key := return ⟨⟨← natField j "fiber"⟩, ← natField j "token"⟩

/-- Record shape is projected from HostProtocol, including required keys and scalar types. -/
def checkRecord (j : J) (session : String) : Except String String := do
  let kind ← strField j "kind"
  let some shape := Api.HostProtocol.hostProtocol.records.find? (fun s => s.kind == kind)
    | throw "unknown record kind"
  keys j (["kind", "version", "session"] ++ shape.fields.map Prod.fst)
  unless (← natField j "version") = version do throw "unknown version"
  unless (← strField j "session") = session do throw "session mismatch"
  for (name, type) in shape.fields do
    match type with
    | .natural => discard (natField j name)
    | .clockMillis => discard (clockField j name)
    | .boolean => discard ((← field j name).getBool?)
    | .text => discard (strField j name)
    | .json => pure ()
  return kind

/-- A checked record as a row of the session's journal (`Api.Runner.Command`). It is the one
reading of a record: `consume` plays the row on a session, and a scenario's replay plays it on a
run. -/
def command (session : String) (rows : RowTable) (j : J) : Except String Api.Runner.Command := do
  match ← checkRecord j session with
  | "call" =>
    let key ← keyOf j
    return .bind ⟨version, session, rows, ← natField j "callId", key.fiber,
      .external (← natField j "row"), ← decodeVal 64 (← field j "request")⟩ key.token
  | "reply" =>
    let key ← keyOf j
    let answer ← decodeAnswer (← field j "completion")
    return .submit ⟨version, session, ← natField j "callId", key, answer⟩
  | "apply" => return .apply (← keyOf j)
  | "advanceClock" => return .control (.advance (← clockField j "millis"))
  | "cancel" => return .control (.interruptFrom none .empty ⟨← natField j "fiber"⟩)
  | "evaluate" => return .control (.evaluate ⟨← natField j "fiber"⟩)
  | "fire" => return .control (.fire ⟨← natField j "fiber"⟩)
  | "flush" => return .control .flush
  | "yieldVerdict" =>
    return .control (.yieldVerdict ⟨← natField j "fiber"⟩ (← (← field j "verdict").getBool?))
  | "installMiddleware" => return .control .installMiddleware
  | _ => throw "unimplemented protocol record"

def consume {p : Api.Program} {rows : RowTable} (s : Session p rows) (fuel : Nat)
    (j : J) : Except String (Effect4.Api.HostSession.Result p rows) := do
  let row ← command s.header.session rows j
  -- Nonempty Some is the stream binding refinement, checked before ordinary Envelope.
  if rows = streamTable then
    match row with
    | .submit reply =>
      match requestOf s.machine reply.key.fiber reply.key.token, reply.completion with
      | some (.external 1, _), .ofExit (.success value) =>
        if (Stream.chunk? value).isNone then throw "empty or malformed stream chunk"
      | _, _ => pure ()
    | _ => pure ()
  return Api.Runner.result ⟨p, rows, fuel, s⟩ row

structure Walk (p : Api.Program) (rows : RowTable) where
  session : Session p rows
  position : Nat := 0
  status : String := "prefix-end"

def walk {p : Api.Program} {rows : RowTable} (s : Session p rows) (fuel : Nat)
    (pos : Nat) : List J → Walk p rows
  | [] => ⟨s, pos, "prefix-end"⟩
  | record :: rest =>
    match consume s (if (strField record "kind") = .ok "apply" then fuel else 1000) record with
    | .error why => ⟨s, pos, "refused: " ++ why⟩
    | .ok result => match result.phase with
      | .refused why => ⟨s, pos, "refused: " ++ reprStr why⟩
      | .frontier => ⟨result.session, pos, "frontier"⟩
      | _ => walk result.session fuel (pos + 1) rest

def awaitJson (entry : Await) : J :=
  let ⟨fiber, token, op, request⟩ := entry
  Json.mkObj [("fiber", toJson fiber.value), ("token", toJson token),
    ("row", match op with | .external n => toJson n | _ => .null), ("request", valJson request)]

def receipt {p : Api.Program} {rows : RowTable} (w : Walk p rows) : J :=
  let s := w.session
  Json.mkObj [("status", .str w.status), ("position", toJson w.position),
    ("exit", ((inspect s).exit.map exitJson).getD .null),
    ("phase", .str (reprStr (Api.HostProtocol.observe s.machine))),
    ("awaits", toJson ((outstanding s).map awaitJson)),
    ("consumed", toJson s.consumed), ("pending", toJson ((pendingReplies s).map Reply.callId)),
    ("retired", toJson (s.retired.map (fun r => r.bound.call.callId))),
    ("allocated", toJson s.machine.state.externals.allocated),
    ("oracleAnswers", toJson s.machine.state.externals.answers.length)]

def replay (j : J) (fuel : Nat := 1000) : Except String J := do
  keys j ["header", "records"]
  let h ← field j "header"
  keys h ["format", "version", "session", "profile", "program", "table"]
  unless (← strField h "format") = "effect4-host-session-v3" && (← natField h "version") = version do
    throw "version 3 required; version 2 and older inputs need explicit migration"
  unless (← strField h "profile") = "keyed-v3" do throw "profile mismatch"
  let f ← fixture (← strField h "program")
  unless (← field h "table") == tableJson f.table do throw "full table mismatch"
  let header : Header := ⟨version, ← strField h "session", "keyed-v3", f.table⟩
  let s ← (start f.program f.table "keyed-v3" header 1000).mapError reprStr
  let records := (← (← field j "records").getArr?).toList
  return receipt (walk s fuel 0 records)

/-- Independent finite stream model for the golden source configurations. Host runs use
actual rc.112 Stream/Channel/Scope, then their actual tapes are replayed through Session. -/
def chunks (variant source : Nat) : List (List Nat) :=
  let offset := source * 10
  let base := match variant with
    | 0 => [[1, 2, 3]] | 1 => [[1], [2, 3]] | 2 => []
    | 3 => [[1, 2], [3, 4]] | 4 => [[2, 3, 4]]
    | 5 | 6 => [[1]] | 7 => [[1, 2, 3]] | 8 => [[1], [2]]
    | 9 => [] | 10 => [[0], [1], [2]] | _ => [[1, 2], [3]]
  base.map (fun chunk => chunk.map (· + offset))

structure ModelState where
  sources : List Nat := []
  cursors : List Nat := []

def modelReply (f : Fixture) (s : ModelState) (bound : BoundCall) : Except String (Answer × ModelState) := do
  let ok (v : Val) := (.ofExit (.success v), s)
  if f.table = scalarTable then return ok bound.call.request
  if f.table = Packages.keyValueStoreMemory then
    match bound.call.op, bound.call.request with
    | .external 0, _ => return ok (.nat 0)
    | .external 2, _ => return ok .unit
    | .external 1, .list [_, .str key] => return ok (.some (.str (if key = "a" then "A" else "B")))
    | _, _ => throw "unexpected key-value model request"
  let variant := if f.name = "concurrentStreams" then 1 else ((f.name.drop 7).toString.toNat?).getD 0 / 4
  match bound.call.op, bound.call.request with
  | .external 0, .nat source =>
    return (.ofExit (.success (.nat s.sources.length)),
      ⟨s.sources ++ [source], s.cursors ++ [0]⟩)
  | .external 1, Value.external index =>
    let cursor := (s.cursors[index]?).getD 0
    let next := { s with cursors := s.cursors.set index (cursor + 1) }
    if variant = 5 && cursor ≥ 1 then
      return (.ofExit (.failure (Cause.fail (.tagged "Stream" "selected failure"))), next)
    if variant = 6 && cursor ≥ 1 then
      return (.ofExit (.failure (Cause.die (.error (.text "stream defect")))), next)
    let values := chunks variant ((s.sources[index]?).getD 0)
    return (.ofExit (.success (match values[cursor]? with
      | none => .none | some vs => .some (.list (vs.map Val.nat)))), next)
  | .external 2, _ =>
    if variant = 7 || variant = 9 then return (.ofExit (.failure (Cause.die (.error (.text "close defect")))), s)
    return ok .unit
  | _, _ => throw "unexpected stream model request"

def answerJson (answer : Answer) : J := match answer with
  | .ofExit exit => exitJson exit
  | _ => Json.mkObj [("unsupported", .bool true)]

def planRun (f : Fixture) (s : Session f.program f.table) (model : ModelState) :
    Nat → Except String (List J × J)
  | 0 => .error "fixture plan exhausted fuel"
  | fuel + 1 => do
    let mut current := s
    let mut calls := []
    for ⟨fiber, token, op, request⟩ in outstanding s do
      let key : Key := ⟨fiber, token⟩
      unless current.active.any (fun b => b.key == key) do
        let call : Call := ⟨version, current.header.session, f.table, current.nextCall, fiber, op, request⟩
        let bound := bindCall current call token
        unless bound.phase = .bound do throw "fixture binding refused"
        calls := calls ++ [Json.mkObj [("callId", toJson call.callId), ("fiber", toJson fiber.value),
          ("token", toJson token), ("row", match op with | .external n => toJson n | _ => .null),
          ("request", valJson request)]]
        current := bound.session
    match current.active with
    | [] =>
      if (inspect current).exit.isSome then return (calls, ((inspect current).exit.map exitJson).getD .null)
      let step := advance current 1000 .flush
      let (rest, exit) ← planRun f step.session model fuel
      return (calls ++ rest, exit)
    | bound :: _ =>
      let (answer, nextModel) ← modelReply f model bound
      let reply : Reply := ⟨version, current.header.session, bound.call.callId, bound.key, answer⟩
      let submitted := submit current reply
      unless submitted.phase = .preflight do throw ("fixture receipt refused: " ++ reprStr submitted.phase)
      let applied := applyReply submitted.session bound.key 1000
      unless applied.phase = .applied do throw "fixture application refused"
      let (rest, exit) ← planRun f applied.session nextModel fuel
      return (calls ++ [Json.mkObj [("answerFor", toJson bound.call.callId), ("completion", answerJson answer)]] ++ rest, exit)

def plan (f : Fixture) : Except String (List J × J) := do
  let header : Header := ⟨version, "plan", "keyed-v3", f.table⟩
  let s ← (start f.program f.table "keyed-v3" header 1000).mapError reprStr
  let s := (advance s 1000 Api.evaluate).session
  planRun f s {} 100

def emitFixture (name : String) : Except String J := do
  let f ← fixture name
  discard <| (Api.admitProgram f.program ⟨f.table, []⟩).mapError (fun _ => "program admission refused: " ++ name)
  let expr ← (Api.print f.program f.table).mapError (fun _ => "print refused: " ++ name)
  let (schedule, expected) ← plan f
  return Json.mkObj [("name", .str name), ("table", tableJson f.table),
    ("plan", toJson schedule), ("expected", expected),
    ("source", f.source), ("expression", .str (TypeScript.Render.expr TypeScript.house0 0 expr))]

/-! ## The scenarios' host runs (decisions row 254)

A scenario of `Test/Dogfood/Scenario/` runs on this lane as its printed module. One host run is
one script of a battery on one program that the battery builds. The lane writes one fixture for
each run that a host can perform, and it names each run that a host cannot perform, with the
reason.

* **The script.** The battery's own `List Move`, played by the battery's own driver. The lane
  takes it from the battery's record, where each script stands once as a named run: this file
  holds no script. The fixture holds the journal rows that the script leaves, as records of this
  lane's wire. The host acts out each row, and it writes each record from what it did.
* **The calls.** Every call that the machine waits on during the script, in the order of the
  guard tokens: the order in which the fibers parked. The recorder gives the n-th call that the
  module starts the n-th key.
* **The observation.** The battery's own `observe` of the scripted run, one JSON value a field.
* **The readers.** The notes inside the program's state that the run may use on the host, each
  with its premise checked here (`readersOf`).
* **The replay.** `Run.play` over the rows of the host's recording, from the run that the battery
  opens. It reads the battery's `observe`, and it compares by the battery's own equality. It
  also gives the session's verdict of each row, which the recorder's ledger predicted.

Each host run is a finite host run of one script. It proves nothing. -/
namespace Scenarios
open Test.Dogfood

abbrev Row := Api.Runner.Command

/-- A reader inside the program's state (the coordinator's ruling of 2026-10-06, the seat's
receipt). Each is a note that the lane adds on the host, and it changes nothing that the module
does: the lane's check compares the recording with a reader and the recording without one.

* `cells`: the value of each cell that the module makes, by allocation index.
* `fibers`: each fiber that the module forks, in fork order, with its exit.
* `sleeps`: each pending sleep of the clock boundary, with its fiber and its wake time.
* `dispatchers`: whether a dispatcher of the run is armed, as a count. -/
inductive Reader
  | cells | fibers | sleeps | dispatchers
deriving DecidableEq

def Reader.word : Reader → String
  | .cells => "cells" | .fibers => "fibers" | .sleeps => "sleeps" | .dispatchers => "dispatchers"

/-- One host run of a scenario: a script of a battery on a program that the battery opened. -/
structure HostRun where
  /-- The run's name: the scenario, a slash, and the script's name. -/
  name : String
  /-- The scenario's name, as its row of `Test/Dogfood/README.md` quotes it. -/
  scenario : String
  /-- The built program, opened as the battery opens it. -/
  opened : Run
  /-- The battery's script. -/
  moves : List Scenario.Move
  /-- The battery's observation of a run, one JSON value a field, in the order of its fields. -/
  observed : Run → List (String × J)
  /-- Whether two runs show one observation, by the battery's own equality. -/
  same : Run → Run → Bool
  /-- A reason that keeps the run out of the lane and that no rule of `performable` measures:
  a finding of the target type check, stated with its evidence. -/
  out : Option String := none
  /-- The readers inside the program's state that the scenario's observation asks for. A
  reader is off unless a run asks for it and its premise holds on that run (`readersOf`). -/
  asks : List Reader := []

/-! ### The observation's wire -/

def keyJson (key : Key) : J :=
  Json.mkObj [("fiber", toJson key.fiber.value), ("token", toJson key.token)]

/-- A call as the host sees it: the row's spelling, the request and the key. -/
def seenJson (seen : Scenario.Seen) : J :=
  Json.mkObj [("row", .str seen.row), ("request", valJson seen.request),
    ("fiber", toJson seen.key.fiber.value), ("token", toJson seen.key.token)]

def exitOrNull (exit : Option ExitV) : J := (exit.map exitJson).getD .null

/-- The session's reason for a refusal, as one word. -/
def refusalWord : Effect4.Api.HostSession.Refusal → String
  | .version => "version" | .session => "session" | .profile => "profile" | .table => "table"
  | .program _ => "program" | .duplicateCall => "duplicateCall" | .protocol => "protocol"
  | .selectionRequired => "selectionRequired" | .pendingReply => "pendingReply"
  | .callOrder => "callOrder" | .noCall => "noCall" | .staleCall => "staleCall"
  | .envelope => "envelope" | .directAnswer => "directAnswer"
  | .pendingControl => "pendingControl" | .stuck => "stuck"

/-- The session's verdict of a row: a word, or the refusal with its reason. The check compares
it with what the recorder's ledger predicted for the same record. -/
def verdictJson : Phase → J
  | .bound => "bound" | .preflight => "preflight" | .applied => "applied"
  | .progressed => "progressed" | .frontier => "frontier"
  | .refused why => Json.mkObj [("refused", .str (refusalWord why))]

/-! ### A script as the host's acts -/

/-- A journal row as a record of the lane's wire, without its version and session: the act that
the host performs. `none` for a row that the wire does not carry. It is the inverse of
`command`. -/
def rowJson : Row → Option J
  | .bind call token =>
    match call.op with
    | .external row =>
      some (Json.mkObj [("kind", "call"), ("callId", toJson call.callId),
        ("fiber", toJson call.fiber.value), ("token", toJson token), ("row", toJson row),
        ("request", valJson call.request)])
    | _ => none
  | .submit reply =>
    some (Json.mkObj [("kind", "reply"), ("callId", toJson reply.callId),
      ("fiber", toJson reply.key.fiber.value), ("token", toJson reply.key.token),
      ("completion", answerJson reply.completion)])
  | .apply key =>
    some (Json.mkObj [("kind", "apply"), ("fiber", toJson key.fiber.value),
      ("token", toJson key.token)])
  | .control (.evaluate fiber) =>
    some (Json.mkObj [("kind", "evaluate"), ("fiber", toJson fiber.value)])
  | .control .flush => some (Json.mkObj [("kind", "flush")])
  | .control (.advance millis) =>
    some (Json.mkObj [("kind", "advanceClock"), ("millis", .str millis.toDecimal)])
  | .control (.interruptFrom none annotations fiber) =>
    if annotations.entries.isEmpty then
      some (Json.mkObj [("kind", "cancel"), ("fiber", toJson fiber.value)])
    else none
  | _ => none

/-- Whether a host answer is a scripted completion that the host can give: a success, or one
tagged failure with no annotation. -/
def scripted : Effect4.Api.HostSession.Answer → Bool
  | .ofExit (.success _) => true
  | .ofExit (.failure cause) =>
    match cause.reasons with
    | [.fail (.tagged _ _) annotations] => annotations.entries.isEmpty
    | _ => false
  | _ => false

/-- Every call that the machine waits on while a journal plays, once each, in the order of the
guard tokens. A fiber takes its token when it parks, so this is the order in which the fibers
parked. -/
def callsOf (opened : Run) (journal : List Row) : List Await :=
  let walked := journal.foldl (fun (state : Run × List Await) row =>
    let next := state.1.step row
    (next, state.2 ++ next.outstanding.filter fun a =>
      !state.2.any fun b => b.fiber == a.fiber && b.token == a.token)) (opened, [])
  walked.2.mergeSort fun a b => a.token ≤ b.token

/-- Why a host cannot perform a script, as an error. The host has seven acts: the root's start,
a flush, a clock step, a cancellation, holding a call, a reply receipt and a reply application.

* **The acts.** A raw control that is none of the first four is no act of a host. A cancellation
  needs a fiber that the host can name: the root, or a fiber that made a call.
* **The ledger.** A host's reply carries the call id of the call it holds at that key, so a
  forged reply is no act of a host. The recorder's ledger predicts two refusals of the session:
  a reply or an application with no live call, and a second reply at a key. Any other refusal
  is the session's alone, and a host has no act that shows it.
* **The budget.** A host has no budget, so a row that stops at a frontier has no host act.
* **The schedule.** A host lets every dispatcher run after each act but the root's start. So
  the machine must have no armed owner and no runnable fiber after a row, unless the row is the
  root's start or the next row is a flush. -/
def performable (opened : Run) (journal : List Row) : Except String Unit := do
  let mut run := opened
  let mut held : List (Nat × Key) := []
  let mut known : List FiberId := [Api.root]
  let mut first := true
  let mut restless := false
  for row in journal do
    let next := run.step row
    let phase := next.phases.getLast?.getD .frontier
    if first && row != .control (.evaluate Api.root) then
      throw "the script does not start with the root's evaluation"
    if restless && row != .control .flush then
      throw "the machine has work for a flush where the script gives another row"
    match row with
    | .control (.evaluate _) =>
      unless first do throw "a second evaluation is no act of a host"
    | .control .flush => pure ()
    | .control (.advance _) => pure ()
    | .control (.interruptFrom none annotations fiber) =>
      unless annotations.entries.isEmpty do throw "an annotated interruption is outside the wire"
      unless known.contains fiber do
        throw s!"the host has no name for fiber {fiber.value}: it made no call before its cancellation"
    | .control (.answerAsync _ _ _) => throw "a direct answer decision is no act of a host"
    | .control _ => throw "a control of the scheduler that is no act of a host"
    | .bind call token =>
      unless phase == .bound do throw "the session refuses the held call"
      held := held ++ [(call.callId, ⟨call.fiber, token⟩)]
    | .submit reply =>
      unless held.contains (reply.callId, reply.key) do
        throw "a forged reply: a host's reply carries the call id of the call it holds at the key"
      unless scripted reply.completion do
        throw "a host answer that is no scripted completion: not a success and not one tagged failure"
      match phase with
      | .preflight | .refused .noCall | .refused .pendingReply => pure ()
      | .refused why =>
        throw s!"the session refuses the reply ({refusalWord why}), and a host has no reply admission of its own"
      | _ => throw "a reply receipt with an unexpected verdict"
    | .apply _ =>
      match phase with
      | .applied | .refused .noCall => pure ()
      | .frontier => throw "the reply application stops at a frontier of the budget, and a host has no budget"
      | .refused why => throw s!"the session refuses the application ({refusalWord why})"
      | _ => throw "a reply application with an unexpected verdict"
    match row, phase with
    | .control _, .progressed => pure ()
    | .control _, .frontier => throw "a control stops at a frontier of the budget, and a host has no budget"
    | .control _, _ => throw "the session refuses a control"
    | _, _ => pure ()
    restless := !first && !(next.work.queued.isEmpty && next.work.runnable.isEmpty)
    known := known ++ ((next.outstanding.map (·.fiber)).filter fun fiber => !known.contains fiber)
    first := false
    run := next

/-! ### The rows as the module's host bindings -/

/-- The TypeScript type of a row's column, as the type printer spells it. -/
def columnType (ty : Ty) : Except String String :=
  match Effect4.Codegen.Types.ofTy ty with
  | some target => .ok (TypeScript.Render.type TypeScript.house0 target)
  | none => .error "a row's column has no TypeScript type"

/-- The host bindings of a row table, as the printed module names them: the namespaces, and the
TypeScript type of the object that holds them. A row `Spelling.method` is one method. It takes
the request, or nothing when the request is `unit`, and it answers
`Effect.Effect<answer, error>`. -/
def bindingsType (table : RowTable) : Except String (List String × String) := do
  let methods ← table.mapM fun (raw : Program.Row) => do
    let row := raw.normalizeTypes
    unless row.shape == .call && row.trailing.isEmpty && row.typeArgs.isEmpty &&
        row.registration == .external && row.kind == .async do
      throw s!"the row {row.spelling} is no plain host call"
    let (space, method) ← match row.spelling.splitOn "." with
      | [space, method] => pure (space, method)
      | _ => throw s!"the row {row.spelling} is not spelled Namespace.method"
    let parameter ← if row.request == .unit then pure "" else do
      pure ("request: " ++ (← columnType row.request))
    pure (space, s!"readonly {method}: ({parameter}) => Effect.Effect<{← columnType row.answer}, {← columnType row.error}>")
  let spaces := (methods.map (·.1)).eraseDups
  let fields := spaces.map fun space =>
    s!"readonly {space}: \{ {"; ".intercalate ((methods.filter (·.1 == space)).map (·.2))} }"
  return (spaces, s!"\{ {"; ".intercalate fields} }")

/-! ### The readers' premises

A reader maps what the host notes to a part of the machine by position: the n-th cell that the
module makes is cell n, and the n-th fiber that it forks is fiber n. Each premise below is what
makes that position the machine's. Lean checks it on the program and on the scripted run. A
reader whose premise fails is refused for that run, with the reason, and its fields wait. -/

/-- Whether a program makes a cell: a `Ref.make` anywhere in it. -/
def makesCell (program : Api.Program) : Bool :=
  foldMap_eff false (· || ·) program (f_eff := fun
    | .perform .refMake _ => true
    | _ => false)

/-- Whether a program makes a fiber: a fork head, a fiber run into a scope, or a race, anywhere
in it. -/
def makesFiber (program : Api.Program) : Bool :=
  foldMap_eff false (· || ·) program (f_action := fun
    | .fork _ _ | .forkIn _ _ _ | .forkScoped _ _ | .runIn _ _ | .raceAll _ => true
    | _ => false)

/-- Whether a program holds a race. A race forks its entrants through no fork head. -/
def races (program : Api.Program) : Bool :=
  foldMap_eff false (· || ·) program (f_action := fun
    | .raceAll _ => true
    | _ => false)

/-- Whether a forked program of a program makes a fiber. A fork that starts at once runs its
program before its own fork head answers, so a fiber that the forked program makes is noted on
the host before the forked fiber is. -/
def forksInFork (program : Api.Program) : Bool :=
  foldMap_eff false (· || ·) program (f_action := fun
    | .fork forked _ | .forkIn forked _ _ | .forkScoped forked _ => makesFiber forked
    | _ => false)

/-- Whether the root makes every cell before it makes a fiber. Down the program's spine of
binds, a part that makes a fiber makes no cell, and no part after it makes one. So one fiber
makes every cell, in the program's order, and the n-th `Ref.make` that runs is cell n. The check
is conservative: it refuses a part that makes both, whatever their order inside it. -/
def cellsFirst : Api.Program → Bool
  | .bind first rest =>
    if makesFiber first then !makesCell first && !makesCell rest else cellsFirst rest
  | program => !(makesFiber program && makesCell program)

-- Controls of the premises, on small programs. A cell before a fork passes, and a cell after a
-- fork or inside one does not. The lane's program `two` forks twice and holds no race.
#guard cellsFirst (.bind (.perform .refMake (.lit (.nat 0))) two)
#guard !cellsFirst (.bind two (.perform .refMake (.lit (.nat 0))))
#guard !cellsFirst (.withFiber (.fork (.perform .refMake (.lit (.nat 0))) opts))
#guard makesFiber two && !makesCell two && !races two && !forksInFork two
#guard races (.withFiber (.raceAll (.cons two .nil))) && forksInFork (.withFiber (.fork two opts))

/-- The readers that a run gets, each with what the host must find, and the readers that it is
refused, each with the reason. The third part gives the premise of each of the four readers on
the run, asked for or not: `true`, or the reason it fails.

* `cells`: the root makes every cell before it makes a fiber (`cellsFirst`). The fixture holds
  the count of cells at the script's end.
* `fibers`: the program holds no race and no fork inside a forked program, and every fiber of
  the run but the root has a source point and the next number. The fixture holds the count of
  those fibers.
* `sleeps`: every fiber that sleeps at the script's end is the root or made a call, so the host
  has its number.
* `dispatchers`: the machine has no armed owner and no runnable fiber at the script's end. The
  host reads a count, and it names no fiber. -/
def readersOf (run : HostRun) (scripted : Run) : List (String × J) × List J × List (String × J) :=
  let program := run.opened.built.program
  let machine := scripted.machine
  let callers := Api.root :: (callsOf run.opened scripted.journal).map (·.fiber)
  let verdict : Reader → Except String J
    | .cells =>
      if cellsFirst program then .ok (toJson machine.state.refs.length)
      else .error "a Ref.make of the program follows a fork, or stands in one"
    | .fibers =>
      if races program then .error "the program holds a race, which forks through no fork head"
      else if forksInFork program then
        .error "a forked program of the program makes a fiber, so the host notes it out of order"
      else if machine.forks.any (·.site.isEmpty) then
        .error "a fiber of the run has no source point"
      else if machine.forks.map (·.child.value) != (List.range machine.forks.length).map (· + 1) then
        .error "the forked fibers of the run are not numbered in fork order"
      else .ok (toJson machine.forks.length)
    | .sleeps =>
      if scripted.work.timers.all fun timer => callers.contains timer.1 then .ok (Json.bool true)
      else .error "a fiber that sleeps at the script's end made no call, so the host has no number for it"
    | .dispatchers =>
      if scripted.work.runnable.isEmpty && scripted.work.queued.isEmpty then .ok (Json.bool true)
      else .error "the machine names an armed owner or a runnable fiber, and the host reads a count"
  let asked := run.asks.foldl (fun (state : List (String × J) × List J) reader =>
    match verdict reader with
    | .ok found => (state.1 ++ [(reader.word, found)], state.2)
    | .error why =>
      (state.1, state.2 ++ [Json.mkObj [("reader", .str reader.word), ("why", .str why)]])) ([], [])
  let premises := [Reader.cells, .fibers, .sleeps, .dispatchers].map fun reader =>
    match verdict reader with
    | .ok _ => (reader.word, Json.bool true)
    | .error why => (reader.word, Json.str why)
  (asked.1, asked.2, premises)

/-! ### The fixture and the replay -/

/-- One run's fixture: the printed module, the bindings' type, the table, the calls, the script
as the host's acts, the battery's observation of the scripted run with its fields in the
battery's order, and the readers that the run gets. -/
def emitRun (run : HostRun) : Except String J := do
  let built := run.opened.built
  let scripted := Scenario.play run.opened run.moves
  performable run.opened scripted.journal
  if let some why := run.out then throw why
  let some module := Api.printModule "main" built.program built.table
    | throw "the module printer refuses the program"
  let acts ← scripted.journal.mapM fun row =>
    match rowJson row with
    | some act => pure act
    | none => throw "a row outside the wire"
  let (spaces, bindings) ← bindingsType built.table
  let (readers, refused, premises) := readersOf run scripted
  return Json.mkObj [("name", .str run.name), ("scenario", .str run.scenario),
    ("session", .str run.opened.id),
    ("module", .str (String.join (module.decls.map (TypeScript.Render.decl TypeScript.house0)))),
    ("namespaces", toJson spaces), ("bindings", .str bindings), ("table", tableJson built.table),
    ("calls", toJson ((callsOf run.opened scripted.journal).map awaitJson)),
    ("acts", toJson acts), ("observation", Json.mkObj (run.observed scripted)),
    ("fields", toJson ((run.observed scripted).map (·.1))),
    ("readers", Json.mkObj readers), ("refusedReaders", toJson refused),
    ("premises", Json.mkObj premises)]

/-- Lean's replay of a host's recording: the rows of the recording played by `Run.play` from the
run that the battery opens. `same` is the battery's own equality of the replayed observation and
the scripted one. `fields` gives the same comparison for each field's JSON value. `verdicts`
gives the session's verdict of each row, in order. -/
def replayRun (run : HostRun) (recording : J) : Except String J := do
  keys recording ["header", "records"]
  let header ← field recording "header"
  keys header ["format", "version", "session", "profile", "program", "table"]
  unless (← strField header "format") = "effect4-host-session-v3" &&
      (← natField header "version") = version do
    throw "version 3 required; version 2 and older inputs need explicit migration"
  unless (← strField header "profile") = "keyed-v3" do throw "profile mismatch"
  unless (← strField header "session") = run.opened.id do throw "session mismatch"
  unless (← strField header "program") = run.name do throw "program mismatch"
  unless (← field header "table") == tableJson run.opened.built.table do throw "full table mismatch"
  let records := (← (← field recording "records").getArr?).toList
  let rows ← records.mapM (command run.opened.id run.opened.built.table)
  let replayed := run.opened.play rows
  let scripted := Scenario.play run.opened run.moves
  let fields := ((run.observed replayed).zip (run.observed scripted)).map fun (mine, theirs) =>
    (mine.1, Json.bool (mine.2 == theirs.2))
  return Json.mkObj [("same", toJson (run.same replayed scripted)), ("fields", Json.mkObj fields),
    ("journal", toJson (decide (replayed.journal = scripted.journal))),
    ("verdicts", toJson (replayed.phases.map verdictJson)),
    ("observation", Json.mkObj (run.observed replayed))]

/-! ### The runs

The lane holds no script. A scenario's battery lists its named runs once, in its record
(`Scenario.runs`, `Test/Dogfood/Scenario.lean`), and the lane performs each one. So a changed
script of a battery is the lane's script at the next run, with no edit here. What the lane holds
of a scenario is its own: the observation's wire, the readers that the observation asks for, and
a stated reason for a run that the lane keeps out. -/

/-- What the lane holds of one scenario beside its battery's record. -/
structure Wire where
  /-- The battery's record. Its name is the scenario's name, and its runs are the lane's runs. -/
  scenario : Scenario.Scenario
  /-- The battery's observation of a run, one JSON value a field, in the order of its fields. -/
  observed : Run → List (String × J)
  /-- Whether two runs show one observation, by the battery's own equality. -/
  same : Run → Run → Bool
  /-- The readers inside the program's state that the scenario's observation asks for. -/
  asks : List Reader := []

/-- The runs that the lane keeps out for a reason that no rule of `performable` measures, each by
its name: a finding of the target type check, stated with its evidence. -/
def keptOut : List (String × String) :=
  [ ("routing/exact-escape",
      "tsgo 7 refuses the printed module of the exact error column (TS2375, twice): the lane runs only a module that type-checks") ]

/-- The host runs of a scenario: each named run of its battery's record, in the record's order.
A run's name is the scenario's name, a slash and the run's name. -/
def Wire.runs (wire : Wire) : List HostRun :=
  wire.scenario.runs.map fun run =>
    let name := wire.scenario.name ++ "/" ++ run.name
    { name := name
      scenario := wire.scenario.name
      opened := run.opened
      moves := run.moves
      observed := wire.observed
      same := wire.same
      out := (keptOut.find? (·.1 == name)).map (·.2)
      asks := wire.asks }

/-- The routing scenario (`Test/Dogfood/Scenario/Routing.lean`), with its observation's three
fields. -/
def routing : Wire :=
  { scenario := Scenario.Routing.scenario
    observed := fun run =>
      let o := Scenario.Routing.observe run
      [ ("outcome", exitOrNull o.outcome)
      , ("repositoryCalls", toJson (o.repositoryCalls.map valJson))
      , ("refusals", toJson (o.refusals.map fun entry => [entry.1, refusalWord entry.2])) ]
    same := fun a b => Scenario.Routing.observe a == Scenario.Routing.observe b }

/-- The workers scenario (`Test/Dogfood/Scenario/Workers.lean`). Its observation has seven
fields. The work left is five readings, and each has its own entry, because the host reads two
of them. -/
def workers : Wire :=
  { scenario := Scenario.Workers.scenario
    observed := fun run =>
      let o := Scenario.Workers.observe run
      [ ("assignment", toJson (o.assignment.map valJson))
      , ("receipts", toJson (o.receipts.map seenJson))
      , ("applications", toJson (o.applications.map seenJson))
      , ("retired", toJson (o.retired.map fun entry =>
          Json.mkObj [("call", seenJson entry.1), ("kept", toJson entry.2)]))
      , ("cleanups", toJson (o.cleanups.map valJson))
      , ("rootExit", exitOrNull o.rootExit)
      , ("workLeft.runnable", toJson (o.workLeft.runnable.map (·.value)))
      , ("workLeft.queued", toJson (o.workLeft.queued.map (·.value)))
      , ("workLeft.awaiting", toJson (o.workLeft.awaiting.map awaitJson))
      , ("workLeft.pending", toJson (o.workLeft.pending.map keyJson))
      , ("workLeft.timers", toJson (o.workLeft.timers.map fun timer =>
          [toJson timer.1.value, Json.str timer.2.toDecimal])) ]
    same := fun a b => Scenario.Workers.observe a == Scenario.Workers.observe b
    asks := [.cells, .sleeps, .dispatchers] }

/-- A held call's fate, as one JSON object with one key. -/
def fateJson : Scenario.Timeout.Fate → J
  | .live => Json.mkObj [("live", true)]
  | .answered body => Json.mkObj [("answered", valJson body)]
  | .failed tag message => Json.mkObj [("failed", toJson [tag, message])]
  | .retired kept => Json.mkObj [("retired", kept)]
  | .other => Json.mkObj [("other", true)]

/-- The root's ending, as one JSON object with one key. -/
def endingJson : Scenario.Timeout.Ending → J
  | .running => Json.mkObj [("running", true)]
  | .answered body => Json.mkObj [("answered", valJson body)]
  | .failed tag message => Json.mkObj [("failed", toJson [tag, message])]
  | .interrupted => Json.mkObj [("interrupted", true)]
  | .other => Json.mkObj [("other", true)]

/-- The timeout scenario (`Test/Dogfood/Scenario/Timeout.lean`), with its observation's nine
fields. -/
def timeout : Wire :=
  { scenario := Scenario.Timeout.scenario
    observed := fun run =>
      let o := Scenario.Timeout.observe run
      [ ("calls", toJson (o.calls.map fateJson))
      , ("receipts", toJson (o.receipts.map keyJson))
      , ("applications", toJson (o.applications.map keyJson))
      , ("retired", toJson (o.retired.map fun entry =>
          Json.mkObj [("key", keyJson entry.1), ("kept", toJson entry.2)]))
      , ("stored", toJson (o.stored.map keyJson))
      , ("attempts", toJson o.attempts)
      , ("cleanups", toJson (o.cleanups.map valJson))
      , ("root", endingJson o.root)
      , ("timers", toJson (o.timers.map fun timer => [timer.1, timer.2])) ]
    same := fun a b => Scenario.Timeout.observe a == Scenario.Timeout.observe b
    asks := [.cells, .sleeps] }

/-- The atomic scenario (`Test/Dogfood/Scenario/Atomic.lean`), with its observation's five
fields. -/
def atomic : Wire :=
  { scenario := Scenario.Atomic.scenario
    observed := fun run =>
      let o := Scenario.Atomic.observe run
      [ ("decisions", toJson (o.decisions.map fun
          | .pending => Json.mkObj [("pending", true)]
          | .admitted => Json.mkObj [("admitted", true)]
          | .rejected => Json.mkObj [("rejected", true)]
          | .failedBehind => Json.mkObj [("failedBehind", true)]
          | .interrupted interruptor =>
            Json.mkObj [("interrupted", (interruptor.map fun (fiber : FiberId) => toJson fiber.value).getD .null)]
          | .other => Json.mkObj [("other", true)]))
      , ("window", (o.window.map valJson).getD .null)
      , ("account", (o.account.map valJson).getD .null)
      , ("completed", toJson o.completed)
      , ("cleanups", toJson (o.cleanups.map valJson)) ]
    same := fun a b => Scenario.Atomic.observe a == Scenario.Atomic.observe b
    asks := [.cells, .fibers] }

/-- The scenarios that the lane performs, in the lane's order. -/
def wires : List Wire := [routing, workers, timeout, atomic]

/-- The kept-out names that no run carries: a reason that outlived its run. -/
def stale (kept : List (String × String)) (all : List HostRun) : List String :=
  (kept.map (·.1)).filter fun name => !all.any (·.name == name)

-- Control of the refusal below: a kept-out name with no run is stale.
#guard stale [("routing/gone", "a reason")] [] == ["routing/gone"] && stale [] [] == []

/-- Every host run of every scenario: the named runs of the four records. It refuses a record
that lists no run, which is a battery whose program does not build. It refuses a kept-out name
that no record lists, so a reason cannot outlive its run. -/
def runs : Except String (List HostRun) := do
  for wire in wires do
    if wire.scenario.runs.isEmpty then
      throw s!"the scenario {wire.scenario.name} lists no run: a program of its battery does not build"
  let all := wires.flatMap Wire.runs
  if let name :: _ := stale keptOut all then
    throw s!"the lane keeps out the run {name}, and no scenario lists it"
  return all

/-- The fixtures of the runs that a host can perform, and each other run with the reason. -/
def emit : Except String J := do
  let all ← runs
  let fixtures := all.filterMap fun run => (emitRun run).toOption
  let waiting := all.filterMap fun run =>
    match emitRun run with
    | .ok _ => none
    | .error why => some (Json.mkObj [("name", .str run.name), ("scenario", .str run.scenario),
        ("why", .str why)])
  return Json.mkObj [("runs", toJson fixtures), ("waiting", toJson waiting)]

/-- Lean's replay of each recording of a batch, by the run's name. -/
def batch (inputs : List J) : Except String J := do
  let all ← runs
  return toJson (← inputs.mapM fun input => do
    let name ← input.getObjValAs? String "name"
    let recording ← input.getObjVal? "recording"
    let result := match all.find? (·.name == name) with
      | none => Json.mkObj [("refused", .str "unknown run")]
      | some run =>
        match replayRun run recording with
        | .ok result => result
        | .error why => Json.mkObj [("refused", .str why)]
    return Json.mkObj [("name", .str name), ("result", result)])

end Scenarios
end KeyedTool

def main (args : List String) : IO UInt32 := do
  let result ← match args with
    | ["emit"] => pure <| do
      let names := ["two", "shared", "kv", "concurrentStreams"] ++ (List.range 48).map (fun n => "stream-" ++ toString n)
      return toJson (← names.mapM KeyedTool.emitFixture)
    | ["replay", file] | ["zero", file] => do
      let input ← IO.FS.readFile file
      pure (Json.parse input >>= fun j => KeyedTool.replay j (if args.head? = some "zero" then 0 else 1000))
    | ["batch", file] => do
      let input ← IO.FS.readFile file
      pure <| do
        let inputs ← (← Json.parse input).getArr?
        return toJson (← inputs.toList.mapM fun j => do
          let name ← j.getObjValAs? String "name"
          let result := match KeyedTool.replay (← j.getObjVal? "recording") ((j.getObjValAs? Nat "fuel").toOption.getD 1000) with
            | .ok receipt => receipt | .error why => Json.mkObj [("refused", .str why)]
          return Json.mkObj [("name", .str name), ("result", result)])
    | ["scenarios"] => pure KeyedTool.Scenarios.emit
    | ["scenario-batch", file] => do
      let input ← IO.FS.readFile file
      pure <| do KeyedTool.Scenarios.batch (← (← Json.parse input).getArr?).toList
    | _ => pure (.error "usage: emit | replay FILE | zero FILE | batch FILE | scenarios | scenario-batch FILE")
  match result with
  | .error why => IO.eprintln why; pure 2
  | .ok j => IO.println j.compress; pure 0

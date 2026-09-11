import Effect4.Api.HostSession
import Effect4.Program.Profile
import Effect4.Program.Stream
import Tools.ProfileJson
import TypeScript.Render
import Lean.Data.Json

/-! Strict v2 decision-tape tool. The runtime session is the semantic owner; this is
only fixture construction, JSON transport, and rendering of the same admitted Eff program.
No legacy tape inference, oracle answer queue, or implicit pending-reply scheduler. -/
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
def two : Api.Program := forkPair (.callback (.external 0) (.lit (.nat 2)))
  (.callback (.external 0) (.lit (.nat 3))) 0

def sharedChild (value : Nat) : Api.Program :=
  .bind (.callback (.external 0) (.lit (.nat value)))
    (.perform .refSet (pair (.var 0) (.lit (.nat value))))
def shared : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (forkPair (sharedChild 1) (sharedChild 2) 1) (.perform .refGet (.var 0)))

def kv : Api.Program :=
  .bind (.callback (.external 0) (.lit .unit))
    (.bind (.callback (.external 2) (pair (.var 0) (pair (.lit (.str "a")) (.lit (.str "A")))))
      (.bind (.callback (.external 2) (pair (.var 0) (pair (.lit (.str "b")) (.lit (.str "B")))))
        (forkPair (.callback (.external 1) (pair (.var 0) (.lit (.str "a"))))
          (.callback (.external 1) (pair (.var 0) (.lit (.str "b")))) 3)))

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
    | _ => throw "unsupported error shape"
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
    | .boolean => discard ((← field j name).getBool?)
    | .text => discard (strField j name)
    | .json => pure ()
  return kind

def consume {p : Api.Program} {rows : RowTable} (s : Session p rows) (fuel : Nat)
    (j : J) : Except String (Effect4.Api.HostSession.Result p rows) := do
  match ← checkRecord j s.header.session with
  | "call" =>
    let key ← keyOf j
    return bindCall s ⟨version, s.header.session, rows, ← natField j "callId", key.fiber,
      .external (← natField j "row"), ← decodeVal 64 (← field j "request")⟩ key.token
  | "reply" =>
    let key ← keyOf j
    let answer ← decodeAnswer (← field j "completion")
    -- Nonempty Some is the stream binding refinement, checked before ordinary Envelope.
    if rows = streamTable then
      match requestOf s.machine key.fiber key.token, answer with
      | some (.external 1, _), .ofExit (.success value) =>
        if (Stream.chunk? value).isNone then throw "empty or malformed stream chunk"
      | _, _ => pure ()
    return submit s ⟨version, s.header.session, ← natField j "callId", key, answer⟩
  | "apply" => return applyReply s (← keyOf j) fuel
  | "advanceClock" => return advance s fuel (.advance (← natField j "millis"))
  | "cancel" => return advance s fuel (.interruptFrom none .empty ⟨← natField j "fiber"⟩)
  | "evaluate" => return advance s fuel (.evaluate ⟨← natField j "fiber"⟩)
  | "fire" => return advance s fuel (.fire ⟨← natField j "fiber"⟩)
  | "flush" => return advance s fuel .flush
  | "yieldVerdict" => return advance s fuel (.yieldVerdict ⟨← natField j "fiber"⟩ (← (← field j "verdict").getBool?))
  | "installMiddleware" => return advance s fuel .installMiddleware
  | _ => throw "unimplemented protocol record"

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
  let (fiber, token, op, request) := entry
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
  unless (← strField h "format") = "effect4-host-session-v2" && (← natField h "version") = version do
    throw "version 2 required; legacy input needs explicit migration"
  unless (← strField h "profile") = "keyed-v2" do throw "profile mismatch"
  let f ← fixture (← strField h "program")
  unless (← field h "table") == tableJson f.table do throw "full table mismatch"
  let header : Header := ⟨version, ← strField h "session", "keyed-v2", f.table⟩
  let s ← (start f.program f.table "keyed-v2" header 1000).mapError reprStr
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
    for (fiber, token, op, request) in outstanding s do
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
  let header : Header := ⟨version, "plan", "keyed-v2", f.table⟩
  let s ← (start f.program f.table "keyed-v2" header 1000).mapError reprStr
  let s := (advance s 1000 Api.evaluate).session
  planRun f s {} 100

def emitFixture (name : String) : Except String J := do
  let f ← fixture name
  discard <| (Api.admitProgram f.program f.table).mapError (fun _ => "program admission refused: " ++ name)
  let expr ← (Api.print f.program f.table).mapError (fun _ => "print refused: " ++ name)
  let (schedule, expected) ← plan f
  return Json.mkObj [("name", .str name), ("table", tableJson f.table),
    ("plan", toJson schedule), ("expected", expected),
    ("source", f.source), ("expression", .str (TypeScript.Render.expr TypeScript.house0 0 expr))]
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
    | _ => pure (.error "usage: emit | replay FILE | zero FILE | batch FILE")
  match result with
  | .error why => IO.eprintln why; pure 2
  | .ok j => IO.println j.compress; pure 0

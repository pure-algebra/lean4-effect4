import Effect4.Api.HostSession
import Effect4.Program.Profile
import Tools.ProfileJson
import TypeScript.Render
import Lean.Data.Json

/-! Thin strict JSON boundary for the selected serial-root scalar session.
The table check is equality with Tools.ProfileJson's complete view. This tool is outside
canonical Eff and the library proof boundary; no JSON-parser or JS-adequacy theorem is claimed.
This is the explicit v1 serial adapter; it binds the missing key at the actual park and
retains the original v1 records. New v2 recordings use Keyed.lean and require recorded keys. -/

open Lean Effect4 Effect4.Machine Effect4.Program Effect4.Api.HostSession
abbrev J := Lean.Json
namespace HostSessionTool

def table : RowTable := [Profile.Scalar.waitRow]
def resourceFailure : Api.Program := .scoped
  (.bind (.acquireRelease (.callback (.external 0) (.lit .unit)) (.callback (.external 2) (.var 0)))
    (.bind (.callback (.external 1) (.var 0))
      (.bind (.callback (.external 1) (.var 0)) (.callback (.external 1) (.var 0)))))
def resourceSuccess : Api.Program := .scoped
  (.bind (.acquireRelease (.callback (.external 0) (.lit .unit)) (.callback (.external 2) (.var 0)))
    (.callback (.external 1) (.var 0)))
def resourceClosed : Api.Program :=
  .bind (.callback (.external 0) (.lit .unit))
    (.bind (.callback (.external 2) (.var 0)) (.callback (.external 1) (.var 0)))
def isResource (name : String) : Bool := ["resourceFailure", "resourceSuccess", "resourceClosed"].contains name
def tableFor (name : String) : RowTable := if isResource name then [Profile.Resource.acquireRow, Profile.Resource.useRow, Profile.Resource.releaseRow] else table
def profileFor (name : String) : String := if isResource name then "serial-root-resource-v1" else "serial-root-scalar-v1"

def program (name : String) : Except String Api.Program :=
  if name = "two" then .ok (.bind (.callback (.external 0) (.lit (.nat 2)))
    (.callback (.external 0) (.lit (.nat 3))))
  else if name = "failure" then .ok (.callback (.external 0) (.lit (.nat 7)))
  else if name = "resourceFailure" then .ok resourceFailure
  else if name = "resourceSuccess" then .ok resourceSuccess
  else if name = "resourceClosed" then .ok resourceClosed
  else .error "unknown fixture"

def tableJson (rows : RowTable) : J := .arr (rows.map Tools.ProfileJson.rowJson).toArray

def emitFixture (name : String) : Except String J := do
  let p ← program name
  let rows := tableFor name
  let e ← (Api.print p rows).mapError (fun _ => "printer refused")
  return Json.mkObj [("name", .str name), ("expression", .str (TypeScript.Render.expr TypeScript.house0 0 e)),
    ("profile", .str (profileFor name)), ("table", tableJson rows), ("natBound", toJson Profile.Scalar.profile.natBound)]

def keys (j : J) (wanted : List String) : Except String Unit := do
  let obj ← j.getObj?
  let actual := obj.toList.map Prod.fst
  if actual.length = wanted.length && actual.all (fun k => wanted.contains k) then pure ()
  else throw "missing or extra fields"

def boundedText (j : J) : Except String String := do
  let s ← j.getStr?
  if s.length ≤ 4096 then pure s else throw "text exceeds protocol bound"

def field (j : J) (key : String) : Except String J := j.getObjVal? key

def strField (j : J) (key : String) : Except String String := field j key >>= boundedText

def natField (j : J) (key : String) : Except String Nat := do
  let n ← (← field j key).getNat?
  if n ≤ rc112.natBound then pure n else throw "unsafe natural"

def checkVersion (j : J) : Except String Unit := do
  if (← natField j "version") = 1 then pure () else throw "unknown version"

def decodeAnswer (j : J) : Except String Answer := do
  match ← strField j "kind" with
  | "success" =>
    keys j ["kind", "value"]
    if (← field j "value") == .null then return (.ofExit (.success .unit))
    let n ← natField j "value"
    if n > Profile.Scalar.profile.natBound then throw "outsideProfile: answer natural"
    pure (.ofExit (.success (.nat n)))
  | "fail" =>
    keys j ["kind", "error", "diagnostic"]
    let pair ← (← field j "error").getArr?
    if pair.size ≠ 2 then throw "expected pair failure"
    let tag ← boundedText (pair[0]!)
    let message ← boundedText (pair[1]!)
    let d ← field j "diagnostic"
    keys d ["category", "tag", "message"]
    if (← strField d "category") ≠ "Fail" || (← strField d "tag") ≠ tag ||
      (← strField d "message") ≠ message then throw "contradictory failure diagnostic"
    pure (.ofExit (.failure (Cause.fail (.tagged tag message))))
  | "die" =>
    keys j ["kind", "message", "diagnostic"]
    let message ← strField j "message"
    let d ← field j "diagnostic"
    keys d ["category", "message"]
    if (← strField d "category") ≠ "Die" || (← strField d "message") ≠ message then
      throw "contradictory defect diagnostic"
    pure (.ofExit (.failure (Cause.die (.error (.text message)))))
  | _ => throw "unsupported completion category"

/-- Decode the resource profile's explicit identity claim. A scalar index remains a scalar;
only this discriminated request form becomes a prepared machine handle. -/
def decodeRequest (session profile : String) (j : J) : Except String Val := do
  if j == .null then return .unit
  match j with
  | .num _ =>
    let n ← j.getNat?
    if n > Profile.Scalar.profile.natBound then throw "outsideProfile: request natural"
    pure (.nat n)
  | _ =>
    if profile ≠ "serial-root-resource-v1" then throw "resource request outside resource profile"
    keys j ["resource"]
    let claim ← field j "resource"
    keys claim ["session", "target", "index"]
    if (← strField claim "session") ≠ session || (← strField claim "target") ≠ Profile.Resource.target then
      throw "foreign resource claim"
    pure (Value.external (← natField claim "index"))

/-- Scalar/session record check. Runtime identity is the explicit serial-root association;
its semantic identity remains zero. The replay token is obtained separately from that park. -/
def consume {p : Api.Program} {rows : RowTable} (s : Session p rows) (rootRuntime : Nat) (fuel : Nat)
    (j : J) : Except String (Effect4.Api.HostSession.Result p rows) := do
  checkVersion j
  let session ← strField j "session"
  let callId ← natField j "callId"
  if session ≠ s.header.session then throw "session mismatch"
  match ← strField j "kind" with
  | "call" =>
    keys j ["kind", "version", "session", "callId", "fiber", "runtimeFiber", "row", "request"]
    let fiber ← natField j "fiber"
    if fiber ≠ 0 || (← natField j "runtimeFiber") ≠ rootRuntime then throw "outside serial root fiber"
    let row ← natField j "row"
    let request ← decodeRequest session s.header.profile (← field j "request")
    let some current := (outstanding s).find? (fun x => x.1 = ⟨fiber⟩)
      | throw "no outstanding call for recorded fiber"
    pure (bindCall s ⟨version, session, s.header.table, callId, ⟨fiber⟩, .external row, request⟩ current.2.1)
  | "reply" =>
    keys j ["kind", "version", "session", "callId", "completion"]
    let completion ← decodeAnswer (← field j "completion")
    let some bound := s.active.find? (fun b => b.call.callId == callId)
      | throw "unknown legacy call association"
    let reply : Reply := ⟨version, session, callId, bound.key, completion⟩
    let staged ← match readReply s.pending reply.key with
      | none => pure (submit s reply)
      | some old => if old = reply then pure ⟨.preflight, s⟩ else throw "pending reply differs"
    if staged.phase = .preflight then pure (applyPending staged.session fuel)
    else pure staged
  | _ => throw "unknown record kind"

structure Walk (p : Api.Program) (rows : RowTable) where
  session : Session p rows
  position : Nat
  status : String
  remaining : List J

/-- The current completion record remains unconsumed at zero fuel. A caller can resume the
same remaining list and session; no replay record is manufactured or loaded into an oracle. -/
def walk {p : Api.Program} {rows : RowTable} (rootRuntime fuel : Nat) (s : Session p rows)
    (position : Nat) (records : List J) : Walk p rows :=
  match records with
  | [] => ⟨s, position, "prefix-end", []⟩
  | record :: rest =>
    match consume s rootRuntime fuel record with
    | .error why => ⟨s, position, "refused: " ++ why, records⟩
    | .ok result =>
      match result.phase with
      | .bound | .applied => walk rootRuntime fuel result.session (position + 1) rest
      | .frontier => ⟨result.session, position, "frontier", records⟩
      | .refused why => ⟨result.session, position, "refused: " ++ reprStr why, records⟩
      | _ => ⟨result.session, position, "unexpected phase", records⟩
termination_by records

def exitJson : ExitV → J
  | .success .unit => Json.mkObj [("success", .null)]
  | .success (.nat n) => Json.mkObj [("success", toJson n)]
  | .failure cause => Json.mkObj [("failure", .arr (cause.reasons.map fun r =>
      match r with
      | .fail (.tagged tag message) _ => Json.mkObj [("fail", toJson [tag, message])]
      | .die (.error (.text message)) _ => Json.mkObj [("die", Json.mkObj [("error", .str message)])]
      | _ => Json.mkObj [("unsupported", .bool true)]).toArray)]
  | _ => Json.mkObj [("unsupported", .bool true)]

def outcomeJson (o : Api.Outcome) : J := .str <| match o with
  | .finished => "finished" | .frontier => "frontier" | .stuck _ => "stuck"

def receipt {p : Api.Program} {rows : RowTable} (r : Walk p rows) : J :=
  let run := inspect r.session
  Json.mkObj [("status", .str r.status), ("position", toJson r.position),
    ("applied", toJson r.session.applied), ("pending", .bool (!(pendingReplies r.session).isEmpty)),
    ("outcome", outcomeJson run.outcome), ("exit", (run.exit.map exitJson).getD .null),
    ("remaining", toJson r.remaining.length), ("allocated", toJson r.session.machine.state.externals.allocated), ("oracleAnswers", toJson r.session.machine.state.externals.answers.length),
    ("awaits", .arr ((outstanding r.session).map fun (fiber, token, op, req) => Json.mkObj [
      ("fiber", toJson fiber.value), ("token", toJson token),
      ("row", match op with | .external i => toJson i | _ => .null),
      ("request", match req with | .nat n => toJson n | _ => .null)]).toArray)]

def replay (j : J) (fuel : Nat) (splitAt : Option Nat := none) : Except String J := do
  keys j ["header", "records"]
  let h ← field j "header"
  keys h ["format", "version", "session", "profile", "program", "table", "rootRuntimeFiber"]
  checkVersion h
  if (← strField h "format") ≠ "effect4-host-session-v1" then throw "unknown format"
  let name ← strField h "program"
  let p ← program name
  let rows := tableFor name
  if (← field h "table") != tableJson rows then throw "full table mismatch"
  let rootRuntime ← natField h "rootRuntimeFiber"
  let header : Header := ⟨version, ← strField h "session", ← strField h "profile", rows⟩
  let s ← (start p rows (profileFor name) header 300).mapError reprStr
  let s := (advance s 300 Api.evaluate).session
  let records := (← (← field j "records").getArr?).toList
  let first := walk rootRuntime fuel s 0 (records.take (splitAt.getD records.length))
  let all := match splitAt with
    | none => first
    | some n => walk rootRuntime 300 first.session first.position (first.remaining ++ records.drop n)
  pure <| Json.mkObj [("prefix", receipt first), ("result", receipt all)]

end HostSessionTool

def main (args : List String) : IO UInt32 := do
  let result ← match args with
    | ["emit"] => pure <| do
      let fixtures ← ["two", "failure", "resourceFailure", "resourceSuccess", "resourceClosed"].mapM HostSessionTool.emitFixture
      pure (Lean.Json.mkObj [("fixtures", toJson fixtures)])
    | ["batch", file] => do
      let text ← IO.FS.readFile file
      pure <| do
        let cases ← (← Lean.Json.parse text).getArr?
        let results ← cases.toList.mapM fun item => do
          let name ← item.getObjValAs? String "name"
          let recording ← item.getObjVal? "recording"
          let result := match HostSessionTool.replay recording 300 with
            | .ok value => value
            | .error why => Lean.Json.mkObj [("refused", .str why)]
          pure (Lean.Json.mkObj [("name", .str name), ("result", result)])
        pure (toJson results)
    | ["replay", file] => do
      let text ← IO.FS.readFile file
      pure (Lean.Json.parse text >>= fun j => HostSessionTool.replay j 300)
    | ["resume", file] => do
      let text ← IO.FS.readFile file
      pure (Lean.Json.parse text >>= fun j => HostSessionTool.replay j 300 (some 2))
    | ["zero", file] => do
      let text ← IO.FS.readFile file
      pure (Lean.Json.parse text >>= fun j => HostSessionTool.replay j 0 (some 2))
    | _ => pure (.error "usage: emit | replay FILE | resume FILE | zero FILE | batch FILE")
  match result with
  | .ok j => IO.println j.compress; pure 0
  | .error why => IO.eprintln why; pure 2

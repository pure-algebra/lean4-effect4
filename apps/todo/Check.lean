import Tools.RunChecks
import Test.Dogfood.Scenario.Todo

/-!
# The to-do application's checker (decisions row 378 (16), slice V4)

    lake env lean --run apps/todo/Check.lean SESSION...

Reads each session's file that the front wrote (`apps/todo/server.ts`): a header line, then one
record a line. For each request it decides the five checks of the lowering note's §6.1
(`Tools.RunChecks.checkSession`):

1. the entry builds at the request's arguments (`builtAt`, `Test/Dogfood/Scenario/Todo.lean`);
2. the host that answers from the record drives the built program (`Run.runWith`), and it answers
   every call, in order, from the record;
3. the root's exit of that run is the face's exit;
4. the run is funded, at rest and driven by a host;
5. the run conforms to the application's protocols, and the reference model `repository` gives
   its answers. The model's state is threaded across the session's requests, from the start state
   that the session's header gives.

Prints one JSON object: each session with each request's verdict. The checker refuses a session's
file that is malformed, that records another application, or whose table is not the
application's table, and it then exits 2. A failing check is a verdict, not a refusal.

Placement: each decision discharges a premise that the claim record grades `validated`
(`claimRecord`, `Test/Dogfood/Scenario/Todo/Claims.lean`). Its consumers are `conforms_sat` and
`agrees_hostRun` (`src/Effect4/Laws/Program/Validated.lean`). Where every check of a request
passes, the to-do's proved claims hold of Lean's run of that record. Nothing is established of a
run that no check read. The start state is the front's reading of the database: no check reads it.
-/

open Lean Effect4 Effect4.Machine Effect4.Program
open Tools.RunChecks (J keys field text nat natField literal decodeSession checkSession valJson
  Verdict)
open Test.Dogfood.Scenario.Todo (application builtAt protocols repository Repo)

/-- The model's start state from a session's header: the next id and the stored to-dos, each
`[id, title, done]`. -/
def startOf (j : J) : Except String Repo := do
  keys j ["next", "todos"]
  let todos ← (← (← field j "todos").getArr?).toList.mapM fun todo => do
    match (← todo.getArr?).toList with
    | [id, title, done] => return (← nat id, ← text title, ← done.getBool?)
    | _ => throw "a stored to-do is [id, title, done]"
  return (← natField j "next", todos)

/-- An entry built at a request's arguments, each a source literal. -/
def build (entry : String) (args : List Val) : Option Api.Built :=
  (args.mapM literal).bind fun lits => builtAt entry (lits.map Authoring.lit)

/-- The checks of one session's file. -/
def checkFile (path : String) (lines : List String) : Except String J := do
  let (header, records) ← decodeSession lines
  unless header.application = application.name do
    throw s!"{path}: the session records the application {header.application}"
  unless header.table == Tools.ProfileJson.tableJson application.table do
    throw s!"{path}: the session's table is not the application's table"
  let start ← startOf header.start
  let verdicts := checkSession build header.session protocols repository start records
  let requests := (records.zip verdicts).map fun (record, verdict) =>
    Json.mkObj [("entry", .str record.entry), ("args", toJson (record.args.map valJson)),
      ("verdict", verdict.json)]
  return Json.mkObj [("path", .str path), ("session", .str header.session),
    ("requests", toJson requests), ("passed", toJson (verdicts.all Verdict.passed))]

def main (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "usage: Check.lean SESSION..."
    return 2
  let mut sessions := #[]
  for path in paths do
    match checkFile path (← IO.FS.lines path).toList with
    | .ok session => sessions := sessions.push session
    | .error why =>
      IO.eprintln why
      return 2
  IO.println (Json.mkObj [("sessions", .arr sessions)]).compress
  return 0

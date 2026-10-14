import Tools.RunChecks
import Test.Dogfood.Scenario.Todo.Cached

/-!
# The to-do application's recorded cached-service checker

    lake env lean --run apps/todo/Check.lean SESSION...

Each record builds the cached service module. Its main makes the service state once, then invokes
the selected method at that state and the record's literal arguments (`Cached.consumerBuiltAt`).
Each replay starts from empty stores, matching the face's fresh service cells per request.
Unknown method names refuse.

`Tools.RunChecks.checkSession` checks the build, exact ordered host calls, the root exit, funding,
rest and host control, protocol conformance, and reference-model answers. The model state passes
between records from the session header. The checker refuses malformed files, another application,
or another row table. A failing check produces a verdict.

The consumers are `conforms_sat_blocks` and `agrees_hostRun_blocks`
(`src/Effect4/Laws/Program/ValidatedBlocks.lean`), through `H9Blocks`. Their reach requires a
completed `BlockRows` run and matching host answers, beside the checked runtime premises.
A postcondition also needs its separate tree-level claim on every finished budgeted leaf.
Passing runtime checks alone proves no arbitrary postcondition or outside-host agreement.

The twin invokes definitions. It does not replay the face's layer scope and memo map.
The header supplies the initial database state; no check verifies that reading.
-/

open Lean Effect4 Effect4.Machine Effect4.Program
open Tools.RunChecks (J keys field text nat natField literal decodeSession checkSession valJson
  Verdict)
open Test.Dogfood.Scenario.Todo (application protocols repository Repo)
open Test.Dogfood.Scenario.Todo.Cached (consumerBuiltAt)

/-- The model's start state from a session's header: the next id and the stored to-dos, each
`[id, title, done]`. -/
def startOf (j : J) : Except String Repo := do
  keys j ["next", "todos"]
  let todos ← (← (← field j "todos").getArr?).toList.mapM fun todo => do
    match (← todo.getArr?).toList with
    | [id, title, done] => return (← nat id, ← text title, ← done.getBool?)
    | _ => throw "a stored to-do is [id, title, done]"
  return (← natField j "next", todos)

/-- A fresh cached service consumer at a request's arguments, each a source literal. -/
def build (entry : String) (args : List Val) : Option Api.Built :=
  (args.mapM literal).bind fun lits => consumerBuiltAt entry (lits.map Authoring.lit)

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

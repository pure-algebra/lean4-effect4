import Effect4.Schema.Prepare
import Tools.JsonBridge
import Test.Dogfood.Scenario.Todo

open Effect4 Effect4.Schema.DocumentJson Effect4.Schema.Prepare

def fixtureText : String := include_str "../../../Test/fixtures/schema-documents/effect-rpc-rc112.json"

def fieldOf (j : Json) (k : String) : Option Json :=
  match j with
  | .obj fs => List.lookup k fs
  | _ => none

def arrOf : Option Json → List Json
  | some (.arr js) => js
  | _ => []

def strOf : Option Json → String
  | some (.str s) => s
  | _ => "?"

def showRead {α : Type} (f : α → String) : Read α → String
  | .ok a => s!"ok {f a}"
  | .error e => s!"refused at {e.path}: {reprStr e.reason}"

#eval show IO Unit from do
  let some j := (Lean.Json.parse fixtureText).toOption.bind (Tools.JsonBridge.ofLeanJson 4096)
    | IO.println "fixture unread"
  for rpc in arrOf (fieldOf j "rpcs") do
    let tag := strOf (fieldOf rpc "tag")
    for part in ["payload", "success", "error", "exit"] do
      let doc := (fieldOf rpc part).getD .null
      let d := Document.ofJson doc
      let back := match d with
        | .ok d => decide (Document.ofJson d.toJson = .ok d)
        | .error _ => false
      IO.println s!"{tag}.{part}: doc {showRead (fun _ => "") d} back={back}; prepared {showRead (fun r => (reprStr r).take 0) (d >>= prepare)}; ty {showRead (fun t => reprStr t) (tyOfJson doc)}"
  let env := (fieldOf j "envelope").getD .null
  IO.println s!"envelope: doc {showRead (fun _ => "") (Document.ofJson env)}; ty {showRead (fun t => reprStr t) (tyOfJson env)}"

open Test.Dogfood.Scenario.Todo in
#eval show IO Unit from do
  for r in TodoRepo.rows do
    IO.println s!"{r.row.spelling}: request {reprStr r.row.request}; answer {reprStr r.row.answer}; error {reprStr r.row.error}"

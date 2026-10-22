import Effect4.Run.Runner
import Effect4.Run.Event
import Test.Dogfood.Scenario.Todo.CachedProgram

/-! Law-free finite fixtures for checked service sessions.
The contract battery owns the evaluations. Each reactor holds only its own state.
These fixtures make no claim about physical host effects or arbitrary service behaviour. -/

set_option autoImplicit false
namespace Test.Api.SessionFixtures
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Machine
open Effect4.Api (Built SessionRefusal)
open Test.Dogfood.Scenario.Todo (Repo repository todo)

/-- Replies are accepted calls at session reply rows, in journal order. -/
def replies (run : Run) : List (String × Val) :=
  (Run.rows run).filterMap fun
    | (.bind call _, .bound) => do
      let row ← run.rowOf call.op
      if Effect4.Api.ServiceSession.isReplyRow row then some (row.spelling, call.request) else none
    | _ => none

/-- Record each repository operation that receives an answer. -/
def recordedRepository : Run.Reactor (Repo × List String) := fun row sent state =>
  (repository row sent state.1).map fun (answer, next) =>
    (answer, (next, state.2 ++ [row.spelling]))

def todoBuilt : Option Built :=
  Test.Dogfood.Scenario.Todo.Cached.built? Examples.Todo.application
def cachedBuilt : Option Built :=
  Test.Dogfood.Scenario.Todo.Cached.built? Test.Dogfood.Scenario.Todo.Cached.cached
def todoSession : Option Built := todoBuilt.bind fun b => (b.session "TodoApp").toOption
def cachedSession : Option Built := cachedBuilt.bind fun b => (b.session "TodoApp").toOption

def todoRequests : List Val :=
  [.list [.str "add", .str "milk"], .list [.str "add", .str "café 日本 🙂"],
   .list [.str "list", .unit], .list [.str "complete", .nat 1],
   .list [.str "list", .unit], .list [.str "remove", .nat 1],
   .list [.str "list", .unit]]
def twoLists : List Val := [.list [.str "list", .unit], .list [.str "list", .unit]]
def stocked : Repo := (2, [(1, "milk", false)])

/-- One whole to-do lifetime with a recorded repository. -/
def runTodo (built : Built) (requests : List Val) (initial : Repo) :
    Run × (List Val × (Repo × List String)) :=
  Run.runWith built (Run.Reactor.tensor Run.Reactor.queue recordedRepository) (requests, (initial, []))
    "session-contract" {} 512

def todoRun : Option (Run × (List Val × (Repo × List String))) :=
  todoSession.map fun b => runTodo b todoRequests (1, [])

/-- One client creates the service state once and keeps every method exit. -/
def clientMain : Src NativeOp :=
  bindWith (Def.invoke "TodoAppContext" []) fun state =>
  bindWith (exit (Def.invoke "TodoApp_add" [state, str "milk"])) fun first =>
  bindWith (exit (Def.invoke "TodoApp_add" [state, str "café 日本 🙂"])) fun second =>
  bindWith (exit (Def.invoke "TodoApp_list" [state])) fun third =>
  bindWith (exit (Def.invoke "TodoApp_complete" [state, nat 1])) fun fourth =>
  bindWith (exit (Def.invoke "TodoApp_list" [state])) fun fifth =>
  bindWith (exit (Def.invoke "TodoApp_remove" [state, nat 1])) fun sixth =>
  bindWith (exit (Def.invoke "TodoApp_list" [state])) fun seventh =>
  succeed (app "pair" [first, app "pair" [second, app "pair" [third,
    app "pair" [fourth, app "pair" [fifth, app "pair" [sixth, app "pair" [seventh, unit]]]]]]])

def clientBuilt : Option Built :=
  (Examples.Todo.application.serviceModule "TodoApp").toOption.bind fun m =>
    (Effect4.Api.Author.build { m with main := clientMain }).toOption

def clientRun : Option (Run × (Repo × List String)) :=
  clientBuilt.map fun b => Run.runWith b recordedRepository ((1, []), []) "session-client" {} 512

def success (value : Val) : Val := reifyExitVal (.success value)
def todoExpected : List Val :=
  [success (todo 1 "milk" false), success (todo 2 "café 日本 🙂" false),
   success (.list [todo 1 "milk" false, todo 2 "café 日本 🙂" false]),
   success (todo 1 "milk" true),
   success (.list [todo 1 "milk" true, todo 2 "café 日本 🙂" false]),
   success .unit, success (.list [todo 2 "café 日本 🙂" false])]

/-- Reopen a changed object and run the public constructor, keeping exact refusals. -/
def sessionObject (object : Object) (service : String) : Except SessionRefusal Object := do
  let built ← object.open.mapError .admission
  return Object.ofBuilt (← built.session service)

def withRow (object : Object) (spelling : String) : Object :=
  { object with app := { object.app with
      rows := object.app.rows ++ [(Row.host spelling .unit .unit).row] } }

/-- A plain definition shadows the name of the selected list method.
The original method still has its service role and position. -/
def shadowed : Option Object := todoBuilt.bind fun b =>
  match b.program with
  | .defs decls bodies main layers => do
    let d ← decls.find? fun d => match d.role with
      | .serviceMethod s m _ => s == "TodoApp" && m == "list"
      | _ => false
    let program := .defs ({ d with role := .plain } :: decls)
      (.cons (.succeed (.app "nil" .nil)) bodies) main layers
    pure { app := b.app, program := program }
  | _ => none

def unitProgram : NativeEff := .succeed (.lit .unit)
def initialDecl : DefDecl :=
  { name := "initial", request := .unit, answer := .unit, role := .serviceInit "Simple" }
def methodDecl : DefDecl :=
  { name := "method", request := .unit, answer := .unit,
    role := .serviceMethod "Simple" "m" 0 }

/-- A two-definition object whose changes isolate each constructor boundary. -/
def oneMethod (method : DefDecl := methodDecl) (body : NativeEff := unitProgram)
    (initial : DefDecl := initialDecl) (initBody : NativeEff := unitProgram) : Object :=
  let program := .defs [initial, method] (.cons initBody (.cons body .nil)) unitProgram .nil
  { app := {}, program := program }

def unitKey : ServiceKey := ⟨⟨30⟩, ⟨6⟩⟩
def natKey : ServiceKey := ⟨⟨30⟩, ⟨4⟩⟩
def programParameter : ParamDecl := { name := "callback", request := .unit, answer := .unit }

def parameterized : Object := oneMethod { methodDecl with params := [programParameter] }
def remaining : Object :=
  oneMethod { methodDecl with requires := [unitKey] } (.service unitKey)
def nonunit : Object :=
  oneMethod methodDecl unitProgram { initialDecl with requires := [natKey] }
def incomingHandle : Object :=
  oneMethod
    { methodDecl with
      request := .prod .unit (.refOf .nat)
      role := .serviceMethod "Simple" "m" 1 }
def outgoingHandle : Object :=
  oneMethod { methodDecl with answer := .refOf .nat } (.perform .refMake (.lit (.nat 0)))
/-- A read of a key the signature does not type: source admission refuses it. -/
def foreignKey : ServiceKey := ⟨⟨30⟩, ⟨99⟩⟩
def foreignRemaining : Object :=
  oneMethod { methodDecl with requires := [foreignKey] } (.service foreignKey)
def named (name : String) : Object :=
  oneMethod { methodDecl with role := .serviceMethod "Simple" name 0 }

/-- An unused program parameter does not restrict the selected service. -/
def unusedParameterized : Object :=
  let helper := { methodDecl with name := "helper", role := .plain, params := [programParameter] }
  let program := .defs [initialDecl, methodDecl, helper]
    (.cons unitProgram (.cons unitProgram (.cons unitProgram .nil))) unitProgram .nil
  { app := {}, program := program }

/-- Two value arguments retain their tuple shape through request dispatch. -/
def twoArguments : Object :=
  oneMethod
    { methodDecl with
      request := .prod .unit (.prod .nat .string)
      answer := .prod .nat .string
      role := .serviceMethod "Simple" "m" 2 }
    (.succeed (.app "snd" (.cons (.var 0) .nil)))

/-- Initialization fails before the session asks the host for a request. -/
def initialFailure : Object :=
  oneMethod methodDecl unitProgram { initialDecl with error := .nat } (.fail (.lit (.nat 13)))

/-- A method reads a module layer through its stored position. -/
def moduleLayer : Object :=
  let body : NativeEff := .provideLayer (.ref [2, 0]) false (.service natKey)
  let program := .defs [initialDecl, { methodDecl with answer := .nat }]
    (.cons unitProgram (.cons body .nil)) unitProgram
    (.cons (.succeed natKey (.nat 23)) .nil)
  { app := {}, program := program }

/-- A small service for the outside execution control: failure, then two updates to one cell. -/
def exampleModule : Module NativeOp :=
  { defs :=
      [ DefSrc.serviceInit "Example"
          { name := "exampleInit", params := [], answer := .refOf .nat, body := fun _ => Ref.make (nat 0) },
        DefSrc.serviceMethod "Example" "check"
          { name := "exampleCheck", params := [("state", .refOf .nat), ("n", .nat)],
            answer := .nat, error := .nat,
            body := fun
              | [state, n] => ifElse (app "eq" [n, nat 0]) (fail (nat 0))
                  (Ref.updateAndGetWith state (fun current => app "add" [current, n]))
              | _ => succeed (nat 0) } ],
    main := succeed unit }
def exampleBuilt : Option Built := (Effect4.Api.Author.build exampleModule).toOption
def exampleSession : Option Built := exampleBuilt.bind fun b => (b.session "Example").toOption
def exampleRequests : List Val :=
  [.list [.str "check", .nat 0], .list [.str "check", .nat 7], .list [.str "check", .nat 2]]
def exampleExpected : List Val :=
  [reifyExitVal (.failure (.fail (.tag 0))), success (.nat 7), success (.nat 9)]
def noHost : Run.Reactor Unit := fun _ _ _ => none
def runExample (built : Built) (requests : List Val) : Run × (List Val × Unit) :=
  Run.runWith built (Run.Reactor.tensor Run.Reactor.queue noHost)
    (requests, ()) "session-example" {} 128
def exampleRun : Option (Run × (List Val × Unit)) :=
  exampleSession.map fun b => runExample b exampleRequests

end Test.Api.SessionFixtures

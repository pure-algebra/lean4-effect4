import Probe.Session

/-! Finite controls for session construction and a smaller positional construction.
Consumer: the proposed session admission and BlockRows obligations, R6 and R13.
These controls establish no transformation theorem or physical host behaviour. -/

set_option autoImplicit false
namespace Refinement.Session
open Effect4 Effect4.Program Effect4.Machine
open Probe.Session

def collisionObject : Option Object := todoObject.map fun o =>
  { o with app := { o.app with rows := o.app.rows ++
      [(Authoring.Row.host "Session.next" .unit .unit).row] } }
#guard collisionObject.map (fun o => o.open.isOk && o.services.isOk) = some true
#guard (collisionObject.bind fun o => (session o "TodoApp").toOption).isSome
#guard (collisionObject.bind fun o => (session o "TodoApp").toOption).map
  (fun so => so.open.isOk) = some false

-- Prepend an admitted definition that shares a method's name and type.
-- The selected original method remains identified by its position.
def shadowedObject : Option Object := todoObject.bind fun o =>
  match o.program with
  | .defs decls bodies main layers => do
    let d ← decls.find? fun d => match d.role with
      | .serviceMethod s m _ => s == "TodoApp" && m == "list"
      | _ => false
    let program := .defs ({ d with role := .plain } :: decls)
      (.cons (.succeed (.app "nil" .nil)) bodies) main layers
    pure { o with program := program }
  | _ => none
#guard shadowedObject.map (fun o => o.open.isOk && o.services.isOk) = some true

def shadowedBuilt : Option Api.Built := shadowedObject.bind fun o =>
  ((session o "TodoApp").toOption).bind fun so => so.open.toOption
#guard shadowedBuilt.isSome

def oneList : List Val := [.list [.str "list", .unit]]
def ordinaryReply : Option (List Val) := todoSessionBuilt.map fun b =>
  (sessionRun b oneList stocked).2.1.2.map (·.2)
def shadowedReply : Option (List Val) := shadowedBuilt.map fun b =>
  (sessionRun b oneList stocked).2.1.2.map (·.2)
#guard ordinaryReply = some [reifyExitVal (.success (.list
  [Test.Dogfood.Scenario.Todo.todo 1 "milk" false]))]
#guard shadowedReply = some [reifyExitVal (.success (.list []))]
#guard ordinaryReply != shadowedReply

/-! A checked construction uses the existing service positions throughout.
It creates no stored method representation. Refusals remain strings in this probe only.
The production interface must retain the original located admission refusal. -/
open Effect4.Program.Authoring

def invokeAt (k : Nat) (args : List TermSrc) : Src NativeOp :=
  perform (.call k) (requestOf args)

def dispatchAt (state : TermSrc) (replyBase : Nat) :
    List (String × Nat × Nat) → TermSrc → Src NativeOp
  | [], _ => succeed (bool false)
  | (name, k, arity) :: rest, req =>
    selectTagWith req name
      (fun payload =>
        bindWith (exit (invokeAt k (if arity == 0 then [state] else [state, payload])))
          fun ex => andThen (perform (.external replyBase) ex) (succeed (bool true)))
      (fun residual => dispatchAt state (replyBase + 1) rest residual)

def mainAt (keys : List ServiceKey) (init next : Nat)
    (methods : List (String × Nat × Nat)) : Src NativeOp :=
  keys.foldr (fun k body => provideService k unit body)
    (bindWith (invokeAt init []) fun state =>
      loopWith (bool true) (fun c => c)
        (fun _ => bindWith (perform (.external next) unit) fun r =>
          selectOptionWith r (succeed (bool false))
            (fun req => dispatchAt state (next + 1) methods req))
        (fun _ a => a) (fun _ => unit))

-- Both input and output pass the existing checker. No second checker is introduced.
def checkedSession (o : Object) (service : String) : Except String Api.Built := do
  let _ ← o.open.mapError fun _ => "source admission"
  let ss ← o.services.mapError fun _ => "service formation"
  let some s := ss.find? (·.name == service) | throw "missing service"
  let some initD := o.program.defsOf[s.init]? | throw "missing initial program"
  let some ms := methodsOf o s initD.answer | throw "method arguments"
  let keys := initD.requires
  if !(keys.all fun k => o.app.serviceTy k == some .unit) then throw "unit provision profile"
  let rows := o.app.rows ++ [nextRow ms] ++ ms.map replyRow
  match o.program with
  | .defs decls bodies _ layers =>
    let main ← (mainAt keys s.init o.app.rows.length s.methods {} [1]).mapError
      fun _ => "main elaboration"
    let result : Object :=
      { app := { o.app with rows := rows }
        program := .defs decls bodies main layers }
    let b ← result.open.mapError fun _ => "result admission"
    if !b.requires.isEmpty then throw "open service requirements"
    return b
  | _ => throw "no definition block"

#guard todoObject.map (fun o => (checkedSession o "TodoApp").isOk) = some true
#guard cachedObject.map (fun o => (checkedSession o "TodoApp").isOk) = some true
#guard collisionObject.map (fun o => (checkedSession o "TodoApp").isOk) = some false
#guard (shadowedObject.bind fun o => (checkedSession o "TodoApp").toOption).map
  (fun b => (sessionRun b oneList stocked).2.1.2.map (·.2)) = ordinaryReply
-- The positional construction produces the same program data on the original applications.
#guard (todoObject.bind fun o => (checkedSession o "TodoApp").toOption).map
  Object.ofBuilt = todoSession
#guard (cachedObject.bind fun o => (checkedSession o "TodoApp").toOption).map
  Object.ofBuilt = cachedSession

end Refinement.Session

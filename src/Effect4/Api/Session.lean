import Effect4.Api.Object
import Effect4.Program.Authoring.Named

/-!
# Api.Session — a checked service lifetime as an ordinary program

`Built.session` selects a service from an admitted block. It derives request and reply rows,
constructs the lifetime through existing authoring forms, and admits the result once.
Definition and external calls retain positions throughout construction.
The source bodies, declarations, module layers and signature declarations stay unchanged.
The main program initializes once and handles requests sequentially until input ends.

This is a checked protocol adaptation. It adds no program syntax, host implementation or
reply checker. The existing session protocol admits host replies at their call instances.
The result's requirement row is closed. Unsupported provisions and transport columns retain
program admission's located refusals. Host progress and physical I/O remain outside this API.
-/

set_option autoImplicit false
namespace Effect4.Api
open Effect4.Program Effect4.Program.Authoring

/-- Why a selected service cannot become a closed session program.
Existing owners retain their paths and reasons. Selection names the missing service;
`requirements` locates the remaining keys at the new main program. -/
inductive SessionRefusal where
  | service (why : PrintRefusal)
  | missingService (name : String)
  | scope (why : Authoring.Refusal)
  | admission (why : AdmitRefusal)
  | requirements (path : List Nat) (keys : List Effect4.ServiceKey)
deriving DecidableEq

namespace ServiceSession

/-- The right-associated sum of tagged requests, with no redundant final empty alternative. -/
def requestSum : List Ty → Ty
  | [] => .never
  | [t] => t
  | t :: ts => .union t (requestSum ts)

/-- Derive a method's tagged request and reply row from its declaration at the recorded position.
This pair is a temporary view, not stored program syntax. -/
def methodPort (decls : List DefDecl) (service : Service) (state : Ty)
    (method : String × Nat × Nat) : Except PrintRefusal (Ty × Program.Row) := do
  let (name, position, arity) := method
  let some d := decls[position]? | throw (.serviceMethod service.name name)
  let some args := methodArgs state d arity | throw (.serviceMethod service.name name)
  return (.prod (.lit name) (requestTy args),
    (Row.host ("Session.reply_" ++ name) (.exitOf d.answer d.error) .unit).row)

/-- The request row followed by reply rows in the selected service's method order. -/
def rows (decls : List DefDecl) (service : Service) (state : Ty) :
    Except PrintRefusal RowTable := do
  let ports ← service.methods.mapM (methodPort decls service state)
  return (Row.host "Session.next" .unit (.option (requestSum (ports.map (·.1))))).row ::
    ports.map (·.2)

/-- Invoke the definition position directly. No definition name is resolved again. -/
def invokeAt (position : Nat) (args : List TermSrc) : Src NativeOp :=
  perform (.call position) (Authoring.requestOf args)

/-- Select a method by its request tag, invoke its position, and send its exit to its reply row. -/
def dispatch (state : TermSrc) (reply : Nat) :
    List (String × Nat × Nat) → TermSrc → Src NativeOp
  | [], _ => succeed (bool false)
  | (name, position, arity) :: rest, request =>
    selectTagWith request name
      (fun payload =>
        bindWith (exit (invokeAt position (if arity == 0 then [state] else [state, payload])))
          fun answer => andThen (perform (.external reply) answer) (succeed (bool true)))
      (fun residual => dispatch state (reply + 1) rest residual)

/-- Provide the initializer's keys, initialize once, then receive, dispatch and reply in a loop.
Program admission checks every unit provision against its declared carrier. -/
def main (keys : List Effect4.ServiceKey) (init next : Nat)
    (methods : List (String × Nat × Nat)) : Src NativeOp :=
  keys.foldr (fun key body => provideService key unit body)
    (bindWith (invokeAt init []) fun state =>
      loopWith (bool true) (fun cursor => cursor)
        (fun _ => bindWith (perform (.external next) unit) fun request =>
          selectOptionWith request (succeed (bool false))
            (fun payload => dispatch state (next + 1) methods payload))
        (fun _ answer => answer) (fun _ => unit))

/-- Construct the candidate object. Only `Built.session` returns it with admission evidence.
This helper uses the existing service view and block projection, never a program traversal. -/
def candidate (b : Built) (name : String) : Except SessionRefusal Object := do
  let object := Object.ofBuilt b
  let services ← object.services.mapError .service
  let some service := services.find? (·.name == name) | throw (.missingService name)
  let some (decls, bodies, _, layers) := b.program.block? | throw (.missingService name)
  let some init := decls[service.init]? | throw (.service (.service name))
  let appended ← (rows decls service init.answer).mapError .service
  let program ← (main init.requires service.init b.table.length service.methods {} [1]).mapError .scope
  return { app := { b.app with rows := b.table ++ appended }
           program := .defs decls bodies program layers }

/-- Admit a candidate through its existing owner, then require a closed requirement row. -/
def finish (object : Object) : Except SessionRefusal Built := do
  let built ← object.open.mapError .admission
  if built.requires.isEmpty then return built
  else throw (.requirements [1] built.requires)

end ServiceSession

/-- Build a service lifetime from an admitted program and its selected service name.
Request and reply rows append to the signature. The source definitions and layers keep their
positions. The result passes full program admission and has no unprovided service requirements.
The constructor performs no host work and makes no claim of termination. -/
def Built.session (b : Built) (service : String) : Except SessionRefusal Built :=
  (ServiceSession.candidate b service).bind ServiceSession.finish

end Effect4.Api

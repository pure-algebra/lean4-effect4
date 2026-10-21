import Effect4.Api.Object
import Effect4.Program.Authoring.Named

/-!
# Api.Session — a service's lifetime as one program, built from the object

`Object.session` is data to data. It selects a service of the object, derives the protocol rows,
writes the lifetime as the object's new main program, and appends the rows. The block's
declarations, bodies, module layers, named types and service declarations are the object's own,
in place. The lifetime provides every key the initializer and the methods require with the
unit, initializes once, then receives, dispatches and replies until the input ends.

`Built.session` is that construction followed by program admission at the new signature, with
the requirement row required closed. Definitions and rows are invoked by position throughout,
so no name is resolved after the service view read it.

This is a checked protocol adaptation. It adds no program syntax, host implementation or reply
checker: the session protocol admits a host's replies at their call instances, as for any row.
Target printing, transport support, host progress and physical I/O stay outside this module.
-/

set_option autoImplicit false
namespace Effect4.Api
open Effect4.Program Effect4.Program.Authoring

/-- Why a selected service has no session. Each owner keeps its path and reason. Selection
names the missing service; `requirements` locates the keys left open at the new main program. -/
inductive SessionRefusal where
  | service (why : PrintRefusal)
  | missingService (name : String)
  | scope (why : Authoring.Refusal)
  | admission (why : AdmitRefusal)
  | requirements (path : List Nat) (keys : List Effect4.ServiceKey)
deriving DecidableEq

namespace ServiceSession

/-- The sum of a list of types, with `never` as its unit: the dual of `requestTy`. -/
def sumTy : List Ty → Ty
  | [] => .never
  | [t] => t
  | t :: ts => .union t (sumTy ts)

/-- A method's part of the protocol: its tagged request type, and its reply row at its exit
type, read off its declaration at the recorded position. A view, never stored. -/
def methodPort (decls : List DefDecl) (service : Service) (state : Ty)
    (method : String × Nat × Nat) : Except PrintRefusal (Ty × Program.Row) := do
  let (name, position, arity) := method
  let some d := decls[position]? | throw (.serviceMethod service.name name)
  let some args := methodArgs state d arity | throw (.serviceMethod service.name name)
  return (.prod (.lit name) (requestTy args),
    (Row.host ("Session.reply_" ++ name) (.exitOf d.answer d.error) .unit).row)

/-- The protocol rows: `Session.next`, whose answer is the next tagged request or none, then
one reply row a method, in the service's method order. -/
def rows (decls : List DefDecl) (service : Service) (state : Ty) :
    Except PrintRefusal RowTable := do
  let ports ← service.methods.mapM (methodPort decls service state)
  return (Row.host "Session.next" .unit (.option (sumTy (ports.map (·.1))))).row ::
    ports.map (·.2)

/-- The keys the lifetime provides: those the initializer and the methods require, each once. -/
def keysOf (decls : List DefDecl) (init : DefDecl) (service : Service) : List Effect4.ServiceKey :=
  (init.requires ++
    (service.methods.filterMap fun (_, position, _) => decls[position]?).flatMap (·.requires)).eraseDups

/-- Invoke the definition at a position. No name is resolved. -/
def invokeAt (position : Nat) (args : List TermSrc) : Src NativeOp :=
  perform (.call position) (Authoring.requestOf args)

/-- Dispatch a request by its tag. Each method comes paired with its reply row's position:
invoke the method's position on the state and the payload, send its exit to its reply row,
and answer `true` to continue. -/
def dispatch (state : TermSrc) : List ((String × Nat × Nat) × Nat) → TermSrc → Src NativeOp
  | [], _ => succeed (bool false)
  | ((name, position, arity), reply) :: rest, request =>
    selectTagWith request name
      (fun payload =>
        bindWith (exit (invokeAt position (if arity == 0 then [state] else [state, payload])))
          fun answer => andThen (perform (.external reply) answer) (succeed (bool true)))
      (fun residual => dispatch state rest residual)

/-- The lifetime: provide each key with the unit, initialize once, then receive from
`Session.next` at position `next`, dispatch, and reply, until no request comes. The reply rows
follow `next` in method order, so method `k` replies at `next + 1 + k`. Program admission checks
each unit provision against the key's declared carrier. -/
def main (keys : List Effect4.ServiceKey) (init next : Nat)
    (methods : List (String × Nat × Nat)) : Src NativeOp :=
  keys.foldr (fun key body => provideService key unit body)
    (bindWith (invokeAt init []) fun state =>
      loopWith (bool true) (fun cursor => cursor)
        (fun _ => bindWith (perform (.external next) unit) fun request =>
          selectOptionWith request (succeed (bool false))
            (fun payload =>
              dispatch state (methods.zipIdx.map fun (m, k) => (m, next + 1 + k)) payload))
        (fun _ answer => answer) (fun _ => unit))

/-- Admit a session object at its signature, then require its requirement row closed. -/
def finish (object : Object) : Except SessionRefusal Built := do
  let built ← object.open.mapError .admission
  if built.requires.isEmpty then return built
  else throw (.requirements [1] built.requires)

end ServiceSession

/-- **The session object of a service**: the object's block with the lifetime as its main
program and the protocol rows appended after the object's rows. Data to data: the service view
checks formation, and admission is `Built.session`'s. -/
def _root_.Effect4.Program.Object.session (o : Object) (name : String) :
    Except SessionRefusal Object := do
  let services ← o.services.mapError .service
  let some service := services.find? (·.name == name) | throw (.missingService name)
  let some (decls, bodies, _, layers) := o.program.block? | throw (.missingService name)
  let some init := decls[service.init]? | throw (.service (.service name))
  let appended ← (ServiceSession.rows decls service init.answer).mapError .service
  let program ← (ServiceSession.main (ServiceSession.keysOf decls init service) service.init
    o.app.rows.length service.methods {} [1]).mapError .scope
  return { app := { o.app with rows := o.app.rows ++ appended }
           program := .defs decls bodies program layers }

/-- **A service's lifetime, admitted**: the session object of the service, opened at its new
signature, with no requirement left open. The source's definitions and rows keep their
positions. The constructor performs no host work and claims no termination. -/
def Built.session (b : Built) (service : String) : Except SessionRefusal Built :=
  (Object.session (Object.ofBuilt b) service).bind ServiceSession.finish

end Effect4.Api

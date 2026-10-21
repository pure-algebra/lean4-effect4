import Effect4.Api.Object
import Effect4.Program.Authoring.Named

/-!
# Api.Session — a service's lifetime as one program, built from the object

`Object.session` is data to data. It selects a service of the object, derives the protocol rows,
writes the lifetime as the object's new main program, and appends the rows. The block's
declarations, bodies, module layers, named types and service declarations are the object's own,
in place. The lifetime initializes once, then receives, dispatches and replies until the input
ends. It provides nothing: the services it requires are the signature's, which the host
supplies at every target (the repository layer on Effect, the rows' answers on the machine).

`Built.session` is that construction followed by program admission at the new signature, with
the requirement row closed modulo the signature: every key left is one the signature types
(`SigApp.serviceTy`). Definitions and rows are invoked by position throughout, so no name is
resolved after the service view read it.

This is a checked protocol adaptation. It adds no program syntax, host implementation or reply
checker: the session protocol admits a host's replies at their call instances, as for any row.
Target printing, transport support, host progress and physical I/O stay outside this module.
-/

set_option autoImplicit false
namespace Effect4.Api
open Effect4.Program Effect4.Program.Authoring

/-- Why a selected service has no session. Each owner keeps its path and reason. Selection
names the missing service; `requirements` locates, at the new main program, the required keys
that the signature does not type, which no host could supply. -/
inductive SessionRefusal where
  | service (why : PrintRefusal)
  | missingService (name : String)
  | scope (why : Authoring.Refusal)
  | admission (why : AdmitRefusal)
  | requirements (path : List Nat) (keys : List Effect4.ServiceKey)
deriving DecidableEq

namespace ServiceSession

/-- The request row's spelling, shared by construction and reactors. -/
def nextName : String := "Session.next"

/-- The reply rows' prefix, shared by construction and reactors. -/
def replyPrefix : String := "Session.reply_"

/-- Whether a row uses the session reply prefix. Admission checks its actual columns.
The byte-list operation keeps prefix recognition within the core's axiom ceiling. -/
def isReplyRow (row : Program.Row) : Bool :=
  replyPrefix.toUTF8.data.toList.isPrefixOf row.spelling.toUTF8.data.toList

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
    (Row.host (replyPrefix ++ name) (.exitOf d.answer d.error) .unit).row)

/-- The protocol rows: `Session.next`, whose answer is the next tagged request or none, then
one reply row a method, in the service's method order. -/
def rows (decls : List DefDecl) (service : Service) (state : Ty) :
    Except PrintRefusal RowTable := do
  let ports ← service.methods.mapM (methodPort decls service state)
  return (Row.host nextName .unit (.option (sumTy (ports.map (·.1))))).row ::
    ports.map (·.2)

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

/-- The lifetime: initialize once, then receive from `Session.next` at position `next`,
dispatch, and reply, until no request comes. The reply rows follow `next` in method order, so
method `k` replies at `next + 1 + k`. The initializer's requirements are the lifetime's: the
host's services, left for the host. -/
def main (init next : Nat) (methods : List (String × Nat × Nat)) : Src NativeOp :=
  bindWith (invokeAt init []) fun state =>
    loopWith (bool true) (fun cursor => cursor)
      (fun _ => bindWith (perform (.external next) unit) fun request =>
        selectOptionWith request (succeed (bool false))
          (fun payload =>
            dispatch state (methods.zipIdx.map fun (m, k) => (m, next + 1 + k)) payload))
      (fun _ answer => answer) (fun _ => unit)

/-- The required keys the signature does not type: the ones no host could supply. -/
def foreign (built : Built) : List Effect4.ServiceKey :=
  built.requires.filter fun key => (built.app.serviceTy key).isNone

/-- Admit a session object at its signature, then require its requirement row closed modulo the
signature: every key left is one the signature types, so the host supplies it. -/
def finish (object : Object) : Except SessionRefusal Built := do
  let built ← object.open.mapError .admission
  if (foreign built).isEmpty then return built
  else throw (.requirements [1] (foreign built))

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
  let program ← (ServiceSession.main service.init o.app.rows.length service.methods {} [1]).mapError
    .scope
  return { app := { o.app with rows := o.app.rows ++ appended }
           program := .defs decls bodies program layers }

/-- **A service's lifetime, admitted**: the session object of the service, opened at its new
signature, every requirement left a key the signature types. The source's definitions and rows
keep their positions. The constructor performs no host work and claims no termination. -/
def Built.session (b : Built) (service : String) : Except SessionRefusal Built :=
  (Object.session (Object.ofBuilt b) service).bind ServiceSession.finish

end Effect4.Api

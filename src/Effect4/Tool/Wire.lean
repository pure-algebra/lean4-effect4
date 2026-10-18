import Effect4.Tool.ToolDerived
import Effect4.Tool.Serve

/-!
# Tool.Wire — the wire core around `Tool.serve`

`serveEnvelope` is the one wire core every driver calls: it checks a read envelope against the
connection (`check`), calls `Tool.serve` once, and frames the reply under the request's method and
version. Each driver owns only its ends: the JSON driver reads and writes through the JSON profile
(`serveJson`, `CodecProfile`), and the native shell through value trees (`Tool/Native.lean`). It
holds no action interpreter: every state change is `serve`'s.

A wire refusal is the transport's (`Wire.Refusal`): the driver then keeps the state it was given,
so a request the tool never saw, or a reply the profile cannot print, records nothing.

`responds` states how a reply pairs with its request. It is the statement of `serve_answers`
(`Laws/Tool/Wire.lean`), which proves every reply `serve` gives pairs; no driver re-checks it.
-/

set_option autoImplicit false
namespace Effect4.Tool.Wire
open Effect4.Store Effect4.Program.Check

/-- **An action's answer pairs with the action**: the same kind, and the played run's identity. -/
def actionPairs : Action → ActionAnswer → Bool
  | .open_ .., .opened .. => true
  | .edit .., .edited .. => true
  | .fill .., .filled .. => true
  | .publish .., .published .. => true
  | .reset, .reset .. => true
  | .start .., .started .. => true
  | .restore .., .restored .. => true
  | .play id _, .played id' .. => id.n == id'.n
  | _, _ => false

/-- **A preview's answer pairs with its query.** -/
def previewPairs : PreviewQuery → PreviewAnswer → Bool
  | .settle .., .settled .. => true
  | .frames .., .frames .. => true
  | .explore .., .explored .. => true
  | _, _ => false

/-- **A run query's answer pairs with it**: the same run, in the requested form. -/
def runPairs (id : RunId) (form : RunForm) (id' : RunId) (answer : RunAnswer) : Bool :=
  id.n == id'.n &&
    match form, answer with
    | .view, .view .. => true
    | .record, .record .. => true
    | .journal, .journal .. => true
    | _, _ => false

/-- **A query's answer pairs with the query.** A dry run's answer pairs as its action's would. -/
def queryPairs : Query → Answer → Bool
  | .doc .., .doc .. => true
  | .history, .history .. => true
  | .fills, .fills .. => true
  | .suggest .., .suggested .. => true
  | .run id form, .run id' answer => runPairs id form id' answer
  | .preview q, .preview answer => previewPairs q answer
  | .dry a, .dry (.ok answer) => actionPairs a answer
  | .dry _, .dry (.error _) => true
  | .discover, .methods .. => true
  | .table, .table .. => true
  | .addresses, .addresses .. => true
  | .slots path _, .slots path' .. => decide (path = path')
  | _, _ => false

/-- **The reply answers the request**: a refusal answers any request; an answer pairs with it. -/
def responds (request : Request) (reply : Reply) : Bool :=
  match reply.result, request with
  | .error _, _ => true
  | .ok (.acted answer), .act a => actionPairs a answer
  | .ok _, .act _ => false
  | .ok answer, .ask q => queryPairs q answer

/-- **Check a read envelope** against the connection: a valid connection, the payload's own method,
selected at a supported version, and that version. The wire core (`serveEnvelope`) calls it. -/
def check (connection : Connection) (envelope : Envelope Request) : Except Refusal (Envelope Request) := do
  if !connection.valid then throw .connection
  let actual := envelope.payload.method
  if envelope.method != actual then throw (.method envelope.method actual)
  match connection.selected.lookup actual with
  | none => throw (.unselected actual)
  | some selected =>
    if !(((supportedMethods.lookup actual).getD []).contains selected) then throw (.unselected actual)
    if envelope.version != selected then throw (.version actual selected envelope.version)
    pure envelope

/-- **Decode a request** through the JSON profile and check it against the connection. -/
def decode (connection : Connection) (json : Effect4.Json) : Except Refusal (Envelope Request) := do
  let envelope ← (CodecProfile.read (α := Envelope Request) json).mapError Refusal.codec
  check connection envelope

/-- **Serve one envelope**: check it against the connection, serve its request once, and frame the
reply under the request's method and version. A refusal here runs no check and changes nothing. -/
def serveEnvelope (oracle : Oracle) (connection : Connection) (state : State)
    (envelope : Envelope Request) : Checked (Except Refusal (State × Envelope Reply)) :=
  match check connection envelope with
  | .error why => pure (.error why)
  | .ok envelope => do
    let (next, reply) ← serve oracle state envelope.payload
    pure (.ok (next, ⟨envelope.method, envelope.version, reply⟩))

/-- **Serve one JSON request** through the wire core. The driver publishes the next state only
after the reply passes the JSON write guard. -/
def serveJson (oracle : Oracle) (connection : Connection) (state : State) (json : Effect4.Json) :
    Checked (State × Except Refusal Effect4.Json) :=
  match CodecProfile.read (α := Envelope Request) json with
  | .error why => pure (state, .error (.codec why))
  | .ok envelope => do
    match ← serveEnvelope oracle connection state envelope with
    | .error why => pure (state, .error why)
    | .ok (next, reply) =>
      match CodecProfile.write reply with
      | .error why => pure (state, .error (.codec why))
      | .ok json => pure (next, .ok json)

end Effect4.Tool.Wire

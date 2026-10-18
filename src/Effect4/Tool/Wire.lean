import Effect4.Tool.ToolDerived
import Effect4.Tool.Serve

/-!
# Tool.Wire — the JSON adapter around `Tool.serve`

A driver hands the adapter one JSON value and gets back the next state and a JSON reply. The
adapter decodes an `Envelope Request` through the JSON profile (`CodecProfile.read`), checks the
connection's selected version for the method, calls `Tool.serve` once, checks that the answer
pairs with the request (`responds`), and encodes the `Envelope Reply` (`CodecProfile.write`). It
holds no action interpreter: every state change is `serve`'s.

A wire refusal is the transport's (`Wire.Refusal`): the adapter then returns the state it was
given, so a request the tool never saw, or a reply the profile cannot print, records nothing.

The pairing is one exhaustive match: a new request or answer constructor fails to compile here
until its pair is written, so the pairing cannot drift from the protocol.
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
selected at a supported version, and that version. The JSON adapter (`decode`) and the native
shell (`Tool/Native.lean`) both call it. -/
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

/-- **Decode a request** at the connection's chosen method version, before calling the tool. -/
def decode (connection : Connection) (json : Effect4.Json) : Except Refusal (Envelope Request) := do
  if !connection.valid then throw .connection
  let envelope ← (CodecProfile.read (α := Envelope Request) json).mapError Refusal.codec
  check connection envelope

/-- **Serve one JSON request.** The adapter publishes its next pure state only after the reply
pairs with the request and passes the JSON write guard. -/
def serveJson (oracle : Oracle) (connection : Connection) (state : State) (json : Effect4.Json) :
    Checked (State × Except Refusal Effect4.Json) := do
  match decode connection json with
  | .error why => pure (state, .error why)
  | .ok envelope =>
    let (next, answer) ← serve oracle state envelope.payload
    if !responds envelope.payload answer then pure (state, .error .response)
    else
      match CodecProfile.write (⟨envelope.method, envelope.version, answer⟩ : Envelope Reply) with
      | .error why => pure (state, .error (.codec why))
      | .ok json => pure (next, .ok json)

end Effect4.Tool.Wire

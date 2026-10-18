import Effect4.Tool.Exchange
import Effect4.Tool.ToolDerived
import Effect4.Tool.Wire

/-!
# Tool.Native — the tool at the native boundary (seams S6)

The native shell (`ocaml/engine/kit/kit_tool.ml`) serves the generated `Tool.serve`, not a copy of
it. This module is the boundary it is generated from (`ocaml/gen/roots.json`, the `api_gen`
artefact): requests and replies cross as canonical value trees, so the shell's one JSON reader and
printer (`Kit_json`, driven by each carrier's shape) does the text, and the semantics stays here.

- `requestShape` and `replyShape` give the shell each carrier's shape document.
- `requestOfVal` reads a request through the Tool group's exact codec; `replyToVal` writes a reply.
- `serveVal` serves one request through a memo and learns the reply's checked trace. The memo
  changes cost, never an answer (`serve_transparent`), so the cached and uncached transcripts are
  equal; the shell's controls compare them.

JSON parsing, method-version selection, framing and IO stay in the shell, outside the state.
-/

set_option autoImplicit false

namespace Effect4.Tool.Native

open Effect4 Effect4.Store Effect4.Program.Check

/-- The shape document of a request, for the shell's JSON reader. -/
def requestShape : ShapeDoc := shape Request

/-- The shape document of a reply, for the shell's JSON printer. -/
def replyShape : ShapeDoc := shape Reply

/-- A request from its value tree, through the exact codec. -/
def requestOfVal (v : Val) : Option Request := Canonical.ofVal v

/-- A reply's value tree. -/
def replyToVal (r : Reply) : Val := Canonical.toVal r

/-- The memo's hit rule: an exact key, or a part key whose row table extends the stored one. -/
def rule : HitRule := HitRule.exact.or extension

/-- The empty tool state and an empty memo: where a native session starts. -/
def start : State × Memo := (empty, Memo.empty)

/-- **Serve one request** through the memo: the next state, the reply, and the memo that learned
the reply's trace. -/
def serveVal (st : State × Memo) (request : Request) : (State × Reply) × Memo :=
  let served := serve (st.2.oracle rule) st.1 request
  (served.value, st.2.learn served)

/-- **Serve one request uncached**: the control the cached transcript is compared with. -/
def serveUncached (s : State) (request : Request) : State × Reply :=
  (serve Oracle.uncached s request).value

/-- The shape document of a request envelope, for the shell's JSON reader. -/
def envelopeShape : ShapeDoc := shape (Wire.Envelope Request)

/-- The shape document of a reply envelope, for the shell's JSON printer. -/
def replyEnvelopeShape : ShapeDoc := shape (Wire.Envelope Reply)

/-- The shape document of a wire refusal. -/
def refusalShape : ShapeDoc := shape Wire.Refusal

/-- A wire refusal's value tree. -/
def refusalToVal (why : Wire.Refusal) : Val := Canonical.toVal why

/-- **Serve one envelope**, as `Wire.serveJson` does at the value boundary: read it through the exact
codec, check it against the version-1 connection (`Wire.check`), serve its request through the
memo, and refuse a reply that does not pair with it. A refusal leaves the state as it was. -/
def serveEnvelope (st : State × Memo) (v : Val) : Except Wire.Refusal (Val × (State × Memo)) :=
  match Canonical.ofVal (α := Wire.Envelope Request) v with
  | none => .error (.codec .unreadable)
  | some envelope =>
    match Wire.check Wire.Connection.v1 envelope with
    | .error why => .error why
    | .ok envelope =>
      let ((next, reply), memo) := serveVal st envelope.payload
      if !Wire.responds envelope.payload reply then .error .response
      else .ok (Canonical.toVal (⟨envelope.method, envelope.version, reply⟩ : Wire.Envelope Reply),
        (next, memo))

end Effect4.Tool.Native

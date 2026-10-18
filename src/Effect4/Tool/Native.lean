import Effect4.Tool.ToolDerived
import Effect4.Tool.Wire

/-!
# Tool.Native — the tool at the native boundary

The native shell (`ocaml/engine/kit/kit_tool.ml`) serves the generated wire core, not a copy of
it. This module is what it is generated from (`ocaml/gen/roots.json`, the `api_gen` artefact).

- A `Session` holds the tool state and the checker memo. The generated interface keeps it abstract
  (`roots.json`, `abstract`), so only `start` and `serve` build one: a native caller cannot forge
  a state or a memo.
- Envelopes cross as canonical value trees. The shell's one JSON reader and printer (`Kit_json`,
  driven by each carrier's shape) does the text; the semantics is `Wire.serveEnvelope`'s.
- `serve` learns each reply's checked trace; `serveUncached` is its control. The memo changes
  cost, never an answer (`serve_transparent`), so the shell's controls compare the two.

JSON parsing, framing and IO stay in the shell.
-/

set_option autoImplicit false

namespace Effect4.Tool.Native

open Effect4 Effect4.Store Effect4.Program.Check

/-- **A native session**: the tool state and the checker memo, abstract in OCaml. -/
structure Session where
  state : State
  memo : Memo

/-- The memo's hit rule: an exact key, or a part key whose row table extends the stored one. -/
def rule : HitRule := HitRule.exact.or extension

/-- Where a native session starts: no action accepted, an empty memo. -/
def start : Session := ⟨empty, Memo.empty⟩

/-- **One envelope's value tree through the wire core**, at an oracle: read it through the exact
codec, serve it at the version-1 connection, and write the reply envelope's tree. -/
def answer (o : Oracle) (state : State) (v : Val) : Checked (Except Wire.Refusal (Val × State)) :=
  match Canonical.ofVal (α := Wire.Envelope Request) v with
  | none => pure (.error (.codec .unreadable))
  | some envelope => do
    match ← Wire.serveEnvelope o Wire.Connection.v1 state envelope with
    | .error why => pure (.error why)
    | .ok (next, reply) => pure (.ok (Canonical.toVal reply, next))

/-- **Serve one envelope** through the memo, and learn the reply's trace. A refusal leaves the
session as it was. -/
def serve (session : Session) (v : Val) : Except Wire.Refusal (Val × Session) :=
  let served := answer (session.memo.oracle rule) session.state v
  served.value.map fun (reply, next) => (reply, ⟨next, session.memo.learn served⟩)

/-- **Serve one envelope uncached**: the control the cached transcript is compared with. -/
def serveUncached (session : Session) (v : Val) : Except Wire.Refusal (Val × Session) :=
  (answer Oracle.uncached session.state v).value.map fun (reply, next) =>
    (reply, {session with state := next})

/-- The shape document of a request envelope, for the shell's JSON reader. -/
def envelopeShape : ShapeDoc := shape (Wire.Envelope Request)

/-- The shape document of a reply envelope, for the shell's JSON printer. -/
def replyEnvelopeShape : ShapeDoc := shape (Wire.Envelope Reply)

/-- The shape document of a wire refusal. -/
def refusalShape : ShapeDoc := shape Wire.Refusal

/-- A wire refusal's value tree. -/
def refusalToVal (why : Wire.Refusal) : Val := Canonical.toVal why

end Effect4.Tool.Native

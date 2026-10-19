import Effect4.Tool.ToolDerived
import Effect4.Tool.Wire
import Effect4.Tool.Methods

/-!
# Tool.Native — the tool at the native boundary

The native shell (`ocaml/engine/kit/kit_tool.ml`) serves the generated wire core, not a copy of
it. This module is what it is generated from (`ocaml/gen/roots.json`, the `api_gen` artefact).

- A `Session` holds the tool state and the checker memo. The generated interface keeps it abstract
  (`roots.json`, `abstract`), so only `start` and `serve` build one: a native caller cannot forge
  a state or a memo.
- Envelopes cross as canonical value trees, or as the profile's JSON tree (`serveTree`). The
  shell parses the text into the tree and renders the tree as text (`NatJson.render`); reading the
  tree under the envelope's shape, with a located refusal, and printing the reply are Lean's
  (`Store/Domain/ShapeJson.lean`). The semantics is `Wire.serveEnvelope`'s.
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
codec within the JSON profile's naturals (`CodecProfile.carries`), serve it at the version-1
connection, and write the reply envelope's tree, refusing one the profile cannot carry. These are
the JSON driver's refusals (`CodecProfile.read`, `CodecProfile.write`), so both drivers keep the
same state. A value tree has no JSON place finer than its root, so its refusals are located
there. -/
def answer (o : Oracle) (state : State) (v : Val) : Checked (Except Wire.Refusal (Val × State)) :=
  match Canonical.ofVal (α := Wire.Envelope Request) v with
  | none => pure (.error (.codec (.unreadable ⟨.value [], .carrierValue⟩)))
  | some envelope =>
    if !CodecProfile.carries v then
      pure (.error (.codec (.unreadable ⟨.value [], .naturalOutsideProfile CodecProfile.natLimit⟩)))
    else do
    match ← Wire.serveEnvelope o Wire.Connection.v1 state envelope with
    | .error why => pure (.error why)
    | .ok (next, reply) =>
      let out := Canonical.toVal reply
      if CodecProfile.carries out then pure (.ok (out, next))
      else pure (.error (.codec .unprintable))

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

/-- **One request's JSON tree through the session**: read under the request envelope's shape by
the profile's located reader, served (`serve`), and the reply envelope printed as the tools print
it (`ShapeDoc.printTree`). A tree that does not read is the codec's refusal at its place, and the
session stays as it was. -/
def serveTree (session : Session) (t : NatJson) : Except Wire.Refusal (NatJson × Session) :=
  match envelopeShape.readLocated t with
  | .error why => .error (.codec (.unreadable why))
  | .ok v => (serve session v).map fun (reply, next) => (replyEnvelopeShape.printTree reply, next)

/-- A wire refusal as the profile's JSON tree, as the tools print it. -/
def refusalTree (why : Wire.Refusal) : NatJson := refusalShape.printTree (refusalToVal why)

/-- **A refusal relative to a part of the request**: a shell that writes a request around a part
the agent wrote (the MCP server writes a tool's arguments at `payload.<field>`) places the codec's
refusal in that part by removing the part's path from the site. Any other refusal is unchanged. -/
def relativeRefusal (base : List JsonStep) : Wire.Refusal → Wire.Refusal
  | .codec (.unreadable why) => .codec (.unreadable (why.mapSite (JsonSite.relative base)))
  | other => other

/-- The tool table an MCP server lists (`Tool/Methods.lean`). -/
def methods : List Methods.Entry := Methods.entries

/-- The `describe` tool an MCP server lists beside the methods, and its answers: the schemas the
methods' schemas leave to it (`Tool/Methods.lean`). -/
def describe : Methods.Describe := Methods.describe

end Effect4.Tool.Native

import Effect4.Tool.Wire
import Tools.JsonBridge

/-!
# Tools.WireText — the tool's wire as text lines

The drivers read and write the tool's JSON one line at a time. This module moves a line between
text and the tree's JSON (`Tools.JsonBridge`), and reads a request envelope through the tool's
JSON profile (`Tool.CodecProfile.read`). A request line is an `Envelope Request` in the Tool
group's generated JSON (`Tool/ToolDerived.lean`).
-/

namespace Tools.WireText

open Effect4.Tool

/-- **A line as the tree's JSON**, or why it does not read. -/
def parseTree (text : String) : Except String Effect4.Json := do
  let j ← Lean.Json.parse text
  match Tools.JsonBridge.ofLeanJson Tools.JsonBridge.depth j with
  | some tree => pure tree
  | none => throw "not tree JSON: a number that binary64 rounds, or nesting past the depth"

/-- **A line as a request envelope**, through the tool's JSON profile. -/
def readEnvelope (text : String) : Except String (Wire.Envelope Request) := do
  let tree ← parseTree text
  match CodecProfile.read (α := Wire.Envelope Request) tree with
  | .ok envelope => pure envelope
  | .error _ => throw "not a request envelope"

/-- **A line as a request**: the envelope's payload. -/
def readRequest (text : String) : Except String Request :=
  (readEnvelope text).map (·.payload)

/-- **A request as a line**: its envelope at version 1, in the generated JSON. -/
def requestLine (request : Request) : String :=
  (Tools.JsonBridge.printJson (⟨request.method, 1, request⟩ : Wire.Envelope Request)).compress

/-- **A reply as a line**, in the generated JSON. -/
def replyLine (reply : Reply) : String :=
  (Tools.JsonBridge.printJson reply).compress

end Tools.WireText

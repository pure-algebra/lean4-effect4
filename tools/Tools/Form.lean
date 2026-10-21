/-!
# The forms of a figure's node

A node of a figure's graph is drawn in one of three forms, and the form is data of the node
(decisions row 443, the owner's review of 2026-10-21: a row and a definition must read apart).
The document holds the form, each fold draws it its own way, and the drawing kit's node carries
the same form. This module is the one vocabulary both import.

- A **box** is a thing that computes: a layer, a service block, a definition, a main program.
  It is drawn as a rectangle, and Mermaid writes it `["…"]`.
- A **wire** is a name things meet on: a service tag, a row namespace. It is drawn as a pill,
  and Mermaid writes it `(["…"])`.
- A **port** is an operation of the host boundary: a row. It is drawn as a rectangle with the
  host's post at its left, and Mermaid writes it `[["…"]]`.

In the layer hypergraph (`Tools.View.LayerGraph`), boxes are keyed by their position and never
glue, and wires are keyed by their name and glue by it: that is what the two forms show.
-/

namespace Tools

/-- The form of a figure's node: a box computes, a wire names, a port is a row of the host. -/
inductive Form where
  | box
  | wire
  | port
deriving DecidableEq, Repr, Inhabited, BEq

/-- The form's word, as the JSON fold writes it. -/
def Form.word : Form → String
  | .box => "box"
  | .wire => "wire"
  | .port => "port"

/-- The form a word names; the retraction of `Form.word`. -/
def Form.ofWord : String → Option Form
  | "box" => some .box
  | "wire" => some .wire
  | "port" => some .port
  | _ => none

theorem Form.ofWord_word (f : Form) : Form.ofWord f.word = some f := by
  cases f <;> rfl

end Tools

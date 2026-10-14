import Tools.View.Tube.Tile
import Tools.View.Tube.Glyphs
import Tools.View.Program
import Effect4.Store.Domain.ProgramWire

/-!
# Program syntax drawn with the peg vocabulary

The tile fold supplies addresses and room. The vocabulary supplies each constructor's mark.
The peg renderer supplies its geometry. These are three consumers of existing data.
The words include the non-child arguments, as the program view does.

This page shows syntax composition, not control flow or a run's state.
It introduces no value-wire relation and claims no read-back law.
-/

namespace Tools.View.Tube.TilePage

open Effect4.Program Whatwg.Html

/-- The visible word and its full syntax text, beside the vocabulary's mark. -/
structure Label where
  shape : Glyph.Shape
  word : String
  detail : String

/-- The constructor namespace of each sort in the existing program signature. -/
def family : EffFam → Lean.Name
  | .eff => ``Eff
  | .stmt => ``Stmt
  | .stmts => ``Stmts
  | .effs => ``Effs
  | .action => ``ActionTerm
  | .layer => ``LayerTerm
  | .layers => ``LayerTerms

/-- Read the existing vocabulary; never keep another constructor-to-glyph table. -/
def label (fam : EffFam) (ctor : String) (args : Tile.Header NativeOp) : Label :=
  let detail := Tools.View.Program.ownText ctor args
  match Glyph.table.find? (fun row => row.ctor == Lean.Name.str (family fam) ctor) with
  | some row => ⟨row.shape, row.word, detail⟩
  | none => ⟨.box, ctor, detail⟩

/-- Draw each cell with the peg renderer and translate it by its grid coordinates. -/
def picture (tile : Tile.Tile Label) : Except String SvgNode := do
  let cells ← tile.items.mapM fun c => do
    let glyph ← (Glyphs.pegStill c.value.shape).mapError fun i =>
      s!"peg body {i} at {Tools.View.Program.bracket c.address} has no tangent"
    pure <| Svg.g
      [.attr .transform [.translate (.ofInt (12 * c.at_.x)) (some (.ofInt (12 * c.at_.y)))]]
      [glyph,
       Svg.text 48 108 c.value.word [.className "tile-word", .attr .text_anchor "middle"],
       .element .title [] [.text c.value.detail]]
  pure <| Svg.Frame.svg { width := 12 * tile.w, height := 12 * tile.h, ratio := 1 }
    [.className "tube-view program-tiles"] cells

private def el (tag : String) (children : List RawNode)
    (attrs : List (String × String) := []) : RawNode := .element tag attrs children

/-- A program's peg picture and its addressed words come from the same fold. -/
def figure (name : String) (program : NativeEff) : RawNode :=
  let tile := Tile.ofProgram label program
  let words := tile.items.map fun c => el "li"
    [el "code" [.text (Tools.View.Program.bracket c.address)], .text (" " ++ c.value.detail)]
  let caption := el "figcaption" [el "strong" [.text name], el "ol" words]
  match picture tile with
  | .ok svg => el "figure" [svg.toRaw, caption] [("class", "tube")]
  | .error why => el "figure" [el "p" [.text why], caption] [("class", "tube")]

/-- The page's real program examples, including a fork and a continuation. -/
def blocks : List RawNode :=
  [el "p" [.text "The program's operations on a grid. Read a row from left to right. A constructor keeps its children beside it, separated by an empty row. These pictures show syntax; the run's score shows execution."],
   figure "A value" (.succeed (.lit (.nat 3))),
   figure "Bind and its continuation" (.bind (.succeed (.lit (.nat 3))) (.succeed (.var 0))),
   figure "A fork and its await" Wire.Corpus.pFork]

def css : String :=
  Tube.css ++ ".program-tiles { max-width: 100%; height: auto; }\n" ++
  ".tile-word { font: 10px monospace; fill: currentColor; }\n"

end Tools.View.Tube.TilePage

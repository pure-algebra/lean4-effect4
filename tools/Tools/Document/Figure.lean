import Tools.Document
import Tools.View.Graph
import Tools.View.SvgOut

/-!
# Tools.Document.Figure — a graph figure drawn by the view's layout (decisions row 365)

The HTML fold of a figure (`Block.graph`): the graph's nodes and edges go to the view's one layered
layout (`Tools.View.Graph.layout`, the same layout the C player's stream draws), and its drawing
calls to a typed SVG tree on `lean4-whatwg`'s kit (`Tools.View.SvgOut`). No script draws it.

* A node is a box: its label on the first line, its status word on the second, and a planned goal
  lit, so a status reads by its word and never by a colour alone.
* A node that opens a part is a link: its marks stand inside one SVG `a`, whose text (the label and
  the status) names it to a screen reader.
* The picture is drawn in the base look; the page's looks file recolours it by class
  (`Tools.View.Tokens.rules`), so a figure follows the reader's light or dark scheme.
* Below the picture, the figure in words: each node, its status and the nodes it points to.
-/

namespace Tools.Document.Figure

open Tools.View

/-- The margin around a figure's graph, in logical pixels. -/
def MARGIN : Int := 12

/-- The view's graph of a figure: each node keyed `node:` and its key, its label on the first line
and its status and detail on the second, a planned goal lit; each edge keyed by its place. An edge
to a key no node holds is dropped; `Document.check` refuses it first. -/
def graphOf (nodes : List GraphNode) (edges : List (String × String)) : Graph where
  nodes := (nodes.map fun n => ({
    key := "node:" ++ n.key
    line1 := n.label
    line2 := " · ".intercalate ([n.status, n.detail].filter (!·.isEmpty))
    lit := n.status == "goal"
    form := n.form } : GNode)).toArray
  edges := (edges.zipIdx.filterMap fun ((a, b), i) => do
    return ({ key := s!"edge:{i}", src := ← nodes.findIdx? (·.key == a), dst := ← nodes.findIdx? (·.key == b) } : GEdge)).toArray

/-- **The picture of a figure**, with the link of each node that opens a part from `href`. -/
def picture (href : String → Option String) (nodes : List GraphNode) (edges : List (String × String)) :
    Whatwg.Html.SvgNode :=
  let l := (graphOf nodes edges).layout
  let L : Look := {}
  let W := l.width + 2 * MARGIN
  let H := l.height + 2 * MARGIN
  let link (key : Key) : Option String :=
    if key.startsWith "node:" then
      (nodes.find? (·.key == (key.drop 5).toString)).bind fun n => n.ref.bind href
    else none
  SvgOut.linkedPicture L W.toNat H.toNat 1 link (lowerAll 1 (l.calls L MARGIN MARGIN))

end Tools.Document.Figure

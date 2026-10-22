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
* A node is anchored: its group carries the `id` that `anchor` gives its key, so a relation row's
  link (`Compiler.Graphs`) lands on its mark. The HTML fold qualifies the id by the figure's key,
  because one page may draw one entity in several figures and the site's check wants each id once.
* A node's text is set in the data face, which the cell grid measures. The name and label faces are
  proportional and unmeasured here (`PaintBounds.textUnmeasured`), so a name set in them is cut.
* The picture is drawn in the base look; the page's looks file recolours it by class
  (`Tools.View.Tokens.rules`), so a figure follows the reader's light or dark scheme.
* Below the picture, its description: each node, its status and the nodes it points to.
-/

namespace Tools.Document.Figure

open Tools.View

/-- The margin around a figure's graph, in logical pixels. -/
def MARGIN : Int := 12

/-- **The anchor of a node in a figure**: the figure's key, then the drawn node's key, `node:` and
its own. A relation row links `#` and this (`Compiler.Graphs`). -/
def anchorIn (figure key : String) : String := figure ++ ":node:" ++ key

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

/-- **The picture of a figure**, with the link of each node that opens a part from `href`, and the
`id` of each node's group from `anchor`, by the node's key. -/
def picture (href anchor : String → Option String) (nodes : List GraphNode) (edges : List (String × String)) :
    Whatwg.Html.SvgNode :=
  let l := (graphOf nodes edges).layout
  let L : Look := {}
  let W := l.width + 2 * MARGIN
  let H := l.height + 2 * MARGIN
  let node (key : Key) : Option GraphNode :=
    if key.startsWith "node:" then nodes.find? (·.key == (key.drop 5).toString) else none
  let link (key : Key) : Option String := (node key).bind fun n => n.ref.bind href
  let id (key : Key) : Option String := (node key).bind fun n => anchor n.key
  SvgOut.linkedPicture L W.toNat H.toNat 1 link id (lowerAll 1 (l.calls L MARGIN MARGIN))

end Tools.Document.Figure

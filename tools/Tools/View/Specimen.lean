import Tools.View.Page
import Tools.View.GraphLayout

/-!
# A graph built one edge at a time: the layout's specimen

A tool control of the graph view (`Tools.View.Graph`; `docs/research/2026-10-09-visual-pipeline.md`).
Its consumer is the view's own check: each frame adds one edge to a small graph, and the frames
show each part of the layout at work, with motion between them by key:

- a chain, whose ranks follow its order;
- a shortcut over two ranks, which passes through a point in the rank between;
- a diamond, whose join takes the longer path's rank;
- an edge against the order, a back edge: it closes a cycle and climbs a lane at the right;
- an edge from a node to itself, a back edge of its own.

It holds no semantics of the language: the nodes are letters.
-/

namespace Tools.View.Specimen

open Tools.View

/-- The specimen's nodes, in their order. The order decides the back edges: `e` stands before
`d`, so the diamond's `e → d` is forward, and `d → b` is the one edge against it. -/
def names : List String := ["a", "b", "c", "e", "d", "f"]

/-- The edges, in the order they are added, each with what it shows. -/
def steps : List (String × String × String) :=
  [ ("a", "b", "a chain: each node one rank below the one before"),
    ("b", "c", "the chain grows"),
    ("a", "c", "a shortcut over two ranks passes through a point in the rank between"),
    ("c", "d", "the chain grows"),
    ("b", "e", "a second branch"),
    ("e", "d", "a diamond: the join takes the rank of its longer path"),
    ("d", "b", "an edge against the order is a back edge: it closes a cycle, up a lane at the right"),
    ("d", "f", "a new node below the join"),
    ("f", "f", "an edge to itself is a back edge too") ]

/-- The graph after the first `k` edges: the nodes that an edge has reached, in their order. -/
def graphAt (k : Nat) : Graph :=
  let es := steps.take k
  let used := names.filter fun n => es.any fun (s, d, _) => s == n || d == n
  let pos (n : String) : Nat := used.findIdx (· == n)
  { nodes := (used.map fun n => ({ key := n, line1 := n } : GNode)).toArray,
    edges := (es.map fun (s, d, _) => ({ key := s ++ "→" ++ d, src := pos s, dst := pos d } : GEdge)).toArray }

private def page (g : Graph) (value : Laid) (s d why : String) (i n : Nat) : Page :=
  { title := s!"graph · add {s} → {d}", judgment := why, place := s!"{i + 1} / {n}",
    heads := ("", ""), foot := s!"{g.nodes.size} nodes, {g.edges.size} edges",
    graph := some { title := "", laid := value } }

private def litGraph (i : Nat) (target : String) : Graph :=
  let g := graphAt (i + 1)
  { g with nodes := g.nodes.map fun (v : GNode) => { v with lit := v.key == target } }

/-- One frame after each edge. The last edge's target is lit. -/
def frames : List Page :=
  let n := steps.length
  (steps.zipIdx.map fun ((s, d, why), i) =>
    let g := litGraph i d
    page g g.layout s d why i n)

/-- Check both graph input and layout before constructing each specimen frame. -/
def checkedFrames : Except GraphCheck.Refusal (List Page) :=
  let n := steps.length
  steps.zipIdx.mapM fun ((s, d, why), i) => do
    let g := litGraph i d
    let checked ← GraphLayout.checked g
    pure (page g checked.value s d why i n)

end Tools.View.Specimen

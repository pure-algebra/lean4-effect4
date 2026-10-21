import Effect4.Program.LayerView
import Tools.View.AlgGraph

/-!
# The layer incidence observation

The atoms come from a caller's algebra over the existing `AGraph` carrier. A caller can
read those atoms from the program's relations. The layer combinators then use overlay.
`EffAlgebra.ofLayer` turns a relation reader into the atom algebra.
The generated `cata_layer` is the only traversal.

The observation keeps named vertices and edges. It forgets construction order, cache
identity, and the input and output boundaries. It is not the address-keyed syntax graph.
In particular, equal incidence does not make two ordered layer evaluations equal.

G1 and G2 serve `initial-algebras-folds`, R14, and the `inspect` command's layer reading.
Their claims are `layer-graph-glue` and `layer-graph-merge`
in `tools/ProofGraph/Registry.lean`.
The reach is every `LayerTerm` and every algebra for the atoms.
The observation states no pushout property: that needs explicit boundary maps.
-/

namespace Tools.View.LayerGraph

open Effect4.Program

variable {Op α : Type}

/-- The layer incidence algebra: atoms keep their reader; composition is overlay.
The graph alone forgets which boundary wires `provide` hides. -/
def algebra (atoms : EffAlgebra Op (fun _ => AGraph α)) :
    EffAlgebra Op (fun _ => AGraph α) :=
  { atoms with
    layer_provide := AGraph.overlay
    layer_provideMerge := AGraph.overlay
    layer_merge := AGraph.overlay
    layer_fresh := id
    layer_orDie := id
    layer_mergeAll := id
    layers_nil := .empty
    layers_cons := AGraph.overlay }

/-- The named incidence graph, folded from the layer signature. -/
def hypergraph (atoms : EffAlgebra Op (fun _ => AGraph α)) (term : LayerTerm Op) : AGraph α :=
  cata_layer (algebra atoms) term

/-- G1: providing overlays the incidence graphs, without an extra gluing traversal.
Placement: `layer-graph-glue`, concept `initial-algebras-folds`, R14.
The consumer is the view-graph battery's incidence reader. -/
theorem hypergraph_provide (atoms : EffAlgebra Op (fun _ => AGraph α))
    (self that : LayerTerm Op) :
    hypergraph atoms (.provide self that) =
      .overlay (hypergraph atoms self) (hypergraph atoms that) := rfl

/-- G2: exchanging merged layers keeps the vertices and edges of this observation.
Placement: `layer-graph-merge`, concept `initial-algebras-folds`, R14.
The consumer is the view-graph battery's incidence reader.
The statement does not identify ordered evaluation or address-keyed syntax. -/
theorem hypergraph_merge_comm (atoms : EffAlgebra Op (fun _ => AGraph α))
    (left right : LayerTerm Op) :
    AGraph.denote (hypergraph atoms (.merge left right)) =
      AGraph.denote (hypergraph atoms (.merge right left)) :=
  AGraph.overlay_comm (hypergraph atoms left) (hypergraph atoms right)

end Tools.View.LayerGraph

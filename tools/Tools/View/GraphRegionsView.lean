import Tools.View.GraphRegions
import Tools.View.GraphCheck

/-! A Graph adapter for checked region projection.

The result retains every source edge occurrence, including hidden edges.
The visible graph uses separate node and region key namespaces.
Placement: `docs/research/2026-10-13-graph-regions-view-plan.md`, concept 7, R14.
The observations concern view data, not program meaning or quotient-path lifting.
-/

namespace Tools.View.GraphRegionsView

inductive Refusal where
  | input (reason : GraphCheck.Refusal)
  | ownerCount (actual expected : Nat)
  | regions (reason : GraphRegions.Refusal)

/-- Retained source data, projection occurrences, and the visible graph. -/
structure Prepared where
  source : Graph
  prepared : GraphRegions.Prepared
  edges : Array (GraphRegions.EdgeOccurrence GEdge)
  graph : Graph

/-- Exactly one direct-owner entry corresponds to each original graph node. -/
def ownerCount (g : Graph) (membership : GraphRegions.Membership) : Bool :=
  membership.owner.size == g.nodes.size

/-- The adapter's size observation is exact array-size equality.
A helper of preparation, placed in the adapter plan for the compound-graph generator. -/
theorem ownerCount_iff (g : Graph) (membership : GraphRegions.Membership) :
    ownerCount g membership = true ↔ membership.owner.size = g.nodes.size :=
  beq_iff_eq

/-- Label a visible representative. Prepared projections supply valid source positions.
Missing caller labels use the region's declared key. -/
def visibleNode (g : Graph) (prepared : GraphRegions.Prepared)
    (labels : Array (String × String)) : GraphRegions.Representative → GNode
  | .node i =>
    let n := g.nodes[i]?.getD { key := "", line1 := "" }
    { n with key := "node:" ++ n.key }
  | .region i =>
    let key := (prepared.membership.regions[i]?.map (·.key)).getD ""
    let label := labels[i]?.getD (key, "")
    { key := "region:" ++ key, line1 := label.1, line2 := label.2 }

/-- Keep each visible original edge occurrence with its key and projected endpoints. -/
def visibleGraph (g : Graph) (prepared : GraphRegions.Prepared)
    (edges : Array (GraphRegions.EdgeOccurrence GEdge))
    (labels : Array (String × String)) : Graph :=
  { nodes := prepared.visible.map (visibleNode g prepared labels),
    edges := edges.filterMap fun e =>
      if e.hidden then none else some { e.original with src := e.source, dst := e.target } }

/-- Check the source, owner count, and region projection in that refusal order.
The source input check scans prior key prefixes; this API claims no large-graph time bound. -/
def prepare (g : Graph) (membership : GraphRegions.Membership) (selected : Array Bool)
    (labels : Array (String × String) := #[]) : Except Refusal Prepared := do
  match GraphCheck.input g with
  | .error reason => throw (.input reason)
  | .ok () => pure ()
  unless ownerCount g membership do
    throw (.ownerCount membership.owner.size g.nodes.size)
  let prepared ← (GraphRegions.prepare membership selected).mapError Refusal.regions
  let edges ← (GraphRegions.project prepared g.edges GEdge.src GEdge.dst).mapError Refusal.regions
  pure { source := g, prepared, edges, graph := visibleGraph g prepared edges labels }

end Tools.View.GraphRegionsView

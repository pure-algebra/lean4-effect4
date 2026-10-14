import Tools.View.GraphRegionsView
import ProofGraph.AxiomAudit

/-! Finite production Graph controls for prepared region projection.
Placement: graph-regions-view plan, concept 7, R14's compound-graph generator.
-/

open Tools.View Tools.View.GraphRegionsView

namespace GraphRegionsViewProbe

def source : Graph :=
  { nodes := #[{ key := "r", line1 := "outside", line2 := "kept", lit := true },
      { key := "node:r", line1 := "inside-one" },
      { key := "region:r", line1 := "inside-two" },
      { key := "tail→node:r", line1 := "target" }],
    edges := #[⟨"outside-loop", 0, 0⟩, ⟨"parallel-one", 0, 1⟩,
      ⟨"parallel-two", 0, 2⟩, ⟨"internal", 1, 2⟩, ⟨"inside-loop", 1, 1⟩,
      ⟨"exit", 2, 3⟩] }

def membership : GraphRegions.Membership :=
  { regions := #[⟨"r", none⟩, ⟨"node:r", some 0⟩, ⟨"region:r", none⟩],
    owner := #[none, some 0, some 1, none] }

def collapsed : Except Refusal Prepared :=
  prepare source membership #[true, true, true] #[("collapsed", "details")]

def expanded : Except Refusal Prepared :=
  prepare source membership #[false, false, false]

def observe (result : Except Refusal Prepared) (check : Prepared → Bool) : Bool :=
  match result with
  | .ok p => check p
  | .error _ => false

#guard observe collapsed fun p =>
  p.graph.nodes.map (·.key) ==
    #["node:r", "region:r", "node:tail→node:r", "region:region:r"]
#guard observe collapsed fun p =>
  p.graph.nodes[0]?.any (fun n => n.line1 == "outside" && n.line2 == "kept" && n.lit)
#guard observe collapsed fun p =>
  p.graph.nodes[1]?.any (fun n => n.line1 == "collapsed" && n.line2 == "details")
#guard observe collapsed fun p => p.graph.nodes[3]?.any (fun n => n.line1 == "region:r")
#guard observe collapsed fun p =>
  p.prepared.members == #[#[0], #[1, 2], #[3], #[]]
#guard observe collapsed fun p =>
  p.source.nodes == source.nodes &&
    p.source.edges.map (fun e => (e.key, e.src, e.dst)) ==
      source.edges.map (fun e => (e.key, e.src, e.dst)) &&
    p.source.edges[2]?.any (fun e => e.dst == 2)
#guard observe collapsed fun p =>
  p.edges.map (·.occurrence) == #[0, 1, 2, 3, 4, 5] &&
    p.edges.map (·.hidden) == #[false, false, false, true, true, false]
#guard observe collapsed fun p =>
  p.edges.toList.all fun e =>
    source.edges[e.occurrence]?.any fun original =>
      e.original.key == original.key && e.originalSource == original.src &&
        e.originalTarget == original.dst && e.original.src == original.src &&
        e.original.dst == original.dst
#guard observe collapsed fun p =>
  p.graph.edges.map (·.key) == #["outside-loop", "parallel-one", "parallel-two", "exit"]
#guard observe collapsed fun p =>
  p.graph.edges[0]?.any (fun e => e.src == 0 && e.dst == 0) &&
    p.graph.edges[1]?.any (fun e => e.src == 0 && e.dst == 1) &&
    p.graph.edges[2]?.any (fun e => e.src == 0 && e.dst == 1) &&
    p.graph.edges[3]?.any (fun e => e.src == 1 && e.dst == 2)
#guard observe collapsed fun p => (GraphCheck.input p.graph).isOk
#guard observe expanded fun p =>
  p.graph.nodes.map (·.key) ==
    #["node:r", "node:node:r", "node:region:r", "node:tail→node:r"] &&
    p.graph.edges.size == source.edges.size && p.edges.toList.all (fun e => !e.hidden)
#guard observe expanded fun p => (GraphCheck.input p.graph).isOk

def ownerRefused (owner : Array (Option Nat)) (actual : Nat) : Bool :=
  match prepare source { membership with owner } #[true, true, true] with
  | .error (.ownerCount a expected) => a == actual && expected == source.nodes.size
  | _ => false

#guard ownerRefused #[] 0
#guard ownerRefused #[none, none, none] 3
#guard ownerRefused #[none, none, none, none, none] 5
-- Source admission runs first, even when the owner array has the wrong size.
#guard match prepare { source with nodes := #[{ key := "", line1 := "bad" }] }
    { membership with owner := #[] } #[true, true, true] with
  | .error (.input r) => r == ⟨.node, 0, .key, .emptyKey⟩
  | _ => false
#guard match prepare source membership #[] with
  | .error (.regions (.selectionSize actual expected)) => actual == 0 && expected == 3
  | _ => false
#guard match prepare source { membership with owner := #[none, some 9, none, none] }
    #[true, true, true] with
  | .error (.regions (.ownerOutside vertex owner count)) =>
    vertex == 1 && owner == 9 && count == 3
  | _ => false

-- Reader of the adapter's size law at the real production source and membership.
example : membership.owner.size = source.nodes.size :=
  (ownerCount_iff source membership).mp (by decide)

end GraphRegionsViewProbe

#axiom_audit checked Tools.View.GraphRegionsView Tools.View.GraphRegions

def main : IO Unit := do
  IO.println "graph-regions-view: labels, namespaces, loops, parallel and hidden records pass"
  IO.println "graph-regions-view: owner count, source precedence and region refusal controls pass"

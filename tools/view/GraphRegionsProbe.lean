import Lean
import Tools.View.GraphRegions

/-!
# Finite explicit-region controls and projection benchmark

The controls read original edge payloads and occurrence ordinals, including duplicates.
The quotient can create a displayed path that the original adjacency does not contain.
The benchmark excludes Graph.layout, rendering, and generic graph input admission.
-/

open Tools.View.GraphRegions

namespace GraphRegionsProbe

structure Edge where
  id : Nat
  src : Nat
  dst : Nat
  deriving BEq, Repr

private def membership : Membership :=
  { regions := #[⟨"outer", none⟩, ⟨"inner", some 0⟩, ⟨"deep", some 1⟩]
    owner := #[none, some 0, some 1, some 2, some 2, none] }

private def edges : Array Edge :=
  #[⟨0, 0, 2⟩, ⟨1, 0, 2⟩, ⟨2, 2, 3⟩, ⟨3, 3, 3⟩, ⟨4, 4, 5⟩, ⟨5, 5, 5⟩,
    ⟨0, 0, 2⟩]

private def ready (flags : Array Bool) : Prepared :=
  (prepare membership flags).toOption.getD ⟨membership, flags, #[], #[], #[], #[]⟩

private def collapsed : Prepared := ready #[true, false, false]
private def projected : Array (EdgeOccurrence Edge) :=
  (project collapsed edges Edge.src Edge.dst).toOption.getD #[]

#guard collapsed.visible == #[.node 0, .region 0, .node 5]
#guard collapsed.nodeMap == #[0, 1, 1, 1, 1, 2]
#guard collapsed.members == #[#[0], #[1, 2, 3, 4], #[5]]
#guard collapsed.outer == #[some 0, some 0, some 0]
#guard projected.map (·.occurrence) == #[0, 1, 2, 3, 4, 5, 6]
#guard (projected.map (·.original)).toList.map (·.id) == edges.toList.map (·.id)
#guard projected.map (·.originalSource) == edges.map (·.src)
#guard projected.map (·.originalTarget) == edges.map (·.dst)
#guard projected.map (·.hidden) == #[false, false, true, true, false, false, false]
#guard projected.size == edges.size
#guard (ready #[true, true, true]).visible == collapsed.visible
#guard (ready #[false, true, false]).visible == #[.node 0, .node 1, .region 1, .node 5]
#guard (ready #[false, false, true]).visible == #[.node 0, .node 1, .node 2, .region 2, .node 5]
#guard (ready #[false, false, false]).nodeMap == #[0, 1, 2, 3, 4, 5]
#guard ((project (ready #[false, false, false]) edges Edge.src Edge.dst).toOption.getD #[]).all
  (!·.hidden)

private def empty : Membership :=
  { regions := #[⟨"empty", none⟩, ⟨"masked", some 0⟩, ⟨"other", none⟩], owner := #[] }
#guard ((prepare empty #[true, true, true]).toOption.map (·.visible)) ==
  some #[.region 0, .region 2]
#guard ((prepare empty #[true, true, true]).toOption.map (·.members)) == some #[#[], #[]]
#guard (prepare membership #[false]).toOption.isNone
#guard (prepare { membership with regions := #[⟨"", none⟩] } #[true]).toOption.isNone
#guard (prepare { membership with regions := #[⟨"same", none⟩, ⟨"same", none⟩] }
  #[false, false]).toOption.isNone
#guard (prepare { regions := #[⟨"self", some 0⟩], owner := #[] } #[false]).toOption.isNone
#guard (prepare { regions := #[⟨"future", some 1⟩, ⟨"later", none⟩], owner := #[] }
  #[false, false]).toOption.isNone
#guard (prepare { regions := #[], owner := #[some 0] } #[]).toOption.isNone
#guard (project collapsed #[Edge.mk 0 6 0] Edge.src Edge.dst).toOption.isNone
#guard (project { collapsed with nodeMap := #[] } edges Edge.src Edge.dst).toOption.isNone

-- No original edge connects either inside member to the other.
private def disconnected : Membership :=
  { regions := #[⟨"group", none⟩], owner := #[none, some 0, some 0, none] }
private def cutEdges : Array Edge := #[⟨0, 0, 1⟩, ⟨1, 2, 3⟩]
private def cut : Prepared := (prepare disconnected #[true]).toOption.getD collapsed
private def cutProjection : Array (EdgeOccurrence Edge) :=
  (project cut cutEdges Edge.src Edge.dst).toOption.getD #[]
#guard !cutEdges.any (fun first => first.src == 0 &&
  cutEdges.any (fun second => first.dst == second.src && second.dst == 3))
#guard cutProjection.any (fun first => first.source == 0 &&
  cutProjection.any (fun second => first.target == second.source && second.target == 2))

private def bench (count : Nat) : IO Unit := do
  let input : Membership :=
    { regions := (List.range 10).map (fun i => RegionDecl.mk (toString i) none) |>.toArray
      owner := (List.range count).map (fun i => some (i % 10)) |>.toArray }
  let inputEdges := (List.range (2 * count)).map (fun i => Edge.mk i (i % count) ((i + 1) % count)) |>.toArray
  let started ← IO.monoNanosNow
  let retained ← IO.mkRef (prepare input (Array.replicate 10 true))
  let preparation ← retained.get
  let preparedAt ← IO.monoNanosNow
  let .ok prepared := preparation | throw (IO.userError "benchmark membership refused")
  let result ← IO.mkRef (project prepared inputEdges Edge.src Edge.dst)
  let value ← result.get
  let projectedAt ← IO.monoNanosNow
  let .ok output := value | throw (IO.userError "benchmark projection refused")
  unless output.size == inputEdges.size && prepared.members.foldl (fun n xs => n + xs.size) 0 == count do
    throw (IO.userError "benchmark conservation failed")
  IO.println (Lean.Json.compress (Lean.Json.mkObj [
    ("vertices", Lean.toJson count), ("regions", Lean.toJson input.regions.size),
    ("input_edges", Lean.toJson inputEdges.size), ("visible", Lean.toJson prepared.visible.size),
    ("retained_edges", Lean.toJson output.size), ("prepare_ns", Lean.toJson (preparedAt - started)),
    ("project_ns", Lean.toJson (projectedAt - preparedAt)),
    ("checksum", Lean.toJson (output.foldl (fun n e => n + e.occurrence + e.originalSource + e.originalTarget) 0))]))

end GraphRegionsProbe

def main (args : List String) : IO Unit := do
  let counts := if args.isEmpty then [100, 1000, 10000] else args.filterMap String.toNat?
  for count in counts do GraphRegionsProbe.bench count

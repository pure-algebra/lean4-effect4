import Baseline
import Tools.View.FlowOrder
import Tools.View.FlowSpecimen
import ProofGraph.Proof

/-! Readers of prepared placement laws against retained pre-change policies.
Finite controls include malformed raw boxes and repeated assignments.
The named obligations and limits are in PLAN.md. -/
set_option autoImplicit false
namespace GraphToolsProbe.Placement
open Tools.View Tools.View.Flow

/-- Existing callers observe the same full placement at every supplied width. -/
theorem placement_old (width : GNode → Int) (f : Flow) :
    placeWith width f = Baseline.placeWith width f := by
  have heights : (preparePlacement (layWith width f)).height =
      Baseline.heightsOf (layWith width f) := by
    funext i
    exact preparePlacement_height _ i
  simp only [placeWith, Baseline.placeWith, heights, preparePlacement_lanes]

/-- A raw box may name an endpoint outside its item list; preparation retains that assignment. -/
def outside : Box :=
  { w := 1, items := [pointAt "one" 0], exits := [("fiber", 0)], waits := [(1, "fiber")] }

#guard (preparePlacement outside).height 1 = Baseline.heightsOf outside 1
#guard (preparePlacement outside).height 1 > outside.topPad
#guard (preparePlacement outside).height 20 = outside.topPad

-- Repeated order positions overwrite earlier heights, including an existing sparse entry.
#guard (List.range 8).all fun i =>
  heightAt 7 (assignHeights (fun _ => 2) [{ fr := 1, to := 4 }] 7 [1, 4, 1, 4] [(1, 30)]) i ==
    assign (fun _ => 2) [{ fr := 1, to := 4 }] 7 [1, 4, 1, 4] (heightAt 7 [(1, 30)]) i

-- Existing fold examples exercise forks, joins, waits, regions, loops, and empty races.
#guard Tools.View.FlowSpecimen.programs.all fun (_, _, program) =>
  let flow := ofProgram program
  let fresh := placeWith nodeWidth flow
  let old := Baseline.placeWith nodeWidth flow
  fresh.placed.map (fun p => (p.key, p.x, p.y, p.w)) ==
      old.placed.map (fun p => (p.key, p.x, p.y, p.w)) && fresh.lanes == old.lanes

-- The selected relation keeps cyclic waits in lanes without adding their constraint.
#guard (acceptWaits 2 [{ fr := 0, to := 1 }] [(1, 0)]).1.length == 1
#guard (acceptWaits 2 [{ fr := 0, to := 1 }] [(1, 0)]).2 == [(1, 0)]
#guard (acceptWaits 2 [] [(0, 1)]).1.length == 1

run_elab do
  let env ← Lean.getEnv
  let exact := [``heightAt, ``assignHeights, ``preparePlacement, ``PreparedPlacement.height,
    ``assignHeights_agrees, ``preparePlacement_height, ``preparePlacement_lanes,
    ``place_placed, ``place_descends, ``place_apart, ``placement_old]
  let (answers, _) := ProofGraph.reachedAxiomsMany env exact.toArray {}
  for (name, answer) in exact.toArray.zip answers do
    let some axioms := answer | throwError "exact dependency traversal exhausted for {name}"
    for axiomName in axioms do
      unless [``propext, ``Quot.sound].contains axiomName do
        throwError "{name} reaches forbidden axiom {axiomName}"
    Lean.logInfo m!"{name}: exact axioms {axioms}"
  Lean.logInfo m!"PASS: prepared placement policies, controls, and exact dependencies"
end GraphToolsProbe.Placement

import Tools.Graph.Path
import Tools.View.FlowLaws
import ProofGraph.Axioms

/-! The shared reader at real declaration dependencies, including type dependencies.
This is a finite reflection control. It proves no extractor theorem or complete environment capture. -/
open Lean Tools.Graph Tools.View.Flow
run_elab do
  let env ← getEnv
  let roots := [``preparePlacement_height, ``assignHeights_agrees]
  let mut occurrences : List (Name × Name) := []
  for root in roots do
    let some info := env.find? root | throwError "missing source declaration {root}"
    occurrences := occurrences ++ (ProofGraph.usedConstantsOf info).toList.map (root, ·)
  let some first := occurrences.findFinIdx? (· == (``preparePlacement_height, ``assignHeights_agrees))
    | throwError "the height connector no longer names the assignment theorem"
  let some second := occurrences.findFinIdx? (· == (``assignHeights_agrees, ``heightAt))
    | throwError "the assignment theorem no longer names the height observation"
  let endpoints := fun i : Fin occurrences.length => occurrences[i]
  let some path := Walk.read? endpoints ``preparePlacement_height ``heightAt [first, second]
    | throwError "actual dependency chain was refused"
  unless path.edges == [first, second] do throwError "dependency occurrences changed"
  unless (Walk.read? endpoints ``preparePlacement_height ``heightAt [second, first]).isNone do
    throwError "reordered dependency path was accepted"
  logInfo m!"PASS: {occurrences.length} captured edge occurrences; checked theorem-to-observation path {path.edges.map (fun i => occurrences[i])}"

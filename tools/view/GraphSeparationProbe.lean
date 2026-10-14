import Tools.View.GraphSeparation
import ProofGraph.AxiomAudit

/-! Finite node-separation controls; no scheduler or between-sample observation. -/

open Whatwg.Svg.Scene Tools.View.GraphSeparation

private def oldBoxes : List IBox := [⟨0, 0, 10, 10⟩, ⟨100, 0, 110, 10⟩]
private def newBoxes : List IBox := oldBoxes.reverse
private def crossing : List IBox := [⟨50, 0, 60, 10⟩, ⟨50, 0, 60, 10⟩]

#guard checkClear []
#guard checkClear [⟨0, 0, 10, 10⟩, ⟨10, 0, 20, 10⟩]
#guard firstOverlap crossing = some ⟨0, 1⟩
#guard firstOverlap [⟨0, 0, 10, 10⟩, ⟨20, 0, 30, 10⟩, ⟨0, 0, 10, 10⟩] = some ⟨0, 2⟩
#guard firstFrameOverlap [oldBoxes, crossing, newBoxes] = some ⟨1, ⟨0, 1⟩⟩
#guard firstFrameOverlap [oldBoxes, newBoxes] = none

-- This sparse sample profile misses the collision; the envelope selector detects it.
#guard (firstSweptOverlap (oldBoxes.zip newBoxes)).isSome
#guard firstSweptOverlap
  [(⟨0, 0, 10, 10⟩, ⟨20, 0, 30, 10⟩), (⟨100, 0, 110, 10⟩, ⟨120, 0, 130, 10⟩)] = none

-- A maximum-size envelope covers a wide target used at the old origin.
#guard movingEnvelope ⟨100, 0, 110, 10⟩ ⟨0, 0, 100, 10⟩ = ⟨0, 0, 200, 10⟩
#guard ¬(⟨100, 0, 200, 10⟩ : IBox).Inside (IBox.hull ⟨100, 0, 110, 10⟩ ⟨0, 0, 100, 10⟩)
example : (⟨100, 0, 200, 10⟩ : IBox).Inside
    (movingEnvelope ⟨100, 0, 110, 10⟩ ⟨0, 0, 100, 10⟩) :=
  movingEnvelope_contains _ _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- These supplied moments pass, but their envelopes intersect: a conservative false positive.
#guard firstFrameOverlap
  [[⟨0, 0, 10, 10⟩, ⟨0, -100, 10, -90⟩],
   [⟨25, 0, 35, 10⟩, ⟨0, -50, 10, -40⟩],
   [⟨50, 0, 60, 10⟩, ⟨0, 0, 10, 10⟩],
   [⟨75, 0, 85, 10⟩, ⟨0, 50, 10, 60⟩],
   [⟨100, 0, 110, 10⟩, ⟨0, 100, 10, 110⟩]] = none
#guard (firstSweptOverlap
  [(⟨0, 0, 10, 10⟩, ⟨100, 0, 110, 10⟩), (⟨0, -100, 10, -90⟩, ⟨0, 100, 10, 110⟩)]).isSome

-- An overshooting origin is outside the envelope's stated premise.
#guard ¬(⟨30, 0, 40, 10⟩ : IBox).Inside (movingEnvelope ⟨0, 0, 10, 10⟩ ⟨20, 0, 30, 10⟩)

#guard fallback 0 = .old 1000
#guard fallback 399 = .old 3
#guard fallback 400 = .hidden
#guard fallback 600 = .hidden
#guard fallback 601 = .new 2
#guard fallback 1000 = .new 1000
#guard fallback 1200 = .new 1000
-- Reader of the policy law at the actual swap's endpoint families.
example (t : Nat) : List.Pairwise IBox.Disjoint ((fallback t).envelopes oldBoxes newBoxes) :=
  fallback_clear _ _ _ ((checkClear_iff _).mp (by decide))
    ((checkClear_iff _).mp (by decide))

#axiom_audit Tools.View.GraphSeparation

def main : IO Unit := do
  IO.println "graph-separation: touching, first refusal, swap, translation, size change controls pass"
  IO.println "graph-separation: sparse-sample miss, conservative false positive, overshoot controls pass"
  IO.println "graph-separation: hidden relocation and endpoint-family fallback controls pass"

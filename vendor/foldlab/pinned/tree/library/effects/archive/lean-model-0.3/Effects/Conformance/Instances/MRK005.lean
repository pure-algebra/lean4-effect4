import Effects.Conformance.Schema.Agreement
import Effects.Conformance.Instances.MRK002

/-!
# MRK-005 — slice decoding agrees with the whole decode

Relational AGREEMENT over the decoder: the slice computation runs the
machine over the range extractor's stream; the ideal computation runs
the whole decode and filters its emissions to the range. They agree at
the emission lists — the named theorem `slice_whole_agreement` is the
law, universally over chunk lists and ranges. The falsification kit is
the over-emitting computation: a mutated run handing back the whole
decode's emissions unfiltered, which observably diverges on any proper
slice.
-/

namespace Effects.Conformance

open Effects.Merkle
open Effects.Cas (Bytes)

private abbrev SliceX := List Bytes × Nat × Nat

private def sliceRun (x : SliceX) : List (Nat × Bytes) :=
  emissionsOf (drun ⟨mrkKitH, x.1.length, root mrkKitH 0 x.1, x.2.1, x.2.2⟩
    (initState ⟨mrkKitH, x.1.length, root mrkKitH 0 x.1, x.2.1, x.2.2⟩)
    (genStream mrkKitH x.2.1 x.2.2 0 x.1)).2

private def wholeRunFiltered (x : SliceX) : List (Nat × Bytes) :=
  (emissionsOf (drun ⟨mrkKitH, x.1.length, root mrkKitH 0 x.1, 0, x.1.length⟩
    (initState ⟨mrkKitH, x.1.length, root mrkKitH 0 x.1, 0, x.1.length⟩)
    (genStream mrkKitH 0 x.1.length 0 x.1)).2).filter
    (fun p => decide (x.2.1 ≤ p.1) && decide (p.1 < x.2.2))

/-- MRK-005: the slice is the whole decode restricted to the range. -/
def mrk005 : Agreement SliceX (List (Nat × Bytes)) (List (Nat × Bytes))
    (List (Nat × Bytes)) (List (Nat × Bytes)) where
  id := "MRK-005"
  sentence := "On nonempty chunk lists and any requested range, the slice decode over the range extractor's stream and the whole decode filtered to the range agree at their emission lists — a slice emits exactly the bytes the whole decode would emit at those offsets, never more, so slice and encoding carriers stay transport while roots and decoded bytes stay the identity."
  hyp := fun x => 0 < x.1.length
  observeF := id
  observeG := id
  rel := Eq
  f := sliceRun
  g := wholeRunFiltered
  law := fun x hx => slice_whole_agreement mrkKitH x.2.1 x.2.2 x.1 hx
  posX := ([[1], [2], [3]], 1, 3)
  pos_hyp := by decide
  negF := fun x => wholeRunFiltered x ++ [(999, [])]
  negX := ([[1], [2]], 0, 1)
  neg_hyp := by decide
  neg_diverges := by
    intro h
    have := congrArg List.length h
    simp at this

end Effects.Conformance

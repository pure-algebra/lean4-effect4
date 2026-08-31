import Effects.Conformance.Schema.Agreement
import Effects.Conformance.Instances.MRK002

/-!
# MRK-006 — the inclusion verifier accepts exactly the judgment

Relational AGREEMENT packaging the reflection: the executable verifier
against the decided inclusion judgment, agreeing at the boolean. The
completeness half (honest paths verify) is `branchRoot_genPath`; the
binding half (two accepted openings of one root and index agree or
exhibit a computable collision, and every accepted opening binds the
committed chunk at its index) is `branchRoot_bind` and
`opening_binds_committed` — cited here, proved in the model. The
falsification kit is the always-accepting verifier against an opening
whose recomputation fails.
-/

namespace Effects.Conformance

open Effects.Merkle
open Effects.Cas (Bytes)

private abbrev OpeningX := Nat × Nat × Bytes × List Bytes × Bytes

/-- Two one-byte chunks. The negative kit decides inclusion by kernel
evaluation, which rebuilds the root and walks the sibling path over this
list, so it stays small. -/
private def kitChunks : List Bytes := [[1], [2]]

/-- MRK-006: the executable inclusion verifier agrees with the decided
inclusion judgment. -/
def mrk006 : Agreement OpeningX Bool Bool Bool Bool where
  id := "MRK-006"
  sentence := "On every opening — an index, a count, leaf bytes, a sibling list, and an expected root — the executable inclusion verifier and the decided inclusion judgment agree at the boolean: the verifier accepts exactly the openings whose derived-side recomputation reaches the expected root, honestly generated paths verify, and two accepted openings of one root and index carry the same bytes or exhibit a computable hash collision."
  hyp := fun _ => True
  observeF := id
  observeG := id
  rel := Eq
  f := fun x => verifyInclusion mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  g := fun x => decide (InclusionOk mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
    x.2.2.2.2)
  law := fun x _ => by
    by_cases hI : InclusionOk mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
    · simp [(verifyInclusion_iff mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
        x.2.2.2.2).mpr hI, hI]
    · have hv : verifyInclusion mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
          x.2.2.2.2 = false := by
        cases hb : verifyInclusion mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
          x.2.2.2.2
        · rfl
        · exact absurd ((verifyInclusion_iff mrkKitH x.1 x.2.1 x.2.2.1
            x.2.2.2.1 x.2.2.2.2).mp hb) hI
      simp [hv, hI]
  posX := (0, 2, [1], genPath mrkKitH 0 0 kitChunks, root mrkKitH 0 kitChunks)
  pos_hyp := trivial
  negF := fun _ => true
  negX := (0, 2, [1], [], root mrkKitH 0 kitChunks)
  neg_hyp := trivial
  neg_diverges := by decide

end Effects.Conformance

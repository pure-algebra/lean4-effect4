import Effects.Conformance.Schema.Agreement
import Effects.Conformance.Instances.MRK002
import Effects.Merkle.Consistency

/-!
# MRK-007 — the consistency verifier accepts exactly the judgment

Relational AGREEMENT packaging the reflection: the executable
consistency verifier against the decided consistency judgment,
agreeing at the boolean. The completeness half (an honestly generated
proof relates the committed prefix root to the whole root) is
`consistency_complete`; the binding half (an accepted proof against an
honest new tree forces the old root to BE the committed prefix's root
or exhibits a computable collision) is `consistency_binds_prefix` —
cited here, proved in the model. The falsification kit is the
always-accepting verifier against an out-of-range claim.
-/

namespace Effects.Conformance

open Effects.Merkle
open Effects.Cas (Bytes)

private abbrev ConsX := Nat × Nat × Bytes × Bytes × List Bytes

private def consKitChunks : List Bytes := [[1], [2], [3]]

/-- MRK-007: the executable consistency verifier agrees with the
decided consistency judgment. -/
def mrk007 : Agreement ConsX Bool Bool Bool Bool where
  id := "MRK-007"
  sentence := "On every claimed relation — an old size, a new size, two roots, and a proof — the executable consistency verifier and the decided consistency judgment agree at the boolean: the verifier accepts exactly the proofs whose size-derived rebuild reproduces both roots with the proof exactly consumed, honestly generated proofs relate the committed prefix root to the whole root, and an accepted proof against an honest new tree forces the old root to be the committed prefix's root or exhibits a computable hash collision."
  hyp := fun _ => True
  observeF := id
  observeG := id
  rel := Eq
  f := fun x => verifyConsistency mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
    x.2.2.2.2
  g := fun x => decide (ConsistencyOk mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
    x.2.2.2.2)
  law := fun x _ => by
    by_cases hC : ConsistencyOk mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
      x.2.2.2.2
    · simp [(verifyConsistency_iff mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
        x.2.2.2.2).mpr hC, hC]
    · have hv : verifyConsistency mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
          x.2.2.2.2 = false := by
        cases hb : verifyConsistency mrkKitH x.1 x.2.1 x.2.2.1 x.2.2.2.1
          x.2.2.2.2
        · rfl
        · exact absurd ((verifyConsistency_iff mrkKitH x.1 x.2.1 x.2.2.1
            x.2.2.2.1 x.2.2.2.2).mp hb) hC
      simp [hv, hC]
  posX := (2, 3, root mrkKitH 0 (consKitChunks.take 2),
    root mrkKitH 0 consKitChunks, genConsProof mrkKitH 0 2 consKitChunks true)
  pos_hyp := trivial
  negF := fun _ => true
  negX := (0, 1, [], [], [])
  neg_hyp := trivial
  neg_diverges := by decide

end Effects.Conformance

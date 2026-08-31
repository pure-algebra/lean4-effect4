import Effects.Conformance.Instances.MRK002

/-!
# MRK-003 — length is observable only through the final chunk

TRACE-EXCLUDES over the same decoder pairing: the guarded mode is "not
entitled to validate the length" — the pending input is not a verified
final chunk — and the excluded decision is the length-validation tag.
This is bao's final-chunk requirement at the machine altitude: no run
observes the declared length before the final chunk itself validates
against the root. The negative kit is the verified final chunk, whose
step does validate the length — the gate is not vacuous.
-/

namespace Effects.Conformance

open Effects.Merkle
open Effects.Cas (Bytes)

private def finalFrame1 : DState Bytes :=
  ⟨[⟨mrkKitH.H (.leaf 1 [8]), 1, 1⟩], .active⟩

private def nonFinalFrame0 : DState Bytes :=
  ⟨[⟨mrkKitH.H (.leaf 0 [7]), 0, 1⟩], .active⟩

/-- MRK-003: no run observes the length before the final chunk
validates. -/
def mrk003 : TraceExcludes (DState Bytes × DInput Bytes) Unit DTag Bool where
  id := "MRK-003"
  sentence := "When the pending input is not a verified final chunk, no step ever validates the length: the declared length is exposed to the caller only when the final chunk itself validates against the root, so a truncated or length-tweaked stream can never make the decoder vouch for a length it did not verify."
  modeOf := fun p => lengthEntitled mrkKitD p.1 p.2
  guarded := false
  decisions := fun p _ =>
    ((dstep mrkKitD p.1 p.2).decisions).map DDecision.tag
  bad := .lengthValidated
  law := fun p _ h => dstep_length_only_final mrkKitD p.1 p.2 h
  posState := (nonFinalFrame0, .chunkNode [7])
  posInput := ()
  pos_mode := by decide
  negState := (finalFrame1, .chunkNode [8])
  negInput := ()
  neg_mode := by decide
  neg_bad := by decide

end Effects.Conformance

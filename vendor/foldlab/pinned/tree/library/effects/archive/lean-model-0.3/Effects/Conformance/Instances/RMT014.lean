import Effects.Conformance.Schema.FailClosed
import Effects.Remote.ControlCodec

/-!
# RMT-014 — control state parses fail-closed

FAIL-CLOSED over the capability-document codec: the hypothesis is
membership in the canonical image — the bytes ARE the encoding of some
representable limits — and when it fails the closed decoder returns
nothing: truncation, oversize fields, and trailing bytes are all
rejected, by the exactness theorem's contrapositive, with the same
posture as node bytes. The negative kit is a canonical encoding, which
decodes — rejection is not universal.
-/

namespace Effects.Conformance

open Effects.Remote

/-- RMT-014: capability documents parse fail-closed. -/
def rmt014 : FailClosed Unit (List UInt8) (Option Limits) where
  id := "RMT-014"
  sentence := "When capability-document bytes are not the canonical encoding of representable limits, the closed decoder returns nothing — truncation, oversize fields, and trailing bytes are all rejected with the same fail-closed posture as node bytes, and a successful decode's input is exactly the canonical encoding of its result."
  wf := fun _ => True
  hyp := fun _ bytes => ∃ l : Limits,
    l.maxBatchKeys < 4294967296 ∧ l.maxBlobBytes < 4294967296 ∧
      bytes = encodeLimits l
  step := fun _ bytes => (decodeLimits? bytes, ())
  isRejection := Option.isNone
  measure := fun _ => 0
  law_reject := fun _ bytes _ hn => by
    match hval : decodeLimits? bytes with
    | none => simp
    | some l =>
      obtain ⟨heq, hk, hb⟩ := decodeLimits_exact bytes l hval
      exact absurd ⟨l, hk, hb, heq⟩ hn
  law_frozen := fun _ _ _ _ => rfl
  posState := ()
  posInput := [1, 2, 3]
  pos_wf := trivial
  pos_nohyp := by
    rintro ⟨l, -, -, heq⟩
    have := congrArg List.length heq
    rw [encodeLimits_length] at this
    simp at this
  negState := ()
  negInput := encodeLimits ⟨2, 3⟩
  neg_hyp := ⟨⟨2, 3⟩, by decide, by decide, rfl⟩

end Effects.Conformance

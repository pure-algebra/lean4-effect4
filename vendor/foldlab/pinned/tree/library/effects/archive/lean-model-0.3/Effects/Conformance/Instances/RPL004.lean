import Effects.Conformance.Schema.FailClosed
import Effects.Replay.Laws

/-!
# RPL-004 — mismatch fails closed

FAIL-CLOSED over the reducer's invocation step: when request-side
compatibility at the cursor fails in an active replay session, the step
returns a typed rejection and the cursor is unchanged — nothing is
consumed. The positive kit's history is empty, so the probe rejects as
history-exhausted; the negative kit matches, so rejection is not
universal.
-/

namespace Effects.Conformance

open Effects.Replay

private abbrev St := SessionState String String String String

private def entry0 : Entry String String String String :=
  ⟨"acme/Rates/get", 1, "req-0", .success "ok"⟩

private def exhausted : St := ⟨.replay, .active, [], 0, none⟩
private def replayOne : St := ⟨.replay, .active, [entry0], 0, none⟩
private def probe : Invocation String String := ⟨"acme/Rates/get", 1, "req-0"⟩

/-- RPL-004: a request-side mismatch rejects and consumes nothing. -/
def rpl004 : FailClosed St (Invocation String String)
    (StepResult String String) where
  id := "RPL-004"
  sentence := "When request-side compatibility at the cursor fails, the step rejects with a typed mismatch category and the cursor is unchanged — a mismatch fails closed: it consumes nothing, names its category, and is terminal for the attempt; nothing falls through to a live adapter."
  wf := fun s => s.status = .active ∧ s.mode = .replay
  hyp := fun s inv => MatchesAt s inv
  step := fun s inv =>
    ((reduce s (.invoke inv)).result, (reduce s (.invoke inv)).state)
  isRejection := StepResult.isRejection
  measure := SessionState.cursor
  law_reject := fun s inv hwf hn =>
    RPL_004_mismatch_rejects s inv hwf.1 hwf.2 hn
  law_frozen := fun s inv hwf hn =>
    RPL_004_mismatch_frozen s inv hwf.1 hwf.2 hn
  posState := exhausted
  posInput := probe
  pos_wf := by decide
  pos_nohyp := by decide
  negState := replayOne
  negInput := probe
  neg_hyp := by decide

end Effects.Conformance

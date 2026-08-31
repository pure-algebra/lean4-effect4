import Effects.Conformance.Schema.FailClosed
import Effects.Replay.Laws

/-!
# RPL-005 — completion rejects an unconsumed suffix

FAIL-CLOSED over the reducer's completion step: when the program's
terminal arrives before the cursor reaches the history length, the step
rejects with the unconsumed-suffix category — carrying the terminal so
far — and the cursor is unchanged. The negative kit completes exactly at
the history length, so rejection is not universal.
-/

namespace Effects.Conformance

open Effects.Replay

private abbrev St := SessionState String String String String

private def entry0 : Entry String String String String :=
  ⟨"acme/Rates/get", 1, "req-0", .success "ok"⟩

private def unconsumed : St := ⟨.replay, .active, [entry0], 0, none⟩
private def consumed : St := ⟨.replay, .active, [entry0], 1, none⟩
private def doneTerminal : Terminal String String := .succeeded "final"

/-- RPL-005: completing with an unconsumed suffix rejects, carrying the
terminal so far. -/
def rpl005 : FailClosed St (Terminal String String)
    (StepResult String String) where
  id := "RPL-005"
  sentence := "When completion arrives before the cursor reaches the history length, the step rejects with the unconsumed-suffix category and the cursor is unchanged — the rejection carries the program's terminal so far, so a same-looking final value cannot hide a recorded action that was never re-emitted."
  wf := fun s => s.status = .active
  hyp := fun s _ => s.cursor = s.history.length
  step := fun s t =>
    ((reduce s (.complete t)).result, (reduce s (.complete t)).state)
  isRejection := StepResult.isRejection
  measure := SessionState.cursor
  law_reject := fun s t ha hn => by
    simp [RPL_005_suffix_rejects_with_terminal s t ha hn,
      StepResult.isRejection]
  law_frozen := fun s t ha hn => by
    simp [RPL_005_suffix_rejects_with_terminal s t ha hn]
  posState := unconsumed
  posInput := doneTerminal
  pos_wf := rfl
  pos_nohyp := by decide
  negState := consumed
  negInput := doneTerminal
  neg_hyp := by decide

end Effects.Conformance

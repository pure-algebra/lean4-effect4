import Effects.Conformance.Schema.ExactStep
import Effects.Replay.Laws

/-!
# RPL-003 — matching consumes exactly the permitted occurrence

EXACT-STEP over the reducer: when the emitted invocation matches the
entry at the cursor of an active replay session, one step advances the
cursor by exactly one. The negative kit's invocation names a different
operation, so the hypothesis discriminates.
-/

namespace Effects.Conformance

open Effects.Replay

private abbrev St := SessionState String String String String

private def entry0 : Entry String String String String :=
  ⟨"acme/Rates/get", 1, "req-0", .success "ok"⟩

private def replayOne : St := ⟨.replay, .active, [entry0], 0, none⟩

/-- RPL-003: a match consumes exactly one occurrence. -/
def rpl003 : ExactStep St (Invocation String String) where
  id := "RPL-003"
  sentence := "When the emitted invocation matches the entry at the cursor, one reducer step advances the cursor by exactly one — a matching request consumes exactly the permitted occurrence: never zero, never two."
  wf := fun s => s.WF ∧ s.status = .active ∧ s.mode = .replay
  hyp := fun s inv => MatchesAt s inv
  step := fun s inv => (reduce s (.invoke inv)).state
  measure := SessionState.cursor
  delta := 1
  law := fun s inv hwf hhyp =>
    RPL_003_match_consumes_exactly_one s inv hwf.2.1 hwf.2.2 hhyp
  posState := replayOne
  posInput := ⟨"acme/Rates/get", 1, "req-0"⟩
  pos_wf := by refine ⟨⟨?_, ?_⟩, rfl, rfl⟩ <;> decide
  pos_hyp := by decide
  negState := replayOne
  negInput := ⟨"acme/Other/get", 1, "req-0"⟩
  neg_hyp := by decide

end Effects.Conformance

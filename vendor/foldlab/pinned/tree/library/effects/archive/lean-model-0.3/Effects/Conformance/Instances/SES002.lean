import Effects.Conformance.Schema.WfPreserve
import Effects.Replay.Laws

/-!
# SES-002 — every reducer step preserves well-formedness

WF-PRESERVE over the reducer with the trivial hypothesis: totality means
EVERY input from a well-formed session state yields a well-formed one.
The falsification witness is an ill-formed raw state — a cursor past the
history.
-/

namespace Effects.Conformance

open Effects.Replay

private abbrev St := SessionState String String String String
private abbrev In := Input String String String String

private def wfState : St := ⟨.record, .active, [], 0, none⟩
private def illState : St := ⟨.record, .active, [], 5, none⟩

/-- SES-002: reducer steps preserve session-state well-formedness. -/
def ses002 : WfPreserve St In where
  id := "SES-002"
  sentence := "On every input, one reducer step from a well-formed session state yields a well-formed session state — the cursor stays inside the history, and record mode keeps it pinned to the history length."
  wf := SessionState.WF
  hyp := fun _ _ => True
  step := fun s i => (reduce s i).state
  law := fun s i hwf _ => SES_002_reduce_preserves_wf s i hwf
  posState := wfState
  posInput := .invoke ⟨"acme/Rates/get", 1, "req-0"⟩
  pos_wf := by decide
  pos_hyp := trivial
  negState := illState
  neg_ill := by decide

end Effects.Conformance

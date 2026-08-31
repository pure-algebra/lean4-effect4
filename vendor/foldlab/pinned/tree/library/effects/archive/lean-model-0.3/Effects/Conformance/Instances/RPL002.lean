import Effects.Conformance.Schema.TraceExcludes
import Effects.Replay.Laws

/-!
# RPL-002 — replay traces never select live delegation

TRACE-EXCLUDES over the reducer at the decision-tag projection: the
guarded mode is replay, the excluded decision is the live-delegation tag.
The negative kit is a record-mode invocation, which DOES delegate —
proving the mode guard is not vacuous. The obligation's second half (no
live-service requirement in replay construction) is the TypeScript layer
fact scheduled at M4; this instance is the Lean trace half.
-/

namespace Effects.Conformance

open Effects.Replay

private abbrev St := SessionState String String String String
private abbrev In := Input String String String String

private def posState : St := ⟨.replay, .active, [], 0, none⟩
private def negState : St := ⟨.record, .active, [], 0, none⟩
private def probe : In := .invoke ⟨"acme/Rates/get", 1, "req-0"⟩

/-- RPL-002: replay-mode decision traces never select live delegation. -/
def rpl002 : TraceExcludes St In DecisionTag Mode where
  id := "RPL-002"
  sentence := "In replay mode, no step ever emits a live-delegation decision — replay is hermetic: whether a live adapter was requested is a projection of the decision trace, and in replay mode that projection is empty by law, never by luck."
  modeOf := SessionState.mode
  guarded := .replay
  decisions := fun s i => (reduce s i).decisions.map Decision.tag
  bad := .liveDelegation
  law := fun s i hm => RPL_002_replay_excludes_live_delegation s i hm
  posState := posState
  posInput := probe
  pos_mode := rfl
  negState := negState
  negInput := probe
  neg_mode := by decide
  neg_bad := by decide

end Effects.Conformance

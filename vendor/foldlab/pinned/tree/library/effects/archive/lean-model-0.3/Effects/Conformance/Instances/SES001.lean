import Effects.Conformance.Schema.TraceExcludes
import Effects.Replay.Laws

/-!
# SES-001 — nothing appends past the structural abort

TRACE-EXCLUDES over the reducer with the session STATUS as the guarded
mode: in an aborted session no step emits the occurrence-append decision —
indeed an aborted session emits nothing at all, which is the structural
form of "histories are truthful prefixes, never gapped subsequences". The
negative kit is an active record-mode append, which DOES emit the append
decision. The transport-seam half (the failure surfaces as the session's
typed store error, catchable by no wrapped method) is the TypeScript
layer fact scheduled at M4.
-/

namespace Effects.Conformance

open Effects.Replay

private abbrev St := SessionState String String String String
private abbrev In := Input String String String String

private def posState : St := ⟨.record, .aborted, [], 0, none⟩
/-- The negative kit is a SOLICITED append: the outstanding delegation
names the arriving invocation, so the append fires. -/
private def negState : St :=
  ⟨.record, .active, [], 0, some ⟨"acme/Rates/get", 1, "req-0"⟩⟩
private def appendIn : In :=
  .recorded ⟨"acme/Rates/get", 1, "req-0"⟩ (.success "ok")

/-- SES-001: an aborted session appends nothing. -/
def ses001 : TraceExcludes St In DecisionTag Status where
  id := "SES-001"
  sentence := "In an aborted session, no step ever emits an occurrence-append decision — a record-mode append failure aborts the session structurally, nothing appends past the failure, and histories stay truthful prefixes, never gapped subsequences."
  modeOf := SessionState.status
  guarded := .aborted
  decisions := fun s i => (reduce s i).decisions.map Decision.tag
  bad := .occurrenceAppended
  law := fun s i h => by
    simp [SES_001_aborted_emits_nothing s i h]
  posState := posState
  posInput := appendIn
  pos_mode := rfl
  negState := negState
  negInput := appendIn
  neg_mode := by decide
  neg_bad := by decide

end Effects.Conformance

import Effects.Conformance.Schema.FailClosed
import Effects.Conformance.Rider
import Effects.Replay.Run

/-!
# SES-003 — record-mode delegation is exclusive and outcome-solicited

FAIL-CLOSED over the reducer with the solicitation protocol as the
hypothesis: an invocation is solicited when no delegation is outstanding,
and a recorded outcome is solicited when the outstanding delegation
registered exactly that invocation. When solicitation fails the step
rejects with a typed category — delegation outstanding, or unsolicited
outcome — and the history length is unchanged, so interleaved live calls
and cross-wired outcomes can never corrupt a history: lawful record runs
append in invocation order — the run half is carried structurally by the
sentence rider below. The positive kit is an
invocation arriving while another is outstanding; the negative kit is the
same invocation arriving into a clean state, which delegates.
-/

namespace Effects.Conformance

open Effects.Replay

private abbrev St := SessionState String String String String
private abbrev In := Input String String String String

private def invA : Invocation String String := ⟨"acme/Rates/get", 1, "req-0"⟩
private def invB : Invocation String String := ⟨"acme/Fx/list", 1, "req-1"⟩

private def outstanding : St := ⟨.record, .active, [], 0, some invA⟩
private def clean : St := ⟨.record, .active, [], 0, none⟩

/-- The solicitation hypothesis: what the record-mode protocol permits. -/
private def solicited (s : St) (i : In) : Prop :=
  match i with
  | .invoke _ => s.pending = none
  | .recorded inv _ => s.pending = some inv
  | .appendFailed => True
  | .complete _ => True

/-- SES-003: unsolicited record-mode steps fail closed. -/
def ses003 : FailClosed St In (StepResult String String) where
  id := "SES-003"
  sentence := "When record-mode delegation is not solicited — an invocation while one is outstanding, or a recorded outcome without or beside its outstanding invocation — the step rejects with a typed category and the history length is unchanged; delegation is exclusive, outcomes append only as solicited, and lawful record runs append in invocation order."
  wf := fun s => s.WF ∧ s.status = .active ∧ s.mode = .record
  hyp := solicited
  step := fun s i => ((reduce s i).result, (reduce s i).state)
  isRejection := StepResult.isRejection
  measure := fun s => s.history.length
  law_reject := fun s i hwf hn => by
    cases i with
    | invoke inv =>
      cases hp : s.pending with
      | none => exact absurd hp hn
      | some p =>
        rw [SES_003_interleaved_invoke_rejects s inv p hwf.2.1 hwf.2.2 hp]
        rfl
    | recorded inv out =>
      rw [SES_003_unsolicited_outcome_rejects s inv out hwf.2.1 hwf.2.2 hn]
      rfl
    | appendFailed => exact absurd trivial hn
    | complete t => exact absurd trivial hn
  law_frozen := fun s i hwf hn => by
    cases i with
    | invoke inv =>
      cases hp : s.pending with
      | none => exact absurd hp hn
      | some p =>
        rw [SES_003_interleaved_invoke_rejects s inv p hwf.2.1 hwf.2.2 hp]
        rfl
    | recorded inv out =>
      rw [SES_003_unsolicited_outcome_rejects s inv out hwf.2.1 hwf.2.2 hn]
      rfl
    | appendFailed => exact absurd trivial hn
    | complete t => exact absurd trivial hn
  posState := outstanding
  posInput := .invoke invB
  pos_wf := ⟨by decide, rfl, rfl⟩
  pos_nohyp := fun h => nomatch h
  negState := clean
  negInput := .invoke invA
  neg_hyp := rfl

/-- The run half of the sentence: over any solicited call-pair list from
a clean active record state, the whole run appends exactly those
entries in invocation order, cursor pinned, pending clear. -/
def ses003OrderRider : SentenceRider :=
  .of "SES-003" "lawful record runs append in invocation order"
    (@SES_003_solicited_run_appends_in_order)

end Effects.Conformance

import Effects.Replay.Relation

/-!
# The obligation laws

One theorem per obligation clause, named by ledger ID (the one-name rule:
ledger ID = theorem name = manifest family = suite test name). The schema
instances cite these; nothing here is a new statement — each theorem is
the Lean half of its plan-ledger row.
-/

namespace Effects.Replay

variable {Op Req Val Err : Type} [DecidableEq Op] [DecidableEq Req]

/-! ## SES-001 — the structural abort emits and appends nothing -/

/-- An aborted session emits NO decisions at all — in particular, nothing
appends past a failure, so histories stay truthful prefixes. -/
theorem SES_001_aborted_emits_nothing (s : SessionState Op Req Val Err)
    (i : Input Op Req Val Err) (h : s.status = .aborted) :
    (reduce s i).decisions = [] := by
  simp [reduce, h, absorb]

/-- The record-mode append DOES emit its occurrence decision — the guard
in SES-001 is not vacuous. -/
theorem record_append_emits_occurrence (s : SessionState Op Req Val Err)
    (inv : Invocation Op Req) (out : Outcome Val Err)
    (ha : s.status = .active) (hm : s.mode = .record)
    (hp : s.pending = some inv) :
    (reduce s (.recorded inv out)).decisions
      = [.occurrenceAppended inv.op s.cursor] := by
  simp [reduce, ha, hm, appendRecord, hp]

/-! ## RPL-002 — replay-mode traces never select live delegation -/

theorem RPL_002_replay_excludes_live_delegation
    (s : SessionState Op Req Val Err) (i : Input Op Req Val Err)
    (hm : s.mode = .replay) :
    DecisionTag.liveDelegation ∉ (reduce s i).decisions.map Decision.tag := by
  cases hst : s.status with
  | aborted => simp [reduce, hst, absorb]
  | active =>
    cases i with
    | invoke inv =>
      simp only [reduce, hst, hm]
      cases he : s.history[s.cursor]? with
      | none => simp [invokeReplay, he, rejectStep, Decision.tag]
      | some e =>
        by_cases hop : e.op = inv.op
        · by_cases hrev : e.revision = inv.revision
          · by_cases hreq : e.request = inv.request
            · simp [invokeReplay, he, hop, hrev, hreq, Decision.tag]
            · simp [invokeReplay, he, hop, hrev, hreq, rejectStep,
                Decision.tag]
          · simp [invokeReplay, he, hop, hrev, rejectStep, Decision.tag]
        · simp [invokeReplay, he, hop, rejectStep, Decision.tag]
    | recorded inv out => simp [reduce, hst, hm, absorb]
    | appendFailed => simp [reduce, hst, hm, absorb]
    | complete t =>
      simp only [reduce, hst, hm]
      by_cases hc : s.cursor = s.history.length
      · simp [completeStep, hc, Decision.tag]
      · simp [completeStep, hc, Decision.tag]

/-- Record mode DOES delegate on an invocation — RPL-002's mode guard is
not vacuous. -/
theorem record_invoke_delegates (s : SessionState Op Req Val Err)
    (inv : Invocation Op Req) (ha : s.status = .active)
    (hm : s.mode = .record) (hp : s.pending = none) :
    (reduce s (.invoke inv)).decisions = [.liveDelegation inv.op s.cursor] := by
  simp [reduce, ha, hm, invokeRecord, hp]

/-! ## RPL-003 — matching consumes exactly the permitted occurrence -/

theorem RPL_003_match_consumes_exactly_one
    (s : SessionState Op Req Val Err) (inv : Invocation Op Req)
    (ha : s.status = .active) (hm : s.mode = .replay)
    (h : MatchesAt s inv) :
    (reduce s (.invoke inv)).state.cursor = s.cursor + 1 := by
  obtain ⟨e, he, hop, hrev, hreq⟩ := h
  simp [reduce, ha, hm, invokeReplay, he, hop, hrev, hreq]

/-! ## RPL-004 — mismatch fails closed -/

theorem RPL_004_mismatch_rejects (s : SessionState Op Req Val Err)
    (inv : Invocation Op Req) (ha : s.status = .active)
    (hm : s.mode = .replay) (h : ¬ MatchesAt s inv) :
    (reduce s (.invoke inv)).result.isRejection = true := by
  simp only [reduce, ha, hm]
  cases he : s.history[s.cursor]? with
  | none => simp [invokeReplay, he, rejectStep, StepResult.isRejection]
  | some e =>
    by_cases hop : e.op = inv.op
    · by_cases hrev : e.revision = inv.revision
      · by_cases hreq : e.request = inv.request
        · exact absurd ⟨e, he, hop, hrev, hreq⟩ h
        · simp [invokeReplay, he, hop, hrev, hreq, rejectStep,
            StepResult.isRejection]
      · simp [invokeReplay, he, hop, hrev, rejectStep,
          StepResult.isRejection]
    · simp [invokeReplay, he, hop, rejectStep, StepResult.isRejection]

/-- Failing closed consumes nothing: the cursor is frozen on every
request-side rejection. -/
theorem RPL_004_mismatch_frozen (s : SessionState Op Req Val Err)
    (inv : Invocation Op Req) (ha : s.status = .active)
    (hm : s.mode = .replay) (h : ¬ MatchesAt s inv) :
    (reduce s (.invoke inv)).state.cursor = s.cursor := by
  simp only [reduce, ha, hm]
  cases he : s.history[s.cursor]? with
  | none => simp [invokeReplay, he, rejectStep]
  | some e =>
    by_cases hop : e.op = inv.op
    · by_cases hrev : e.revision = inv.revision
      · by_cases hreq : e.request = inv.request
        · exact absurd ⟨e, he, hop, hrev, hreq⟩ h
        · simp [invokeReplay, he, hop, hrev, hreq, rejectStep]
      · simp [invokeReplay, he, hop, hrev, rejectStep]
    · simp [invokeReplay, he, hop, rejectStep]

/-! ## RPL-005 — completion rejects an unconsumed suffix, carrying the
program's terminal so far -/

theorem RPL_005_suffix_rejects_with_terminal
    (s : SessionState Op Req Val Err) (t : Terminal Val Err)
    (ha : s.status = .active) (hc : ¬ s.cursor = s.history.length) :
    reduce s (.complete t) =
      { result := .outcome (.rejected .unconsumedSuffix s.cursor (some t))
        state := { s with status := .aborted, pending := none }
        decisions := [.typedRejection .unconsumedSuffix s.cursor] } := by
  cases hm : s.mode <;> simp [reduce, ha, hm, completeStep, hc]

/-- Completion at the history length completes with the terminal — the
rejection above is not universal. -/
theorem complete_at_end (s : SessionState Op Req Val Err)
    (t : Terminal Val Err) (ha : s.status = .active)
    (hc : s.cursor = s.history.length) :
    reduce s (.complete t) =
      { result := .outcome (.completed t), state := s
        decisions := [.completed s.cursor] } := by
  cases hm : s.mode <;> simp [reduce, ha, hm, completeStep, hc]

/-! ## CMP-002 — identical requests remain separate occurrences -/

/-- Appending a solicited occurrence advances the position by one,
regardless of content — position is the occurrence identity, so identical
invocation content never collapses occurrences. -/
theorem CMP_002_append_advances_position (s : SessionState Op Req Val Err)
    (inv : Invocation Op Req) (out : Outcome Val Err)
    (ha : s.status = .active) (hm : s.mode = .record)
    (hp : s.pending = some inv) :
    (reduce s (.recorded inv out)).state.cursor = s.cursor + 1 := by
  simp [reduce, ha, hm, appendRecord, hp]

/-- The solicited append preserves the active record flags and clears
the registration, so call pairs can be appended in sequence. -/
theorem append_preserves_flags (s : SessionState Op Req Val Err)
    (inv : Invocation Op Req) (out : Outcome Val Err)
    (ha : s.status = .active) (hm : s.mode = .record)
    (hp : s.pending = some inv) :
    (reduce s (.recorded inv out)).state.status = .active ∧
      (reduce s (.recorded inv out)).state.mode = .record ∧
      (reduce s (.recorded inv out)).state.pending = none := by
  simp [reduce, ha, hm, appendRecord, hp]

/-! ## SES-003 — record-mode delegation is exclusive and outcome-solicited -/

/-- SES-003, exclusivity half: a second invocation while a delegation is
outstanding is a typed rejection. -/
theorem SES_003_interleaved_invoke_rejects (s : SessionState Op Req Val Err)
    (inv p : Invocation Op Req) (ha : s.status = .active)
    (hm : s.mode = .record) (hp : s.pending = some p) :
    reduce s (.invoke inv) = rejectStep s .delegationOutstanding := by
  simp [reduce, ha, hm, invokeRecord, hp]

/-- SES-003, solicitation half: an outcome nobody solicited — none
outstanding, or a different invocation than registered — is a typed
rejection. -/
theorem SES_003_unsolicited_outcome_rejects (s : SessionState Op Req Val Err)
    (inv : Invocation Op Req) (out : Outcome Val Err)
    (ha : s.status = .active) (hm : s.mode = .record)
    (hp : ¬ s.pending = some inv) :
    reduce s (.recorded inv out) = rejectStep s .unsolicitedOutcome := by
  simp only [reduce, ha, hm, appendRecord]
  cases hpe : s.pending with
  | none => rfl
  | some p =>
    have hne : ¬ p = inv := fun hpi => hp (by rw [hpe, hpi])
    dsimp only
    rw [if_neg hne]

/-- SES-003, inversion: an append happened only for the invocation the
outstanding delegation registered — nothing unsolicited enters a
history. -/
theorem SES_003_append_solicited (s : SessionState Op Req Val Err)
    (inv : Invocation Op Req) (out : Outcome Val Err)
    (h : (reduce s (.recorded inv out)).result = .appended) :
    s.status = .active ∧ s.mode = .record ∧ s.pending = some inv := by
  cases hst : s.status with
  | aborted =>
    simp only [reduce, hst, absorb] at h
    exact nomatch h
  | active =>
    cases hm : s.mode with
    | replay =>
      simp only [reduce, hst, hm, absorb] at h
      exact nomatch h
    | record =>
      refine ⟨rfl, rfl, ?_⟩
      simp only [reduce, hst, hm, appendRecord] at h
      cases hpe : s.pending with
      | none =>
        simp only [hpe, rejectStep] at h
        exact nomatch h
      | some p =>
        by_cases hpi : p = inv
        · rw [hpi]
        · simp only [hpe, if_neg hpi, rejectStep] at h
          exact nomatch h

/-! ## SES-002 — every step preserves session-state well-formedness -/

omit [DecidableEq Op] [DecidableEq Req] in
/-- A typed rejection preserves well-formedness: cursor and history are
frozen, the mode is kept, and the outstanding delegation is cleared. -/
private theorem rejectStep_preserves_wf (s : SessionState Op Req Val Err)
    (c : MismatchCategory) (h : s.WF) : (rejectStep s c).state.WF := by
  obtain ⟨hle, hrec, _⟩ := h
  exact ⟨hle, fun hr => hrec hr, fun _ => rfl⟩

theorem SES_002_reduce_preserves_wf (s : SessionState Op Req Val Err)
    (i : Input Op Req Val Err) (h : s.WF) : (reduce s i).state.WF := by
  obtain ⟨hle, hrec, hrep⟩ := h
  cases hst : s.status with
  | aborted =>
    simp only [reduce, hst, absorb]
    exact ⟨hle, hrec, hrep⟩
  | active =>
    cases hm : s.mode with
    | record =>
      cases i with
      | invoke inv =>
        simp only [reduce, hst, hm, invokeRecord]
        cases hp : s.pending with
        | none =>
          refine ⟨hle, fun hr => ?_, fun hpp => ?_⟩
          · first
              | exact hrec hr
              | exact hrec hm
          · first
              | exact nomatch hpp
              | exact absurd (hm ▸ hpp) (by decide)
        | some p =>
          exact rejectStep_preserves_wf s _ ⟨hle, hrec, hrep⟩
      | recorded inv out =>
        have hcur := hrec hm
        simp only [reduce, hst, hm, appendRecord]
        cases hp : s.pending with
        | none =>
          exact rejectStep_preserves_wf s _ ⟨hle, hrec, hrep⟩
        | some p =>
          by_cases hpi : p = inv
          · simp only [if_pos hpi]
            refine ⟨?_, fun _ => ?_, fun _ => ?_⟩
            · dsimp only
              simp only [List.length_append, List.length_cons,
                List.length_nil]
              omega
            · dsimp only
              simp only [List.length_append, List.length_cons,
                List.length_nil]
              omega
            · rfl
          · simp only [if_neg hpi]
            exact rejectStep_preserves_wf s _ ⟨hle, hrec, hrep⟩
      | appendFailed =>
        simp only [reduce, hst, hm, abortRecord]
        refine ⟨hle, fun hr => ?_, fun _ => rfl⟩
        first
          | exact hrec hr
          | exact hrec hm
      | complete t =>
        simp only [reduce, hst, hm, completeStep]
        by_cases hc : s.cursor = s.history.length
        · simp only [if_pos hc]
          exact ⟨hle, hrec, hrep⟩
        · simp only [if_neg hc]
          refine ⟨hle, fun hr => ?_, fun _ => rfl⟩
          first
            | exact hrec hr
            | exact hrec hm
    | replay =>
      cases i with
      | invoke inv =>
        simp only [reduce, hst, hm]
        cases he : s.history[s.cursor]? with
        | none =>
          simp only [invokeReplay, he]
          exact rejectStep_preserves_wf s _ ⟨hle, hrec, hrep⟩
        | some e =>
          have hlt : s.cursor < s.history.length :=
            (List.getElem?_eq_some_iff.mp he).1
          by_cases hop : e.op = inv.op
          · by_cases hrev : e.revision = inv.revision
            · by_cases hreq : e.request = inv.request
              · simp only [invokeReplay, he, if_pos hop, if_pos hrev,
                  if_pos hreq]
                refine ⟨?_, fun hr => ?_, fun _ => ?_⟩
                · dsimp only
                  omega
                · simp [hm] at hr
                · first
                    | exact hrep hm
                    | exact hrep rfl
              · simp only [invokeReplay, he, if_pos hop, if_pos hrev,
                  if_neg hreq]
                exact rejectStep_preserves_wf s _ ⟨hle, hrec, hrep⟩
            · simp only [invokeReplay, he, if_pos hop, if_neg hrev]
              exact rejectStep_preserves_wf s _ ⟨hle, hrec, hrep⟩
          · simp only [invokeReplay, he, if_neg hop]
            exact rejectStep_preserves_wf s _ ⟨hle, hrec, hrep⟩
      | recorded inv out =>
        simp only [reduce, hst, hm, absorb]
        exact ⟨hle, hrec, hrep⟩
      | appendFailed =>
        simp only [reduce, hst, hm, absorb]
        exact ⟨hle, hrec, hrep⟩
      | complete t =>
        simp only [reduce, hst, hm, completeStep]
        by_cases hc : s.cursor = s.history.length
        · simp only [if_pos hc]
          exact ⟨hle, hrec, hrep⟩
        · simp only [if_neg hc]
          refine ⟨hle, fun hr => ?_, fun _ => rfl⟩
          first
            | exact nomatch hr
            | exact absurd (hm ▸ hr) (by decide)

end Effects.Replay

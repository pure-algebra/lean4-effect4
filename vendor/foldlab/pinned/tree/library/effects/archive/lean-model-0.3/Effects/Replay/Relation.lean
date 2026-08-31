import Effects.Replay.Reducer

/-!
# The derived transition relation and its agreement

`Step` is the relational reading of the reducer: one constructor per rule,
premises stated as propositions rather than control flow. The agreement
theorem (`step_iff_reduce`) proves the relation and the function present
the same transition system; determinism (`step_deterministic`) — replay is
deterministic for a fixed admitted state and input — follows from
agreement because the reducer is a function. This is the RPL-001
substance: determinism holds by carrier construction, and the relation is
the reviewable rule-per-rule statement of what that carrier does.
-/

namespace Effects.Replay

variable {Op Req Val Err : Type} [DecidableEq Op] [DecidableEq Req]

/-- The transition relation, rule per rule. -/
inductive Step :
    SessionState Op Req Val Err → Input Op Req Val Err →
    StepOut Op Req Val Err → Prop where
  /-- An aborted session absorbs every input. -/
  | absorbAborted {s : SessionState Op Req Val Err}
      {i : Input Op Req Val Err} (h : s.status = .aborted) :
      Step s i (absorb s)
  /-- Record mode registers the outstanding delegation for an invocation
  when none is outstanding. -/
  | recordDelegates {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req}
      (ha : s.status = .active) (hm : s.mode = .record)
      (hp : s.pending = none) :
      Step s (.invoke inv)
        { result := .delegated
          state := { s with pending := some inv }
          decisions := [.liveDelegation inv.op s.cursor] }
  /-- Record mode refuses an invocation while a delegation is
  outstanding — delegation is exclusive. -/
  | recordRefusesInterleaved {s : SessionState Op Req Val Err}
      {inv p : Invocation Op Req}
      (ha : s.status = .active) (hm : s.mode = .record)
      (hp : s.pending = some p) :
      Step s (.invoke inv) (rejectStep s .delegationOutstanding)
  /-- Record mode appends the occurrence its outstanding delegation
  solicited, clearing the registration. -/
  | recordAppends {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req} {out : Outcome Val Err}
      (ha : s.status = .active) (hm : s.mode = .record)
      (hp : s.pending = some inv) :
      Step s (.recorded inv out)
        { result := .appended
          state := { s with
                     pending := none,
                     history := s.history ++ [inv.entry out],
                     cursor := s.cursor + 1 }
          decisions := [.occurrenceAppended inv.op s.cursor] }
  /-- Record mode refuses an outcome nobody solicited — none outstanding,
  or a different invocation than the one registered. -/
  | recordRefusesUnsolicited {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req} {out : Outcome Val Err}
      (ha : s.status = .active) (hm : s.mode = .record)
      (hp : ¬ s.pending = some inv) :
      Step s (.recorded inv out) (rejectStep s .unsolicitedOutcome)
  /-- Record mode aborts structurally when the append is refused. -/
  | recordAborts {s : SessionState Op Req Val Err}
      (ha : s.status = .active) (hm : s.mode = .record) :
      Step s .appendFailed (abortRecord s)
  /-- Replay substitutes the recorded outcome when the entry at the cursor
  matches the invocation, consuming exactly that occurrence. -/
  | replaySubstitutes {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req} {e : Entry Op Req Val Err}
      (ha : s.status = .active) (hm : s.mode = .replay)
      (he : s.history[s.cursor]? = some e) (hmt : e.matches inv) :
      Step s (.invoke inv)
        { result := .substituted e.outcome
          state := { s with cursor := s.cursor + 1 }
          decisions := [.recordedSubstitution inv.op s.cursor,
                        .historyConsumed s.cursor] }
  /-- Replay rejects when the history is exhausted at the cursor. -/
  | replayExhausted {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req}
      (ha : s.status = .active) (hm : s.mode = .replay)
      (he : s.history[s.cursor]? = none) :
      Step s (.invoke inv) (rejectStep s .historyExhausted)
  /-- Replay rejects on operation identity disagreement. -/
  | replayOperationMismatch {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req} {e : Entry Op Req Val Err}
      (ha : s.status = .active) (hm : s.mode = .replay)
      (he : s.history[s.cursor]? = some e) (hop : ¬ e.op = inv.op) :
      Step s (.invoke inv) (rejectStep s .operationMismatch)
  /-- Replay rejects on revision disagreement at an agreeing operation. -/
  | replayRevisionMismatch {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req} {e : Entry Op Req Val Err}
      (ha : s.status = .active) (hm : s.mode = .replay)
      (he : s.history[s.cursor]? = some e) (hop : e.op = inv.op)
      (hrev : ¬ e.revision = inv.revision) :
      Step s (.invoke inv) (rejectStep s .revisionMismatch)
  /-- Replay rejects on request-content disagreement at an agreeing
  operation and revision. -/
  | replayRequestMismatch {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req} {e : Entry Op Req Val Err}
      (ha : s.status = .active) (hm : s.mode = .replay)
      (he : s.history[s.cursor]? = some e) (hop : e.op = inv.op)
      (hrev : e.revision = inv.revision)
      (hreq : ¬ e.request = inv.request) :
      Step s (.invoke inv) (rejectStep s .requestMismatch)
  /-- Replay absorbs the record-only outcome-arrival input. -/
  | replayAbsorbsRecorded {s : SessionState Op Req Val Err}
      {inv : Invocation Op Req} {out : Outcome Val Err}
      (ha : s.status = .active) (hm : s.mode = .replay) :
      Step s (.recorded inv out) (absorb s)
  /-- Replay absorbs the record-only append-failure input. -/
  | replayAbsorbsAppendFailed {s : SessionState Op Req Val Err}
      (ha : s.status = .active) (hm : s.mode = .replay) :
      Step s .appendFailed (absorb s)
  /-- Completion succeeds in either mode exactly at the history length. -/
  | completes {s : SessionState Op Req Val Err} {t : Terminal Val Err}
      (ha : s.status = .active) :
      Step s (.complete t) (completeStep s t)

/-- The reducer realizes the relation: every state and input step to the
reducer's output. -/
theorem step_reduce (s : SessionState Op Req Val Err)
    (i : Input Op Req Val Err) : Step s i (reduce s i) := by
  cases hst : s.status with
  | aborted =>
    simp only [reduce, hst]
    exact .absorbAborted hst
  | active =>
    cases hm : s.mode with
    | record =>
      cases i with
      | invoke inv =>
        simp only [reduce, hst, hm]
        cases hp : s.pending with
        | none =>
          simp only [invokeRecord, hp]
          exact .recordDelegates hst hm hp
        | some p =>
          simp only [invokeRecord, hp]
          exact .recordRefusesInterleaved hst hm hp
      | recorded inv out =>
        simp only [reduce, hst, hm]
        cases hp : s.pending with
        | none =>
          simp only [appendRecord, hp]
          exact .recordRefusesUnsolicited hst hm
            (by rw [hp]; exact fun h => nomatch h)
        | some p =>
          by_cases hpi : p = inv
          · subst hpi
            simp only [appendRecord, hp]
            exact .recordAppends hst hm hp
          · simp only [appendRecord, hp, if_neg hpi]
            exact .recordRefusesUnsolicited hst hm
              (by rw [hp]; exact fun h => hpi (Option.some.inj h))
      | appendFailed =>
        simp only [reduce, hst, hm]
        exact .recordAborts hst hm
      | complete t =>
        simp only [reduce, hst, hm]
        exact .completes hst
    | replay =>
      cases i with
      | invoke inv =>
        simp only [reduce, hst, hm]
        cases he : s.history[s.cursor]? with
        | none =>
          simp only [invokeReplay, he]
          exact .replayExhausted hst hm he
        | some e =>
          by_cases hop : e.op = inv.op
          · by_cases hrev : e.revision = inv.revision
            · by_cases hreq : e.request = inv.request
              · simp only [invokeReplay, he, if_pos hop, if_pos hrev,
                  if_pos hreq]
                exact .replaySubstitutes hst hm he ⟨hop, hrev, hreq⟩
              · simp only [invokeReplay, he, if_pos hop, if_pos hrev,
                  if_neg hreq]
                exact .replayRequestMismatch hst hm he hop hrev hreq
            · simp only [invokeReplay, he, if_pos hop, if_neg hrev]
              exact .replayRevisionMismatch hst hm he hop hrev
          · simp only [invokeReplay, he, if_neg hop]
            exact .replayOperationMismatch hst hm he hop
      | recorded inv out =>
        simp only [reduce, hst, hm]
        exact .replayAbsorbsRecorded hst hm
      | appendFailed =>
        simp only [reduce, hst, hm]
        exact .replayAbsorbsAppendFailed hst hm
      | complete t =>
        simp only [reduce, hst, hm]
        exact .completes hst

/-- The relation computes the reducer: a step's output IS the reducer's
output. -/
theorem step_eq_reduce {s : SessionState Op Req Val Err}
    {i : Input Op Req Val Err} {o : StepOut Op Req Val Err}
    (h : Step s i o) : reduce s i = o := by
  cases h with
  | absorbAborted hst => simp only [reduce, hst]
  | recordDelegates hst hm hp =>
    simp only [reduce, hst, hm, invokeRecord, hp]
  | recordRefusesInterleaved hst hm hp =>
    simp only [reduce, hst, hm, invokeRecord, hp]
  | recordAppends hst hm hp =>
    simp only [reduce, hst, hm, appendRecord, hp]
    split
    · rfl
    · rename_i hne
      first
        | exact absurd rfl hne
        | exact absurd trivial hne
  | recordRefusesUnsolicited hst hm hp =>
    rename_i inv out
    simp only [reduce, hst, hm, appendRecord]
    cases hpe : s.pending with
    | none => rfl
    | some p =>
      have hne : ¬ p = inv := fun hpi => hp (by rw [hpe, hpi])
      dsimp only
      rw [if_neg hne]
  | recordAborts hst hm => simp only [reduce, hst, hm]
  | replaySubstitutes hst hm he hmt =>
    obtain ⟨hop, hrev, hreq⟩ := hmt
    simp only [reduce, hst, hm, invokeReplay, he, if_pos hop, if_pos hrev,
      if_pos hreq]
  | replayExhausted hst hm he =>
    simp only [reduce, hst, hm, invokeReplay, he]
  | replayOperationMismatch hst hm he hop =>
    simp only [reduce, hst, hm, invokeReplay, he, if_neg hop]
  | replayRevisionMismatch hst hm he hop hrev =>
    simp only [reduce, hst, hm, invokeReplay, he, if_pos hop, if_neg hrev]
  | replayRequestMismatch hst hm he hop hrev hreq =>
    simp only [reduce, hst, hm, invokeReplay, he, if_pos hop, if_pos hrev,
      if_neg hreq]
  | replayAbsorbsRecorded hst hm => simp only [reduce, hst, hm]
  | replayAbsorbsAppendFailed hst hm => simp only [reduce, hst, hm]
  | completes hst =>
    cases hm : s.mode <;> simp only [reduce, hst, hm]

/-- Agreement: the relation and the reducer present the same transition
system. -/
theorem step_iff_reduce {s : SessionState Op Req Val Err}
    {i : Input Op Req Val Err} {o : StepOut Op Req Val Err} :
    Step s i o ↔ reduce s i = o :=
  ⟨step_eq_reduce, fun h => h ▸ step_reduce s i⟩

/-- Determinism: replay is deterministic for a fixed admitted state and
input — the RPL-001 statement, discharged by carrier construction. -/
theorem step_deterministic {s : SessionState Op Req Val Err}
    {i : Input Op Req Val Err} {o o' : StepOut Op Req Val Err}
    (h : Step s i o) (h' : Step s i o') : o = o' := by
  rw [← step_eq_reduce h, ← step_eq_reduce h']

end Effects.Replay

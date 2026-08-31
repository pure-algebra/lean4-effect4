import Effects.Replay.Session

/-!
# The pure replay reducer

One total function from state and input to result, successor state, and
emitted decisions. Every rule is a named helper so statements and proofs
work at one shallow layer each.

Inputs: `invoke` is a wrapped method's emitted invocation (both modes);
`recorded` carries a record-mode invocation together with the live outcome
the interpreter obtained, and appends the occurrence; `appendFailed` is
the interpreter's signal that the history store refused an append;
`complete` carries the program terminal. In replay mode `recorded` and
`appendFailed` cannot occur under the interpreter and are absorbed —
totality by explicit no-op, never by panic.

Rules of note:

- record-mode delegation is exclusive and outcome-solicited: `invoke`
  registers the outstanding invocation and a second `invoke` while one is
  outstanding is a typed rejection; `recorded` appends only the outcome
  its outstanding delegation solicited — none outstanding, or a different
  invocation than registered, is a typed rejection — so lawful record
  runs append in invocation order;
- an aborted session absorbs EVERY input and emits nothing — the
  structural session abort: nothing appends past a failure, so histories
  are truthful prefixes without a mutable poisoned flag;
- a replay mismatch is a typed rejection at the current position that
  freezes the cursor and aborts the session — terminal for the attempt,
  so live fallback is unexpressible downstream;
- the matching ladder checks operation, then revision, then request
  content, against the entry at the cursor — request-side compatibility;
  outcome-side admissibility is a distinct later check and no rule here
  emits `outcomeInadmissible` in this slice;
- completion is uniform in both modes: the program's terminal completes
  the session exactly when the cursor equals the history length;
  otherwise the unconsumed-suffix rejection carries the terminal so far.
-/

namespace Effects.Replay

/-- Reducer input. -/
inductive Input (Op Req Val Err : Type) where
  | invoke (inv : Invocation Op Req)
  | recorded (inv : Invocation Op Req) (out : Outcome Val Err)
  | appendFailed
  | complete (t : Terminal Val Err)

/-- Reducer result: what the caller of one step observes. -/
inductive StepResult (Val Err : Type) where
  | substituted (out : Outcome Val Err)
  | delegated
  | appended
  | rejected (category : MismatchCategory) (pos : Nat)
  | outcome (o : SessionOutcome Val Err)
  | aborted
  | absorbed
  deriving DecidableEq

/-- Whether a result is a typed rejection — at a step, or carried by the
completion outcome. -/
def StepResult.isRejection {Val Err : Type} : StepResult Val Err → Bool
  | .rejected _ _ => true
  | .outcome (.rejected _ _ _) => true
  | _ => false

/-- One step's output: result, successor state, emitted decisions. -/
structure StepOut (Op Req Val Err : Type) where
  result : StepResult Val Err
  state : SessionState Op Req Val Err
  decisions : List (Decision Op)

variable {Op Req Val Err : Type}

/-- Absorb an input: no result, no state change, no decisions. -/
def absorb (s : SessionState Op Req Val Err) : StepOut Op Req Val Err :=
  { result := .absorbed, state := s, decisions := [] }

/-- A typed rejection at the current position: the cursor and history are
frozen, any outstanding delegation is discarded, and the session aborts —
the mismatch is terminal for the attempt. -/
def rejectStep (s : SessionState Op Req Val Err) (c : MismatchCategory) :
    StepOut Op Req Val Err :=
  { result := .rejected c s.cursor
    state := { s with status := .aborted, pending := none }
    decisions := [.typedRejection c s.cursor] }

/-- Record mode, invocation: register the outstanding delegation and
request live execution; the occurrence is not claimed until the outcome
arrives. Delegation is exclusive — a second invocation while one is
outstanding is the interleaving the sequential protocol refuses. -/
def invokeRecord (s : SessionState Op Req Val Err) (inv : Invocation Op Req) :
    StepOut Op Req Val Err :=
  match s.pending with
  | some _ => rejectStep s .delegationOutstanding
  | none =>
    { result := .delegated
      state := { s with pending := some inv }
      decisions := [.liveDelegation inv.op s.cursor] }

/-- Record mode, outcome arrived: append the occurrence the outstanding
delegation solicited and clear it. An outcome nobody solicited — none
outstanding, or a different invocation than the one registered — is
refused; nothing unsolicited ever enters a history. -/
def appendRecord [DecidableEq Op] [DecidableEq Req]
    (s : SessionState Op Req Val Err) (inv : Invocation Op Req)
    (out : Outcome Val Err) : StepOut Op Req Val Err :=
  match s.pending with
  | none => rejectStep s .unsolicitedOutcome
  | some p =>
    if p = inv then
      { result := .appended
        state := { s with
                   pending := none,
                   history := s.history ++ [inv.entry out],
                   cursor := s.cursor + 1 }
        decisions := [.occurrenceAppended inv.op s.cursor] }
    else rejectStep s .unsolicitedOutcome

/-- Record mode, append refused: abort the session structurally; the
occurrence is NOT recorded, the outstanding delegation is discarded, and
nothing later will append. -/
def abortRecord (s : SessionState Op Req Val Err) : StepOut Op Req Val Err :=
  { result := .aborted, state := { s with status := .aborted, pending := none }
    decisions := [] }

/-- Completion, uniform in both modes: complete exactly when the cursor
equals the history length; otherwise the unconsumed-suffix rejection
carries the program's terminal so far. -/
def completeStep (s : SessionState Op Req Val Err) (t : Terminal Val Err) :
    StepOut Op Req Val Err :=
  if s.cursor = s.history.length then
    { result := .outcome (.completed t), state := s
      decisions := [.completed s.cursor] }
  else
    { result := .outcome (.rejected .unconsumedSuffix s.cursor (some t))
      state := { s with status := .aborted, pending := none }
      decisions := [.typedRejection .unconsumedSuffix s.cursor] }

variable [DecidableEq Op] [DecidableEq Req]

/-- Replay mode, invocation: the matching ladder against the entry at the
cursor — operation, then revision, then request content. -/
def invokeReplay (s : SessionState Op Req Val Err) (inv : Invocation Op Req) :
    StepOut Op Req Val Err :=
  match s.history[s.cursor]? with
  | none => rejectStep s .historyExhausted
  | some e =>
    if e.op = inv.op then
      if e.revision = inv.revision then
        if e.request = inv.request then
          { result := .substituted e.outcome
            state := { s with cursor := s.cursor + 1 }
            decisions := [.recordedSubstitution inv.op s.cursor,
                          .historyConsumed s.cursor] }
        else rejectStep s .requestMismatch
      else rejectStep s .revisionMismatch
    else rejectStep s .operationMismatch

/-- The pure replay reducer: total on every state and input. -/
def reduce (s : SessionState Op Req Val Err) (i : Input Op Req Val Err) :
    StepOut Op Req Val Err :=
  match s.status with
  | .aborted => absorb s
  | .active =>
    match s.mode, i with
    | .record, .invoke inv => invokeRecord s inv
    | .record, .recorded inv out => appendRecord s inv out
    | .record, .appendFailed => abortRecord s
    | .record, .complete t => completeStep s t
    | .replay, .invoke inv => invokeReplay s inv
    | .replay, .recorded _ _ => absorb s
    | .replay, .appendFailed => absorb s
    | .replay, .complete t => completeStep s t

/-- Request-side compatibility at the cursor: some entry sits there and
matches the invocation. The exact-consumption and fail-closed laws share
this hypothesis. -/
def MatchesAt (s : SessionState Op Req Val Err) (inv : Invocation Op Req) :
    Prop :=
  ∃ e, s.history[s.cursor]? = some e ∧ e.matches inv

instance (s : SessionState Op Req Val Err) (inv : Invocation Op Req) :
    Decidable (MatchesAt s inv) := by
  unfold MatchesAt
  match s.history[s.cursor]? with
  | none => exact .isFalse (by simp)
  | some e => exact decidable_of_iff (e.matches inv) (by simp)

end Effects.Replay

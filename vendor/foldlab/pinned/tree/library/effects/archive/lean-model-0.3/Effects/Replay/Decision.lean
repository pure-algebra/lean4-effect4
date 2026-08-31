/-!
# Mismatch categories and the decision trace

The eight ratified mismatch categories. Request-side, checked against the
entry at the cursor: operation mismatch, revision mismatch, request
mismatch, history exhausted. Completion-side: unconsumed suffix.
Outcome-side, checked at consumption: outcome inadmissible.
Protocol-side, checked in record mode: delegation outstanding (a second
invocation while one delegation is in flight — the interleaving the
sequential protocol refuses) and unsolicited outcome (a recorded outcome
that no outstanding delegation asked for, or that names a different
invocation than the one registered). There is deliberately no "order
mismatch" — it always manifests as a request-side case at the current
position — and CAS storage failures are a distinct typed family, never
folded in. `outcomeInadmissible` is emitted only when raw recorded
outcomes enter the model (a later slice); the constructor is present
because the category set is ratified caller-visible API.

The decision trace is the primary observable: the ordered decisions the
pure reducer emits. Whether a live adapter was requested is a derived
projection of the trace — `Decision.tag` composed over the trace — never
a separate Boolean oracle.
-/

namespace Effects.Replay

/-- The eight ratified mismatch categories. -/
inductive MismatchCategory where
  | operationMismatch
  | revisionMismatch
  | requestMismatch
  | historyExhausted
  | unconsumedSuffix
  | outcomeInadmissible
  | delegationOutstanding
  | unsolicitedOutcome
  deriving DecidableEq

/-- One reducer decision. `pos` fields carry the occurrence position the
decision concerns; `completed` carries how much history was consumed. -/
inductive Decision (Op : Type) where
  | liveDelegation (op : Op) (pos : Nat)
  | occurrenceAppended (op : Op) (pos : Nat)
  | recordedSubstitution (op : Op) (pos : Nat)
  | historyConsumed (pos : Nat)
  | typedRejection (category : MismatchCategory) (pos : Nat)
  | completed (consumed : Nat)
  deriving DecidableEq

/-- The payload-free decision tag: the projection the trace observations
and the trace-exclusion laws quantify over. -/
inductive DecisionTag where
  | liveDelegation
  | occurrenceAppended
  | recordedSubstitution
  | historyConsumed
  | typedRejection
  | completed
  deriving DecidableEq

def Decision.tag {Op : Type} : Decision Op → DecisionTag
  | .liveDelegation _ _ => .liveDelegation
  | .occurrenceAppended _ _ => .occurrenceAppended
  | .recordedSubstitution _ _ => .recordedSubstitution
  | .historyConsumed _ => .historyConsumed
  | .typedRejection _ _ => .typedRejection
  | .completed _ => .completed

end Effects.Replay

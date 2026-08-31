import Effects.Replay.Outcome

/-!
# Invocations and the flat history

An invocation is what a wrapped method emits: stable operation identity,
revision, and canonical request content. A history entry is one logical
operation occurrence: the invocation content plus its recorded outcome
envelope. The history is flat and ordered; occurrence identity is
structural position — under exact positional matching, position IS the
semantics, so no occurrence identifier field exists. Identical invocation
content never collapses occurrences: the store deduplicates request
nodes, the history keeps entries distinct by position.

Histories are truthful prefixes of what happened, never gapped
subsequences (the structural session abort in the reducer enforces this);
the converse — that every live action was recorded — is never claimed.
-/

namespace Effects.Replay

/-- One emitted invocation: operation identity, revision, canonical
request content. -/
structure Invocation (Op Req : Type) where
  op : Op
  revision : Nat
  request : Req
  deriving DecidableEq

/-- One recorded occurrence: the invocation content and its recorded
outcome envelope. Position in the history is the occurrence identity. -/
structure Entry (Op Req Val Err : Type) where
  op : Op
  revision : Nat
  request : Req
  outcome : Outcome Val Err
  deriving DecidableEq

/-- The entry an invocation would record with the given outcome. -/
def Invocation.entry {Op Req Val Err : Type} (inv : Invocation Op Req)
    (out : Outcome Val Err) : Entry Op Req Val Err :=
  ⟨inv.op, inv.revision, inv.request, out⟩

/-- Request-side compatibility of an invocation with a recorded entry:
operation, revision, and request content agree. Outcome-side
admissibility is a distinct check with a distinct category. -/
def Entry.matches {Op Req Val Err : Type} (e : Entry Op Req Val Err)
    (inv : Invocation Op Req) : Prop :=
  e.op = inv.op ∧ e.revision = inv.revision ∧ e.request = inv.request

instance {Op Req Val Err : Type} [DecidableEq Op] [DecidableEq Req]
    (e : Entry Op Req Val Err) (inv : Invocation Op Req) :
    Decidable (e.matches inv) := by
  unfold Entry.matches; infer_instance

end Effects.Replay

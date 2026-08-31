import Effects.Replay.Session

/-!
# The reified sequential program

A closed, terminating, sequential program over invocation leaves: `pure`
returns a value, `fail` raises the program's own typed failure, and
`invoke` emits one invocation and continues from the recorded outcome
envelope — the continuation receives BOTH channels, so recovery fires
exactly as it did live and re-raising is the continuation's choice, not
the carrier's.

The reification pattern is the event-syntax node of the pinned
Interaction Trees study material (`.reference/clones/InteractionTrees`),
inductive rather than coinductive because this slice models closed
terminating programs — the sequential-deterministic class the replay
survey names as the first slice
(`research/cas-effect-program-replay.md`). Continuations are meta-level
Lean functions and are model-internal: nothing serializes them (a
captured continuation is not a value snapshot — the Blaze warning). The
serializable first-order descriptor with a defunctionalized continuation
machine is the extraction report's later lane
(`research/docs/research/effect-runtime-ground-truth-extraction-scope.md`)
and enters through its own admission when it comes.
-/

namespace Effects.Replay

/-- A reified sequential program over invocation leaves. -/
inductive Prog (Op Req Val Err : Type) (α : Type) where
  /-- Return a value; consumes nothing. -/
  | pure (a : α)
  /-- The program's own typed failure. -/
  | fail (e : Err)
  /-- Emit one invocation and continue from its outcome envelope. -/
  | invoke (inv : Invocation Op Req)
      (k : Outcome Val Err → Prog Op Req Val Err α)

variable {Op Req Val Err : Type} {α β : Type}

/-- Sequential composition: graft the continuation at every return leaf.
Failure short-circuits — the continuation never runs. -/
def Prog.bind : Prog Op Req Val Err α → (α → Prog Op Req Val Err β) →
    Prog Op Req Val Err β
  | .pure a, f => f a
  | .fail e, _ => .fail e
  | .invoke inv k, f => .invoke inv fun out => (k out).bind f

instance : Monad (Prog Op Req Val Err) where
  pure := .pure
  bind := Prog.bind

end Effects.Replay

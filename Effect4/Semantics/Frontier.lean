import Effects.Flow.Block

/-!
# Semantics.Frontier

Owner: live, unanswered, and exhausted frontiers of a flow run.

A frontier is where a finite run stops without an outcome. Under DB-04
(`docs/DESIGN-BASIS.md`) fuel is an approximation, not a denotation: running
out of it is a live frontier, never a failure and never a refusal. Tape
exhaustion is the unanswered frontier. `stuck` names an unresolvable block,
variable, successor, or operation; admission makes it unreachable
(`Effect4.Flow.run_checked_not_stuck`).
-/

namespace Effect4

open Effects

/-- Why a finite run stopped without an outcome. -/
inductive Frontier where
  /-- The fuel ran out while about to enter `block`. -/
  | fuel (block : BlockId)
  /-- A `choose` at `site` found the tape exhausted. -/
  | unansweredDecision (site : DecisionId)
  /-- A block, variable, successor, or operation did not resolve. -/
  | stuck (block : BlockId)
deriving DecidableEq, Repr

end Effect4

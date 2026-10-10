import ProofGraph.Axioms
import ProofGraph.GoalTag

/-!
# Planned goals: a theorem's standing

A theorem's standing is read from its dependencies with goals as leaves (`standing`): open when it
is a goal, proved modulo the goals the walk stops at when it reaches one, and proved otherwise.
The goals themselves, their tag and the `proof_goal` command, are `ProofGraph.GoalTag`'s; this
module adds the walk (`ProofGraph.Axioms`), so only the tools import it. This reflection is
tooling only; it never enters stored program content.
-/
namespace ProofGraph
open Lean Meta

/-- The standing of a theorem, read from its dependencies with goals as leaves. -/
inductive Standing
  /-- the theorem is a goal -/
  | goal
  /-- the theorem reaches these goals and no other `sorry` -/
  | modulo (goals : Array Name)
  /-- the theorem reaches no goal -/
  | proved
  deriving Inhabited, BEq

def Standing.word : Standing → String
  | .goal => "goal"
  | .modulo _ => "modulo"
  | .proved => "proved"

/-- The axioms and the goals `name` reaches, goals as leaves, with the memo threaded through;
`none` only if the step budget ran out. -/
def reachedWithGoals (env : Environment) (name : Name) :
    StateM AxiomMemo (Option (Array Name × Array Name)) := do
  let some all ← reachedAxioms env name (isGoal env) | return none
  return some (all.filter (!isGoal env ·), all.filter (isGoal env ·))

/-- The standing of `name` and the axioms it reaches. -/
def standing (env : Environment) (name : Name) :
    StateM AxiomMemo (Option (Standing × Array Name)) := do
  let some (axioms, goals) ← reachedWithGoals env name | return none
  if isGoal env name then return some (.goal, axioms)
  if goals.isEmpty then return some (.proved, axioms)
  return some (.modulo (goals.qsort (·.toString < ·.toString)), axioms)

end ProofGraph

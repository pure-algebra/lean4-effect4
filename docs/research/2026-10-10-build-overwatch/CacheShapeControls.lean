import ProofGraph.ClosureAudit
import ProofGraph.Axioms

namespace CacheShapeControls
open Lean Elab Command ProofGraph

def before (n : Nat) : Nat → Bool :=
  let table := List.range n
  fun k => table.contains k

def inside (n k : Nat) : Bool :=
  let table := List.range n
  table.contains k

run_cmd liftTermElabM do
  let env ← getEnv
  let some (.defnInfo b) := env.find? ``before | throwError "missing before"
  let some (.defnInfo i) := env.find? ``inside | throwError "missing inside"
  unless (← Lean.Meta.isDefEq b.type i.type) do throwError "the types differ"
  let deps (ci : ConstantInfo) := (usedConstantsOf ci).qsort Name.lt
  unless deps (.defnInfo b) == deps (.defnInfo i) do throwError "the dependencies differ"
  unless exactAxioms env ``before == exactAxioms env ``inside do throwError "the axioms differ"
  unless !(letsBeforeClosure b.value).isEmpty && (letsBeforeClosure i.value).isEmpty do
    throwError "the shape distinction disappeared"

end CacheShapeControls

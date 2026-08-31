/-!
# Declared mutants

Mutants are never proof-bearing and never imported by the model; they exist
only to be executed by the mutation tasks. Quarantine is layout plus gate
grep: mutant instances live under `Effects/Mutants/` when the M3 slice lands
them, and `Effects/` model files never import that tree.
-/

namespace Effects.Conformance

/-- A declared mutant. `represents` is the plain-meaning statement of what
killing this mutant demonstrates; `attacks` names the obligation it targets. -/
structure Mutant (F : Type) where
  id : String
  attacks : String
  represents : String
  mutant : F

end Effects.Conformance

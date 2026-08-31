import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RPL003SkipAdvance

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- A substitution that consumes nothing: the cursor stays put after a
match. -/
def mutantReduce : RReducer := fun s i =>
  let o := reduce s i
  match o.result with
  | .substituted _ => { o with state := { o.state with cursor := s.cursor } }
  | _ => o

def mutant : Mutant RReducer where
  id := "RPL003_SkipAdvance"
  attacks := "RPL-003"
  represents := "Killing this mutant demonstrates the vectors notice a match that consumes zero occurrences — the same recorded outcome would answer forever."
  mutant := mutantReduce

end Effects.Mutants.RPL003SkipAdvance

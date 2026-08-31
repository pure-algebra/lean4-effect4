import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RPL004ConsumeOnMismatch

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- A rejection that consumes anyway: the cursor advances on mismatch. -/
def mutantReduce : RReducer := fun s i =>
  let o := reduce s i
  match o.result with
  | .rejected _ _ => { o with state := { o.state with cursor := s.cursor + 1 } }
  | _ => o

def mutant : Mutant RReducer where
  id := "RPL004_ConsumeOnMismatch"
  attacks := "RPL-004"
  represents := "Killing this mutant demonstrates the vectors notice a mismatch that fails open — consuming the occurrence it rejected instead of freezing the cursor."
  mutant := mutantReduce

end Effects.Mutants.RPL004ConsumeOnMismatch

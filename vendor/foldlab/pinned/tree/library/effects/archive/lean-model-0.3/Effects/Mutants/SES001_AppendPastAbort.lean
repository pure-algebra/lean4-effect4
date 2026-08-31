import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.SES001AppendPastAbort

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- An aborted session that keeps appending — the poisoned history the
structural abort exists to make unrepresentable. -/
def mutantReduce : RReducer := fun s i =>
  match s.status, i with
  | .aborted, .recorded inv out => appendRecord s inv out
  | _, _ => reduce s i

def mutant : Mutant RReducer where
  id := "SES001_AppendPastAbort"
  attacks := "SES-001"
  represents := "Killing this mutant demonstrates the vectors notice recording past an append failure — a history that is a gapped subsequence, not a truthful prefix."
  mutant := mutantReduce

end Effects.Mutants.SES001AppendPastAbort

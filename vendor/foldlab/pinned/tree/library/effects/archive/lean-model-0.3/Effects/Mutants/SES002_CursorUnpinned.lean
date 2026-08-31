import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.SES002CursorUnpinned

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- An append that advances the cursor by two, breaking the record-mode
pin to the history length. -/
def mutantReduce : RReducer := fun s i =>
  let o := reduce s i
  match o.result with
  | .appended => { o with state := { o.state with cursor := s.cursor + 2 } }
  | _ => o

def mutant : Mutant RReducer where
  id := "SES002_CursorUnpinned"
  attacks := "SES-002"
  represents := "Killing this mutant demonstrates the vectors notice a step that breaks session-state well-formedness — the record-mode cursor detaches from the history length."
  mutant := mutantReduce

end Effects.Mutants.SES002CursorUnpinned

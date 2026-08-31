import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT002OversizeAccepted

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client whose budget checks are vacuous: every declaration fits. -/
def mutantStep : RStep :=
  Effects.Remote.step
    { vecParams with budgets := ⟨1000000, 1000000⟩ }

def mutant : Mutant RStep where
  id := "RMT002_OversizeAccepted"
  attacks := "RMT-002"
  represents := "Killing this mutant demonstrates the vectors notice a client that lets over-budget declarations through to hashing and decoding — the budget check is the denial-of-service boundary, and it must fire before any byte is inspected."
  mutant := mutantStep

end Effects.Mutants.RMT002OversizeAccepted

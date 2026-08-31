import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK006AcceptAnyRoot

open Effects.Conformance Effects.Conformance.Manifest

/-- A verifier that checks only the index bound and accepts any root —
the recomputation dropped. -/
def mutantVerify : VerifyFn := fun m n _ _ _ => decide (m < n)

def mutant : Mutant VerifyFn where
  id := "MRK006_AcceptAnyRoot"
  attacks := "MRK-006"
  represents := "Killing this mutant demonstrates the vectors notice a verifier that accepts without recomputing — the inclusion verifier accepts exactly the openings whose derived-side recomputation reaches the expected root."
  mutant := mutantVerify

end Effects.Mutants.MRK006AcceptAnyRoot

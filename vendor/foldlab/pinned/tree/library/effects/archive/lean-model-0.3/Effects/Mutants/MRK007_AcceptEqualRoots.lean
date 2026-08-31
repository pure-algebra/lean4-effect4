import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK007AcceptEqualRoots

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest
open Effects.Cas (Addr32)

/-- A consistency verifier that accepts whenever the two roots
coincide, skipping the reconstruction entirely. -/
def mutantVerify : ConsFn := fun m n oldRoot newRoot proof =>
  decide (oldRoot = newRoot) ||
    verifyConsistency merkleH m n oldRoot newRoot proof

def mutant : Mutant ConsFn where
  id := "MRK007_AcceptEqualRoots"
  attacks := "MRK-007"
  represents := "Killing this mutant demonstrates the vectors notice a consistency verifier that shortcuts on equal roots without reconstructing — a relation claimed by identity instead of proved by the size-derived rebuild."
  mutant := mutantVerify

end Effects.Mutants.MRK007AcceptEqualRoots

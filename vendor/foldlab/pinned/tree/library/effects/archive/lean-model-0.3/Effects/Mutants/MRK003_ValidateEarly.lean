import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK003ValidateEarly

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest

/-- A decoder that vouches for the length on every emission, not just
the final chunk's — bao's final-chunk requirement ignored. -/
def mutantStep : MStep := fun D s i =>
  let o := dstep D s i
  if o.decisions.any (fun d => match d with
      | .emitted _ _ => true
      | _ => false) then
    ⟨o.state, o.decisions ++ [.lengthValidated]⟩
  else o

def mutant : Mutant MStep where
  id := "MRK003_ValidateEarly"
  attacks := "MRK-003"
  represents := "Killing this mutant demonstrates the vectors notice a decoder that exposes the length before the final chunk validates — the declared length is vouched for exactly when the final chunk itself verifies against the root."
  mutant := mutantStep

end Effects.Mutants.MRK003ValidateEarly

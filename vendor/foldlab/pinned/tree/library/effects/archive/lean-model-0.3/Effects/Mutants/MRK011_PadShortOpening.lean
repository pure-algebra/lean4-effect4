import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK011PadShortOpening

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest

/-- An opening decoder that zero-pads short documents to the header
width and decodes them anyway — truncated proof material read as
authoritative zeros. -/
def mutantDecode : OpeningDecodeFn := fun b =>
  if b.length < 12 then
    decodeOpening? (b ++ List.replicate (12 - b.length) 0)
  else decodeOpening? b

def mutant : Mutant OpeningDecodeFn where
  id := "MRK011_PadShortOpening"
  attacks := "MRK-011"
  represents := "Killing this mutant demonstrates the vectors notice an opening decoder that accepts truncated documents by padding them — proof material parsed open instead of fail-closed."
  mutant := mutantDecode

end Effects.Mutants.MRK011PadShortOpening

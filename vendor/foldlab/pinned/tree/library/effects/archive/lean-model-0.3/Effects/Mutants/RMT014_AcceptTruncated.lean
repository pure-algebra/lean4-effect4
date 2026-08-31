import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT014AcceptTruncated

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A decoder that zero-pads short capability documents to length and
decodes them anyway — truncated control state read as authoritative
zeros. -/
def mutantDecode (bytes : List UInt8) : Option Limits :=
  decodeLimits? (bytes ++ List.replicate (8 - bytes.length) 0)

def mutant : Mutant (List UInt8 → Option Limits) where
  id := "RMT014_AcceptTruncated"
  attacks := "RMT-014"
  represents := "Killing this mutant demonstrates the vectors notice a decoder that accepts truncated capability documents by padding them — control state parsed open instead of fail-closed."
  mutant := mutantDecode

end Effects.Mutants.RMT014AcceptTruncated

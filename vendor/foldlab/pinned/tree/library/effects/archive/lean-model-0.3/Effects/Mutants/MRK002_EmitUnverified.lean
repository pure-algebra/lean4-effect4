import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK002EmitUnverified

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest

/-- A decoder that emits whatever chunk arrives for a leaf frame,
skipping the address verification entirely. -/
def mutantStep : MStep := fun D s i =>
  match s.status, s.stack, i with
  | .active, f :: rest, .chunkNode c =>
    if ¬ D.disjoint f ∧ f.count ≤ 1 then
      ⟨popped rest,
        if f.base + 1 = D.total then
          [.emitted f.base c, .lengthValidated]
        else [.emitted f.base c]⟩
    else dstep D s i
  | _, _, _ => dstep D s i

def mutant : Mutant MStep where
  id := "MRK002_EmitUnverified"
  attacks := "MRK-002"
  represents := "Killing this mutant demonstrates the vectors notice a decoder that emits unverified bytes — a chunk is emitted only in the branch where its leaf pre-image hashed to exactly the expected subtree address."
  mutant := mutantStep

end Effects.Mutants.MRK002EmitUnverified

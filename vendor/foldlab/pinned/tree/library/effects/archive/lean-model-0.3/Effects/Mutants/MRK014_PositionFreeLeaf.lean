import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK014PositionFreeLeaf

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest
open Effects.Cas (Bytes)

/-- A materializer whose leaves all declare index zero — position
binding dropped from the blob graph. -/
def mutantGraph (chunks : List Bytes) (base : Nat) :
    List Effects.Cas.Node × Effects.Cas.Addr32 :=
  if _h : chunks.length ≤ 1 then
    let c := chunkDataNode (chunks.headD [])
    let l := leafRefNode 0 (chunks.headD []).length (blobNodeAddr c)
    ([c, l], blobNodeAddr l)
  else
    let k := pow2Below chunks.length
    let left := mutantGraph (chunks.take k) base
    let right := mutantGraph (chunks.drop k) (base + k)
    let p := parentRefNode left.2 right.2
    (left.1 ++ right.1 ++ [p], blobNodeAddr p)
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

def mutant : Mutant BlobGraphFn where
  id := "MRK014_PositionFreeLeaf"
  attacks := "MRK-014"
  represents := "Killing this mutant demonstrates the vectors notice a blob materializer whose leaves drop the absolute index — position binding erased from the graph, so a reordered blob could reuse another position's leaves."
  mutant := mutantGraph

end Effects.Mutants.MRK014PositionFreeLeaf

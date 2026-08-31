import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK020FullWalk

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest
open Effects.Cas (Bytes Addr32)

/-- A walk that ignores the range and loads every node — the linear
read that makes a one-chunk slice cost the whole tree. -/
def mutantAccess (chunks : List Bytes) (base : Nat) (_lo _hi : Nat) :
    List Addr32 :=
  if _h : chunks.length ≤ 1 then
    let c := chunkDataNode (chunks.headD [])
    let l := leafRefNode base (chunks.headD []).length (blobNodeAddr c)
    [blobNodeAddr l, blobNodeAddr c]
  else
    let k := pow2Below chunks.length
    let left := blobTreeNodes (chunks.take k) base
    let right := blobTreeNodes (chunks.drop k) (base + k)
    let p := parentRefNode left.2 right.2
    blobNodeAddr p
      :: (mutantAccess (chunks.take k) base _lo _hi
        ++ mutantAccess (chunks.drop k) (base + k) _lo _hi)
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

def mutant : Mutant RangedAccessFn where
  id := "MRK020_FullWalk"
  attacks := "MRK-020"
  represents := "Killing this mutant demonstrates the vectors notice a reader that walks the whole tree for a ranged read — the access set, not a benchmark, is what convicts the linear walk."
  mutant := mutantAccess

end Effects.Mutants.MRK020FullWalk

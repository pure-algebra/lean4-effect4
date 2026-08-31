import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK005SkipEmitsGhost

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest

/-- A slice decoder that emits ghost bytes for skipped subtrees — a
slice serving bytes the whole decode would never emit at those
offsets. -/
def mutantStep : MStep := fun D s i =>
  match s.status, s.stack, i with
  | .active, f :: rest, .skipNode =>
    if D.disjoint f then
      ⟨popped rest, [.emitted f.base []]⟩
    else dstep D s i
  | _, _, _ => dstep D s i

def mutant : Mutant MStep where
  id := "MRK005_SkipEmitsGhost"
  attacks := "MRK-005"
  represents := "Killing this mutant demonstrates the vectors notice a slice decoder that emits bytes for skipped subtrees — a slice emits exactly what the whole decode would emit at those offsets, never more."
  mutant := mutantStep

end Effects.Mutants.MRK005SkipEmitsGhost

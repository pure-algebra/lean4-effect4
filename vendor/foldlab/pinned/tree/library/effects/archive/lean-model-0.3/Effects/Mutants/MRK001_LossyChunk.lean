import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK001LossyChunk

open Effects.Conformance Effects.Conformance.Manifest

/-- A chunker that silently drops its final chunk — the partition made
lossy, so rejoining loses the tail and a second root appears for the
same content. -/
def mutantChunk : ChunkFn := fun b => (realChunk b).dropLast

def mutant : Mutant ChunkFn where
  id := "MRK001_LossyChunk"
  attacks := "MRK-001"
  represents := "Killing this mutant demonstrates the vectors notice a chunker that loses bytes — chunking must be a lossless declared partition, with one root per recipe and content."
  mutant := mutantChunk

end Effects.Mutants.MRK001LossyChunk

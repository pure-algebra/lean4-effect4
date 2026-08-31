import Effects.Conformance.Schema.Codec
import Effects.Merkle.Chunk

/-!
# MRK-001 — chunking is a lossless declared partition

CODEC over the declared recipe: the content is the value, the chunk
list is the encoding. Rejoining restores the bytes exactly and chunking
is injective, so one root exists per (recipe, content); the checked
inverse accepts exactly the lists chunking produces — a rechunked or
padded list is rejected, never silently rejoined. Canonicalization is
the identity: every byte string is already canonical content.
-/

namespace Effects.Conformance

open Effects.Merkle
open Effects.Cas (Bytes)

/-- The kit recipe: chunk size four. -/
def mrkRecipe : Recipe := ⟨4, by omega⟩

/-- MRK-001: one chunk-tree root per declared recipe and content. -/
def mrk001 : Codec Bytes (List Bytes) where
  id := "MRK-001"
  sentence := "Chunking under the declared recipe is a lossless partition: rejoining the chunks restores the bytes exactly, two different contents never chunk alike, and the checked inverse accepts exactly the lists chunking produces — the recipe is declared, never inferred, so one root exists per recipe and content and no rechunk can mint a second identity."
  canon := id
  encode := mrkRecipe.chunk
  decode := mrkRecipe.unchunk?
  law_canon_idem := fun _ => rfl
  law_roundtrip := fun x => mrkRecipe.unchunk_chunk x
  law_inj := fun _ _ _ _ h => mrkRecipe.chunk_injective h
  law_exact := fun _ _ h => (mrkRecipe.unchunk_exact h).1
  posVal := [7, 7, 7, 7, 7]
  negBytes := [[], []]
  neg_rejects := by
    have hchunk : mrkRecipe.chunk [] = [[]] := by
      unfold Recipe.chunk chunkGo
      simp
    simp [Recipe.unchunk?, hchunk]

end Effects.Conformance

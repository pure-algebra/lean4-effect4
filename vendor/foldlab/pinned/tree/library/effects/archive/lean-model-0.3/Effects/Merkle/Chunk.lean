import Effects.Cas.Value

/-!
# Chunking — a lossless declared partition

The recipe is a declared parameter, never inferred from data: a positive
chunk size. Chunking splits bytes into full chunks with a final chunk of
at most the chunk size; empty input becomes one empty chunk (the bao
convention, so every content has at least one leaf). Rejoining restores
the bytes exactly — chunking is a partition, so one root exists per
(recipe, content) and no rechunk can mint a second identity. The
checked inverse accepts exactly the lists chunking produces.
-/

namespace Effects.Merkle

open Effects.Cas (Bytes)

/-- The declared chunking recipe: a positive chunk size. -/
structure Recipe where
  chunkSize : Nat
  size_pos : 0 < chunkSize

/-- Split bytes into chunks of the declared size; the final chunk is
whatever remains (possibly the whole input, possibly empty for empty
input). Total, and never returns an empty list. -/
def chunkGo (size : Nat) (hpos : 0 < size) (b : Bytes) : List Bytes :=
  if _h : b.length ≤ size then [b]
  else b.take size :: chunkGo size hpos (b.drop size)
termination_by b.length
decreasing_by simp only [List.length_drop]; omega

def Recipe.chunk (r : Recipe) (b : Bytes) : List Bytes :=
  chunkGo r.chunkSize r.size_pos b

theorem chunkGo_ne_nil (size : Nat) (hpos : 0 < size) (b : Bytes) :
    chunkGo size hpos b ≠ [] := by
  unfold chunkGo
  split <;> simp

theorem chunkGo_flatten (size : Nat) (hpos : 0 < size) (b : Bytes) :
    (chunkGo size hpos b).flatten = b := by
  unfold chunkGo
  split
  · simp
  · simp only [List.flatten_cons]
    rw [chunkGo_flatten size hpos (b.drop size)]
    exact List.take_append_drop size b
termination_by b.length
decreasing_by simp only [List.length_drop]; omega

/-- Rejoining the chunks restores the bytes: chunking is lossless. -/
theorem Recipe.chunk_flatten (r : Recipe) (b : Bytes) :
    (r.chunk b).flatten = b :=
  chunkGo_flatten r.chunkSize r.size_pos b

/-- Chunking is injective: the recipe mints one chunk list per content. -/
theorem Recipe.chunk_injective (r : Recipe) {a b : Bytes}
    (h : r.chunk a = r.chunk b) : a = b := by
  have := congrArg List.flatten h
  rwa [r.chunk_flatten, r.chunk_flatten] at this

/-- The checked inverse: accept exactly the lists chunking produces —
recompute the chunking of the joined bytes and compare. -/
def Recipe.unchunk? (r : Recipe) (chunks : List Bytes) : Option Bytes :=
  let b := chunks.flatten
  if r.chunk b = chunks then some b else none

theorem Recipe.unchunk_chunk (r : Recipe) (b : Bytes) :
    r.unchunk? (r.chunk b) = some b := by
  simp [Recipe.unchunk?, r.chunk_flatten b]

/-- Exactness: a successful un-chunk's input IS the chunking of its
result — the checked inverse accepts nothing chunking does not
produce. -/
theorem Recipe.unchunk_exact (r : Recipe) {chunks : List Bytes}
    {b : Bytes} (h : r.unchunk? chunks = some b) :
    chunks = r.chunk b ∧ b = chunks.flatten := by
  dsimp only [Recipe.unchunk?] at h
  split at h
  · rename_i heq
    injection h with h
    subst h
    exact ⟨heq.symm, rfl⟩
  · exact nomatch h

end Effects.Merkle

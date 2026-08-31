import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK012LenientTags

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest
open Effects.Cas (Addr32)
open Effects.Wire

/-- A lenient item reader that treats any unknown tag as a skip token
instead of rejecting. -/
def lenientItems (bs : List UInt8) : Option (List (DInput Addr32)) :=
  match bs with
  | [] => some []
  | t :: rest =>
    if t = 0 then (lenientItems rest).map (.skipNode :: ·)
    else if t = 1 then
      match hr : readNat32 rest with
      | none => none
      | some (len, r) =>
        if len ≤ r.length then
          (lenientItems (r.drop len)).map (.chunkNode (r.take len) :: ·)
        else none
    else if t = 2 then
      if h : 64 ≤ rest.length then
        (lenientItems (rest.drop 64)).map
          (.parentNode ⟨rest.take 32, by simp only [List.length_take]; omega⟩
            ⟨(rest.drop 32).take 32, by
              simp only [List.length_take, List.length_drop]; omega⟩ :: ·)
      else none
    else (lenientItems rest).map (.skipNode :: ·)
termination_by bs.length
decreasing_by
  · simp only [List.length_cons]
    omega
  · have hrest := (readNat32_some rest len r hr).1
    have hrlen : rest.length = 4 + r.length := by
      rw [hrest]
      simp only [nat32, List.length_append, List.length_cons,
        List.length_nil]
    simp only [List.length_drop, List.length_cons]
    omega
  · simp only [List.length_drop, List.length_cons]
    omega
  · simp only [List.length_cons]
    omega

/-- The stream decoder over the lenient reader. -/
def mutantDecode : StreamDecodeFn := fun bytes =>
  match readNat32 bytes with
  | none => none
  | some (total, r1) =>
    match readNat32 r1 with
    | none => none
    | some (lo, r2) =>
      match readNat32 r2 with
      | none => none
      | some (hi, r3) =>
        match lenientItems r3 with
        | none => none
        | some items => some (⟨total, lo, hi⟩, items)

def mutant : Mutant StreamDecodeFn where
  id := "MRK012_LenientTags"
  attacks := "MRK-012"
  represents := "Killing this mutant demonstrates the vectors notice a stream reader that treats unknown item tags as skips instead of rejecting — a forward-compatibility reflex that lets an attacker splice unverified structure into a proof stream."
  mutant := mutantDecode

end Effects.Mutants.MRK012LenientTags

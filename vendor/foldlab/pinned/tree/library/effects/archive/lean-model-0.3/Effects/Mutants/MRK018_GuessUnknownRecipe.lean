import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK018GuessUnknownRecipe

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest
open Effects.Wire

/-- A manifest reader that drops the recipe gate: any recipe
identifier is accepted and its semantics guessed. -/
def mutantDecode : List UInt8 → Option ManifestContent := fun bytes =>
  match readNat32 bytes with
  | none => none
  | some (recipeId, r1) =>
    match readNat64 r1 with
    | none => none
    | some (totalBytes, r2) =>
      match readNat32 r2 with
      | some (leafCount, []) => some ⟨recipeId, totalBytes, leafCount⟩
      | _ => none

def mutant : Mutant (List UInt8 → Option ManifestContent) where
  id := "MRK018_GuessUnknownRecipe"
  attacks := "MRK-018"
  represents := "Killing this mutant demonstrates the vectors notice a manifest reader that accepts an unregistered recipe identifier instead of failing closed — a reader guessing blob semantics it was never taught."
  mutant := mutantDecode

end Effects.Mutants.MRK018GuessUnknownRecipe

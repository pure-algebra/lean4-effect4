import Effects.Conformance.Manifest
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.CAS004UnsortedKeys

open Effects.Conformance Effects.Conformance.Manifest Effects.Conformance.Json

mutual

/-- A canonical renderer that emits object fields in declaration order,
skipping the codepoint sort — two writers of the same value diverge. -/
def mutantRender : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .int i => toString i
  | .str s => "\"" ++ escapeCompact s ++ "\""
  | .arr xs => "[" ++ String.intercalate "," (mutantItems xs) ++ "]"
  | .obj fields =>
    "{" ++
      String.intercalate "," ((mutantFields fields).map fun (k, s) =>
        "\"" ++ escapeCompact k ++ "\":" ++ s) ++
      "}"

def mutantItems : List Value → List String
  | [] => []
  | x :: rest => mutantRender x :: mutantItems rest

def mutantFields : List (String × Value) → List (String × String)
  | [] => []
  | (k, v) :: rest => (k, mutantRender v) :: mutantFields rest

end

def mutant : Mutant ValueRenderFn where
  id := "CAS004_UnsortedKeys"
  attacks := "CAS-004"
  represents := "Killing this mutant demonstrates the vectors notice a canonical renderer that keeps declaration order for object keys — without the codepoint sort, two writers of the same value produce different bytes and split its content identity."
  mutant := mutantRender

end Effects.Mutants.CAS004UnsortedKeys

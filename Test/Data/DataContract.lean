import Effect4.Data.Constructive
import Test.Data.ConstructiveAxiomReport

/-!
# Constructive standard library contract tests

Validates that constructive lemmas evaluate correctly and provide exact finite receipts
under .
-/

namespace Test.Data.DataContract

open Effect4.Constructive

-- Option bind and map guards
#guard (Option.bind (some 42) (fun x => some (x + 1))) = some 43
#guard (Option.map (· + 1) (some 42)) = some 43
#guard (Option.isSome (some 42)) = true
#guard (Option.isNone (none : Option Nat)) = true

-- Bool reflection guards
#guard ((true && false) == false)
#guard ((true || false) == true)
#guard ((!true) == false)

-- Decidable reflection guards
#guard (decide (2 + 2 = 4 ∧ 3 + 3 = 6)) = true
#guard (decide (2 + 2 = 4 ∨ 3 + 3 = 5)) = true

-- List guards
#guard [1, 2, 3].all (· > 0) = true
#guard [1, 2, 3].all (· > 2) = false
#guard [1, 2, 3].any (· == 2) = true
#guard [1, 2, 3].any (· == 5) = false
#guard [("a", 1), ("b", 2)].lookup "b" = some 2
#guard [("a", 1), ("b", 2)].lookup "c" = none

end Test.Data.DataContract

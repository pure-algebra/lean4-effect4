import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Store.Carrier.Fold

/-! A generated fold's family comes from every mutual sibling.
The same imported environment contains both value and type-expression folds. -/

namespace Effect4.Test.FoldFamilySelection
open Effect4.Program

mutual
def count (_value : Store.Val) : Ty → Nat
  | .tuple types => countList types
  | _ => 0
def countList : List Ty → Nat
  | [] => 0
  | ty :: rest => count .unit ty + countList rest
end

/-- error: fold_of: requested family Effect4.Store.Val is not shared by every member -/
#guard_msgs (error, substring := true) in
fold_of count (family := Effect4.Store.Val)

fold_of count

-- Both arguments name a generated family, but only an explicit choice is stable here.
def ambiguous (value : Store.Val) : Ty → Nat
  | .option ty => ambiguous value ty
  | _ => 0

/-- error: fold_of: Effect4.Test.FoldFamilySelection.ambiguous has ambiguous generated families -/
#guard_msgs (error, substring := true) in
fold_of ambiguous

fold_of ambiguous (family := Effect4.Program.Ty)

#print axioms count.eq_cata
#print axioms countList.eq_cata
#print axioms ambiguous.eq_cata

end Effect4.Test.FoldFamilySelection

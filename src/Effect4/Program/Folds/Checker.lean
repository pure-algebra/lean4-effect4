import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Program.Checker

/-!
# The checker as an `EffAlgebra`

`Checker.check`'s block (`Program/Checker.lean`) as one algebra over the program's family: the
accumulator shape, the environment, the path and the mode flags as the carriers' arguments
(`R .eff = TyEnv → List Nat → Except TypeRefusal EffTy`, `R .stmt = TyEnv → Bool → List Nat →
Except TypeRefusal StmtTy`, `R .stmts = TyEnv → Bool → Option (List Nat) → List Nat → Except
TypeRefusal GenTy`, `R .layerTerms = List Nat → Except TypeRefusal (List LayerTy)`). The hand
checker `effTy` and the hand blame `explainEff` reach the algebra through the agreement
(`Typing/Agreement.lean`) and this `eq_cata`.
-/

namespace Effect4.Program

fold_of Effect4.Program.Checker.check

end Effect4.Program

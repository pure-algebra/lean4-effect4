import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Program.Checker

/-!
# The fold checker as an `EffAlgebra`

`Checker.effTy`'s block (`Program/Checker.lean`) as one algebra over the program's family: the
accumulator shape, the environment and the mode flags as the carriers' arguments
(`R .eff = TyEnv → Option EffTy`, `R .stmt = TyEnv → Bool → Option StmtTy`,
`R .stmts = TyEnv → Bool → Bool → Option GenTy`, `R .layerTerms = Option (List LayerTy)`).
The hand checker `effTy` reaches the algebra through `Checker.effTy_eq`
(`Laws/Program/Typing/Checker.lean`) and this `eq_cata`.
-/

namespace Effect4.Program

fold_of Effect4.Program.Checker.effTy

end Effect4.Program

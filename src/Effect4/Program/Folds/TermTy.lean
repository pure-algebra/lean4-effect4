import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Program.Typing.Terms

/-!
# The term typer as a `TermAlgebra`

`Checker.argTy`/`argsTy` (`Typing/Terms.lean`) as one algebra over the term family, the const
flag as the carriers' argument (`R .term = Bool → Option Ty`, `R .terms = Bool → Option (List
Ty)`). `termTy` and `termsTy` reach it through the agreement (`Typing/Agreement.lean`).
-/

namespace Effect4.Program

fold_of Effect4.Program.Checker.argTy

end Effect4.Program

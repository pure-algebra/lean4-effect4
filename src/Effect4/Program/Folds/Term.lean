import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Codegen.PrintLeaf
import Effect4.Codegen.Read
import Effect4.Program.Native
import Effect4.Program.Typing

/-!
# The hand traversals of `Term` / `Terms` as folds

Twelve of the fourteen the census lists (`docs/core/traversal-census.md` §3.3): the leaf
printer (`printTerm`/`printTerms`), the reader's `Terms.names?` and `noRow`, `Terms.toList`,
`scoped` and `weaken` (the level in the carrier), the evaluator `evalTerm`/`evalTerms` (the
environment in the carrier) and `argTy`, each as a `TermAlgebra` with its connectors. Not here:
`termTy`/`termsTy` — `termsTy` splits on the term child's constructor and calls `termTy` on the
rebuilt child (`.cons (.var index) tail => termTy sig env (.var index)`), so its homomorphism
equation holds by cases on the child, not by unfolding; the next shape for `fold_of`.
-/

namespace Effect4.Program

fold_of Effect4.Program.printTerm
fold_of Effect4.Program.Terms.names?
fold_of Effect4.Program.noRow
fold_of Effect4.Program.Terms.toList
fold_of Effect4.Program.Term.scoped
fold_of Effect4.Program.Term.weaken
fold_of Effect4.Program.evalTerm
fold_of Effect4.Program.argTy

end Effect4.Program

import Effect4.Program.FoldOf
import Effect4.Program.Fold
import Effect4.Codegen.PrintLeaf
import Effect4.Codegen.Read
import Effect4.Program.Native
import Effect4.Program.Typing

/-!
# The hand traversals of `Term` / `Terms` as folds

Every one the census lists (`docs/core/traversal-census.md` §3.3): the leaf printer
(`printTerm`/`printTerms`), the reader's `Terms.names?` and `noRow`, `Terms.toList`, `scoped`
and `weaken` (the level in the carrier), the evaluator `evalTerm`/`evalTerms` (the environment
in the carrier) and the term typer `argTy`/`argsTy` (the const flag in the carrier; `termTy` is
its projection at `false`, `Typing/Rules.lean`), each as a `TermAlgebra` with its connectors.
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

module

public import Effect4.Program.FoldOf
public import Effect4.Program.Fold
public import Effect4.Program.Typing.Annotate

@[expose] public section

/-!
Core proof-owner move of the existing annotated fold connector.
Concept: initial-algebras-folds. Claim: annotate-table. R14.
Consumer: Annotate.check_restrict, then the extension hit rule.
Scope: the annotated fold. No module checking or host behavior follows.
-/
namespace Effect4.Program
fold_of Effect4.Program.Annotate.check
end Effect4.Program

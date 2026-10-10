import Effect4.Laws.Program.DenoteRowsB
import Effect4.Program.FoldOf
import ProofGraph.AxiomAudit

/-!
Probe placement, before generation:
1. Concept initial-algebras-folds; the required fold connection for a new traversal.
2. Helper of rows-loop-session: denoteRowsB.eq_cata connects the meaning to its generated algebra.
   Consumer: the proposed shared meaning algebra, before any caller migration.
3. All NativeEff values, at each fixed row table and loop budget; exact call-tree equality.
4. No new machine, progress, typing, resource, concurrency or host-implementation claim.
5. R2 and R6: use the existing fold tooling for this added meaning without a second representation.
This remains a research probe. It changes no production definition or registry.
-/
namespace Effect4.Program
fold_of Effect4.Program.Denote.denoteRowsB (family := Effect4.Program.Eff)
end Effect4.Program
#check Effect4.Program.Denote.denoteRowsB.eq_cata

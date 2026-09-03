/-
Axiom receipts for the structured form's label-scoping law
(`test/contracts/flow-structured-lowering.contract.md`).

Expected union: `propext` and `Quot.sound`, except for the declarations whose
*statements* name Effect4's own block lowering or its printer.
`Skeleton.render` spells block-local names and compares TypeScript types, so it
already reaches `Classical.choice` through Lean's UTF-8 folds; a theorem about
its output inherits that. Those four are admitted by exact declaration in
`Effect4Test/Audit/AxiomGate.lean`. The scoping law itself, over
`Structuring.emitWith`, and its discharge at the skeleton
(`skeletonBlockWith_wellScoped`, `skeletonBody_wellScoped`) are `String`-free
and stay at the ceiling — one crossing fewer than before packet D3.
-/

import Effect4.Target.TypeScript.StructureLaws

#print axioms Effect4.Target.Structured.wellScoped
#print axioms Effect4.Target.Structured.wellScopedList
#print axioms Effect4.Target.Structured.Skel.wellScoped
#print axioms Effect4.Target.Structured.Skel.wellScopedList
#print axioms Effect4.Target.Structured.Skel.wellScopedList_append
#print axioms Effect4.Target.Structured.wellScopedList_append
#print axioms Effect4.Target.Structured.wellScopedList_of_forall
#print axioms Effect4.Target.Structured.dominates_step
#print axioms Effect4.Target.Structured.dominates_entry
#print axioms Effect4.Target.Structured.mem_succs_of_mem_preds
#print axioms Effect4.Target.Structured.exists_pred_of_transferTarget
#print axioms Effect4.Target.Structured.lt_size_of_transferTarget
#print axioms Effect4.Target.Structured.loops_of_child
#print axioms Effect4.Target.Structured.emitNode_wellScoped
#print axioms Effect4.Target.Structured.mem_blockLabels
#print axioms Effect4.Target.Structured.emitWith_wellScoped
#print axioms Effect4.Target.Structured.paramMove_wellScoped
#print axioms Effect4.Target.Structured.graphOf_closed

-- The exact crossings: their statements name the string-carrying lowering
-- and the printer.
#print axioms Effect4.Target.Structured.skeletonBlockWith_wellScoped
#print axioms Effect4.Target.Structured.skeletonBody_wellScoped
#print axioms Effect4.Target.Structured.render_wellScoped
#print axioms Effect4.Target.Structured.renderList_wellScoped
#print axioms Effect4.Target.Structured.renderCases_wellScoped
#print axioms Effect4.Target.Structured.structuredBody_wellScoped

/-
Axiom receipts for the structured form's label-scoping law
(`test/contracts/flow-structured-lowering.contract.md`).

Expected union: `propext` and `Quot.sound`, except for the two declarations
whose *statements* name Effect4's own block lowering. `Flow.lowerBlockWith` and
`Flow.structuredBody` spell block-local names and compare TypeScript types, so
they already reach `Classical.choice` through Lean's UTF-8 folds; a theorem
about their output inherits that. Both are admitted by exact declaration in
`Effect4Test/Audit/AxiomGate.lean`. The scoping law itself, over the package's
`emitWith`, is `String`-free and stays at the ceiling.
-/

import Effect4.Target.TypeScript.StructureLaws

#print axioms Effect4.Target.Structured.wellScoped
#print axioms Effect4.Target.Structured.wellScopedList
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

-- The two exact crossings: their statements name the string-carrying lowering.
#print axioms Effect4.Target.Structured.lowerBlockWith_wellScoped
#print axioms Effect4.Target.Structured.structuredBody_wellScoped

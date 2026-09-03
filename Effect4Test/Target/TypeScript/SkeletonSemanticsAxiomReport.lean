/-
Axiom receipts for the skeleton denotation and the two agreement theorems
(packet D3; `test/contracts/flow-denotation.contract.md` and
`test/contracts/flow-structured-lowering.contract.md`).

Expected union for every declaration below: `propext` and `Quot.sound` — the
ceiling. `Classical.choice` is forbidden here and does not appear.

`Effect4/Target/TypeScript/SkeletonSemantics.lean` carries `String` only as
labels and slot names it never decides anything by; every semantic choice the
denotation makes is a `Nat`, a `Bool` or a `Val`. Two places where the obvious
library lemma would have crossed are avoided on purpose and are worth naming,
because a future edit that reaches for them puts `Classical.choice` back:
`List.filter_eq_nil_iff` (used by the flat-graph argument, replaced by the local
`filter_false_nil` / `filter_nil_of_all_false` inductions) and `Exists.choose`
(which an existential `execList_move_goto` would have needed for a `perform`'s
continuation — `Skel.movedMachine` names that machine instead).

`Skeleton.render` and the string-carrying lowerings are not subjects here:
`Flow.skeletonBlock` and `Flow.skeletonBlockWith` appear in *statements* only,
and their own axiom set is `propext`.
-/

import Effect4.Target.TypeScript.SkeletonSemantics

#print axioms Effect4.Target.EffectV4.Skel.two_le_size
#print axioms Effect4.Target.EffectV4.Skel.execList_nil
#print axioms Effect4.Target.EffectV4.Skel.execList_cons
#print axioms Effect4.Target.EffectV4.Skel.execList_cons_simple
#print axioms Effect4.Target.EffectV4.Skel.runSimple_append
#print axioms Effect4.Target.EffectV4.Skel.execList_append_simple
#print axioms Effect4.Target.EffectV4.Skel.paramMove_eq
#print axioms Effect4.Target.EffectV4.Skel.ownedBy_noTemp
#print axioms Effect4.Target.EffectV4.Skel.ownedBy_ne_param
#print axioms Effect4.Target.EffectV4.Skel.setVal_other
#print axioms Effect4.Target.EffectV4.Skel.setVal_self
#print axioms Effect4.Target.EffectV4.Skel.temps_cons
#print axioms Effect4.Target.EffectV4.Skel.moves_cons
#print axioms Effect4.Target.EffectV4.Skel.direct_cons
#print axioms Effect4.Target.EffectV4.Skel.runSimple_temps
#print axioms Effect4.Target.EffectV4.Skel.runSimple_moves
#print axioms Effect4.Target.EffectV4.Skel.runSimple_direct
#print axioms Effect4.Target.EffectV4.Skel.runSimple_paramMove
#print axioms Effect4.Target.EffectV4.Skel.execControl_gotoBlock
#print axioms Effect4.Target.EffectV4.Skel.execControl_ret
#print axioms Effect4.Target.EffectV4.Skel.execControl_perform
#print axioms Effect4.Target.EffectV4.Skel.execControl_atom
#print axioms Effect4.Target.EffectV4.Skel.execControl_literal
#print axioms Effect4.Target.EffectV4.Skel.execControl_decide
#print axioms Effect4.Target.EffectV4.Skel.performOp_eq
#print axioms Effect4.Target.EffectV4.Skel.afterFell_fell
#print axioms Effect4.Target.EffectV4.Skel.afterFell_continueLoop
#print axioms Effect4.Target.EffectV4.Skel.afterFell_finished
#print axioms Effect4.Target.EffectV4.Skel.dispatchRun_zero
#print axioms Effect4.Target.EffectV4.Skel.dispatchRun_succ
#print axioms Effect4.Target.EffectV4.Skel.dispatchCatch_continueLoop
#print axioms Effect4.Target.EffectV4.Skel.dispatchCatch_finished
#print axioms Effect4.Target.EffectV4.Skel.readArgs_getElem?
#print axioms Effect4.Target.EffectV4.Skel.enter_vals
#print axioms Effect4.Target.EffectV4.Skel.setIndex_vals
#print axioms Effect4.Target.EffectV4.Skel.setIndex_same
#print axioms Effect4.Target.EffectV4.Skel.execControl_dispatchLoop
#print axioms Effect4.Target.EffectV4.Skel.execList_cons_control
#print axioms Effect4.Target.EffectV4.Skel.holds_of_getElem?
#print axioms Effect4.Target.EffectV4.Skel.execList_move_goto
-- The seven `plan` inversions and the two `testValue` readings moved to
-- `Effect4.Flow` on 2026-09-03 (survey finding L7); their receipts are in
-- `Effect4Test/Semantics/PlanInversionAxiomReport.lean`.
#print axioms Effect4.Target.EffectV4.Skel.execControl_performCatch_eq_perform
#print axioms Effect4.Target.EffectV4.Skel.answerSlots_agree
#print axioms Effect4.Target.EffectV4.Skel.execList_answerMove
#print axioms Effect4.Target.EffectV4.Skel.ownedBy_argSlots
#print axioms Effect4.Target.EffectV4.Skel.argSlots_agree
#print axioms Effect4.Target.EffectV4.Skel.BlockLaw
#print axioms Effect4.Target.EffectV4.Skel.execList_skeletonBlock
#print axioms Effect4.Target.EffectV4.Skel.bind_pure
#print axioms Effect4.Target.EffectV4.Skel.bind_vis_inl
#print axioms Effect4.Target.EffectV4.Skel.bind_vis_inr
#print axioms Effect4.Target.EffectV4.Skel.start_input
#print axioms Effect4.Target.EffectV4.Skel.runSimple_fixed
#print axioms Effect4.Target.EffectV4.Skel.runSimple_acquisitions
#print axioms Effect4.Target.EffectV4.Skel.runSimple_declarations
#print axioms Effect4.Target.EffectV4.Skel.caseBody?_of_mapM
#print axioms Effect4.Target.EffectV4.Skel.dispatchRun_denoteFuel
#print axioms Effect4.Target.EffectV4.Skel.execList_dispatchPrefix
#print axioms Effect4.Target.EffectV4.Skel.movedMachine_eq
#print axioms Effect4.Target.EffectV4.Skel.execList_move_then
#print axioms Effect4.Target.EffectV4.Skel.execList_skeletonBlockWith
#print axioms Effect4.Target.EffectV4.Skel.emitNode_flat
#print axioms Effect4.Target.EffectV4.Skel.emitWith_flat
#print axioms Effect4.Target.EffectV4.Skel.graphOf_bounded
#print axioms Effect4.Target.EffectV4.Skel.flat_of_flatBelow
#print axioms Effect4.Target.EffectV4.Skel.getElem?_of_findIdx?
#print axioms Effect4.Target.EffectV4.Skel.findIdx?_isSome_of_find?
#print axioms Effect4.Target.EffectV4.Skel.skeletonBody_eq
#print axioms Effect4.Target.EffectV4.Skel.denoteOutcome_stable
#print axioms Effect4.Target.EffectV4.Skel.execList_emitNode_flat
#print axioms Effect4.Target.EffectV4.skeletonDispatch_denote
#print axioms Effect4.Target.EffectV4.skeletonStructured_denote
#print axioms Effect4.Target.EffectV4.skeletonStructured_denote_dispatch

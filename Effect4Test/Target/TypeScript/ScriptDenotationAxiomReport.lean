/-
Axiom receipts for the script embedding's denotation (packet D5).
Expected union: `propext` and `Quot.sound`. `Effect4/Target/TypeScript/ScriptDenotation.lean`
is a semantic module and takes no exemption from the axiom gate: `ScriptFlow`
and `EffectV4` are exempt for `Classical.choice` because they render, and that
is exactly why the semantics live in a module of their own.
-/

import Effect4.Target.TypeScript.ScriptDenotation

-- The pure-operation lemma D5 owes.
#print axioms Effect4.Target.EffectV4.interpret_vis_of_pure
#print axioms Effect4.Target.EffectV4.tableService_handle_pure

-- Reading the embedded graph.
#print axioms Effect4.Target.EffectV4.lookupBlock_ordered
#print axioms Effect4.Target.EffectV4.lookupBlock_at
#print axioms Effect4.Target.EffectV4.tableAlphabet_lookup_iff
#print axioms Effect4.Target.EffectV4.readArgs_allVars

-- Segments.
#print axioms Effect4.Target.EffectV4.Segment.refl
#print axioms Effect4.Target.EffectV4.Segment.trans
#print axioms Effect4.Target.EffectV4.performTo_segment
#print axioms Effect4.Target.EffectV4.ret_denote

-- The `Build` invariant.
#print axioms Effect4.Target.EffectV4.ordered_append_one
#print axioms Effect4.Target.EffectV4.performTo_appends
#print axioms Effect4.Target.EffectV4.literal_appends
#print axioms Effect4.Target.EffectV4.materialize_appends
#print axioms Effect4.Target.EffectV4.embedStep_appends
#print axioms Effect4.Target.EffectV4.foldlM_appends

-- The two inductions and the theorem.
#print axioms Effect4.Target.EffectV4.mint_segment
#print axioms Effect4.Target.EffectV4.literal_segment
#print axioms Effect4.Target.EffectV4.materialize_segment
#print axioms Effect4.Target.EffectV4.familyIndex_lt
#print axioms Effect4.Target.EffectV4.step_segment
#print axioms Effect4.Target.EffectV4.liftScript_bind
#print axioms Effect4.Target.EffectV4.stepsWalk_denote
#print axioms Effect4.Target.EffectV4.Script.toFlow_denote

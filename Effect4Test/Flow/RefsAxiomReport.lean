/-
Kernel dependency report for the `Refs` family and its Lean handler
(`Effect4/Stateful/RefFamily.lean`, `docs/TRACE-DAG.md`).

Accepted ceiling: no dependency, `propext`, or `propext` with `Quot.sound`.
`Classical.choice` is not admitted here and the module carries no exemption in
`Effect4Test/Audit/AxiomGate.lean`. That is the separation this report records:
the DSL that *emits* these declarations reaches `Classical.choice` through
`CommandElabM` and is exempt for that reason, while everything it emits — the
family, the wire encoders, the traced service — stays at the semantic ceiling.
-/

import Effect4Test.Flow.RefsContract

/-! ## The family the DSL emits -/

#print axioms Effect4.RefFamily.Refs
#print axioms Effect4.RefFamily.Refs.rows
#print axioms Effect4.RefFamily.Refs.Name.spelling
#print axioms Effect4.RefFamily.Refs.encodeParam
#print axioms Effect4.RefFamily.Refs.encodeAnswer
#print axioms Effect4.RefFamily.Refs.traced
#print axioms Effect4.RefFamily.ERefs.rows
#print axioms Effect4.RefFamily.ERefs.encodeAnswer
#print axioms Effect4.RefFamily.ERefs.traced

/-! ## The named functions the read-modify-write rows take

DB-02 keeps a Lean function out of canonical content, so rc.112's `(a) => A`
and `(a) => Option<A>` arguments are table indices; `RefFns` is the one
declaration both faces come from. -/

#print axioms Effect4.RefFamily.RefFns.rows
#print axioms Effect4.RefFamily.RefFn.ofHandle_index

/-! ## The handler and the store it models -/

#print axioms Effect4.RefFamily.refPeek
#print axioms Effect4.RefFamily.refPoke
#print axioms Effect4.RefFamily.succ
#print axioms Effect4.RefFamily.refStep
#print axioms Effect4.RefFamily.refsLive
#print axioms Effect4.RefFamily.erefsLive

/-! ## The projection lemma, and the clauses the census rows name

`refsLive` *is* `refStep` under `refOpOf` and `refAnswerOf`; every clause below
is a clause of the heap, and the handler carries it through that equation. -/

#print axioms Effect4.RefFamily.refsLive_is_refStep
#print axioms Effect4.RefFamily.refsLive_of_step
#print axioms Effect4.RefFamily.refStep_make
#print axioms Effect4.RefFamily.refStep_set
#print axioms Effect4.RefFamily.refStep_update
#print axioms Effect4.RefFamily.set_answer_ne_update_answer
#print axioms Effect4.RefFamily.refStep_setAndGet
#print axioms Effect4.RefFamily.refStep_modifySome_none
#print axioms Effect4.RefFamily.refStep_updateSomeAndGet_none
#print axioms Effect4.RefFamily.updateSomeAndGet_ne_getAndUpdateSome

/-! ## The corpus and the traced runs the goldens are receipts of -/

#print axioms Effect4.RefFamily.refGoldenLog
#print axioms Effect4.RefFamily.erefGoldenLog
#print axioms Effect4.RefFamily.refPrograms
#print axioms Effect4.RefFamily.refFamilies

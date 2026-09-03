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

/-! ## The handler and the store it models -/

#print axioms Effect4.RefFamily.refPeek
#print axioms Effect4.RefFamily.refPoke
#print axioms Effect4.RefFamily.succ
#print axioms Effect4.RefFamily.refsLive
#print axioms Effect4.RefFamily.erefsLive

/-! ## The corpus and the traced runs the goldens are receipts of -/

#print axioms Effect4.RefFamily.refGoldenLog
#print axioms Effect4.RefFamily.erefGoldenLog
#print axioms Effect4.RefFamily.refPrograms
#print axioms Effect4.RefFamily.refFamilies

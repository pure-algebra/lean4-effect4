import Effect4.Laws.Auto.AnswerGate

/-!
# Test.Audit.AnswerGate — completeness check for SyncOp and FiberOp protocols

Invokes #answer_gate to verify that all 31 SyncOp rows and 40 FiberOp rows (71 total)
are present in the manifest and accounted for.
-/

#answer_gate

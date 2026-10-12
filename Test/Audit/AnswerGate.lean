import Effect4.Laws.Auto.AnswerGate
import Effect4.Laws.Program.Sched

/-!
# Test.Audit.AnswerGate — completeness check for SyncOp and FiberOp protocols

Invokes #answer_gate to verify that all 31 SyncOp rows and 42 FiberOp rows (73 total)
are present in the manifest and accounted for.
-/

#answer_gate

import Effect4.Program.Sched

/-!
Fresh kernel dependency report for the term scheduler's signature
(`src/Effect4/Program/Sched.lean`; packet `Test/contracts/program-sched.contract.md`).

Coordinator-owned, appended from the `#print axioms` output at each landing. Every theorem
below is expected at the ceiling `propext`/`Quot.sound`; the gate
(`Test/Audit/AxiomGate.lean`) is what enforces it, this file is the human-readable receipt.
-/

-- The signature.
#print axioms Effect4.Program.Sched.FiberOp
#print axioms Effect4.Program.Sched.FiberOp.answer
#print axioms Effect4.Program.Sched.FiberOp.defaultAnswer
#print axioms Effect4.Program.Sched.FiberSig
#print axioms Effect4.Program.Sched.RSig
#print axioms Effect4.Program.Sched.RSig_op
#print axioms Effect4.Program.Sched.RSig_answer_inl
#print axioms Effect4.Program.Sched.RSig_answer_inr
#print axioms Effect4.Program.Sched.RProgram
#print axioms Effect4.Program.Sched.perform_inl_bind

-- The store half, lifted.
#print axioms Effect4.Program.Sched.fiberRefusal
#print axioms Effect4.Program.Sched.rHandler
#print axioms Effect4.Program.Sched.rHandler_inl
#print axioms Effect4.Program.Sched.rHandler_inr
#print axioms Effect4.Program.Sched.interpret_inl_store
#print axioms Effect4.Program.Sched.meaning_via_rsig

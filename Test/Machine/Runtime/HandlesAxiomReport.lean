import Test.Machine.Runtime.HandlesContract

/-! C13 handle-invariant dependency receipts. The theorem concerns the collected positions
of the Lean frame machine, under the explicit starting-state and external-answer premises. -/

#print axioms Effect4.Machine.Handle
#print axioms Effect4.Machine.primKeys
#print axioms Effect4.Machine.MintedAt
#print axioms Effect4.Machine.AnswersValidAt
#print axioms Effect4.Machine.KeyBounded
#print axioms Effect4.Machine.syncOpStep_keys
#print axioms Effect4.Machine.stores_keyBounded
#print axioms Effect4.Machine.evaluatePrim_minted
#print axioms Effect4.Machine.driveState_minted
#print axioms Effect4.Machine.fireState_minted
#print axioms Effect4.Machine.flushAllState_minted
#print axioms Effect4.Machine.stepDecisionState_minted
#print axioms Effect4.Machine.replayEval_minted
#print axioms Effect4.Program.compileEff_keys
#print axioms Effect4.Program.runStmts_keys
#print axioms Effect4.Program.actionAt_keys
#print axioms Effect4.Program.interpOf_keyBounded
#print axioms Effect4.Program.Minted
#print axioms Effect4.Program.AnswersValid
#print axioms Effect4.Program.load_minted
#print axioms Effect4.Program.handles_minted
#print axioms Test.Runtime.HandlesContract.waiting_answered_minted
#print axioms Test.Runtime.HandlesContract.forkJoin_minted

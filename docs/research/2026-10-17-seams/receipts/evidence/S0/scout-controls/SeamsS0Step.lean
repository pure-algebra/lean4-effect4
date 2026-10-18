import Effect4.Program.Admit

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- The existing native evaluator at a stable linkage root. No reply admission occurs here. -/
def stepChecked (program : NativeEff) (table : RowTable)
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (fuel : Nat) (machine : NativeMachine) (decision : NativeDecision) :
    NativeMachine × Bool :=
  letI := evaluatorFor program table
  stepDecisionState interp fuel machine decision

end Effect4.Program

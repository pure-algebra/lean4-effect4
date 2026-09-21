import Effect4.Laws.Api.Supervision
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Auto.Obligations

/-! Trace/origin agreement on the existing API decision-prefix domain.
Arbitrary records with erased traces are not in the premise of these obligations. -/

set_option autoImplicit false
namespace Effect4.Api.TraceFacts.M1Trace
open Effect4 Effect4.Machine Effect4.Program

theorem step_agrees (program : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (_reachable : Guard.Reachable program table compileFuel answers m)
    (_agrees : Agrees m) (fuel : Nat) (decision : NativeDecision) :
    ProofGraph.Obligation (Agrees (steppedBy program fuel table m decision)) := ⟨⟩
#proof_wanted step_agrees

theorem reachable_agrees (program : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (_reachable : Guard.Reachable program table compileFuel answers m) :
    ProofGraph.Obligation (forkedOf m.trace = originForks m) := ⟨⟩
#proof_wanted reachable_agrees

end Effect4.Api.TraceFacts.M1Trace

#typed_state_obligations Effect4.Api.TraceFacts.M1Trace ceiling 2 using aesop (rule_sets := [Effect4.Stores, Effect4.Fibers])

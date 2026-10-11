import Effect4.Laws.Program.ReleaseCustody.NativeAccounting
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody
open Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.RuntimeShape
open Effect4.Program.ReleaseCustody.Sequencing

example (q : List Nat) (b : Api.Built) (m : NativeMachine) (fiber : RuntimeShape.Fiber) (yielding : Bool) :
    IterDebit q m fiber (evaluatePrim.stepFrame (interpAt b.program m.completedExits b.table) m fiber yielding) :=
  NativeAccounting.step_frame q b.program m.completedExits b.table m fiber yielding

example (q : List Nat) (b : Api.Built) (m : NativeMachine) (fiber : RuntimeShape.Fiber)
    (yielding : Bool) (scope : Nat) (fin : FinName) (state : Stores) (value : Val)
    (current : fiber.frame.current = .sync (.op (.scopeAdd scope fin)))
    (unique : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (step : syncOpStep (.scopeAdd scope fin) m.state = some (state,value)) :
    IterDebit q m fiber (evaluateNative b.program m fiber yielding b.table) :=
  NativeAccounting.sync_answer q b.program b.table m fiber yielding _ state value current unique fresh held step

#axiom_audit Effect4.Laws.Program.ReleaseCustody.NativeAccounting

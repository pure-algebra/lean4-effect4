import Effect4.Laws.Program.ReleaseCustody.NativePrimitiveDebit
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

example (q : List Nat) (b : Api.Built) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (exit : ExitV) (held : Kept fiber.frame.current fiber.frame.stack) :
    IterDebit q m fiber (evaluatePrim.finalizerOr (interpAt b.program m.completedExits b.table) m fiber yielding exit) :=
  NativePrimitiveDebit.finalizer q b.program m.completedExits b.table m fiber yielding exit held

example (q : List Nat) (b : Api.Built) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (name : EffName) (signal : Bool) (cancel : Option EffName)
    (current : fiber.frame.current = .async name signal cancel)
    (held : Kept fiber.frame.current fiber.frame.stack) :
    IterDebit q m fiber (evaluatePrim (interpAt b.program m.completedExits b.table) m fiber yielding) :=
  NativePrimitiveDebit.asynchronous q b.program b.table m fiber yielding name signal cancel current held

#axiom_audit Effect4.Laws.Program.ReleaseCustody.NativePrimitiveDebit

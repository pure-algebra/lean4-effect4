import Effect4.Laws.Program.ReleaseCustody.NativeParkDebit
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

example (q : List Nat) (b : Api.Built) (m : NativeMachine) (fiber : Control.Fiber) (yielding : Bool)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (fragment : SourceScope.Fragment b.program) (owned : SourceScope.FrameAt b.program fiber.frame)
    (sequential : SourceScope.SequentialSource b.program)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (races : m.races = []) :
    IterDebit q m fiber (evaluatePrim (interpAt b.program m.completedExits b.table) m fiber yielding) :=
  NativeParkDebit.primitive q b.program b.table m fiber yielding held fragment owned sequential fibers scopes fresh races

#axiom_audit Effect4.Laws.Program.ReleaseCustody.NativeParkDebit

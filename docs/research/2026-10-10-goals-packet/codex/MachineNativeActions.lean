import Effect4.Laws.Program.ReleaseCustody.NativeActionDebit
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

example (q : List Nat) (b : Api.Built) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (thunk : EffThunk) (selected : NAction)
    (current : fiber.frame.current = .withFiber thunk)
    (kept : Kept fiber.frame.current fiber.frame.stack)
    (fragment : SourceScope.Fragment b.program) (source : SourceScope.FrameAt b.program fiber.frame)
    (sequential : SourceScope.SequentialSource b.program)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (found : (interpAt b.program m.completedExits b.table).withFiberOf thunk = some selected) :
    IterDebit q m fiber (evaluatePrim.withFiber (interpAt b.program m.completedExits b.table) m fiber yielding selected) :=
  NativeActionDebit.native_action q b.program b.table m fiber yielding thunk selected current kept fragment source sequential fibers scopes fresh found

example (q : List Nat) (b : Api.Built) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (scope : Nat) (exit : ExitV) (held : NoAdd fiber.frame.stack)
    (unique : (m.state.scopes.entries.map ScopeEntry.key).Nodup) :
    IterDebit q m fiber (evaluatePrim.withFiber (interpAt b.program m.completedExits b.table) m fiber yielding (.closeScope scope exit)) :=
  NativeActionDebit.closeScope q b.program b.table m fiber yielding scope exit held unique

#axiom_audit Effect4.Laws.Program.ReleaseCustody.NativeActionDebit

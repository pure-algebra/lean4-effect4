import Effect4.Laws.Program.ReleaseCustody.CommandSequencing
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing Effect4.Program.ReleaseCustody.CommandStacks

example (b : Api.Built) (m : NativeMachine) (fiber old : Control.Fiber)
    (yielding : Bool) (rest : List NCmd)
    (active : fiber.parked = .notParked)
    (kept : Kept fiber.frame.current fiber.frame.stack)
    (source : SourceScope.FrameAt b.program fiber.frame) (guard : FrameCodeOwned m fiber)
    (found : (evaluateNative b.program m fiber yielding b.table).machine.fiber? fiber.id = some old)
    (tail : QueueStable (settle fiber.id rest (evaluateNative b.program m fiber yielding b.table)).1 rest) :
    QueueStable (settle fiber.id rest (evaluateNative b.program m fiber yielding b.table)).1
      (settle fiber.id rest (evaluateNative b.program m fiber yielding b.table)).2 :=
  CommandSequencing.settle_queue b.program b.table fiber.id rest _ old
    (Interruption.evaluateNative_id b.program b.table m fiber yielding) found
    (ReturnCommands.evaluateNative_nested b.program b.table m fiber yielding guard)
    (NativeSequencing.native_returned b.program b.table m fiber yielding active kept source) tail

#axiom_audit Effect4.Laws.Program.ReleaseCustody.CommandSequencing

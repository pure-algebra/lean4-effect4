import Effect4.Laws.Program.ReleaseCustody.NativeStacks
import Effect4.Laws.Program.ReleaseCustody.IterationDebit
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody
open Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.RuntimeShape

example (b : Api.Built) (m : NativeMachine) (fiber : RuntimeShape.Fiber) (yielding : Bool) :
    CommandStacks.StackLinks m (iteration (evaluator := evaluatorFor b.program b.table)
      (interpOf b.program b.table) m fiber yielding).machine :=
  NativeStacks.iteration_links b.program b.table m fiber yielding

example (q : List Nat) (m : NativeMachine) (owner : FiberId) (old next : RuntimeShape.Fiber)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? owner = some old)
    (selected : next.id = owner) :
    machineCredits q (m.update next) = outsideCredits q owner m + fiberCredits q next :=
  outside_install q m owner old next unique found selected

example (q : List Nat) (before : NativeMachine) (fiber : RuntimeShape.Fiber)
    (it : Iteration) (rest : List Control.Command)
    (unique : (before.fibers.map RunFiber.id).Nodup) (found : before.fiber? fiber.id = some fiber)
    (afterUnique : (it.machine.fibers.map RunFiber.id).Nodup)
    (old : RuntimeShape.Fiber) (afterFound : it.machine.fiber? fiber.id = some old)
    (key : it.fiber.id = fiber.id) (debit : IterDebit q before fiber it) (funded : Funded q before rest) :
    Funded q (settle fiber.id rest it).1 (settle fiber.id rest it).2 :=
  settle_funded q before fiber it rest unique found afterUnique old afterFound key debit funded

#axiom_audit Effect4.Laws.Machine.ControlWeights
  Effect4.Laws.Program.ReleaseCustody.Outside
  Effect4.Laws.Program.ReleaseCustody.NativeStacks
  Effect4.Laws.Program.ReleaseCustody.IterationDebit

import Effect4.Laws.Program.ReleaseCustody.AdministrativeQueue
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.CommandStacks

example (b : Api.Built) (m : NativeMachine) (id : FiberId) (yielding : Bool) (kind : ParkKind)
    (rest : List NCmd) (state : GuardState m)
    (guard : GuardQueue b.program b.table m (.afterInterrupt id yielding kind :: rest))
    (held : QueueStable m (.afterInterrupt id yielding kind :: rest)) (empty : m.races = []) :
    letI := evaluatorFor b.program b.table
    let out := driveStep (interpOf b.program b.table) m (.afterInterrupt id yielding kind) rest
    QueueStable out.1 out.2 :=
  AdministrativeQueue.non_evaluator b.program b.table m _ rest state guard held empty
    (by intro _ _ wrong; cases wrong) (by intro _ _ wrong; cases wrong)

#axiom_audit Effect4.Laws.Program.ReleaseCustody.AdministrativeQueue

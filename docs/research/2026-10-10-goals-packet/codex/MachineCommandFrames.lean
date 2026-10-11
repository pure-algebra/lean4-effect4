import Effect4.Laws.Program.ReleaseCustody.AdministrativeKept
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.RuntimeShape Effect4.Program.ReleaseCustody.CommandStacks

example (q : List Nat) (b : Api.Built) (m : NativeMachine) (id : FiberId) (yielding : Bool) (rest : List NCmd)
    (guard : GuardState m) (commands : GuardQueue b.program b.table m (.loop id yielding :: rest))
    (scopes : Execution.ScopeRows m) (frames : ConfigurationKept m)
    (queue : QueueStable m (.loop id yielding :: rest)) (source : SourceScope.ConfigurationAt b.program m)
    (fragment : SourceScope.Fragment b.program) (sequential : SourceScope.SequentialSource b.program)
    (raceFree : SourceScope.RaceFreeSource b.program) (funded : Funded q m (.loop id yielding :: rest)) :
    letI := evaluatorFor b.program b.table
    let out := driveStep (interpOf b.program b.table) m (.loop id yielding) rest
    Funded q out.1 out.2 ∧ ConfigurationKept out.1 ∧ QueueStable out.1 out.2 :=
  LoopCommand.loop q b.program b.table m id yielding rest guard commands scopes frames queue source fragment sequential raceFree funded

example (b : Api.Built) (m : NativeMachine) (id : FiberId) (token : Nat) (answer : NCode) (rest : List NCmd)
    (frames : ConfigurationKept m) (queue : QueueStable m (.resume id token answer :: rest))
    (source : SourceScope.CommandAt b.program (.resume id token answer))
    (raceFree : SourceScope.RaceFreeSource b.program) (races : m.races = []) :
    letI := evaluatorFor b.program b.table
    ConfigurationKept (driveStep (interpOf b.program b.table) m (.resume id token answer) rest).1 :=
  AdministrativeKept.non_evaluator b.program b.table m _ rest frames queue source raceFree races
    (by intro _ _ wrong; cases wrong) (by intro _ _ wrong; cases wrong)

#axiom_audit Effect4.Laws.Program.ReleaseCustody.LoopCommand Effect4.Laws.Program.ReleaseCustody.AdministrativeKept

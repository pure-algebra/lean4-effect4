import Effect4.Laws.Program.ReleaseCustody.CommandClosure
import Effect4.Api.Built
import ProofGraph.AxiomAudit
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody

example (q : List Nat) (b : Api.Built) (fuel : Nat) (m : NativeMachine) (commands : List Guard.NCmd)
    (fragment : SourceScope.Fragment b.program) (sequential : SourceScope.SequentialSource b.program)
    (raceFree : SourceScope.RaceFreeSource b.program) (held : CommandClosure.Held q b.program m)
    (queued : CommandClosure.Queued q b.program b.table m commands) :
    letI := evaluatorFor b.program b.table
    let out := driveState (interpOf b.program b.table) fuel m commands
    CommandClosure.Held q b.program out.1 ∧ CommandClosure.Queued q b.program b.table out.1 out.2 :=
  CommandClosure.drive q b.program b.table fuel m commands fragment sequential raceFree held queued

#axiom_audit Effect4.Laws.Program.ReleaseCustody.CommandClosure

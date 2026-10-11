import Effect4.Laws.Program.ReleaseCustody.FrameSequencing
import Test.Dogfood.Scenario.Programs
import ProofGraph.AxiomAudit

/-!
Reader: the complete native primitive evaluator at the actual Workers program.
The matching registration-body premise is the shared source predicate's field.
The reader asserts no full native command or admitted-history closure.
-/
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Sequencing
open Effect4.Program.ReleaseCustody.Pop (Frame)

example (total : Nat) (fiber : Frame) (held : Kept fiber.current fiber.stack)
    (template : ∀ body a fin, fiber.current = .onSuccess body (.afterScopeAdd a fin) →
      ∃ scope, body = .sync (.op (.scopeAdd scope fin))) :
    match (fiber.step (interpAt (Test.Dogfood.Scenario.Programs.workersProgram total) []).toPrimInterp).1 with
    | .running next => Kept next.current next.stack
    | .finished _ => True :=
  Effect4.Program.ReleaseCustody.FrameSequencing.step _ [] [] fiber held template

#axiom_audit Effect4.Laws.Program.ReleaseCustody.PopSequencing
  Effect4.Laws.Program.ReleaseCustody.FrameSequencing

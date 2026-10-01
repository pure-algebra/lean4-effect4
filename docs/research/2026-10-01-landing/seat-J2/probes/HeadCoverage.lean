import Effect4.Api.RunnerDerived

/-! Seat J2, step 3b: what the generated groups' print-agreement guards cover. For each list a guard
holds `Canonical.head x == printedHead (Canonical.print x)` on: how many values it lists, how many
distinct constructors those values reach, and how many constructors the carrier's shape declares
(`Canonical.heads`). Run: `lake env lean docs/research/2026-10-01-landing/seat-J2/probes/HeadCoverage.lean`. -/

open Effect4 Effect4.Store Effect4.Program Effect4.Api Effect4.Machine

/-- Values listed, distinct constructors reached, constructors declared. -/
def coverage {α : Type} [Canonical α] (name : String) (xs : List α) : String :=
  let reached := (xs.map Canonical.head).eraseDups
  s!"{name}: {xs.length} values reach {reached.length} of {(Canonical.heads α).length} constructors"

#eval do
  IO.println "Refusals group"
  IO.println (coverage "TableRefusal" RefusalsAcceptance.tables)
  IO.println (coverage "AdmitRefusal" RefusalsAcceptance.admissions)
  IO.println (coverage "Authoring.Reason" (RefusalsAcceptance.scopes.map (·.reason)))
  IO.println (coverage "TypeReason" RefusalsAcceptance.reasons)
  IO.println (coverage "AuthorRefusal" RefusalsAcceptance.authors)
  IO.println (coverage "PrintRefusal" RefusalsAcceptance.prints)
  IO.println (coverage "ReadRefusal" RefusalsAcceptance.reads)
  IO.println (coverage "BuildRefusal" RefusalsAcceptance.builds)
  IO.println (coverage "TypeRefusal (a structure)" RefusalsAcceptance.typings)
  IO.println "Runner group"
  IO.println (coverage "Err" RunnerAcceptance.errs)
  IO.println (coverage "Defect" RunnerAcceptance.defects)
  IO.println (coverage "Reason (the cause's)" RunnerAcceptance.failed.reasons)
  IO.println (coverage "Exit" RunnerAcceptance.exits)
  IO.println (coverage "Completion" RunnerAcceptance.completions)
  IO.println (coverage "NativeDecision" RunnerAcceptance.decisions)
  IO.println (coverage "HostSession.Refusal" RunnerAcceptance.refusals)
  IO.println (coverage "HostSession.Phase" RunnerAcceptance.phases)
  IO.println (coverage "Runner.Command" RunnerAcceptance.commands)
  IO.println (coverage "HostProtocol.State" RunnerAcceptance.states)
  IO.println (coverage "Machine.Stuck" RunnerAcceptance.stucks)
  IO.println (coverage "Api.Outcome" RunnerAcceptance.outcomes)
  IO.println (coverage "FiberStatus" RunnerAcceptance.statuses)

import ProofGraph.Goal
import ProofGraph.Audit

/-!
# `#axiom_audit`: the gate's exact walk over named modules

`#axiom_audit M₁ M₂ …` walks every declaration of the named modules with the axiom gate's walk
(`reachedAxiomsMany`, one memo for the whole command), and stops at planned goals as the gate
does (`isGoal`, decisions row 203). A declaration that reaches an axiom outside
`[propext, Quot.sound]`, or whose walk ran out of its step budget, is an error that names it.
Otherwise the command reports how many declarations it walked, and how many rest on goals.

It is a seat's audit of a landing (cleanup C7 of the host-call note,
`docs/research/2026-10-09-host-calls-and-cleanup.md`). Lean's own collector misses axioms behind
a cycle, so a seat audits with this command, not with `#print axioms`. It applies no admission:
the gate's admitted modules and exemptions are the gate's (`Test/Audit/AxiomGate.lean`).
-/

namespace ProofGraph
open Lean Elab Command

/-- The axioms a declaration of the law graph may reach. -/
def trustedAxioms : Array Name := #[``propext, ``Quot.sound]

/-- `#axiom_audit M₁ M₂ …`: every declaration of the named modules, by the gate's exact walk. -/
syntax (name := axiomAudit) "#axiom_audit" (ppSpace ident)+ : command

@[command_elab axiomAudit] def elabAxiomAudit : CommandElab := fun stx => do
  let modules := stx[1].getArgs.map (·.getId)
  let env ← getEnv
  for module in modules do
    unless env.header.moduleNames.contains module do
      throwError "#axiom_audit: the module {module} is not imported"
  -- the gate's own scan: each module's declarations, read from the environment
  let (facts, _, _) := Audit.auditedFacts env modules.contains
  let roots := facts.map (·.name)
  let goals := roots.filter (isGoal env)
  let walked := roots.filter (!isGoal env ·)
  let (results, _) := reachedAxiomsMany env walked {} (isGoal env)
  let mut offenders : Array MessageData := #[]
  let mut modulo : Nat := 0
  for (name, result) in walked.zip results do
    match result with
    | none => offenders := offenders.push m!"{name}: the walk ran out of its step budget"
    | some reached =>
      let outside := reached.filter fun axiomName =>
        !trustedAxioms.contains axiomName && !isGoal env axiomName
      if !outside.isEmpty then offenders := offenders.push m!"{name} reaches {outside}"
      if reached.any (isGoal env) then modulo := modulo + 1
  if offenders.isEmpty then
    logInfo m!"#axiom_audit: {walked.size} declarations within [propext, Quot.sound], \
      {modulo} of them modulo planned goals; {goals.size} planned goals"
  else
    throwError m!"#axiom_audit: {offenders.size} of {walked.size} declarations reach axioms \
      outside [propext, Quot.sound]:{indentD (MessageData.joinSep offenders.toList Format.line)}"

end ProofGraph

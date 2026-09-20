import Effect4.Laws.Auto.Census
import Effect4.Laws.Auto.RuleSets
import ProofGraph.Ledger

/-!
The declaration-backed obligation ledger. `ProofGraph.Obligation p` marks the expected goal
set; `#proof_wanted goal` explicitly records pending work without repeating its proposition.
The ledger searches from the actual statements and publishes checked theorem terms. It never
creates placeholders as a side effect of checking, so deleting one cannot silently heal a gap.
-/
namespace Effect4.Laws.Auto.Obligations
open Lean Meta Elab Command
open ProofGraph

private def readGoal (name : Name) : MetaM (Option Goal) := do
  let info ← getConstInfo name
  forallTelescope info.type fun xs body => do
    if body.isAppOfArity ``Obligation 1 then
      return some ⟨name, info.levelParams, (← mkForallFVars xs body.appArg!), #[]⟩
    if info.type.getUsedConstants.contains ``Obligation then
      throwError "obligation ledger: unsupported declaration shape at {name}"
    return none

syntax (name := proofWanted) "#proof_wanted " ident : command
@[command_elab proofWanted] def elabProofWanted : CommandElab := fun stx => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let some goal ← readGoal name | throwError "obligation ledger: {name} is not an obligation"
    addWanted (name ++ `wanted) goal.levels goal.proposition

syntax (name := typedStateObligations)
  "#typed_state_obligations " ident " ceiling " num " using " tacticSeq : command

@[command_elab typedStateObligations] def elabTypedStateObligations : CommandElab := fun stx => do
  let scope := stx[1].getId
  let limit := stx[3].toNat
  let tactic := stx[5]
  let report ← liftTermElabM do
    let env ← getEnv
    let names := env.constants.toList.map (·.1) |>.filter (scope.isPrefixOf ·)
      |>.toArray.qsort (·.toString < ·.toString)
    let mut goals : Array Goal := #[]
    let mut placeholders : Array Name := #[]
    for name in names do
      if let some goal ← readGoal name then goals := goals.push goal
      let ci ← getConstInfo name
      -- a marker is recognized under any binders, so a parameterized leftover is stale, not invisible
      let marker ← forallTelescope ci.type fun _ body => pure (body.isAppOfArity ``ProofWanted 1)
      if marker then placeholders := placeholders.push name
    if goals.isEmpty then throwError "obligation ledger: no declared goals under {scope}"
    for name in placeholders do
      unless goals.any (fun g => g.id ++ `wanted == name) do
        throwError "obligation ledger: stale placeholder {name}"
    let mut entries : Array Entry := #[]
    -- every mismatch is collected, so one run reports the whole residue of a scope
    let mut missing : Array Name := #[]
    let mut stale : Array Name := #[]
    for goal in goals do
      let wanted := goal.id ++ `wanted
      let checked := goal.id ++ `checked
      match ← ProofGraph.search goal.proposition tactic 40000 with
      | .ok proof =>
        if placeholders.contains wanted then
          stale := stale.push goal.id
        if let some _ := (← getEnv).find? checked then
          let ref : ProofRef := ⟨checked, goal.levels, goal.proposition⟩
          if let .error why ← ref.validate then throwError why
        else
          discard <| addTheorem checked goal.levels goal.proposition proof
        entries := entries.push ⟨goal.id, .proved checked⟩
      | .error _ =>
        unless placeholders.contains wanted do
          missing := missing.push goal.id
        entries := entries.push ⟨goal.id, .wanted wanted⟩
    unless stale.isEmpty do
      throwError "obligation ledger: proved goals still have a placeholder: {stale}"
    unless missing.isEmpty do
      throwError "obligation ledger: missing proof or placeholder for {missing}"
    ProofGraph.check goals entries limit
  logInfo m!"{scope}: {report.wanted} open, {report.proved} proved, {report.wanted + report.proved} total; ceiling {limit}"

end Effect4.Laws.Auto.Obligations

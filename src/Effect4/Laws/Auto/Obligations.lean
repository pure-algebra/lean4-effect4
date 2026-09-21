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
      unless info matches .thmInfo _ do
        throwError "obligation ledger: {name} must be declared as a theorem"
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

/-- An explicit term proves the extracted proposition, never the empty obligation marker. -/
syntax (name := obligationProved) "#obligation_proved " ident " := " term : command

@[command_elab obligationProved] def elabObligationProved : CommandElab := fun stx => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let some goal ← readGoal name | throwError "obligation ledger: {name} is not an obligation"
    let proof ← Term.withLevelNames goal.levels <| Term.withoutErrToSorry do
      let proof ← Term.elabTermEnsuringType stx[3] goal.proposition
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars proof
    discard <| addTheorem (name ++ `checked) goal.levels goal.proposition proof

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
      let existing := (← getEnv).contains checked
      if existing then
        let ref : ProofRef := ⟨checked, goal.levels, goal.proposition⟩
        if let .error why ← ref.validate then throwError why
      let searched ← ProofGraph.search goal.proposition tactic 40000
      let proved ← if existing then pure true else do
        match searched with
        | .ok proof =>
          discard <| addTheorem checked goal.levels goal.proposition proof
          pure true
        | .error _ => pure false
      if proved then
        if placeholders.contains wanted then
          stale := stale.push goal.id
        entries := entries.push ⟨goal.id, .proved checked⟩
      else
        unless placeholders.contains wanted do
          missing := missing.push goal.id
        entries := entries.push ⟨goal.id, .wanted wanted⟩
    unless stale.isEmpty do
      throwError "obligation ledger: proved goals still have a placeholder: {stale}"
    unless missing.isEmpty do
      throwError "obligation ledger: missing proof or placeholder for {missing}"
    ProofGraph.check goals entries limit
  logInfo m!"{scope}: {report.wanted} open, {report.proved} proved, {report.wanted + report.proved} total; ceiling {limit}"

/-- Compare complete obligation propositions with namesake laws from their source module.
A checked adapter is required when their argument order differs. Name discovery is audit
metadata only: it never publishes proof evidence or closes a ledger row. -/
syntax (name := obligationAudit) "#obligation_audit " ident : command

@[command_elab obligationAudit] def elabObligationAudit : CommandElab := fun stx => do
  let scope := stx[1].getId
  liftTermElabM do
    let env ← getEnv
    let mut laws : Std.HashMap Name (Array Name) := {}
    let mut goals : Array Goal := #[]
    for (name, info) in env.constants.toList do
      if scope.isPrefixOf name then
        if let some goal ← readGoal name then goals := goals.push goal
      if let .thmInfo _ := info then
        let leaf := name.components.getLast!
        laws := laws.insert leaf ((laws[leaf]?.getD #[]).push name)
    if goals.isEmpty then throwError "obligation audit: no declared goals under {scope}"
    let mut paired : Nat := 0
    let mut unpaired : Array Name := #[]
    let mut failures : Array Name := #[]
    for goal in goals.qsort (·.id.toString < ·.id.toString) do
      let direct := goal.id.getPrefix.getPrefix ++ goal.id.components.getLast!
      let candidates := (laws[goal.id.components.getLast!]?.getD #[]).filter fun name =>
        name != goal.id && env.getModuleIdxFor? name == env.getModuleIdxFor? goal.id
      let mut backing : Option Name := none
      for candidate in candidates do
        if (← readGoal candidate).isNone then
          if candidate == direct ||
              (← isDefEq goal.proposition (← getConstInfo candidate).type) then
            backing := some candidate
      let some lawName := backing | unpaired := unpaired.push goal.id; continue
      paired := paired + 1
      let law ← getConstInfo lawName
      let a ← forallTelescope goal.proposition fun xs _ => pure xs.size
      let b ← forallTelescope law.type fun xs _ => pure xs.size
      let exactType ← isDefEq goal.proposition law.type
      let adapted ← if exactType then pure false else do
        let ref : ProofRef := ⟨goal.id ++ `checked, goal.levels, goal.proposition⟩
        pure (← ref.validate).isOk
      logInfo m!"{goal.id}: {a}/{b} binders; law {lawName}; exact {exactType}; adapter {adapted}"
      if a != b || (!exactType && !adapted) then failures := failures.push goal.id
    unless failures.isEmpty do
      throwError "obligation audit: statement mismatch for {failures}"
    logInfo m!"{scope}: {paired} paired, {unpaired.size} without a namesake, 0 mismatches"

end Effect4.Laws.Auto.Obligations

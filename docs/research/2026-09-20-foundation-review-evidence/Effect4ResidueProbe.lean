import Effect4.Laws
import Test.Audit.Obligations
import Test.Audit.IndexedColumns
import ProofGraph.Proof

open Lean Meta Elab Command ProofGraph

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let env ← getEnv
  let wantedNames := env.constants.toList.map (·.1) |>.filter
    (fun n => n.getString! == "wanted") |>.toArray.qsort (·.toString < ·.toString)
  let theorems := env.constants.toList.filterMap fun (n, ci) =>
    match ci with
    | .thmInfo t => some (n, t)
    | _ => none
  let mut sourceCount : Nat := 0
  let mut testCount : Nat := 0
  let mut exactCount : Nat := 0
  let mut proposedCount : Nat := 0
  for wantedName in wantedNames do
    let goalName := wantedName.getPrefix
    if !(Name.mkSimple "Effect4").isPrefixOf goalName &&
        !(Name.mkSimple "Test").isPrefixOf goalName then continue
    let some info := env.find? goalName | continue
    let maybeProp ← forallTelescope info.type fun xs body => do
      if body.isAppOfArity ``Obligation 1 then
        return some (← mkForallFVars xs body.appArg!)
      return none
    let some proposition := maybeProp | continue
    if (Name.mkSimple "Effect4").isPrefixOf goalName then sourceCount := sourceCount + 1
    else testCount := testCount + 1
    let proposed := goalName.getPrefix.getPrefix ++ Name.mkSimple goalName.getString!
    let proposedRef : ProofRef := ⟨proposed, info.levelParams, proposition⟩
    let proposedResult ← proposedRef.validate
    if let .ok _ := proposedResult then proposedCount := proposedCount + 1
    let mut exact : Array Name := #[]
    let mut mismatched : Array String := #[]
    for (n, _) in theorems do
      if n.getString! != goalName.getString! &&
          !(goalName.getString! == "source_fork_extension" && n.getString! == "fork_source_extension") then continue
      let reference : ProofRef := ⟨n, info.levelParams, proposition⟩
      match ← reference.validate with
      | .ok _ => exact := exact.push n
      | .error why => mismatched := mismatched.push why
    if !exact.isEmpty then exactCount := exactCount + 1
    let proposedText := match proposedResult with
      | .ok _ => "valid"
      | .error why => why
    logInfo m!"RESIDUE {goalName}\n  proposed: {proposedText}\n  exact: {exact}\n  rejected: {mismatched}"
  logInfo m!"TOTAL source={sourceCount}, test={testCount}, exact theorem matches={exactCount}, proposed algorithm matches={proposedCount}"

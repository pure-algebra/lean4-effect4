import Effect4.Laws
import Test.Audit.IndexedColumns
import ProofGraph.Proof

open Lean Meta Elab Command ProofGraph

def cappedRef (p : ProofRef) : TermElabM (Except String Unit) :=
  withoutModifyingState do
    tryCatchRuntimeEx
      (withOptions (fun o => Elab.async.set (maxHeartbeats.set o 4000) false) <|
        withTheReader Core.Context
          (fun ctx => { ctx with maxHeartbeats := Core.getMaxHeartbeats ctx.options }) <|
        withCurrHeartbeats do p.validate)
      (fun ex => return .error ("INCONCLUSIVE: " ++ (← ex.toMessageData.toString)))

set_option maxHeartbeats 0 in
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
    IO.println s!"BEGIN {goalName}"
    let proposedResult ← cappedRef proposedRef
    if let .ok _ := proposedResult then proposedCount := proposedCount + 1
    let mut exact : Array Name := #[]
    let mut mismatched : Array String := #[]
    for (n, _) in theorems do
      if n.getString! != goalName.getString! &&
          !(goalName.getString! == "source_fork_extension" && n.getString! == "fork_source_extension") &&
          !(goalName.getString! == "supervision_static" &&
            ["supervision_static_flags", "supervision_static_origins"].contains n.getString!) &&
          !(goalName.getString! == "source_fork" && n.getString! == "source_fork_holds") &&
          !(goalName.getString! == "race_launch_origins" && n.getString! == "race_launch_origins_holds") then continue
      let reference : ProofRef := ⟨n, info.levelParams, proposition⟩
      match ← cappedRef reference with
      | .ok _ => exact := exact.push n
      | .error why => mismatched := mismatched.push why
    if !exact.isEmpty then exactCount := exactCount + 1
    let proposedText := match proposedResult with
      | .ok _ => "valid"
      | .error why => why
    IO.println s!"RESIDUE {goalName}\n  proposed: {proposedText}\n  exact: {exact}\n  rejected or inconclusive: {mismatched}"
  logInfo m!"TOTAL source={sourceCount}, test={testCount}, exact theorem matches={exactCount}, proposed algorithm matches={proposedCount}"

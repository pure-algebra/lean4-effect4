import Effect4.Laws
import Lean
open Lean Meta Elab Command
run_cmd liftTermElabM do
  let env ← getEnv
  let names := env.constants.toList.map (·.1) |>.filter ((`Effect4).isPrefixOf ·)
    |>.toArray.qsort (·.toString < ·.toString)
  let mut laws : Std.HashMap String (Array Name) := {}
  for n in names do
    if let some (.thmInfo _) := env.find? n then
      laws := laws.insert n.getString! ((laws[n.getString!]?.getD #[]).push n)
  let mut total : Nat := 0
  let mut paired : Nat := 0
  let mut mismatch : Nat := 0
  for n in names do
    let ci ← getConstInfo n
    let goal? ← forallTelescope ci.type fun xs body => do
      if body.isAppOfArity ``ProofGraph.Obligation 1 then
        return some (xs.size, ← mkForallFVars xs body.appArg!)
      return none
    if let some (_, goal) := goal? then
      total := total + 1
      let mut candidate := n.getPrefix.getPrefix ++ Name.mkSimple n.getString!
      unless (env.find? candidate).isSome do
        let localLaws := (laws[n.getString!]?.getD #[]).filter fun other =>
          env.getModuleIdxFor? other == env.getModuleIdxFor? n
        for other in localLaws do
          if ← isDefEq goal (← getConstInfo other).type then
            candidate := other
      let explicit : List (Name × Name) := [
        (`Effect4.Program.Sched.M1Origin.actionAt_fork, `Effect4.Program.Sched.actionAt_fork),
        (`Effect4.Program.Sched.M1Origin.actionAt_forkIn, `Effect4.Program.Sched.actionAt_forkIn),
        (`Effect4.Program.Sched.M1Origin.actionAt_not_forkScoped, `Effect4.Program.Sched.actionAt_not_forkScoped),
        (`Effect4.Program.Sched.M1Origin.actionAt_raceAll, `Effect4.Program.Sched.actionAt_raceAll),
        (`Effect4.Program.Sched.M1Actions.scopeLinkFiber_ok, `Effect4.Program.Sched.scopeLinkFiber_ok),
        (`Effect4.Program.Sched.M1Origin.fork_rel, `Effect4.Program.Sched.fork_rel),
        (`Effect4.Program.Sched.M1Origin.forkIn_rel, `Effect4.Program.Sched.forkIn_rel),
        (`Effect4.Program.Sched.M1Origin.raceAll_rel, `Effect4.Program.Sched.raceAll_rel),
        (`Effect4.Machine.M1Clock.book_advanceState, `Effect4.Machine.book_advanceState),
        (`Effect4.Program.Sched.M1Drive.dropFinalizer_ok, `Effect4.Program.Sched.dropFinalizer_ok),
        (`Effect4.Program.Sched.M1Deliver.storesOk_closeScopeUnsafe, `Effect4.Program.Sched.storesOk_closeScopeUnsafe),
        (`Effect4.Program.Typed.WorldWanted.memoBuild_extension, `Effect4.Program.Typed.memoBuild_extension),
        (`Effect4.Program.Typed.M2ForkSourceWanted.source_fork_extension, `Effect4.Program.Typed.M2ForkSourceWanted.fork_source_extension),
        (`Effect4.Api.M1Trace.fork_forked, `Effect4.Api.fork_forked),
        (`Effect4.Api.M1Trace.forkScoped_forked, `Effect4.Api.forkScoped_forked),
        (`Effect4.Api.M1Trace.forkFinalizers_forked, `Effect4.Api.forkFinalizers_forked),
        (`Effect4.Api.M1Trace.supervision_static, `Effect4.Api.TraceFacts.supervision_static_flags),
        (`Effect4.Api.M1Origin.supervision_static, `Effect4.Api.supervision_static_origins),
        (`Effect4.Api.M1Origin.source_fork, `Effect4.Api.source_fork_holds),
        (`Effect4.Api.M1Origin.race_launch_origins, `Effect4.Api.race_launch_origins_holds),
        (`Effect4.Machine.M1Origin.spawnChild_keys_subset, `Effect4.Machine.spawnChild_keys_subset),
        (`Effect4.Machine.M1Origin.spawn_minted, `Effect4.Machine.spawn_minted),
        (`Effect4.Machine.M1Origin.fork_arm_minted, `Effect4.Machine.fork_arm_minted),
        (`Effect4.Machine.M1Origin.withFiber_fork_minted, `Effect4.Machine.withFiber_fork_minted),
        (`Effect4.Machine.M1.Handles.register_keys, `Effect4.Machine.DeferredStore.register_keys),
        (`Effect4.Machine.M1.Handles.complete_keys, `Effect4.Machine.DeferredStore.complete_keys),
        (`Effect4.Machine.M1.Handles.drainDue_keys, `Effect4.Machine.DeferredStore.drainDue_keys),
        (`Effect4.Machine.M1.Handles.setCell_keys_of_subset, `Effect4.Machine.DeferredStore.setCell_keys_of_subset),
        (`Effect4.Machine.M1.Handles.setCell_appendDue_keys, `Effect4.Machine.DeferredStore.setCell_appendDue_keys),
        (`Effect4.Program.Guard.NativeState.M1Results.countdown, `Effect4.Program.Guard.NativeState.StateStep.countdown_result)]
      if let some (_, target) := explicit.find? (·.1 == n) then candidate := target
      let count ← forallTelescope goal fun xs _ => pure xs.size
      if let some (.thmInfo thm) := env.find? candidate then
        paired := paired + 1
        let lawCount ← forallTelescope thm.type fun xs _ => pure xs.size
        let same ← isDefEq goal thm.type
        if count != lawCount || !same then mismatch := mismatch + 1
        logInfo m!"PAIR {n} {candidate} binders={count}/{lawCount} exact={same}"
        if count != lawCount || !same then
          logInfo m!"OBLIGATION {goal}\nLAW {thm.type}"
      else
        let candidates := laws[n.getString!]?.getD #[]
        logInfo m!"UNPAIRED {n} binders={count} candidates={candidates}"
  logInfo m!"AUDIT total={total} paired={paired} mismatches={mismatch}"

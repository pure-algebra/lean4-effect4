import Effect4.Laws
import Test.Counterexamples.Machine.Semantics.ActionAtRaceAllPremise
open Lean Meta Elab Command ProofGraph
#obligation_audit Effect4
run_cmd liftTermElabM do
  let env ← getEnv
  let mut goals : Array Goal := #[]
  let mut entries : Array Entry := #[]
  for (name, info) in env.constants.toList do
    if (`Effect4).isPrefixOf name then
      let goal? ← forallTelescope info.type fun xs body => do
        if body.isAppOfArity ``Obligation 1 then
          return some (⟨name, info.levelParams, ← mkForallFVars xs body.appArg!, #[]⟩ : Goal)
        return none
      if let some goal := goal? then
        goals := goals.push goal
        let checked := name ++ `checked
        if env.contains checked then
          unless !env.contains (name ++ `wanted) do throwError "stale marker {name}"
          entries := entries.push ⟨name, .proved checked⟩
        else
          entries := entries.push ⟨name, .wanted (name ++ `wanted)⟩
          logInfo m!"OPEN {name}"
  let report ← ProofGraph.check goals entries 9
  logInfo m!"UNIQUE LEDGER: {goals.size} total; {report.proved} proved; {report.wanted} open"
#print axioms Effect4.Program.Sched.M1Origin.actionAt_fork.checked
#print axioms Effect4.Program.Sched.M1Origin.actionAt_forkIn.checked
#print axioms Effect4.Program.Sched.M1Origin.actionAt_not_forkScoped.checked
#print axioms Effect4.Program.Sched.M1Origin.actionAt_raceAll.checked
#print axioms Effect4.Program.Sched.M1Actions.scopeLinkFiber_ok.checked
#print axioms Effect4.Program.Sched.M1Origin.fork_rel.checked
#print axioms Effect4.Program.Sched.M1Origin.forkIn_rel.checked
#print axioms Effect4.Program.Sched.M1Origin.raceAll_rel.checked
#print axioms Effect4.Machine.M1Clock.book_advanceState.checked
#print axioms Effect4.Program.Sched.M1Drive.dropFinalizer_ok.checked
#print axioms Effect4.Program.Sched.M1Deliver.storesOk_closeScopeUnsafe.checked
#print axioms Effect4.Program.Typed.WorldWanted.memoBuild_extension.checked
#print axioms Effect4.Program.Typed.M2ForkSourceWanted.source_fork_extension.checked
#print axioms Effect4.Api.M1Trace.fork_forked.checked
#print axioms Effect4.Api.M1Trace.forkScoped_forked.checked
#print axioms Effect4.Api.M1Trace.forkFinalizers_forked.checked
#print axioms Effect4.Api.M1Trace.supervision_static.checked
#print axioms Effect4.Api.M1Origin.supervision_static.checked
#print axioms Effect4.Api.M1Origin.source_fork.checked
#print axioms Effect4.Api.M1Origin.race_launch_origins.checked
#print axioms Effect4.Machine.M1Origin.spawnChild_keys_subset.checked
#print axioms Effect4.Machine.M1Origin.spawn_minted.checked
#print axioms Effect4.Machine.M1Origin.fork_arm_minted.checked
#print axioms Effect4.Machine.M1Origin.withFiber_fork_minted.checked
#print axioms Effect4.Machine.M1.Handles.register_keys.checked
#print axioms Effect4.Machine.M1.Handles.complete_keys.checked
#print axioms Effect4.Machine.M1.Handles.drainDue_keys.checked
#print axioms Effect4.Machine.M1.Handles.setCell_keys_of_subset.checked
#print axioms Effect4.Machine.M1.Handles.setCell_appendDue_keys.checked
#print axioms Effect4.Program.Sched.M1PendingOrigin.fork_pendingOk.checked
#print axioms Effect4.Program.Sched.M1PendingOrigin.forkIn_pendingOk.checked
#print axioms Effect4.Program.Sched.M1PendingOrigin.forkScoped_pendingOk.checked

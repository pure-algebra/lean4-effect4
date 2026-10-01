import Lean.Util.CollectAxioms
import Effect4.Laws.Program.Guard.ForkLedger

/- Source-enumerated D theorem receipt, generated from the staged production files.
No Lean process was run by this generator. Every public theorem gets its own print.
The single private theorem is resolved by exact user name AND owning module below. -/

-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:24
#print axioms Effect4.Machine.ForkLedger.Invariant.ViewOk.of_view
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:33
#print axioms Effect4.Machine.ForkLedger.Invariant.ViewOk.fresh_ids
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:38
#print axioms Effect4.Machine.ForkLedger.Invariant.ViewOk.fresh_children
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:52
#print axioms Effect4.Machine.ForkLedger.Invariant.ViewOk.spawn
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:74
#print axioms Effect4.Machine.ForkLedger.Invariant.ViewOk.root
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:98
#print axioms Effect4.Machine.ForkLedger.Invariant.of_view
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:104
#print axioms Effect4.Machine.ForkLedger.Invariant.fiber_ids_unique
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:107
#print axioms Effect4.Machine.ForkLedger.Invariant.record_children_unique
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:110
#print axioms Effect4.Machine.ForkLedger.Invariant.fiber_below
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:114
#print axioms Effect4.Machine.ForkLedger.Invariant.record_below
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:118
#print axioms Effect4.Machine.ForkLedger.Invariant.record_corresponds
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:123
#print axioms Effect4.Machine.ForkLedger.Invariant.fresh
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:128
#print axioms Effect4.Machine.ForkLedger.Invariant.fresh_fiber_lookup
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:137
#print axioms Effect4.Machine.ForkLedger.Invariant.empty_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:142
#print axioms Effect4.Machine.ForkLedger.Invariant.update_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:146
#print axioms Effect4.Machine.ForkLedger.Invariant.emit_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:149
#print axioms Effect4.Machine.ForkLedger.Invariant.updateRace_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:152
#print axioms Effect4.Machine.ForkLedger.Invariant.halt_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:155
#print axioms Effect4.Machine.ForkLedger.Invariant.arm_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:158
#print axioms Effect4.Machine.ForkLedger.Invariant.disarm_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:161
#print axioms Effect4.Machine.ForkLedger.Invariant.state_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:164
#print axioms Effect4.Machine.ForkLedger.Invariant.middleware_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:167
#print axioms Effect4.Machine.ForkLedger.Invariant.modify_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:175
#print axioms Effect4.Machine.ForkLedger.Invariant.mapFibers_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:184
#print axioms Effect4.Machine.ForkLedger.Invariant.postTask_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:192
#print axioms Effect4.Machine.ForkLedger.Invariant.start_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:199
#print axioms Effect4.Machine.ForkLedger.Invariant.drainOwed_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:216
#print axioms Effect4.Machine.ForkLedger.Invariant.spawn_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:227
#print axioms Effect4.Machine.ForkLedger.Invariant.launchEntrant_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:233
#print axioms Effect4.Machine.ForkLedger.Invariant.forkFinalizers_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:243
#print axioms Effect4.Machine.ForkLedger.Invariant.settle_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:257
#print axioms Effect4.Machine.ForkLedger.Invariant.interruptEdit_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:272
#print axioms Effect4.Machine.ForkLedger.Invariant.edits
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:285
#print axioms Effect4.Machine.ForkLedger.Invariant.stepDecision_ok
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:301
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_update_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:310
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_emit_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:314
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_modify_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:323
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_updateRace_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:327
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_arm_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:331
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_disarm_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:335
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_halt_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:339
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_state_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:343
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_token_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:347
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_state_token_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:351
#print axioms Effect4.Machine.ForkLedger.Invariant.ok_middleware_iff
-- src/Effect4/Laws/Machine/ForkLedgerInvariant.lean:354
#print axioms Effect4.Machine.ForkLedger.Invariant.appendRoot_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:11
#print axioms Effect4.Machine.ForkLedger.Invariant.load_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:27
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.countdown_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:37
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.countdown_result_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:46
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.linkScope_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:53
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.interruptEach_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:65
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.interruptEach_result_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:74
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.beginRace_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:78
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.registerRace_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:85
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.stepFrame_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:91
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.finalizerOr_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:102
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.withFiber_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:115
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.evaluatePrim_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:124
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.enterScoped_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:128
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.exitScoped_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:142
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.evaluateNative_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:154
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.iteration_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:170
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.exitFiber_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:176
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.fireObserver_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:187
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.driveStep_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:199
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.steppedBy_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:207
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.drive_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:216
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.runFork_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:225
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.runCallback_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:234
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.reachable_ok
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:241
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.reachable_unique
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:246
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.reachable_bounded
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:254
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.reachable_corresponding
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:261
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.reachable_fresh
-- src/Effect4/Laws/Program/Guard/ForkLedger.lean:275
#print axioms Effect4.Machine.ForkLedger.Invariant.Native.update_with_bank
-- Resolve the actual private constant, never a guessed _private numeric suffix.
run_cmd do
  let env ← Lean.getEnv
  let owner := `Effect4.Laws.Machine.ForkLedgerInvariant
  let user := `Effect4.Machine.ForkLedger.Invariant.ViewOk.nodup_snoc
  let some ownerIdx := env.getModuleIdx? owner
    | throwError "D private theorem owner is not imported: {owner}"
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if Lean.privateToUserName? name == some user &&
        env.getModuleIdxFor? name == some ownerIdx then some name else none
  match candidates with
  | [name] =>
    let deps ← Lean.collectAxioms name
    Lean.logInfo m!"'{name}' depends on axioms: {deps}"
    unless deps.all (fun dep => dep == ``propext || dep == ``Quot.sound) do
      throwError "D private theorem exceeds the axiom ceiling: {name}: {deps}"
  | _ => throwError "D private theorem {user} resolved to {candidates.length} constants; expected exactly one"

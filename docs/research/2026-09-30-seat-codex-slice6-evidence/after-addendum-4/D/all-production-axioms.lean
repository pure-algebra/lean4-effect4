import Lean.Util.CollectAxioms
import Effect4.Laws.Program.Guard.ForkLedger
import Test.Api.TraceOrigin

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
-- Test/Api/TraceOrigin.lean:29
#print axioms Effect4.Api.M1Trace.forkedOf_append
-- Test/Api/TraceOrigin.lean:35
#print axioms Effect4.Api.forkedOf_append
-- Test/Api/TraceOrigin.lean:39
#print axioms Effect4.Api.M1Trace.spawn_forked
-- Test/Api/TraceOrigin.lean:47
#print axioms Effect4.Api.spawn_forked
-- Test/Api/TraceOrigin.lean:55
#print axioms Effect4.Api.M1Trace.start_forked
-- Test/Api/TraceOrigin.lean:62
#print axioms Effect4.Api.start_forked
-- Test/Api/TraceOrigin.lean:68
#print axioms Effect4.Api.M1Trace.fork_forked
-- Test/Api/TraceOrigin.lean:77
#print axioms Effect4.Api.fork_forked
-- Test/Api/TraceOrigin.lean:86
#print axioms Effect4.Api.M1Trace.forkIn_forked
-- Test/Api/TraceOrigin.lean:95
#print axioms Effect4.Api.forkIn_forked
-- Test/Api/TraceOrigin.lean:103
#print axioms Effect4.Api.M1Trace.forkScoped_forked
-- Test/Api/TraceOrigin.lean:113
#print axioms Effect4.Api.forkScoped_forked
-- Test/Api/TraceOrigin.lean:123
#print axioms Effect4.Api.M1Trace.forkScoped_none_forked
-- Test/Api/TraceOrigin.lean:132
#print axioms Effect4.Api.forkScoped_none_forked
-- Test/Api/TraceOrigin.lean:142
#print axioms Effect4.Api.M1Trace.launchEntrant_forked
-- Test/Api/TraceOrigin.lean:151
#print axioms Effect4.Api.launchEntrant_forked
-- Test/Api/TraceOrigin.lean:159
#print axioms Effect4.Api.M1Trace.forkFinalizers_forked
-- Test/Api/TraceOrigin.lean:169
#print axioms Effect4.Api.forkFinalizers_forked
-- Test/Api/TraceOrigin.lean:186
#print axioms Effect4.Api.M1Trace.action_fork_forked
-- Test/Api/TraceOrigin.lean:195
#print axioms Effect4.Api.action_fork_forked
-- Test/Api/TraceOrigin.lean:205
#print axioms Effect4.Api.M1Trace.action_forkIn_forked
-- Test/Api/TraceOrigin.lean:214
#print axioms Effect4.Api.action_forkIn_forked
-- Test/Api/TraceOrigin.lean:223
#print axioms Effect4.Api.M1Trace.action_forkScoped_forked
-- Test/Api/TraceOrigin.lean:233
#print axioms Effect4.Api.action_forkScoped_forked
-- Test/Api/TraceOrigin.lean:242
#print axioms Effect4.Api.M1Trace.supervision_static
-- Test/Api/TraceOrigin.lean:262
#print axioms Effect4.Api.TraceFacts.supervision_static_flags
-- Test/Api/TraceOrigin.lean:302
#print axioms Effect4.Api.TraceFacts.M1Trace.load_agrees
-- Test/Api/TraceOrigin.lean:333
#print axioms Effect4.Api.TraceFacts.Agreement.noFork_nil
-- Test/Api/TraceOrigin.lean:336
#print axioms Effect4.Api.TraceFacts.Agreement.noFork_append
-- Test/Api/TraceOrigin.lean:344
#print axioms Effect4.Api.TraceFacts.Agreement.forkedOf_frame_map
-- Test/Api/TraceOrigin.lean:353
#print axioms Effect4.Api.TraceFacts.Agreement.noFork_frame_map
-- Test/Api/TraceOrigin.lean:359
#print axioms Effect4.Api.TraceFacts.Agreement.ok_update_iff
-- Test/Api/TraceOrigin.lean:364
#print axioms Effect4.Api.TraceFacts.Agreement.ok_emit_iff
-- Test/Api/TraceOrigin.lean:375
#print axioms Effect4.Api.TraceFacts.Agreement.ok_modify_iff
-- Test/Api/TraceOrigin.lean:384
#print axioms Effect4.Api.TraceFacts.Agreement.ok_updateRace_iff
-- Test/Api/TraceOrigin.lean:388
#print axioms Effect4.Api.TraceFacts.Agreement.ok_arm_iff
-- Test/Api/TraceOrigin.lean:392
#print axioms Effect4.Api.TraceFacts.Agreement.ok_disarm_iff
-- Test/Api/TraceOrigin.lean:396
#print axioms Effect4.Api.TraceFacts.Agreement.ok_halt_iff
-- Test/Api/TraceOrigin.lean:400
#print axioms Effect4.Api.TraceFacts.Agreement.ok_state_iff
-- Test/Api/TraceOrigin.lean:404
#print axioms Effect4.Api.TraceFacts.Agreement.ok_token_iff
-- Test/Api/TraceOrigin.lean:408
#print axioms Effect4.Api.TraceFacts.Agreement.ok_state_token_iff
-- Test/Api/TraceOrigin.lean:412
#print axioms Effect4.Api.TraceFacts.Agreement.ok_middleware_iff
-- Test/Api/TraceOrigin.lean:416
#print axioms Effect4.Api.TraceFacts.Agreement.ok_fibers_iff
-- Test/Api/TraceOrigin.lean:421
#print axioms Effect4.Api.TraceFacts.Agreement.update_keeps
-- Test/Api/TraceOrigin.lean:424
#print axioms Effect4.Api.TraceFacts.Agreement.emit_keeps
-- Test/Api/TraceOrigin.lean:428
#print axioms Effect4.Api.TraceFacts.Agreement.update_ok
-- Test/Api/TraceOrigin.lean:432
#print axioms Effect4.Api.TraceFacts.Agreement.emit_ok
-- Test/Api/TraceOrigin.lean:436
#print axioms Effect4.Api.TraceFacts.Agreement.updateRace_ok
-- Test/Api/TraceOrigin.lean:439
#print axioms Effect4.Api.TraceFacts.Agreement.halt_ok
-- Test/Api/TraceOrigin.lean:442
#print axioms Effect4.Api.TraceFacts.Agreement.arm_ok
-- Test/Api/TraceOrigin.lean:445
#print axioms Effect4.Api.TraceFacts.Agreement.disarm_ok
-- Test/Api/TraceOrigin.lean:448
#print axioms Effect4.Api.TraceFacts.Agreement.state_ok
-- Test/Api/TraceOrigin.lean:451
#print axioms Effect4.Api.TraceFacts.Agreement.middleware_ok
-- Test/Api/TraceOrigin.lean:454
#print axioms Effect4.Api.TraceFacts.Agreement.modify_ok
-- Test/Api/TraceOrigin.lean:458
#print axioms Effect4.Api.TraceFacts.Agreement.mapFibers_ok
-- Test/Api/TraceOrigin.lean:462
#print axioms Effect4.Api.TraceFacts.Agreement.appendRoot_ok
-- Test/Api/TraceOrigin.lean:466
#print axioms Effect4.Api.TraceFacts.Agreement.postTask_ok
-- Test/Api/TraceOrigin.lean:474
#print axioms Effect4.Api.TraceFacts.Agreement.start_ok
-- Test/Api/TraceOrigin.lean:481
#print axioms Effect4.Api.TraceFacts.Agreement.drainOwed_ok
-- Test/Api/TraceOrigin.lean:497
#print axioms Effect4.Api.TraceFacts.Agreement.spawn_forked_site
-- Test/Api/TraceOrigin.lean:510
#print axioms Effect4.Api.TraceFacts.Agreement.spawn_iff
-- Test/Api/TraceOrigin.lean:530
#print axioms Effect4.Api.TraceFacts.Agreement.spawn_keeps
-- Test/Api/TraceOrigin.lean:536
#print axioms Effect4.Api.TraceFacts.Agreement.spawn_ok
-- Test/Api/TraceOrigin.lean:543
#print axioms Effect4.Api.TraceFacts.Agreement.launchEntrant_ok
-- Test/Api/TraceOrigin.lean:549
#print axioms Effect4.Api.TraceFacts.Agreement.forkFinalizers_ok
-- Test/Api/TraceOrigin.lean:559
#print axioms Effect4.Api.TraceFacts.Agreement.settle_ok
-- Test/Api/TraceOrigin.lean:573
#print axioms Effect4.Api.TraceFacts.Agreement.interruptEdit_ok
-- Test/Api/TraceOrigin.lean:598
#print axioms Effect4.Api.TraceFacts.Agreement.agrees_updates
-- Test/Api/TraceOrigin.lean:606
#print axioms Effect4.Api.TraceFacts.Agreement.agrees_edits
-- Test/Api/TraceOrigin.lean:619
#print axioms Effect4.Api.TraceFacts.Agreement.edits
-- Test/Api/TraceOrigin.lean:638
#print axioms Effect4.Api.TraceFacts.Agreement.Native.countdown_ok
-- Test/Api/TraceOrigin.lean:649
#print axioms Effect4.Api.TraceFacts.Agreement.Native.countdown_result_ok
-- Test/Api/TraceOrigin.lean:658
#print axioms Effect4.Api.TraceFacts.Agreement.Native.linkScope_ok
-- Test/Api/TraceOrigin.lean:665
#print axioms Effect4.Api.TraceFacts.Agreement.Native.interruptEach_ok
-- Test/Api/TraceOrigin.lean:677
#print axioms Effect4.Api.TraceFacts.Agreement.Native.interruptEach_result_ok
-- Test/Api/TraceOrigin.lean:686
#print axioms Effect4.Api.TraceFacts.Agreement.Native.beginRace_ok
-- Test/Api/TraceOrigin.lean:692
#print axioms Effect4.Api.TraceFacts.Agreement.Native.registerRace_ok
-- Test/Api/TraceOrigin.lean:699
#print axioms Effect4.Api.TraceFacts.Agreement.Native.stepFrame_ok
-- Test/Api/TraceOrigin.lean:705
#print axioms Effect4.Api.TraceFacts.Agreement.Native.finalizerOr_ok
-- Test/Api/TraceOrigin.lean:716
#print axioms Effect4.Api.TraceFacts.Agreement.Native.withFiber_ok
-- Test/Api/TraceOrigin.lean:729
#print axioms Effect4.Api.TraceFacts.Agreement.Native.evaluatePrim_ok
-- Test/Api/TraceOrigin.lean:738
#print axioms Effect4.Api.TraceFacts.Agreement.Native.enterScoped_ok
-- Test/Api/TraceOrigin.lean:742
#print axioms Effect4.Api.TraceFacts.Agreement.Native.exitScoped_ok
-- Test/Api/TraceOrigin.lean:756
#print axioms Effect4.Api.TraceFacts.Agreement.Native.evaluateNative_ok
-- Test/Api/TraceOrigin.lean:768
#print axioms Effect4.Api.TraceFacts.Agreement.Native.iteration_ok
-- Test/Api/TraceOrigin.lean:784
#print axioms Effect4.Api.TraceFacts.Agreement.Native.exitFiber_ok
-- Test/Api/TraceOrigin.lean:790
#print axioms Effect4.Api.TraceFacts.Agreement.Native.fireObserver_ok
-- Test/Api/TraceOrigin.lean:801
#print axioms Effect4.Api.TraceFacts.Agreement.Native.driveStep_ok
-- Test/Api/TraceOrigin.lean:813
#print axioms Effect4.Api.TraceFacts.Agreement.Native.steppedBy_ok
-- Test/Api/TraceOrigin.lean:821
#print axioms Effect4.Api.TraceFacts.Agreement.Native.drive_ok
-- Test/Api/TraceOrigin.lean:830
#print axioms Effect4.Api.TraceFacts.Agreement.Native.runFork_ok
-- Test/Api/TraceOrigin.lean:839
#print axioms Effect4.Api.TraceFacts.Agreement.Native.runCallback_ok
-- Test/Api/TraceOrigin.lean:849
#print axioms Effect4.Api.TraceFacts.Agreement.Native.load_agrees
-- Test/Api/TraceOrigin.lean:854
#print axioms Effect4.Api.TraceFacts.Agreement.Native.reachable_agrees_of
-- Test/Api/TraceOrigin.lean:867
#print axioms Effect4.Api.TraceFacts.Agreement.Native.step_agrees
-- Test/Api/TraceOrigin.lean:875
#print axioms Effect4.Api.TraceFacts.Agreement.Native.reachable_agrees
-- Test/Api/TraceOrigin.lean:890
#print axioms Effect4.Api.TraceFacts.Agreement.emit_with_bank
-- Test/Api/TraceOrigin.lean:904
#print axioms Effect4.Api.TraceFacts.M1Trace.step_agrees
-- Test/Api/TraceOrigin.lean:910
#print axioms Effect4.Api.TraceFacts.M1Trace.reachable_agrees

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

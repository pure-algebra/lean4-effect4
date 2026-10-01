import Effect4.Laws.Program.Typed.Assembly

/-!
# The split `J`/`I` as landed (decisions rows 134, 139, 140)

`#print` shows `J` (`MachineTyped`: `TypedState`, `LiveCode`, `MachineLive`) and `I`
(`ConfigTyped`: `J`, `ReadCode`, `QueueOk`) as the elaborator holds them, with the production
bundle `preds` and the generated scope-state clause the un-refused row now states. `#print axioms`
lists every theorem in `Laws/Program/Typed/Assembly.lean` and `Laws/Program/Typed/Scheduler.lean`
and the ledger's checked theorems; the trust ceiling is `[propext, Quot.sound]`. Reading aid and
axiom list; no claim is made here.
-/

open Effect4.Program.Typed

#print MachineTyped
#print TypedState
#print LiveCode
#print MachineLive
#print ConfigTyped
#print ReadCode
#print ReadsCode
#print QueueOk
#print StepPreserves
#print preds
#print ScopeStateOk
#print SnapshotTyped
#print DecisionEdits
#print DenotesTyped
#print TermFits
#print Reestablishes

#print axioms Effect4.Program.Typed.savedPosition_of_saved
#print axioms Effect4.Program.Typed.pending_below
#print axioms Effect4.Program.Typed.QueueOk.fresh
#print axioms Effect4.Program.Typed.machineTyped_of_configTyped
#print axioms Effect4.Program.Typed.machineTyped_not_halted
#print axioms Effect4.Program.Typed.evaluate_entry
#print axioms Effect4.Program.Typed.stepKeeps_of_stepPreserves
#print axioms Effect4.Program.Typed.driveState_typed_of_stepPreserves
#print axioms Effect4.Program.Typed.mem_taskCmds
#print axioms Effect4.Program.Typed.taskCmd_owner
#print axioms Effect4.Program.Typed.taskCmd_not_registrationDone
#print axioms Effect4.Program.Typed.taskCmd_not_reads
#print axioms Effect4.Program.Typed.taskCmd_not_link
#print axioms Effect4.Program.Typed.taskCmd_tail
#print axioms Effect4.Program.Typed.registrationTail_mono
#print axioms Effect4.Program.Typed.registrationQueue_append_tasks
#print axioms Effect4.Program.Typed.queueOk_append_tasks
#print axioms Effect4.Program.Typed.readsCode_append_tasks
#print axioms Effect4.Program.Typed.configTyped_append_tasks
#print axioms Effect4.Program.Typed.guarded_stepKeeps_of_stepPreserves
#print axioms Effect4.Program.Typed.machineTyped_congr
#print axioms Effect4.Program.Typed.queueOk_emit
#print axioms Effect4.Program.Typed.envTyped_append
#print axioms Effect4.Program.Typed.capture_lookup
#print axioms Effect4.Program.Typed.machineLive_of_quiet
#print axioms Effect4.Program.Typed.machineTyped_load
#print axioms Effect4.Program.Typed.envTyped_nil
#print axioms Effect4.Program.Typed.loadsTyped_of_denotesTyped
#print axioms Effect4.Program.Typed.preds_savedOk_mono
#print axioms Effect4.Program.Typed.admittedReplay_noHostAnswer
#print axioms Effect4.Program.Typed.reachable_of_ledger
#print axioms Effect4.Program.Typed.replayR_nil_machine
#print axioms Effect4.Program.Typed.rreachable_load
#print axioms Effect4.Program.Typed.queueOk_nil
#print axioms Effect4.Program.Typed.not_readsCode_taskCmds
#print axioms Effect4.Program.Typed.edit_nil
#print axioms Effect4.Program.Typed.edit_evaluate
#print axioms Effect4.Program.Typed.edit_ran
#print axioms Effect4.Program.Typed.edit_middleware
#print axioms Effect4.Program.Typed.edit_skip
#print axioms Effect4.Program.Typed.edit_task
#print axioms Effect4.Program.Typed.decisionLift_of_ledger
#print axioms Effect4.Program.Typed.decisionKeeps_of_ledger
#print axioms Effect4.Program.Typed.reestablishes
#print axioms Effect4.Program.Typed.obsTyped_of_machineTyped
#print axioms Effect4.Program.Typed.replay_stuck_eq
#print axioms Effect4.Program.Typed.m7_of_capstone
#print axioms Effect4.Program.Typed.m7_of_ledger
#print axioms Effect4.Program.Typed.replayEval_machine_prefix
#print axioms Effect4.Program.Typed.replayR_bmeans_reachable
#print axioms Effect4.Program.Typed.reifyExitVal_fits
#print axioms Effect4.Program.Typed.observerDeliveredExit_fits
#print axioms Effect4.Program.Typed.observer_exitValue_typed
#print axioms Effect4.Program.Typed.countdownAt_congr
#print axioms Effect4.Program.Typed.storedObserverOk_congr
#print axioms Effect4.Program.Typed.observerCommandOk_congr
#print axioms Effect4.Program.Typed.registrationState_load
#print axioms Effect4.Program.Typed.observerCommand_resume_typed
#print axioms Effect4.Program.Typed.requestOfR_load_none
#print axioms Effect4.Program.Typed.schedulerState_load
#print axioms Effect4.Program.Typed.observerState_load
#print axioms Effect4.Program.Typed.M3bAssembly.capture_lookup.checked
#print axioms Effect4.Program.Typed.M6Edits.nil.checked
#print axioms Effect4.Program.Typed.M6Edits.evaluate.checked
#print axioms Effect4.Program.Typed.M6Edits.ran.checked
#print axioms Effect4.Program.Typed.M6Edits.task.checked
#print axioms Effect4.Program.Typed.M6Edits.skip.checked
#print axioms Effect4.Program.Typed.M6Edits.middleware.checked
#print axioms Effect4.Program.Typed.M6Edits.reestablish.checked
#print axioms Effect4.Program.Typed.M3bWorld.preds_savedOk_mono.checked

/-! ## M5's reduction is for a program as loaded

`loadsTyped_of_denotesTyped` reduces M5 to `denoteR_typed` for a program with no layer-reference
sites. The typed corpus's `layer.ref` program (`Test/Program/TypedCorpus.lean:76`) shows why the
premise is there: `Api.typeOf` certifies the program's expansion (`Program/Typing.lean:61-64`),
the checker refuses the program as written at its reference (`Program/Checker.lean:259`), and
`loadR` loads the program as written, its reference resolved at run time by redirect
(`Laws/Program/DenoteR.lean:733-737`). So `PointTyped` fails at its root point and
`denoteR_typed` says nothing about its loaded code. -/

namespace Test.Program.TypedSplit
open Effect4 Effect4.Program Effect4.Machine

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

def layerRef : NativeEff :=
  .bind (.provideLayer (.succeed key (.nat 7)) false (.service key))
    (.provideLayer (.ref [0, 0]) false (.service key))

#guard (Api.typeOf layerRef).isSome
#guard (layerRef.refSites []).isEmpty = false
#guard match Checker.check (nativeSignature []) [] [] layerRef with
  | .ok _ => false
  | .error _ => true

end Test.Program.TypedSplit

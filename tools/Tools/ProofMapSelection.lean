import Tools.ProofMap

/-! Significant proof steps, authored after reading Adams (pp.1–16), Ballarin (pp.34–50)
and Wiedijk (pp.378–393), TYPES 2003. The selection is explanatory, not a complete census.
Names must resolve and evidence is validated in the loaded environment. No status is authored.
Feature prerequisites do not claim conservative extension. -/
namespace Tools.Semantics.ProofMap

def selection : Selection where
  features := #[
    { id := "values"
      title := "Values, environments and world growth"
      concepts := ["store-typing", "subtyping-algebra"]
      «syntax» := [`Effect4.Program.Ty]
      judgments := [`Effect4.Program.Typed.World, `Effect4.Program.Typed.Fits, `Effect4.Program.Typed.FitsAll]
      rules := [`Effect4.Program.Typed.fits_mono, `Effect4.Program.Typed.fits_subN, `Effect4.Program.Typed.evalTerm_fitsAll, `Effect4.Program.Typed.evalTerm_progress, `Effect4.Program.Typed.evalTerm_progress_env, `Effect4.Program.Typed.termFits, `Effect4.Program.Typed.M3bAssembly.evalTerm_fits]
      requires := []
      boundary := "Unary world-indexed membership. Host world growth and subtyping are distinct relations; these facts do not alone type an execution." },
    { id := "control"
      title := "Sequencing, failure and cleanup"
      concepts := ["residual-program-typing"]
      «syntax» := [`Effect4.Program.Eff.bind, `Effect4.Program.Eff.catchCause, `Effect4.Program.Eff.onExit, `Effect4.Program.Eff.exit]
      judgments := [`Effect4.Program.Typed.TypedProg, `Effect4.Program.Typed.ChildDenotes]
      rules := [`Effect4.Program.Typed.seq_typed, `Effect4.Program.Typed.guardBind_typed, `Effect4.Program.Typed.allGuard_typed, `Effect4.Program.Typed.catchGuard_typed, `Effect4.Program.Typed.bind_arm, `Effect4.Program.Typed.catchCause_arm, `Effect4.Program.Typed.onExit_arm, `Effect4.Program.Typed.exit_arm, `Effect4.Program.Typed.inlineYield_typed]
      requires := ["values"]
      boundary := "Stored bind has two syntax trees; the residual semantic carrier has function continuations. General bind closure is refuted; these constructor-specific rules retain their premises." },
    { id := "stateful"
      title := "References, operations and services"
      concepts := ["store-typing", "context-requirements", "host-session-protocol"]
      «syntax» := [`Effect4.Program.Eff.perform, `Effect4.Program.Eff.service, `Effect4.Program.Eff.provideService]
      judgments := [`Effect4.Program.Typed.StoreImplements]
      rules := [`Effect4.Program.Typed.fits_refTy_inv, `Effect4.Program.Typed.refDeclared_mono, `Effect4.Program.Typed.refRead_nat, `Effect4.Program.Typed.syncRow_typed, `Effect4.Program.Typed.syncPerform_arm, `Effect4.Program.Typed.deferredAwait_arm, `Effect4.Program.Typed.sleep_arm, `Effect4.Program.Typed.external_arm, `Effect4.Program.Typed.perform_arm, `Effect4.Program.Typed.servicesFit_mono, `Effect4.Program.Typed.service_arm, `Effect4.Program.Typed.provideService_arm, `Effect4.Program.Typed.storeStep_typed]
      requires := ["values"]
      boundary := "Request/post typing and concrete handler fulfillment are different obligations. External-operation denotation rules do not establish live-host or backend correctness." },
    { id := "scopes"
      title := "Scopes, fibers and finalization"
      concepts := ["scope-lifetime-finalization", "reactive-scheduling"]
      «syntax» := [`Effect4.Program.Eff.scoped, `Effect4.Program.Eff.withFiber, `Effect4.Program.Eff.acquireRelease]
      judgments := []
      rules := [`Effect4.Program.Typed.scoped_arm, `Effect4.Program.Typed.fork_arm, `Effect4.Program.Typed.forkScoped_arm, `Effect4.Program.Typed.withFiber_arm, `Effect4.Program.Typed.acquireRelease_arm, `Effect4.Program.Typed.typedProg_mono]
      requires := ["control", "stateful"]
      boundary := "World transport must retain scope presence, owner and continuation conditions. These denotation arms are not a global progress or fairness theorem." },
    { id := "layers"
      title := "Layer provision and its current boundary"
      concepts := ["context-requirements", "residual-program-typing"]
      «syntax» := [`Effect4.Program.Eff.provideLayer]
      judgments := [`Effect4.Program.Typed.ProvideLayerArm, `Effect4.Program.Typed.LayerFree]
      rules := [`Effect4.Program.Typed.provideLayerArm_of_layerFree, `Effect4.Program.Typed.M3bAssembly.denoteR_typed_provideLayer]
      requires := ["stateful", "control"]
      boundary := "The layer arm remains a formal goal. The layer-free proof discharges it only by excluding every provideLayer node. The context-image repair discussed in row 176 is separate work; this snapshot's register has not yet recorded the owner's later approval." },
    { id := "denotation"
      title := "M5: constructor rules to typed denotation"
      concepts := ["residual-program-typing"]
      «syntax» := [`Effect4.Program.Eff]
      judgments := [`Effect4.Program.Typed.PointTyped, `Effect4.Program.Typed.DenotesTyped, `Effect4.Program.Typed.LoadsTyped]
      rules := [`Effect4.Program.Typed.succeed_arm, `Effect4.Program.Typed.fail_arm, `Effect4.Program.Typed.failCause_arm, `Effect4.Program.Typed.sync_arm, `Effect4.Program.Typed.suspend_arm, `Effect4.Program.Typed.gen_arm, `Effect4.Program.Typed.matchCause_arm, `Effect4.Program.Typed.uninterruptible_arm, `Effect4.Program.Typed.interruptible_arm, `Effect4.Program.Typed.yieldNow_arm, `Effect4.Program.Typed.awaitFiber_arm, `Effect4.Program.Typed.catchIf_arm, `Effect4.Program.Typed.select_arm, `Effect4.Program.Typed.iterate_arm, `Effect4.Program.Typed.childDenotes_upto, `Effect4.Program.Typed.denotesTyped_of_provideLayer, `Effect4.Program.Typed.denotesTyped_of_layerFree, `Effect4.Program.Typed.loadsTyped_of_denotesTyped, `Effect4.Program.Typed.M3bAssembly.denoteR_typed, `Effect4.Program.Typed.M3bAssembly.typedState_load]
      requires := ["control", "stateful", "scopes", "layers"]
      boundary := "The induction assembles every constructor given ProvideLayerArm. M5 is proved for LayerFree; the general denotation and load goals remain open. Loading additionally requires the no-race-marker equation." },
    { id := "invariant"
      title := "M6–M7: transitions and observable typing"
      concepts := ["reactive-scheduling", "translation-simulation"]
      «syntax» := []
      judgments := [`Effect4.Program.Typed.MachineTyped, `Effect4.Program.Typed.StepPreserves, `Effect4.Program.Typed.DecisionKeeps, `Effect4.Program.Typed.M7Fragment, `Effect4.Program.Typed.ExitHandlesValid]
      rules := [`Effect4.Program.Typed.decisionKeeps_of_ledger, `Effect4.Program.Typed.reachable_of_ledger, `Effect4.Program.Typed.m7_of_capstone, `Effect4.Program.Typed.m7_of_ledger, `Effect4.Program.Typed.M6Ledger.step_loop, `Effect4.Program.Typed.M6Ledger.step_deliver, `Effect4.Program.Typed.M6Ledger.step_finish, `Effect4.Program.Typed.M6Ledger.step_resume, `Effect4.Program.Typed.M6Ledger.step_wake, `Effect4.Program.Typed.M6Ledger.decision_preserves, `Effect4.Program.Typed.M6Ledger.typedState_reachable, `Effect4.Program.Typed.M7.exits_typed, `Effect4.Program.Typed.M7.stores_typed, `Effect4.Program.Typed.M7.never_halts, `Effect4.Program.Typed.M7.exitHandles_valid]
      requires := ["denotation"]
      boundary := "The capstone connectors are proved implications. Their formal input goals remain separately measured. M7 excludes host answers, requires an empty table and closed source; exit handle validity is a separate property." },
    { id := "replay"
      title := "Internal compilation and reference replay"
      concepts := ["translation-simulation"]
      «syntax» := []
      judgments := [`Effect4.Program.Sched.CodeMeans, `Effect4.Machine.ReplayRel]
      rules := [`Effect4.Program.Sched.code_intro_aux, `Effect4.Program.Sched.code_intro, `Effect4.Program.Sched.compile_intro, `Effect4.Program.Sched.load_rel, `Effect4.Program.Sched.stepAgrees, `Effect4.Program.Sched.hooksAgree_of, `Effect4.Program.Sched.replay_rel, `Effect4.Program.Sched.run_eq_ref, `Effect4.Machine.book_replayEval]
      requires := []
      boundary := "CodeMeans and replay relate the compiled frame machine to the residual reference, for a named observation and scope. They do not certify Lean compiler lowering, OCaml execution or the TypeScript runtime." },
    { id := "printed-modules"
      title := "Checked TypeScript module reconstruction"
      concepts := ["exact-codecs", "translation-simulation"]
      «syntax» := []
      judgments := [`Effect4.Codegen.ModuleEmission, `Effect4.Program.moduleReadable]
      rules := [`Effect4.Codegen.ModuleEmission.readModule, `Effect4.Codegen.ModuleEmission.hasTy, `Effect4.Codegen.emitModule_complete, `Effect4.Program.readModule_printModule_readable, `Effect4.Program.readModule_printModule, `Effect4.Program.printModule_readable]
      requires := ["values"]
      boundary := "Successful module emission retains source typing and an exact printer equation. Readback requires lawful tables and readable source; rendered bytes and target execution need separate evidence." }
  ]
  prerequisites := #[
    (`Effect4.Program.Typed.M3bAssembly.denoteR_typed, `Effect4.Program.Typed.M3bAssembly.denoteR_typed_provideLayer),
    (`Effect4.Program.Typed.M3bAssembly.typedState_load, `Effect4.Program.Typed.M3bAssembly.denoteR_typed),
    (`Effect4.Program.Typed.M6Ledger.typedState_reachable, `Effect4.Program.Typed.M3bAssembly.typedState_load),
    (`Effect4.Program.Typed.M6Ledger.typedState_reachable, `Effect4.Program.Typed.M6Ledger.decision_preserves),
    (`Effect4.Program.Typed.M7.exits_typed, `Effect4.Program.Typed.M6Ledger.typedState_reachable),
    (`Effect4.Program.Typed.M7.stores_typed, `Effect4.Program.Typed.M6Ledger.typedState_reachable),
    (`Effect4.Program.Typed.M7.never_halts, `Effect4.Program.Typed.M6Ledger.typedState_reachable)
  ]
  work := #[
    { id := "repair-layer-context"
      title := "Implement and check the layer context-image repair"
      features := ["layers"]
      after := []
      source := "docs/core/decisions.md"
      reason := "Aim to discharge M3bAssembly.denoteR_typed_provideLayer by distinguishing freshly built context images and memo-hit results. The owner approved option (b) after this snapshot's open row 176; integrate that ruling with the repair. Existing conditional assembly is a consumer, not a proof of the repair." },
    { id := "resume-transport"
      title := "Connect restricted resume transport to actual M6 consumers"
      features := ["invariant", "scopes"]
      after := ["Effect4.Program.Typed.typedProg_mono"]
      source := "docs/core/semantics.md"
      reason := "Preserve token, source and owner premises; M6Ledger.step_resume is a consumer to discharge, not a prerequisite already proved. Existing world-transport probes guide the candidate; broadening their relation is not licensed by finite tests." },
    { id := "lowering-local-rule"
      title := "State one lowering relation at the actual number boundary"
      features := ["replay"]
      after := []
      source := "docs/core/lcnf-route.md"
      reason := "Start with a scoped primitive translation law and explicit numeric premises, then connect the actual producer/reader. Current internal replay is not its correctness witness." },
    { id := "target-observation"
      title := "Connect emitted target behavior to a named observation"
      features := ["replay", "printed-modules"]
      after := ["lowering-local-rule"]
      source := "docs/core/system-map.md"
      reason := "Separate source typing, reified internal compilation, serialization, target compilation and runtime behavior. Each connector needs its own proposition or explicitly bounded test receipt." }
  ]
end Tools.Semantics.ProofMap

import Effect4.Laws.Program.Typed.Seq
import Effect4.Laws.Program.Typing.CheckInversion
import Effect4.Laws.Program.Address

/-!
Context typing serves `typed-state-reachable` under decisions rows 117 and 349.
The existing program and frame arrows carry the entry and completion requirement rows.
The reader uses actual runtime coverage and declared service membership.
The provider entry supplies the checked row difference before the body runs.
These source and frame producers are dependencies of the typed-state preservation proof.
They do not establish that every machine satisfies their coverage premises.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-- The ambient reader demand transports declared carriers through the existing host order.
Consumer: ambient current-code world transport. -/
theorem ambientFiberPre_mono (root : ProgramSource) {w w' : World} (ord : w.leHost w')
    (available : Env.Requirement) (op : FiberOp) (cert : FiberCert op)
    (pre : ambientFiberPre root w available op cert) :
    ambientFiberPre root w' available op cert := by
  fun_cases ambientFiberPre root w available op cert with
  | case1 =>
    rcases pre with coarse | ⟨keys, same, covered, declared⟩
    · exact .inl coarse
    · refine .inr ⟨keys, same, covered, fun key member => ?_⟩
      rw [le_serviceTy ord.1]
      exact declared key member
  | case2 | case3 =>
    refine ⟨bodyTyped_mono ord pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, ?_⟩
    constructor
    · intro region same
      obtain ⟨intrinsic, typed, answer, error, covered⟩ := pre.2.2.2.2.1 region same
      exact ⟨intrinsic, regionTyped_mono ord typed, answer, error, covered⟩
    · intro update region flag same
      obtain ⟨intrinsic, typed, answer, error, covered⟩ := pre.2.2.2.2.2 update region flag same
      exact ⟨intrinsic, regionTyped_mono ord typed, answer, error, covered⟩
  | case4 | case5 =>
    exact ⟨pointTyped_mono ord pre.1, pre.2⟩
  | case6 =>
    exact ⟨⟨pointTyped_mono ord pre.1.1, scopeLive_mono ord.1 pre.1.2⟩, pre.2⟩
  | case7 =>
    exact ⟨⟨pointTyped_mono ord pre.1.1, pre.1.2⟩, pre.2⟩
  | case8 =>
    exact ⟨loopPointTyped_mono ord pre.1, pre.2⟩
  | case9 | case10 =>
    intro point member
    obtain ⟨ty, typed, answer, error, covered⟩ := pre point member
    exact ⟨ty, pointTyped_mono ord typed, answer, error, covered⟩
  | case11 =>
    rename_i notGetter notMask notFork notScoped notForkScoped notForkIn notGen notLoop notRace notFirst
    rw [ambientFiberPre.eq_11 root w available op cert notGetter notMask notFork notScoped
      notForkScoped notForkIn notGen notLoop notRace notFirst] at pre
    rw [ambientFiberPre.eq_11 root w' available op cert notGetter notMask notFork notScoped
      notForkScoped notForkIn notGen notLoop notRace notFirst]
    exact fiberPre_mono root ord op cert pre

/-- The same program-arrow world law transports the ambient instance.
Consumer: current, saved and queued ambient entry positions. -/
theorem ambientProg_mono (root : ProgramSource) {w w' : World} {available : Env.Requirement}
    {position : AmbientPosition} {code : RProgram} (ord : w.leHost w')
    (typed : AmbientProg root w available position code) :
    AmbientProg root w' available position code := by
  refine ProgramArrow.mono ?_ ?_ ?_ ord typed
  · intro before after input op cert ordered pre
    exact storePre_mono root ordered op cert pre
  · intro before after input op cert ordered pre
    exact ambientFiberPre_mono root ordered input op cert pre
  · intro before after input position exit ordered payload
    exact ⟨strongExit_mono before after position.type exit ordered payload.1, payload.2⟩

/-- The ambient instance exposes the bound at the actual current entry.
Consumer: interruption and current-code entry in the existing runtime typing relation. -/
theorem ambient_entry {root : ProgramSource} {w : World} {available : Env.Requirement}
    {position : AmbientPosition} {code : RProgram}
    (typed : AmbientProg root w available position code) :
    Row.Subset position.failureRow available := by
  have bound := ProgramArrow.entry typed
  exact bound

/-- The admitted source reader lowers to the existing context operation and uses its typed row.
Consumer: the context arm of the source denotation proof. -/
theorem checked_context_arm (root : ProgramSource) (w : World) (p : Point)
    (env : TyEnv) (keys available : Env.Requirement) (ty : EffTy)
    (node : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.context keys))))
    (checked : Checker.checkAction (root.scopeSig p.path) env p.path (.context keys) = .ok ty)
    (services : w.serviceTy = root.sig.serviceTy) (covered : Row.Subset keys available) :
    AmbientProg root w available (ty, available, available) (denoteAction root.program p) := by
  obtain ⟨declared, rfl⟩ := Checker.inv_action_context _ _ _ _ _ checked
  have action : actionAt root.program p = some WithFiberAction.getContext := by
    unfold actionAt
    rw [node]
  unfold denoteAction
  rw [action]
  refine ambient_getContext_typed root w keys available covered ?_
  intro key member
  obtain ⟨carrier, present⟩ := declared key member
  have present' : w.serviceTy key = some carrier := by
    rw [services]
    change root.signature.serviceTy key = some carrier
    rw [← root.scopeSig_serviceTy p.path]
    exact present
  rw [present']
  rfl

/-- The source reader's full denotation retains actual requirements and a live fuel frontier.
Consumer: the ambient M5 withFiber arm and checked_provideContext_reader. -/
theorem checked_context_denotation (root : ProgramSource) (w : World) (p : Point)
    (env : TyEnv) (keys available : Env.Requirement) (ty : EffTy)
    (node : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber (.context keys))))
    (checked : Checker.check (root.scopeSig p.path) env p.path (.withFiber (.context keys)) = .ok ty)
    (services : w.serviceTy = root.sig.serviceTy) (coverage : Row.Subset ty.requires available) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.withFiber (.context keys)) p) := by
  have actionCheck := Checker.inv_withFiber _ _ _ _ _ checked
  obtain ⟨declared, same⟩ := Checker.inv_action_context _ _ _ _ _ actionCheck
  have required : Row.Subset keys available := by
    rw [same] at coverage
    exact coverage
  have actionHere : Checker.checkAction (root.scopeSig p.path) env p.path (.context keys) = .ok ty := by
    rw [same]
    have loop := (Checker.context_keys_eq_ok (root.scopeSig p.path) p.path keys.elems).mpr declared
    simp only [Checker.checkAction, bind_pure_comp, List.forIn_yield_eq_foldlM]
    rw [loop]
    rfl
  by_cases exhausted : p.fuel = 0
  · rw [denoteR_zero _ _ _ exhausted]
    refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () True.intro ?_ (Row.subset_refl _)
    intro _ _ _ impossible
    exact impossible.elim
  · rw [denoteR_withFiber _ _ _ exhausted]
    exact checked_context_arm root w p env keys available ty node actionHere services required


/-- The actual native getter satisfies the indexed answer protocol in the current context.
Consumer: the typed getter evaluation clause. -/
theorem native_context_answer (root : ProgramSource) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (w : World) (available : Env.Requirement) (cert : FiberCert .getContext)
    (services : ServicesFit w f.context.services)
    (coverage : f.context.services.Satisfies available)
    (pre : ambientFiberPre root w available .getContext cert) :
    (FiberAction.getContext (interpOf root.program table) m f yielding).fiber.frame.current =
      .success (Val.context f.context) ∧
    ambientFiberPost w available .getContext cert (Val.context f.context) :=
  ⟨rfl, ambient_getContext_answers services coverage pre⟩

/-- The getter's saved completion owns the actual returned context and its guaranteed services.
Consumer: the provider's merge, identity branch and captured-context restoration. -/
theorem ambient_captured_context {w : World} {guaranteed : Env.Requirement} {ctx : Ctx}
    (payload : AmbientExit w
      (ambientInput (.capturedContext guaranteed) (.success (Val.context ctx)))
      (.capturedContext guaranteed) (.success (Val.context ctx))) :
    ServicesFit w ctx.services ∧ ctx.services.Satisfies guaranteed := by
  have member : Fits w (Val.context ctx) Ty.context := payload.1.1
  obtain ⟨returned, decoded, services⟩ := fits_context_inv member
  have same : returned = ctx := Option.some.inj (decoded.symm.trans (Val.context?_context _))
  subst returned
  refine ⟨services, (Provision.satisfies_iff_subset_keysRow _ guaranteed).mpr ?_⟩
  have bound := payload.2.1
  change Row.Subset guaranteed (match Val.context? (Val.context ctx) with
    | some ctx => ctx.services.keysRow
    | none => guaranteed) at bound
  rw [Val.context?_context] at bound
  exact bound

/-- The provider's actual entry merges services and supplies the body's checked requirements.
Consumer: the context provider arm, before its body and restored tail are constructed. -/
theorem provider_entry (root : ProgramSource) (w : World) (available required keys : Env.Requirement)
    (previous supplied : Ctx)
    (ambient : Fits w (Val.context previous) (.contextOf (Row.diff required keys)))
    (given : Fits w (Val.context supplied) (.contextOf keys))
    (entryCoverage : previous.services.Satisfies available) :
    let next := Ctx.withServices (previous.services.merge supplied.services)
    Fits w (Val.context next) (.contextOf required) ∧
      AmbientProg root w available (EffTy.pure .unit, next.services.keysRow, available)
        (fiberValR (.setContext next) rfl) := by
  have members := fits_contextOf_provide ambient given
  refine ⟨members, ambient_setContext_typed root w available _ ?_ ?_⟩
  · obtain ⟨next, decoded, serviceMembers, _, _⟩ := fits_contextOf_inv members
    have same : next = Ctx.withServices (previous.services.merge supplied.services) :=
      Option.some.inj (decoded.symm.trans (Val.context?_context _))
    subst next
    exact serviceMembers
  · exact (Provision.satisfies_iff_subset_keysRow _ available).mp
      (Provision.satisfies_merge_left previous.services supplied.services available entryCoverage)

/-- The shared frame hooks retain the original hook contracts and their exact row index.
The scope callback restores its captured row through the existing scope-exit contract. -/
def ambientFrameProtocols (root : ProgramSource) : Contracts.FrameProtocols AmbientPosition where
  asyncFinalizer w before after name := match before, after with
    | .result a success failure, .result b success' failure' =>
      (success, failure) = (success', failure') ∧ (frameProtocols root).asyncFinalizer w a b name
    | _, _ => False
  iterator w before after name := match before, after with
    | .result a success failure, .result b success' failure' =>
      (success, failure) = (success', failure') ∧ (frameProtocols root).iterator w a b name
    | _, _ => False
  loop w before after name cursor := match before, after with
    | .result a success failure, .result b success' failure' =>
      (success, failure) = (success', failure') ∧ (frameProtocols root).loop w a b name cursor
    | _, _ => False
  scopeExit := (frameProtocols root).scopeExit

/-- The existing saved-code relation uses the same complete ambient frame positions.
Consumer: actual parked and resumed code in the runtime typing relation. -/
abbrev AmbientSaved (root : ProgramSource) (w : World) (available : Env.Requirement)
    (final : AmbientPosition) (saved : RSaved) : Prop :=
  Contracts.SavedArrow (AmbientProg root) AmbientExit (ambientFrameProtocols root)
    ambientInput (fun ctx => ctx.services.keysRow) w available final saved

/-- The existing scoped frame returns to services covered by its actual captured context.
Consumer: scoped body delivery in the indexed typed-state preservation path. -/
theorem ambient_scoped_frame (root : ProgramSource) (w : World) (ty : EffTy)
    (bodyRow restoredRow : Env.Requirement) (previous : Ctx) (scope : Nat)
    (next : ExitV → RProgram)
    (shape : ∀ exit, Contracts.scopeExitCallback? (next exit) = some (previous, scope, exit))
    (hook : ∀ later, w.leHost later → (frameProtocols root).scopeExit later previous scope)
    (restored : Row.Subset restoredRow previous.services.keysRow) :
    Contracts.FrameArrow (AmbientProg root) AmbientExit (ambientFrameProtocols root)
      ambientInput (fun ctx => ctx.services.keysRow) w (ty, bodyRow, bodyRow) (ty, restoredRow, restoredRow)
      (.resume (.onExit false) next) :=
  .scopedResume next previous scope shape hook (fun _ _ ex exit => ⟨exit.1, by cases ex <;> exact restored⟩)

/-- The shared output law weakens type columns and guaranteed rows without changing execution.
Consumer: provider bodies and captured-context finalizers in the source denotation path. -/
theorem ambientProg_widen (root : ProgramSource) {w : World} {available : Env.Requirement}
    {before after : EffTy × Env.Requirement × Env.Requirement} {code : RProgram}
    (answer : Ty.subN before.1.answer after.1.answer = true)
    (error : Ty.subN before.1.error after.1.error = true)
    (success : Row.Subset after.2.1 before.2.1) (failure : Row.Subset after.2.2 before.2.2)
    (typed : AmbientProg root w available before code) :
    AmbientProg root w available after code := by
  refine ProgramArrow.outputMap typed ?_ ?_
  · intro world input exit payload
    refine ⟨exitOk_widen answer error payload.1, ?_⟩
    cases exit with
    | success value => exact Row.subset_trans success payload.2
    | failure cause => exact Row.subset_trans failure payload.2
  · intro input bound
    exact Row.subset_trans failure bound

/-- The shared guarded composition carries actual completion rows into its saved callback.
Consumer: context setter and restoring finalizer composition for provideContext. -/
theorem ambient_guardBind (root : ProgramSource) {w : World} {available : Env.Requirement}
    {mid result : AmbientPosition} {kind : GuardKind} {body : RProgram} {next : ExitV → RProgram}
    (typed : AmbientProg root w available mid body)
    (run : ∀ later, w.leHost later → ∀ exit, kind.hasExitArm exit = true →
      AmbientExit later (ambientInput mid exit) mid exit →
      AmbientProg root later (ambientInput mid exit) result (next exit))
    (skip : ∀ later, w.leHost later → ∀ exit,
      AmbientExit later (ambientInput mid exit) mid exit → kind.hasExitArm exit = false →
      AmbientExit later (ambientInput mid exit) result exit)
    (entry : Row.Subset result.failureRow available) :
    AmbientProg root w available result ((guardR kind body).bind next) :=
  ProgramArrow.guardBind typed (fun later ordered exit post => run later ordered exit post.1 post.2)
    skip entry


/-- Counted suspension retains the same entry row through the existing program arrow.
Consumer: suspend, select and invocation source arms in the ambient M5 proof. -/
theorem ambient_suspendR_typed (root : ProgramSource) {w : World} {available : Env.Requirement}
    {position : AmbientPosition} {point : Point} {body : RProgram}
    (entry : Row.Subset position.failureRow available)
    (typed : ∀ later, w.leHost later → AmbientProg root later available position body) :
    AmbientProg root w available position (suspendR point body) :=
  .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () True.intro (fun later ordered _ _ => typed later ordered) entry

/-- Construction retains the actual completed view and the same available service row.
Consumer: source children constructed after suspension or a saved callback in ambient M5. -/
theorem ambient_constructR_typed (root : ProgramSource) {w : World} {available : Env.Requirement}
    {position : AmbientPosition} {next : List (FiberId × ExitV) → RProgram}
    (entry : Row.Subset position.failureRow available)
    (typed : ∀ later, w.leHost later → ∀ completed,
      (∀ id ∈ completed, ∃ ty, later.Γ id.1 = some ty ∧ ExitOk later ty id.2) →
      AmbientProg root later available position (next completed)) :
    AmbientProg root w available position (constructR next) :=
  .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () True.intro (fun later ordered completed post =>
      typed later ordered completed post) entry

/-- The existing finalizer boundary retains its cleanup's actual common service guarantee.
Consumer: source onExit and the provider's actual restoring setter adapter. -/
theorem ambient_finalizer_typed (root : ProgramSource) {w : World}
    {available guaranteed : Env.Requirement} {ty cleanupType : EffTy} {cleanup : RProgram}
    (bodyExit : ExitV) (payload : ExitOk w ty bodyExit)
    (errorBound : Ty.subN cleanupType.error ty.error = true)
    (typed : AmbientProg root w available (cleanupType, guaranteed, guaranteed) cleanup) :
    AmbientProg root w available (ty, guaranteed, guaranteed) (finalizerR bodyExit cleanup) := by
  have entry := ambient_entry typed
  have work : ∀ originalExit, ExitOk w ty originalExit → AmbientProg root w available
      ((⟨cleanupType.answer, ty.error, cleanupType.requires⟩ : EffTy), guaranteed, guaranteed)
      (match originalExit with
      | .success _ => cleanup
      | .failure _ => (guardR .onFailure cleanup).bind fun
          | .success value => .pure (.success value)
          | .failure cause => .pure (Exit.restoreAfterFinalizer originalExit (.failure cause))) := by
    intro originalExit originalPayload
    cases originalExit with
    | success value =>
      exact ambientProg_widen root (before := (cleanupType, guaranteed, guaranteed))
        (Ty.subN_refl _) errorBound (Row.subset_refl _) (Row.subset_refl _) typed
    | failure cause =>
      refine ambient_guardBind root typed (fun later ordered exit arm clean => ?_)
        (fun later ordered exit clean absent => ?_) entry
      · cases exit with
        | success value => exact Bool.noConfusion arm
        | failure cleanupCause =>
          refine .pure ⟨?_, Row.subset_refl guaranteed⟩ (Row.subset_refl guaranteed)
          exact exitOk_restore (strongExit_mono _ _ _ _ ordered originalPayload)
            (exitOk_failure_of_errorN errorBound clean.1)
      · cases exit with
        | success value =>
          exact ⟨exitOk_success_of_answerN (Ty.subN_refl _) clean.1, Row.subset_refl _⟩
        | failure cleanupCause => exact Bool.noConfusion absent
  unfold finalizerR
  refine ambient_guardBind root (work bodyExit payload) (fun later ordered exit arm clean => ?_)
    (fun later ordered exit clean absent => ?_) entry
  · cases exit with
    | success value =>
      refine .finishFinalizer ⟨strongExit_mono _ _ _ _ ordered payload, ?_⟩ (Row.subset_refl _)
      cases bodyExit <;> exact Row.subset_refl _
    | failure cause => exact Bool.noConfusion arm
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Ty.subN_refl _) clean.1, Row.subset_refl guaranteed⟩

/-- The real restoring finalizer returns the saved body exit with its common service guarantee.
Consumer: provideContext's compiled restoring region and the source denotation adapter. -/
theorem ambient_restore_finalizer (root : ProgramSource) {w : World} (available guaranteed : Env.Requirement)
    (previous : Ctx) (services : ServicesFit w previous.services)
    (entry : Row.Subset guaranteed available) (restored : Row.Subset guaranteed previous.services.keysRow)
    (ty : EffTy) (bodyExit : ExitV) (payload : ExitOk w ty bodyExit) :
    AmbientProg root w available (ty, guaranteed, guaranteed)
      (finalizerR bodyExit (fiberValR (.setContext previous) rfl)) := by
  have cleanup := ambient_setContext_guarantees root w available guaranteed previous services entry restored
  exact ambient_finalizer_typed root bodyExit payload (Bounds.subN_never _)
    (ambientProg_widen root (before := (EffTy.pure .unit, previous.services.keysRow, guaranteed))
      (after := (EffTy.pure .unit, guaranteed, guaranteed))
      (Ty.subN_refl _) (Ty.subN_refl _) restored (Row.subset_refl _) cleanup)

/-- The existing onExit region preserves body and cleanup membership and their actual common row.
Consumer: the source onExit arm in the ambient M5 induction. -/
theorem ambient_onExit_typed (root : ProgramSource) {w : World}
    {available guaranteed : Env.Requirement} {bodyType cleanupType resultType : EffTy}
    {body : RProgram} {cleanup : ExitV → RProgram} {flag : Bool}
    (answerBound : Ty.subN bodyType.answer resultType.answer = true)
    (bodyErrorBound : Ty.subN bodyType.error resultType.error = true)
    (cleanupErrorBound : Ty.subN cleanupType.error resultType.error = true)
    (typed : AmbientProg root w available (bodyType, guaranteed, guaranteed) body)
    (finalizer : ∀ later, w.leHost later → ∀ exit, ExitOk later bodyType exit →
      AmbientProg root later guaranteed (cleanupType, guaranteed, guaranteed) (cleanup exit)) :
    AmbientProg root w available (resultType, guaranteed, guaranteed) (onExitR body cleanup flag) := by
  unfold onExitR
  refine ambient_guardBind root typed (fun later ordered exit _ payload => ?_)
    (fun _ _ exit _ absent => by cases exit <;> exact Bool.noConfusion absent)
    (show Row.Subset guaranteed available from ambient_entry typed)
  have selected : ambientInput (bodyType, guaranteed, guaranteed) exit = guaranteed := by
    cases exit <;> rfl
  rw [selected]
  exact ambient_finalizer_typed root exit (exitOk_widen answerBound bodyErrorBound payload.1)
    cleanupErrorBound (finalizer later ordered exit payload.1)

/-- The existing onExit region runs the actual captured-context restoring finalizer.
Consumer: provideContext's bodyThen region and the source admission-to-execution adapter. -/
theorem ambient_onExit_restore (root : ProgramSource) {w : World}
    {available guaranteed : Env.Requirement} {ty : EffTy} {body : RProgram}
    (previous : Ctx) (services : ServicesFit w previous.services)
    (restored : Row.Subset guaranteed previous.services.keysRow)
    (typed : AmbientProg root w available (ty, guaranteed, guaranteed) body) :
    AmbientProg root w available (ty, guaranteed, guaranteed)
      (onExitR body fun _ => fiberValR (.setContext previous) rfl) := by
  unfold onExitR
  refine ambient_guardBind root typed (fun later ordered exit _ payload => ?_)
    (fun _ _ exit _ absent => by cases exit <;> exact Bool.noConfusion absent) (ambient_entry typed)
  have selected : ambientInput (ty, guaranteed, guaranteed) exit = guaranteed := by
    cases exit <;> rfl
  rw [selected]
  have members : ServicesFit later previous.services :=
    servicesFit_map ordered.1.2.1 ordered.1.2.2.1 ordered.1.2.2.2.1 ordered.2 ordered.1.1.2
      (serviceTy_of_le ordered.1) services
  exact ambient_restore_finalizer root guaranteed guaranteed previous members
    (Row.subset_refl _) restored ty exit payload.1

/-- A typed store leaf preserves the available context row.
The existing unit store certificate and answer proof remain unchanged.
Consumer: the actual synchronous source-operation arm of M5. -/
theorem ambient_storeR_of_typed (root : ProgramSource) {w : World} {ty : EffTy}
    (available : Env.Requirement) {op : SyncOp} (typed : TypedProg root w ty (storeR op)) :
    AmbientProg root w available (ty, available, available) (storeR op) := by
  obtain ⟨cert, pre, next⟩ := TypedProg.store_inv typed
  refine .store cert pre ?_ (Row.subset_refl _)
  intro later ordered answer post
  exact .pure ⟨TypedProg.pure_inv (next later ordered answer post), Row.subset_refl _⟩ (Row.subset_refl _)

/-- The existing mask reader retains the ambient entry through its restored slot.
Consumer: the provider's protected-entry program arrow. -/
theorem ambient_captureMask_typed (root : ProgramSource) (w : World)
    (available : Env.Requirement) :
    AmbientProg root w available (EffTy.pure Ty.maskRestore, available, available)
      (fiberValR .getInterruptible rfl) := by
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () True.intro ?_ (Row.subset_refl _)
  intro later _ value post
  obtain ⟨flag, rfl⟩ := post
  exact .pure ⟨strongExit_success later _ _ (fits_savedMask later flag), Row.subset_refl _⟩
    (Row.subset_refl _)

/-- The actual provider mask checks the installed map's body requirements.
Consumer: the typed source provider arm on the typed-state-reachable path. -/
theorem ambient_updateContext_provide (root : ProgramSource) {w : World}
    (available guaranteed required keys : Env.Requirement) (supplied : Ctx)
    (given : Fits w (Val.context supplied) (.contextOf keys))
    (needed : Row.Subset (Row.diff required keys) available)
    (entry : Row.Subset guaranteed available) (ty : EffTy) (body : Region)
    (typedBody : RegionTyped root w body ⟨ty.answer, ty.error, required⟩)
    (update : Env.ContextUpdate)
    (applies : ∀ previous, update.apply previous = previous.merge supplied.services) :
    AmbientProg root w available (ty, guaranteed, guaranteed)
      (updateContextR update body) := by
  obtain ⟨provided, decoded, suppliedMembers, suppliedKeys, _⟩ := fits_contextOf_inv given
  have same : provided = supplied := Option.some.inj
    (decoded.symm.trans (Val.context?_context _))
  subst provided
  unfold updateContextR
  refine ambient_guardBind root (ambient_captureMask_typed root w available)
    (fun later ordered exit arm payload => ?_) (fun _ _ exit payload absent => ?_) entry
  · cases exit with
    | failure cause => exact Bool.noConfusion arm
    | success value =>
      obtain ⟨flag, rfl⟩ := fits_maskRestore_inv payload.1.1
      simp only [seqR, Val.savedMask?_savedMask]
      let intrinsic : EffTy := ⟨ty.answer, ty.error, required⟩
      let cut : EffTy := ⟨ty.answer, ty.error, available⟩
      have region : RegionTyped root later body intrinsic := regionTyped_mono ordered typedBody
      have updateTyped : ContextUpdateTyped later update := by
        intro after grew previous members
        rw [applies]
        have future := leHost_trans _ _ _ ordered grew
        exact servicesFit_merge members (servicesFit_map future.1.2.1 future.1.2.2.1
          future.1.2.2.2.1 future.2 future.1.1.2 (serviceTy_of_le future.1) suppliedMembers)
      refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) cut ?_ ?_ entry
      · refine ⟨.contextEntry _ body flag intrinsic cut region (Ty.subN_refl _) (Ty.subN_refl _)
          updateTyped, Row.subset_refl _, ?_, ?_, ?_, ?_⟩
        · intro point ctx impossible
          cases impossible
        · intro point previous impossible
          cases impossible
        · intro actual impossible
          cases impossible
        · intro actual region' flag' shape
          cases shape
          refine ⟨intrinsic, region, Ty.subN_refl _, Ty.subN_refl _, ?_⟩
          intro previous covered
          rw [applies]
          have fromBefore := Provision.satisfies_merge_left previous supplied.services
            (Row.diff required keys) (previous.satisfies_weaken covered needed)
          have fromGiven := Provision.satisfies_merge_right previous supplied.services keys suppliedKeys
          refine ⟨?_, Provision.satisfies_merge_left previous supplied.services available covered⟩
          intro key member
          by_cases suppliedKey : key ∈ keys
          · exact fromGiven key suppliedKey
          · exact fromBefore key ((Row.mem_diff key required keys).mpr ⟨member, suppliedKey⟩)
      · intro after _ delivered post
        refine .pure ⟨post, ?_⟩ entry
        cases delivered <;> exact entry
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause => exact ⟨exitOk_failure_of_errorN (Bounds.subN_never _) payload.1, entry⟩

/-- The checked provider source arm uses its actual child and immediate-exit premises.
Consumer: ambient M5 source denotation and checked_provideContext_reader. -/
theorem checked_provideContext_arm (root : ProgramSource) (w : World) (p : Point)
    (env : TyEnv) (context : Term) (body : NativeEff) (available : Env.Requirement)
    (ty : EffTy) (supplied : Ctx)
    (checked : Checker.check (root.scopeSig p.path) env p.path
      (.provideContext context body) = .ok ty)
    (values : EnvTyped w env p.env) (evaluated : evalTerm p.env context = some (Val.context supplied))
    (coverage : Row.Subset ty.requires available) (budget : p.fuel ≠ 0)
    (immediate : ∀ bodyTy, Checker.check (root.scopeSig p.path) env (p.path ++ [0]) body = .ok bodyTy →
      ∀ exit, inlineYield body (p.child 0) = some exit → ExitOk w bodyTy exit)
    (child : ∀ bodyTy, Checker.check (root.scopeSig p.path) env (p.path ++ [0]) body = .ok bodyTy →
      PointTyped root w (p.child 0) bodyTy) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.provideContext context body) p) := by
  obtain ⟨contextTy, keys, bodyTy, termCheck, normalized, bodyCheck, rfl⟩ :=
    Checker.inv_provideContext _ _ _ _ _ _ checked
  have constants : (root.scopeSig p.path).constAtom = nativeConstAtom :=
    (root.scopeSig_extends p.path).constAtom.trans rfl
  have atoms : (root.scopeSig p.path).atomOf = nativeAtomTy :=
    (root.scopeSig_extends p.path).atomOf.trans rfl
  have members := evalTerm_fits (sig := root.scopeSig p.path) atoms constants values termCheck evaluated
  have given : Fits w (Val.context supplied) (.contextOf keys) := by
    rw [← normalized]
    exact (fits_normalize _ _ _).mpr members
  rw [denoteR_provideContext _ _ _ budget, evaluated]
  simp only [Option.bind_some, Val.context?_context]
  cases head : inlineYield body (p.child 0) with
  | some exit =>
    refine .pure ⟨?_, ?_⟩ (Row.subset_refl available)
    · exact exitOk_widen (Ty.subN_refl _) (Ty.subN_refl _) (immediate bodyTy bodyCheck exit head)
    · cases exit <;> exact Row.subset_refl available
  | none =>
    exact ambient_updateContext_provide root available available bodyTy.requires keys supplied
      given coverage (Row.subset_refl _)
      ⟨bodyTy.answer, bodyTy.error, Row.diff bodyTy.requires keys⟩
      (.program (p.child 0)) (child bodyTy bodyCheck)
      (.provide supplied.services) (fun _ => rfl)


/-- An actual checked provider and context-reader body use the installed merged row.
Consumer: the new source constructor's denotation clause on the typed-state-reachable path. -/
theorem checked_provideContext_reader (root : ProgramSource) (w : World) (p : Point)
    (env : TyEnv) (context : Term) (required available : Env.Requirement) (ty : EffTy) (supplied : Ctx)
    (_node : Node.at_ (.eff root.program) p.path =
      some (.eff (.provideContext context (.withFiber (.context required)))))
    (checked : Checker.check (root.scopeSig p.path) env p.path
      (.provideContext context (.withFiber (.context required))) = .ok ty)
    (values : EnvTyped w env p.env) (evaluated : evalTerm p.env context = some (Val.context supplied))
    (_services : w.serviceTy = root.sig.serviceTy) (coverage : Row.Subset ty.requires available)
    (budget : p.fuel ≠ 0)
    (admitted : ∀ bodyTy, Checker.check (root.scopeSig p.path) env (p.path ++ [0])
      (.withFiber (.context required)) = .ok bodyTy → PointTyped root w (p.child 0) bodyTy) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.provideContext context (.withFiber (.context required))) p) := by
  refine checked_provideContext_arm root w p env context (.withFiber (.context required))
    available ty supplied checked values evaluated coverage budget ?_ ?_
  · intro bodyTy bodyCheck exit head
    have noInline : inlineYield (.withFiber (.context required)) (p.child 0) = none := by
      unfold inlineYield
      split <;> rfl
    rw [noInline] at head
    cases head
  · exact admitted


/-- The checked service provider consumes the common restoring provider protocol.
Consumer: ambient M5 source denotation and checked_provideService_reader. -/
theorem checked_provideService_arm (root : ProgramSource) (w : World) (p : Point)
    (env : TyEnv) (key : ServiceKey) (value : Term) (body : NativeEff)
    (available : Env.Requirement) (ty : EffTy) (provided : Val)
    (checked : Checker.check (root.scopeSig p.path) env p.path
      (.provideService key value body) = .ok ty)
    (values : EnvTyped w env p.env) (evaluated : evalTerm p.env value = some provided)
    (services : w.serviceTy = root.sig.serviceTy)
    (carriers : ∀ carrier, root.sig.serviceTy key = some carrier → flatCarrier carrier = true)
    (coverage : Row.Subset ty.requires available) (budget : p.fuel ≠ 0)
    (child : ∀ bodyTy, Checker.check (root.scopeSig p.path) env (p.path ++ [0]) body = .ok bodyTy →
      PointTyped root w (p.child 0) bodyTy) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.provideService key value body) p) := by
  obtain ⟨carrier, valueTy, bodyTy, declared, termCheck, orderedValue, bodyCheck, rfl⟩ :=
    Checker.inv_provideService _ _ _ _ _ _ _ checked
  have declaredRoot : root.sig.serviceTy key = some carrier := by
    rw [root.scopeSig_serviceTy] at declared
    exact declared
  have declaredWorld : w.serviceTy key = some carrier := services ▸ declaredRoot
  have constants : (root.scopeSig p.path).constAtom = nativeConstAtom :=
    (root.scopeSig_extends p.path).constAtom.trans rfl
  have atoms : (root.scopeSig p.path).atomOf = nativeAtomTy :=
    (root.scopeSig_extends p.path).atomOf.trans rfl
  have valueFit := evalTerm_fits (sig := root.scopeSig p.path) atoms constants values termCheck evaluated
  have carrierFit : Fits w provided carrier := fits_subN w orderedValue provided valueFit
  let supplied : Ctx := Ctx.withServices ((Env.Context.empty : Env.Ctx).addV key provided)
  have given : Fits w (Val.context supplied) (.contextOf (Env.Requirement.single key)) := by
    refine fits_contextOf_intro (servicesFit_addV (servicesFit_empty w) declaredWorld
      (fits_flatFits (carriers carrier declaredRoot) carrierFit) (fits_live w _ _ carrierFit))
      (Provision.satisfies_single_addV key provided) ?_
    intro other member
    have same : other = key := (Row.mem_singleton key other).mp member
    subst other
    rw [declaredWorld]
    rfl
  rw [denoteR_provideService _ _ _ _ budget, evaluated]
  dsimp only
  exact ambient_updateContext_provide root available available bodyTy.requires
    (Env.Requirement.single key) supplied given coverage (Row.subset_refl _)
    ⟨bodyTy.answer, bodyTy.error, Row.diff bodyTy.requires (Env.Requirement.single key)⟩
    (.program (p.child 0))
    (child bodyTy bodyCheck) (.provideService key provided) (fun _ => rfl)

/-- The real service provider installs the checked carrier before its context reader.
Consumer: the closed provider reader and ambient M5 source denotation. -/
theorem checked_provideService_reader (root : ProgramSource) (w : World) (p : Point)
    (env : TyEnv) (key : ServiceKey) (value : Term) (required available : Env.Requirement)
    (ty : EffTy) (provided : Val)
    (_node : Node.at_ (.eff root.program) p.path =
      some (.eff (.provideService key value (.withFiber (.context required)))))
    (checked : Checker.check (root.scopeSig p.path) env p.path
      (.provideService key value (.withFiber (.context required))) = .ok ty)
    (values : EnvTyped w env p.env) (evaluated : evalTerm p.env value = some provided)
    (services : w.serviceTy = root.sig.serviceTy)
    (carriers : ∀ carrier, root.sig.serviceTy key = some carrier → flatCarrier carrier = true)
    (coverage : Row.Subset ty.requires available) (budget : p.fuel ≠ 0)
    (admitted : ∀ bodyTy, Checker.check (root.scopeSig p.path) env (p.path ++ [0])
      (.withFiber (.context required)) = .ok bodyTy → PointTyped root w (p.child 0) bodyTy) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.provideService key value (.withFiber (.context required))) p) := by
  exact checked_provideService_arm root w p env key value (.withFiber (.context required))
    available ty provided checked values evaluated services carriers coverage budget admitted


end Effect4.Program.Typed

import Effect4.Laws.Program.Typed.Seq
import Effect4.Laws.Program.Typed.StackCertificates
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
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro region same
      obtain ⟨intrinsic, typed, answer, error, covered, arguments⟩ := pre.2.2.2.2.1 region same
      exact ⟨intrinsic, regionTyped_mono ord typed, answer, error, covered,
        regionStackTyped_mono ord arguments⟩
    · intro update region flag same
      obtain ⟨intrinsic, typed, answer, error, covered⟩ := pre.2.2.2.2.2.1 update region flag same
      refine ⟨intrinsic, regionTyped_mono ord typed, answer, error, ?_⟩
      intro previous present
      have installed := covered previous present
      exact ⟨installed.1, installed.2.1, regionStackTyped_mono ord installed.2.2⟩
    · intro point role
      exact ambientStackTyped_mono ord (pre.2.2.2.2.2.2.1 point role)
    · intro point memo scope same
      exact ambientStackTyped_mono ord (pre.2.2.2.2.2.2.2 point memo scope same)
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

/-- The same captured callback transports through the existing host order.
Consumer: ambient foreign registration and captured cleanup activation. -/
theorem ambientCapturePolicy_mono {root : ProgramSource} {w w' : World}
    (ordered : w.leHost w') {capture : Capture} (policy : AmbientCapturePolicy root w capture) :
    AmbientCapturePolicy root w' capture :=
  fun later after completed typed exit member =>
    policy later (leHost_trans _ _ _ ordered after) completed typed exit member

/-- Store admission preserves its captured callback through the same world law.
Consumer: ProgramArrow.mono's ambient instance. -/
theorem ambientStorePre_mono (root : ProgramSource) {w w' : World} (ordered : w.leHost w')
    (available : Env.Requirement) (op : SyncOp) (cert : StoreCert op)
    (pre : ambientStorePre root w available op cert) :
    ambientStorePre root w' available op cert :=
  ⟨storePre_mono root ordered op cert pre.1,
    fun scope capture identity => ambientCapturePolicy_mono ordered (pre.2 scope capture identity)⟩

/-- The same program-arrow world law transports the ambient instance.
Consumer: current, saved and queued ambient entry positions. -/
theorem ambientProg_mono (root : ProgramSource) {w w' : World} {available : Env.Requirement}
    {position : AmbientPosition} {code : RProgram} (ord : w.leHost w')
    (typed : AmbientProg root w available position code) :
    AmbientProg root w' available position code := by
  refine ProgramArrow.mono ?_ ?_ ?_ ord typed
  · intro before after input op cert ordered pre
    exact ambientStorePre_mono root ordered input op cert pre
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

/-! ## The hook protocols over the row-indexed judgment

A named hook frame keeps one success row and one failure row for its whole protocol. The walk
pops it at the success row (`ambientInput` of a success), so a resumed body or a loop's finishing
code is typed there, and every frame the walk re-pushes keeps both rows. The unit protocols
(`IteratorStep`, `LoopStep`, `Typed/Residual.lean`) are these with the rows erased.
Concept: residual-program-typing, R4 and R9. Consumers: the walk's hook laws and the generator,
loop and parallel-close clauses of typed-state preservation. -/

/-- A saved ambient iterator frame's state: world, success and failure rows, input and final
types, the hook name. -/
abbrev AmbientIterState := World × Env.Requirement × Env.Requirement × EffTy × EffTy × EffName

/-- A saved ambient loop frame's state: as an iterator's, with the cursor. -/
abbrev AmbientLoopState :=
  World × Env.Requirement × Env.Requirement × EffTy × EffTy × EffName × Val

/-- One ambient iterator step: `IteratorStep` with each resumed body typed at the frame's success
row and the same two rows. -/
def AmbientIteratorStep (root : ProgramSource) (I : AmbientIterState → Prop) :
    AmbientIterState → Prop
  | (w, success, failure, tin, tout, name) =>
    tin.error = tout.error ∧
      (tout.requires = Env.Requirement.empty → tin.requires = Env.Requirement.empty) ∧
      ∀ w', w.leHost w' → ∀ completed, ViewTyped w' completed → ∀ v, Fits w' v tin.answer →
        match ((interpRAt root.program completed).iterNext name v).2 with
        | .done result => ExitOk w' tout (.success result)
        | .halt cause => ExitOk w' tout (.failure cause)
        | .resume code name' => ∃ tin', AmbientProg root w' success (tin', success, failure) code ∧
            I (w', success, failure, tin', tout, name')

/-- One ambient loop step: `LoopStep` with each body and finishing code typed at the frame's
success row. -/
def AmbientLoopStep (root : ProgramSource) (I : AmbientLoopState → Prop) :
    AmbientLoopState → Prop
  | (w, success, failure, tin, tout, name, cursor) =>
    tin.error = tout.error ∧
      (tout.requires = Env.Requirement.empty → tin.requires = Env.Requirement.empty) ∧
      ∀ w', w.leHost w' → ∀ completed, ViewTyped w' completed → ∀ v, Fits w' v tin.answer →
        match (interpRAt root.program completed).loopResume name cursor v with
        | .continue cursor' body => ∃ tin', AmbientProg root w' success (tin', success, failure) body ∧
            I (w', success, failure, tin', tout, name, cursor')
        | .finish code => AmbientProg root w' success (tout, success, failure) code

section AmbientProtocols
open Contracts (Greatest StepMono)
variable {root : ProgramSource}

theorem ambientIteratorStep_mono : StepMono (AmbientIteratorStep root) := by
  rintro I J sub ⟨w, success, failure, tin, tout, name⟩ ⟨errors, rows, next⟩
  refine ⟨errors, rows, fun w' o completed view v hv => ?_⟩
  have step := next w' o completed view v hv
  revert step
  cases ((interpRAt root.program completed).iterNext name v).2 with
  | done result => exact id
  | halt cause => exact id
  | resume code name' =>
    intro step
    obtain ⟨tin', typed, tail⟩ := step
    exact ⟨tin', typed, sub _ tail⟩

theorem ambientLoopStep_mono : StepMono (AmbientLoopStep root) := by
  rintro I J sub ⟨w, success, failure, tin, tout, name, cursor⟩ ⟨errors, rows, next⟩
  refine ⟨errors, rows, fun w' o completed view v hv => ?_⟩
  have step := next w' o completed view v hv
  revert step
  cases (interpRAt root.program completed).loopResume name cursor v with
  | «continue» cursor' body =>
    intro step
    obtain ⟨tin', typed, tail⟩ := step
    exact ⟨tin', typed, sub _ tail⟩
  | finish code => exact id

/-- An ambient iterator frame's protocol: the greatest invariant of its step. -/
abbrev AmbientIteratorProtocol (root : ProgramSource) (w : World) (success failure : Env.Requirement)
    (tin tout : EffTy) (name : EffName) : Prop :=
  Greatest (AmbientIteratorStep root) (w, success, failure, tin, tout, name)

/-- An ambient loop frame's protocol: the greatest invariant of its step. -/
abbrev AmbientLoopProtocol (root : ProgramSource) (w : World) (success failure : Env.Requirement)
    (tin tout : EffTy) (name : EffName) (cursor : Val) : Prop :=
  Greatest (AmbientLoopStep root) (w, success, failure, tin, tout, name, cursor)

theorem AmbientIteratorProtocol.unfold {w : World} {success failure : Env.Requirement}
    {tin tout : EffTy} {name : EffName}
    (h : AmbientIteratorProtocol root w success failure tin tout name) :
    AmbientIteratorStep root (Greatest (AmbientIteratorStep root))
      (w, success, failure, tin, tout, name) :=
  Greatest.unfold ambientIteratorStep_mono h

theorem AmbientIteratorProtocol.fold {w : World} {success failure : Env.Requirement}
    {tin tout : EffTy} {name : EffName}
    (h : AmbientIteratorStep root (Greatest (AmbientIteratorStep root))
      (w, success, failure, tin, tout, name)) :
    AmbientIteratorProtocol root w success failure tin tout name :=
  Greatest.fold ambientIteratorStep_mono h

theorem AmbientLoopProtocol.unfold {w : World} {success failure : Env.Requirement}
    {tin tout : EffTy} {name : EffName} {cursor : Val}
    (h : AmbientLoopProtocol root w success failure tin tout name cursor) :
    AmbientLoopStep root (Greatest (AmbientLoopStep root))
      (w, success, failure, tin, tout, name, cursor) :=
  Greatest.unfold ambientLoopStep_mono h

theorem AmbientLoopProtocol.fold {w : World} {success failure : Env.Requirement}
    {tin tout : EffTy} {name : EffName} {cursor : Val}
    (h : AmbientLoopStep root (Greatest (AmbientLoopStep root))
      (w, success, failure, tin, tout, name, cursor)) :
    AmbientLoopProtocol root w success failure tin tout name cursor :=
  Greatest.fold ambientLoopStep_mono h

/-- An ambient iterator protocol holds at every later world. -/
theorem ambientIteratorProtocol_mono {w w' : World} (ord : w.leHost w')
    {success failure : Env.Requirement} {tin tout : EffTy} {name : EffName}
    (h : AmbientIteratorProtocol root w success failure tin tout name) :
    AmbientIteratorProtocol root w' success failure tin tout name := by
  obtain ⟨errors, rows, next⟩ := h.unfold
  exact AmbientIteratorProtocol.fold ⟨errors, rows, fun w'' o => next w'' (leHost_trans _ _ _ ord o)⟩

/-- An ambient loop protocol holds at every later world. -/
theorem ambientLoopProtocol_mono {w w' : World} (ord : w.leHost w')
    {success failure : Env.Requirement} {tin tout : EffTy} {name : EffName} {cursor : Val}
    (h : AmbientLoopProtocol root w success failure tin tout name cursor) :
    AmbientLoopProtocol root w' success failure tin tout name cursor := by
  obtain ⟨errors, rows, next⟩ := h.unfold
  exact AmbientLoopProtocol.fold ⟨errors, rows, fun w'' o => next w'' (leHost_trans _ _ _ ord o)⟩

end AmbientProtocols

/-- The async finalizer's ambient clause: the cancellation runs at the frame's failure row, the
row its pop delivers a failure at. -/
def AmbientAsyncFinalizer (root : ProgramSource) (w : World) (success failure : Env.Requirement)
    (tin tout : EffTy) (name : EffName) : Prop :=
  tin = tout ∧ ∀ w', w.leHost w' →
    ∀ cause, ExitOk w' tin (.failure cause) → cause.hasInterrupts = true →
      AmbientProg root w' failure (tout, success, failure)
        ((interpR root.program).cancelThenFail name cause)

/-- The shared frame hooks over row-indexed positions. A hook frame keeps its two rows, and its
protocol types resumed code at them. The scope callback restores its captured row through the
existing scope-exit contract. -/
def ambientFrameProtocols (root : ProgramSource) : Contracts.FrameProtocols AmbientPosition where
  asyncFinalizer w before after name := match before, after with
    | .result a success failure, .result b success' failure' =>
      (success, failure) = (success', failure') ∧ AmbientAsyncFinalizer root w success failure a b name
    | _, _ => False
  iterator w before after name := match before, after with
    | .result a success failure, .result b success' failure' =>
      (success, failure) = (success', failure') ∧
        AmbientIteratorProtocol root w success failure a b name
    | _, _ => False
  loop w before after name cursor := match before, after with
    | .result a success failure, .result b success' failure' =>
      (success, failure) = (success', failure') ∧
        AmbientLoopProtocol root w success failure a b name cursor
    | _, _ => False
  scopeExit := (frameProtocols root).scopeExit

/-- The existing scoped frame returns to services covered by its actual captured context.
Consumer: scoped body delivery in the indexed typed-state preservation path. -/
theorem ambient_scoped_frame (root : ProgramSource) (w : World) (ty : EffTy)
    (bodyRow restoredRow : Env.Requirement) (previous : Ctx) (scope : Nat)
    (next : ExitV → RProgram)
    (shape : ∀ exit, Contracts.scopeExitCallback? (next exit) = some (previous, scope, exit))
    (hook : ∀ later, w.leHost later → (frameProtocols root).scopeExit later previous scope)
    (restored : Row.Subset restoredRow previous.services.keysRow) :
    Contracts.FrameArrow (AmbientProg root) AmbientExit (ambientFrameProtocols root)
      ambientInput (fun ctx => ctx.services.keysRow)
    (fun _ position exit => ambientInput position exit) w (ty, bodyRow, bodyRow) (ty, restoredRow, restoredRow)
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

/-- Distinct cleanup guarantees compose through the existing finalizer boundary.
Concept: residual-program-typing, R4 and R9; helper of the closed M5 source claim.
Consumer: captured release restoration; entry interruption retains the failure guarantee.
This law establishes no machine preservation or external observation. -/
theorem ambient_finalizer_guarantees (root : ProgramSource) {w : World}
    {available success failure : Env.Requirement} {ty cleanupType : EffTy} {cleanup : RProgram}
    (bodyExit : ExitV) (payload : ExitOk w ty bodyExit)
    (errorBound : Ty.subN cleanupType.error ty.error = true)
    (kept : Row.Subset failure success)
    (typed : AmbientProg root w available (cleanupType, success, failure) cleanup) :
    AmbientProg root w available (ty, success, failure) (finalizerR bodyExit cleanup) := by
  have entry := ambient_entry typed
  have work : ∀ originalExit, ExitOk w ty originalExit → AmbientProg root w available
      ((⟨cleanupType.answer, ty.error, cleanupType.requires⟩ : EffTy), success, failure)
      (match originalExit with
      | .success _ => cleanup
      | .failure _ => (guardR .onFailure cleanup).bind fun
          | .success value => .pure (.success value)
          | .failure cause => .pure (Exit.restoreAfterFinalizer originalExit (.failure cause))) := by
    intro originalExit originalPayload
    cases originalExit with
    | success value =>
      exact ambientProg_widen root (before := (cleanupType, success, failure))
        (Ty.subN_refl _) errorBound (Row.subset_refl _) (Row.subset_refl _) typed
    | failure cause =>
      refine ambient_guardBind root typed (fun later ordered exit arm clean => ?_)
        (fun later ordered exit clean absent => ?_) entry
      · cases exit with
        | success value => exact Bool.noConfusion arm
        | failure cleanupCause =>
          refine .pure ⟨?_, Row.subset_refl failure⟩ (Row.subset_refl failure)
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
      refine .finishFinalizer ⟨strongExit_mono _ _ _ _ ordered payload, ?_⟩ kept
      cases bodyExit with
      | success _ => exact Row.subset_refl _
      | failure _ => exact kept
    | failure cause => exact Bool.noConfusion arm
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Ty.subN_refl _) clean.1, Row.subset_refl failure⟩

/-- The common-row finalizer law is an instance of the distinct-guarantee law.
Consumer: source onExit and existing provider callbacks. -/
theorem ambient_finalizer_typed (root : ProgramSource) {w : World}
    {available guaranteed : Env.Requirement} {ty cleanupType : EffTy} {cleanup : RProgram}
    (bodyExit : ExitV) (payload : ExitOk w ty bodyExit)
    (errorBound : Ty.subN cleanupType.error ty.error = true)
    (typed : AmbientProg root w available (cleanupType, guaranteed, guaranteed) cleanup) :
    AmbientProg root w available (ty, guaranteed, guaranteed) (finalizerR bodyExit cleanup) :=
  ambient_finalizer_guarantees root bodyExit payload errorBound (Row.subset_refl _) typed

/-- The restoring setter promises its actual map on success and its entry bound on failure.
Consumer: captured release restoration through the existing finalizer program. -/
theorem ambient_restore_finalizer_guarantees (root : ProgramSource) {w : World} (available failure : Env.Requirement)
    (previous : Ctx) (services : ServicesFit w previous.services)
    (entry : Row.Subset failure available) (restored : Row.Subset failure previous.services.keysRow)
    (ty : EffTy) (bodyExit : ExitV) (payload : ExitOk w ty bodyExit) :
    AmbientProg root w available (ty, previous.services.keysRow, failure)
      (finalizerR bodyExit (fiberValR (.setContext previous) rfl)) :=
  ambient_finalizer_guarantees root bodyExit payload (Bounds.subN_never _) restored
    (ambient_setContext_guarantees root w available failure previous services entry restored)

/-- The common-row restoring finalizer retains its original statement.
Consumer: provideContext's source denotation adapter. -/
theorem ambient_restore_finalizer (root : ProgramSource) {w : World} (available guaranteed : Env.Requirement)
    (previous : Ctx) (services : ServicesFit w previous.services)
    (entry : Row.Subset guaranteed available) (restored : Row.Subset guaranteed previous.services.keysRow)
    (ty : EffTy) (bodyExit : ExitV) (payload : ExitOk w ty bodyExit) :
    AmbientProg root w available (ty, guaranteed, guaranteed)
      (finalizerR bodyExit (fiberValR (.setContext previous) rfl)) :=
  ambientProg_widen root (before := (ty, previous.services.keysRow, guaranteed))
    (Ty.subN_refl _) (Ty.subN_refl _) restored (Row.subset_refl _)
    (ambient_restore_finalizer_guarantees root available guaranteed previous services entry restored ty bodyExit payload)

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

/-- Captured body services and restored services need no inclusion between their full rows.
Consumer: Body.release_typed's ambient source adapter.
The failure guarantee is covered at both the entry and restoration cuts. -/
theorem ambient_onExit_restore_guarantees (root : ProgramSource) {w : World}
    {available bodyRow failure : Env.Requirement} {ty : EffTy} {body : RProgram}
    (previous : Ctx) (services : ServicesFit w previous.services)
    (entry : Row.Subset failure bodyRow) (restored : Row.Subset failure previous.services.keysRow)
    (typed : AmbientProg root w available (ty, bodyRow, bodyRow) body) :
    AmbientProg root w available (ty, previous.services.keysRow, failure)
      (onExitR body fun _ => fiberValR (.setContext previous) rfl) := by
  unfold onExitR
  refine ambient_guardBind root typed (fun later ordered exit _ payload => ?_)
    (fun _ _ exit _ absent => by cases exit <;> exact Bool.noConfusion absent)
    (Row.subset_trans entry (ambient_entry typed))
  have selected : ambientInput (ty, bodyRow, bodyRow) exit = bodyRow := by cases exit <;> rfl
  rw [selected]
  exact ambient_restore_finalizer_guarantees root bodyRow failure previous (servicesFit_map ordered.1.2.1 ordered.1.2.2.1 ordered.1.2.2.2.1 ordered.2 ordered.1.1.2
      (serviceTy_of_le ordered.1) services)
    entry restored ty exit payload.1

/-- The common-row restoring region retains its original statement.
Consumer: provider bodies and existing source callbacks. -/
theorem ambient_onExit_restore (root : ProgramSource) {w : World}
    {available guaranteed : Env.Requirement} {ty : EffTy} {body : RProgram}
    (previous : Ctx) (services : ServicesFit w previous.services)
    (restored : Row.Subset guaranteed previous.services.keysRow)
    (typed : AmbientProg root w available (ty, guaranteed, guaranteed) body) :
    AmbientProg root w available (ty, guaranteed, guaranteed)
      (onExitR body fun _ => fiberValR (.setContext previous) rfl) :=
  ambientProg_widen root (before := (ty, previous.services.keysRow, guaranteed))
    (Ty.subN_refl _) (Ty.subN_refl _) restored (Row.subset_refl _)
    (ambient_onExit_restore_guarantees root previous services (Row.subset_refl _) restored typed)

/-- A typed store leaf preserves the available context row.
The existing unit store certificate and answer proof remain unchanged.
Consumer: the actual synchronous source-operation arm of M5. -/
theorem ambient_storeR_of_typed (root : ProgramSource) {w : World} {ty : EffTy}
    (available : Env.Requirement) {op : SyncOp}
    (notForeign : ∀ scope capture, op ≠ .scopeAdd scope (.foreign capture))
    (typed : TypedProg root w ty (storeR op)) :
    AmbientProg root w available (ty, available, available) (storeR op) := by
  obtain ⟨cert, pre, next⟩ := TypedProg.store_inv typed
  refine .store cert ⟨pre, fun scope capture identity =>
    False.elim (notForeign scope capture identity)⟩ ?_ (Row.subset_refl _)
  intro later ordered answer post
  exact .pure ⟨TypedProg.pure_inv (next later ordered answer post), Row.subset_refl _⟩ (Row.subset_refl _)

/-- The actual foreign registration retains its captured callback and answers at the existing store columns.
Consumer: the ambient acquireIn body, including the already-closed scope branch. -/
theorem ambient_foreign_registration_typed (root : ProgramSource) {w : World}
    (available : Env.Requirement) (scope : Nat) (capture : Capture)
    (live : ScopeLive w scope) (typed : CaptureTyped root w capture)
    (policy : AmbientCapturePolicy root w capture) :
    AmbientProg root w available
      ((⟨.union .unit (.exitOf .unknown .unknown), .never, Env.Requirement.empty⟩ : EffTy),
        available, available) (storeR (.scopeAdd scope (.foreign capture))) := by
  refine .store () ⟨⟨live, typed⟩, ?_⟩ ?_ (Row.subset_refl _)
  · intro actualScope actualCapture identity
    cases identity
    exact policy
  · intro later _ answer post
    refine .pure ⟨⟨?_, True.intro⟩, Row.subset_refl _⟩ (Row.subset_refl _)
    rcases post with rfl | ⟨exit, rfl, member⟩
    · exact Or.inl True.intro
    · exact Or.inr member

/-- A terminal fiber leaf reuses its existing unit certificate and actual answer proof.
The producer supplies ambient preconditions and the actual unchanged entry row.
Consumer: the primitive source-action arms of the ambient M5 induction. -/
theorem ambient_fiber_leaf_of_typed (root : ProgramSource) {w : World} {ty : EffTy}
    (available : Env.Requirement) (op : FiberOp) (next : op.answer → RProgram)
    (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ exit, op ≠ .unguard exit)
    (notFinish : ∀ exit, op ≠ .finishFinalizer exit)
    (notScopeExit : ∀ previous scope exit, op ≠ .scopeExit previous scope exit)
    (typed : TypedProg root w ty (.vis (.inr op) next))
    (preAt : ∀ cert, fiberPre root w op cert → ambientFiberPre root w available op cert)
    (postAt : ∀ later, w.leHost later → ∀ cert answer,
      ambientFiberPost later available op cert answer → fiberPost later op cert answer)
    (inputAt : ∀ answer, ambientFiberInput available op answer = available)
    (terminal : ∀ answer, ∃ exit, next answer = .pure exit) :
    AmbientProg root w available (ty, available, available) (.vis (.inr op) next) := by
  obtain ⟨cert, pre, answerTyped⟩ := TypedProg.fiber_inv typed notGuard notUnguard notFinish notScopeExit
  refine .fiber notGuard notUnguard notFinish notScopeExit cert (preAt cert pre) ?_
    (Row.subset_refl _)
  intro later ordered answer post
  rw [inputAt answer]
  obtain ⟨exit, returned⟩ := terminal answer
  rw [returned]
  have member := answerTyped later ordered answer (postAt later ordered cert answer post)
  rw [returned] at member
  exact .pure ⟨TypedProg.pure_inv member, by cases exit <;> exact Row.subset_refl _⟩
    (Row.subset_refl _)

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

/-- **The protected context entry** at any update whose installed map covers the body's checked
row and keeps the entry row: the mask captured, the context installed with its restoration, the
body run at the installed row. Concept `residual-program-typing` (R4, decisions row 349); a step of
the closed M5 source claim. Consumers: `ambient_updateContext_provide` and the layer builds'
installs (`Typed/LayerArm.lean`). It states no machine preservation. -/
theorem ambient_updateContext (root : ProgramSource) {w : World}
    (available guaranteed required : Env.Requirement) (entry : Row.Subset guaranteed available)
    (ty : EffTy) (body : Region) (typedBody : RegionTyped root w body ⟨ty.answer, ty.error, required⟩)
    (arguments : RegionStackTyped root w available body)
    (update : Env.ContextUpdate) (updateTyped : ContextUpdateTyped w update)
    (covers : ∀ previous : Env.Ctx, previous.Satisfies available →
      (update.apply previous).Satisfies required ∧ (update.apply previous).Satisfies available) :
    AmbientProg root w available (ty, guaranteed, guaranteed)
      (updateContextR update body) := by
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
      have laterUpdate : ContextUpdateTyped later update := fun after grew =>
        updateTyped after (leHost_trans _ _ _ ordered grew)
      refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) cut ?_ ?_ entry
      · refine ⟨.contextEntry _ body flag intrinsic cut region (Ty.subN_refl _) (Ty.subN_refl _)
          laterUpdate, Row.subset_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro point ctx impossible
          cases impossible
        · intro flag point previous impossible
          cases impossible
        · intro actual impossible
          cases impossible
        · intro actual region' flag' shape
          cases shape
          refine ⟨intrinsic, region, Ty.subN_refl _, Ty.subN_refl _, fun previous covered => ?_⟩
          have installed := covers previous covered
          exact ⟨installed.1, installed.2, regionStackTyped_widen
            ((Provision.satisfies_iff_subset_keysRow _ available).mp installed.2)
            (regionStackTyped_mono ordered arguments)⟩
        · intro point role
          rcases role with impossible | ⟨ctx, impossible | impossible⟩
          · cases impossible
          · cases impossible
          · cases impossible
        · intro point memo scope impossible
          cases impossible
      · intro after _ delivered post
        refine .pure ⟨post, ?_⟩ entry
        cases delivered <;> exact entry
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause => exact ⟨exitOk_failure_of_errorN (Bounds.subN_never _) payload.1, entry⟩

/-- The actual provider mask checks the installed map's body requirements: the protected entry at
the merge with a supplied context of the provided keys.
Consumer: the typed source provider arm on the typed-state-reachable path. -/
theorem ambient_updateContext_provide (root : ProgramSource) {w : World}
    (available guaranteed required keys : Env.Requirement) (supplied : Ctx)
    (given : Fits w (Val.context supplied) (.contextOf keys))
    (needed : Row.Subset (Row.diff required keys) available)
    (entry : Row.Subset guaranteed available) (ty : EffTy) (body : Region)
    (typedBody : RegionTyped root w body ⟨ty.answer, ty.error, required⟩)
    (arguments : RegionStackTyped root w available body)
    (update : Env.ContextUpdate)
    (applies : ∀ previous, update.apply previous = previous.merge supplied.services) :
    AmbientProg root w available (ty, guaranteed, guaranteed)
      (updateContextR update body) := by
  obtain ⟨provided, decoded, suppliedMembers, suppliedKeys, _⟩ := fits_contextOf_inv given
  have same : provided = supplied := Option.some.inj
    (decoded.symm.trans (Val.context?_context _))
  subst provided
  refine ambient_updateContext root available guaranteed required entry ty body typedBody arguments
    update (fun later grew previous members => ?_) (fun previous covered => ?_)
  · rw [applies]
    exact servicesFit_merge members (servicesFit_map grew.1.2.1 grew.1.2.2.1
      grew.1.2.2.2.1 grew.2 grew.1.1.2 (serviceTy_of_le grew.1) suppliedMembers)
  · rw [applies]
    have fromBefore := Provision.satisfies_merge_left previous supplied.services
      (Row.diff required keys) (previous.satisfies_weaken covered needed)
    have fromGiven := Provision.satisfies_merge_right previous supplied.services keys suppliedKeys
    refine ⟨fun key member => ?_, Provision.satisfies_merge_left previous supplied.services available covered⟩
    by_cases suppliedKey : key ∈ keys
    · exact fromGiven key suppliedKey
    · exact fromBefore key ((Row.mem_diff key required keys).mpr ⟨member, suppliedKey⟩)

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
      PointTyped root w (p.child 0) bodyTy)
    (saved : AmbientStackTyped root w available (scopeParams root.program (p.child 0).path)
      (p.child 0).params) :
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
      (.program (p.child 0)) (child bodyTy bodyCheck) saved
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
      (.withFiber (.context required)) = .ok bodyTy → PointTyped root w (p.child 0) bodyTy)
    (saved : AmbientStackTyped root w available (scopeParams root.program (p.child 0).path)
      (p.child 0).params) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.provideContext context (.withFiber (.context required))) p) := by
  refine checked_provideContext_arm root w p env context (.withFiber (.context required))
    available ty supplied checked values evaluated coverage budget ?_ ?_ saved
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
      PointTyped root w (p.child 0) bodyTy)
    (saved : AmbientStackTyped root w available (scopeParams root.program (p.child 0).path)
      (p.child 0).params) :
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
    (child bodyTy bodyCheck) saved (.provideService key provided) (fun _ => rfl)

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
      (.withFiber (.context required)) = .ok bodyTy → PointTyped root w (p.child 0) bodyTy)
    (saved : AmbientStackTyped root w available (scopeParams root.program (p.child 0).path)
      (p.child 0).params) :
    AmbientProg root w available (ty, available, available)
      (denoteR root.program (.provideService key value (.withFiber (.context required))) p) := by
  exact checked_provideService_arm root w p env key value (.withFiber (.context required))
    available ty provided checked values evaluated services carriers coverage budget admitted saved


end Effect4.Program.Typed

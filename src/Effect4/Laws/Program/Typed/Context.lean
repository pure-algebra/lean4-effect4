import Effect4.Laws.Program.Typed.Seq
import Effect4.Laws.Program.Typing.CheckInversion

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
  | case2 =>
    rename_i notGetter
    rw [ambientFiberPre.eq_2 root w available op cert notGetter] at pre
    rw [ambientFiberPre.eq_2 root w' available op cert notGetter]
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
    exact ⟨strongExit_mono before after position.1 exit ordered payload.1, payload.2⟩

/-- The ambient instance exposes the bound at the actual current entry.
Consumer: interruption and current-code entry in the existing runtime typing relation. -/
theorem ambient_entry {root : ProgramSource} {w : World} {available : Env.Requirement}
    {position : AmbientPosition} {code : RProgram}
    (typed : AmbientProg root w available position code) :
    Row.Subset position.2.2 available := by
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
  asyncFinalizer w before after name := before.2 = after.2 ∧
    (frameProtocols root).asyncFinalizer w before.1 after.1 name
  iterator w before after name := before.2 = after.2 ∧
    (frameProtocols root).iterator w before.1 after.1 name
  loop w before after name cursor := before.2 = after.2 ∧
    (frameProtocols root).loop w before.1 after.1 name cursor
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

end Effect4.Program.Typed

import Effect4.Laws.Program.Typed.Context

/-!
Concept: residual-program-typing, R4 and R9; helper of the closed M5 source claim.
The existing program arrows retain the actual protected entry of a captured release body.
The entry index separates pre-entry interruption from completion after context restoration.
The physical premise is supplied by the evaluator and saved-mask region, not source spelling.
This module establishes no whole-machine preservation or outside-runtime observation.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

/-- True forgets the physical mask; false records an established noninterruptible entry.
Consumer: the captured release body and current, saved and queued position adapters. -/
abbrev AmbientEntryInput := Env.Requirement × Bool

/-- The actual frame discharges protection; ordinary entry makes no mask assertion. -/
def AmbientEntryAt (input : AmbientEntryInput) (saved : RSaved) : Prop :=
  input.2 = false → saved.interruptible = false

/-- Interruption before ordinary evaluation must retain the guaranteed failure services. -/
def ambientEntryBound (input : AmbientEntryInput) (position : AmbientPosition) : Prop :=
  input.2 = false ∨ Row.Subset position.failureRow input.1

/-- Whole fiber actions return through the saved entry mask, while setters update the row. -/
def ambientEntryStep (input : AmbientEntryInput) (op : FiberOp) (answer : op.answer) : AmbientEntryInput :=
  (ambientFiberInput input.1 op answer, input.2)

/-- The actual false onExit pop protects its callback; other callbacks forget protection. -/
def ambientGuardInput (kind : GuardKind) (position : AmbientPosition) (exit : ExitV) : AmbientEntryInput :=
  (ambientInput position exit, match kind with | .onExit false => false | _ => true)

/-- The protected instance uses the same program constructors and strong value membership. -/
abbrev AmbientProgAt (root : ProgramSource) (world : Typed.World) (input : AmbientEntryInput)
    (position : AmbientPosition) (program : RProgram) : Prop :=
  ProgramArrow (fun w input => ambientStorePre root w input.1)
    (fun w (_ : AmbientEntryInput) => storePost w)
    (fun w input => ambientFiberPre root w input.1)
    (fun w input => ambientFiberPost w input.1) ambientEntryStep
    (fun w input => AmbientExit w input.1)
    (fun w input kind mid exit => kind.hasExitArm exit = true ∧ AmbientExit w input.1 mid exit)
    (fun position exit => (ambientInput position exit, true))
    (fun context => (context.services.keysRow, true)) ambientEntryBound ambientGuardInput
    world input position program

/-- Conservative positions forget only the mask fact, never context coverage. -/
theorem ambientEntry_forget {available : Env.Requirement} {frame : RSaved}
    (_protectedEntry : AmbientEntryAt (available, false) frame) : AmbientEntryAt (available, true) frame := by
  intro impossible
  exact Bool.noConfusion impossible

/-- The actual false onExit producer supplies protected callback entry on either exit. -/
theorem ambientGuardInput_false_at (interp : RInterp) (position : AmbientPosition)
    (exit : ExitV) (next : ExitV → RProgram) (rest : List ScopeFrame) (frame : RSaved) :
    AmbientEntryAt (ambientGuardInput (.onExit false) position exit)
      (popR interp exit (.resume (.onExit false) next :: rest) frame).1 := by
  intro _
  cases exit <;> rfl

/-- True onExit makes no false-mask claim, even when the prior frame is interruptible. -/
theorem ambientGuardInput_true_at (interp : RInterp) (position : AmbientPosition)
    (exit : ExitV) (next : ExitV → RProgram) (rest : List ScopeFrame) (frame : RSaved) :
    AmbientEntryAt (ambientGuardInput (.onExit true) position exit)
      (popR interp exit (.resume (.onExit true) next :: rest) frame).1 := by
  intro impossible
  exact Bool.noConfusion impossible

/-- Existing ambient certificates enter the same carrier at either physical entry index.
This connector adds no returned services and keeps the original type-only instance unchanged. -/
theorem ambientProg_entry (root : ProgramSource) {world : Typed.World} {available : Env.Requirement}
    {position : AmbientPosition} {program : RProgram}
    (typed : AmbientProg root world available position program) (mode : Bool) :
    AmbientProgAt root world (available, mode) position program := by
  induction typed generalizing mode with
  | pure payload entry => exact .pure payload (Or.inr entry)
  | store cert pre _ entry ih =>
    exact .store cert pre (fun later ordered answer post => ih later ordered answer post mode) (Or.inr entry)
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ entry ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert pre
      (fun later ordered answer post => ih later ordered answer post mode) (Or.inr entry)
  | guard mid _ _ skip entry ihBody ihRun =>
    exact .guard mid (ihBody mode)
      (fun later ordered exit post => ihRun later ordered exit post _) skip (Or.inr entry)
  | unguard payload entry => exact .unguard payload (Or.inr entry)
  | finishFinalizer payload entry => exact .finishFinalizer payload (Or.inr entry)
  | scopedGuard mid previous scope _ callback live services widen entry ihBody =>
    exact .scopedGuard mid previous scope (ihBody mode) callback live services widen (Or.inr entry)

/-- The restoring setter starts protected and completes under the actual previous map. -/
theorem ambient_setContext_protected (root : ProgramSource) (world : Typed.World)
    (available : Env.Requirement) (previous : Ctx) (services : ServicesFit world previous.services) :
    AmbientProgAt root world (available, false)
      (EffTy.pure .unit, previous.services.keysRow, previous.services.keysRow)
      (fiberValR (.setContext previous) rfl) := by
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () services ?_ (Or.inl rfl)
  intro _ _ answer post
  change answer = Val.unit at post
  subst answer
  exact .pure ⟨strongExit_success _ _ _ True.intro, Row.subset_refl _⟩ (Or.inl rfl)

/-- Protected cleanup restores its actual previous services on either exit.
Consumer: the captured release body; no entry coverage is inferred from a future success. -/
theorem ambient_restore_finalizer_protected (root : ProgramSource) {world : Typed.World}
    (available : Env.Requirement) (previous : Ctx) (services : ServicesFit world previous.services)
    (type : EffTy) (bodyExit : ExitV) (payload : ExitOk world type bodyExit) :
    AmbientProgAt root world (available, false)
      (type, previous.services.keysRow, previous.services.keysRow)
      (finalizerR bodyExit (fiberValR (.setContext previous) rfl)) := by
  let middle : AmbientPosition :=
    ((⟨.unit, type.error, Env.Requirement.empty⟩ : EffTy),
      previous.services.keysRow, previous.services.keysRow)
  have setter : AmbientProgAt root world (available, false) middle
      (fiberValR (.setContext previous) rfl) := by
    refine ProgramArrow.outputMap
      (ty := ((EffTy.pure .unit, previous.services.keysRow, previous.services.keysRow) : AmbientPosition))
      (ty' := middle) (ambient_setContext_protected root world available previous services)
      ?_ (fun _ bound => bound)
    intro later input exit clean
    exact ⟨exitOk_widen (mid := EffTy.pure .unit) (ty := middle.type)
      (Ty.subN_refl .unit) (Bounds.subN_never type.error) clean.1, clean.2⟩
  have work : ∀ originalExit, ExitOk world type originalExit →
      AmbientProgAt root world (available, false) middle
      (match originalExit with
      | .success _ => fiberValR (.setContext previous) rfl
      | .failure _ => (guardR .onFailure (fiberValR (.setContext previous) rfl)).bind fun
          | .success value => .pure (.success value)
          | .failure cause => .pure (Exit.restoreAfterFinalizer originalExit (.failure cause))) := by
    intro originalExit originalPayload
    cases originalExit with
    | success value => exact setter
    | failure cause =>
      refine ProgramArrow.guardBind setter (fun later ordered exit post => ?_)
        (fun later ordered exit clean absent => ?_) (Or.inl rfl)
      · cases exit with
        | success value => exact Bool.noConfusion post.1
        | failure cleanupCause =>
          refine .pure ⟨?_, Row.subset_refl _⟩ (Or.inr (Row.subset_refl _))
          have original : ExitOk later middle.type (.failure cause) :=
            exitOk_failure_of_errorN (Ty.subN_refl _) (strongExit_mono _ _ _ _ ordered originalPayload)
          exact exitOk_restore original post.2.1
      · cases exit with
        | success value => exact clean
        | failure cleanupCause => exact Bool.noConfusion absent
  unfold finalizerR
  refine ProgramArrow.guardBind (work bodyExit payload) (fun later ordered exit post => ?_)
    (fun later ordered exit clean absent => ?_) (Or.inl rfl)
  · cases exit with
    | success value =>
      refine .finishFinalizer ⟨strongExit_mono _ _ _ _ ordered payload, ?_⟩
        (Or.inr (Row.subset_refl _))
      cases bodyExit <;> exact Row.subset_refl _
    | failure cause => exact Bool.noConfusion post.1
  · cases exit with
    | success value => exact Bool.noConfusion absent
    | failure cause =>
      exact ⟨exitOk_failure_of_errorN (Ty.subN_refl _) clean.1, Row.subset_refl _⟩

/-- The actual loop top can deliver a deferred interruption under a false physical mask.
Consumer: current, saved and queued ambient input selection. -/
def ambientEntryMode (saved : RSaved) : Bool :=
  saved.interruptible || saved.deferredInterrupt

/-- The effective protected input follows both physical fields of the actual saved frame. -/
theorem ambientEntryMode_at (available : Env.Requirement) (saved : RSaved) :
    AmbientEntryAt (available, ambientEntryMode saved) saved := by
  intro protectedEntry
  exact (Bool.or_eq_false_iff.mp protectedEntry).1

/-- A false onExit callback retains any already-deferred interruption.
Consumer: the actual saved-callback entry adapter, after the loop top has cleared the flag. -/
theorem ambientEntryMode_false_pop (interp : RInterp) (exit : ExitV)
    (next : ExitV → RProgram) (rest : List ScopeFrame) (saved : RSaved) :
    ambientEntryMode (popR interp exit (.resume (.onExit false) next :: rest) saved).1 =
      saved.deferredInterrupt := by
  cases exit <;> rfl

/-- World growth retains the protected program certificate without changing its input fields.
Consumer: the ambient current and queued-code world adapters. -/
theorem ambientProgAt_mono (root : ProgramSource) {world later : Typed.World}
    (ordered : world.leHost later) {input : AmbientEntryInput} {position : AmbientPosition}
    {code : RProgram} (typed : AmbientProgAt root world input position code) :
    AmbientProgAt root later input position code := by
  refine ProgramArrow.mono ?_ ?_ ?_ ordered typed
  · intro before after entry op cert order pre
    exact ambientStorePre_mono root order entry.1 op cert pre
  · intro before after entry op cert order pre
    exact ambientFiberPre_mono root order entry.1 op cert pre
  · intro before after entry result exit order payload
    exact ⟨strongExit_mono before after result.type exit order payload.1, payload.2⟩

/-- The same certificate weakens only its conservative entry flag to established protection.
Consumer: callback installation when its actual producer clears the deferred flag. -/
theorem ambientProgAt_protect (root : ProgramSource) {world : Typed.World}
    {input : AmbientEntryInput} {position : AmbientPosition} {code : RProgram}
    (typed : AmbientProgAt root world input position code) :
    AmbientProgAt root world (input.1, false) position code := by
  induction typed with
  | pure payload _ => exact .pure payload (Or.inl rfl)
  | store cert pre _ _ ih =>
    exact .store cert pre (fun later ordered answer post => ih later ordered answer post) (Or.inl rfl)
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ _ ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert pre
      (fun later ordered answer post => ih later ordered answer post) (Or.inl rfl)
  | guard mid _ run skip _ ihBody _ =>
    exact .guard mid ihBody run skip (Or.inl rfl)
  | unguard payload _ => exact .unguard payload (Or.inl rfl)
  | finishFinalizer payload _ => exact .finishFinalizer payload (Or.inl rfl)
  | scopedGuard mid previous scope _ callback live services widen _ ihBody =>
    exact .scopedGuard mid previous scope ihBody callback live services widen (Or.inl rfl)

/-- Ordinary callback evidence enters the actual saved mask without widening its row.
Consumer: current and queued callback installation at the effective entry cut. -/
theorem ambientProgAt_at_saved (root : ProgramSource) {world : Typed.World}
    {available : Env.Requirement} {position : AmbientPosition} {code : RProgram}
    (typed : AmbientProgAt root world (available, true) position code) (saved : RSaved) :
    AmbientProgAt root world (available, ambientEntryMode saved) position code := by
  cases flag : ambientEntryMode saved with
  | false => exact ambientProgAt_protect root typed
  | true => exact typed

/-- The existing saved-code relation reads its effective input from the actual saved frame.
Consumer: parked and resumed positions in the ambient runtime relation. -/
abbrev AmbientSaved (root : ProgramSource) (world : Typed.World) (available : Env.Requirement)
    (final : AmbientPosition) (saved : RSaved) : Prop :=
  Contracts.SavedArrow (AmbientProgAt root) (fun world input => AmbientExit world input.1)
    (ambientFrameProtocols root) (fun position exit => (ambientInput position exit, true))
    (fun ctx => (ctx.services.keysRow, true)) ambientGuardInput
    world (available, ambientEntryMode saved) final saved

/-- The existing saved relation exposes the physical assertion of its selected input.
Consumer: actual parked-code and queued-overwrite adapters. -/
theorem ambientSaved_entry_at (root : ProgramSource) (world : Typed.World)
    (available : Env.Requirement) (final : AmbientPosition) (saved : RSaved)
    (_typed : AmbientSaved root world available final saved) :
    AmbientEntryAt (available, ambientEntryMode saved) saved :=
  ambientEntryMode_at available saved

/-- The actual captured release body retains all-exit restoration under its installed false mask.
The source body uses its own captured map; the returned map is the actual previous context.
Consumer: mask installation in Body and the original closed Assembly typing path. -/
theorem ambient_release_body_protected (root : ProgramSource) {world : Typed.World}
    (available : Env.Requirement) (point : Point) (previous : Ctx)
    (services : ServicesFit world previous.services) (type : EffTy)
    (typed : AmbientProg root world available (type, available, available)
      (denoteAt root.program point)) :
    AmbientProgAt root world (available, false)
      (type, previous.services.keysRow, previous.services.keysRow)
      (bodyR (interpR root.program) (.release point previous)) := by
  change AmbientProgAt root world (available, false)
    (type, previous.services.keysRow, previous.services.keysRow)
    (onExitR (denoteAt root.program point) fun _ => fiberValR (.setContext previous) rfl)
  unfold onExitR
  refine ProgramArrow.guardBind (ambientProg_entry root typed false)
    (fun later ordered exit post => ?_) (fun _ _ exit _ absent => ?_) (Or.inl rfl)
  · exact ambient_restore_finalizer_protected root _ previous
      (servicesFit_map ordered.1.2.1 ordered.1.2.2.1 ordered.1.2.2.2.1 ordered.2 ordered.1.1.2
        (serviceTy_of_le ordered.1) services) type exit post.2.1
  · cases exit <;> exact Bool.noConfusion absent

end Effect4.Program.Typed

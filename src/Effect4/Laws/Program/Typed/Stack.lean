import Effect4.Laws.Program.Typed.Residual
import Effect4.Laws.Program.Typed.Adequacy
import Effect4.Laws.Auto.Obligations

/-!
# Laws.Program.Typed.Stack — the saved stack's walk preserves typing

Slice 5 (M4) of the foundations plan, as amended by the contract ruling of 2026-09-23 and the
protocol repair of 2026-09-24. `popR_typed`: delivering a typed exit to a typed stack either
installs typed code over a typed remaining stack, or completes with an exit typed at the stack's
final type. Its only premises are `HookLaws` (the three named hooks) and `InterruptProvenance`
(recorded causes are interrupts); there is no run premise. A preempted catch passes the sanitized
cause (`U-01`), which carries no `Fail`. Its original typed exit and recorded-interrupt
provenance separately supply the part-one defect exclusion.

The stacks are Kripke-closed (decisions row 135, `Contracts.FrameAccepts`): the walk reads each
frame's clauses at the current world, and every stack it hands back, including a frame it
re-pushes after an iterator or loop resume, holds at every later world. `HookLaws` therefore
returns a resumed protocol at every later world with one intermediate type.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-- Exactly the facts `popR`'s three named-hook arms need about an interpreter. A resume's
protocol is handed back at every later world with one intermediate type, so the frame the walk
re-pushes is Kripke-closed (row 135; `output_not_kripke` refutes a per-world choice). -/
structure HookLaws (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols) : Prop where
  asyncFinalizer : ∀ w tin tout name, hooks.asyncFinalizer w tin tout name →
    tin = tout ∧ ∀ cause, ExitOk w tin (.failure cause) → cause.hasInterrupts = true →
      TypedProg root w tout (interp.cancelThenFail name cause)
  iterator : ∀ w tin tout name, hooks.iterator w tin tout name →
    tin.error = tout.error ∧ ∀ v, Fits w v tin.answer →
      match (interp.iterNext name v).2 with
      | .done result => ExitOk w tout (.success result)
      | .halt cause => ExitOk w tout (.failure cause)
      | .resume code name' => ∃ tin', TypedProg root w tin' code ∧
          ∀ w', w.leHost w' → hooks.iterator w' tin' tout name'
  loop : ∀ w tin tout name cursor, hooks.loop w tin tout name cursor →
    tin.error = tout.error ∧ ∀ v, Fits w v tin.answer →
      match interp.loopResume name cursor v with
      | .continue cursor' body => ∃ tin', TypedProg root w tin' body ∧
          ∀ w', w.leHost w' → hooks.loop w' tin' tout name cursor'
      | .finish code => TypedProg root w tout code

/-- The walk ran a `scoped` guard's slot (decisions row 188 (a)): the current code is that scope's
exit callback, whose exit is typed at the remaining stack's input type, over the remaining stack
with the finalizer mask the `onExit` slot pushes. `prepareScopedExitR` consumes it in the same
evaluation; it is no typed program. -/
def CallbackSaved (root : ProgramSource) (hooks : FrameProtocols) (w : World) (tout : EffTy)
    (x : RSaved) : Prop :=
  ∃ ty prev sc ex, scopeExitCallback? x.current = some (prev, sc, ex) ∧ ExitOk w ty ex ∧
    hooks.scopeExit w prev sc ∧ StackAccepts (TypedProg root) ExitOk hooks w ty tout x.stack ∧
    InterruptProvenance x

/-- The outcomes of the walk, at the saved stack's final type: typed code over the remaining
stack, a scope's exit callback over it (row 188 (a)), or the exit the whole stack delivered. -/
def WalkTyped (root : ProgramSource) (hooks : FrameProtocols) (w : World) (tout : EffTy) :
    RSaved × Option ExitV → Prop
  | (frame, none) => SavedOk (TypedProg root) ExitOk hooks w tout frame ∨
      CallbackSaved root hooks w tout frame
  | (_, some ex) => ExitOk w tout ex

/-! ## Clean exits along the walk -/

/-- A cause whose reasons are all interrupts is clean. -/
theorem cleanExit_of_interrupts (c : CauseV) (h : ∀ r ∈ c.reasons, r.tag = .interrupt) :
    cleanExit (.failure c) = true := by
  unfold cleanExit
  rw [List.all_eq_true]
  intro r hr
  rw [h r hr]
  rfl

/-- A recorded interrupt is clean. -/
theorem recorded_clean {x : RSaved} (hp : InterruptProvenance x) {c : CauseV}
    (hc : x.interruptedCause = some c) : cleanExit (.failure c) = true :=
  cleanExit_of_interrupts c (hp.recorded c hc)

/-- The cause a masked region injects is clean. -/
theorem pendingCause_clean {x : RSaved} (hp : InterruptProvenance x) :
    cleanExit (.failure x.pendingCause) = true := by
  cases hc : x.interruptedCause with
  | some c =>
    have : x.pendingCause = c := by simp only [RSaved.pendingCause, hc, Option.getD_some]
    rw [this]
    exact recorded_clean hp hc
  | none =>
    have : x.pendingCause = Cause.empty := by simp only [RSaved.pendingCause, hc, Option.getD_none]
    rw [this]
    rfl

/-- The sanitized cause at a preempted catch is clean (`U-01`, `Cause.sanitize_clean`). -/
theorem sanitize_clean_exit {x : RSaved} (hp : InterruptProvenance x) (cause : CauseV) {ic : CauseV}
    (hic : x.interruptedCause = some ic) : cleanExit (.failure (Cause.sanitize cause ic)) = true := by
  have hne : ∀ r ∈ ic.reasons, r.tag ≠ .fail := by
    intro r hr heq
    have := hp.recorded ic hic r hr
    rw [heq] at this
    cases this
  unfold cleanExit
  rw [List.all_eq_true]
  intro r hr
  exact bne_iff_ne.mpr (Cause.sanitize_clean cause ic hne r hr)

/-- A recorded cause has only interrupt reasons, so it meets part one's exclusion. -/
theorem recorded_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x)
    {cause : CauseV} (recorded : x.interruptedCause = some cause) :
    NoShapeDefect ty (.failure cause) :=
  noShapeDefect_of_interrupts ty cause (hp.recorded cause recorded)

/-- The injected pending cause is recorded interruption or the empty cause. -/
theorem pendingCause_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x) :
    NoShapeDefect ty (.failure x.pendingCause) := by
  cases recorded : x.interruptedCause with
  | some cause =>
    have pending : x.pendingCause = cause := by
      simp only [RSaved.pendingCause, recorded, Option.getD_some]
    rw [pending]
    exact recorded_noShapeDefect ty hp recorded
  | none =>
    have pending : x.pendingCause = Cause.empty := by
      simp only [RSaved.pendingCause, recorded, Option.getD_none]
    rw [pending]
    exact noShapeDefect_of_interrupts ty Cause.empty (fun _ member => nomatch member)

/-- Preemption keeps exclusion only when the original cause has it; provenance supplies
exclusion of the recorded cause. No requirement-row transport is claimed in part one. -/
theorem sanitize_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x)
    (cause : CauseV) {interrupted : CauseV} (recorded : x.interruptedCause = some interrupted)
    (shape : NoShapeDefect ty (.failure cause)) :
    NoShapeDefect ty (.failure (Cause.sanitize cause interrupted)) :=
  noShapeDefect_sanitize ty cause interrupted shape (recorded_noShapeDefect ty hp recorded)

/-- In part one, failure membership depends on the error column and the exclusion
is independent of all type columns. -/
theorem strongExit_failure_of_error {w : World} {tin tout : EffTy} {c : CauseV}
    (herr : tin.error = tout.error) (h : ExitOk w tin (.failure c)) : ExitOk w tout (.failure c) := ⟨fitsExit_failure_of_error herr h.1, h.2⟩

theorem walk_saved {root : ProgramSource} {hooks : FrameProtocols} {w : World} {tout : EffTy}
    {x : RSaved} (tin : EffTy) (code : TypedProg root w tin x.current)
    (stack : StackAccepts (TypedProg root) ExitOk hooks w tin tout x.stack)
    (hp : InterruptProvenance x) : WalkTyped root hooks w tout (x, none) :=
  .inl ⟨tin, code, stack, hp⟩

theorem walk_done {root : ProgramSource} {hooks : FrameProtocols} {w : World} {tout : EffTy}
    {x : RSaved} {ex : ExitV} (h : ExitOk w tout ex) : WalkTyped root hooks w tout (x, some ex) :=
  h

/-! ## The walk -/

theorem popR_typed (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (laws : HookLaws root interp hooks) (w : World) :
    ∀ (stack : List ScopeFrame) (tin tout : EffTy) (ex : ExitV) (frame : RSaved),
      StackAccepts (TypedProg root) ExitOk hooks w tin tout stack →
      ExitOk w tin ex → InterruptProvenance frame →
      WalkTyped root hooks w tout (popR interp ex stack frame) := by
  intro stack
  induction stack with
  | nil =>
    intro tin tout ex frame hstack hex _
    cases hstack
    exact hex
  | cons slot rest ih =>
    intro tin tout ex frame hstack hex hp
    cases hstack with
    | cons head tail =>
    cases head with
    | restoreMask flag =>
      obtain ⟨current, stack, interruptible, ic, deferred⟩ := frame
      cases ic with
      | none => exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
      | some c =>
        cases flag with
        | false =>
          cases ex <;> simp only [popR, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;>
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        | true =>
          cases ex with
          | success v =>
            simp only [popR, Bool.not_false, Bool.and_self, ↓reduceIte]
            exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ c (recorded_clean hp rfl) (recorded_noShapeDefect _ hp rfl)))
              tail ⟨hp.recorded, hp.deferred⟩
          | failure c' =>
            simp only [popR, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
    | finalizerMask flag =>
      obtain ⟨current, stack, interruptible, ic, deferred⟩ := frame
      cases ic with
      | none => exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
      | some c =>
        cases flag with
        | false =>
          cases ex <;> simp only [popR, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;>
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        | true =>
          cases ex with
          | success v =>
            simp only [popR, Bool.not_false, Bool.and_self, ↓reduceIte]
            exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ c (recorded_clean hp rfl) (recorded_noShapeDefect _ hp rfl)))
              tail ⟨hp.recorded, hp.deferred⟩
          | failure c' =>
            simp only [popR, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
    | resume kind next run skip =>
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      have hp' : ∀ (c : RProgram) (s : List ScopeFrame) (b : Bool),
          InterruptProvenance ⟨c, s, b, ic, deferred⟩ := fun _ _ _ => ⟨hp.recorded, hp.deferred⟩
      -- Provenance makes the recorded cause clean; the original cause must also
      -- satisfy exclusion, supplied by the incoming typed exit.
      have preempt : ∀ (ty : EffTy) (cause ic' : CauseV),
          NoShapeDefect ty (.failure cause) → ic = some ic' →
          ExitOk w ty (.failure (Cause.sanitize cause ic')) := fun ty cause _ shape h =>
        strongExit_of_clean w ty _ (sanitize_clean_exit hp cause h)
          (sanitize_noShapeDefect ty hp cause h shape)
      cases kind with
      | onSuccess =>
        cases ex with
        | success v =>
          simp only [popR]
          exact walk_saved _ (run w (leHost_refl w) _ hex rfl) tail (hp' _ _ _)
        | failure c =>
          simp only [popR]
          cases ic <;> exact ih _ _ _ _ tail (skip w (leHost_refl w) _ hex rfl) (hp' _ _ _)
      | onFailure =>
        cases ex with
        | success v =>
          simp only [popR]
          exact ih _ _ _ _ tail (skip w (leHost_refl w) _ hex rfl) (hp' _ _ _)
        | failure c =>
          simp only [popR]
          cases i <;> cases ic
          · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) tail (hp' _ _ _)
          · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) tail (hp' _ _ _)
          · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) tail (hp' _ _ _)
          · exact ih _ _ _ _ tail (preempt _ c _ hex.2 rfl) (hp' _ _ _)
      | all =>
        cases ex with
        | success v =>
          simp only [popR]
          exact walk_saved _ (run w (leHost_refl w) _ hex rfl) tail (hp' _ _ _)
        | failure c =>
          simp only [popR]
          cases i <;> cases ic
          · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) tail (hp' _ _ _)
          · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) tail (hp' _ _ _)
          · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) tail (hp' _ _ _)
          · exact ih _ _ _ _ tail (preempt _ c _ hex.2 rfl) (hp' _ _ _)
      | onExit b =>
        cases b with
        | false =>
          cases ex <;> simp only [popR] <;>
            exact walk_saved _ (run w (leHost_refl w) _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
        | true =>
          cases ex with
          | success v =>
            simp only [popR]
            exact walk_saved _ (run w (leHost_refl w) _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
          | failure c =>
            simp only [popR]
            cases i <;> cases ic
            · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact walk_saved _ (run w (leHost_refl w) _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact ih _ _ _ _ tail (preempt _ c _ hex.2 rfl) (hp' _ _ _)
    | scopedResume next prev sc callback hook widen =>
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex <;> simp only [popR] <;>
        exact .inr ⟨_, prev, sc, _, callback _, widen w (leHost_refl w) _ hex, hook w (leHost_refl w),
          .cons (.finalizerMask _ _) tail, ⟨hp.recorded, hp.deferred⟩⟩
    | answer next run =>
      have hrun := run w (leHost_refl w) ex hex
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      simp only [popR]
      split
      · rename_i ex' heq
        rw [heq] at hrun
        exact ih _ _ _ _ tail (TypedProg.pure_inv hrun) ⟨hp.recorded, hp.deferred⟩
      · rename_i ex' k heq
        rw [heq] at hrun
        exact ih _ _ _ _ tail (unguard_payload_inv _ _ _ _ _ hrun) ⟨hp.recorded, hp.deferred⟩
      · exact walk_saved _ hrun tail ⟨hp.recorded, hp.deferred⟩
    | asyncFinalizer name protocol =>
      obtain ⟨same, cancel⟩ := laws.asyncFinalizer w _ _ name (protocol w (leHost_refl w))
      subst same
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        have code : TypedProg root w tin
            (if c.hasInterrupts then interp.cancelThenFail name c else .pure (.failure c)) := by
          split
          · rename_i hint
            exact cancel c hex hint
          · exact TypedProg.pure hex
        simp only [popR]
        cases i
        · exact walk_saved _ code tail ⟨hp.recorded, hp.deferred⟩
        · exact walk_saved _ code (.cons (.restoreMask _ _) tail) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        simp only [popR]
        cases i <;> cases ic
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ _ (pendingCause_clean ⟨hp.recorded, hp.deferred⟩)
          (pendingCause_noShapeDefect _ ⟨hp.recorded, hp.deferred⟩)))
            tail ⟨hp.recorded, hp.deferred⟩
    | iter name protocol =>
      obtain ⟨errors, step⟩ := laws.iterator w _ _ name (protocol w (leHost_refl w))
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail (strongExit_failure_of_error errors hex) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex.1
        cases hs : (interp.iterNext name v).2 with
        | done result =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_saved _ (TypedProg.pure h) tail ⟨hp.recorded, hp.deferred⟩
        | halt cause =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_saved _ (TypedProg.pure h) tail ⟨hp.recorded, hp.deferred⟩
        | resume code name' =>
          rw [hs] at h
          obtain ⟨tin', typed, next⟩ := h
          simp only [popR, hs]
          exact walk_saved _ typed (.cons (.iter _ next) tail) ⟨hp.recorded, hp.deferred⟩
    | loop name cursor protocol =>
      obtain ⟨errors, step⟩ := laws.loop w _ _ name cursor (protocol w (leHost_refl w))
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail (strongExit_failure_of_error errors hex) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex.1
        cases hs : interp.loopResume name cursor v with
        | «continue» cursor' body =>
          rw [hs] at h
          obtain ⟨tin', typed, next⟩ := h
          simp only [popR, hs]
          exact walk_saved _ typed (.cons (.loop _ _ next) tail) ⟨hp.recorded, hp.deferred⟩
        | finish code =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_saved _ h tail ⟨hp.recorded, hp.deferred⟩

/-! ## The reference interpreter's hooks -/

/-- The concrete hook contracts are exactly what the walk needs of `interpR` (the M5 hook
obligation of the slice 5 brief, closed here because the repaired protocols state them
directly). Each protocol reads its step at the current world; a resumed tail holds at every
later world because the protocols are closed in their own definitions
(`iteratorProtocol_mono`, `loopProtocol_mono`). -/
theorem hookLaws_interpR (root : ProgramSource) :
    HookLaws root (interpR root.program) (frameProtocols root) where
  asyncFinalizer w _ _ _ h := ⟨h.1, h.2 w (leHost_refl w)⟩
  iterator w tin tout name h := by
    cases h with
    | step errors _ next =>
      refine ⟨errors, fun v hv => ?_⟩
      have answer := next w (leHost_refl w) v hv
      revert answer
      generalize ((interpR root.program).iterNext name v).2 = s
      intro answer
      cases answer with
      | done result typed => exact typed
      | halt cause typed => exact typed
      | resume code name' tin' typed tail =>
        exact ⟨tin', typed, fun _ ord => iteratorProtocol_mono ord tail⟩
  loop w tin tout name cursor h := by
    cases h with
    | step errors _ next =>
      refine ⟨errors, fun v hv => ?_⟩
      have answer := next w (leHost_refl w) v hv
      revert answer
      generalize (interpR root.program).loopResume name cursor v = s
      intro answer
      cases answer with
      | «continue» cursor' body tin' typed tail =>
        exact ⟨tin', typed, fun _ ord => loopProtocol_mono ord tail⟩
      | finish code typed => exact typed

/-- The walk on the reference interpreter needs no hook premise. -/
theorem popR_typed_interpR (root : ProgramSource) (w : World) (stack : List ScopeFrame)
    (tin tout : EffTy) (ex : ExitV) (frame : RSaved)
    (hstack : StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin tout stack)
    (hex : ExitOk w tin ex) (hp : InterruptProvenance frame) :
    WalkTyped root (frameProtocols root) w tout (popR (interpR root.program) ex stack frame) :=
  popR_typed root _ _ (hookLaws_interpR root) w stack tin tout ex frame hstack hex hp

/-! ## Saving and delivering -/

/-- Installing an operation's code below its answer adapter keeps the saved state typed: the
adapter and the old stack meet at `middle`, the code has the operation's own type `tin`. The
adapter is typed at every later world, as `TypedProg`'s own continuations are (row 135). -/
theorem saveAnswerR_typed (root : ProgramSource) (hooks : FrameProtocols) (w : World)
    (tin middle final : EffTy) (f : RFiber) (next : ExitV → RProgram) (code : RProgram)
    (hcode : TypedProg root w tin code)
    (hnext : ∀ w', w.leHost w' → ∀ ex, ExitOk w' tin ex → TypedProg root w' middle (next ex))
    (hstack : StackAccepts (TypedProg root) ExitOk hooks w middle final f.frame.stack)
    (hp : InterruptProvenance f.frame) :
    SavedOk (TypedProg root) ExitOk hooks w final (answerR (saveAnswerR f next) code).frame :=
  ⟨tin, hcode, .cons (.answer next hnext) hstack, ⟨hp.recorded, hp.deferred⟩⟩

/-- The fiber a matching resume leaves: unparked, the token's pending entries dropped, the
delivered code current, the stack untouched. -/
def resumed (f : RFiber) (token : Nat) (code : RProgram) : RFiber :=
  { f with
    parked := .notParked
    pending := f.pending.filter (fun p => p.token ≠ token)
    frame := { f.frame with current := code } }

/-- A resume at the parked token installs the delivered code, which `ResumeOk` types at the
token's declared type, over the stack the park saved at that type. -/
theorem deliver_active (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (w : World) (tin final : EffTy) (m : RState) (f : RFiber) (token : Nat) (code : RProgram)
    (rest : List RCmd) (found : m.fiber? f.id = some f) (parked : f.parked = .withGuard token)
    (declared : w.Θ f.id token = some tin) (typed : ResumeOk (TypedProg root) w f.id token code)
    (hstack : StackAccepts (TypedProg root) ExitOk hooks w tin final f.frame.stack)
    (hp : InterruptProvenance f.frame) :
    (letI := termEvaluatorFor root.program
     driveStep interp m (.resume f.id token code) rest) =
      ((m.update (resumed f token code)).emit [.resumedWith f.id token code], .evaluate f.id :: rest) ∧
    SavedOk (TypedProg root) ExitOk hooks w final (resumed f token code).frame := by
  refine ⟨?_, tin, typed tin declared, hstack, ⟨hp.recorded, hp.deferred⟩⟩
  simp only [driveStep, found, parked, ↓reduceIte]
  rfl

/-- A resume at another token leaves the machine and the queue as they were. -/
theorem deliver_stale (root : ProgramSource) (interp : RInterp) (m : RState) (f : RFiber)
    (parkedToken token : Nat) (code : RProgram) (rest : List RCmd)
    (found : m.fiber? f.id = some f) (parked : f.parked = .withGuard parkedToken)
    (stale : parkedToken ≠ token) :
    (letI := termEvaluatorFor root.program
     driveStep interp m (.resume f.id token code) rest) = (m, rest) := by
  simp only [driveStep, found, parked, stale, ↓reduceIte]


namespace M4Stack

theorem popR_typed (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (_laws : HookLaws root interp hooks) (w : World) : ProofGraph.Obligation
    (∀ (stack : List ScopeFrame) (tin tout : EffTy) (ex : ExitV) (frame : RSaved),
      StackAccepts (TypedProg root) ExitOk hooks w tin tout stack →
      ExitOk w tin ex → InterruptProvenance frame →
      WalkTyped root hooks w tout (popR interp ex stack frame)) := ⟨⟩

theorem saveAnswerR_typed (root : ProgramSource) (hooks : FrameProtocols) (w : World)
    (tin middle final : EffTy) (f : RFiber) (next : ExitV → RProgram) (code : RProgram)
    (_hcode : TypedProg root w tin code)
    (_hnext : ∀ w', w.leHost w' → ∀ ex, ExitOk w' tin ex → TypedProg root w' middle (next ex))
    (_hstack : StackAccepts (TypedProg root) ExitOk hooks w middle final f.frame.stack)
    (_hp : InterruptProvenance f.frame) : ProofGraph.Obligation
    (SavedOk (TypedProg root) ExitOk hooks w final (answerR (saveAnswerR f next) code).frame) := ⟨⟩

theorem deliver_active (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (w : World) (tin final : EffTy) (m : RState) (f : RFiber) (token : Nat) (code : RProgram)
    (rest : List RCmd) (_found : m.fiber? f.id = some f) (_parked : f.parked = .withGuard token)
    (_declared : w.Θ f.id token = some tin) (_typed : ResumeOk (TypedProg root) w f.id token code)
    (_hstack : StackAccepts (TypedProg root) ExitOk hooks w tin final f.frame.stack)
    (_hp : InterruptProvenance f.frame) : ProofGraph.Obligation
    ((letI := termEvaluatorFor root.program
      driveStep interp m (.resume f.id token code) rest) =
        ((m.update (resumed f token code)).emit [.resumedWith f.id token code], .evaluate f.id :: rest) ∧
      SavedOk (TypedProg root) ExitOk hooks w final (resumed f token code).frame) := ⟨⟩

theorem deliver_stale (root : ProgramSource) (interp : RInterp) (m : RState) (f : RFiber)
    (parkedToken token : Nat) (code : RProgram) (rest : List RCmd)
    (_found : m.fiber? f.id = some f) (_parked : f.parked = .withGuard parkedToken)
    (_stale : parkedToken ≠ token) : ProofGraph.Obligation
    ((letI := termEvaluatorFor root.program
      driveStep interp m (.resume f.id token code) rest) = (m, rest)) := ⟨⟩

end M4Stack

namespace M5Hooks
theorem hookLaws_interpR (root : ProgramSource) :
    ProofGraph.Obligation (HookLaws root (interpR root.program) (frameProtocols root)) := ⟨⟩
end M5Hooks

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M4Stack.popR_typed := @Effect4.Program.Typed.popR_typed
#obligation_proved Effect4.Program.Typed.M4Stack.saveAnswerR_typed :=
  @Effect4.Program.Typed.saveAnswerR_typed
#obligation_proved Effect4.Program.Typed.M4Stack.deliver_active := @Effect4.Program.Typed.deliver_active
#obligation_proved Effect4.Program.Typed.M4Stack.deliver_stale := @Effect4.Program.Typed.deliver_stale
#obligation_proved Effect4.Program.Typed.M5Hooks.hookLaws_interpR :=
  @Effect4.Program.Typed.hookLaws_interpR
#typed_state_obligations Effect4.Program.Typed.M4Stack ceiling 0
  using aesop (rule_sets := [Effect4.TypedState])
#typed_state_obligations Effect4.Program.Typed.M5Hooks ceiling 0
  using aesop (rule_sets := [Effect4.TypedState])

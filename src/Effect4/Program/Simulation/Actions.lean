import Effect4.Program.Simulation.Deliver

/-!
# The shared fiber actions (P3, step 4d)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). The frame's
`withFiber` arms and the two parks the alphabet spells are the shared `FiberAction` helpers
under the frame's own answer (`Test/Program/RuntimeRContract.lean` states the identities by
`rfl`); the term evaluator calls the same helpers with its continuation as the answer. This
module proves each helper, and the machine operations they compose (`spawn`, `start`,
`countdownPark`, `beginRace`, `registerRace`, `linkScope`, `interruptRecord`,
`forkFinalizers`), on related inputs at the two instances.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## Answers and the saved answer slot -/

abbrev FAnswer := FiberAction.Answer EffName EffThunk Val Err Defect FiberId Ann Ctx NCode FFiber
abbrev RAnswer := FiberAction.Answer EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram RSaved

/-- Two answer functions install related value answers on related fibers. -/
def AnswerRel (root : NativeEff) (a₁ : FAnswer) (a₂ : RAnswer) : Prop :=
  ∀ (f₁ : FRun) (f₂ : RFiber) (v : Val), FMeans root f₁ f₂ → FMeans root (a₁ f₁ v) (a₂ f₂ v)

/-- The frame's own answer against a continuation related on every value. -/
theorem answerRel_core (root : NativeEff) {k : Val → RProgram}
    (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
    AnswerRel root FiberAction.coreAnswer (answerWith k) :=
  fun _ _ v h => h.answer (hk v)

/-- The term saves a delivering continuation as an answer slot the frame does not have. -/
theorem FMeans.saveAnswer {root : NativeEff} {f₁ : FRun} {f₂ : RFiber} (h : FMeans root f₁ f₂)
    {k : ExitV → RProgram} (hk : Delivers k) : FMeans root f₁ (saveAnswerR f₂ k) :=
  FMeans.mk' h.id h.parked h.context h.running h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher
    ⟨h.interruptible, h.interruptedCause, h.deferred, h.current, StackMeans.answer k hk h.stack,
      h.maskInv⟩

/-! ## The interpreters, beyond the code hooks -/

/-- What the shared machine operations read off the two interpreters. -/
structure InterpAgree (i₁ : FInterp) (i₂ : RInterp) : Prop where
  encodeFiber : i₁.encodeFiber = i₂.encodeFiber
  stackAnnotations : i₁.stackAnnotations = i₂.stackAnnotations
  scopeStatus : i₁.scopeStatus = i₂.scopeStatus
  scopeLinkFiber : i₁.scopeLinkFiber = i₂.scopeLinkFiber
  linkOk : ∀ mode scope fiber s s' key, StoresOk s →
    i₁.scopeLinkFiber mode scope fiber s = some (s', key) → StoresOk s'

/-- Registration keeps the loop's store invariant: the deferred half is untouched, and the
registration-key bound survives because the allocated key is the supply's own value
(`Machine.scopeLinkFiber_keysFresh`, `E4-CHECK-CE-016`). -/
theorem scopeLinkFiber_ok (root : NativeEff) (mode : Supervision.ScopeMode) (scope : Nat)
    (fiber : FiberId) (s s' : Stores) (key : Nat) (hs : StoresOk s)
    (h : (interpOf root).scopeLinkFiber mode scope fiber s = some (s', key)) : StoresOk s' := by
  have hstores : stores.scopeLinkFiber mode scope fiber s = some (s', key) := h
  refine ⟨?_, scopeLinkFiber_keysFresh mode scope fiber hs.2 hstores⟩
  dsimp only [interpOf] at h
  cases hentry : s.scopes.entryAt scope with
  | none => rw [hentry] at h; cases h
  | some entry =>
    rw [hentry] at h
    dsimp only at h
    unfold DeferredOk
    rw [← (Prod.mk.inj (Option.some.inj h)).1]
    exact hs.1

theorem interpAgree_at (root : NativeEff) (c c' : List (FiberId × ExitV)) :
    InterpAgree (interpAt root c) (interpRAt root c') :=
  ⟨rfl, rfl, rfl, rfl, fun mode scope fiber s s' key hs h =>
    scopeLinkFiber_ok root mode scope fiber s s' key hs h⟩

theorem interpAgree_of (root : NativeEff) : InterpAgree (interpOf root) (interpR root) :=
  ⟨rfl, rfl, rfl, rfl, fun mode scope fiber s s' key hs h =>
    scopeLinkFiber_ok root mode scope fiber s s' key hs h⟩

/-! ## Recording an interrupt -/

/-- The cause `interruptUnsafe` records, accumulated over the one already pending. -/
def accumulatedCause {κ φ : Type} [core : FiberCore EffName Val Err Defect FiberId Ann κ φ]
    (i : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores κ) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx κ φ) :
    CauseV :=
  let cause : CauseV :=
    Cause.annotate (Supervision.interruptCause i.encodeFiber who (i.stackAnnotations f.id)) extra false
  match core.interruptedCause f.frame with
  | none => cause
  | some previous => Cause.combine previous cause

theorem interruptRecord_frame_eq (i : FInterp) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (f : FRun) :
    interruptRecord i who extra f =
      if f.exit.isSome then (f, false)
      else if f.frame.interruptible then
        if f.running then
          ({ f with frame := { f.frame with
              interruptedCause := some (accumulatedCause i who extra f), deferredInterrupt := true } },
            false)
        else
          ({ f with
              parked := .notParked
              pending := []
              frame := { f.frame with
                interruptedCause := some (accumulatedCause i who extra f)
                current := Prim.failure (accumulatedCause i who extra f) } }, true)
      else ({ f with frame := { f.frame with interruptedCause := some (accumulatedCause i who extra f) } },
        false) := by
  unfold interruptRecord accumulatedCause
  dsimp only [FiberCore.interruptible, FiberCore.recordCause, FiberCore.setDeferred,
    FiberCore.answerWith, FiberCore.failure, FiberCore.interruptedCause, frameCore]
  cases f.frame.interruptedCause <;> rfl

theorem interruptRecord_term_eq (i : RInterp) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (f : RFiber) :
    interruptRecord i who extra f =
      if f.exit.isSome then (f, false)
      else if f.frame.interruptible then
        if f.running then
          ({ f with frame := { f.frame with
              interruptedCause := some (accumulatedCause i who extra f), deferredInterrupt := true } },
            false)
        else
          ({ f with
              parked := .notParked
              pending := []
              frame := { f.frame with
                interruptedCause := some (accumulatedCause i who extra f)
                current := .pure (.failure (accumulatedCause i who extra f)) } }, true)
      else ({ f with frame := { f.frame with interruptedCause := some (accumulatedCause i who extra f) } },
        false) := by
  unfold interruptRecord accumulatedCause
  dsimp only [FiberCore.interruptible, FiberCore.recordCause, FiberCore.setDeferred,
    FiberCore.answerWith, FiberCore.failure, FiberCore.interruptedCause, termCore]
  cases f.frame.interruptedCause <;> rfl

/-- `interruptUnsafe` on related fibers: related fibers, the same verdict. -/
theorem interruptRecord_rel (root : NativeEff) {i₁ : FInterp} {i₂ : RInterp} (hi : InterpAgree i₁ i₂)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) {t₁ : FRun} {t₂ : RFiber}
    (ht : FMeans root t₁ t₂) :
    FMeans root (interruptRecord i₁ who extra t₁).1 (interruptRecord i₂ who extra t₂).1 ∧
      (interruptRecord i₁ who extra t₁).2 = (interruptRecord i₂ who extra t₂).2 := by
  rw [interruptRecord_frame_eq, interruptRecord_term_eq]
  have hacc : accumulatedCause i₁ who extra t₁ = accumulatedCause i₂ who extra t₂ := by
    dsimp only [accumulatedCause, FiberCore.interruptedCause, frameCore, termCore]
    rw [ht.interruptedCause, ht.id, hi.encodeFiber, hi.stackAnnotations]
  rw [hacc]
  generalize accumulatedCause i₂ who extra t₂ = acc
  by_cases hex : t₁.exit.isSome = true
  · have hex₂ : t₂.exit.isSome = true := by rw [← ht.exit]; exact hex
    rw [if_pos hex, if_pos hex₂]
    exact ⟨ht, rfl⟩
  · have hex₂ : ¬ t₂.exit.isSome = true := by rw [← ht.exit]; exact hex
    rw [if_neg hex, if_neg hex₂]
    by_cases hint : t₁.frame.interruptible = true
    · have hint₂ : t₂.frame.interruptible = true := by rw [← ht.interruptible]; exact hint
      rw [if_pos hint, if_pos hint₂]
      by_cases hrun : t₁.running = true
      · have hrun₂ : t₂.running = true := by rw [← ht.running]; exact hrun
        rw [if_pos hrun, if_pos hrun₂]
        exact ⟨ht.withFrame ⟨ht.interruptible, rfl, rfl, ht.current, ht.stack, ht.maskInv⟩, rfl⟩
      · have hrun₂ : ¬ t₂.running = true := by rw [← ht.running]; exact hrun
        rw [if_neg hrun, if_neg hrun₂]
        exact ⟨FMeans.mk' ht.id rfl ht.context ht.running rfl ht.finalizing ht.exit ht.opCount
          ht.maxOps ht.preventYield ht.yieldOverride ht.observers ht.children ht.dispatcher
          ⟨ht.interruptible, rfl, ht.deferred, CodeMeans.failure acc, ht.stack, ht.maskInv⟩, rfl⟩
    · have hint₂ : ¬ t₂.frame.interruptible = true := by rw [← ht.interruptible]; exact hint
      rw [if_neg hint, if_neg hint₂]
      exact ⟨ht.withFrame ⟨ht.interruptible, rfl, ht.deferred, ht.current, ht.stack, ht.maskInv⟩, rfl⟩

/-- The book's hook obligation, discharged at the two instances. -/
theorem hooksAgree_of (root : NativeEff) :
    HooksAgree (interpOf root) (interpR root) (CodeMeans root) (Means root) :=
  ⟨answerCode_means root, fun t₁ t₂ who extra ht =>
    interruptRecord_rel root (interpAgree_of root) who extra ht⟩

/-! ## The machine operations the actions compose -/

/-- A result carrying a machine, a fiber and a list. -/
def TripleRel (root : NativeEff) {γ₁ γ₂ : Type} (R : γ₁ → γ₂ → Prop)
    (r₁ : FMachine × FRun × γ₁) (r₂ : RState × RFiber × γ₂) : Prop :=
  MachineOk StoresOk r₁.1 ∧ BMeans root r₁.1 r₂.1 ∧ FMeans root r₁.2.1 r₂.2.1 ∧ R r₁.2.2 r₂.2.2

/-- A result carrying a machine and the commands it leaves. -/
def CmdsRel (root : NativeEff) (r₁ : FMachine × List FCmd) (r₂ : RState × List RCmd) : Prop :=
  MachineOk StoresOk r₁.1 ∧ BMeans root r₁.1 r₂.1 ∧ ListRel (CMeans root) r₁.2 r₂.2

theorem listRel_evaluate (root : NativeEff) :
    ∀ l : List FiberId, ListRel (CMeans root) (l.map Cmd.evaluate) (l.map Cmd.evaluate)
  | [] => ListRel.nil
  | _ :: rest => ListRel.cons rfl (listRel_evaluate root rest)

theorem spawn_rel (root : NativeEff) {i₁ : FInterp} {i₂ : RInterp} (hb : i₁.budgetOf = i₂.budgetOf)
    {m₁ : FMachine} {m₂ : RState}
    (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {p₁ : FRun} {p₂ : RFiber}
    (hp : FMeans root p₁ p₂) {prog₁ : NCode} {prog₂ : RProgram} (hprog : CodeMeans root prog₁ prog₂)
    (options : Supervision.ForkOptions) :
    TripleRel root Eq (spawn i₁ m₁ p₁ prog₁ options) (spawn i₂ m₂ p₂ prog₂ options) := by
  unfold spawn
  dsimp only [FiberCore.interruptible, frameCore, termCore]
  rw [hm.nextId, hp.context, hb]
  cases options.maskMode with
  | interruptible =>
    exact ⟨machineOk_emit (machineOk_appendFiber hok (pendingOk_make _ _ _ _ _) _) _,
      BMeans.emit (hm.appendFiber (fmeans_make root _ hprog _ _ _) _) _ _, hp, rfl⟩
  | uninterruptible =>
    exact ⟨machineOk_emit (machineOk_appendFiber hok (pendingOk_make _ _ _ _ _) _) _,
      BMeans.emit (hm.appendFiber (fmeans_make root _ hprog _ _ _) _) _ _, hp, rfl⟩
  | inherit =>
    dsimp only
    rw [hp.interruptible]
    exact ⟨machineOk_emit (machineOk_appendFiber hok (pendingOk_make _ _ _ _ _) _) _,
      BMeans.emit (hm.appendFiber (fmeans_make root _ hprog _ _ _) _) _ _, hp, rfl⟩

theorem start_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState} (hok : MachineOk StoresOk m₁)
    (hm : BMeans root m₁ m₂) {p₁ : FRun} {p₂ : RFiber} (hp : FMeans root p₁ p₂) (child : FiberId)
    (imm : Bool) :
    TripleRel root (ListRel (CMeans root)) (start m₁ p₁ child imm) (start m₂ p₂ child imm) := by
  cases imm with
  | true => exact ⟨hok, hm, hp, ListRel.cons rfl ListRel.nil⟩
  | false =>
    refine ⟨machineOk_emit (machineOk_arm hok _) _, ?_, hp.enqueue 0 (taskMeans_start child),
      ListRel.nil⟩
    show BMeans root ((m₁.arm p₁.id).emit _) ((m₂.arm p₂.id).emit _)
    rw [hp.id]
    exact BMeans.emit (hm.arm _) _ _

theorem forkFinalizers_rel (root : NativeEff) (c : List (FiberId × ExitV)) :
    ∀ {l₁ : List NCode} {l₂ : List RProgram}, ListRel (CodeMeans root) l₁ l₂ →
    ∀ {m₁ : FMachine} {m₂ : RState}, MachineOk StoresOk m₁ → BMeans root m₁ m₂ →
    ∀ {h₁ : FRun} {h₂ : RFiber}, FMeans root h₁ h₂ →
      MachineOk StoresOk (forkFinalizers (interpAt root c) m₁ h₁ l₁).1 ∧
        BMeans root (forkFinalizers (interpAt root c) m₁ h₁ l₁).1
          (forkFinalizers (interpRAt root c) m₂ h₂ l₂).1 ∧
        (forkFinalizers (interpAt root c) m₁ h₁ l₁).2 = (forkFinalizers (interpRAt root c) m₂ h₂ l₂).2 := by
  intro l₁ l₂ hl
  induction hl with
  | nil => intro m₁ m₂ hok hm h₁ h₂ _; exact ⟨hok, hm, rfl⟩
  | @cons p₁ p₂ l₁ l₂ hp _ ih =>
    intro m₁ m₂ hok hm h₁ h₂ hh
    have hs := spawn_rel root (i₁ := interpAt root c) (i₂ := interpRAt root c) rfl hok hm hh hp ⟨true, true, Supervision.MaskMode.inherit⟩
    unfold forkFinalizers
    generalize spawn (interpAt root c) m₁ h₁ p₁ ⟨true, true, Supervision.MaskMode.inherit⟩ = s₁ at hs ⊢
    generalize spawn (interpRAt root c) m₂ h₂ p₂ ⟨true, true, Supervision.MaskMode.inherit⟩ = s₂ at hs ⊢
    obtain ⟨sm₁, sf₁, ch₁⟩ := s₁
    obtain ⟨sm₂, sf₂, ch₂⟩ := s₂
    obtain ⟨hok', hm', _, hch⟩ := hs
    dsimp only at hok' hm' hch
    subst hch
    dsimp only
    have := ih hok' hm' hh
    generalize forkFinalizers (interpAt root c) sm₁ h₁ l₁ = r₁ at this ⊢
    generalize forkFinalizers (interpRAt root c) sm₂ h₂ l₂ = r₂ at this ⊢
    obtain ⟨rm₁, rc₁⟩ := r₁
    obtain ⟨rm₂, rc₂⟩ := r₂
    obtain ⟨hok'', hm'', hc⟩ := this
    dsimp only at hok'' hm'' hc
    subst hc
    exact ⟨hok'', hm'', rfl⟩

theorem countdownWalk_eq {root : NativeEff} {m₁ : FMachine} {m₂ : RState} (hm : BMeans root m₁ m₂) :
    ∀ (ts : List FiberId) (exits : List ExitV), countdownWalk m₁ ts exits = countdownWalk m₂ ts exits
  | [], _ => rfl
  | t :: rest, exits => by
    unfold countdownWalk
    rcases hm.fiber?_cases t with ⟨h₁, h₂⟩ | ⟨g₁, g₂, h₁, h₂, hg⟩
    · rw [h₁, h₂]
      exact countdownWalk_eq hm rest exits
    · rw [h₁, h₂]
      dsimp only
      rw [hg.exit]
      cases g₂.exit with
      | some ex => exact countdownWalk_eq hm rest _
      | none => rfl

theorem countdownPark_rel (root : NativeEff) (c : List (FiberId × ExitV)) {m₁ : FMachine} {m₂ : RState}
    (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
    (hf : FMeans root f₁ f₂) (targets : List FiberId) (resume : Resume EffName)
    (hres : ∀ name, resume ≠ Resume.continueWith name) (failFast : Bool) :
    TripleRel root Eq (countdownPark (interpAt root c) m₁ f₁ targets resume failFast)
      (countdownPark (interpRAt root c) m₂ f₂ targets resume failFast) := by
  unfold countdownPark
  dsimp only
  rw [hm.nextToken, countdownWalk_eq (hm.withNextToken (m₂.nextToken + 1)) targets []]
  cases countdownWalk { m₂ with nextToken := m₂.nextToken + 1 } targets [] with
  | mk exits opt =>
    cases opt with
    | none =>
      dsimp only [TripleRel]
      refine ⟨machineOk_withNextToken hok _, hm.withNextToken _,
        hf.withFrame (means_answerWith hf.means ?_), rfl⟩
      cases resume with
      | exitsValue => exact CodeMeans.success _
      | void => exact CodeMeans.success _
      | continueWith name => exact absurd rfl (hres name)
    | some tr =>
      obtain ⟨target, remaining⟩ := tr
      dsimp only [TripleRel]
      refine ⟨machineOk_emit (machineOk_modify (machineOk_withNextToken hok _) target ?_) _,
        BMeans.emit ((hm.withNextToken _).modify target (fun g₁ g₂ hg => ?_)) _ _,
        (hf.withFrame ?_).park _, rfl⟩
      · exact fun _ hg => pendingOk_of_fields hg rfl
      · rw [← hg.observers, hf.id]
        exact hg.withObservers _
      · rw [hf.id]
        exact means_pushAsyncFinalizer hf.means _

theorem beginRace_rel (root : NativeEff) (c : List (FiberId × ExitV)) {m₁ : FMachine} {m₂ : RState}
    (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
    (hf : FMeans root f₁ f₂) (y : Bool) {e₁ : List NCode} {e₂ : List RProgram}
    (he : ListRel (CodeMeans root) e₁ e₂) :
    IterRel root (beginRace (interpAt root c) m₁ f₁ y e₁) (beginRace (interpRAt root c) m₂ f₂ y e₂) := by
  unfold beginRace
  dsimp only
  rw [hm.nextRace, hm.nextToken, ListRel.length he]
  exact ⟨machineOk_emit (machineOk_appendRace hok _ _ _) _,
    BMeans.emit (hm.appendRace (raceMeans_mk' rfl hf.id rfl rfl rfl rfl he) _ _) _ _,
    hf.withFrame (means_answerWith hf.means (parkCode_means root _)), rfl, rfl, ListRel.nil⟩

theorem registerRace_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState} (hok : MachineOk StoresOk m₁)
    (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber} (hf : FMeans root f₁ f₂) (y : Bool)
    (raceId : Nat) :
    IterRel root (registerRace m₁ f₁ y raceId) (registerRace m₂ f₂ y raceId) := by
  unfold registerRace
  rcases hm.race?_cases raceId with ⟨h₁, h₂⟩ | ⟨r₁, r₂, h₁, h₂, hr⟩
  · rw [h₁, h₂]
    exact ⟨hok, hm, hf, rfl, rfl, ListRel.nil⟩
  · rw [h₁, h₂]
    exact ⟨machineOk_updateRace hok _,
      hm.updateRace ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, rfl, hr.2.2.2.2.2.2⟩,
      hf, rfl, rfl, ListRel.cons rfl (ListRel.cons ⟨rfl, rfl⟩ ListRel.nil)⟩

theorem linkScope_rel (root : NativeEff) {i₁ : FInterp} {i₂ : RInterp} (hi : InterpAgree i₁ i₂)
    {m₁ : FMachine} {m₂ : RState} (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId) (interruptor : Option FiberId)
    (extra : ReasonAnnotations Ann) :
    CmdsRel root (linkScope i₁ m₁ mode scope target interruptor extra)
      (linkScope i₂ m₂ mode scope target interruptor extra) := by
  unfold linkScope
  rw [hi.scopeStatus, hm.state]
  cases i₂.scopeStatus scope m₂.state with
  | none => exact ⟨machineOk_halt hok _, hm.halt _, ListRel.nil⟩
  | some status =>
    cases status with
    | some closingExit =>
      rcases hm.fiber?_cases target with ⟨h₁, h₂⟩ | ⟨t₁, t₂, h₁, h₂, ht⟩
      · rw [h₁, h₂]
        exact ⟨machineOk_halt hok _, hm.halt _, ListRel.nil⟩
      · rw [h₁, h₂]
        dsimp only
        have hrec := interruptRecord_rel root hi interruptor extra ht
        have hpend := interruptRecord_pendingOk i₁ interruptor extra (pendingOk_of_fiber? hok h₁)
        generalize interruptRecord i₁ interruptor extra t₁ = r₁ at hrec hpend ⊢
        generalize interruptRecord i₂ interruptor extra t₂ = r₂ at hrec ⊢
        obtain ⟨t₁', a₁⟩ := r₁
        obtain ⟨t₂', a₂⟩ := r₂
        obtain ⟨hrel, ha⟩ := hrec
        dsimp only at hrel ha hpend
        subst ha
        refine ⟨machineOk_emit (machineOk_update hok hpend) _, BMeans.emit (hm.update hrel) _ _, ?_⟩
        cases a₁
        · exact ListRel.nil
        · exact ListRel.cons rfl ListRel.nil
    | none =>
      rcases hm.fiber?_cases target with ⟨h₁, h₂⟩ | ⟨t₁, t₂, h₁, h₂, ht⟩
      · rw [h₁, h₂]
        exact ⟨machineOk_halt hok _, hm.halt _, ListRel.nil⟩
      · rw [h₁, h₂]
        dsimp only
        rw [ht.exit]
        cases t₂.exit.isSome with
        | true => exact ⟨hok, hm, ListRel.nil⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hi.scopeLinkFiber]
          cases hlink : i₂.scopeLinkFiber mode scope target m₂.state with
          | none => exact ⟨machineOk_halt hok _, hm.halt _, ListRel.nil⟩
          | some res =>
            obtain ⟨state, key⟩ := res
            have hs : StoresOk state :=
              hi.linkOk mode scope target m₂.state state key (hm.state ▸ hok.state)
                (by rw [hi.scopeLinkFiber]; exact hlink)
            dsimp only [CmdsRel]
            refine ⟨machineOk_emit (machineOk_modify (machineOk_stateOf hok hs) target ?_) _,
              BMeans.emit ((hm.stateOf state).modify target (fun g₁ g₂ hg => ?_)) _ _, ListRel.nil⟩
            · exact fun _ hg => pendingOk_of_fields hg rfl
            · rw [← hg.observers]
              exact hg.withObservers _

/-! ## The fiber actions on related fibers -/

theorem outcomeOf_eq {root : NativeEff} {m₁ : FMachine} {m₂ : RState} (hm : BMeans root m₁ m₂)
    (parked : Bool) : FiberAction.outcomeOf m₁ parked = FiberAction.outcomeOf m₂ parked := by
  unfold FiberAction.outcomeOf
  rw [hm.stuck]

theorem BMeans.armOf {root : NativeEff} {m₁ : FMachine} {m₂ : RState} (h : BMeans root m₁ m₂)
    {o₁ o₂ : FiberId} (ho : o₁ = o₂) : BMeans root (m₁.arm o₁) (m₂.arm o₂) :=
  ho ▸ h.arm o₁

theorem taskMeans_resume' {root : NativeEff} {id₁ id₂ : FiberId} (hid : id₁ = id₂) (token : Nat)
    {c₁ : NCode} {c₂ : RProgram} (hc : CodeMeans root c₁ c₂) :
    TaskMeans (CodeMeans root) (Task.resume id₁ token c₁ : FTask) (Task.resume id₂ token c₂ : RTask) :=
  hid ▸ taskMeans_resume id₁ token hc

theorem FMeans.answerEnqueue {root : NativeEff} {f₁ : FRun} {f₂ : RFiber} (h : FMeans root f₁ f₂)
    {c₁ : NCode} {c₂ : RProgram} (hc : CodeMeans root c₁ c₂) (priority : Nat) {t₁ : FTask} {t₂ : RTask}
    (ht : TaskMeans (CodeMeans root) t₁ t₂) :
    FMeans root
      { f₁ with frame := { f₁.frame with current := c₁ }, dispatcher := f₁.dispatcher.enqueue priority t₁ }
      { f₂ with frame := { f₂.frame with current := c₂ }, dispatcher := f₂.dispatcher.enqueue priority t₂ } :=
  FMeans.mk' h.id h.parked h.context h.running h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children
    (dispatcherMeans_enqueue h.dispatcher priority ht) (means_answerWith h.means hc)

/-- A value answered through related answer functions. -/
theorem iterRel_answer {root : NativeEff} {m₁ : FMachine} {m₂ : RState} (hok : MachineOk StoresOk m₁)
    (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber} (hf : FMeans root f₁ f₂) {a₁ : FAnswer}
    {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) (v : Val) (y : Bool)
    (o : Outcome EffName EffThunk Val Err Defect FiberId Ann) :
    IterRel root ⟨m₁, a₁ f₁ v, y, o, []⟩ ⟨m₂, a₂ f₂ v, y, o, []⟩ :=
  ⟨hok, hm, ha _ _ _ hf, rfl, rfl, ListRel.nil⟩

theorem storesOk_closeScope {root : NativeEff} {c : List (FiberId × ExitV)} {scope : Nat} {ex : ExitV}
    {flag : Bool} {id : FiberId} {s s' : Stores} {p : NCode} (hs : StoresOk s)
    (h : (interpAt root c).closeScope scope ex flag id s = some (s', p)) : StoresOk s' := by
  have h' : ((storesCloseScope scope ex flag s).map fun r => (r.1, embed r.2)) = some (s', p) := h
  unfold storesCloseScope at h'
  cases hu : storesCloseScopeUnsafe scope ex flag s with
  | none => rw [hu] at h'; cases h'
  | some r =>
    obtain ⟨st, prog⟩ := r
    rw [hu] at h'
    have hst : st = s' := (Prod.mk.inj (Option.some.inj h')).1
    exact hst ▸ storesOk_closeScopeUnsafe hs hu

theorem ambientScope_eq (root : NativeEff) (c : List (FiberId × ExitV)) {f₁ : FRun} {f₂ : RFiber}
    (hf : FMeans root f₁ f₂) :
    (interpAt root c).ambientScope f₁.context = (interpRAt root c).ambientScope f₂.context := by
  show Ctx.ambientScope f₁.context = Ctx.ambientScope f₂.context
  rw [hf.context]

section Actions

variable (root : NativeEff) (c : List (FiberId × ExitV)) {m₁ : FMachine} {m₂ : RState}
  (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
  (hf : FMeans root f₁ f₂) (y : Bool)

include hok hm hf

theorem getId_rel {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.getId (interpAt root c) m₁ f₁ y a₁)
      (FiberAction.getId (interpRAt root c) m₂ f₂ y a₂) := by
  unfold FiberAction.getId
  rw [hf.id]
  exact iterRel_answer hok hm hf ha _ y _

theorem getContext_rel {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.getContext (interpAt root c) m₁ f₁ y a₁)
      (FiberAction.getContext (interpRAt root c) m₂ f₂ y a₂) := by
  unfold FiberAction.getContext
  rw [hf.context]
  exact iterRel_answer hok hm hf ha _ y _

theorem setContext_rel (context : Ctx) {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.setContext (interpAt root c) m₁ f₁ y context a₁)
      (FiberAction.setContext (interpRAt root c) m₂ f₂ y context a₂) := by
  unfold FiberAction.setContext
  exact ⟨machineOk_emit hok _, BMeans.emit hm _ _, ha _ _ _ (hf.withContext context _ _), rfl, rfl,
    ListRel.nil⟩

theorem snapshotChildren_rel {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.snapshotChildren (interpAt root c) m₁ f₁ y a₁)
      (FiberAction.snapshotChildren (interpRAt root c) m₂ f₂ y a₂) := by
  unfold FiberAction.snapshotChildren
  rw [hf.children]
  exact iterRel_answer hok hm hf ha _ y _

theorem dropObservers_rel (token : Nat) {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.dropObservers (interpAt root c) m₁ f₁ y token a₁)
      (FiberAction.dropObservers (interpRAt root c) m₂ f₂ y token a₂) := by
  unfold FiberAction.dropObservers
  dsimp only
  refine ⟨machineOk_mapFibers hok ?_, hm.mapFibers ?_, ha _ _ _ hf, rfl, rfl, ListRel.nil⟩
  · exact fun _ hg => pendingOk_of_fields hg rfl
  · intro g₁ g₂ hg
    rw [← hg.observers]
    exact hg.withObservers _

theorem runIn_rel (target : FiberId) (scope : Nat) {a₁ : FAnswer} {a₂ : RAnswer}
    (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.runIn (interpAt root c) m₁ f₁ y target scope a₁)
      (FiberAction.runIn (interpRAt root c) m₂ f₂ y target scope a₂) := by
  unfold FiberAction.runIn
  have hl := linkScope_rel root (interpAgree_at root c c) hok hm Supervision.ScopeMode.fiberRunIn scope
    target (some target) ReasonAnnotations.empty
  generalize linkScope (interpAt root c) m₁ Supervision.ScopeMode.fiberRunIn scope target (some target)
    ReasonAnnotations.empty = r₁ at hl ⊢
  generalize linkScope (interpRAt root c) m₂ Supervision.ScopeMode.fiberRunIn scope target (some target)
    ReasonAnnotations.empty = r₂ at hl ⊢
  obtain ⟨n₁, cs₁⟩ := r₁
  obtain ⟨n₂, cs₂⟩ := r₂
  obtain ⟨hok', hm', hcs⟩ := hl
  dsimp only at hok' hm' hcs
  exact ⟨hok', hm', ha _ _ _ hf, rfl, outcomeOf_eq hm' false, hcs⟩

theorem fork_rel {p₁ : NCode} {p₂ : RProgram} (hp : CodeMeans root p₁ p₂)
    (options : Supervision.ForkOptions) {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.fork (interpAt root c) m₁ f₁ y p₁ options a₁)
      (FiberAction.fork (interpRAt root c) m₂ f₂ y p₂ options a₂) := by
  unfold FiberAction.fork
  cases hd : options.daemon with
  | true =>
    simp only [↓reduceIte, List.append_nil]
    have hs := spawn_rel root (i₁ := interpAt root c) (i₂ := interpRAt root c) rfl hok hm hf hp options
    generalize spawn (interpAt root c) m₁ f₁ p₁ options = s₁ at hs ⊢
    generalize spawn (interpRAt root c) m₂ f₂ p₂ options = s₂ at hs ⊢
    obtain ⟨sm₁, sf₁, ch₁⟩ := s₁
    obtain ⟨sm₂, sf₂, ch₂⟩ := s₂
    obtain ⟨hok', hm', hf', hch⟩ := hs
    dsimp only at hok' hm' hf' hch
    subst hch
    dsimp only
    have hst := start_rel root hok' hm' hf' ch₁ options.startImmediately
    generalize start sm₁ sf₁ ch₁ options.startImmediately = t₁ at hst ⊢
    generalize start sm₂ sf₂ ch₁ options.startImmediately = t₂ at hst ⊢
    obtain ⟨tm₁, tf₁, tn₁⟩ := t₁
    obtain ⟨tm₂, tf₂, tn₂⟩ := t₂
    obtain ⟨hok'', hm'', hf'', hn⟩ := hst
    dsimp only at hok'' hm'' hf'' hn
    exact ⟨hok'', hm'', ha _ _ _ hf'', rfl, rfl, hn⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hs := spawn_rel root (i₁ := interpAt root c) (i₂ := interpRAt root c) rfl
      (machineOk_middleware hok) hm.middlewareOn hf hp options
    generalize spawn (interpAt root c) { m₁ with middlewareInstalled := true } f₁ p₁ options = s₁ at hs ⊢
    generalize spawn (interpRAt root c) { m₂ with middlewareInstalled := true } f₂ p₂ options = s₂ at hs ⊢
    obtain ⟨sm₁, sf₁, ch₁⟩ := s₁
    obtain ⟨sm₂, sf₂, ch₂⟩ := s₂
    obtain ⟨hok', hm', hf', hch⟩ := hs
    dsimp only at hok' hm' hf' hch
    subst hch
    dsimp only
    have hst := start_rel root hok' hm' hf' ch₁ options.startImmediately
    generalize start sm₁ sf₁ ch₁ options.startImmediately = t₁ at hst ⊢
    generalize start sm₂ sf₂ ch₁ options.startImmediately = t₂ at hst ⊢
    obtain ⟨tm₁, tf₁, tn₁⟩ := t₁
    obtain ⟨tm₂, tf₂, tn₂⟩ := t₂
    obtain ⟨hok'', hm'', hf'', hn⟩ := hst
    dsimp only at hok'' hm'' hf'' hn
    exact ⟨hok'', hm'', ha _ _ _ hf'', rfl, rfl,
      ListRel.append hn (ListRel.cons ⟨hf.id, rfl⟩ ListRel.nil)⟩

theorem forkIn_rel {p₁ : NCode} {p₂ : RProgram} (hp : CodeMeans root p₁ p₂)
    (options : Supervision.ForkOptions) (scope : Nat) {a₁ : FAnswer} {a₂ : RAnswer}
    (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.forkIn (interpAt root c) m₁ f₁ y p₁ options scope a₁)
      (FiberAction.forkIn (interpRAt root c) m₂ f₂ y p₂ options scope a₂) := by
  unfold FiberAction.forkIn
  have hs := spawn_rel root (i₁ := interpAt root c) (i₂ := interpRAt root c) rfl hok hm hf hp { options with daemon := true }
  generalize spawn (interpAt root c) m₁ f₁ p₁ { options with daemon := true } = s₁ at hs ⊢
  generalize spawn (interpRAt root c) m₂ f₂ p₂ { options with daemon := true } = s₂ at hs ⊢
  obtain ⟨sm₁, sf₁, ch₁⟩ := s₁
  obtain ⟨sm₂, sf₂, ch₂⟩ := s₂
  obtain ⟨hok', hm', hf', hch⟩ := hs
  dsimp only at hok' hm' hf' hch
  subst hch
  dsimp only
  have hst := start_rel root hok' hm' hf' ch₁ options.startImmediately
  generalize start sm₁ sf₁ ch₁ options.startImmediately = t₁ at hst ⊢
  generalize start sm₂ sf₂ ch₁ options.startImmediately = t₂ at hst ⊢
  obtain ⟨tm₁, tf₁, tn₁⟩ := t₁
  obtain ⟨tm₂, tf₂, tn₂⟩ := t₂
  obtain ⟨hok'', hm'', hf'', hn⟩ := hst
  dsimp only at hok'' hm'' hf'' hn
  dsimp only
  refine ⟨hok'', hm'', ha _ _ _ hf'', rfl, rfl,
    ListRel.append hn (ListRel.cons ⟨rfl, rfl, rfl, congrArg some hf''.id, ?_⟩ ListRel.nil)⟩
  show stackAnnotationsOf tf₁.id = stackAnnotationsOf tf₂.id
  rw [hf''.id]

theorem ambientScope_rel {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.ambientScope (interpAt root c) m₁ f₁ y a₁)
      (FiberAction.ambientScope (interpRAt root c) m₂ f₂ y a₂) := by
  unfold FiberAction.ambientScope
  rw [ambientScope_eq root c hf]
  cases (interpRAt root c).ambientScope f₂.context with
  | some scope => exact iterRel_answer hok hm hf ha _ y _
  | none =>
    exact ⟨hok, hm, hf.withFrame (means_answerWith hf.means (CodeMeans.failure _)), rfl, rfl,
      ListRel.nil⟩

theorem closePar_rel {l₁ : List NCode} {l₂ : List RProgram} (hl : ListRel (CodeMeans root) l₁ l₂) :
    IterRel root (FiberAction.closePar (interpAt root c) m₁ f₁ y l₁)
      (FiberAction.closePar (interpRAt root c) m₂ f₂ y l₂) := by
  unfold FiberAction.closePar
  have hff := forkFinalizers_rel root c hl hok hm hf
  generalize forkFinalizers (interpAt root c) m₁ f₁ l₁ = r₁ at hff ⊢
  generalize forkFinalizers (interpRAt root c) m₂ f₂ l₂ = r₂ at hff ⊢
  obtain ⟨rm₁, ch₁⟩ := r₁
  obtain ⟨rm₂, ch₂⟩ := r₂
  obtain ⟨hok', hm', hch⟩ := hff
  dsimp only at hok' hm' hch
  subst hch
  exact ⟨hok', hm', hf, rfl, rfl,
    ListRel.append (listRel_evaluate root ch₁) (ListRel.cons ⟨hf.id, rfl, rfl⟩ ListRel.nil)⟩

theorem refuse_rel (cause : CauseV) :
    IterRel root (FiberAction.refuse m₁ f₁ y cause) (FiberAction.refuse m₂ f₂ y cause) :=
  ⟨hok, hm, hf.withFrame (means_answerWith hf.means (CodeMeans.failure cause)), rfl, rfl, ListRel.nil⟩

theorem closeScope_rel (scope : Nat) (ex : ExitV) :
    IterRel root (FiberAction.closeScope (interpAt root c) m₁ f₁ y scope ex)
      (FiberAction.closeScope (interpRAt root c) m₂ f₂ y scope ex) := by
  unfold FiberAction.closeScope
  dsimp only [FiberCore.interruptible, frameCore, termCore]
  have h : OptRel (fun (a : Stores × NCode) (b : Stores × RProgram) => a.1 = b.1 ∧ CodeMeans root a.2 b.2)
      ((interpAt root c).closeScope scope ex f₁.frame.interruptible f₁.id m₁.state)
      ((interpRAt root c).closeScope scope ex f₂.frame.interruptible f₂.id m₂.state) := by
    rw [hf.interruptible, hf.id, hm.state]
    exact closeScope_means root scope ex f₂.frame.interruptible f₂.id m₂.state
  generalize hr₁ : (interpAt root c).closeScope scope ex f₁.frame.interruptible f₁.id m₁.state = r₁ at h ⊢
  generalize (interpRAt root c).closeScope scope ex f₂.frame.interruptible f₂.id m₂.state = r₂ at h ⊢
  cases r₁ with
  | none =>
    cases r₂ with
    | none => exact ⟨hok, hm, hf, rfl, rfl, ListRel.nil⟩
    | some _ => exact h.elim
  | some p₁ =>
    cases r₂ with
    | none => exact h.elim
    | some p₂ =>
      obtain ⟨s₁, c₁⟩ := p₁
      obtain ⟨s₂, c₂⟩ := p₂
      obtain ⟨hs, hc⟩ := h
      dsimp only at hs hc
      subst hs
      exact ⟨machineOk_stateOf hok (storesOk_closeScope hok.state hr₁), hm.stateOf _,
        hf.withFrame (means_answerWith hf.means hc), rfl, rfl, ListRel.nil⟩

theorem interrupt_rel (target : FiberId) :
    IterRel root (FiberAction.interrupt (interpAt root c) m₁ f₁ y target)
      (FiberAction.interrupt (interpRAt root c) m₂ f₂ y target) := by
  unfold FiberAction.interrupt
  exact ⟨hok, hm, hf.withFrame (means_answerWith hf.means
    (by rw [hf.id]; exact interruptAsCode_means root target f₂.id)), rfl, rfl, ListRel.nil⟩

theorem interruptAs_rel (target who : FiberId) :
    IterRel root (FiberAction.interruptAs (interpAt root c) m₁ f₁ y target who)
      (FiberAction.interruptAs (interpRAt root c) m₂ f₂ y target who) := by
  unfold FiberAction.interruptAs
  rcases hm.fiber?_cases target with ⟨h₁, h₂⟩ | ⟨t₁, t₂, h₁, h₂, ht⟩
  · rw [h₁, h₂]
    exact ⟨hok, hm, hf, rfl, rfl, ListRel.nil⟩
  · rw [h₁, h₂]
    dsimp only
    have hann : (interpRAt root c).stackAnnotations = (interpAt root c).stackAnnotations := rfl
    rw [hann, hf.id]
    have hrec := interruptRecord_rel root (interpAgree_at root c c) (some who)
      ((interpAt root c).stackAnnotations f₂.id) ht
    have hpend := interruptRecord_pendingOk (interpAt root c) (some who)
      ((interpAt root c).stackAnnotations f₂.id) (pendingOk_of_fiber? hok h₁)
    generalize interruptRecord (interpAt root c) (some who) ((interpAt root c).stackAnnotations f₂.id) t₁ = r₁
      at hrec hpend ⊢
    generalize interruptRecord (interpRAt root c) (some who) ((interpAt root c).stackAnnotations f₂.id) t₂ = r₂
      at hrec ⊢
    obtain ⟨t₁', a₁⟩ := r₁
    obtain ⟨t₂', a₂⟩ := r₂
    obtain ⟨hrel, ha⟩ := hrec
    dsimp only at hrel ha hpend
    subst ha
    refine ⟨machineOk_emit (machineOk_update hok hpend) _, BMeans.emit (hm.update hrel) _ _, hf, rfl,
      rfl, ListRel.append ?_ (ListRel.cons ⟨rfl, rfl, rfl⟩ ListRel.nil)⟩
    cases a₁
    · exact ListRel.nil
    · exact ListRel.cons rfl ListRel.nil

theorem interruptScoped_rel (target : FiberId) {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.interruptScoped (interpAt root c) m₁ f₁ y target a₁)
      (FiberAction.interruptScoped (interpRAt root c) m₂ f₂ y target a₂) := by
  unfold FiberAction.interruptScoped
  by_cases h : target = f₁.id
  · have h₂ : target = f₂.id := by rw [← hf.id]; exact h
    rw [if_pos h, if_pos h₂]
    exact iterRel_answer hok hm hf ha _ y _
  · have h₂ : ¬ target = f₂.id := by rw [← hf.id]; exact h
    rw [if_neg h, if_neg h₂]
    exact ⟨hok, hm, hf.withFrame (means_answerWith hf.means (interruptCode_means root target)), rfl,
      rfl, ListRel.nil⟩

theorem interruptAll_rel (targets : List FiberId) (who : Option FiberId) :
    IterRel root (FiberAction.interruptAll (interpAt root c) m₁ f₁ y targets who)
      (FiberAction.interruptAll (interpRAt root c) m₂ f₂ y targets who) := by
  unfold FiberAction.interruptAll
  rw [hf.id]
  exact ⟨hok, hm, hf, rfl, rfl,
    ListRel.append
      (ListRel.map_rel (fun a b (h : a = b) => by subst h; exact ⟨rfl, rfl, rfl⟩)
        (ListRel.refl (fun _ => rfl) targets))
      (ListRel.cons ⟨rfl, rfl, rfl⟩ ListRel.nil)⟩

theorem awaitAll_rel (targets : List FiberId) (failFast : Bool) :
    IterRel root (FiberAction.awaitAll (interpAt root c) m₁ f₁ y targets failFast)
      (FiberAction.awaitAll (interpRAt root c) m₂ f₂ y targets failFast) := by
  unfold FiberAction.awaitAll
  have hp := countdownPark_rel root c hok hm hf targets Resume.exitsValue
    (fun _ h => nomatch h) failFast
  generalize countdownPark (interpAt root c) m₁ f₁ targets Resume.exitsValue failFast = r₁ at hp ⊢
  generalize countdownPark (interpRAt root c) m₂ f₂ targets Resume.exitsValue failFast = r₂ at hp ⊢
  obtain ⟨pm₁, pf₁, pk₁⟩ := r₁
  obtain ⟨pm₂, pf₂, pk₂⟩ := r₂
  obtain ⟨hok', hm', hf', hpk⟩ := hp
  dsimp only at hok' hm' hf' hpk
  subst hpk
  exact ⟨hok', hm', hf', rfl, outcomeOf_eq hm' pk₁, ListRel.nil⟩

theorem awaitNewChildren_rel (snapshot : List FiberId) :
    IterRel root (FiberAction.awaitNewChildren (interpAt root c) m₁ f₁ y snapshot)
      (FiberAction.awaitNewChildren (interpRAt root c) m₂ f₂ y snapshot) := by
  unfold FiberAction.awaitNewChildren
  dsimp only
  rw [hf.children]
  have hp := countdownPark_rel root c hok hm hf (f₂.children.filter fun c => !(snapshot.contains c))
    Resume.void (fun _ h => nomatch h) false
  generalize countdownPark (interpAt root c) m₁ f₁ (f₂.children.filter fun c => !(snapshot.contains c))
    Resume.void false = r₁ at hp ⊢
  generalize countdownPark (interpRAt root c) m₂ f₂ (f₂.children.filter fun c => !(snapshot.contains c))
    Resume.void false = r₂ at hp ⊢
  obtain ⟨pm₁, pf₁, pk₁⟩ := r₁
  obtain ⟨pm₂, pf₂, pk₂⟩ := r₂
  obtain ⟨hok', hm', hf', hpk⟩ := hp
  dsimp only at hok' hm' hf' hpk
  subst hpk
  exact ⟨hok', hm', hf', rfl, outcomeOf_eq hm' pk₁, ListRel.nil⟩

theorem cancelRace_rel (raceId : Nat) {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) :
    IterRel root (FiberAction.cancelRace (interpAt root c) m₁ f₁ y raceId a₁)
      (FiberAction.cancelRace (interpRAt root c) m₂ f₂ y raceId a₂) := by
  unfold FiberAction.cancelRace
  rcases hm.race?_cases raceId with ⟨h₁, h₂⟩ | ⟨r₁, r₂, h₁, h₂, hr⟩
  · rw [h₁, h₂]
    exact iterRel_answer hok hm hf ha _ y _
  · rw [h₁, h₂]
    exact ⟨hok, hm, hf, rfl, rfl,
      ListRel.cons ⟨rfl, hf.id, rfl, congrArg (fun s => s.live) (raceMeans_state hr), rfl⟩ ListRel.nil⟩

theorem raceAll_rel {e₁ : List NCode} {e₂ : List RProgram} (he : ListRel (CodeMeans root) e₁ e₂) :
    IterRel root (FiberAction.raceAll (interpAt root c) m₁ f₁ y e₁)
      (FiberAction.raceAll (interpRAt root c) m₂ f₂ y e₂) :=
  beginRace_rel root c hok hm hf y he

theorem yieldNow_rel (priority : Nat) :
    IterRel root (FiberAction.yieldNow (interpAt root c) m₁ f₁ y priority)
      (FiberAction.yieldNow (interpRAt root c) m₂ f₂ y priority) := by
  unfold FiberAction.yieldNow
  dsimp only
  rw [hm.nextToken]
  exact ⟨machineOk_emit (machineOk_arm (machineOk_withNextToken hok _) _) _,
    BMeans.emit (BMeans.armOf (hm.withNextToken _) hf.id) _ _,
    (FMeans.answerEnqueue hf (CodeMeans.success _) priority
      (taskMeans_resume' hf.id _ (CodeMeans.success _))).park _,
    rfl, rfl, ListRel.nil⟩

theorem join_rel (target : FiberId) (mode : Supervision.ObserverMode) :
    IterRel root (FiberAction.join (interpAt root c) m₁ f₁ y target mode)
      (FiberAction.join (interpRAt root c) m₂ f₂ y target mode) := by
  unfold FiberAction.join
  rcases hm.fiber?_cases target with ⟨h₁, h₂⟩ | ⟨t₁, t₂, h₁, h₂, ht⟩
  · rw [h₁, h₂]
    exact ⟨hok, hm, hf, rfl, rfl, ListRel.nil⟩
  · rw [h₁, h₂]
    dsimp only
    have hex := ht.exit
    rcases hex₁ : t₁.exit with _ | ex
    · rw [hex₁] at hex
      rw [← hex]
      dsimp only
      rw [hm.nextToken]
      refine ⟨machineOk_emit (machineOk_update (machineOk_withNextToken hok _) ?_) _,
        BMeans.emit ((hm.withNextToken _).update ?_) _ _, (hf.withFrame ?_).park _, rfl, rfl,
        ListRel.nil⟩
      · exact pendingOk_of_fields (pendingOk_of_fiber? hok h₁) rfl
      · exact FMeans.mk' ht.id ht.parked ht.context ht.running ht.pending ht.finalizing rfl ht.opCount
          ht.maxOps ht.preventYield ht.yieldOverride (by rw [ht.observers, hf.id]) ht.children
          ht.dispatcher ht.means
      · rw [hf.id]
        exact means_pushAsyncFinalizer hf.means _
    · rw [hex₁] at hex
      rw [← hex]
      exact ⟨hok, hm, hf.withFrame (means_answerWith hf.means (exitValue_means root ex mode)), rfl, rfl,
        ListRel.nil⟩

end Actions

end Effect4.Program.Sched

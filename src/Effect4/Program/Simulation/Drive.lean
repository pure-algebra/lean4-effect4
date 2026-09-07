import Effect4.Program.Simulation.Evaluate
import Effect4.Program.Simulation.Pending

/-!
# The command driver (P3, step 5)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). The generic book
(`Machine/Book.lean`) lifts one obligation, `StepAgrees`, through the whole loop: every
command of `driveStep` keeps the frame machine's invariant and leaves related machines and
related residual commands. This module discharges it at the native alphabets: the two
evaluators through `evaluate_rel`, and the sixteen bookkeeping commands through the shared
machine operations and the code-valued hooks (`Simulation/Hooks.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program

/-! ## Results and commands -/

theorem CmdsRel.mk' {root : NativeEff} {r₁ : FMachine × List FCmd} {r₂ : RState × List RCmd}
    (hok : MachineOk StoresOk r₁.1) (hm : BMeans root r₁.1 r₂.1)
    (hn : ListRel (CMeans root) r₁.2 r₂.2) : CmdsRel root r₁ r₂ := ⟨hok, hm, hn⟩

theorem CmdsRel.appendRest {root : NativeEff} {a₁ : FMachine × List FCmd} {a₂ : RState × List RCmd}
    (h : CmdsRel root a₁ a₂) {r₁ : List FCmd} {r₂ : List RCmd} (hr : ListRel (CMeans root) r₁ r₂) :
    CmdsRel root (a₁.1, a₁.2 ++ r₁) (a₂.1, a₂.2 ++ r₂) := ⟨h.1, h.2.1, ListRel.append h.2.2 hr⟩

theorem cmeans_evaluate (root : NativeEff) {a b : FiberId} (h : a = b) :
    CMeans root (.evaluate a) (.evaluate b) := h
theorem cmeans_loop (root : NativeEff) (id : FiberId) (y : Bool) :
    CMeans root (.loop id y) (.loop id y) := ⟨rfl, rfl⟩
theorem cmeans_deliver (root : NativeEff) (id : FiberId) (y : Bool) :
    CMeans root (.deliver id y) (.deliver id y) := ⟨rfl, rfl⟩
theorem cmeans_finish (root : NativeEff) (id : FiberId) (ex : ExitV) :
    CMeans root (.finish id ex) (.finish id ex) := ⟨rfl, rfl⟩
theorem cmeans_resume (root : NativeEff) {a b : FiberId} (h : a = b) (token : Nat) {c₁ : NCode}
    {c₂ : RProgram} (hc : CodeMeans root c₁ c₂) :
    CMeans root (.resume a token c₁) (.resume b token c₂) := ⟨h, rfl, hc⟩
theorem cmeans_launch (root : NativeEff) (r : Nat) : CMeans root (.launch r) (.launch r) := rfl
theorem cmeans_enrollRace (root : NativeEff) (r : Nat) (c : FiberId) :
    CMeans root (.enrollRace r c) (.enrollRace r c) := ⟨rfl, rfl⟩
theorem cmeans_enrollRace' (root : NativeEff) (r : Nat) {a b : FiberId} (h : a = b) :
    CMeans root (.enrollRace r a) (.enrollRace r b) := ⟨rfl, h⟩
theorem cmeans_registrationDone (root : NativeEff) (r : Nat) (y : Bool) :
    CMeans root (.registrationDone r y) (.registrationDone r y) := ⟨rfl, rfl⟩
theorem cmeans_interruptTarget (root : NativeEff) (t : FiberId) (w : Option FiberId)
    {x₁ x₂ : ReasonAnnotations Ann} (hx : x₁ = x₂) :
    CMeans root (.interruptTarget t w x₁) (.interruptTarget t w x₂) := ⟨rfl, rfl, hx⟩
theorem cmeans_afterInterrupt (root : NativeEff) (h : FiberId) (y : Bool) (k : ParkKind) :
    CMeans root (.afterInterrupt h y k) (.afterInterrupt h y k) := ⟨rfl, rfl, rfl⟩
theorem cmeans_raceCancel (root : NativeEff) (r : Nat) (h : FiberId) (y : Bool)
    (rem vis : List FiberId) :
    CMeans root (.raceCancel r h y rem vis) (.raceCancel r h y rem vis) := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem cmeans_trackChild (root : NativeEff) (p c : FiberId) :
    CMeans root (.trackChild p c) (.trackChild p c) := ⟨rfl, rfl⟩
theorem cmeans_observe (root : NativeEff) {a b : FiberId} (h : a = b) (e : ExitV) (o : Observer) :
    CMeans root (.observe a e o) (.observe b e o) := ⟨h, rfl, rfl⟩
theorem cmeans_exitDone (root : NativeEff) {a b : FiberId} (h : a = b) :
    CMeans root (.exitDone a) (.exitDone b) := h
theorem cmeans_closeParAwait (root : NativeEff) (h : FiberId) (y : Bool) (fs : List FiberId) :
    CMeans root (.closeParAwait h y fs) (.closeParAwait h y fs) := ⟨rfl, rfl, rfl⟩
theorem cmeans_link (root : NativeEff) (md : Supervision.ScopeMode) (s k : Nat) (t : FiberId)
    (i : Option FiberId) (x : ReasonAnnotations Ann) :
    CMeans root (.link md s k t i x) (.link md s k t i x) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem cmeans_drainDue (root : NativeEff) : CMeans root .drainDue .drainDue := trivial

theorem listRel_observe (root : NativeEff) {a b : FiberId} (hab : a = b) (exit : ExitV) :
    ∀ l : List Observer,
      ListRel (CMeans root) (l.map (Cmd.observe a exit)) (l.map (Cmd.observe b exit))
  | [] => ListRel.nil
  | _ :: rest => ListRel.cons ⟨hab, rfl, rfl⟩ (listRel_observe root hab exit rest)

/-- The due resumes read into related commands: every owed program is a completion. -/
theorem drain_rel (root : NativeEff) :
    ∀ (l : List (FiberId × Nat × Program)), (∀ e ∈ l, CompletionShaped e.2.2) →
      ListRel (CMeans root)
        ((l.map fun d => (d.1, d.2.1, embed d.2.2)).map fun d => Cmd.resume d.1 d.2.1 d.2.2)
        ((l.map fun d => (d.1, d.2.1, denoteStored d.2.2)).map fun d => Cmd.resume d.1 d.2.1 d.2.2)
  | [], _ => ListRel.nil
  | e :: rest, h =>
    ListRel.cons ⟨rfl, rfl, stored_means root (h e (List.mem_cons.mpr (Or.inl rfl)))⟩
      (drain_rel root rest fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))

/-! ## Fibers, at the shapes the driver produces -/

section FiberShapes

variable {root : NativeEff} {f₁ : FRun} {f₂ : RFiber}

theorem FMeans.mapChildren (h : FMeans root f₁ f₂) (g : List FiberId → List FiberId) :
    FMeans root { f₁ with children := g f₁.children } { f₂ with children := g f₂.children } := by
  rw [h.children]
  exact h.withChildren _

theorem FMeans.mapObservers (h : FMeans root f₁ f₂) (g : List Observer → List Observer) :
    FMeans root { f₁ with observers := g f₁.observers } { f₂ with observers := g f₂.observers } := by
  rw [h.observers]
  exact h.withObservers _

theorem FMeans.publish (h : FMeans root f₁ f₂) (exit : ExitV) :
    FMeans root (f₁.publish exit) (f₂.publish exit) := by
  unfold RunFiber.publish
  dsimp only [FiberCore.setDeferred, frameCore, termCore]
  exact FMeans.mk' h.id rfl h.context rfl rfl rfl rfl h.opCount h.maxOps h.preventYield
    h.yieldOverride h.observers h.children h.dispatcher (means_setDeferred h.means false)

theorem FMeans.cleared (h : FMeans root f₁ f₂) :
    FMeans root (f₁.cleared (interpOf root)) (f₂.cleared (interpR root)) := by
  unfold RunFiber.cleared
  dsimp only [FiberCore.clearStack, frameCore, termCore]
  exact FMeans.mk' h.id h.parked rfl h.running h.pending h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride rfl rfl h.dispatcher (means_clearStack h.means)

theorem FMeans.runloopTop (h : FMeans root f₁ f₂) :
    FMeans root (runloopTop f₁) (runloopTop f₂) := by
  unfold Effect4.Machine.runloopTop
  dsimp only [FiberCore.deferredInterrupt, FiberCore.pendingFailure, frameCore, termCore]
  by_cases hd : f₂.frame.deferredInterrupt = true
  · rw [if_pos (h.deferred.trans hd), if_pos hd]
    exact h.withFrame (means_pendingFailure h.means)
  · rw [if_neg (fun e => hd (h.deferred.symm.trans e)), if_neg hd]
    exact h

/-- The countdown's park entry, rewritten on both fibers. -/
theorem FMeans.countdownEntry (h : FMeans root f₁ f₂) (token : Nat) (w : Option FiberId)
    (rem : List FiberId) (exits : List ExitV) :
    FMeans root
      { f₁ with pending := f₂.pending.map fun q =>
        if q.token = token then { q with waitingOn := w, remaining := rem, collected := exits } else q }
      { f₂ with pending := f₂.pending.map fun q =>
        if q.token = token then { q with waitingOn := w, remaining := rem, collected := exits } else q } :=
  FMeans.mk' h.id h.parked h.context h.running rfl h.finalizing h.exit h.opCount h.maxOps
    h.preventYield h.yieldOverride h.observers h.children h.dispatcher h.means

end FiberShapes

/-! ## Parks and pending entries -/

theorem pendingOk_nil {g : FRun} (h : g.pending = []) : PendingOk g := by
  intro p hp
  rw [h] at hp
  simp at hp

theorem pendingOk_filter {w : FRun} (hw : PendingOk w)
    (P : Pending EffName Val Err Defect FiberId Ann → Bool) {g : FRun}
    (h : g.pending = w.pending.filter P) : PendingOk g := by
  intro p hp
  rw [h] at hp
  exact hw p (List.mem_filter.mp hp).1

theorem pendingOk_map {w : FRun} (hw : PendingOk w)
    (g : Pending EffName Val Err Defect FiberId Ann → Pending EffName Val Err Defect FiberId Ann)
    (hg : ∀ q, (g q).resumeWith = q.resumeWith) {w' : FRun} (h : w'.pending = w.pending.map g) :
    PendingOk w' := by
  intro p hp
  rw [h] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [hg q]
  exact hw q hq

/-- The countdown's park entry keeps the invariant: only bookkeeping fields change. -/
theorem pendingOk_countdownEntry {w₁ : FRun} (hw : PendingOk w₁) {w₂ : RFiber}
    (hpend : w₁.pending = w₂.pending) (token : Nat) (w : Option FiberId) (rem : List FiberId)
    (exits : List ExitV) :
    PendingOk { w₁ with pending := w₂.pending.map fun q =>
      if q.token = token then { q with waitingOn := w, remaining := rem, collected := exits } else q } := by
  refine pendingOk_map hw
    (fun q => if q.token = token then { q with waitingOn := w, remaining := rem, collected := exits } else q)
    (fun q => ?_) (by rw [hpend])
  split <;> rfl

theorem dropFinalizer_ok (root : NativeEff) (scope key : Nat) {s s' : Stores} (hs : StoresOk s)
    (h : (interpOf root).dropFinalizer scope key s = some s') : StoresOk s' := by
  dsimp only [interpOf] at h
  split at h
  · cases h
  · rw [← Option.some.inj h]
    exact storesOk_of_deferreds rfl hs

theorem dueResumes_frame (root : NativeEff) (s : Stores) :
    (interpOf root).dueResumes s =
      ((s.deferreds.drainDue).1.map fun d => (d.1, d.2.1, embed d.2.2),
        { s with deferreds := (s.deferreds.drainDue).2 }) := rfl

theorem dueResumes_term (root : NativeEff) (s : Stores) :
    (interpR root).dueResumes s =
      ((s.deferreds.drainDue).1.map fun d => (d.1, d.2.1, denoteStored d.2.2),
        { s with deferreds := (s.deferreds.drainDue).2 }) := rfl

theorem resumePrim_means (root : NativeEff) (resume : Resume EffName)
    (hres : ∀ name, resume ≠ Resume.continueWith name) (exits : List ExitV) :
    CodeMeans root (countdownPark.resumePrim (interpOf root) resume exits)
      (countdownPark.resumePrim (interpR root) resume exits) := by
  cases resume with
  | exitsValue => exact CodeMeans.success _
  | void => exact CodeMeans.success _
  | continueWith name => exact absurd rfl (hres name)

/-- `awaitCode` reads the same fiber on both machines. -/
theorem awaitCode_means (root : NativeEff) {m₁ : FMachine} {m₂ : RState} (hm : BMeans root m₁ m₂)
    (kind : ParkKind) :
    CodeMeans root (awaitCode (interpOf root) m₁ kind) (awaitCode (interpR root) m₂ kind) := by
  cases kind with
  | join target mode =>
    have hex : (m₁.fiber? target).bind RunFiber.exit = (m₂.fiber? target).bind RunFiber.exit := by
      rcases hm.fiber?_cases target with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
      · rw [h₁, h₂]
        rfl
      · rw [h₁, h₂]
        exact hf.exit
    unfold awaitCode
    dsimp only
    rw [hex]
    cases (m₂.fiber? target).bind RunFiber.exit with
    | some exit => exact exitValue_means root exit mode
    | none => exact parkCode_means root (.join target mode)
  | race r => exact parkCode_means root (.race r)
  | awaitAll targets => exact parkCode_means root (.awaitAll targets)

theorem asVoidCode_means (root : NativeEff) {c₁ : NCode} {c₂ : RProgram} (hc : CodeMeans root c₁ c₂) :
    CodeMeans root (asVoidCode (interpOf root) c₁) (asVoidCode (interpR root) c₂) :=
  restore_means root hc (.success .unit)

/-! ## Settling an iteration -/

theorem settle_rel (root : NativeEff) {it₁ : FIter} {it₂ : RIter} (h : IterRel root it₁ it₂)
    (hp : PendingOk it₁.fiber) {id₁ id₂ : FiberId} (hid : id₁ = id₂) {r₁ : List FCmd}
    {r₂ : List RCmd} (hr : ListRel (CMeans root) r₁ r₂) :
    CmdsRel root (settle id₁ r₁ it₁) (settle id₂ r₂ it₂) := by
  subst hid
  obtain ⟨m₁, f₁, y₁, o₁, n₁⟩ := it₁
  obtain ⟨m₂, f₂, y₂, o₂, n₂⟩ := it₂
  obtain ⟨hok, hm, hf, hy, ho, hn⟩ := h
  dsimp only at hok hm hf hy ho hn hp
  subst hy ho
  unfold settle
  dsimp only [FiberCore.deferredInterrupt, frameCore, termCore]
  cases o₁ with
  | continue_ =>
    dsimp only
    exact CmdsRel.mk' (machineOk_update hok hp) (hm.update hf)
      (ListRel.append (ListRel.append hn (ListRel.cons (cmeans_loop root id₁ y₁) ListRel.nil)) hr)
  | answered =>
    dsimp only
    exact CmdsRel.mk' (machineOk_update hok hp) (hm.update hf)
      (ListRel.append (ListRel.append hn (ListRel.cons (cmeans_deliver root id₁ y₁) ListRel.nil)) hr)
  | parked =>
    dsimp only
    by_cases hd : f₂.frame.deferredInterrupt = true
    · rw [if_pos (hf.deferred.trans hd), if_pos hd]
      exact CmdsRel.mk' (machineOk_update hok (pendingOk_nil rfl)) (hm.update hf.unparked)
        (ListRel.append (ListRel.append hn (ListRel.cons (cmeans_loop root id₁ y₁) ListRel.nil)) hr)
    · rw [if_neg (fun e => hd (hf.deferred.symm.trans e)), if_neg hd]
      exact CmdsRel.mk' (machineOk_update hok (pendingOk_of_fields hp rfl))
        (hm.update (hf.withRunning false)) (ListRel.append hn hr)
  | commands =>
    dsimp only
    exact CmdsRel.mk' (machineOk_update hok hp) (hm.update hf) (ListRel.append hn hr)
  | finished ex =>
    dsimp only
    exact CmdsRel.mk' (machineOk_update hok hp) (hm.update hf)
      (ListRel.append (ListRel.append hn (ListRel.cons (cmeans_finish root id₁ ex) ListRel.nil)) hr)
  | stuck why =>
    dsimp only
    exact CmdsRel.mk'
      (machineOk_halt (machineOk_update (f := { f₁ with running := false }) hok
        (pendingOk_of_fields hp rfl)) why)
      ((hm.update (hf.withRunning false)).halt why) ListRel.nil

/-! ## One iteration -/

theorem iteration_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState} (hstuck : m₁.stuck = none)
    (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
    (hf : FMeans root f₁ f₂) (y : Bool) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    IterRel root (iteration (interpOf root) m₁ f₁ y) (iteration (interpR root) m₂ f₂ y) := by
  have hf₁ : FMeans root (countOp (runloopTop f₁)) (countOp (runloopTop f₂)) :=
    hf.runloopTop.counted
  have hcond : (!y && !(countOp (runloopTop f₁)).preventYield && yieldVerdict (countOp (runloopTop f₁)))
      = (!y && !(countOp (runloopTop f₂)).preventYield && yieldVerdict (countOp (runloopTop f₂))) := by
    rw [hf₁.preventYield, hf₁.verdict]
  unfold iteration injectYield
  dsimp only
  by_cases hc : (!y && !(countOp (runloopTop f₁)).preventYield && yieldVerdict (countOp (runloopTop f₁))) = true
  · rw [if_pos hc, if_pos (hcond.symm.trans hc)]
    dsimp only
    refine evaluate_rel root ?_ (machineOk_emit hok _) (BMeans.emit hm _ _)
      ((hf₁.withYield none).answer (yieldBefore_means root hf₁.current)) true
    exact hstuck
  · rw [if_neg hc, if_neg (fun e => hc (hcond.trans e))]
    dsimp only
    exact evaluate_rel root hstuck hok hm hf₁ y

/-! ## Interrupts and observers -/

theorem interruptEach_rel (root : NativeEff) {i₁ : FInterp} {i₂ : RInterp} (hi : InterpAgree i₁ i₂)
    {m₁ : FMachine} {m₂ : RState} (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂)
    (who : FiberId) {x₁ x₂ : ReasonAnnotations Ann} (hx : x₁ = x₂) (targets : List FiberId)
    {n₁ : List FCmd} {n₂ : List RCmd} (hn : ListRel (CMeans root) n₁ n₂) :
    CmdsRel root (interruptEach i₁ who x₁ targets (m₁, n₁)) (interruptEach i₂ who x₂ targets (m₂, n₂)) := by
  subst hx
  unfold interruptEach
  refine foldl_rel (P := fun (x : FMachine × List FCmd) (y : RState × List RCmd) => CmdsRel root x y)
    (R := Eq) ?_ (ListRel.refl (fun _ => rfl) targets) (CmdsRel.mk' hok hm hn)
  intro a₁ a₂ t₁ t₂ ha ht
  subst ht
  obtain ⟨hok', hm', hn'⟩ := ha
  dsimp only
  rcases hm'.fiber?_cases t₁ with ⟨h₁, h₂⟩ | ⟨g₁, g₂, h₁, h₂, hg⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok' hm' hn'
  · rw [h₁, h₂]
    dsimp only
    have hrec := interruptRecord_rel root hi (some who) x₁ hg
    have hpend := interruptRecord_pendingOk i₁ (some who) x₁ (pendingOk_of_fiber? hok' h₁)
    generalize interruptRecord i₁ (some who) x₁ g₁ = s₁ at hrec hpend ⊢
    generalize interruptRecord i₂ (some who) x₁ g₂ = s₂ at hrec ⊢
    obtain ⟨g₁', a₁'⟩ := s₁
    obtain ⟨g₂', a₂'⟩ := s₂
    obtain ⟨hrel, ha⟩ := hrec
    dsimp only at hrel ha hpend ⊢
    subst ha
    refine CmdsRel.mk' (machineOk_emit (machineOk_update hok' hpend) _)
      (BMeans.emit (hm'.update hrel) _ _) (ListRel.append hn' ?_)
    cases a₁'
    · exact ListRel.nil
    · exact ListRel.cons (cmeans_evaluate root rfl) ListRel.nil

theorem fireObserver_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState} (hok : MachineOk StoresOk m₁)
    (hm : BMeans root m₁ m₂) (id : FiberId) (exit : ExitV) {n₁ : List FCmd} {n₂ : List RCmd}
    (hn : ListRel (CMeans root) n₁ n₂) (observer : Observer) :
    CmdsRel root (fireObserver (interpOf root) id exit (m₁, n₁) observer)
      (fireObserver (interpR root) id exit (m₂, n₂) observer) := by
  cases observer with
  | resumeAwait waiter token mode =>
    simp only [fireObserver]
    exact CmdsRel.mk' (machineOk_emit hok _) (BMeans.emit hm _ _)
      (ListRel.append hn
        (ListRel.cons (cmeans_resume root rfl token (exitValue_means root exit mode)) ListRel.nil))
  | untrackChild parent =>
    simp only [fireObserver]
    refine CmdsRel.mk' (machineOk_modify (machineOk_emit hok _) parent ?_)
      ((BMeans.emit hm _ _).modify parent ?_) hn
    · intro _ hg
      exact pendingOk_of_fields hg rfl
    · intro g₁ g₂ hg
      exact hg.mapChildren (fun l => l.filter fun c => c ≠ id)
  | dropScopeFinalizer scope key =>
    simp only [fireObserver]
    have hok' := machineOk_emit hok [RunEvent.observerFired id (Observer.dropScopeFinalizer scope key)]
    have hm' := BMeans.emit hm [RunEvent.observerFired id (Observer.dropScopeFinalizer scope key)]
      [RunEvent.observerFired id (Observer.dropScopeFinalizer scope key)]
    generalize m₁.emit [RunEvent.observerFired id (Observer.dropScopeFinalizer scope key)] = M₁
      at hok' hm' ⊢
    generalize m₂.emit [RunEvent.observerFired id (Observer.dropScopeFinalizer scope key)] = M₂
      at hm' ⊢
    have hd : (interpR root).dropFinalizer scope key M₂.state
        = (interpOf root).dropFinalizer scope key M₁.state := by
      rw [hm'.state]
      rfl
    rw [hd]
    cases hres : (interpOf root).dropFinalizer scope key M₁.state with
    | none => exact CmdsRel.mk' (machineOk_halt hok' _) (hm'.halt _) hn
    | some state =>
      exact CmdsRel.mk' (machineOk_stateOf hok' (dropFinalizer_ok root scope key hok'.state hres))
        (hm'.stateOf state) hn
  | countdown waiter token =>
    simp only [fireObserver]
    have hok' := machineOk_emit hok [RunEvent.observerFired id (Observer.countdown waiter token)]
    have hm' := BMeans.emit hm [RunEvent.observerFired id (Observer.countdown waiter token)]
      [RunEvent.observerFired id (Observer.countdown waiter token)]
    generalize m₁.emit [RunEvent.observerFired id (Observer.countdown waiter token)] = M₁
      at hok' hm' ⊢
    generalize m₂.emit [RunEvent.observerFired id (Observer.countdown waiter token)] = M₂
      at hm' ⊢
    rcases hm'.fiber?_cases waiter with ⟨h₁, h₂⟩ | ⟨w₁, w₂, h₁, h₂, hw⟩
    · rw [h₁, h₂]
      exact CmdsRel.mk' hok' hm' hn
    · have hpw : PendingOk w₁ := pendingOk_of_fiber? hok' h₁
      simp only [h₁, h₂, hw.pending]
      cases hfind : w₂.pending.find? (fun p => p.token = token) with
      | none => exact CmdsRel.mk' hok' hm' hn
      | some p =>
        dsimp only
        have hp : ∀ name, p.resumeWith ≠ Resume.continueWith name :=
          hpw p (by rw [hw.pending]; exact List.mem_of_find?_eq_some hfind)
        by_cases hff : (p.failFast && !exit.isSuccess && p.collected.all Exit.isSuccess) = true
        · rw [if_pos hff, if_pos hff]
          have hie := interruptEach_rel root (interpAgree_of root) hok' hm' waiter
            (x₁ := (interpOf root).stackAnnotations waiter) (x₂ := (interpR root).stackAnnotations waiter)
            rfl p.remaining (n₁ := []) (n₂ := []) ListRel.nil
          generalize interruptEach (interpOf root) waiter ((interpOf root).stackAnnotations waiter)
            p.remaining (M₁, []) = ie₁ at hie ⊢
          generalize interruptEach (interpR root) waiter ((interpR root).stackAnnotations waiter)
            p.remaining (M₂, []) = ie₂ at hie ⊢
          obtain ⟨im₁, in₁⟩ := ie₁
          obtain ⟨im₂, in₂⟩ := ie₂
          obtain ⟨hok'', hm'', hn''⟩ := hie
          dsimp only at hok'' hm'' hn'' ⊢
          rw [countdownWalk_eq hm'' p.remaining (p.collected ++ [exit])]
          cases hcw : countdownWalk im₂ p.remaining (p.collected ++ [exit]) with
          | mk exits opt =>
            cases opt with
            | none =>
              dsimp only
              exact CmdsRel.mk' (machineOk_update hok'' (pendingOk_countdownEntry hpw hw.pending token none [] exits))
                (hm''.update (hw.countdownEntry token none [] exits))
                (ListRel.append (ListRel.append hn hn'')
                  (ListRel.cons (cmeans_resume root rfl token (resumePrim_means root p.resumeWith hp exits))
                    ListRel.nil))
            | some tr =>
              obtain ⟨next, rest⟩ := tr
              dsimp only
              refine CmdsRel.mk'
                (machineOk_update (machineOk_modify hok'' next ?_)
                  (pendingOk_countdownEntry hpw hw.pending token (some next) rest exits))
                ((hm''.modify next ?_).update (hw.countdownEntry token (some next) rest exits))
                (ListRel.append hn hn'')
              · intro _ hg
                exact pendingOk_of_fields hg rfl
              · intro g₁ g₂ hg
                exact hg.mapObservers (fun l => l ++ [Observer.countdown waiter token])
        · rw [if_neg hff, if_neg hff]
          dsimp only
          rw [countdownWalk_eq hm' p.remaining (p.collected ++ [exit])]
          cases hcw : countdownWalk M₂ p.remaining (p.collected ++ [exit]) with
          | mk exits opt =>
            cases opt with
            | none =>
              dsimp only
              exact CmdsRel.mk' (machineOk_update hok' (pendingOk_countdownEntry hpw hw.pending token none [] exits))
                (hm'.update (hw.countdownEntry token none [] exits))
                (ListRel.append (ListRel.append hn ListRel.nil)
                  (ListRel.cons (cmeans_resume root rfl token (resumePrim_means root p.resumeWith hp exits))
                    ListRel.nil))
            | some tr =>
              obtain ⟨next, rest⟩ := tr
              dsimp only
              refine CmdsRel.mk'
                (machineOk_update (machineOk_modify hok' next ?_)
                  (pendingOk_countdownEntry hpw hw.pending token (some next) rest exits))
                ((hm'.modify next ?_).update (hw.countdownEntry token (some next) rest exits))
                (ListRel.append hn ListRel.nil)
              · intro _ hg
                exact pendingOk_of_fields hg rfl
              · intro g₁ g₂ hg
                exact hg.mapObservers (fun l => l ++ [Observer.countdown waiter token])
  | raceCallback raceId =>
    simp only [fireObserver]
    have hok' := machineOk_emit hok [RunEvent.observerFired id (Observer.raceCallback raceId)]
    have hm' := BMeans.emit hm [RunEvent.observerFired id (Observer.raceCallback raceId)]
      [RunEvent.observerFired id (Observer.raceCallback raceId)]
    generalize m₁.emit [RunEvent.observerFired id (Observer.raceCallback raceId)] = M₁
      at hok' hm' ⊢
    generalize m₂.emit [RunEvent.observerFired id (Observer.raceCallback raceId)] = M₂
      at hm' ⊢
    rcases hm'.race?_cases raceId with ⟨h₁, h₂⟩ | ⟨r₁, r₂, h₁, h₂, hr⟩
    · rw [h₁, h₂]
      exact CmdsRel.mk' hok' hm' hn
    · rw [h₁, h₂]
      obtain ⟨id₁, host₁, token₁, state₁, settled₁, progs₁, reg₁⟩ := r₁
      obtain ⟨id₂, host₂, token₂, state₂, settled₂, progs₂, reg₂⟩ := r₂
      dsimp only [RaceMeans] at hr
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hprog⟩ := hr
      dsimp only
      have hrace : RaceMeans (CodeMeans root)
          ⟨id₁, host₁, token₁, Supervision.raceComplete state₁ id exit, settled₁, progs₁, reg₁⟩
          ⟨id₁, host₁, token₁, Supervision.raceComplete state₁ id exit, settled₁, progs₂, reg₁⟩ :=
        raceMeans_mk' rfl rfl rfl rfl rfl rfl hprog
      cases settled₁ with
      | true =>
        cases hacc : (Supervision.raceComplete state₁ id exit).accepted <;>
          exact CmdsRel.mk' (machineOk_updateRace hok' _) (hm'.updateRace hrace) hn
      | false =>
        cases hacc : (Supervision.raceComplete state₁ id exit).accepted with
        | none => exact CmdsRel.mk' (machineOk_updateRace hok' _) (hm'.updateRace hrace) hn
        | some accepted =>
          dsimp only
          refine CmdsRel.mk' (machineOk_emit (machineOk_updateRace (machineOk_updateRace hok' _) _) _)
            (BMeans.emit ((hm'.updateRace hrace).updateRace
              (raceMeans_mk' rfl rfl rfl rfl rfl rfl hprog)) _ _)
            (ListRel.append hn ?_)
          cases reg₁ with
          | true => exact ListRel.nil
          | false =>
            exact ListRel.cons
              (cmeans_resume root rfl token₁ (raceSettle_means root raceId _ accepted)) ListRel.nil
  | callback key =>
    simp only [fireObserver]
    exact CmdsRel.mk' (machineOk_emit (machineOk_emit hok _) _) (BMeans.emit (BMeans.emit hm _ _) _ _) hn

/-! ## The exit path -/

theorem exitInterruptChildren_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState}
    (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
    (hf : FMeans root f₁ f₂) (hp : PendingOk f₁) (exit : ExitV) :
    CmdsRel root (exitFiber.exitInterruptChildren (interpOf root) m₁ f₁ exit)
      (exitFiber.exitInterruptChildren (interpR root) m₂ f₂ exit) := by
  unfold exitFiber.exitInterruptChildren
  dsimp only [FiberCore.answerWith, FiberCore.setDeferred, FiberCore.onSuccess, frameCore, termCore]
  have hcode : CodeMeans root
      (Prim.onSuccess ((interpOf root).interruptAllCode f₁.children) ((interpOf root).restoreName exit))
      (restoreR ((interpR root).interruptAllCode f₂.children) ((interpR root).restoreName exit)) := by
    rw [hf.children]
    exact restore_means root (interruptAllCode_means root f₂.children) exit
  refine CmdsRel.mk' (machineOk_emit (machineOk_update hok ?_) _)
    (BMeans.emit (hm.update ?_) _ _) (ListRel.cons (cmeans_evaluate root hf.id) ListRel.nil)
  · exact pendingOk_of_fields hp rfl
  · exact FMeans.mk' hf.id hf.parked hf.context rfl hf.pending rfl hf.exit hf.opCount hf.maxOps
      hf.preventYield hf.yieldOverride hf.observers hf.children hf.dispatcher
      (means_answerWith (means_setDeferred hf.means false) hcode)

theorem exitStore_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState}
    (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
    (hf : FMeans root f₁ f₂) (exit : ExitV) :
    CmdsRel root (exitFiber.exitStore (interpOf root) m₁ f₁ exit)
      (exitFiber.exitStore (interpR root) m₂ f₂ exit) := by
  unfold exitFiber.exitStore
  have hpub := hf.publish exit
  have hobs : (f₁.publish exit).observers = (f₂.publish exit).observers := hpub.observers
  simp only [hobs]
  cases hcase : (f₂.publish exit).observers with
  | nil =>
    exact CmdsRel.mk'
      (machineOk_update (machineOk_emit (machineOk_update hok (pendingOk_nil rfl)) _) (pendingOk_nil rfl))
      ((BMeans.emit (hm.update hpub) _ _).update hpub.cleared)
      (ListRel.cons (cmeans_drainDue root) ListRel.nil)
  | cons o os =>
    exact CmdsRel.mk' (machineOk_emit (machineOk_update hok (pendingOk_nil rfl)) _)
      (BMeans.emit (hm.update hpub) _ _)
      (ListRel.append (listRel_observe root hpub.id exit (o :: os))
        (ListRel.cons (cmeans_exitDone root hpub.id) (ListRel.cons (cmeans_drainDue root) ListRel.nil)))

theorem exitFiber_rel (root : NativeEff) {m₁ : FMachine} {m₂ : RState}
    (hok : MachineOk StoresOk m₁) (hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
    (hf : FMeans root f₁ f₂) (hp : PendingOk f₁) (exit : ExitV) :
    CmdsRel root (exitFiber (interpOf root) m₁ f₁ exit) (exitFiber (interpR root) m₂ f₂ exit) := by
  unfold exitFiber
  have hc : (m₁.middlewareInstalled && f₁.finalizing.isNone && !f₁.children.isEmpty)
      = (m₂.middlewareInstalled && f₂.finalizing.isNone && !f₂.children.isEmpty) := by
    rw [hm.middleware, hf.finalizing, hf.children]
  by_cases h : (m₁.middlewareInstalled && f₁.finalizing.isNone && !f₁.children.isEmpty) = true
  · rw [if_pos h, if_pos (hc.symm.trans h)]
    exact exitInterruptChildren_rel root hok hm hf hp exit
  · rw [if_neg h, if_neg (fun e => h (hc.trans e))]
    exact exitStore_rel root hok hm hf exit

/-! ## The seventeen commands -/

section Commands

variable (root : NativeEff) {m₁ : FMachine} {m₂ : RState} (hok : MachineOk StoresOk m₁)
  (hm : BMeans root m₁ m₂) {r₁ : List FCmd} {r₂ : List RCmd} (hr : ListRel (CMeans root) r₁ r₂)

include hok hm hr

theorem drive_evaluate (id : FiberId) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.evaluate id) r₁)
      (driveStep (interpR root) m₂ (.evaluate id) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases id with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only
    have hc : (f₁.exit.isSome || f₁.running) = (f₂.exit.isSome || f₂.running) := by
      rw [hf.exit, hf.running]
    by_cases h : (f₁.exit.isSome || f₁.running) = true
    · rw [if_pos h, if_pos (hc.symm.trans h)]
      exact CmdsRel.mk' hok hm hr
    · rw [if_neg h, if_neg (fun e => h (hc.trans e))]
      refine CmdsRel.mk' (machineOk_emit (machineOk_update hok ?_) _)
        (BMeans.emit (hm.update hf.started) _ _) (ListRel.cons (cmeans_loop root id false) hr)
      exact pendingOk_of_fields (pendingOk_of_fiber? hok h₁) rfl

theorem drive_loop (hstuck : m₁.stuck = none) (id : FiberId) (y : Bool) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.loop id y) r₁)
      (driveStep (interpR root) m₂ (.loop id y) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases id with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only
    exact settle_rel root (iteration_rel root hstuck hok hm hf y)
      (iteration_pendingOk root m₁ f₁ y (pendingOk_of_fiber? hok h₁)) rfl hr

theorem drive_deliver (hstuck : m₁.stuck = none) (id : FiberId) (y : Bool) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.deliver id y) r₁)
      (driveStep (interpR root) m₂ (.deliver id y) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases id with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only
    exact settle_rel root (evaluate_rel root hstuck hok hm hf y)
      (evaluateNative_pendingOk root m₁ f₁ y (pendingOk_of_fiber? hok h₁)) rfl hr

theorem drive_finish (id : FiberId) (exit : ExitV) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.finish id exit) r₁)
      (driveStep (interpR root) m₂ (.finish id exit) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases id with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only
    exact CmdsRel.appendRest
      (exitFiber_rel root hok hm (hf.withRunning false)
        (pendingOk_of_fields (pendingOk_of_fiber? hok h₁) rfl) exit) hr

theorem drive_resume (id : FiberId) (token : Nat) {c₁ : NCode} {c₂ : RProgram}
    (hc : CodeMeans root c₁ c₂) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.resume id token c₁) r₁)
      (driveStep (interpR root) m₂ (.resume id token c₂) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases id with ⟨h₁, h₂⟩ | ⟨t₁, t₂, h₁, h₂, ht⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only [FiberCore.answerWith, frameCore, termCore]
    simp only [ht.parked]
    cases hp : t₂.parked with
    | notParked => exact CmdsRel.mk' hok hm hr
    | withGuard parkedToken =>
      dsimp only
      by_cases he : parkedToken = token
      · rw [if_pos he, if_pos he]
        refine CmdsRel.mk' (machineOk_emit (machineOk_update hok ?_) _)
          (BMeans.emit (hm.update ?_) _ _) (ListRel.cons (cmeans_evaluate root rfl) hr)
        · exact pendingOk_filter (pendingOk_of_fiber? hok h₁) _ rfl
        · exact FMeans.mk' ht.id rfl ht.context ht.running (by rw [ht.pending]) ht.finalizing ht.exit
            ht.opCount ht.maxOps ht.preventYield ht.yieldOverride ht.observers ht.children ht.dispatcher
            (means_answerWith ht.means hc)
      · rw [if_neg he, if_neg he]
        exact CmdsRel.mk' hok hm hr

theorem drive_launch (raceId : Nat) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.launch raceId) r₁)
      (driveStep (interpR root) m₂ (.launch raceId) r₂) := by
  simp only [driveStep]
  rcases hm.race?_cases raceId with ⟨h₁, h₂⟩ | ⟨r₁', r₂', h₁, h₂, hrace⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    obtain ⟨id₁, host₁, token₁, state₁, settled₁, progs₁, reg₁⟩ := r₁'
    obtain ⟨id₂, host₂, token₂, state₂, settled₂, progs₂, reg₂⟩ := r₂'
    dsimp only [RaceMeans] at hrace
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hprog⟩ := hrace
    dsimp only
    cases hprog with
    | nil => exact CmdsRel.mk' hok hm hr
    | @cons p₁ p₂ more₁ more₂ hpc hrest =>
      dsimp only
      by_cases hacc : state₁.accepted.isSome = true
      · rw [if_pos hacc, if_pos hacc]
        exact CmdsRel.mk' hok hm hr
      · rw [if_neg hacc, if_neg hacc]
        rcases hm.fiber?_cases host₁ with ⟨hh₁, hh₂⟩ | ⟨g₁, g₂, hh₁, hh₂, hg⟩
        · rw [hh₁, hh₂]
          exact CmdsRel.mk' hok hm hr
        · rw [hh₁, hh₂]
          unfold launchEntrant
          have hs := spawn_rel root (i₁ := interpOf root) (i₂ := interpR root) rfl hok hm hg hpc
            ⟨true, true, Supervision.MaskMode.interruptible⟩
          dsimp only [TripleRel] at hs
          obtain ⟨hsok, hsm, -, hchild⟩ := hs
          dsimp only
          exact CmdsRel.mk' (machineOk_emit (machineOk_updateRace hsok _) _)
            (BMeans.emit (hsm.updateRace (raceMeans_mk' rfl rfl rfl rfl rfl rfl hrest)) _ _)
            (ListRel.cons (cmeans_evaluate root hchild)
              (ListRel.cons (cmeans_enrollRace' root raceId hchild)
                (ListRel.cons (cmeans_launch root raceId) hr)))

theorem drive_enrollRace (raceId : Nat) (child : FiberId) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.enrollRace raceId child) r₁)
      (driveStep (interpR root) m₂ (.enrollRace raceId child) r₂) := by
  simp only [driveStep]
  rcases hm.race?_cases raceId with ⟨h₁, h₂⟩ | ⟨r₁', r₂', h₁, h₂, hrace⟩
  · rw [h₁, h₂]
    cases m₁.fiber? child <;> cases m₂.fiber? child <;> exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    rcases hm.fiber?_cases child with ⟨hc₁, hc₂⟩ | ⟨c₁, c₂, hc₁, hc₂, hc⟩
    · rw [hc₁, hc₂]
      exact CmdsRel.mk' hok hm hr
    · rw [hc₁, hc₂]
      obtain ⟨id₁, host₁, token₁, state₁, settled₁, progs₁, reg₁⟩ := r₁'
      obtain ⟨id₂, host₂, token₂, state₂, settled₂, progs₂, reg₂⟩ := r₂'
      dsimp only [RaceMeans] at hrace
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hprog⟩ := hrace
      dsimp only
      have hrace' : RaceMeans (CodeMeans root)
          ⟨id₁, host₁, token₁, { state₁ with live := state₁.live ++ [child] }, settled₁, progs₁, reg₁⟩
          ⟨id₁, host₁, token₁, { state₁ with live := state₁.live ++ [child] }, settled₁, progs₂, reg₁⟩ :=
        raceMeans_mk' rfl rfl rfl rfl rfl rfl hprog
      simp only [hc.exit]
      cases hex : c₂.exit with
      | some exit =>
        exact CmdsRel.appendRest
          (fireObserver_rel root (machineOk_updateRace hok _) (hm.updateRace hrace') child exit
            ListRel.nil (Observer.raceCallback raceId)) hr
      | none =>
        refine CmdsRel.mk' (machineOk_modify (machineOk_updateRace hok _) child ?_)
          ((hm.updateRace hrace').modify child ?_) hr
        · intro _ hg
          exact pendingOk_of_fields hg rfl
        · intro g₁ g₂ hg
          exact hg.mapObservers (fun l => l ++ [Observer.raceCallback raceId])

theorem drive_registrationDone (raceId : Nat) (y : Bool) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.registrationDone raceId y) r₁)
      (driveStep (interpR root) m₂ (.registrationDone raceId y) r₂) := by
  simp only [driveStep]
  rcases hm.race?_cases raceId with ⟨h₁, h₂⟩ | ⟨r₁', r₂', h₁, h₂, hrace⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    obtain ⟨id₁, host₁, token₁, state₁, settled₁, progs₁, reg₁⟩ := r₁'
    obtain ⟨id₂, host₂, token₂, state₂, settled₂, progs₂, reg₂⟩ := r₂'
    dsimp only [RaceMeans] at hrace
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hprog⟩ := hrace
    dsimp only
    have hok' := machineOk_updateRace hok
      (⟨id₁, host₁, token₁, state₁, settled₁, progs₁, false⟩ : FRace)
    have hm' := hm.updateRace (r₁ := ⟨id₁, host₁, token₁, state₁, settled₁, progs₁, false⟩)
      (r₂ := ⟨id₁, host₁, token₁, state₁, settled₁, progs₂, false⟩)
      (raceMeans_mk' rfl rfl rfl rfl rfl rfl hprog)
    generalize m₁.updateRace ⟨id₁, host₁, token₁, state₁, settled₁, progs₁, false⟩ = M₁ at hok' hm' ⊢
    generalize m₂.updateRace ⟨id₁, host₁, token₁, state₁, settled₁, progs₂, false⟩ = M₂ at hm' ⊢
    rcases hm'.fiber?_cases host₁ with ⟨hh₁, hh₂⟩ | ⟨f₁, f₂, hh₁, hh₂, hf⟩
    · rw [hh₁, hh₂]
      exact CmdsRel.mk' hok' hm' hr
    · rw [hh₁, hh₂]
      dsimp only
      cases hacc : state₁.accepted with
      | some exit =>
        exact settle_rel root
          ⟨hok', hm', hf.answer (raceSettle_means root raceId _ exit), rfl, rfl, ListRel.nil⟩
          (pendingOk_of_fields (pendingOk_of_fiber? hok' hh₁) rfl) hf.id hr
      | none =>
        have hname : (interpOf root).cancelName ((interpOf root).raceCancelName raceId) f₁.id token₁
            = (interpR root).cancelName ((interpR root).raceCancelName raceId) f₂.id token₁ :=
          congrArg (fun i => (interpOf root).cancelName ((interpOf root).raceCancelName raceId) i token₁)
            hf.id
        rw [← hname]
        exact settle_rel root
          ⟨machineOk_emit hok' _, BMeans.emit hm' _ _,
            (hf.withFrame (means_pushAsyncFinalizer hf.means _)).park _, rfl, rfl, ListRel.nil⟩
          (pendingOk_parkVoid (pendingOk_of_fields (pendingOk_of_fiber? hok' hh₁) rfl) _ _ _ _ _)
          hf.id hr

theorem drive_interruptTarget (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.interruptTarget target who extra) r₁)
      (driveStep (interpR root) m₂ (.interruptTarget target who extra) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases target with ⟨h₁, h₂⟩ | ⟨g₁, g₂, h₁, h₂, hg⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only
    have hrec := interruptRecord_rel root (interpAgree_of root) who extra hg
    have hpend := interruptRecord_pendingOk (interpOf root) who extra (pendingOk_of_fiber? hok h₁)
    generalize interruptRecord (interpOf root) who extra g₁ = s₁ at hrec hpend ⊢
    generalize interruptRecord (interpR root) who extra g₂ = s₂ at hrec ⊢
    obtain ⟨g₁', a₁⟩ := s₁
    obtain ⟨g₂', a₂⟩ := s₂
    obtain ⟨hrel, ha⟩ := hrec
    dsimp only at hrel ha hpend ⊢
    subst ha
    refine CmdsRel.mk' (machineOk_emit (machineOk_update hok hpend) _)
      (BMeans.emit (hm.update hrel) _ _) (ListRel.append ?_ hr)
    cases a₁
    · exact ListRel.nil
    · exact ListRel.cons (cmeans_evaluate root rfl) ListRel.nil

theorem drive_afterInterrupt (host : FiberId) (y : Bool) (kind : ParkKind) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.afterInterrupt host y kind) r₁)
      (driveStep (interpR root) m₂ (.afterInterrupt host y kind) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases host with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only
    exact settle_rel root
      ⟨hok, hm, hf.answer (asVoidCode_means root (awaitCode_means root hm kind)), rfl, rfl, ListRel.nil⟩
      (pendingOk_of_fields (pendingOk_of_fiber? hok h₁) rfl) hf.id hr

theorem drive_raceCancel (raceId : Nat) (host : FiberId) (y : Bool) (remaining visited : List FiberId) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.raceCancel raceId host y remaining visited) r₁)
      (driveStep (interpR root) m₂ (.raceCancel raceId host y remaining visited) r₂) := by
  simp only [driveStep]
  cases remaining with
  | nil => exact CmdsRel.mk' hok hm (ListRel.cons (cmeans_afterInterrupt root host y _) hr)
  | cons t more =>
    rcases hm.race?_cases raceId with ⟨h₁, h₂⟩ | ⟨r₁', r₂', h₁, h₂, hrace⟩
    · rw [h₁, h₂]
      exact CmdsRel.mk' hok hm (ListRel.cons (cmeans_afterInterrupt root host y _) hr)
    · rw [h₁, h₂]
      dsimp only
      have hlive : (t ∈ r₁'.state.live) = (t ∈ r₂'.state.live) := by
        rw [raceMeans_state hrace]
      by_cases hl : t ∈ r₁'.state.live
      · rw [if_pos hl, if_pos (Eq.mp hlive hl)]
        exact CmdsRel.mk' hok hm
          (ListRel.cons (cmeans_interruptTarget root t (some host)
              (x₁ := (interpOf root).stackAnnotations host) (x₂ := (interpR root).stackAnnotations host) rfl)
            (ListRel.cons (cmeans_raceCancel root raceId host y more (visited ++ [t])) hr))
      · rw [if_neg hl, if_neg (fun e => hl (Eq.mpr hlive e))]
        exact CmdsRel.mk' hok hm (ListRel.cons (cmeans_raceCancel root raceId host y more visited) hr)

theorem drive_trackChild (parent child : FiberId) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.trackChild parent child) r₁)
      (driveStep (interpR root) m₂ (.trackChild parent child) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases child with ⟨h₁, h₂⟩ | ⟨c₁, c₂, h₁, h₂, hc⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only
    have hex : c₁.exit.isSome = c₂.exit.isSome := by rw [hc.exit]
    by_cases he : c₁.exit.isSome = true
    · rw [if_pos he, if_pos (hex.symm.trans he)]
      exact CmdsRel.mk' hok hm hr
    · rw [if_neg he, if_neg (fun e => he (hex.trans e))]
      refine CmdsRel.mk' (machineOk_modify (machineOk_modify hok parent ?_) child ?_)
        ((hm.modify parent ?_).modify child ?_) hr
      · intro _ hg
        exact pendingOk_of_fields hg rfl
      · intro _ hg
        exact pendingOk_of_fields hg rfl
      · intro g₁ g₂ hg
        exact hg.mapChildren (fun l => l ++ [child])
      · intro g₁ g₂ hg
        exact hg.mapObservers (fun l => l ++ [Observer.untrackChild parent])

theorem drive_observe (id : FiberId) (exit : ExitV) (observer : Observer) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.observe id exit observer) r₁)
      (driveStep (interpR root) m₂ (.observe id exit observer) r₂) := by
  simp only [driveStep]
  exact CmdsRel.appendRest (fireObserver_rel root hok hm id exit ListRel.nil observer) hr

theorem drive_exitDone (id : FiberId) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.exitDone id) r₁)
      (driveStep (interpR root) m₂ (.exitDone id) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases id with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    exact CmdsRel.mk' (machineOk_update hok (pendingOk_of_fields (pendingOk_of_fiber? hok h₁) rfl))
      (hm.update hf.cleared) hr

theorem drive_closeParAwait (host : FiberId) (y : Bool) (fibers : List FiberId) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.closeParAwait host y fibers) r₁)
      (driveStep (interpR root) m₂ (.closeParAwait host y fibers) r₂) := by
  simp only [driveStep]
  rcases hm.fiber?_cases host with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]
    exact CmdsRel.mk' hok hm hr
  · rw [h₁, h₂]
    dsimp only
    exact settle_rel root
      ⟨hok, hm,
        hf.withFrame (means_answerWith (means_pushIterator hf.means _ _)
          (parkCode_means root (ParkKind.awaitAll fibers))), rfl, rfl, ListRel.nil⟩
      (pendingOk_of_fields (pendingOk_of_fiber? hok h₁) rfl) hf.id hr

theorem drive_link (mode : Supervision.ScopeMode) (scope key : Nat) (target : FiberId)
    (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ (.link mode scope key target interruptor extra) r₁)
      (driveStep (interpR root) m₂ (.link mode scope key target interruptor extra) r₂) := by
  simp only [driveStep]
  exact CmdsRel.appendRest
    (linkScope_rel root (interpAgree_of root) hok hm mode scope key target interruptor extra) hr

theorem drive_drainDue :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    CmdsRel root (driveStep (interpOf root) m₁ .drainDue r₁) (driveStep (interpR root) m₂ .drainDue r₂) := by
  simp only [driveStep]
  have hs : StoresOk m₂.state := hm.state ▸ hok.state
  have hd := deferredOk_drainDue hs
  rw [hm.state]
  show CmdsRel root
    ({ m₁ with state := ((interpOf root).dueResumes m₂.state).2 },
      (((interpOf root).dueResumes m₂.state).1.map fun d => Cmd.resume d.1 d.2.1 d.2.2) ++ r₁)
    ({ m₂ with state := ((interpR root).dueResumes m₂.state).2 },
      (((interpR root).dueResumes m₂.state).1.map fun d => Cmd.resume d.1 d.2.1 d.2.2) ++ r₂)
  rw [dueResumes_frame, dueResumes_term]
  dsimp only
  exact CmdsRel.mk'
    (machineOk_stateOf (s := { m₂.state with deferreds := (m₂.state.deferreds.drainDue).2 }) hok hd.1)
    (hm.stateOf _) (ListRel.append (drain_rel root _ hd.2) hr)

end Commands

/-! ## The obligation, discharged -/

/-- **`StepAgrees` at the native alphabets.** Every command of the shared driver keeps the
frame machine's invariant and leaves the two machines and their residual commands in the
book. -/
theorem stepAgrees (root : NativeEff) :
    letI := evaluatorFor root
    letI := termEvaluatorFor root
    StepAgrees (interpOf root) (interpR root) StoresOk (CodeMeans root) (Means root) := by
  intro a b c₁ c₂ r₁ r₂ hstuck hok hm hc hr
  cases c₁ with
  | evaluate id =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with rfl
    exact drive_evaluate root hok hm hr _
  | loop id y =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl⟩
    exact drive_loop root hok hm hr hstuck _ _
  | deliver id y =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl⟩
    exact drive_deliver root hok hm hr hstuck _ _
  | finish id ex =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl⟩
    exact drive_finish root hok hm hr _ _
  | resume id token c =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl, hcode⟩
    exact drive_resume root hok hm hr _ _ hcode
  | launch raceId =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with rfl
    exact drive_launch root hok hm hr _
  | enrollRace raceId child =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl⟩
    exact drive_enrollRace root hok hm hr _ _
  | registrationDone raceId y =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl⟩
    exact drive_registrationDone root hok hm hr _ _
  | interruptTarget target who extra =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl, rfl⟩
    exact drive_interruptTarget root hok hm hr _ _ _
  | afterInterrupt host y kind =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl, rfl⟩
    exact drive_afterInterrupt root hok hm hr _ _ _
  | raceCancel raceId host y rem vis =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact drive_raceCancel root hok hm hr _ _ _ _ _
  | trackChild parent child =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl⟩
    exact drive_trackChild root hok hm hr _ _
  | observe id ex observer =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl, rfl⟩
    exact drive_observe root hok hm hr _ _ _
  | exitDone id =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with rfl
    exact drive_exitDone root hok hm hr _
  | closeParAwait host y fs =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl, rfl⟩
    exact drive_closeParAwait root hok hm hr _ _ _
  | link mode scope key target interruptor extra =>
    cases c₂ <;> try exact (hc : False).elim
    rcases hc with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact drive_link root hok hm hr _ _ _ _ _ _
  | drainDue =>
    cases c₂ <;> try exact (hc : False).elim
    exact drive_drainDue root hok hm hr

end Effect4.Program.Sched

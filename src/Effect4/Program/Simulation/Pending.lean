import Effect4.Program.Simulation.Actions

/-!
# The parks the frame evaluator creates (P3, step 4f)

The book's invariant on the frame machine, `PendingOk`, says no parked entry resumes with
`Resume.continueWith`: that constructor is dead in the machine, and the term instance has no
reading for it. This module proves the frame evaluator keeps the invariant: every park it
creates resumes with the void answer or the collected exits, and every other arm leaves the
parks alone.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program

theorem pendingOk_parkVoid {f : FRun} (hf : PendingOk f) (token : Nat) (waitingOn : Option FiberId)
    (remaining : List FiberId) (collected : List ExitV) (failFast : Bool) :
    PendingOk (f.park ⟨token, waitingOn, remaining, collected, Resume.void, failFast⟩) :=
  pendingOk_park hf _ (fun _ h => nomatch h)

theorem start_pending (m : FMachine) (p : FRun) (child : FiberId) (imm : Bool) :
    (start m p child imm).2.1.pending = p.pending := by
  unfold start
  split <;> rfl

theorem countdownPark_pendingOk (i : FInterp) (m : FMachine) (f : FRun) (targets : List FiberId)
    (resume : Resume EffName) (failFast : Bool) (hf : PendingOk f)
    (hres : ∀ name, resume ≠ Resume.continueWith name) :
    PendingOk (countdownPark i m f targets resume failFast).2.1 := by
  unfold countdownPark
  dsimp only
  split
  · exact pendingOk_of_fields hf rfl
  · exact pendingOk_park (pendingOk_of_fields hf rfl) _ hres

theorem registerRace_pendingOk (m : FMachine) (f : FRun) (y : Bool) (raceId : Nat) (hf : PendingOk f) :
    PendingOk (registerRace m f y raceId).fiber := by
  unfold registerRace
  split <;> exact hf

theorem beginRace_pendingOk (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (entrants : List NCode)
    (hf : PendingOk f) : PendingOk (beginRace i m f y entrants).fiber :=
  pendingOk_of_fields hf rfl

theorem finishFrame_pendingOk (m : FMachine) (f : FRun) (y : Bool)
    (next : FrameStep EffName EffThunk Val Err Defect FiberId Ann)
    (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) (nested : List FCmd)
    (hf : PendingOk f) : PendingOk (evaluatePrim.finishFrame m f y next events nested).fiber := by
  unfold evaluatePrim.finishFrame
  dsimp only
  split <;> exact pendingOk_of_fields hf rfl

theorem stepFrame_pendingOk (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (hf : PendingOk f) :
    PendingOk (evaluatePrim.stepFrame i m f y).fiber :=
  finishFrame_pendingOk m f y _ _ _ hf

theorem finalizerOr_pendingOk (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV)
    (hf : PendingOk f) : PendingOk (evaluatePrim.finalizerOr i m f y ex).fiber := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  repeat' split
  all_goals first
    | exact pendingOk_of_fields hf rfl
    | exact stepFrame_pendingOk i m f y hf

theorem interruptAs_pendingOk (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (target who : FiberId)
    (hf : PendingOk f) : PendingOk (evaluatePrim.interruptAs i m f y target who).fiber := by
  unfold evaluatePrim.interruptAs
  dsimp only
  repeat' split
  all_goals exact hf

section Actions

variable (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (hf : PendingOk f)

include hf

theorem fork_pendingOk (program : NCode) (options : Supervision.ForkOptions) {a : FAnswer}
    (ha : ∀ g v, PendingOk g → PendingOk (a g v)) :
    PendingOk (FiberAction.fork i m f y program options a).fiber := by
  unfold FiberAction.fork
  dsimp only
  have hs : (spawn i (if options.daemon then m else { m with middlewareInstalled := true }) f program
    options).2.1 = f := rfl
  generalize spawn i (if options.daemon then m else { m with middlewareInstalled := true }) f program
    options = s at hs ⊢
  obtain ⟨sm, sf, ch⟩ := s
  dsimp only at hs
  subst hs
  have hst := start_pending sm sf ch options.startImmediately
  generalize start sm sf ch options.startImmediately = t at hst ⊢
  obtain ⟨tm, tf, tn⟩ := t
  dsimp only at hst
  exact ha _ _ (pendingOk_of_fields hf hst)

theorem forkIn_pendingOk (program : NCode) (options : Supervision.ForkOptions) (scope key : Nat)
    {a : FAnswer} (ha : ∀ g v, PendingOk g → PendingOk (a g v)) :
    PendingOk (FiberAction.forkIn i m f y program options scope key a).fiber := by
  unfold FiberAction.forkIn
  dsimp only
  have hs : (spawn i m f program { options with daemon := true }).2.1 = f := rfl
  generalize spawn i m f program { options with daemon := true } = s at hs ⊢
  obtain ⟨sm, sf, ch⟩ := s
  dsimp only at hs
  subst hs
  have hst := start_pending sm sf ch options.startImmediately
  generalize start sm sf ch options.startImmediately = t at hst ⊢
  obtain ⟨tm, tf, tn⟩ := t
  dsimp only at hst
  exact ha _ _ (pendingOk_of_fields hf hst)

theorem forkScoped_pendingOk (program : NCode) (options : Supervision.ForkOptions) (key : Nat)
    {a : FAnswer} (ha : ∀ g v, PendingOk g → PendingOk (a g v)) :
    PendingOk (FiberAction.forkScoped i m f y program options key a).fiber := by
  unfold FiberAction.forkScoped
  split
  · dsimp only
    have hs : (spawn i m f program { options with daemon := true }).2.1 = f := rfl
    generalize spawn i m f program { options with daemon := true } = s at hs ⊢
    obtain ⟨sm, sf, ch⟩ := s
    dsimp only at hs
    subst hs
    have hst := start_pending sm sf ch options.startImmediately
    generalize start sm sf ch options.startImmediately = t at hst ⊢
    obtain ⟨tm, tf, tn⟩ := t
    dsimp only at hst
    exact ha _ _ (pendingOk_of_fields hf hst)
  · exact pendingOk_of_fields hf rfl

theorem runIn_pendingOk (target : FiberId) (scope key : Nat) {a : FAnswer}
    (ha : ∀ g v, PendingOk g → PendingOk (a g v)) :
    PendingOk (FiberAction.runIn i m f y target scope key a).fiber := by
  unfold FiberAction.runIn
  generalize linkScope i m Supervision.ScopeMode.fiberRunIn scope key target (some target)
    ReasonAnnotations.empty = r
  obtain ⟨rm, rc⟩ := r
  exact ha _ _ hf

theorem awaitAll_pendingOk (targets : List FiberId) (failFast : Bool) :
    PendingOk (FiberAction.awaitAll i m f y targets failFast).fiber := by
  unfold FiberAction.awaitAll
  have hp := countdownPark_pendingOk i m f targets Resume.exitsValue failFast hf (fun _ h => nomatch h)
  generalize countdownPark i m f targets Resume.exitsValue failFast = r at hp
  obtain ⟨rm, rf, rk⟩ := r
  exact hp

theorem awaitNewChildren_pendingOk (snapshot : List FiberId) :
    PendingOk (FiberAction.awaitNewChildren i m f y snapshot).fiber := by
  unfold FiberAction.awaitNewChildren
  dsimp only
  have hp := countdownPark_pendingOk i m f (f.children.filter fun c => !(snapshot.contains c))
    Resume.void false hf (fun _ h => nomatch h)
  generalize countdownPark i m f (f.children.filter fun c => !(snapshot.contains c)) Resume.void false = r
    at hp
  obtain ⟨rm, rf, rk⟩ := r
  exact hp

theorem closePar_pendingOk (finalizers : List NCode) :
    PendingOk (FiberAction.closePar i m f y finalizers).fiber := by
  unfold FiberAction.closePar
  generalize forkFinalizers i m f finalizers = r
  obtain ⟨rm, rc⟩ := r
  exact hf

end Actions

theorem withFiber_pendingOk (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (action : NAction)
    (hf : PendingOk f) : PendingOk (evaluatePrim.withFiber i m f y action).fiber := by
  have hcore : ∀ (g : FRun) (v : Val), PendingOk g →
      PendingOk (FiberAction.coreAnswer (κ := NCode) (φ := FFiber) g v) :=
    fun _ _ hg => pendingOk_of_fields hg rfl
  cases action with
  | fork program options => exact fork_pendingOk i m f y hf program options hcore
  | forkIn program options scope key => exact forkIn_pendingOk i m f y hf program options scope key hcore
  | forkScoped program options key => exact forkScoped_pendingOk i m f y hf program options key hcore
  | ambientScope =>
    unfold evaluatePrim.withFiber
    dsimp only
    split <;> exact pendingOk_of_fields hf rfl
  | runIn target scope key => exact runIn_pendingOk i m f y hf target scope key hcore
  | interrupt target => exact pendingOk_of_fields hf rfl
  | interruptAs target who => exact interruptAs_pendingOk i m f y target who hf
  | interruptScoped target =>
    unfold evaluatePrim.withFiber
    dsimp only
    split <;> exact pendingOk_of_fields hf rfl
  | interruptAll targets who => exact hf
  | awaitAll targets => exact awaitAll_pendingOk i m f y hf targets false
  | awaitAllFailFast targets => exact awaitAll_pendingOk i m f y hf targets true
  | snapshotChildren => exact pendingOk_of_fields hf rfl
  | awaitNewChildren snapshot => exact awaitNewChildren_pendingOk i m f y hf snapshot
  | raceAll entrants => exact beginRace_pendingOk i m f y entrants hf
  | setInterruptible body flag =>
    cases flag with
    | false => exact pendingOk_of_fields hf rfl
    | true =>
      unfold evaluatePrim.withFiber
      dsimp only
      try split
      all_goals exact pendingOk_of_fields hf rfl
  | setContext context =>
    unfold evaluatePrim.withFiber
    dsimp only
    try split
    all_goals exact pendingOk_of_fields hf rfl
  | getContext => exact pendingOk_of_fields hf rfl
  | getId => exact pendingOk_of_fields hf rfl
  | closeScope scope exit =>
    unfold evaluatePrim.withFiber
    dsimp only
    split
    · exact hf
    · exact pendingOk_of_fields hf rfl
  | closePar finalizers => exact closePar_pendingOk i m f y hf finalizers
  | refuse cause => exact pendingOk_of_fields hf rfl
  | dropObservers token => exact pendingOk_of_fields hf rfl
  | cancelRace raceId =>
    unfold evaluatePrim.withFiber
    dsimp only
    split
    · exact pendingOk_of_fields hf rfl
    · exact hf

theorem evaluatePrim_pendingOk (i : FInterp) (m : FMachine) (f : FRun) (y : Bool) (hf : PendingOk f) :
    PendingOk (evaluatePrim i m f y).fiber := by
  unfold evaluatePrim
  dsimp only
  split
  · exact pendingOk_parkVoid (pendingOk_of_fields hf rfl) _ _ _ _ _
  · split
    · exact pendingOk_of_fields hf rfl
    · split <;> exact pendingOk_parkVoid (pendingOk_of_fields hf rfl) _ _ _ _ _
  · split
    · exact pendingOk_of_fields hf rfl
    · exact registerRace_pendingOk m f y _ hf
    · rename_i targets heq₁
      exact countdownPark_pendingOk i m f targets Resume.exitsValue false hf (fun _ h => nomatch h)
    · split
      · exact hf
      · split
        · exact pendingOk_of_fields hf rfl
        · exact pendingOk_parkVoid (pendingOk_of_fields hf rfl) _ _ _ _ _
    · split
      · split
        · exact withFiber_pendingOk i m f y _ hf
        · exact stepFrame_pendingOk i m f y hf
      · split
        · exact pendingOk_of_fields hf rfl
        · exact pendingOk_of_fields hf rfl
      · exact finalizerOr_pendingOk i m f y _ hf
      · exact finalizerOr_pendingOk i m f y _ hf
      · exact stepFrame_pendingOk i m f y hf

theorem exitScoped_pendingOk (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) (ex : ExitV)
    (hf : PendingOk f) : PendingOk (exitScoped root m f y ex).fiber := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact pendingOk_of_fields hf rfl
    · exact pendingOk_of_fields hf rfl
  · exact evaluatePrim_pendingOk _ m f y hf

theorem evaluateNative_pendingOk (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool)
    (hf : PendingOk f) : PendingOk (evaluateNative root m f y).fiber := by
  unfold evaluateNative
  split
  · split
    · exact pendingOk_of_fields hf rfl
    · exact evaluatePrim_pendingOk _ m f y hf
  · exact exitScoped_pendingOk root m f y _ hf
  · exact exitScoped_pendingOk root m f y _ hf
  · exact evaluatePrim_pendingOk _ m f y hf

theorem iteration_pendingOk (root : NativeEff) (m : FMachine) (f : FRun) (y : Bool) (hf : PendingOk f) :
    letI := evaluatorFor root
    PendingOk (iteration (interpOf root) m f y).fiber := by
  unfold iteration
  dsimp only
  have hf' : PendingOk (countOp (runloopTop f)) := by
    unfold runloopTop countOp
    split <;> exact pendingOk_of_fields hf rfl
  split
  · rename_i it heq
    unfold injectYield at heq
    split at heq
    · cases heq
      exact evaluateNative_pendingOk root _ _ _ (pendingOk_of_fields hf' rfl)
    · cases heq
  · exact evaluateNative_pendingOk root m _ y hf'

end Effect4.Program.Sched

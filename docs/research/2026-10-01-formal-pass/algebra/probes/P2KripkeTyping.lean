import Effect4.Laws.Program.Typed.Stack

/-!
# P2 — Kripke monotonicity of the computation judgments

Formal pass, seat ALGEBRA, 2026-10-01. Three questions about the typed state's judgments, read
against Kripke logical relations (a judgment indexed by a world must survive every later world):

1. `TypedProg` (the protocol typing of a reference program) is world-monotone: the tree carries
   this as the open obligation `M3bWorld.typedProg_mono` (`Typed/Residual.lean:424`, `:455`).
   It holds: `storePre_mono`, `fiberPre_mono` and `typedProg_mono` below.
2. `StackAccepts` (the saved stack's judgment, `Typed/Contracts.lean:32-55`) types each frame's
   continuation at one world only. **Red control:** it is not world-monotone. A frame whose
   continuation misbehaves only on exits that mention a cell the world does not yet declare is
   accepted at `w0` and refused at the later `w1` that declares the cell.
3. The Kripke-closed variant (each continuation clause quantified over later worlds, as
   `TypedProg`'s own clauses and the vocabulary's `continuation` source already are,
   `Typed/Vocabulary.lean:32`) is monotone with no premise, implies `StackAccepts` at every later
   world, and excludes the bad frame.
-/

set_option autoImplicit false

namespace FormalPass.Algebra.P2

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
open Effect4.Program.Typed.Contracts

/-- The typed state's world (the ghost tables over the store), not the machine's handle world. -/
abbrev TW := Effect4.Program.Typed.World

/-! ## 1. `TypedProg` is world-monotone -/

section Mono

variable {w w' : TW}

theorem envTyped_mono (ord : w.leHost w') {env : List Ty} {vals : List Val}
    (h : EnvTyped w env vals) : EnvTyped w' env vals :=
  ⟨h.1, fun i ty v hi hv => fits_mono ord (h.2 i ty v hi hv)⟩

theorem pointTyped_mono (ord : w.leHost w') {src : ProgramSource} {p : Point} {ty : EffTy}
    (h : PointTyped src w p ty) : PointTyped src w' p ty := by
  obtain ⟨e, env, hat, hchk, henv⟩ := h
  exact ⟨e, env, hat, hchk, envTyped_mono ord henv⟩

theorem bodyTyped_mono (ord : w.leHost w') {src : ProgramSource} {b : Body} {ty : EffTy}
    (h : BodyTyped src w b ty) : BodyTyped src w' b ty := by
  cases h with
  | at_ p ty h => exact .at_ p ty (pointTyped_mono ord h)
  | fin name ex ty hex => exact .fin name ex ty (fitsExit_mono ord hex)
  | raceCleanup race => exact .raceCleanup race
  | acquireIn p ctx ty h => exact .acquireIn p ctx ty (pointTyped_mono ord h)
  | release p prev ty h => exact .release p prev ty (pointTyped_mono ord h)
  | layerBuild p m scope ty h => exact .layerBuild p m scope ty (pointTyped_mono ord h)

theorem storePre_mono (root : ProgramSource) (ord : w.leHost w') (op : SyncOp)
    (cert : StoreCert op) (h : storePre root w op cert) : storePre root w' op cert := by
  have hRho : TableExtends w.Ρ w'.Ρ := ord.1.2.2.2.1
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  cases op with
  | refMake initial =>
    simp only [storePre] at h ⊢
    exact ⟨h.1, fits_mono ord h.2⟩
  | refGet cell | refUpdate cell _ | refGetAndUpdate cell _ | refUpdateAndGet cell _
  | refUpdateSome cell _ | refGetAndUpdateSome cell _ | refUpdateSomeAndGet cell _
  | refModify cell _ | refModifySome cell _ =>
    simp only [storePre] at h ⊢
    obtain ⟨ty, hty⟩ := h
    exact ⟨ty, hRho _ _ hty⟩
  | refSet cell v | refGetAndSet cell v | refSetAndGet cell v =>
    simp only [storePre] at h ⊢
    obtain ⟨ty, hty, hv⟩ := h
    exact ⟨ty, hRho _ _ hty, fits_mono ord hv⟩
  | deferredIsDone key | deferredPoll key | deferredAwaitCleanup key _ _
  | deferredCompleteWith key _ | deferredInterruptWith key _ =>
    simp only [storePre] at h ⊢
    exact isSome_extends hPi h
  | deferredMake | memoBuild _ _ | memoGet _ _ => exact h
  | clockNow | sleepCancel _ _ | scopeMake _ | scopeAdd _ _ | scopeRemove _ _ | scopeIsClosed _
  | scopeFork _ _ | memoFork _ | memoComplete _ _ _ | memoRelease _ _ => exact trivial

theorem asyncPre_mono (root : ProgramSource) (ord : w.leHost w') (register : EffName)
    (cert : EffTy) (h : asyncPre root w register cert) : asyncPre root w' register cert := by
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  unfold asyncPre at h ⊢
  split at h
  · exact h
  · obtain ⟨a, e, hc, ha, he⟩ := h
    exact ⟨a, e, hPi _ _ hc, ha, he⟩
  · obtain ⟨a, e, hc, ha, he⟩ := h
    exact ⟨a, e, hPi _ _ hc, ha, he⟩
  · exact h
  · exact h
  · exact h.elim

theorem fiberPre_mono (root : ProgramSource) (ord : w.leHost w') (op : FiberOp)
    (cert : FiberCert op) (h : fiberPre root w op cert) : fiberPre root w' op cert := by
  have hGamma : TableExtends w.Γ w'.Γ := ord.1.2.1
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  have hRho : TableExtends w.Ρ w'.Ρ := ord.1.2.2.2.1
  cases op with
  | fork body _ _ => exact bodyTyped_mono ord h
  | mask _ body => exact bodyTyped_mono ord h
  | forkIn child _ _ _ => exact pointTyped_mono ord h
  | forkScoped child _ _ => exact pointTyped_mono ord h
  | «scoped» body => exact pointTyped_mono ord h
  | gen p => exact pointTyped_mono ord h
  | loop p _ => exact pointTyped_mono ord h
  | await target _ =>
    simp only [fiberPre] at h ⊢
    exact isSome_extends hGamma h
  | awaitAll targets | awaitAllFailFast targets =>
    simp only [fiberPre] at h ⊢
    obtain ⟨a, e, hc, hall⟩ := h
    refine ⟨a, e, hc, fun t ht => ?_⟩
    obtain ⟨fty, hf, ha, he⟩ := hall t ht
    exact ⟨fty, hGamma _ _ hf, ha, he⟩
  | raceAll entrants _ =>
    simp only [fiberPre] at h ⊢
    intro p hp
    obtain ⟨ty, hpt, ha, he⟩ := h p hp
    exact ⟨ty, pointTyped_mono ord hpt, ha, he⟩
  | async register _ => exact asyncPre_mono root ord register cert h
  | setContext ctx =>
    simp only [fiberPre] at h ⊢
    exact servicesFit_map hPi hRho ord.2 h
  | getContext | snapshotChildren => exact h
  | refuse _ => exact (h : False).elim
  | getId | yieldNow _ | ambientScope | sync _ | suspend _ | interrupt _ | interruptAs _ _
  | interruptScoped _ | interruptAll _ _ | runIn _ _ | awaitNewChildren _ | guard_ _ | unguard _
  | finishFinalizer _ | scopeExit _ _ _ | construction | closeScope _ _ | foreignRelease _ _
  | closeWalk _ _ _ | closeIter _ _ _ | raceRegister _ | cancelRace _ | dropObservers _
  | frontier _ _ => exact trivial

end Mono

/-- **`TypedProg` is world-monotone** (closes `M3bWorld.typedProg_mono`). Every continuation
clause already quantifies over later worlds, so only the leaves, the demands and the guard's
body need transport; the demands are upward closed by `storePre_mono` and `fiberPre_mono`. -/
theorem typedProg_mono (root : ProgramSource) {w : TW} {ty : EffTy} {p : RProgram}
    (h : TypedProg root w ty p) : ∀ {w' : TW}, w.leHost w' → TypedProg root w' ty p := by
  induction h with
  | pure exit =>
    intro w' ord
    exact .pure (fitsExit_mono ord exit)
  | store cert pre next _ =>
    intro w' ord
    exact .store cert (storePre_mono root ord _ cert pre)
      (fun w'' ord' ans post => next w'' (leHost_trans _ _ _ ord ord') ans post)
  | fiber notGuard notUnguard notFinish notScopeExit cert pre next _ =>
    intro w' ord
    exact .fiber notGuard notUnguard notFinish notScopeExit cert (fiberPre_mono root ord _ cert pre)
      (fun w'' ord' ans post => next w'' (leHost_trans _ _ _ ord ord') ans post)
  | guard mid _ run skip ihBody _ =>
    intro w' ord
    exact .guard mid (ihBody ord)
      (fun w'' ord' ex post => run w'' (leHost_trans _ _ _ ord ord') ex post)
      (fun w'' ord' ex hfit harm => skip w'' (leHost_trans _ _ _ ord ord') ex hfit harm)
  | unguard payload =>
    intro w' ord
    exact .unguard (fitsExit_mono ord payload)
  | finishFinalizer payload =>
    intro w' ord
    exact .finishFinalizer (fitsExit_mono ord payload)
  | scopeExit payload next _ =>
    intro w' ord
    exact .scopeExit (fitsExit_mono ord payload)
      (fun w'' ord' ans => next w'' (leHost_trans _ _ _ ord ord') ans)

/-! ## 2. Red control: `StackAccepts` is not world-monotone -/

/-- The empty world. -/
def w0 : TW :=
  { ids := [], state := Stores.empty, Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := fun _ => none, Θ := fun _ _ => none }

/-- The same world after allocating cell 0 at `nat`. -/
def s1 : Stores := { Stores.empty with refs := [Val.nat 0] }

def w1 : TW :=
  { ids := [], state := s1, Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := fun k => if k = ⟨0⟩ then some .nat else none, Θ := fun _ _ => none }

theorem w0_le_w1 : w0.leHost w1 := by
  have hst : Stores.le w0.state w1.state :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩
  have hrho : TableExtends w0.Ρ w1.Ρ := fun _ _ h => by cases h
  have hcells : CellCompatible w0 w1 := by
    unfold CellCompatible
    refine ⟨fun _ _ h => ?_, fun _ _ h => ?_⟩
    · unfold HeapTypedAt at h
      cases h.1
    · unfold PromiseTypedAt at h
      cases h.1
  exact ⟨⟨⟨fun _ h => h, hst⟩, fun _ _ h => h, fun _ _ h => h, hrho, hcells,
    fun _ _ _ h => h⟩, fun _ _ h => h⟩

/-- The frame's input type: a cell at `nat`; its output: `unit`. -/
abbrev tin : EffTy := EffTy.pure (.refOf .nat)
abbrev tout : EffTy := EffTy.pure .unit

/-- A continuation that answers `"x"` (not a `unit`) on every success and passes failures on.
At `w0` no success fits `tin`, so the bad branch is never demanded. -/
def badNext : ExitV → RProgram
  | .success _ => .pure (.success (Val.str "x"))
  | .failure c => .pure (.failure c)

theorem bad_accepted_at_w0 (root : ProgramSource) :
    StackAccepts (TypedProg root) FitsExit (frameProtocols root) w0 tin tout [.answer badNext] := by
  refine .cons (.answer badNext fun ex hex => ?_) (.nil tout)
  cases ex with
  | success v =>
    exfalso
    rw [fitsExit_success_iff] at hex
    change Typed.Fits w0 v (.refOf .nat) at hex
    simp only [Typed.Fits] at hex
    split at hex
    · obtain ⟨t', ht, _⟩ := hex
      cases ht
    · exact hex
  | failure c =>
    refine .pure ?_
    rw [fitsExit_failure_iff] at hex ⊢
    exact hex

theorem cell0_fits_w1 : FitsExit w1 tin (.success (Val.cell ⟨0⟩)) := by
  rw [fitsExit_success_iff]
  change Typed.Fits w1 (Val.cell ⟨0⟩) (.refOf .nat)
  simp only [Typed.Fits]
  exact ⟨.nat, by simp only [w1, if_pos], Ty.sub_refl _, Ty.sub_refl _⟩

theorem bad_refused_at_w1 (root : ProgramSource) :
    ¬ StackAccepts (TypedProg root) FitsExit (frameProtocols root) w1 tin tout [.answer badNext] := by
  intro h
  cases h with
  | cons head tail =>
    cases tail
    cases head with
    | answer next run =>
      have hp := TypedProg.pure_inv (run (.success (Val.cell ⟨0⟩)) cell0_fits_w1)
      rw [fitsExit_success_iff] at hp
      change Typed.Fits w1 (Val.str "x") .unit at hp
      simp only [Typed.Fits] at hp

/-- **World weakening fails for the saved-stack judgment.** -/
theorem stackAccepts_not_mono (root : ProgramSource) :
    ∃ (w w' : TW) (a b : EffTy) (s : List ScopeFrame), w.leHost w' ∧
      StackAccepts (TypedProg root) FitsExit (frameProtocols root) w a b s ∧
      ¬ StackAccepts (TypedProg root) FitsExit (frameProtocols root) w' a b s :=
  ⟨w0, w1, tin, tout, [.answer badNext], w0_le_w1, bad_accepted_at_w0 root, bad_refused_at_w1 root⟩

/-! ## 3. The Kripke-closed frame judgment is monotone and excludes the bad frame -/

section Kripke

variable (TP : TW → EffTy → RProgram → Prop) (Ex : TW → EffTy → ExitV → Prop)
  (hooks : FrameProtocols)

/-- `FrameAccepts` with every world-reading clause quantified over later worlds. -/
inductive FrameAcceptsK (w : TW) : EffTy → EffTy → ScopeFrame → Prop
  | resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → kind.hasExitArm ex = true →
        TP w' tout (next ex))
      (skip : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → kind.hasExitArm ex = false →
        Ex w' tout ex) :
      FrameAcceptsK w tin tout (.resume kind next)
  | answer {tin tout : EffTy} (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → TP w' tout (next ex)) :
      FrameAcceptsK w tin tout (.answer next)
  | restoreMask (ty : EffTy) (flag : Bool) : FrameAcceptsK w ty ty (.restoreMask flag)
  | asyncFinalizer {tin tout : EffTy} (name : EffName)
      (protocol : ∀ w', w.leHost w' → hooks.asyncFinalizer w' tin tout name) :
      FrameAcceptsK w tin tout (.asyncFinalizer name)
  | finalizerMask (ty : EffTy) (flag : Bool) : FrameAcceptsK w ty ty (.finalizerMask flag)
  | iter {tin tout : EffTy} (name : EffName)
      (protocol : ∀ w', w.leHost w' → hooks.iterator w' tin tout name) :
      FrameAcceptsK w tin tout (.iter name)
  | loop {tin tout : EffTy} (name : EffName) (cursor : Val)
      (protocol : ∀ w', w.leHost w' → hooks.loop w' tin tout name cursor) :
      FrameAcceptsK w tin tout (.loop name cursor)

inductive StackAcceptsK (w : TW) : EffTy → EffTy → List ScopeFrame → Prop
  | nil (ty : EffTy) : StackAcceptsK w ty ty []
  | cons {tin middle tout : EffTy} {frame : ScopeFrame} {rest : List ScopeFrame}
      (head : FrameAcceptsK TP Ex hooks w tin middle frame)
      (tail : StackAcceptsK w middle tout rest) : StackAcceptsK w tin tout (frame :: rest)

variable {TP Ex hooks}

theorem frameAcceptsK_mono {w w' : TW} (ord : w.leHost w') {a b : EffTy} {f : ScopeFrame}
    (h : FrameAcceptsK TP Ex hooks w a b f) : FrameAcceptsK TP Ex hooks w' a b f := by
  cases h with
  | resume kind next run skip =>
    exact .resume kind next (fun w'' o ex hx hk => run w'' (leHost_trans _ _ _ ord o) ex hx hk)
      (fun w'' o ex hx hk => skip w'' (leHost_trans _ _ _ ord o) ex hx hk)
  | answer next run => exact .answer next (fun w'' o ex hx => run w'' (leHost_trans _ _ _ ord o) ex hx)
  | restoreMask flag => exact .restoreMask _ flag
  | asyncFinalizer name protocol =>
    exact .asyncFinalizer name (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o))
  | finalizerMask flag => exact .finalizerMask _ flag
  | iter name protocol => exact .iter name (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o))
  | loop name cursor protocol =>
    exact .loop name cursor (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o))

/-- **The Kripke-closed stack judgment is world-monotone**, with no premise on `TP`, `Ex` or
the hooks: only the preorder laws of the host world order. -/
theorem stackAcceptsK_mono {w w' : TW} (ord : w.leHost w') {a b : EffTy} {s : List ScopeFrame}
    (h : StackAcceptsK TP Ex hooks w a b s) : StackAcceptsK TP Ex hooks w' a b s := by
  induction h with
  | nil ty => exact .nil ty
  | cons head _ ih => exact .cons (frameAcceptsK_mono ord head) ih

theorem frameAcceptsK_now {w : TW} {a b : EffTy} {f : ScopeFrame}
    (h : FrameAcceptsK TP Ex hooks w a b f) : FrameAccepts TP Ex hooks w a b f := by
  cases h with
  | resume kind next run skip =>
    exact .resume kind next (run w (leHost_refl w)) (skip w (leHost_refl w))
  | answer next run => exact .answer next (run w (leHost_refl w))
  | restoreMask flag => exact .restoreMask _ flag
  | asyncFinalizer name protocol => exact .asyncFinalizer name (protocol w (leHost_refl w))
  | finalizerMask flag => exact .finalizerMask _ flag
  | iter name protocol => exact .iter name (protocol w (leHost_refl w))
  | loop name cursor protocol => exact .loop name cursor (protocol w (leHost_refl w))

/-- The Kripke judgment gives the current judgment at the current world, so the stack walk
(`popR_typed`, stated at one world) applies unchanged. -/
theorem stackAcceptsK_now {w : TW} {a b : EffTy} {s : List ScopeFrame}
    (h : StackAcceptsK TP Ex hooks w a b s) : StackAccepts TP Ex hooks w a b s := by
  induction h with
  | nil ty => exact .nil ty
  | cons head _ ih => exact .cons (frameAcceptsK_now head) ih

end Kripke

/-- The Kripke judgment refuses the bad frame already at `w0`. -/
theorem bad_not_kripke (root : ProgramSource) :
    ¬ StackAcceptsK (TypedProg root) FitsExit (frameProtocols root) w0 tin tout [.answer badNext] :=
  fun h => bad_refused_at_w1 root (stackAcceptsK_now (stackAcceptsK_mono w0_le_w1 h))

end FormalPass.Algebra.P2

#print axioms FormalPass.Algebra.P2.storePre_mono
#print axioms FormalPass.Algebra.P2.fiberPre_mono
#print axioms FormalPass.Algebra.P2.typedProg_mono
#print axioms FormalPass.Algebra.P2.stackAccepts_not_mono
#print axioms FormalPass.Algebra.P2.stackAcceptsK_mono
#print axioms FormalPass.Algebra.P2.stackAcceptsK_now
#print axioms FormalPass.Algebra.P2.bad_not_kripke
#print axioms FormalPass.Algebra.P2.envTyped_mono
#print axioms FormalPass.Algebra.P2.pointTyped_mono
#print axioms FormalPass.Algebra.P2.bodyTyped_mono
#print axioms FormalPass.Algebra.P2.asyncPre_mono
#print axioms FormalPass.Algebra.P2.w0_le_w1
#print axioms FormalPass.Algebra.P2.bad_accepted_at_w0
#print axioms FormalPass.Algebra.P2.bad_refused_at_w1
#print axioms FormalPass.Algebra.P2.frameAcceptsK_mono
#print axioms FormalPass.Algebra.P2.frameAcceptsK_now

-- Synthesis seat port to the merged head (0c534f06) of seat ALGEBRA's P2 §1 (typedProg_mono): exits read through H2's ExitOk.
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

namespace Research.Synthesis.HeadTypedProgMono

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
  | fin name ex ty hex => exact .fin name ex ty (strongExit_mono _ _ _ _ ord hex)
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
    exact .pure (strongExit_mono _ _ _ _ ord exit)
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
    exact .unguard (strongExit_mono _ _ _ _ ord payload)
  | finishFinalizer payload =>
    intro w' ord
    exact .finishFinalizer (strongExit_mono _ _ _ _ ord payload)
  | scopeExit payload next _ =>
    intro w' ord
    exact .scopeExit (strongExit_mono _ _ _ _ ord payload)
      (fun w'' ord' ans => next w'' (leHost_trans _ _ _ ord ord') ans)

/-- The ledger's own statement shape (`M3bWorld.typedProg_mono`, binder order `w w' ty p`). -/
theorem typedProg_mono_ledger (root : ProgramSource) (w w' : TW) (ty : EffTy) (p : RProgram) :
    w.leHost w' → TypedProg root w ty p → TypedProg root w' ty p :=
  fun ord h => typedProg_mono root h ord

end Research.Synthesis.HeadTypedProgMono

#print axioms Research.Synthesis.HeadTypedProgMono.storePre_mono
#print axioms Research.Synthesis.HeadTypedProgMono.fiberPre_mono
#print axioms Research.Synthesis.HeadTypedProgMono.typedProg_mono
#print axioms Research.Synthesis.HeadTypedProgMono.typedProg_mono_ledger

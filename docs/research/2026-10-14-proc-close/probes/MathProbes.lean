import Effect4.Laws.Program.BlockMeaning
import Effect4.Laws.Program.HostRuns
import Effect4.Laws.Library.Ref.Operations
import Effect4.Laws.Library.Queue.Steps
import Effect4.Laws.Library.Semaphore.Steps
import Test.Dogfood.Scenario.Todo.Cached
import Test.Dogfood.Scenario.QueueWorkers
import ProofGraph.Plan

/-!
# Mathematical Probes for Round 2 Review (2026-10-14)

Probes testing Q1, Q2, Q3, Q4, Q7, Q8, and Q9 of `gemini-math-review-prompt.md`
against the current Lean tree at `b2a1e3c15`.
-/

set_option autoImplicit false

namespace Effect4.Probes.MathReview

open Effect4
open Effect4.Machine
open Effect4.Program
open Effect4.Program.Denote
open Effect4.Modules (Table)
open Effect4.Store (Image)

/-! ## Probe 1 (Q1): Peeling `StoreSig` and Relational Tree Simulation `PeelSim` / `RefinesB` -/

/-- Relational step lift over `RowSig table` after peeling `StoreSig` via `Effects.Program.peel storeStep`.
    A budget frontier `.done (none, s₁)` on the left is treated as a directed bottom element `⊥`:
    it places no requirement on the right-hand step, because `RefinesB` quantifies `∀ k, ∃ k'`
    and a finite budget cut may stop inside a critical section before `onExit` runs.
    A completed exit `.done (some ex₁, s₁)` must be matched by `.done (some ex₂, s₂)` under `R_out`.
    A visible host call `.call op k₁` must be matched by `.call op k₂` with related continuations. -/
def PeelStepRel {table : RowTable} {S₁ S₂ : Type} {X₁ X₂ : Type}
    (R_out : (ExitV × S₁) → (ExitV × S₂) → Prop)
    (R : X₁ → X₂ → Prop) :
    Effects.Step (RowSig table) (Option ExitV × S₁) X₁ →
    Effects.Step (RowSig table) (Option ExitV × S₂) X₂ → Prop
  | .done (none, _), _ => True
  | .done (some ex₁, s₁), .done (some ex₂, s₂) => R_out (ex₁, s₁) (ex₂, s₂)
  | .call op₁ k₁, .call op₂ k₂ =>
      ∃ h : op₁ = op₂, ∀ r, R (k₁ r) (k₂ (h ▸ r))
  | _, _ => False

/-- Bounded relational simulation on programs over `RowsSig table` paired with abstract store states,
    stepping via custom store handlers `step₁` and `step₂` through `Effects.Program.peel`. -/
def PeelSimAt {table : RowTable} {S₁ S₂ : Type}
    (step₁ : (o : StoreSig.Op) → S₁ → StoreSig.Answer o × S₁)
    (step₂ : (o : StoreSig.Op) → S₂ → StoreSig.Answer o × S₂)
    (R_out : (ExitV × S₁) → (ExitV × S₂) → Prop) :
    Nat →
    (Effects.Program (RowsSig table) (Option ExitV) × S₁) →
    (Effects.Program (RowsSig table) (Option ExitV) × S₂) → Prop
  | 0, _, _ => True
  | n + 1, (p₁, s₁), (p₂, s₂) =>
      PeelStepRel R_out (PeelSimAt step₁ step₂ R_out n)
        (p₁.peel step₁ s₁) (p₂.peel step₂ s₂)

/-- Full relational simulation on peeled `RowSig table` interaction trees. -/
def PeelSim {table : RowTable} {S₁ S₂ : Type}
    (step₁ : (o : StoreSig.Op) → S₁ → StoreSig.Answer o × S₁)
    (step₂ : (o : StoreSig.Op) → S₂ → StoreSig.Answer o × S₂)
    (R_out : (ExitV × S₁) → (ExitV × S₂) → Prop)
    (ps₁ : Effects.Program (RowsSig table) (Option ExitV) × S₁)
    (ps₂ : Effects.Program (RowsSig table) (Option ExitV) × S₂) : Prop :=
  ∀ n, PeelSimAt step₁ step₂ R_out n ps₁ ps₂

theorem PeelSimAt.refl {table : RowTable} {S : Type}
    (step : (o : StoreSig.Op) → S → StoreSig.Answer o × S)
    {R_out : (ExitV × S) → (ExitV × S) → Prop}
    (hRefl : ∀ x, R_out x x) :
    ∀ n (ps : Effects.Program (RowsSig table) (Option ExitV) × S),
      PeelSimAt step step R_out n ps ps
  | 0, _ => trivial
  | n + 1, (p, s) => by
      simp only [PeelSimAt]
      rcases hp : p.peel step s with ⟨o, s'⟩ | ⟨op, k⟩
      · cases o with
        | none => trivial
        | some ex => exact hRefl (ex, s')
      · exact ⟨rfl, fun r => PeelSimAt.refl step hRefl n (k r)⟩

/-- Relational composition of terminal relations. -/
def RelComp {A B C : Type} (R₁₂ : A → B → Prop) (R₂₃ : B → C → Prop) (a : A) (c : C) : Prop :=
  ∃ b, R₁₂ a b ∧ R₂₃ b c

/-- `PeelSimAt` composes transitively along `RelComp R₁₂ R₂₃`. -/
theorem PeelSimAt.comp {table : RowTable} {S₁ S₂ S₃ : Type}
    {step₁ : (o : StoreSig.Op) → S₁ → StoreSig.Answer o × S₁}
    {step₂ : (o : StoreSig.Op) → S₂ → StoreSig.Answer o × S₂}
    {step₃ : (o : StoreSig.Op) → S₃ → StoreSig.Answer o × S₃}
    {R₁₂ : (ExitV × S₁) → (ExitV × S₂) → Prop}
    {R₂₃ : (ExitV × S₂) → (ExitV × S₃) → Prop} :
    ∀ n {ps₁ : Effects.Program (RowsSig table) (Option ExitV) × S₁}
        {ps₂ : Effects.Program (RowsSig table) (Option ExitV) × S₂}
        {ps₃ : Effects.Program (RowsSig table) (Option ExitV) × S₃},
      PeelSimAt step₁ step₂ R₁₂ n ps₁ ps₂ →
      PeelSimAt step₂ step₃ R₂₃ n ps₂ ps₃ →
      PeelSimAt step₁ step₃ (RelComp R₁₂ R₂₃) n ps₁ ps₃
  | 0, _, _, _, _, _ => trivial
  | n + 1, (p₁, s₁), (p₂, s₂), (p₃, s₃), h₁₂, h₂₃ => by
      simp only [PeelSimAt] at h₁₂ h₂₃ ⊢
      rcases hp₁ : p₁.peel step₁ s₁ with ⟨o₁, s₁'⟩ | ⟨op₁, k₁⟩
      · cases o₁ with
        | none => trivial
        | some ex₁ =>
          rw [hp₁] at h₁₂
          rcases hp₂ : p₂.peel step₂ s₂ with ⟨o₂, s₂'⟩ | ⟨op₂, k₂⟩
          · cases o₂ with
            | none => rw [hp₂] at h₁₂; cases h₁₂
            | some ex₂ =>
              rw [hp₂] at h₁₂ h₂₃
              rcases hp₃ : p₃.peel step₃ s₃ with ⟨o₃, s₃'⟩ | ⟨op₃, k₃⟩
              · cases o₃ with
                | none => rw [hp₃] at h₂₃; cases h₂₃
                | some ex₃ =>
                  rw [hp₃] at h₂₃
                  exact ⟨(ex₂, s₂'), h₁₂, h₂₃⟩
              · rw [hp₃] at h₂₃; cases h₂₃
          · rw [hp₂] at h₁₂; cases h₁₂
      · rw [hp₁] at h₁₂
        rcases hp₂ : p₂.peel step₂ s₂ with ⟨_, _⟩ | ⟨op₂, k₂⟩
        · rw [hp₂] at h₁₂; cases h₁₂
        · rw [hp₂] at h₁₂ h₂₃
          rcases hp₃ : p₃.peel step₃ s₃ with ⟨_, _⟩ | ⟨op₃, k₃⟩
          · rw [hp₃] at h₂₃; cases h₂₃
          · rw [hp₃] at h₂₃
            obtain ⟨h₁, hk₁⟩ := h₁₂
            obtain ⟨h₂, hk₂⟩ := h₂₃
            subst h₁; subst h₂
            exact ⟨rfl, fun r => PeelSimAt.comp n (hk₁ r) (hk₂ r)⟩

theorem PeelSim.comp {table : RowTable} {S₁ S₂ S₃ : Type}
    {step₁ : (o : StoreSig.Op) → S₁ → StoreSig.Answer o × S₁}
    {step₂ : (o : StoreSig.Op) → S₂ → StoreSig.Answer o × S₂}
    {step₃ : (o : StoreSig.Op) → S₃ → StoreSig.Answer o × S₃}
    {R₁₂ : (ExitV × S₁) → (ExitV × S₂) → Prop}
    {R₂₃ : (ExitV × S₂) → (ExitV × S₃) → Prop}
    {ps₁ : Effects.Program (RowsSig table) (Option ExitV) × S₁}
    {ps₂ : Effects.Program (RowsSig table) (Option ExitV) × S₂}
    {ps₃ : Effects.Program (RowsSig table) (Option ExitV) × S₃}
    (h₁₂ : PeelSim step₁ step₂ R₁₂ ps₁ ps₂)
    (h₂₃ : PeelSim step₂ step₃ R₂₃ ps₂ ps₃) :
    PeelSim step₁ step₃ (RelComp R₁₂ R₂₃) ps₁ ps₃ :=
  fun n => PeelSimAt.comp n (h₁₂ n) (h₂₃ n)

/-- `PeelSim` implies the host-comodel refinement order of decisions row 383 (1)
    for every host comodel `host : Effects.Comodel (RowSig table) σ`. -/
theorem PeelSim.sound_host {table : RowTable} {S₁ S₂ σ : Type}
    {step₁ : (o : StoreSig.Op) → S₁ → StoreSig.Answer o × S₁}
    {step₂ : (o : StoreSig.Op) → S₂ → StoreSig.Answer o × S₂}
    {R_out : (ExitV × S₁) → (ExitV × S₂) → Prop}
    (host : Effects.Comodel (RowSig table) σ) :
    ∀ (depth : Nat)
      {p₁ : Effects.Program (RowsSig table) (Option ExitV)} {s₁ : S₁}
      {p₂ : Effects.Program (RowsSig table) (Option ExitV)} {s₂ : S₂}
      (st : σ),
      PeelSimAt step₁ step₂ R_out depth (p₁, s₁) (p₂, s₂) →
      ∀ ex₁ s₁' st',
        (Effects.System.peel step₁).run host depth (p₁, s₁) st =
          some (some (some ex₁, s₁'), st') →
        ∃ ex₂ s₂',
          ((Effects.Comodel.ofTotal step₂).route host).run p₂ (s₂, st) =
            some (some ex₂, (s₂', st')) ∧
          R_out (ex₁, s₁') (ex₂, s₂')
  | 0, _, _, _, _, _, _, _, _, _, hRun => by
      simp only [Effects.System.run, Effects.System.unfold_zero, Effects.Comodel.run_pure,
        Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at hRun
  | depth + 1, p₁, s₁, p₂, s₂, st, hSim, ex₁, s₁', st', hRun => by
      simp only [PeelSimAt] at hSim
      rw [Effects.Program.run_route_peel]
      rcases hp₁ : p₁.peel step₁ s₁ with ⟨o₁, s₁₀⟩ | ⟨op₁, k₁⟩
      · cases o₁ with
        | none =>
          have hu := Effects.System.unfold_done (system := Effects.System.peel step₁)
            (state := (p₁, s₁))
            (show Effects.System.peel step₁ (p₁, s₁) = some (.done (none, s₁₀)) by
              show some (p₁.peel step₁ s₁) = _; rw [hp₁]) depth
          rw [Effects.System.run, hu, Effects.Comodel.run_pure] at hRun
          simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at hRun
        | some ex₁₀ =>
          rw [hp₁] at hSim
          have hu := Effects.System.unfold_done (system := Effects.System.peel step₁)
            (state := (p₁, s₁))
            (show Effects.System.peel step₁ (p₁, s₁) = some (.done (some ex₁₀, s₁₀)) by
              show some (p₁.peel step₁ s₁) = _; rw [hp₁]) depth
          rw [Effects.System.run, hu, Effects.Comodel.run_pure] at hRun
          simp only [Option.some.injEq, Prod.mk.injEq] at hRun
          obtain ⟨⟨⟨rfl⟩, rfl⟩, rfl⟩ := hRun
          rcases hp₂ : p₂.peel step₂ s₂ with ⟨o₂, s₂₀⟩ | ⟨op₂, k₂⟩
          · cases o₂ with
            | none => rw [hp₂] at hSim; cases hSim
            | some ex₂₀ =>
              rw [hp₂] at hSim
              exact ⟨ex₂₀, s₂₀, rfl, hSim⟩
          · rw [hp₂] at hSim; cases hSim
      · rw [hp₁] at hSim
        rcases hp₂ : p₂.peel step₂ s₂ with ⟨_, _⟩ | ⟨op₂, k₂⟩
        · rw [hp₂] at hSim; cases hSim
        · rw [hp₂] at hSim
          obtain ⟨hOp, hk⟩ := hSim
          subst hOp
          have hu := Effects.System.unfold_call (system := Effects.System.peel step₁)
            (state := (p₁, s₁))
            (show Effects.System.peel step₁ (p₁, s₁) = some (.call op₁ k₁) by
              show some (p₁.peel step₁ s₁) = _; rw [hp₁]) depth
          rw [Effects.System.run, hu] at hRun
          rcases ha : host.answer op₁ st with _ | ⟨reply, st₁⟩
          · rw [Effects.Comodel.run_vis_none _ _ ha] at hRun
            cases hRun
          · rw [Effects.Comodel.run_vis_some _ _ ha] at hRun
            dsimp only
            rw [ha]
            exact PeelSim.sound_host host depth st₁ (hk reply) ex₁ s₁' st' hRun

/-! ## Probe 2 (Q2): `blockAlgB` maps mask constructors to `outsideExit` -/

/-- `denoteBlockB` maps `uninterruptible` (used by `Semaphore.withPermits`,
    `SynchronizedRef.modify`, and `Queue.poll`) to `outsideExit` even on a single fiber. -/
theorem denoteBlockB_uninterruptible_is_outsideExit (table : RowTable) (bodies : List NativeEff)
    (k : Nat) (ctx : Ctx) (env : List Val) :
    denoteBlockB table bodies (k + 1) [] (.uninterruptible (.succeed (.var 0))) ctx env =
    pure (some outsideExit) := rfl

-- `bodyRowsAlg` currently rejects `uninterruptible`, `restore`, and `getInterruptible` as `false`.
#guard (bodyRowsAlg []).eff_uninterruptible true == false
#guard (bodyRowsAlg []).eff_restore (.var 0) true == false
#guard (bodyRowsAlg []).action_getInterruptible == false

/-! ## Probe 3 (Q3): Waiting `waitRetry` is a 3-action protocol, not 2-phase commit-on-resolve -/

section WaitRetryCounterexamples

/-- In `Queue.Model`:
    1. Waiter `id = 1` calls `take` on an empty queue (`q0`) and enrols (`TakeReply.wait`).
    2. Producer `id = 2` calls `offer q1 2 42`: the item `42` stays in `q2.messages = [42]`,
       waiter `1` stays in `q2.takers`, and `offer` emits `[⟨1, .again⟩]` (`OfferReply.accepted true`).
       Thus the wake signal in `offer` does NOT transfer `42` or remove waiter `1`. -/
def q0 : Queue.Model.State := { capacity := some 1 }
def qStep1 := Queue.Model.take q0 ⟨1, 1, 1⟩
def qStep2 := Queue.Model.offer qStep1.1 2 42

#guard qStep1.2.1 == .wait
#guard qStep2.2.1 == .accepted true
#guard qStep2.2.2 == [⟨1, .again⟩]
#guard qStep2.1.messages == [42]
#guard qStep2.1.takers == [⟨1, 1, 1⟩]

/-- In `Semaphore.Model`:
    1. Fiber 1 holds the 1 permit of `s0 = initial 1` (`s1`).
    2. Waiter `id = 2` calls `take s1 2 1` and enrols at stamp 0 (`false`).
    3. Fiber 1 calls `release s2 1` (`taken = 0`) and the wake helper calls `visit s3 0`:
       waiter `2` is popped and woken (`some ⟨2, 1, 0⟩`), while `taken` remains `0` ("A wake reserves nothing").
    4. An intervening fiber calls `takeIfAvailable s4 1` and takes the permit (`true`, `taken = 1`).
    5. When woken waiter `2` retries `take s5 2 1`, `free s5 = 0`, so waiter `2` returns `false`
       and re-enrols at stamp 1 (`[⟨2, 1, 1⟩]`). -/
def s0 : Semaphore.Model.State := Semaphore.Model.initial 1
def s1 := (Semaphore.Model.take s0 1 1).1
def s2 := Semaphore.Model.take s1 2 1
def s3 := (Semaphore.Model.release s2.1 1).1
def s4 := Semaphore.Model.visit s3 0
def s5 := Semaphore.Model.takeIfAvailable s4.1 1
def s6 := Semaphore.Model.take s5.1 2 1

#guard s2.2 == false
#guard s4.2 == some ⟨2, 1, 0⟩
#guard s4.1.taken == 0
#guard s5.2 == true
#guard s6.2 == false
#guard s6.1.waiters == [⟨2, 1, 1⟩]

end WaitRetryCounterexamples

/-! ## Probe 4 (Q4): Handle Renaming Invariance of `NativeAtom.sameHandle` -/

/-- `NativeAtom.eval .sameHandle` is invariant under any handle-kind-preserving
    bijection `π : UInt8 → Nat → Nat` on `Store.Val.handle`. -/
theorem sameHandle_renaming_invariant
    (π : UInt8 → Nat → Nat)
    (hInj : ∀ k n₁ n₂, π k n₁ = π k n₂ → n₁ = n₂)
    (k₁ k₂ : UInt8) (n₁ n₂ : Nat) :
    NativeAtom.eval .sameHandle [Store.Val.handle k₁ (π k₁ n₁), Store.Val.handle k₂ (π k₂ n₂)] =
    NativeAtom.eval .sameHandle [Store.Val.handle k₁ n₁, Store.Val.handle k₂ n₂] := by
  simp only [NativeAtom.eval]
  by_cases hk : k₁ = k₂
  · subst hk
    have hProp : (π k₁ n₁ = π k₁ n₂) ↔ (n₁ = n₂) :=
      ⟨hInj k₁ n₁ n₂, fun h => congrArg (π k₁) h⟩
    simp only [↓reduceIte, decide_eq_decide.mpr hProp]
  · simp only [hk, ↓reduceIte]

/-! ## Probe 5 (Q7): Unified `ObjectSpec` and `StepsAgree` with `Ref` Instance -/

/-- Unified specification of a single-cell state / synchronization object over `Stores`. -/
structure ObjectSpec (Op : Type) where
  State : Type
  Reply : Op → Type
  Profile : State → Prop
  cellVal : Table → State → Val
  step : (op : Op) → Table → State → Table × State × Reply op
  replyRel : (op : Op) → Table → Reply op → Val → Prop
  opStore : (op : Op) → RefKey → Stores → Option (Stores × Val)

/-- Unified `StepsAgree`: running `opStore op q` on a store whose cell `q` holds
    `cellVal tb s` updates cell `q` to `cellVal tb' s'` (via `refWriteBack`) and returns
    a value related to `r` by `replyRel op tb' r`, while leaving all other cells and `deferreds` untouched. -/
def ObjectSpec.StepsAgree {Op : Type} (M : ObjectSpec Op) : Prop :=
  ∀ (op : Op) (tb : Table) (s : M.State)
    (stores : Stores) (q : RefKey),
    M.Profile s →
    refPeek stores.refs q = some (M.cellVal tb s) →
    let (tb', s', r) := M.step op tb s
    ∃ (w : Option Val) (v : Val),
      M.opStore op q stores =
        some ({ stores with refs := refWriteBack stores.refs q w }, v) ∧
      w.getD (M.cellVal tb s) = M.cellVal tb' s' ∧
      M.Profile s' ∧
      M.replyRel op tb' r v

/-- Concrete instance of `ObjectSpec` for `Effect4.Ref` (`get`, `getAndSet`),
    witnessed directly by the proved `Ref.ref_steps_agree` in `Effect4.Laws.Library.Ref.Operations`. -/
inductive RefOp (α : Type) where
  | get
  | getAndSet (a : α)

def refObjectSpec {α : Type} (I : Image α) : ObjectSpec (RefOp α) where
  State := α
  Reply
    | .get => α
    | .getAndSet _ => α
  Profile := fun _ => True
  cellVal := fun _ a => I.toVal a
  step
    | .get, tb, a => (tb, a, a)
    | .getAndSet a', tb, a => (tb, a', a)
  replyRel
    | .get, _, a, v => v = I.toVal a
    | .getAndSet _, _, a, v => v = I.toVal a
  opStore
    | .get, q, stores => syncOpStep (.refGet q) stores
    | .getAndSet a', q, stores => syncOpStep (.refGetAndSet q (I.toVal a')) stores

theorem refObjectSpec_stepsAgree {α : Type} (I : Image α) :
    (refObjectSpec I).StepsAgree := by
  intro op tb a stores q _ hCell
  have hRef := Effect4.Ref.ref_steps_agree
  cases op with
  | get =>
      exact ⟨none, I.toVal a, hRef.get I a hCell, rfl, trivial, rfl⟩
  | getAndSet a' =>
      exact ⟨some (I.toVal a'), I.toVal a, hRef.getAndSet I a hCell a', rfl, trivial, rfl⟩

/-! ## Probe 6 (Q8 & Q9): Plan Status Check on `Todo.Cached` and `QueueWorkers` -/

#plan_status Test.Dogfood.Scenario.Todo.Cached.cached_list_after_add
#plan_status Test.Dogfood.Scenario.QueueWorkers.held_within_fed
#plan_status Test.Dogfood.Scenario.QueueWorkers.fed_accounted
#plan_status Test.Dogfood.Scenario.QueueWorkers.queue_settled
#plan_status Test.Dogfood.Scenario.QueueWorkers.releases_once

end Effect4.Probes.MathReview

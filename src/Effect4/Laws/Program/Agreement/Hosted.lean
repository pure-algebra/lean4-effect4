import Effect4.Laws.Program.Agreement.Calls
import Effect4.Laws.Machine.StoresLaws

/-!
# Program.Agreement.Hosted — the command loop over one fiber with host calls

Slice H8 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310), the machine
half. `Agreement/Calls.lean` runs a program of the fragment with calls locally, under a reply
tape (`localRunC`). Here the machine runs it under a host's decisions: `evaluate`, `flush`, and
answers that hold an exit. Each decision moves the machine from one of four forms to another,
and the local run with calls moves the same way, reading one reply for each answer:

* the loaded root (`Api.load`), before its first evaluation;
* the root parked on a yield (`Myield`, `Agreement/Machine.lean`), which `flush` resumes;
* the root parked on a host call (`Mcall`), which an answer at its guard token resumes;
* the root exited (`Mexit`).

**The laws.** One evaluation segment (`drive_seg`): from the running root, within a bound of
commands, the loop reaches the exit path, a host call or a yield, and the local run with calls
reaches the same place with no reply read. One decision (`decision_holds`) and a tape of them
(`tape_holds`): the machine stays in a form whose position the local run with calls reaches,
reading the tape's replies in order. They are steps of the planned goal
`denoteRows_eq_session` (`Laws/Api/SessionMeaning.lean`); concept `translation-simulation`,
requirement R6. They say nothing of a second fiber, a scope, an interruption, a clock step or
a reply that is refused: the decisions are a host's (`hostDecision`), on one fiber.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-! ## The root parked on a host call -/

/-- The root fiber parked on a host call at guard token `t`: the registration's park
(`Fibers.lean`, the `async` arm of `evaluatePrim`), the fiber no longer running. Its frame keeps
the call as its current code, which the answer decision reads. -/
def callParkedAt (fr : NFiber) (k t : Nat) : NRunFiber :=
  { fiberAt fr k with
    running := false
    parked := Parked.withGuard t
    pending := [⟨t, none, [], [], Resume.void, false⟩] }

/-- The machine with its root parked on a host call: nothing armed, the next token taken. -/
def Mcall (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [callParkedAt fr k t], nextId := 1, nextToken := t + 1, trace := tr }

theorem Mcall_stuck (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Mcall fr s k tr t).stuck = none := rfl

theorem Mcall_armed (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Mcall fr s k tr t).armed = [] := rfl

theorem Mcall_state (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Mcall fr s k tr t).state = s := rfl

theorem Mcall_fiber? (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Mcall fr s k tr t).fiber? Api.root = some (callParkedAt fr k t) := rfl

/-- The view of a host call: its row, request and address. -/
theorem eq_call_of_isCall {cur : NCode} (h : IsCall cur = true) :
    ∃ j v w, cur = Prim.async (EffName.external (.external j) v w) false none := by
  unfold IsCall at h
  split at h
  next j v w => exact ⟨j, v, w, rfl⟩
  next => cases h

/-- With no preloaded answer, a host call's registration answers nothing and leaves the stores
as they are (`interpOf`'s external arm). -/
theorem registerAsync_call (root : NativeEff) (completed : List (FiberId × ExitV)) (j : Nat)
    (v : Val) (w : List Nat) (f : FiberId) (t : Nat) {s : Stores} (hs : s.externals.answers = []) :
    (interpAt root completed table).registerAsync (EffName.external (.external j) v w) f t s =
      (s, none) := by
  show (if (externalRow table j).isNone then (s, none) else
    match s.externals.answers with
    | [] => (s, none)
    | answer :: rest =>
      if externalAdmits table j answer s.externals.allocated then
        let (next, code) := prepareExternalAnswer table
          (some (.async (EffName.external (.external j) v w) false none)) answer s
        ({ next with externals := { next.externals with answers := rest } }, some code)
      else
        let rejected := s.externals.rejected.orElse
          (fun _ => some (j, answer, s.externals.answers.length))
        ({ s with externals := { s.externals with rejected } }, none)) = (s, none)
  rw [hs]
  split <;> rfl

/-- **The loop parks the root on a host call**: one command, the token taken, nothing armed. -/
theorem drive_loop_call (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd)
    (hc : IsCall cur = true) (hk : k + 1 < defaultBudget) (hs : s.externals.answers = []) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
        (M (fiberOf cur K i) s k tr nt) (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (Mcall (fiberOf cur K i) s (k + 1) tr' nt) rest := by
  obtain ⟨j, v, w, rfl⟩ := eq_call_of_isCall hc
  refine ⟨tr ++ [RunEvent.parkedOn Api.root nt], fun n => ?_⟩
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table)
      (M (fiberOf (Prim.async (EffName.external (.external j) v w) false none) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.async (EffName.external (.external j) v w) false none) K i) k) false =
      ⟨{ M (fiberOf (Prim.async (EffName.external (.external j) v w) false none) K i) s k
          (tr ++ [RunEvent.parkedOn Api.root nt]) nt with nextToken := nt + 1 },
        (fiberAt (fiberOf (Prim.async (EffName.external (.external j) v w) false none) K i) (k + 1)).park
          ⟨nt, none, [], [], Resume.void, false⟩,
        false, Outcome.parked, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    simp only [evaluateNative, fiberAt_frame, fiberOf]
    simp only [evaluatePrim, fiberAt_frame, M_state, registerAsync_call root _ j v w _ _ hs]
    rfl
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit,
    settle]
  rfl

/-! ## One evaluation segment -/

/-- A finishing local step that is no call finishes the local run with calls in one step, with
no reply read. -/
theorem localRunC_finish {root : NativeEff} {fr : NFiber} {s s' : Stores} {ex : ExitV}
    (hstep : localStep root fr s = .finished ex s') (hc : IsCall fr.current = false)
    (r : ReplyTape) : localRunC table root 1 fr s r = some (.exit ex s' r) := by
  show localRunC table root (0 + 1) fr s r = _
  simp only [localRunC, localStepC, hc, Bool.false_eq_true, if_false, hstep]

/-- **What one evaluation segment owes**, from the running root at count `k` with `d` the next
command (`cmdOf`). Within `c ≤ 2n + 2` commands the loop reaches one of three places, and the
local run with calls from the same fiber reaches the same place with no reply read:

* the exit path of an exit over stores, and the local run finishes with that exit over them;
* a host call, the root parked on it (`Mcall`);
* a yield, the root parked on its dispatcher (`Myield`) with the run still to do.

The stores stay quiet and hold no preloaded answer. -/
def SegOwes (root : NativeEff) (table : RowTable) (n : Nat) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (d : Bool) :
    Prop :=
  ∃ c, c ≤ 2 * n + 2 ∧
    ((∃ ex s' fr k' tr' l, Quiet s' ∧ s'.externals.answers = [] ∧
        (∀ r, localRunC table root l (fiberOf cur K i) s r = some (.exit ex s' r)) ∧
        ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
            (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
          driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
            (M fr s' k' tr' nt) (Cmd.finish Api.root ex :: rest)) ∨
      (∃ cur₁ K₁ i₁ s₁ k₁ tr' l, IsCall cur₁ = true ∧ PlainStack K₁ ∧ Quiet s₁ ∧
        s₁.externals.answers = [] ∧
        (∀ r, ReachesC table root l (fiberOf cur K i) s r (fiberOf cur₁ K₁ i₁) s₁ r) ∧
        ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
            (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
          driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
            (Mcall (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt) rest) ∨
      (∃ cur₁ K₁ i₁ s₁ k₁ tr' l, PlainCode cur₁ = true ∧ PlainStack K₁ ∧ Quiet s₁ ∧
        s₁.externals.answers = [] ∧
        (∀ r, ReachesC table root l (fiberOf cur K i) s r (fiberOf cur₁ K₁ i₁) s₁ r) ∧
        ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
            (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
          driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
            (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt) rest))

/-- One or two commands and `l₀` local steps in front of what is owed. -/
theorem SegOwes.step {root : NativeEff} {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {d : Bool}
    {cur₁ : NCode} {K₁ : List NCode} {i₁ : Bool} {s₁ : Stores} {k₁ : Nat} {tr₁ : NTrace}
    (d₁ : Bool) (a : Nat) (ha : a ≤ 2) (l₀ : Nat)
    (hreach : ∀ r, ReachesC table root l₀ (fiberOf cur K i) s r (fiberOf cur₁ K₁ i₁) s₁ r)
    (hdrv : ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + a) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
        (M (fiberOf cur₁ K₁ i₁) s₁ k₁ tr₁ nt) (cmdOf d₁ :: rest))
    (h : SegOwes root table n cur₁ K₁ i₁ s₁ k₁ tr₁ nt rest d₁) :
    SegOwes root table (n + 1) cur K i s k tr nt rest d := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c + a, by omega, ?_⟩
  have hrec : ∀ (X : Api.Machine) (R : List NCmd),
      (∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
          (M (fiberOf cur₁ K₁ i₁) s₁ k₁ tr₁ nt) (cmdOf d₁ :: rest) =
        driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel X R) →
      ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table)
          (fuel + (c + a)) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
        driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel X R := by
    intro X R hX fuel
    rw [show fuel + (c + a) = fuel + c + a by omega, hdrv, hX]
  rcases h with ⟨ex, s', fr, k', tr', l, hq, hans, hrun, hX⟩ |
    ⟨cur₂, K₂, i₂, s₂, k₂, tr', l, hc₂, hK₂, hq, hans, hr, hX⟩ |
    ⟨cur₂, K₂, i₂, s₂, k₂, tr', l, hpl₂, hK₂, hq, hans, hr, hX⟩
  · exact Or.inl ⟨ex, s', fr, k', tr', l + l₀, hq, hans,
      fun r => (hreach r l).trans (hrun r), hrec _ _ hX⟩
  · exact Or.inr (Or.inl ⟨cur₂, K₂, i₂, s₂, k₂, tr', l₀ + l, hc₂, hK₂, hq, hans,
      fun r => (hreach r).trans (hr r), hrec _ _ hX⟩)
  · exact Or.inr (Or.inr ⟨cur₂, K₂, i₂, s₂, k₂, tr', l₀ + l, hpl₂, hK₂, hq, hans,
      fun r => (hreach r).trans (hr r), hrec _ _ hX⟩)

/-- The exit path, one command away. -/
theorem SegOwes.finish {root : NativeEff} {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {d : Bool} {ex : ExitV}
    {fr : NFiber} {k' : Nat} {tr' : NTrace} (hq : Quiet s) (hans : s.externals.answers = [])
    (hrun : ∀ r, localRunC table root 1 (fiberOf cur K i) s r = some (.exit ex s r))
    (hdrv : ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + 1) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
        (M fr s k' tr' nt) (Cmd.finish Api.root ex :: rest)) :
    SegOwes root table n cur K i s k tr nt rest d :=
  ⟨1, by omega, Or.inl ⟨ex, s, fr, k', tr', 1, hq, hans, hrun, hdrv⟩⟩

/-- The root parked on a host call, one command away. -/
theorem SegOwes.call {root : NativeEff} {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {d : Bool} {k' : Nat}
    {tr' : NTrace} (hc : IsCall cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hans : s.externals.answers = [])
    (hdrv : ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + 1) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel
        (Mcall (fiberOf cur K i) s k' tr' nt) rest) :
    SegOwes root table n cur K i s k tr nt rest d :=
  ⟨1, by omega, Or.inr (Or.inl ⟨cur, K, i, s, k', tr', 0, hc, hK, hq, hans,
    fun r => ReachesC.refl table root _ s r, hdrv⟩)⟩

/-- The yield, two commands away: the count about to reach the budget at the loop. -/
theorem SegOwes.yield (root : NativeEff) {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd}
    (hk : defaultBudget ≤ k + 1) (hpl : PlainCode cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hans : s.externals.answers = []) :
    SegOwes root table n cur K i s k tr nt rest false := by
  obtain ⟨tr', h⟩ := drive_loop_yield (table := table) root cur K i s k tr nt rest hk
  exact ⟨2, by omega, Or.inr (Or.inr ⟨cur, K, i, s, k + 2, tr', 0, hpl, hK, hq, hans,
    fun r => ReachesC.refl table root _ s r, h⟩)⟩

/-- **One evaluation segment** (H8, the machine layer). From the running root over a plain
fiber, quiet stores with no preloaded answer, and a measure `n` of what is left of the op
budget, the loop does what `SegOwes` says: it reaches the exit path, a host call or a yield,
and the local run with calls reaches the same place with no reply read. Induction on the
measure: each command takes one local step, or answers a `sync` that the next command
delivers. Reach: `LoopedRows`, one fiber, any row table. It does not establish that the run
ends: a yield leaves the rest to `flush`. -/
theorem drive_seg (root : NativeEff) (hroot : LoopedRows root = true) :
    ∀ (n : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat) (tr : NTrace)
      (nt : Nat) (rest : List NCmd) (d : Bool),
      2 * (defaultBudget - k) + d.toNat ≤ n →
      PlainCode cur = true → PlainStack K → Quiet s → s.externals.answers = [] →
      (d = true → (∀ t, cur ≠ Prim.sync t) ∧ IsCall cur = false) →
      SegOwes root table n cur K i s k tr nt rest d
  | 0, cur, K, i, s, k, tr, nt, rest, d, hm, hpl, hK, hq, hans, _ => by
    -- nothing left of the budget: the loop yields
    cases d with
    | true =>
      simp only [Bool.toNat_true] at hm
      exact absurd hm (by omega)
    | false =>
      simp only [Bool.toNat_false, Nat.add_zero] at hm
      exact SegOwes.yield root (by omega) hpl hK hq hans
  | n + 1, cur, K, i, s, k, tr, nt, rest, d, hm, hpl, hK, hq, hans, hd => by
    cases d with
    | true =>
      -- the delivery: no `sync` and no call here, the step is the frame machine's, no count
      simp only [Bool.toNat_true] at hm
      obtain ⟨hns, hnc⟩ := hd rfl
      rcases hstep : localStep root (fiberOf cur K i) s with ⟨fr₁, s₁⟩ | ⟨ex₁, s₁⟩
      · have hreach := fun r => ReachesC.step (table := table) hstep hnc r
        have hs₁ := localStep_stores hns hstep
        subst hs₁
        obtain ⟨cur₁, K₁, i₁, rfl, hpl₁, hK₁⟩ :=
          localStep_plain hroot cur K i s fr₁ s hpl hK hstep
        obtain ⟨tr₁, hdrv⟩ :=
          drive_deliver_running (table := table) root cur K i s k tr nt rest cur₁ K₁ i₁ hpl hK hns
            hnc hstep
        exact SegOwes.step false 1 (by omega) 1 hreach hdrv
          (drive_seg root hroot n cur₁ K₁ i₁ s k tr₁ nt rest false
            (by simp only [Bool.toNat_false, Nat.add_zero]; omega) hpl₁ hK₁ hq hans
            (fun h => by cases h))
      · have hs₁ := localStep_finished_stores hstep
        subst hs₁
        obtain ⟨tr₁, hdrv⟩ :=
          drive_deliver_finish (table := table) root cur K i s k tr nt rest ex₁ hpl hns hstep
        exact SegOwes.finish hq hans (localRunC_finish hstep hnc) hdrv
    | false =>
      simp only [Bool.toNat_false, Nat.add_zero] at hm
      rcases Nat.lt_or_ge (k + 1) defaultBudget with hk | hk
      · cases hcall : IsCall cur
        · rcases hstep : localStep root (fiberOf cur K i) s with ⟨fr₁, s₁⟩ | ⟨ex₁, s₁⟩
          · -- one more local step at the loop
            have hreach := fun r => ReachesC.step (table := table) hstep hcall r
            cases hsy : isSync cur
            · have hns := not_sync_of_isSync_false hsy
              have hs₁ := localStep_stores hns hstep
              subst hs₁
              obtain ⟨cur₁, K₁, i₁, rfl, hpl₁, hK₁⟩ :=
                localStep_plain hroot cur K i s fr₁ s hpl hK hstep
              obtain ⟨tr₁, hdrv⟩ :=
                drive_loop_running (table := table) root cur K i s k tr nt rest cur₁ K₁ i₁ hpl hK
                  hns hcall hk hstep
              exact SegOwes.step false 1 (by omega) 1 hreach hdrv
                (drive_seg root hroot n cur₁ K₁ i₁ s (k + 1) tr₁ nt rest false
                  (by simp only [Bool.toNat_false, Nat.add_zero]; omega) hpl₁ hK₁ hq hans
                  (fun h => by cases h))
            · -- a `sync`: answered at the loop, delivered next
              obtain ⟨t, rfl⟩ := eq_sync_of_isSync hsy
              cases t <;> simp only [PlainCode, Bool.false_eq_true] at hpl
              · -- pure
                rename_i p
                rw [step_sync_pure] at hstep
                simp only [LocalStep.running.injEq] at hstep
                obtain ⟨hfr, hs⟩ := hstep
                subst hfr
                subst hs
                obtain ⟨tr₁, hdrv⟩ :=
                  drive_loop_sync_pure (table := table) root p K i s k tr nt rest hk
                exact SegOwes.step true 1 (by omega) 1 hreach hdrv
                  (drive_seg root hroot n _ K i s (k + 1) tr₁ nt rest true
                    (by simp only [Bool.toNat_true]; omega) rfl hK hq hans
                    (fun _ => ⟨fun _ h => (by cases h), rfl⟩))
              · -- a store operation
                rename_i o
                rw [step_sync_op] at hstep
                rcases hso : syncOpStep o s with _ | ⟨s₂, v⟩ <;> rw [hso] at hstep <;>
                  simp only [LocalStep.running.injEq] at hstep <;> obtain ⟨hfr, hs⟩ := hstep <;>
                  subst hfr <;> subst hs
                · obtain ⟨tr₁, hdrv⟩ :=
                    drive_loop_sync_op_none (table := table) root o K i s k tr nt rest hk hso
                  exact SegOwes.step true 1 (by omega) 1 hreach hdrv
                    (drive_seg root hroot n _ K i s (k + 1) tr₁ nt rest true
                      (by simp only [Bool.toNat_true]; omega) rfl hK hq hans
                      (fun _ => ⟨fun _ h => (by cases h), rfl⟩))
                · have hq₂ : Quiet s₂ := syncOpStep_quiet hso hq
                  have hans₂ : s₂.externals.answers = [] := by
                    rw [syncOpStep_externals o s s₂ v hso]
                    exact hans
                  obtain ⟨tr₁, hdrv⟩ :=
                    drive_loop_sync_op (table := table) root o K i s k tr nt rest s₂ v hk hso
                  have hdrain := drive_drainDue (table := table) root
                    (m := M (fiberOf (Prim.success v) K i) s₂ (k + 1) tr₁ nt)
                    (rest := Cmd.deliver Api.root false :: rest) (hs := rfl) (hq := hq₂)
                  refine SegOwes.step true 2 (by omega) 1 hreach (fun fuel => ?_)
                    (drive_seg root hroot n _ K i s₂ (k + 1) tr₁ nt rest true
                      (by simp only [Bool.toNat_true]; omega) rfl hK hq₂ hans₂
                      (fun _ => ⟨fun _ h => (by cases h), rfl⟩))
                  simp only [cmdOf]
                  rw [show fuel + 2 = fuel + 1 + 1 by omega, hdrv, hdrain]
          · -- the last local step at the loop: the exit
            have hs₁ := localStep_finished_stores hstep
            subst hs₁
            cases hsy : isSync cur
            · have hns := not_sync_of_isSync_false hsy
              obtain ⟨tr₁, hdrv⟩ :=
                drive_loop_finish (table := table) root cur K i s k tr nt rest ex₁ hpl hns hk hstep
              exact SegOwes.finish hq hans (localRunC_finish hstep hcall) hdrv
            · -- a `sync` never finishes the fiber
              obtain ⟨t, rfl⟩ := eq_sync_of_isSync hsy
              cases t <;> simp only [PlainCode, Bool.false_eq_true] at hpl
              · rw [step_sync_pure] at hstep
                cases hstep
              · rename_i o
                rw [step_sync_op] at hstep
                rcases hso : syncOpStep o s with _ | ⟨s₂, v⟩ <;> rw [hso] at hstep <;> cases hstep
        · -- a host call: the root parks on it
          obtain ⟨tr₁, hdrv⟩ := drive_loop_call (table := table) root cur K i s k tr nt rest hcall hk hans
          exact SegOwes.call hcall hK hq hans hdrv
      · -- the count is at the budget: the loop yields before anything else
        exact SegOwes.yield root hk hpl hK hq hans

/-! ## Where the run is -/

/-- A position of the local run with calls: a live fiber over stores, or an exit over stores. -/
inductive Pos where
  | live (fr : NFiber) (s : Stores)
  | done (ex : ExitV) (s : Stores)

/-- **The local run with calls leads from one position to another**, reading the replies
between `r` and `r'`: a live fiber reaches a live fiber (`ReachesC`) or finishes with an exit;
an exit leads only to itself, reading nothing. -/
def Leads (table : RowTable) (root : NativeEff) : Pos → ReplyTape → Pos → ReplyTape → Prop
  | .live fr s, r, .live fr' s', r' => ∃ c, ReachesC table root c fr s r fr' s' r'
  | .live fr s, r, .done ex s', r' => ∃ c, localRunC table root c fr s r = some (.exit ex s' r')
  | .done ex s, r, .done ex' s', r' => ex = ex' ∧ s = s' ∧ r = r'
  | .done _ _, _, .live _ _, _ => False

theorem Leads.refl {root : NativeEff} : ∀ (p : Pos) (r : ReplyTape), Leads table root p r p r
  | .live fr s, r => ⟨0, ReachesC.refl table root fr s r⟩
  | .done _ _, _ => ⟨rfl, rfl, rfl⟩

theorem Leads.trans {root : NativeEff} :
    ∀ {p q u : Pos} {r₁ r₂ r₃ : ReplyTape}, Leads table root p r₁ q r₂ →
      Leads table root q r₂ u r₃ → Leads table root p r₁ u r₃
  | .live _ _, .live _ _, .live _ _, _, _, _, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩ => ⟨c₁ + c₂, h₁.trans h₂⟩
  | .live _ _, .live _ _, .done _ _, _, _, _, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩ => ⟨c₂ + c₁, (h₁ c₂).trans h₂⟩
  | .live _ _, .done _ _, .done _ _, _, _, _, h₁, ⟨rfl, rfl, rfl⟩ => h₁
  | .done _ _, .done _ _, .done _ _, _, _, _, ⟨rfl, rfl, rfl⟩, h₂ => h₂
  | .live _ _, .done _ _, .live _ _, _, _, _, _, h₂ => h₂.elim
  | .done _ _, .done _ _, .live _ _, _, _, _, _, h₂ => h₂.elim
  | .done _ _, .live _ _, _, _, _, _, h₁, _ => h₁.elim

/-- **The machine at rest between decisions, at a position**: the root parked on a yield or
on a host call over a fiber of the fragment's code, or exited; the stores quiet with no
preloaded answer. -/
def Settled (root : NativeEff) (m : Api.Machine) (p : Pos) : Prop :=
  (∃ cur K i s k tr t, m = Myield (fiberOf cur K i) s k tr t ∧ p = .live (fiberOf cur K i) s ∧
      PlainCode cur = true ∧ PlainStack K ∧ Quiet s ∧ s.externals.answers = []) ∨
  (∃ cur K i s k tr t, m = Mcall (fiberOf cur K i) s k tr t ∧ p = .live (fiberOf cur K i) s ∧
      IsCall cur = true ∧ PlainStack K ∧ Quiet s ∧ s.externals.answers = []) ∨
  (∃ ex fr s k tr nt, m = Mexit root ex fr s k tr nt ∧ p = .done ex s ∧ Quiet s)

/-- The forms a host's decisions keep: the loaded root, at the start of its compiled code over
the empty stores, or a settled machine. -/
def Holds (root : NativeEff) (cf : Nat) (m : Api.Machine) (p : Pos) : Prop :=
  (m = Api.load root cf ∧ p = .live (fiberOf (compile root cf) []) Stores.empty) ∨
    Settled root m p

/-- **A segment closed by its drain settles.** From the running root at count `k` over a plain
fiber, the loop and its drain settle in a form of `Settled` within a bound of commands, and the
local run with calls leads to its position with no reply read. -/
theorem seg_settles (root : NativeEff) (hroot : LoopedRows root = true) (cur : NCode)
    (K : List NCode) (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat)
    (hpl : PlainCode cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hans : s.externals.answers = []) :
    ∃ c m' p', c ≤ 4 * defaultBudget + 5 ∧ Settled root m' p' ∧
      (∀ r, Leads table root (.live (fiberOf cur K i) s) r p' r) ∧
      ∀ fuel, driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + c)
        (M (fiberOf cur K i) s k tr nt) [Cmd.loop Api.root false, Cmd.drainDue] = (m', []) := by
  obtain ⟨c, hc, h⟩ := drive_seg (table := table) root hroot (2 * defaultBudget) cur K i s k tr nt
    [Cmd.drainDue] false (by simp only [Bool.toNat_false, Nat.add_zero]; omega) hpl hK hq hans
    (fun h => by cases h)
  rcases h with ⟨ex, s', fr, k', tr', l, hq', hans', hrun, hX⟩ |
    ⟨cur₁, K₁, i₁, s₁, k₁, tr', l, hc₁, hK₁, hq₁, hans₁, hr, hX⟩ |
    ⟨cur₁, K₁, i₁, s₁, k₁, tr', l, hpl₁, hK₁, hq₁, hans₁, hr, hX⟩ <;> simp only [cmdOf] at hX
  · obtain ⟨tr'', hfin⟩ := drive_finish_M (table := table) root ex fr s' k' tr' nt [Cmd.drainDue]
    refine ⟨c + 3, Mexit root ex fr s' k' tr'' nt, .done ex s', by omega,
      Or.inr (Or.inr ⟨ex, fr, s', k', tr'', nt, rfl, rfl, hq'⟩), fun r => ⟨l, hrun r⟩,
      fun fuel => ?_⟩
    rw [show fuel + (c + 3) = fuel + 1 + 1 + 1 + c by omega, hX, hfin,
      drive_drainDue root _ _ _ rfl hq', drive_drainDue root _ _ _ rfl hq', drive_nil]
  · refine ⟨c + 1, Mcall (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt, .live (fiberOf cur₁ K₁ i₁) s₁,
      by omega, Or.inr (Or.inl ⟨cur₁, K₁, i₁, s₁, k₁, tr', nt, rfl, rfl, hc₁, hK₁, hq₁, hans₁⟩),
      fun r => ⟨l, hr r⟩, fun fuel => ?_⟩
    rw [show fuel + (c + 1) = fuel + 1 + c by omega, hX, drive_drainDue root _ _ _ rfl hq₁,
      drive_nil]
  · refine ⟨c + 1, Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt, .live (fiberOf cur₁ K₁ i₁) s₁,
      by omega, Or.inl ⟨cur₁, K₁, i₁, s₁, k₁, tr', nt, rfl, rfl, hpl₁, hK₁, hq₁, hans₁⟩,
      fun r => ⟨l, hr r⟩, fun fuel => ?_⟩
    rw [show fuel + (c + 1) = fuel + 1 + c by omega, hX, drive_drainDue root _ _ _ rfl hq₁,
      drive_nil]

/-! ## One decision at a time -/

/-- A decision whose receipt is true is the decision at any larger fuel, so a result that holds
from some fuel on is its result. -/
theorem step_of_receipt {root : NativeEff} {m R : Api.Machine} {d : Api.Decision} {F c : Nat}
    (hR : ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
      (fuel + c) m d = (R, true))
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m d).2 =
      true) :
    (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m d).1 = R := by
  rw [← stepDecisionState_stable (evaluator := evaluatorFor root table) _ F m d h c, hR F]

/-- `evaluate` on the loaded root runs its first segment. -/
theorem load_evaluate (root : NativeEff) (hroot : LoopedRows root = true) (cf : Nat) :
    ∃ c m' p', Settled root m' p' ∧
      (∀ r, Leads table root (.live (fiberOf (compile root cf) []) Stores.empty) r p' r) ∧
      ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + c) (Api.load root cf) Api.evaluate = (m', true) := by
  obtain ⟨c, m', p', -, hS, hL, hd⟩ := seg_settles (table := table) root hroot (compile root cf) []
    true Stores.empty 0 [RunEvent.started Api.root] 0
    (plainCode_compileEff root _ hroot) PlainStack.nil Quiet.empty rfl
  refine ⟨c + 1, m', p', hS, hL, fun fuel => ?_⟩
  change stepDecisionState.loop (driveState (evaluator := evaluatorFor root table) _ _ _ _) = _
  rw [show fuel + (c + 1) = fuel + c + 1 by omega, drive_evaluate_load root cf _ _, hd]
  rfl

/-- `evaluate` on a root that is parked or exited does nothing, and the drain owes nothing. -/
theorem evaluate_inert (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (hs : m.stuck = none) (hf : m.fiber? Api.root = some f)
    (hp : (f.exit.isSome || f.running || f.parked != Parked.notParked) = true)
    (hq : Quiet m.state) :
    ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
      (fuel + 2) m Api.evaluate = (m, true) := by
  intro fuel
  change stepDecisionState.loop (driveState (evaluator := evaluatorFor root table) _ _ _ _) = _
  rw [show fuel + 2 = fuel + 1 + 1 by omega, driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, hf, hp]
  rw [drive_drainDue root _ _ _ hs hq, drive_nil]
  rfl

/-- `flush` with nothing armed does nothing. -/
theorem flush_unarmed (root : NativeEff) (m : Api.Machine) (h : m.armed = []) :
    ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
      fuel m Api.flush = (m, true) := by
  intro fuel
  change flushAllState (evaluator := evaluatorFor root table) _ fuel fuel m = _
  cases fuel with
  | zero => simp only [flushAllState, h, List.isEmpty_nil, Bool.true_or]
  | succ fuel => simp only [flushAllState, h]

/-- With nothing armed, every round count of `flush` stops at once. -/
theorem flushAllState_unarmed (root : NativeEff) (fuel : Nat) (m : Api.Machine)
    (h : m.armed = []) :
    ∀ rounds, flushAllState (evaluator := evaluatorFor root table) (interpOf root table) fuel
      rounds m = (m, true)
  | 0 => by simp only [flushAllState, h, List.isEmpty_nil, Bool.true_or]
  | _ + 1 => by simp only [flushAllState, h]

/-- **The rounds of `flush` after a yield**, with their receipt true: each round fires the root
back into the loop at count one and settles; a round that yields again leaves the rest to the
next. The rounds end on a settled machine that is not on a yield, and the local run with calls
leads there with no reply read. -/
theorem flush_Myield (root : NativeEff) (hroot : LoopedRows root = true) :
    ∀ (rounds : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat)
      (tr : NTrace) (t : Nat) (fuel : Nat),
      4 * defaultBudget + 8 ≤ fuel → PlainCode cur = true → PlainStack K → Quiet s →
      s.externals.answers = [] →
      (flushAllState (evaluator := evaluatorFor root table) (interpOf root table) fuel rounds
        (Myield (fiberOf cur K i) s k tr t)).2 = true →
      ∃ p', Settled root (flushAllState (evaluator := evaluatorFor root table)
          (interpOf root table) fuel rounds (Myield (fiberOf cur K i) s k tr t)).1 p' ∧
        ∀ r, Leads table root (.live (fiberOf cur K i) s) r p' r
  | 0, cur, K, i, s, k, tr, t, fuel, _, _, _, _, _, h => by
    simp only [flushAllState, Myield_armed, List.isEmpty_cons, Myield_stuck, Option.isSome_none,
      Bool.or_self, Bool.false_eq_true] at h
  | rounds + 1, cur, K, i, s, k, tr, t, fuel, hf, hpl, hK, hq, hans, h => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
    obtain ⟨tr₁, hfire⟩ := fire_Myield (table := table) root cur K i s k tr t
    obtain ⟨c, m', p', hc, hS, hL, hd⟩ :=
      seg_settles (table := table) root hroot cur K i s 1 tr₁ (t + 1) hpl hK hq hans
    have hdn := hd (n - c)
    rw [Nat.sub_add_cancel (by omega : c ≤ n)] at hdn
    have hround : fireState (evaluator := evaluatorFor root table) (interpOf root table)
        (n + 1 + 1 + 1) (Myield (fiberOf cur K i) s k tr t) Api.root = (m', true) := by
      rw [hfire n, hdn]
      rfl
    have hstep : flushAllState (evaluator := evaluatorFor root table) (interpOf root table)
        (n + 1 + 1 + 1) (rounds + 1) (Myield (fiberOf cur K i) s k tr t) =
        flushAllState (evaluator := evaluatorFor root table) (interpOf root table)
          (n + 1 + 1 + 1) rounds m' := by
      simp only [flushAllState, Myield_armed, Myield_stuck, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hround]
    rw [hstep] at h ⊢
    rcases hS with ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, rfl, rfl, hpl₁, hK₁, hq₁, hans₁⟩ |
      ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, rfl, rfl, hc₁, hK₁, hq₁, hans₁⟩ |
      ⟨ex, fr, s', k', tr', nt', rfl, rfl, hq'⟩
    · -- a yield again: the next round
      obtain ⟨p'', hS'', hL''⟩ :=
        flush_Myield root hroot rounds cur₁ K₁ i₁ s₁ k₁ tr₂ t₁ _ hf hpl₁ hK₁ hq₁ hans₁ h
      exact ⟨p'', hS'', fun r => (hL r).trans (hL'' r)⟩
    · -- a host call: nothing armed
      rw [flushAllState_unarmed root _ _ (Mcall_armed _ _ _ _ _)]
      exact ⟨_, Or.inr (Or.inl ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, rfl, rfl, hc₁, hK₁, hq₁, hans₁⟩),
        hL⟩
    · -- the exit: nothing armed
      rw [flushAllState_unarmed root _ _ (Mexit_armed _ _ _ _ _ _ _)]
      exact ⟨_, Or.inr (Or.inr ⟨ex, fr, s', k', tr', nt', rfl, rfl, hq'⟩), hL⟩

/-! ### The answer at a host call -/

/-- The answer the machine prepares from an exit is code of the fragment, over stores whose
cells and preloaded answers are as they were (`prepareExternalAnswer`). -/
theorem prepareExternalAnswer_ofExit (c : Option NCode) (ex : ExitV) (s : Stores) :
    PlainCode (prepareExternalAnswer table c (.ofExit ex) s).2 = true ∧
      (prepareExternalAnswer table c (.ofExit ex) s).1.deferreds = s.deferreds ∧
      (prepareExternalAnswer table c (.ofExit ex) s).1.externals.answers =
        s.externals.answers := by
  have hfall : PlainCode (embed (completionPrim (.ofExit ex))) = true := by cases ex <;> rfl
  unfold prepareExternalAnswer
  split
  · exact ⟨hfall, rfl, rfl⟩
  · split
    · split
      · exact ⟨hfall, rfl, rfl⟩
      · split
        · exact ⟨hfall, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨hfall, rfl, rfl⟩

/-- A machine of one fiber finds that fiber at its own id and nothing else. -/
theorem fiber?_one {m : Api.Machine} {g : NRunFiber} (hm : m.fibers = [g]) {f : FiberId}
    {g' : NRunFiber} (h : m.fiber? f = some g') : g' = g ∧ g.id = f := by
  unfold RunMachine.fiber? at h
  rw [hm, List.find?_cons, List.find?_nil] at h
  split at h
  next hp =>
    cases h
    exact ⟨rfl, of_decide_eq_true hp⟩
  next => cases h

/-- A request the machine is waiting on is a fiber parked at that guard on an external
registration. -/
theorem requestOf_parked {m : Api.Machine} {f : FiberId} {t : Nat}
    (h : Program.requestOf m f t ≠ none) :
    ∃ g, m.fiber? f = some g ∧ g.parked = .withGuard t ∧
      ∃ op req w c d, g.frame.current = .async (.external op req w) c d := by
  unfold Program.requestOf at h
  cases hf : m.fiber? f with
  | none =>
    rw [hf] at h
    exact absurd rfl h
  | some g =>
    rw [hf] at h
    by_cases hp : g.parked = .withGuard t
    · refine ⟨g, rfl, hp, ?_⟩
      simp only [guard, hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      split at h
      next op req w c d heq => exact ⟨op, req, w, c, d, heq⟩
      next => exact absurd rfl h
    · simp only [guard, hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some] at h
      exact absurd rfl h

/-- Only the root's own guard on a host call has a request. -/
theorem requestOf_Mcall {fr : NFiber} {s : Stores} {k : Nat} {tr : NTrace} {t : Nat}
    {f : FiberId} {t' : Nat} (h : Program.requestOf (Mcall fr s k tr t) f t' ≠ none) :
    f = Api.root ∧ t' = t := by
  obtain ⟨g, hf, hp, -⟩ := requestOf_parked h
  obtain ⟨rfl, hid⟩ := fiber?_one rfl hf
  refine ⟨hid.symm, ?_⟩
  cases hp
  rfl

theorem requestOf_Myield {fr : NFiber} {s : Stores} {k : Nat} {tr : NTrace} {t : Nat}
    {f : FiberId} {t' : Nat} (h : Program.requestOf (Myield fr s k tr t) f t' ≠ none) : False := by
  obtain ⟨g, hf, -, op, req, w, c, d, hcur⟩ := requestOf_parked h
  obtain ⟨rfl, -⟩ := fiber?_one rfl hf
  cases hcur

theorem requestOf_Mexit {root : NativeEff} {ex : ExitV} {fr : NFiber} {s : Stores} {k : Nat}
    {tr : NTrace} {nt : Nat} {f : FiberId} {t' : Nat}
    (h : Program.requestOf (Mexit root ex fr s k tr nt) f t' ≠ none) : False := by
  obtain ⟨g, hf, hp, -⟩ := requestOf_parked h
  obtain ⟨rfl, -⟩ := fiber?_one rfl hf
  cases hp

theorem requestOf_load {root : NativeEff} {cf : Nat} {f : FiberId} {t' : Nat}
    (h : Program.requestOf (Api.load root cf) f t' ≠ none) : False := by
  obtain ⟨g, hf, hp, -⟩ := requestOf_parked h
  obtain ⟨rfl, -⟩ := fiber?_one rfl hf
  cases hp

/-- **The answer at the root's call**: the machine prepares the answer from the exit, resumes
the root at that guard and enters it at count zero. -/
theorem answer_Mcall (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores)
    (k : Nat) (tr : NTrace) (t : Nat) (ex : ExitV) {s' : Stores} {code : NCode}
    (hp : prepareExternalAnswer table (some cur) (.ofExit ex) s = (s', code)) :
    ∃ tr', ∀ n, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
        (n + 2) (Mcall (fiberOf cur K i) s k tr t) (RunDecision.answerAsync Api.root t (.ofExit ex)) =
      stepDecisionState.loop (driveState (evaluator := evaluatorFor root table)
        (interpOf root table) n (M (fiberOf code K i) s' 0 tr' (t + 1))
        [Cmd.loop Api.root false, Cmd.drainDue]) := by
  refine ⟨tr ++ [RunEvent.resumedWith Api.root t code] ++ [RunEvent.started Api.root],
    fun n => ?_⟩
  have hprep : prepareAsyncAnswer (interpOf root table) (Mcall (fiberOf cur K i) s k tr t) Api.root t
      (.ofExit ex) = (s', code) := by
    simp only [prepareAsyncAnswer, Mcall_stuck, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, Mcall_fiber?, callParkedAt]
    exact hp
  rw [show stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) (n + 2)
      (Mcall (fiberOf cur K i) s k tr t) (RunDecision.answerAsync Api.root t (.ofExit ex)) =
      stepDecisionState.loop (driveState (evaluator := evaluatorFor root table)
        (interpOf root table) (n + 1 + 1) (Mcall (fiberOf cur K i) s' k tr t)
        [Cmd.resume Api.root t code, Cmd.drainDue]) by
    simp only [stepDecisionState, hprep]
    rfl]
  simp only [Mcall, callParkedAt, fiberAt, RunFiber.make, RunMachine.empty, driveState_succ_cons,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, RunMachine.fiber?, decide_true,
    List.find?_cons_of_pos, RunMachine.emit, RunMachine.update, ne_eq, decide_not, Bool.not_true,
    not_false_eq_true, List.filter_cons_of_neg, List.filter_nil, List.map_cons, List.map_nil,
    List.isEmpty_cons, Bool.or_self, bne_self_eq_false, List.append_assoc, List.cons_append,
    List.nil_append, M]
  rfl

/-! ### The three decisions of a host -/

/-- **`evaluate`** keeps the forms: on the loaded root it runs the first segment; on a parked or
exited root it does nothing. The local run with calls reads no reply. -/
theorem holds_evaluate (root : NativeEff) (hroot : LoopedRows root = true) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat}
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      Api.evaluate).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m Api.evaluate).1 p' ∧ ∀ r, Leads table root p r p' r := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, rfl, rfl, hpl, hK, hq, hans⟩ |
    ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩ | ⟨ex, fr, s, k, tr, nt, rfl, rfl, hq⟩
  · obtain ⟨c, m', p', hS, hL, hR⟩ := load_evaluate (table := table) root hroot cf
    rw [step_of_receipt hR h]
    exact ⟨p', Or.inr hS, hL⟩
  · rw [step_of_receipt (evaluate_inert root _ _ rfl (Myield_fiber? _ _ _ _ _) rfl hq) h]
    exact ⟨_, Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, rfl, rfl, hpl, hK, hq, hans⟩),
      fun r => Leads.refl _ r⟩
  · rw [step_of_receipt (evaluate_inert root _ _ rfl (Mcall_fiber? _ _ _ _ _) rfl hq) h]
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩)),
      fun r => Leads.refl _ r⟩
  · rw [step_of_receipt (evaluate_inert root _ (exitedAt root ex fr k) rfl rfl rfl hq) h]
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨ex, fr, s, k, tr, nt, rfl, rfl, hq⟩)), fun r => Leads.refl _ r⟩

/-- **`flush`** keeps the forms: after a yield it runs the rounds; with nothing armed it does
nothing. The local run with calls reads no reply. -/
theorem holds_flush (root : NativeEff) (hroot : LoopedRows root = true) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat}
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      Api.flush).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m Api.flush).1 p' ∧ ∀ r, Leads table root p r p' r := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, rfl, rfl, hpl, hK, hq, hans⟩ |
    ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩ | ⟨ex, fr, s, k, tr, nt, rfl, rfl, hq⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inl ⟨rfl, rfl⟩, fun r => Leads.refl _ r⟩
  · have hst := stepDecisionState_stable (evaluator := evaluatorFor root table) _ F _ Api.flush h
      (4 * defaultBudget + 8)
    rw [← hst] at h ⊢
    obtain ⟨p', hS, hL⟩ := flush_Myield (table := table) root hroot (F + (4 * defaultBudget + 8))
      cur K i s k tr t (F + (4 * defaultBudget + 8)) (by omega) hpl hK hq hans h
    exact ⟨p', Or.inr hS, hL⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩)),
      fun r => Leads.refl _ r⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨ex, fr, s, k, tr, nt, rfl, rfl, hq⟩)), fun r => Leads.refl _ r⟩

/-- **An answer at a guard the machine is waiting on** keeps the forms: it is the root's host
call, the machine resumes it with the answer it prepares and runs the next segment, and the
local run with calls reads exactly that reply. -/
theorem holds_answer (root : NativeEff) (hroot : LoopedRows root = true) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat} {f : FiberId} {t₀ : Nat}
    {ex : ExitV} (hreq : Program.requestOf m f t₀ ≠ none)
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      (RunDecision.answerAsync f t₀ (.ofExit ex))).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m (RunDecision.answerAsync f t₀ (.ofExit ex))).1 p' ∧
      ∀ r, Leads table root p (ex :: r) p' r := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, rfl, rfl, hpl, hK, hq, hans⟩ |
    ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, hK, hq, hans⟩ | ⟨ex', fr, s, k, tr, nt, rfl, rfl, hq⟩
  · exact (requestOf_load hreq).elim
  · exact (requestOf_Myield hreq).elim
  · obtain ⟨rfl, rfl⟩ := requestOf_Mcall hreq
    obtain ⟨hpc, hdef, hans'⟩ := prepareExternalAnswer_ofExit (table := table) (some cur) ex s
    rcases hp : prepareExternalAnswer table (some cur) (.ofExit ex) s with ⟨s', code⟩
    rw [hp] at hpc hdef hans'
    obtain ⟨tr', hstep⟩ := answer_Mcall (table := table) root cur K i s k tr t₀ ex hp
    obtain ⟨c, m', p', -, hS, hL, hd⟩ := seg_settles (table := table) root hroot code K i s' 0 tr'
      (t₀ + 1) hpc hK (Quiet.of_deferreds_eq hdef hq) (hans'.trans hans)
    have hR : ∀ fuel, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
        (fuel + (c + 2)) (Mcall (fiberOf cur K i) s k tr t₀)
        (RunDecision.answerAsync Api.root t₀ (.ofExit ex)) = (m', true) := by
      intro fuel
      rw [show fuel + (c + 2) = fuel + c + 2 by omega, hstep, hd]
      rfl
    rw [step_of_receipt hR h]
    exact ⟨p', Or.inr hS, fun r => Leads.trans
      (show Leads table root (.live (fiberOf cur K i) s) (ex :: r) (.live (fiberOf code K i) s') r
        from ⟨1, ReachesC.answer s hc ex r hp⟩) (hL r)⟩
  · exact (requestOf_Mexit hreq).elim

/-! ## What a settled machine says of the meaning -/

/-- A run that stops within its budget stops there at every larger budget. -/
theorem localRunC_mono {root : NativeEff} :
    ∀ (c k : Nat) (fr : NFiber) (s : Stores) (r : ReplyTape) {e : RunEnd},
      localRunC table root c fr s r = some e → localRunC table root (c + k) fr s r = some e
  | 0, _, _, _, _, _, h => by cases h
  | c + 1, k, fr, s, r, e, h => by
    rw [show c + 1 + k = (c + k) + 1 by omega]
    rcases hst : localStepC table root fr s r with _ | ⟨_ | _, r'⟩
    · simp only [localRunC, hst] at h ⊢
      exact h
    · simp only [localRunC, hst] at h ⊢
      exact localRunC_mono c k _ _ r' h
    · simp only [localRunC, hst] at h ⊢
      exact h

/-- Two budgets at which the run stops see the same stop. -/
theorem localRunC_agree {root : NativeEff} {fr : NFiber} {s : Stores} {r : ReplyTape} {a b : Nat}
    {e₁ e₂ : RunEnd} (h₁ : localRunC table root a fr s r = some e₁)
    (h₂ : localRunC table root b fr s r = some e₂) : e₁ = e₂ := by
  have h₁' := localRunC_mono a b fr s r h₁
  have h₂' := localRunC_mono b a fr s r h₂
  rw [Nat.add_comm b a, h₁'] at h₂'
  exact Option.some.inj h₂'

/-- An exit's fiber over the empty stack finishes in one step. -/
theorem localRunC_ofExit_nil {root : NativeEff} (ex : ExitV) (i : Bool) (s : Stores)
    (r : ReplyTape) (n : Nat) :
    localRunC table root (n + 1) (fiberOf (Prim.ofExit ex) [] i) s r = some (.exit ex s r) := by
  have hc : IsCall (fiberOf (Prim.ofExit ex) [] i).current = false := isCall_ofExit ex
  simp only [localRunC, localStepC, hc, Bool.false_eq_true, if_false, step_exit_empty]

/-- A host call with no reply left waits. -/
theorem localRunC_waits {root : NativeEff} {fr : NFiber} (hc : IsCall fr.current = true)
    (s : Stores) (n : Nat) : localRunC table root (n + 1) fr s [] = some .waits := by
  simp only [localRunC, localStepC, hc, if_true]

/-- The compile's frontier steps to itself. -/
theorem localStep_frontier (root : NativeEff) {q : Point} (hq : q.fuel = 0) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (frontier q) K i) s =
      .running (fiberOf (frontier { q with completed := [] }) K i) s := by
  rw [frontier, step_suspend]
  simp only [interpAt]
  rw [suspendBodyAt_zero (q := { q with completed := [] }) hq]

/-- **At the compile's frontier the run never stops** (`localStep_frontier`). -/
theorem localRunC_frontier {root : NativeEff} :
    ∀ (n : Nat) {fr : NFiber} (s : Stores) (r : ReplyTape), AtFrontier fr →
      localRunC table root n fr s r = none
  | 0, _, _, _, _ => rfl
  | n + 1, _, s, r, ⟨q, K, i, hq, rfl⟩ => by
    have hnc : IsCall (fiberOf (frontier q) K i).current = false := rfl
    simp only [localRunC, localStepC, hnc, Bool.false_eq_true, if_false,
      localStep_frontier root hq K i s]
    exact localRunC_frontier n s r ⟨{ q with completed := [] }, K, i, hq, rfl⟩

/-- The fragment of the meaning lies in the fragment with host calls. -/
theorem LoopedRows.of_straightRows : ∀ (e : NativeEff), StraightRows table e = true →
    LoopedRows e = true
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .sync _, _ => rfl
  | .perform op _, h => by
    cases op with
    | external _ => rfl
    | _ => exact h
  | .suspend b, h => LoopedRows.of_straightRows b h
  | .exit b, h => LoopedRows.of_straightRows b h
  | .bind a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .select _ _ a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .catchCause a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .catchIf _ a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .onExit a b, h => by
    obtain ⟨ha, hb⟩ : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      Bool.and_self]
  | .matchCause a b c, h => by
    obtain ⟨ha, hb, hc⟩ :
        StraightRows table a = true ∧ StraightRows table b = true ∧ StraightRows table c = true := by
      simpa only [StraightRows, Bool.and_eq_true, and_assoc] using h
    simp only [LoopedRows, LoopedRows.of_straightRows a ha, LoopedRows.of_straightRows b hb,
      LoopedRows.of_straightRows c hc, Bool.and_self]
  | .gen _, h | .uninterruptible _, h | .interruptible _, h | .yieldNow _, h | .awaitFiber _ _, h
  | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h | .provideLayer _ _ _, h | .service _, h
  | .provideService _ _ _, h | .iterate _ _ _ _ _ _, h | .restore _ _, h | .defs _ _ _, h => by
    simp only [StraightRows, Bool.false_eq_true] at h

/-- **The meaning at a settled machine with nothing armed** (H8, the closing step). The local run
with calls from the root's start leads, over the reply tape `R`, to the machine's position with
no reply left. If the root has exited, the meaning is its exit over the stores, with the tape
read to its end; if it waits on a host call, the meaning is the frontier. A compile budget out of
reach makes the run diverge at the compile's frontier, which a settled machine excludes. -/
theorem meaning_settled (root : NativeEff) (hfrag : StraightRows table root = true) (cf : Nat)
    (R : ReplyTape) {m : Api.Machine} {p : Pos} (hS : Settled root m p) (harmed : m.armed = [])
    (hL : Leads table root (.live (fiberOf (compile root cf) []) Stores.empty) R p []) :
    meaningRows table root [] Stores.empty R =
      ((m.fiber? Api.root).bind RunFiber.exit).map fun ex => ((ex, m.state), []) := by
  have hR : RunsToD table root [] true (fiberOf (compile root cf) []) Stores.empty R
      (meaningRows table root [] Stores.empty R) :=
    localRunC_compile table root root (rootPoint cf) [] true Stores.empty R hfrag rfl
  rcases hS with ⟨cur, K, i, s, k, tr, t, rfl, rfl, -⟩ |
    ⟨cur, K, i, s, k, tr, t, rfl, rfl, hc, -⟩ | ⟨ex, fr, s, k, tr, nt, rfl, rfl, -⟩
  · cases harmed
  · -- the root waits on a host call with no reply left: the meaning is the frontier
    obtain ⟨c, hreach⟩ := hL
    have hw : ∀ n, localRunC table root (n + 1 + c) (fiberOf (compile root cf) []) Stores.empty R =
        some .waits := fun n => (hreach (n + 1)).trans (localRunC_waits hc s n)
    show _ = none
    rcases hR with hR | ⟨d, fr', s', r', hd, hfront⟩
    · rcases hm : meaningRows table root [] Stores.empty R with _ | ⟨⟨ex₂, s₂⟩, r₂⟩
      · rfl
      · rw [hm] at hR
        obtain ⟨d, hd⟩ := hR
        have he := (hd 1).trans (localRunC_ofExit_nil ex₂ true s₂ r₂ 0)
        cases localRunC_agree (hw 0) he
    · have h₁ := localRunC_mono (0 + 1 + c) d _ _ _ (hw 0)
      rw [hd (0 + 1 + c), localRunC_frontier _ s' r' hfront] at h₁
      cases h₁
  · -- the root has exited: the meaning is its exit over the stores, the tape read to its end
    obtain ⟨c, hrun⟩ := hL
    show _ = some ((ex, s), [])
    rcases hR with hR | ⟨d, fr', s', r', hd, hfront⟩
    · rcases hm : meaningRows table root [] Stores.empty R with _ | ⟨⟨ex₂, s₂⟩, r₂⟩
      · rw [hm] at hR
        obtain ⟨d, fr', s', hd, hc⟩ := hR
        have hw := (hd 1).trans (localRunC_waits hc s' 0)
        cases localRunC_agree hrun hw
      · rw [hm] at hR
        obtain ⟨d, hd⟩ := hR
        have he := (hd 1).trans (localRunC_ofExit_nil ex₂ true s₂ r₂ 0)
        cases localRunC_agree hrun he
        rfl
    · have h₁ := localRunC_mono c d _ _ _ hrun
      rw [hd c, localRunC_frontier _ s' r' hfront] at h₁
      cases h₁

end Effect4.Program.Agreement

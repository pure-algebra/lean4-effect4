import Effect4.Laws.Program.Agreement.LoopCalls
import Effect4.Laws.Program.Agreement.ContextSegment

/-!
# Program.Agreement.Hosted — the command loop over one fiber with host calls

Slice H8 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310), the machine
half. `Agreement/Calls.lean` runs a program of the fragment with calls locally, under a reply
tape (`localRunC`). Here the machine runs it under a host's decisions: `evaluate`, `flush`, and
answers that hold an exit. Each decision moves the machine from one of four forms to another,
and the local run with calls moves the same way, reading one reply for each answer:

* the loaded root (`Api.load`), before its first evaluation;
* the root parked on a yield (`Myield`, `Agreement/Machine.lean`), which `flush` resumes;
* the root parked on a host call (`Mcall`, `Agreement/Segment.lean`), which an answer at its
  guard token resumes;
* the root exited (`Mexit`).

**The laws.** An actual completed segment receipt settles a plain root
(`seg_settles_receipt`, using `drive_seg_receipt` in `Agreement/ContextSegment.lean`). The local run and the settled
position join on exact stopped observations, with no host reply read. The three hosted decisions
(`holds_evaluate`, `holds_flush`, `holds_answer`) preserve this relation when their actual receipt
is true. An answer reads exactly one host reply. At rest, the form fixes the meaning
(`meaning_settled`). These laws serve `denoteRows_eq_session` through the tape induction.
Concept: `translation-simulation`; requirement R6. Contexts and scheduler budgets remain arbitrary.
The receipt supplies completion; these laws assert no progress bound. They establish no second
fiber, scope, interruption, clock step or refused reply.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-! ## Where the run is -/

/-- A position of the local run with calls: a live fiber over stores, or an exit over stores. -/
inductive Pos where
  | live (fr : NFiber) (s : Stores) (ctx : Ctx := emptyCtx)
  | done (ex : ExitV) (s : Stores)

/-- Observational joining of two live positions, allowing a finite shift on each side.
Concept translation-simulation; rows-block-host/R6. Consumer: `Leads` and its composition.
The observation is `RunEnd`, including the exact context at a wait. This asserts no progress. -/
def RunJoinC {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (fr : NFiber) (s : Stores) (r : σ) (fr' : NFiber) (s' : Stores) (r' : σ)
    (ctx : Ctx := emptyCtx) (ctx' : Ctx := ctx) : Prop :=
  ∃ a b, ∀ n, localRunC host root (n + a) fr s r ctx = localRunC host root (n + b) fr' s' r' ctx'
@[semantics "translation-simulation" (requirement := R6)]
theorem RunJoinC.refl {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (fr : NFiber) (s : Stores) (r : σ) (ctx : Ctx) : RunJoinC host root fr s r fr s r ctx ctx := ⟨0, 0, fun _ => rfl⟩
@[semantics "translation-simulation" (requirement := R6)]
theorem RunJoinC.trans {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr₁ fr₂ fr₃ : NFiber} {s₁ s₂ s₃ : Stores} {r₁ r₂ r₃ : σ} {ctx₁ ctx₂ ctx₃ : Ctx}
    (h₁ : RunJoinC host root fr₁ s₁ r₁ fr₂ s₂ r₂ ctx₁ ctx₂)
    (h₂ : RunJoinC host root fr₂ s₂ r₂ fr₃ s₃ r₃ ctx₂ ctx₃) :
    RunJoinC host root fr₁ s₁ r₁ fr₃ s₃ r₃ ctx₁ ctx₃ := by
  obtain ⟨a, b, h₁⟩ := h₁
  obtain ⟨c, d, h₂⟩ := h₂
  refine ⟨a + c, b + d, fun n => ?_⟩
  calc
    localRunC host root (n + (a + c)) fr₁ s₁ r₁ ctx₁ =
        localRunC host root ((n + c) + a) fr₁ s₁ r₁ ctx₁ := by congr 1; omega
    _ = localRunC host root ((n + c) + b) fr₂ s₂ r₂ ctx₂ := h₁ (n + c)
    _ = localRunC host root ((n + b) + c) fr₂ s₂ r₂ ctx₂ := by congr 1; omega
    _ = localRunC host root ((n + b) + d) fr₃ s₃ r₃ ctx₃ := h₂ (n + b)
    _ = localRunC host root (n + (b + d)) fr₃ s₃ r₃ ctx₃ := by congr 1; omega
@[semantics "translation-simulation" (requirement := R6)]
theorem ReachesC.join {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c : Nat} {fr fr' : NFiber} {s s' : Stores} {r r' : σ} {ctx ctx' : Ctx}
    (h : ReachesC host root c fr s r fr' s' r' ctx ctx') :
    RunJoinC host root fr s r fr' s' r' ctx ctx' := ⟨c, 0, fun n => by simpa only [Nat.add_zero] using h n⟩
@[semantics "translation-simulation" (requirement := R6)]
theorem RunJoinC.terminal {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr fr' : NFiber} {s s' : Stores} {r r' : σ} {ctx ctx' : Ctx} {c : Nat} {e : RunEnd σ}
    (h : RunJoinC host root fr s r fr' s' r' ctx ctx')
    (ht : localRunC host root c fr' s' r' ctx' = some e) :
    ∃ n, localRunC host root n fr s r ctx = some e := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨c + a, (h c).trans (localRunC_mono c b fr' s' r' ht)⟩
/-- Live positions join on their exact stopped observations. A live position leads to a
completed exit when its run reaches that exit. Consumer: hosted session agreement, R6.
This asserts no scheduler progress and requires no context or host-answer restriction. -/
def Leads {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) :
    Pos → σ → Pos → σ → Prop
  | .live fr s ctx, r, .live fr' s' ctx', r' => RunJoinC host root fr s r fr' s' r' ctx ctx'
  | .live fr s ctx, r, .done ex s', r' => ∃ c, localRunC host root c fr s r ctx = some (.exit ex s' r')
  | .done ex s, r, .done ex' s', r' => ex = ex' ∧ s = s' ∧ r = r'
  | .done _ _, _, .live _ _ _, _ => False

@[semantics "translation-simulation" (requirement := R6)]
theorem Leads.refl {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff} :
    ∀ (p : Pos) (r : σ), Leads host root p r p r
  | .live fr s ctx, r => RunJoinC.refl host root fr s r ctx
  | .done _ _, _ => ⟨rfl, rfl, rfl⟩

@[semantics "translation-simulation" (requirement := R6)]
theorem Leads.trans {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff} :
    ∀ {p q u : Pos} {r₁ r₂ r₃ : σ}, Leads host root p r₁ q r₂ →
      Leads host root q r₂ u r₃ → Leads host root p r₁ u r₃
  | .live _ _ _, .live _ _ _, .live _ _ _, _, _, _, h₁, h₂ => RunJoinC.trans h₁ h₂
  | .live _ _ _, .live _ _ _, .done _ _, _, _, _, h₁, ⟨_, h₂⟩ => RunJoinC.terminal h₁ h₂
  | .live _ _ _, .done _ _, .done _ _, _, _, _, h₁, ⟨rfl, rfl, rfl⟩ => h₁
  | .done _ _, .done _ _, .done _ _, _, _, _, ⟨rfl, rfl, rfl⟩, h₂ => h₂
  | .live _ _ _, .done _ _, .live _ _ _, _, _, _, _, h₂ => h₂.elim
  | .done _ _, .done _ _, .live _ _ _, _, _, _, _, h₂ => h₂.elim
  | .done _ _, .live _ _ _, _, _, _, _, h₁, _ => h₁.elim

/-- **Leading with no reply read**: under every host, at every state, the state untouched. What
`evaluate` and `flush` keep. -/
def LeadsQ (root : NativeEff) (p p' : Pos) : Prop :=
  ∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (r : σ), Leads host root p r p' r

theorem LeadsQ.refl (root : NativeEff) (p : Pos) : LeadsQ (table := table) root p p :=
  fun _ r => Leads.refl p r

theorem LeadsQ.trans {root : NativeEff} {p q u : Pos} (h₁ : LeadsQ (table := table) root p q)
    (h₂ : LeadsQ (table := table) root q u) : LeadsQ (table := table) root p u :=
  fun host r => (h₁ host r).trans (h₂ host r)

/-- What a host answers at a position: the call of a live fiber's code, asked of the host. -/
def Pos.hostAnswer {σ : Type} (host : Effects.Comodel (RowSig table) σ) : Pos → σ → Option (ExitV × σ)
  | .live fr _ _, r => Agreement.hostAnswer host fr.current r
  | .done _ _, _ => none

/-- **The machine at rest between decisions, at a position**: the root parked on a yield or
on a host call over a fiber of the fragment's code, or exited; the stores quiet. -/
def Settled (root : NativeEff) (m : Api.Machine) (p : Pos) : Prop :=
  (∃ cur K i s k tr t ctx,
      m = Myield (fiberOf cur K i) s k tr t ctx ∧ p = .live (fiberOf cur K i) s ctx ∧
      PlainCode cur = true ∧ PlainStack K ∧ Quiet s) ∨
  (∃ cur K i s k tr t ctx,
      m = Mcall (fiberOf cur K i) s k tr t ctx ∧ p = .live (fiberOf cur K i) s ctx ∧
      IsCall cur = true ∧ PlainStack K ∧ Quiet s) ∨
  (∃ ex fr s k tr nt ctx,
      m = Mexit root ex fr s k tr nt ctx ∧ p = .done ex s ∧ Quiet s)

/-- The loaded root starts at the empty context. A settled live position retains its
actual context; a completed position observes only its exit and stores. -/
def Holds (root : NativeEff) (cf : Nat) (m : Api.Machine) (p : Pos) : Prop :=
  (m = Api.load root cf ∧ p = .live (fiberOf (compile root cf) []) Stores.empty emptyCtx) ∨
    Settled root m p

/-- A completed command receipt settles a plain segment at every context.
Concept translation-simulation; rows-block-host/R6. Consumers: the evaluate, flush and answer
proofs. The receipt includes the refusal branch, which plainness excludes. No progress bound
or host-answer restriction is asserted. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem seg_settles_receipt (root : NativeEff) (hroot : PlainHooks root) (fuel : Nat)
    (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat)
    (ctx : Ctx) (hpl : PlainCode cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hreceipt : settled (driveState (evaluator := evaluatorFor root table) (interpOf root table)
      fuel (M (fiberOf cur K i) s k tr nt ctx) [Cmd.loop Api.root false, Cmd.drainDue]) = true) :
    ∃ p', Settled root (driveState (evaluator := evaluatorFor root table) (interpOf root table)
        fuel (M (fiberOf cur K i) s k tr nt ctx) [Cmd.loop Api.root false, Cmd.drainDue]).1 p' ∧
      LeadsQ (table := table) root (.live (fiberOf cur K i) s ctx) p'
 := by
  obtain ⟨result, hr, ho⟩ := drive_seg_receipt root hroot fuel cur K i s k tr nt ctx false
    hpl hK hq (fun h => by cases h) hreceipt
  simp only [cmdOf] at hr
  rw [hr]
  rcases ho with ⟨ex, s', fr', k', tr', nt', ctx', rfl, hq', hex⟩ |
    ⟨cur', K', i', s', k', tr', nt', ctx', rfl, hc, hK', hq', c, hreach⟩ |
    ⟨cur', K', i', s', k', tr', nt', ctx', rfl, hpl', hK', hq', c, hreach⟩
  · exact ⟨.done ex s', Or.inr (Or.inr ⟨ex, fr', s', k', tr', nt', ctx', rfl, rfl, hq'⟩),
      fun host r => hex host r⟩
  · exact ⟨.live (fiberOf cur' K' i') s' ctx',
      Or.inr (Or.inl ⟨cur', K', i', s', k', tr', nt', ctx', rfl, rfl, hc, hK', hq'⟩),
      fun host r => ReachesC.join (hreach host r)⟩
  · exact ⟨.live (fiberOf cur' K' i') s' ctx',
      Or.inl ⟨cur', K', i', s', k', tr', nt', ctx', rfl, rfl, hpl', hK', hq'⟩,
      fun host r => ReachesC.join (hreach host r)⟩

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

/-- An actual evaluate receipt settles the loaded root.
Step of rows-block-host/R6, consumed by `holds_evaluate`. No termination bound is asserted. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem load_evaluate_receipt (root : NativeEff) (hroot : PlainHooks root) (cf F : Nat)
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
      F (Api.load root cf) Api.evaluate).2 = true) :
    ∃ p', Settled root (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F (Api.load root cf) Api.evaluate).1 p' ∧
      LeadsQ (table := table) root (.live (fiberOf (compile root cf) []) Stores.empty emptyCtx) p'
 := by
  cases F with
  | zero => cases h
  | succ n =>
    have hd := drive_evaluate_load (table := table) root cf [Cmd.drainDue] n
    change settled (driveState (evaluator := evaluatorFor root table) (interpOf root table)
      (n + 1) (Api.load root cf) [Cmd.evaluate Api.root, Cmd.drainDue]) = true at h
    rw [hd] at h
    have hs := seg_settles_receipt root hroot n (compile root cf) [] true Stores.empty 0
      [RunEvent.started Api.root] 0 emptyCtx
      (by simpa only [resolve, compile, rootPoint, Node.at_] using hroot.resolve (rootPoint cf []))
      (by intro f hf; cases hf) Quiet.empty h
    change ∃ p', Settled root (driveState (evaluator := evaluatorFor root table)
        (interpOf root table) (n + 1) (Api.load root cf)
        [Cmd.evaluate Api.root, Cmd.drainDue]).1 p' ∧ _
    rw [hd]
    exact hs

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

/-- An actual flush receipt settles every completed round at its actual context.
Step of rows-block-host/R6; consumer: `holds_flush`. The resumed wrapper joins its saved code.
No budget restriction, positive-step assumption or progress bound is asserted. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem flush_Myield_receipt (root : NativeEff) (hroot : PlainHooks root) :
    ∀ (rounds : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat)
      (tr : NTrace) (t : Nat) (fuel : Nat) (ctx : Ctx),
      PlainCode cur = true → PlainStack K → Quiet s →
      (flushAllState (evaluator := evaluatorFor root table) (interpOf root table) fuel rounds
        (Myield (fiberOf cur K i) s k tr t ctx)).2 = true →
      ∃ p', Settled root (flushAllState (evaluator := evaluatorFor root table)
          (interpOf root table) fuel rounds (Myield (fiberOf cur K i) s k tr t ctx)).1 p' ∧
        LeadsQ (table := table) root (.live (fiberOf cur K i) s ctx) p'
  | 0, cur, K, i, s, k, tr, t, fuel, ctx, _, _, _, h => by
    simp only [flushAllState, Myield_armed, List.isEmpty_cons, Myield_stuck, Option.isSome_none,
      Bool.or_self, Bool.false_eq_true] at h
  | rounds + 1, cur, K, i, s, k, tr, t, fuel, ctx, hpl, hK, hq, h => by
    have hfire : (fireState (evaluator := evaluatorFor root table) (interpOf root table)
        fuel (Myield (fiberOf cur K i) s k tr t ctx) Api.root).2 = true := by
      cases hr : (fireState (evaluator := evaluatorFor root table) (interpOf root table)
          fuel (Myield (fiberOf cur K i) s k tr t ctx) Api.root).2 with
      | false =>
        simp only [flushAllState, Myield_armed, Myield_stuck, Option.isSome_none,
          Bool.false_eq_true, if_false, hr] at h
      | true => rfl
    have hround : flushAllState (evaluator := evaluatorFor root table) (interpOf root table)
        fuel (rounds + 1) (Myield (fiberOf cur K i) s k tr t ctx) =
        flushAllState (evaluator := evaluatorFor root table) (interpOf root table) fuel rounds
          (fireState (evaluator := evaluatorFor root table) (interpOf root table)
            fuel (Myield (fiberOf cur K i) s k tr t ctx) Api.root).1 := by
      simp only [flushAllState, Myield_armed, Myield_stuck, Option.isSome_none,
        Bool.false_eq_true, if_false, hfire, if_true]
    cases fuel with
    | zero => cases hfire
    | succ fuel =>
      cases fuel with
      | zero =>
        have hdrain : (parkedAt (fiberOf cur K i) k t ctx).dispatcher.drain =
            ([Task.resume Api.root t (Prim.success Val.unit)], Dispatcher.empty) := rfl
        unfold fireState at hfire
        simp only [Myield_fiber?, hdrain] at hfire
        dsimp only [List.foldl, fireStep, taskCmds] at hfire
        simp only [↓reduceIte, RunMachine.emit, RunMachine.disarm, RunMachine.update, parkedAt, fiberAt,
          RunFiber.make, Dispatcher.empty, Myield, RunMachine.empty, List.map_cons, List.map_nil,
          ne_eq, decide_not, decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
          List.filter_cons_of_neg, List.filter_nil, List.isEmpty_cons,
          Option.isSome_none, driveStep, RunMachine.fiber?, List.find?_cons_of_pos,
          List.append_assoc, List.cons_append, List.nil_append, Bool.or_self,
          driveState, settled] at hfire
      | succ n =>
        obtain ⟨tr₁, hraw⟩ := fire_Myield_answer_context (table := table) root (fiberOf cur K i) s k tr t ctx
        have hraw' := hraw n
        change fireState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1 + 1)
          (Myield (fiberOf cur K i) s k tr t ctx) Api.root =
          stepDecisionState.loop (driveState (evaluator := evaluatorFor root table) (interpOf root table)
            n (M (fiberOf (.success Val.unit) (.onSuccessConst (.yieldNowWith 0) cur :: K) i)
              s 0 tr₁ (t + 1) ctx) [Cmd.loop Api.root false, Cmd.drainDue]) at hraw'
        have hsegment : settled (driveState (evaluator := evaluatorFor root table) (interpOf root table)
            n (M (fiberOf (.success Val.unit) (.onSuccessConst (.yieldNowWith 0) cur :: K) i)
              s 0 tr₁ (t + 1) ctx) [Cmd.loop Api.root false, Cmd.drainDue]) = true := by
          change (stepDecisionState.loop _).2 = true
          rw [← hraw']
          exact hfire
        have hKw : PlainStack (.onSuccessConst (.yieldNowWith 0) cur :: K) := by
          intro f hf
          cases hf with
          | head => exact hpl
          | tail _ hf => exact hK f hf
        obtain ⟨p', hS, hL⟩ := seg_settles_receipt root hroot n (.success Val.unit)
          (.onSuccessConst (.yieldNowWith 0) cur :: K) i s 0 tr₁ (t + 1) ctx rfl hKw hq hsegment
        have hback : LeadsQ (table := table) root (.live (fiberOf cur K i) s ctx)
            (.live (fiberOf (.success Val.unit) (.onSuccessConst (.yieldNowWith 0) cur :: K) i) s ctx) := by
          intro σ host r
          have hs := ReachesQ.contextStep (table := table) (contextStep_yieldWrapper root cur K i s ctx) rfl host r
          exact ⟨0, 1, fun n => by simpa only [Nat.add_zero] using (hs n).symm⟩
        have hL' : LeadsQ (table := table) root (.live (fiberOf cur K i) s ctx) p' :=
          hback.trans hL
        rw [hround, hraw'] at h ⊢
        dsimp only [stepDecisionState.loop] at h ⊢
        rcases hS with ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, ctx₁, hshape, rfl, hpl₁, hK₁, hq₁⟩ |
          ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, ctx₁, hshape, rfl, hc₁, hK₁, hq₁⟩ |
          ⟨ex, fr, s', k', tr', nt', ctx', hshape, rfl, hq'⟩
        · rw [hshape] at h ⊢
          obtain ⟨p'', hS'', hL''⟩ := flush_Myield_receipt root hroot rounds cur₁ K₁ i₁ s₁ k₁ tr₂ t₁
            (n + 1 + 1) ctx₁ hpl₁ hK₁ hq₁ h
          exact ⟨p'', hS'', hL'.trans hL''⟩
        · rw [hshape, flushAllState_unarmed root _ _ (Mcall_armed _ _ _ _ _)]
          exact ⟨_, Or.inr (Or.inl ⟨cur₁, K₁, i₁, s₁, k₁, tr₂, t₁, ctx₁, rfl, rfl, hc₁, hK₁, hq₁⟩), hL'⟩
        · rw [hshape, flushAllState_unarmed root _ _ (Mexit_armed _ _ _ _ _ _ _)]
          exact ⟨_, Or.inr (Or.inr ⟨ex, fr, s', k', tr', nt', ctx', rfl, rfl, hq'⟩), hL'⟩

/-! ### The answer at a host call -/

/-- The answer the machine prepares from an exit is code of the fragment, over stores whose
cells are as they were (`prepareExternalAnswer`). -/
theorem prepareExternalAnswer_ofExit (c : Option NCode) (ex : ExitV) (s : Stores) :
    PlainCode (prepareExternalAnswer table c (.ofExit ex) s).2 = true ∧
      (prepareExternalAnswer table c (.ofExit ex) s).1.deferreds = s.deferreds := by
  have hfall : PlainCode (embed (completionPrim (.ofExit ex))) = true := by cases ex <;> rfl
  unfold prepareExternalAnswer
  split
  · exact ⟨hfall, rfl⟩
  · split
    · split
      · exact ⟨hfall, rfl⟩
      · split
        · exact ⟨hfall, rfl⟩
        · exact ⟨rfl, rfl⟩
    · exact ⟨hfall, rfl⟩

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
theorem requestOf_Mcall {ctx : Ctx} {fr : NFiber} {s : Stores} {k : Nat} {tr : NTrace} {t : Nat}
    {f : FiberId} {t' : Nat} (h : Program.requestOf (Mcall fr s k tr t ctx) f t' ≠ none) :
    f = Api.root ∧ t' = t := by
  obtain ⟨g, hf, hp, -⟩ := requestOf_parked h
  obtain ⟨rfl, hid⟩ := fiber?_one rfl hf
  refine ⟨hid.symm, ?_⟩
  cases hp
  rfl

theorem requestOf_Myield {ctx : Ctx} {fr : NFiber} {s : Stores} {k : Nat} {tr : NTrace} {t : Nat}
    {f : FiberId} {t' : Nat} (h : Program.requestOf (Myield fr s k tr t ctx) f t' ≠ none) : False := by
  obtain ⟨g, hf, -, op, req, w, c, d, hcur⟩ := requestOf_parked h
  obtain ⟨rfl, -⟩ := fiber?_one rfl hf
  cases hcur

theorem requestOf_Mexit {root : NativeEff} {ex : ExitV} {ctx : Ctx} {fr : NFiber} {s : Stores} {k : Nat}
    {tr : NTrace} {nt : Nat} {f : FiberId} {t' : Nat}
    (h : Program.requestOf (Mexit root ex fr s k tr nt ctx) f t' ≠ none) : False := by
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
    (hp : prepareExternalAnswer table (some cur) (.ofExit ex) s = (s', code)) (ctx : Ctx := emptyCtx) :
    ∃ tr', ∀ n, stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
        (n + 2) (Mcall (fiberOf cur K i) s k tr t ctx) (RunDecision.answerAsync Api.root t (.ofExit ex)) =
      stepDecisionState.loop (driveState (evaluator := evaluatorFor root table)
        (interpOf root table) n (M (fiberOf code K i) s' 0 tr' (t + 1) ctx)
        [Cmd.loop Api.root false, Cmd.drainDue]) := by
  refine ⟨tr ++ [RunEvent.resumedWith Api.root t code] ++ [RunEvent.started Api.root],
    fun n => ?_⟩
  have hprep : prepareAsyncAnswer (interpOf root table) (Mcall (fiberOf cur K i) s k tr t ctx) Api.root t
      (.ofExit ex) = (s', code) := by
    simp only [prepareAsyncAnswer, Mcall_stuck, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, Mcall_fiber?, callParkedAt]
    exact hp
  rw [show stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) (n + 2)
      (Mcall (fiberOf cur K i) s k tr t ctx) (RunDecision.answerAsync Api.root t (.ofExit ex)) =
      stepDecisionState.loop (driveState (evaluator := evaluatorFor root table)
        (interpOf root table) (n + 1 + 1) (Mcall (fiberOf cur K i) s' k tr t ctx)
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
theorem holds_evaluate (root : NativeEff) (hroot : PlainHooks root) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat}
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      Api.evaluate).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m Api.evaluate).1 p' ∧ LeadsQ (table := table) root p p' := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hpl, hK, hq⟩ |
    ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hc, hK, hq⟩ | ⟨ex, fr, s, k, tr, nt, ctx, rfl, rfl, hq⟩
  · obtain ⟨p', hS, hL⟩ := load_evaluate_receipt (table := table) root hroot cf F h
    exact ⟨p', Or.inr hS, hL⟩
  · rw [step_of_receipt (evaluate_inert root _ _ rfl (Myield_fiber? (ctx := ctx) _ _ _ _ _) rfl hq) h]
    exact ⟨_, Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hpl, hK, hq⟩),
      LeadsQ.refl root _⟩
  · rw [step_of_receipt (evaluate_inert root _ _ rfl (Mcall_fiber? (ctx := ctx) _ _ _ _ _) rfl hq) h]
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hc, hK, hq⟩)),
      LeadsQ.refl root _⟩
  · rw [step_of_receipt (evaluate_inert root _ (exitedAt root ex fr k ctx) rfl rfl rfl hq) h]
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨ex, fr, s, k, tr, nt, ctx, rfl, rfl, hq⟩)), LeadsQ.refl root _⟩

/-- **`flush`** keeps the forms: after a yield it runs the rounds; with nothing armed it does
nothing. The local run with calls reads no reply. -/
theorem holds_flush (root : NativeEff) (hroot : PlainHooks root) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat}
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      Api.flush).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m Api.flush).1 p' ∧ LeadsQ (table := table) root p p' := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hpl, hK, hq⟩ |
    ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hc, hK, hq⟩ | ⟨ex, fr, s, k, tr, nt, ctx, rfl, rfl, hq⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inl ⟨rfl, rfl⟩, LeadsQ.refl root _⟩
  · obtain ⟨p', hS, hL⟩ := flush_Myield_receipt (table := table) root hroot F cur K i s k tr t F ctx
      hpl hK hq h
    exact ⟨p', Or.inr hS, hL⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inr (Or.inr (Or.inl ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hc, hK, hq⟩)),
      LeadsQ.refl root _⟩
  · rw [flush_unarmed root _ rfl F]
    exact ⟨_, Or.inr (Or.inr (Or.inr ⟨ex, fr, s, k, tr, nt, ctx, rfl, rfl, hq⟩)), LeadsQ.refl root _⟩

/-- **An answer at a guard the machine is waiting on** keeps the forms: it is the root's host
call, the machine resumes it with the answer it prepares and runs the next segment, and the
local run with calls reads exactly that reply. -/
theorem holds_answer (root : NativeEff) (hroot : PlainHooks root) (cf : Nat)
    {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {F : Nat} {f : FiberId} {t₀ : Nat}
    {ex : ExitV} (hreq : Program.requestOf m f t₀ ≠ none)
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table) F m
      (RunDecision.answerAsync f t₀ (.ofExit ex))).2 = true) :
    ∃ p', Holds root cf (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F m (RunDecision.answerAsync f t₀ (.ofExit ex))).1 p' ∧
      ∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (r r' : σ),
        p.hostAnswer host r = some (ex, r') → Leads host root p r p' r' := by
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hpl, hK, hq⟩ |
    ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hc, hK, hq⟩ | ⟨ex', fr, s, k, tr, nt, ctx, rfl, rfl, hq⟩
  · exact (requestOf_load hreq).elim
  · exact (requestOf_Myield hreq).elim
  · obtain ⟨rfl, rfl⟩ := requestOf_Mcall hreq
    obtain ⟨hpc, hdef⟩ := prepareExternalAnswer_ofExit (table := table) (some cur) ex s
    rcases hp : prepareExternalAnswer table (some cur) (.ofExit ex) s with ⟨s', code⟩
    rw [hp] at hpc hdef
    have hstable := stepDecisionState_stable (evaluator := evaluatorFor root table)
      (interpOf root table) F _ (RunDecision.answerAsync Api.root t₀ (.ofExit ex)) h 2
    rw [← hstable] at h ⊢
    obtain ⟨tr', hstep⟩ := answer_Mcall (table := table) root cur K i s k tr t₀ ex hp ctx
    have hstep' := hstep F
    have hreceipt : settled (driveState (evaluator := evaluatorFor root table) (interpOf root table)
        F (M (fiberOf code K i) s' 0 tr' (t₀ + 1) ctx) [Cmd.loop Api.root false, Cmd.drainDue]) = true := by
      change (stepDecisionState.loop _).2 = true
      rw [← hstep']
      exact h
    obtain ⟨p', hS, hL⟩ := seg_settles_receipt (table := table) root hroot F code K i s' 0 tr'
      (t₀ + 1) ctx hpc hK (Quiet.of_deferreds_eq hdef hq) hreceipt
    rw [hstep']
    exact ⟨p', Or.inr hS, fun host r r' ha => Leads.trans
      (show Leads host root (.live (fiberOf cur K i) s ctx) r (.live (fiberOf code K i) s' ctx) r'
        from ReachesC.join (ReachesC.answer s hc ha hp ctx)) (hL host r')⟩
  · exact (requestOf_Mexit hreq).elim

/-! ## A waiting call on a row of the table -/

/-- A request the machine is waiting on is the current code of the waiting fiber. -/
theorem requestOf_current {m : Api.Machine} {f : FiberId} {t : Nat} {op : NativeOp} {req : Val}
    (h : Program.requestOf m f t = some (op, req)) :
    ∃ g, m.fiber? f = some g ∧ ∃ w c d, g.frame.current = .async (.external op req w) c d := by
  unfold Program.requestOf at h
  cases hf : m.fiber? f with
  | none =>
    rw [hf] at h
    cases h
  | some g =>
    rw [hf] at h
    by_cases hp : g.parked = .withGuard t
    · refine ⟨g, rfl, ?_⟩
      simp only [guard, hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      split at h
      next op' req' w c d heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨w, c, d, heq⟩
      next => cases h
    · simp only [guard, hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some] at h
      cases h

/-- A row the table registers lies inside the table. -/
theorem lt_of_externalRow {i : Nat} {row : Row} (h : externalRow table i = some row) :
    i < table.length := by
  rcases Nat.lt_or_ge i table.length with hlt | hge
  · exact hlt
  · have hnone : externalRow table i = none := by
      simp only [externalRow, List.getElem?_eq_none hge, Option.bind_eq_bind, Option.bind_none]
    rw [hnone] at h
    cases h

/-- **At a waiting call on a row of the table, a host answers the position as it answers the
call's row and request.** -/
theorem Holds.hostAnswer_eq {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {cf : Nat} {m : Api.Machine} {p : Pos} (hH : Holds root cf m p) {f : FiberId} {t i : Nat}
    {v : Val} (hreq : Program.requestOf m f t = some (.external i, v)) (hi : i < table.length)
    (st : σ) : p.hostAnswer host st = host.answer ⟨⟨i, hi⟩, v⟩ st := by
  have hne : Program.requestOf m f t ≠ none := by
    rw [hreq]
    exact Option.some_ne_none _
  rcases hH with ⟨rfl, rfl⟩ | ⟨cur, K, i', s, k, tr, t', ctx, rfl, rfl, -⟩ |
    ⟨cur, K, i', s, k, tr, t', ctx, rfl, rfl, hc, -⟩ | ⟨ex', fr, s, k, tr, nt, ctx, rfl, rfl, -⟩
  · exact (requestOf_load hne).elim
  · exact (requestOf_Myield hne).elim
  · obtain ⟨g, hg, w, c, d, hcur⟩ := requestOf_current hreq
    obtain ⟨rfl, -⟩ := fiber?_one rfl hg
    obtain ⟨j, v', w', rfl⟩ := eq_call_of_isCall hc
    simp only [callParkedAt, fiberAt_frame, fiberOf, Prim.async.injEq, EffName.external.injEq,
      NativeOp.external.injEq] at hcur
    obtain ⟨⟨rfl, rfl, -⟩, -, -⟩ := hcur
    exact hostAnswer_call host hi v' w' st
  · exact (requestOf_Mexit hne).elim

/-- **At a waiting call on a row of the table, the reply host answers with the tape's next
exit.** H8's step from the session's admitted reply to the reply host. -/
theorem Holds.tapeAnswer {root : NativeEff} {cf : Nat} {m : Api.Machine} {p : Pos}
    (hH : Holds root cf m p) {f : FiberId} {t i : Nat} {v : Val} {row : Row}
    (hreq : Program.requestOf m f t = some (.external i, v)) (hrow : externalRow table i = some row)
    (ex : ExitV) (rest : ReplyTape) :
    p.hostAnswer (tapeHost table) (ex :: rest) = some (ex, rest) := by
  rw [hH.hostAnswer_eq hreq (lt_of_externalRow hrow)]
  rfl

/-! ## What a settled machine says of the meaning -/

/-- An exit's fiber over the empty stack finishes in one step. -/
theorem localRunC_ofExit_nil {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    (ex : ExitV) (i : Bool) (s : Stores) (r : σ) (n : Nat) (ctx : Ctx := emptyCtx) :
    localRunC host root (n + 1) (fiberOf (Prim.ofExit ex) [] i) s r ctx = some (.exit ex s r) := by
  have hc : IsCall (fiberOf (Prim.ofExit ex) [] i).current = false := by cases ex <;> rfl
  simp only [localRunC, localStepC, hc, Bool.false_eq_true, if_false]
  rw [contextStep_fallback root _ s ctx (by intro t ht; cases ex <;> cases ht), step_exit_empty]

/-- The compile's frontier steps to itself. -/
theorem localStep_frontier (root : NativeEff) {q : Point} (hq : q.fuel = 0) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (frontier q) K i) s =
      .running (fiberOf (frontier { q with completed := [] }) K i) s := by
  rw [frontier, step_suspend]
  simp only [interpAt]
  rw [suspendBodyAt_zero (q := { q with completed := [] }) hq]

/-- **At the compile's frontier the run never stops** (`localStep_frontier`). -/
theorem localRunC_frontier {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {ctx : Ctx} :
    ∀ (n : Nat) {fr : NFiber} (s : Stores) (r : σ), AtFrontier fr →
      localRunC host root n fr s r ctx = none
  | 0, _, _, _, _ => rfl
  | n + 1, _, s, r, ⟨q, K, i, hq, rfl⟩ => by
    have hnc : IsCall (fiberOf (frontier q) K i).current = false := rfl
    simp only [localRunC, localStepC, hnc, Bool.false_eq_true, if_false]
    rw [contextStep_fallback root _ s ctx (by intro t ht; cases ht), localStep_frontier root hq K i s]
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
  | .provideService _ _ _, h | .iterate _ _ _ _ _ _, h | .restore _ _, h | .defs _ _ _ _, h => by
    simp only [StraightRows, Bool.false_eq_true] at h

/-- **The meaning at a settled machine with nothing armed** (H8, the closing step), under a host.
The local run with calls from the root's start leads, with the host's state going from `R` to
`st`, to the machine's position; at `st` the host answers the position's call with nothing. If
the root has exited, the meaning is its exit over the stores, with the host at `st`; if it waits
on a host call, the meaning is the frontier. A compile budget out of reach makes the run diverge
at the compile's frontier, which a settled machine excludes. -/
theorem meaning_settled {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (hfrag : StraightRows table root = true) (cf : Nat) (R st : σ) {m : Api.Machine} {p : Pos}
    (hS : Settled root m p) (harmed : m.armed = [])
    (hL : Leads host root (.live (fiberOf (compile root cf) []) Stores.empty) R p st)
    (hstop : p.hostAnswer host st = none) :
    hostRun host root [] Stores.empty R =
      ((m.fiber? Api.root).bind RunFiber.exit).map fun ex => (ex, (m.state, st)) := by
  have hR : RunsToD host root [] true (fiberOf (compile root cf) []) Stores.empty R
      (hostRun host root [] Stores.empty R) :=
    localRunC_compile host root root (rootPoint cf) [] true Stores.empty R emptyCtx hfrag rfl
  rcases hS with ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, -⟩ |
    ⟨cur, K, i, s, k, tr, t, ctx, rfl, rfl, hc, -⟩ | ⟨ex, fr, s, k, tr, nt, ctx, rfl, rfl, -⟩
  · cases harmed
  · -- the root waits on a host call the host does not answer: the meaning is the frontier
    obtain ⟨c, hw⟩ := RunJoinC.terminal hL (localRunC_waits hc hstop s 0 ctx)
    show _ = none
    rcases hR with hR | ⟨d, fr', s', r', reachedCtx, hd, hfront⟩
    · rcases hm : hostRun host root [] Stores.empty R with _ | ⟨ex₂, s₂, r₂⟩
      · rfl
      · rw [hm] at hR
        obtain ⟨d, hd⟩ := hR
        have he := (hd 1).trans (localRunC_ofExit_nil ex₂ true s₂ r₂ 0)
        cases localRunC_agree hw he
    · have h₁ := localRunC_mono c d _ _ _ hw
      rw [hd c, localRunC_frontier _ s' r' hfront] at h₁
      cases h₁
  · -- the root has exited: the meaning is its exit over the stores, with the host at `st`
    obtain ⟨c, hrun⟩ := hL
    show _ = some (ex, (s, st))
    rcases hR with hR | ⟨d, fr', s', r', reachedCtx, hd, hfront⟩
    · rcases hm : hostRun host root [] Stores.empty R with _ | ⟨ex₂, s₂, r₂⟩
      · rw [hm] at hR
        obtain ⟨d, fr', s', r', reachedCtx, hd, hc, ha⟩ := hR
        have hw := (hd 1).trans (localRunC_waits hc ha s' 0 reachedCtx)
        cases localRunC_agree hrun hw
      · rw [hm] at hR
        obtain ⟨d, hd⟩ := hR
        have he := (hd 1).trans (localRunC_ofExit_nil ex₂ true s₂ r₂ 0)
        cases localRunC_agree hrun he
        rfl
    · have h₁ := localRunC_mono c d _ _ _ hrun
      rw [hd c, localRunC_frontier _ s' r' hfront] at h₁
      cases h₁

/-- The reply host, its tape read to the end, answers no call. -/
theorem hostAnswer_tape_nil (code : NCode) : hostAnswer (tapeHost table) code [] = none := by
  unfold hostAnswer
  split
  · show (if _ : _ < table.length then (none : Option (ExitV × ReplyTape)) else none) = none
    split <;> rfl
  · rfl

/-- **H8's closing step**: `meaning_settled` at the reply host, its tape read to the end. -/
theorem meaning_settled_tape (root : NativeEff) (hfrag : StraightRows table root = true) (cf : Nat)
    (R : ReplyTape) {m : Api.Machine} {p : Pos} (hS : Settled root m p) (harmed : m.armed = [])
    (hL : Leads (tapeHost table) root (.live (fiberOf (compile root cf) []) Stores.empty) R p []) :
    meaningRows table root [] Stores.empty R =
      ((m.fiber? Api.root).bind RunFiber.exit).map fun ex => ((ex, m.state), []) := by
  have hstop : p.hostAnswer (tapeHost table) [] = none := by
    cases p with
    | live fr _ _ => exact hostAnswer_tape_nil fr.current
    | done _ _ => rfl
  rw [meaningRows_eq_hostRun, meaning_settled (tapeHost table) root hfrag cf R [] hS harmed hL hstop]
  cases (m.fiber? Api.root).bind RunFiber.exit <;> rfl

end Effect4.Program.Agreement

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

**The laws.** One evaluation segment (`drive_seg`, `Agreement/Segment.lean`) settles
(`seg_settles`): the loop reaches the exit path, a host call or a yield, and the local run with
calls reaches the same place with no reply read. One decision (`holds_evaluate`, `holds_flush`,
`holds_answer`): the machine stays in a form whose position the local run with calls reaches,
reading one reply for each answer. At rest, the form fixes the meaning (`meaning_settled`). They
are steps of `denoteRows_eq_session` (`Laws/Api/SessionMeaning.lean`, with the tape's induction
`tape_holds`); concept `translation-simulation`, requirement R6. They say nothing of a second fiber, a scope, an interruption, a clock step or
a reply that is refused: the decisions are a host's (`hostDecision`), on one fiber.
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
proof_goal seg_settles_receipt (root : NativeEff) (hroot : PlainHooks root) (fuel : Nat)
    (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat)
    (ctx : Ctx) (hpl : PlainCode cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hreceipt : settled (driveState (evaluator := evaluatorFor root table) (interpOf root table)
      fuel (M (fiberOf cur K i) s k tr nt ctx) [Cmd.loop Api.root false, Cmd.drainDue]) = true) :
    ∃ p', Settled root (driveState (evaluator := evaluatorFor root table) (interpOf root table)
        fuel (M (fiberOf cur K i) s k tr nt ctx) [Cmd.loop Api.root false, Cmd.drainDue]).1 p' ∧
      LeadsQ (table := table) root (.live (fiberOf cur K i) s ctx) p'

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
proof_goal load_evaluate_receipt (root : NativeEff) (hroot : PlainHooks root) (cf F : Nat)
    (h : (stepDecisionState (evaluator := evaluatorFor root table) (interpOf root table)
      F (Api.load root cf) Api.evaluate).2 = true) :
    ∃ p', Settled root (stepDecisionState (evaluator := evaluatorFor root table)
        (interpOf root table) F (Api.load root cf) Api.evaluate).1 p' ∧
      LeadsQ (table := table) root (.live (fiberOf (compile root cf) []) Stores.empty emptyCtx) p'


end Effect4.Program.Agreement

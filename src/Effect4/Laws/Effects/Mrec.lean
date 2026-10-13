import Effects.Algebra.Laws
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Effects.Mrec — a recursive handler, cut at a budget

Goal G5 of the procedures note (`docs/research/2026-10-08-seat-PROC-design.md` §4.3 and §8;
slice PROC-5, decisions row 328). A definition block is a handler of its own signature whose
bodies may invoke the block again, so the handler is recursive. `Program` is well founded, so
the knot is not tied inside it, as DB-04 says of a loop. Interaction Trees tie it with `mrec`
(Xia et al. 2020, §4.2), whose unfolding equation holds up to weak bisimulation. Here the
budgeted form `mrecB` unfolds at most `k` nested invocations, and a deeper one is the frontier
`none`, never a failure (DB-04).

The laws, generic in the two signatures:

* **The chain is monotone** (`mrecB_refines`): one more budget refines every frontier and keeps
  every finished leaf, in the approximation order `Approx`.
* **The unfolding law holds at the limit** (`invoke_cofinal_left`, `invoke_cofinal_right`): the
  chain at an invocation and the chain at its unfolding interleave, budget for budget. No single
  budget satisfies the equation (the red control `budget_not_unfolding`,
  `Test/Program/BlockMeaning.lean`).
* **A finished leaf is observed alike** (`Approx.finishes`): under any handler into two states
  over `Option`, what a lower tree finishes with, a higher tree finishes with. So the limit is
  read by convergence, as the loop's is (`Conv`, `src/Effect4/Laws/Program/IterLimit.lean`):
  `conv_unfold` and `conv_unique`.

Probe PROC-1 proved the first three in a scratch file (the procedures note's appendix A.1), and
the PROC-5 probe ran them on today's tree (`docs/research/2026-10-13-proc5-probe/README.md`).
-/

set_option autoImplicit false

namespace Effect4.Laws.Effects.Mrec

open _root_.Effects

variable {S D : Signature.{0, 0}} {A : Type}

/-- One layer of the knot: the program's own operations pass, and an invocation is handed to
`rec`, applied to the body bound to the invocation's continuation. Structural in the program. -/
def mrecStep (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d))
    (rec : Program (S ⊕ₛ D) A → Program S (Option A)) :
    Program (S ⊕ₛ D) A → Program S (Option A)
  | .pure a => .pure (some a)
  | .vis (.inl s) next => .vis s (fun x => mrecStep rh rec (next x))
  | .vis (.inr d) next => rec ((rh d).bind next)

/-- **The budgeted knot**: at budget `0` every invocation is the frontier `none`; at `k + 1` an
invocation unfolds its body and continues at budget `k`. -/
def mrecB (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) :
    Nat → Program (S ⊕ₛ D) A → Program S (Option A)
  | 0 => mrecStep rh (fun _ => .pure none)
  | k + 1 => mrecStep rh (mrecB rh k)

/-- The approximation order on budgeted results: a frontier leaf is below everything, a
finished leaf only below itself, and an operation node below the same operation whose answers
are each above. -/
inductive Approx : Program S (Option A) → Program S (Option A) → Prop
  | frontier (q : Program S (Option A)) : Approx (.pure none) q
  | done (a : A) : Approx (.pure (some a)) (.pure (some a))
  | vis (s : S.Op) {k k' : S.Answer s → Program S (Option A)} :
      (∀ x, Approx (k x) (k' x)) → Approx (.vis s k) (.vis s k')

theorem Approx.refl : ∀ (p : Program S (Option A)), Approx p p
  | .pure none => .frontier _
  | .pure (some a) => .done a
  | .vis s k => .vis s (fun x => Approx.refl (k x))

/-- The unfolding at one budget is definitional: an invocation at `k + 1` is its body at `k`. -/
theorem mrecB_invoke (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) (k : Nat) (d : D.Op)
    (next : D.Answer d → Program (S ⊕ₛ D) A) :
    mrecB rh (k + 1) (.vis (.inr d) next) = mrecB rh k ((rh d).bind next) := rfl

/-- The step is monotone in its recursive argument. A step of `mrecB_refines`. -/
theorem mrecStep_mono (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d))
    {r r' : Program (S ⊕ₛ D) A → Program S (Option A)} (h : ∀ q, Approx (r q) (r' q)) :
    ∀ p, Approx (mrecStep rh r p) (mrecStep rh r' p)
  | .pure a => .done a
  | .vis (.inl s) next => .vis s (fun x => mrecStep_mono rh h (next x))
  | .vis (.inr _) _ => h _

/-- **The budget chain is monotone** (G5, the claim `block-handler-monotone`): one more budget
refines every frontier and keeps every finished leaf. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem mrecB_refines (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) :
    ∀ (k : Nat) (p : Program (S ⊕ₛ D) A), Approx (mrecB rh k p) (mrecB rh (k + 1) p)
  | 0, p => mrecStep_mono rh (fun _ => .frontier _) p
  | k + 1, p => mrecStep_mono rh (fun q => mrecB_refines rh k q) p

/-- The chain at an invocation is below the chain at its unfolding, budget for budget. A step of
`conv_unfold`. -/
theorem invoke_cofinal_left (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) (d : D.Op)
    (next : D.Answer d → Program (S ⊕ₛ D) A) :
    ∀ k, Approx (mrecB rh k (.vis (.inr d) next)) (mrecB rh k ((rh d).bind next))
  | 0 => .frontier _
  | k + 1 => mrecB_refines rh k _

/-- The chain at the unfolding is below the chain at the invocation, one budget later. A step of
`conv_unfold`. -/
theorem invoke_cofinal_right (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d)) (d : D.Op)
    (next : D.Answer d → Program (S ⊕ₛ D) A) (k : Nat) :
    Approx (mrecB rh k ((rh d).bind next)) (mrecB rh (k + 1) (.vis (.inr d) next)) :=
  Approx.refl _

/-! ## The limit, read by convergence -/

variable {α β : Type}

/-- A tree finishes under a handler with the answer `a`, from the states `s` and `t` to `s'` and
`t'`. -/
def Finishes (h : Handler S (StateT α (StateT β Option))) (p : Program S (Option A)) (s : α)
    (t : β) (a : A) (s' : α) (t' : β) : Prop :=
  ((interpret h p).run s).run t = some ((some a, s'), t')

/-- **A finished leaf is observed alike**: what a tree finishes with, every tree above it
finishes with. A step of `conv_unfold` and `conv_unique`. -/
theorem Approx.finishes (h : Handler S (StateT α (StateT β Option))) :
    ∀ {p q : Program S (Option A)}, Approx p q →
      ∀ {s : α} {t : β} {a : A} {s' : α} {t' : β}, Finishes h p s t a s' t' →
        Finishes h q s t a s' t'
  | _, _, .frontier _, _, _, _, _, _, hp => by
    simp only [Finishes, interpret_pure, StateT.run_pure] at hp
    cases hp
  | _, _, .done _, _, _, _, _, _, hp => hp
  | _, _, .vis o hk, s, t, a, s', t', hp => by
    simp only [Finishes, interpret_vis, StateT.run_bind] at hp ⊢
    revert hp
    cases ((h.handle o).run s).run t with
    | none => exact fun hp => hp
    | some r =>
      intro hp
      exact Approx.finishes h (hk r.1.1) hp

/-- Convergence of the budgeted knot: some budget finishes with the answer `a`. -/
def Conv (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d))
    (h : Handler S (StateT α (StateT β Option))) (p : Program (S ⊕ₛ D) A) (s : α) (t : β)
    (a : A) (s' : α) (t' : β) : Prop :=
  ∃ k, Finishes h (mrecB rh k p) s t a s' t'

/-- A budget that finishes keeps finishing alike at every larger budget. A step of
`conv_unique`. -/
theorem finishes_up (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d))
    (h : Handler S (StateT α (StateT β Option))) (p : Program (S ⊕ₛ D) A) {s : α} {t : β}
    {a : A} {s' : α} {t' : β} :
    ∀ (j k : Nat), Finishes h (mrecB rh k p) s t a s' t' →
      Finishes h (mrecB rh (k + j) p) s t a s' t'
  | 0, _, hk => hk
  | j + 1, k, hk => Approx.finishes h (mrecB_refines rh (k + j) p) (finishes_up rh h p j k hk)

/-- **The unfolding law at the limit** (G5, the claim `block-handler-unfolds`): an invocation
converges exactly when its unfolding does. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem conv_unfold (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d))
    (h : Handler S (StateT α (StateT β Option))) (d : D.Op)
    (next : D.Answer d → Program (S ⊕ₛ D) A) (s : α) (t : β) (a : A) (s' : α) (t' : β) :
    Conv rh h (.vis (.inr d) next) s t a s' t' ↔ Conv rh h ((rh d).bind next) s t a s' t' :=
  ⟨fun ⟨k, hk⟩ => ⟨k, Approx.finishes h (invoke_cofinal_left rh d next k) hk⟩,
   fun ⟨k, hk⟩ => ⟨k + 1, Approx.finishes h (invoke_cofinal_right rh d next k) hk⟩⟩

/-- **The limit is single-valued** (G5, the claim `block-handler-unfolds`; the procedures note's
`mrecB_limit_unique`): two finishing budgets agree, states included. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem conv_unique (rh : (d : D.Op) → Program (S ⊕ₛ D) (D.Answer d))
    (h : Handler S (StateT α (StateT β Option))) (p : Program (S ⊕ₛ D) A) {s : α} {t : β}
    {a a' : A} {s₁ s₂ : α} {t₁ t₂ : β} (h₁ : Conv rh h p s t a s₁ t₁)
    (h₂ : Conv rh h p s t a' s₂ t₂) : a = a' ∧ s₁ = s₂ ∧ t₁ = t₂ := by
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨k', hk'⟩ := h₂
  have e₁ := finishes_up rh h p k' k hk
  have e₂ := finishes_up rh h p k k' hk'
  rw [Nat.add_comm k' k] at e₂
  unfold Finishes at e₁ e₂
  rw [e₁] at e₂
  simp only [Option.some.injEq, Prod.mk.injEq] at e₂
  exact ⟨e₂.1.1, e₂.1.2, e₂.2⟩

end Effect4.Laws.Effects.Mrec

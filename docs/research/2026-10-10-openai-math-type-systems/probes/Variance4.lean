/-!
# Probe: the variance semiring, signed paths and polarity-respecting instantiation

A finite probe, core Lean only (no Mathlib, no Effect4 import). It adapts three pieces of the
OpenAI formalization of the β-Barendregt–Geuvers–Klop conjecture
(`openai/math`, `lean/OAI/Computability/TypeSystem/Profiles.lean`, `Candidates.lean`,
`Signed.lean`) to the type language of this repository:

1. `SignedPath` and `parity_unique` (OAI `Profiles.lean`), re-proved without `simp_all`.
2. The polarity of a variable as the set of parities of signed paths to its occurrences: the
   four-point semiring `Var4 = P(ℤ/2)` (bivariant, co, contra, inv).
3. The monotone fixed point on a sign-flipped lattice (OAI `Signed.lean`, `SignedCandidate`)
   in its finite, choice-free form: Kleene iteration of variance inference over a declaration
   table, with the odd-cycle test `closure n n` (OAI's `¬ SignedPath E I I true`).

The main theorem is `eval_respects`: in any model whose constructors respect their declared
variances one argument at a time, evaluation respects the polarity of every variable.
Copies of `Ty.Variance`, `Ty.Variance.holds` and `Bounds.comp` are checked against `Var4`;
the copies are marked, and a connector against the real declarations is a later slice.
-/

namespace Probe

universe u

/-! ## 1. The four-point variance semiring -/

/-- A variance: whether an even-parity path (`pos`) and an odd-parity path (`neg`) reach an
occurrence. `⟨false, false⟩` is bivariant (no occurrence), `⟨true, false⟩` covariant,
`⟨false, true⟩` contravariant, `⟨true, true⟩` invariant. -/
structure Var4 where
  pos : Bool
  neg : Bool
deriving DecidableEq, Repr

namespace Var4

def bi : Var4 := ⟨false, false⟩
def co : Var4 := ⟨true, false⟩
def contra : Var4 := ⟨false, true⟩
def inv : Var4 := ⟨true, true⟩

/-- Join: the parities of either set of paths. -/
def add (a b : Var4) : Var4 := ⟨a.pos || b.pos, a.neg || b.neg⟩

/-- Composition: parities add along a path (ℤ/2 acting on subsets). -/
def mul (a b : Var4) : Var4 :=
  ⟨(a.pos && b.pos) || (a.neg && b.neg), (a.pos && b.neg) || (a.neg && b.pos)⟩

instance : Add Var4 := ⟨add⟩
instance : Mul Var4 := ⟨mul⟩

@[simp] theorem add_pos (a b : Var4) : (a + b).pos = (a.pos || b.pos) := rfl
@[simp] theorem add_neg (a b : Var4) : (a + b).neg = (a.neg || b.neg) := rfl
@[simp] theorem mul_pos (a b : Var4) : (a * b).pos = ((a.pos && b.pos) || (a.neg && b.neg)) := rfl
@[simp] theorem mul_neg (a b : Var4) : (a * b).neg = ((a.pos && b.neg) || (a.neg && b.pos)) := rfl

/-- The order: inclusion of parity sets. A larger variance is a stronger premise. -/
def le (a b : Var4) : Prop := (a.pos = true → b.pos = true) ∧ (a.neg = true → b.neg = true)

/-! The semiring laws: finite, by cases. -/

theorem add_comm (a b : Var4) : a + b = b + a := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b
  cases p <;> cases n <;> cases q <;> cases m <;> rfl

theorem add_assoc (a b c : Var4) : a + b + c = a + (b + c) := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b; obtain ⟨s, t⟩ := c
  cases p <;> cases n <;> cases q <;> cases m <;> cases s <;> cases t <;> rfl

theorem add_idem (a : Var4) : a + a = a := by
  obtain ⟨p, n⟩ := a; cases p <;> cases n <;> rfl

theorem bi_add (a : Var4) : bi + a = a := by
  obtain ⟨p, n⟩ := a; cases p <;> cases n <;> rfl

theorem mul_comm (a b : Var4) : a * b = b * a := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b
  cases p <;> cases n <;> cases q <;> cases m <;> rfl

theorem mul_assoc (a b c : Var4) : a * b * c = a * (b * c) := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b; obtain ⟨s, t⟩ := c
  cases p <;> cases n <;> cases q <;> cases m <;> cases s <;> cases t <;> rfl

theorem co_mul (a : Var4) : co * a = a := by
  obtain ⟨p, n⟩ := a; cases p <;> cases n <;> rfl

theorem bi_mul (a : Var4) : bi * a = bi := by
  obtain ⟨p, n⟩ := a; cases p <;> cases n <;> rfl

theorem mul_add (a b c : Var4) : a * (b + c) = a * b + a * c := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b; obtain ⟨s, t⟩ := c
  cases p <;> cases n <;> cases q <;> cases m <;> cases s <;> cases t <;> rfl

theorem contra_mul_contra : contra * contra = co := rfl
theorem inv_mul_contra : inv * contra = inv := rfl
theorem inv_mul_bi : inv * bi = bi := rfl

/-- The Kleene star of an idempotent finite semiring element: the parities of any number of
traversals of a loop. `contra* = inv`: a loop through one negative edge reaches both parities. -/
def star (a : Var4) : Var4 := co + a + a * a

theorem star_contra : star contra = inv := rfl
theorem star_co : star co = co := rfl
theorem star_bi : star bi = co := rfl

/-! ## 2. Lifting a relation through a variance -/

/-- A relation read at a variance: each parity in the set asks for one direction. -/
def holds {α : Sort u} (v : Var4) (r : α → α → Prop) (x y : α) : Prop :=
  (v.pos = true → r x y) ∧ (v.neg = true → r y x)

theorem holds_bi {α : Sort u} (r : α → α → Prop) (x y : α) : holds bi r x y :=
  ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

theorem holds_co {α : Sort u} {r : α → α → Prop} {x y : α} : holds co r x y ↔ r x y :=
  ⟨fun h => h.1 rfl, fun h => ⟨fun _ => h, fun h' => Bool.noConfusion h'⟩⟩

theorem holds_contra {α : Sort u} {r : α → α → Prop} {x y : α} : holds contra r x y ↔ r y x :=
  ⟨fun h => h.2 rfl, fun h => ⟨fun h' => Bool.noConfusion h', fun _ => h⟩⟩

theorem holds_add {α : Sort u} {r : α → α → Prop} {x y : α} {a b : Var4} :
    holds (a + b) r x y ↔ holds a r x y ∧ holds b r x y := by
  simp only [holds, add_pos, add_neg, Bool.or_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun h => h1 (Or.inl h), fun h => h2 (Or.inl h)⟩,
      ⟨fun h => h1 (Or.inr h), fun h => h2 (Or.inr h)⟩⟩
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    exact ⟨fun h => h.elim a1 b1, fun h => h.elim a2 b2⟩

/-- A larger variance is a stronger premise. -/
theorem holds_le {α : Sort u} {r : α → α → Prop} {x y : α} {a b : Var4} (hab : le a b)
    (h : holds b r x y) : holds a r x y :=
  ⟨fun hp => h.1 (hab.1 hp), fun hn => h.2 (hab.2 hn)⟩

/-- **Composition (the step of a signed path).** If `F` respects the polarities `p` in each
variable, then reading every variable at `v * p i` gives `F` at `v`. The four cases of `v` are
the four ways an outer position reads an inner one. -/
theorem holds_mul {α β : Sort u} {rα : α → α → Prop} {rβ : β → β → Prop}
    (v : Var4) (p : Nat → Var4) (F : (Nat → α) → β)
    (hF : ∀ ρ ρ' : Nat → α, (∀ i, holds (p i) rα (ρ i) (ρ' i)) → rβ (F ρ) (F ρ'))
    (ρ ρ' : Nat → α) (h : ∀ i, holds (v * p i) rα (ρ i) (ρ' i)) :
    holds v rβ (F ρ) (F ρ') := by
  obtain ⟨vp, vn⟩ := v
  constructor
  · intro hvp
    simp only at hvp
    subst hvp
    apply hF
    intro i
    obtain ⟨h1, h2⟩ := h i
    constructor
    · intro hp
      exact h1 (by simp only [mul_pos, hp, Bool.and_self, Bool.true_or])
    · intro hn
      exact h2 (by simp only [mul_neg, hn, Bool.and_self, Bool.true_or])
  · intro hvn
    simp only at hvn
    subst hvn
    apply hF
    intro i
    obtain ⟨h1, h2⟩ := h i
    constructor
    · intro hp
      exact h2 (by simp only [mul_neg, hp, Bool.and_self, Bool.or_true])
    · intro hn
      exact h1 (by simp only [mul_pos, hn, Bool.and_self, Bool.or_true])

end Var4

open Var4

/-! ## 3. A signature with variances, its terms, and the polarity fold -/

/-- A signature whose arrows carry variances: each constructor has an arity and a variance
for each child position. -/
structure Sig where
  C : Type
  arity : C → Nat
  vari : (c : C) → Fin (arity c) → Var4

inductive Tm (S : Sig) : Type where
  | var : Nat → Tm S
  | node : (c : S.C) → (Fin (S.arity c) → Tm S) → Tm S

def sumFin : (n : Nat) → (Fin n → Var4) → Var4
  | 0, _ => bi
  | n + 1, f => f 0 + sumFin n (fun k => f k.succ)

theorem holds_sumFin {α : Sort u} {r : α → α → Prop} {x y : α} :
    ∀ (n : Nat) (f : Fin n → Var4), holds (sumFin n f) r x y → ∀ k, holds (f k) r x y
  | 0, _, _, k => k.elim0
  | n + 1, f, h, k => by
    have h' := holds_add.mp h
    cases k using Fin.cases with
    | zero => exact h'.1
    | succ k => exact holds_sumFin n (fun j => f j.succ) h'.2 k

theorem sumFin_pos : ∀ (n : Nat) (f : Fin n → Var4),
    (sumFin n f).pos = true ↔ ∃ k, (f k).pos = true
  | 0, _ => ⟨fun h => Bool.noConfusion h, fun ⟨k, _⟩ => k.elim0⟩
  | n + 1, f => by
    simp only [sumFin, add_pos, Bool.or_eq_true]
    rw [sumFin_pos n]
    constructor
    · rintro (h | ⟨k, hk⟩)
      · exact ⟨0, h⟩
      · exact ⟨k.succ, hk⟩
    · rintro ⟨k, hk⟩
      cases k using Fin.cases with
      | zero => exact Or.inl hk
      | succ k => exact Or.inr ⟨k, hk⟩

theorem sumFin_neg : ∀ (n : Nat) (f : Fin n → Var4),
    (sumFin n f).neg = true ↔ ∃ k, (f k).neg = true
  | 0, _ => ⟨fun h => Bool.noConfusion h, fun ⟨k, _⟩ => k.elim0⟩
  | n + 1, f => by
    simp only [sumFin, add_neg, Bool.or_eq_true]
    rw [sumFin_neg n]
    constructor
    · rintro (h | ⟨k, hk⟩)
      · exact ⟨0, h⟩
      · exact ⟨k.succ, hk⟩
    · rintro ⟨k, hk⟩
      cases k using Fin.cases with
      | zero => exact Or.inl hk
      | succ k => exact Or.inr ⟨k, hk⟩

variable {S : Sig}

/-- **The polarity fold**: the variance at which a term reads variable `i`. -/
def polarity : Tm S → Nat → Var4
  | .var j, i => if i = j then co else bi
  | .node c ts, i => sumFin (S.arity c) (fun k => S.vari c k * polarity (ts k) i)

/-! ## 4. Signed paths: polarity is the set of path parities (OAI `SignedPath`) -/

/-- An edge at a position of variance `v` has sign `e` when `v` contains parity `e`. -/
def EdgeSign (v : Var4) : Bool → Prop
  | true => v.neg = true
  | false => v.pos = true

/-- A path from the root of a term to an occurrence of variable `i`, with its parity. -/
inductive Reach : Tm S → Nat → Bool → Prop
  | here (i : Nat) : Reach (.var i) i false
  | down {c : S.C} {ts : Fin (S.arity c) → Tm S} {i : Nat} (k : Fin (S.arity c)) (e b p : Bool) :
      EdgeSign (S.vari c k) e → Reach (ts k) i b → xor e b = p → Reach (.node c ts) i p

mutual
/-- **Polarity is path parity**, even half. -/
theorem polarity_pos_iff : ∀ (t : Tm S) (i : Nat), (polarity t i).pos = true ↔ Reach t i false
  | .var j, i => by
    by_cases hij : i = j
    · subst hij
      simp only [polarity]
      exact ⟨fun _ => .here i, fun _ => rfl⟩
    · simp only [polarity, if_neg hij]
      exact ⟨fun h => Bool.noConfusion h, fun h => by cases h; exact absurd rfl hij⟩
  | .node c ts, i => by
    simp only [polarity]
    rw [sumFin_pos]
    constructor
    · rintro ⟨k, hk⟩
      simp only [mul_pos, Bool.or_eq_true, Bool.and_eq_true] at hk
      rcases hk with ⟨hv, hp⟩ | ⟨hv, hn⟩
      · exact .down k false false false hv ((polarity_pos_iff (ts k) i).mp hp) rfl
      · exact .down k true true false hv ((polarity_neg_iff (ts k) i).mp hn) rfl
    · intro h
      cases h with
      | down k e b _ he hr hx =>
        refine ⟨k, ?_⟩
        simp only [mul_pos, Bool.or_eq_true, Bool.and_eq_true]
        cases e <;> cases b <;> cases hx
        · exact Or.inl ⟨he, (polarity_pos_iff (ts k) i).mpr hr⟩
        · exact Or.inr ⟨he, (polarity_neg_iff (ts k) i).mpr hr⟩
/-- **Polarity is path parity**, odd half. -/
theorem polarity_neg_iff : ∀ (t : Tm S) (i : Nat), (polarity t i).neg = true ↔ Reach t i true
  | .var j, i => by
    simp only [polarity]
    by_cases hij : i = j
    · simp only [if_pos hij]
      exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
    · simp only [if_neg hij]
      exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
  | .node c ts, i => by
    simp only [polarity]
    rw [sumFin_neg]
    constructor
    · rintro ⟨k, hk⟩
      simp only [mul_neg, Bool.or_eq_true, Bool.and_eq_true] at hk
      rcases hk with ⟨hv, hn⟩ | ⟨hv, hp⟩
      · exact .down k false true true hv ((polarity_neg_iff (ts k) i).mp hn) rfl
      · exact .down k true false true hv ((polarity_pos_iff (ts k) i).mp hp) rfl
    · intro h
      cases h with
      | down k e b _ he hr hx =>
        refine ⟨k, ?_⟩
        simp only [mul_neg, Bool.or_eq_true, Bool.and_eq_true]
        cases e <;> cases b <;> cases hx
        · exact Or.inl ⟨he, (polarity_neg_iff (ts k) i).mpr hr⟩
        · exact Or.inr ⟨he, (polarity_pos_iff (ts k) i).mpr hr⟩
end

/-! ## 5. Models, and evaluation respects polarity -/

/-- A model of the signature: a preorder and constructors that respect their declared
variance **one argument at a time** (the unary translations of `Algebra/Universal`). -/
structure Model (S : Sig) (α : Type) where
  r : α → α → Prop
  refl : ∀ a, r a a
  trans : ∀ {a b c}, r a b → r b c → r a c
  I : (c : S.C) → (Fin (S.arity c) → α) → α
  unary : ∀ (c : S.C) (k : Fin (S.arity c)) (xs ys : Fin (S.arity c) → α),
    (∀ j, j ≠ k → xs j = ys j) → holds (S.vari c k) r (xs k) (ys k) → r (I c xs) (I c ys)

def eval {α : Type} (M : Model S α) (ρ : Nat → α) : Tm S → α
  | .var i => ρ i
  | .node c ts => M.I c (fun k => eval M ρ (ts k))

/-- Changing all arguments, one position at a time. -/
theorem Model.chain {α : Type} (M : Model S α) (c : S.C) (xs ys : Fin (S.arity c) → α)
    (h : ∀ k, holds (S.vari c k) M.r (xs k) (ys k)) : M.r (M.I c xs) (M.I c ys) := by
  let mix (j : Nat) : Fin (S.arity c) → α := fun k => if k.val < j then ys k else xs k
  have step : ∀ j, j ≤ S.arity c → M.r (M.I c xs) (M.I c (mix j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      have : mix 0 = xs := funext fun k => if_neg (Nat.not_lt_zero _)
      rw [this]
      exact M.refl _
    | succ j ih =>
      intro hj
      refine M.trans (ih (Nat.le_of_succ_le hj)) ?_
      apply M.unary c ⟨j, hj⟩ (mix j) (mix (j + 1))
      · intro k hk
        have hne : k.val ≠ j := fun he => hk (Fin.ext he)
        show (if k.val < j then ys k else xs k) = (if k.val < j + 1 then ys k else xs k)
        by_cases hlt : k.val < j
        · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
        · rw [if_neg hlt, if_neg (fun h' => hlt (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') hne))]
      · show holds (S.vari c ⟨j, hj⟩) M.r (if j < j then ys _ else xs _)
          (if j < j + 1 then ys _ else xs _)
        rw [if_neg (Nat.lt_irrefl j), if_pos (Nat.lt_succ_self j)]
        exact h _
  have hend : mix (S.arity c) = ys := funext fun k => if_pos k.isLt
  have := step (S.arity c) (Nat.le_refl _)
  rwa [hend] at this

/-- **Evaluation respects polarity.** If every variable's two bindings are related at that
variable's polarity in `t`, the two values of `t` are related. A bivariant variable needs
nothing, an invariant one needs both directions. This is the law that instantiating a
template at smaller bindings gives a smaller type, read at each parameter's polarity. -/
theorem eval_respects {α : Type} (M : Model S α) :
    ∀ (t : Tm S) (ρ ρ' : Nat → α), (∀ i, holds (polarity t i) M.r (ρ i) (ρ' i)) →
      M.r (eval M ρ t) (eval M ρ' t)
  | .var j, ρ, ρ', h => by
    have hj := h j
    simp only [polarity] at hj
    exact holds_co.mp hj
  | .node c ts, ρ, ρ', h => by
    apply M.chain
    intro k
    exact holds_mul (S.vari c k) (polarity (ts k)) (fun ρ => eval M ρ (ts k))
      (fun ρ ρ' h' => eval_respects M (ts k) ρ ρ' h') ρ ρ'
      (fun i => holds_sumFin _ _ (h i) k)

/-- **The precision of the least solution** (Pierce–Turner's case split): where the answer
reads each solved variable covariantly or not at all, a pointwise smaller solution gives a
smaller answer. -/
theorem least_solution_least_answer {α : Type} (M : Model S α) (t : Tm S) (ρ ρ' : Nat → α)
    (hco : ∀ i, le (polarity t i) co) (hle : ∀ i, M.r (ρ i) (ρ' i)) :
    M.r (eval M ρ t) (eval M ρ' t) :=
  eval_respects M t ρ ρ' fun i => holds_le (hco i) (holds_co.mpr (hle i))

/-- Where the answer reads each solved variable contravariantly or not at all, the greatest
solution gives the smallest answer. -/
theorem greatest_solution_least_answer {α : Type} (M : Model S α) (t : Tm S) (ρ ρ' : Nat → α)
    (hcontra : ∀ i, le (polarity t i) contra) (hle : ∀ i, M.r (ρ' i) (ρ i)) :
    M.r (eval M ρ t) (eval M ρ' t) :=
  eval_respects M t ρ ρ' fun i => holds_le (hcontra i) (holds_contra.mpr (hle i))

/-! ## 6. OAI's `SignedPath` and `parity_unique`, re-proved by cases -/

inductive SignedPath {V : Type} (E : V → V → Bool → Prop) : V → V → Bool → Prop
  | nil (v : V) : SignedPath E v v false
  | cons {u v w : V} {p q : Bool} : E u v p → SignedPath E v w q → SignedPath E u w (xor p q)

theorem SignedPath.append {V : Type} {E : V → V → Bool → Prop} {v w z : V} {p q : Bool}
    (h : SignedPath E v w p) (k : SignedPath E w z q) : SignedPath E v z (xor p q) := by
  induction h with
  | nil v => simpa using k
  | cons he _ ih => simpa only [Bool.xor_assoc] using SignedPath.cons he (ih k)

/-- In a strongly connected part with no odd closed path, all paths between two vertices have
one parity: the part has a consistent signing (OAI `SignedPath.parity_unique`). -/
theorem SignedPath.parity_unique {V : Type} {E : V → V → Bool → Prop} {v w : V} {p q r : Bool}
    (h : SignedPath E v w p) (k : SignedPath E v w q) (hr : SignedPath E w v r)
    (hodd : ¬ SignedPath E v v true) : p = q := by
  have hp := h.append hr
  have hq := k.append hr
  -- the cases in the order (p, q, r): fff, fft, ftf, ftt, tff, tft, ttf, ttt
  cases p <;> cases q <;> cases r
  · rfl
  · rfl
  · exact absurd hq hodd
  · exact absurd hp hodd
  · exact absurd hp hodd
  · exact absurd hq hodd
  · rfl
  · rfl

/-! ## 7. Copies of the tree's three-valued variance, checked against `Var4`

`V3` copies `Effect4.Program.Ty.Variance` (`src/Effect4/Program/TyVariance.lean`), `holds3`
copies `Ty.Variance.holds`, and `comp3` copies `Bounds.comp` (`src/Effect4/Program/Bounds.lean`).
They are copies, so these checks are evidence about the copies only. -/

inductive V3 | co | contra | inv
deriving DecidableEq, Repr

def V3.toVar4 : V3 → Var4
  | .co => Var4.co
  | .contra => Var4.contra
  | .inv => Var4.inv

def holds3 {α : Type} (r : α → α → Bool) : V3 → α → α → Bool
  | .co, x, y => r x y
  | .contra, x, y => r y x
  | .inv, x, y => r x y && r y x

def comp3 : V3 → V3 → V3
  | .inv, _ => .inv
  | _, .inv => .inv
  | .co, v => v
  | .contra, .co => .contra
  | .contra, .contra => .co

/-- The Boolean reading of `holds`. -/
def holdsB {α : Type} (v : Var4) (r : α → α → Bool) (x y : α) : Bool :=
  (!v.pos || r x y) && (!v.neg || r y x)

/-- `Bounds.comp` is the semiring's product on the three values it has. -/
theorem comp3_agrees (a b : V3) : (comp3 a b).toVar4 = a.toVar4 * b.toVar4 := by
  cases a <;> cases b <;> rfl

/-- `Ty.Variance.holds` is the Boolean `holds` on the three values it has. -/
theorem holds3_agrees {α : Type} (r : α → α → Bool) (v : V3) (x y : α) :
    holds3 r v x y = holdsB v.toVar4 r x y := by
  cases v <;> simp only [holds3, holdsB, V3.toVar4, Var4.co, Var4.contra, Var4.inv,
    Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.and_true, Bool.true_and]

/-- The three values miss the bivariant point: no `V3` maps to `bi`, and `bi` is the product's
zero. A phantom parameter therefore reads as invariant in the tree today
(`Ty.argVariance`'s default `.inv`). -/
theorem no_bi (v : V3) : v.toVar4 ≠ Var4.bi := by
  cases v <;> decide

/-! ## 8. Variance inference over a declaration table, by Kleene iteration

A small type language with one-parameter generic declarations: `ref` is an invariant cell,
`ctx` a contravariant position (`Context.Context`), `app n a` a reference to declaration `n`. -/

inductive T where
  | var0 | nat | str
  | list (a : T) | pair (a b : T) | union (a b : T)
  | ref (a : T) | ctx (a : T)
  | app (n : String) (a : T)
deriving Repr

abbrev Table := List (String × Var4)

def Table.get (V : Table) (n : String) : Var4 := ((V.lookup n).getD Var4.bi)

/-- The polarity of the parameter in a body, reading a declaration at the table's variance. -/
def pol (V : Table) : T → Var4
  | .var0 => co
  | .nat | .str => bi
  | .list a => pol V a
  | .pair a b | .union a b => pol V a + pol V b
  | .ref a => inv * pol V a
  | .ctx a => contra * pol V a
  | .app n a => V.get n * pol V a

abbrev Decls := List (String × T)

def stepTable (ds : Decls) (V : Table) : Table := ds.map fun d => (d.1, pol V d.2)

/-- Kleene iteration from the bivariant table. The lattice has height two per entry, so
`2 * ds.length + 1` rounds reach the least fixed point. -/
def infer (ds : Decls) : Table := (List.range (2 * ds.length + 1)).foldl (fun V _ => stepTable ds V)
  (ds.map fun d => (d.1, Var4.bi))

def isFixed (ds : Decls) (V : Table) : Bool := stepTable ds V == V

/-- The sign with which body `t` reaches declaration `m` (the edge label of the declaration
graph): the parities of paths from the body's root to an `app m`. -/
def reachDecl (V : Table) (m : String) : T → Var4
  | .var0 | .nat | .str => bi
  | .list a => reachDecl V m a
  | .pair a b | .union a b => reachDecl V m a + reachDecl V m b
  | .ref a => inv * reachDecl V m a
  | .ctx a => contra * reachDecl V m a
  | .app n a => (if n == m then co else bi) + V.get n * reachDecl V m a

/-- The edge labels of the declaration graph: `edge a b` is the parity set with which the body
of `a` reaches a reference to `b`. -/
def edge (ds : Decls) (V : Table) (a b : String) : Var4 :=
  ((ds.lookup a).map (reachDecl V b)).getD bi

/-- One round of relaxation of the path table: paths of one more edge. -/
def relax (ds : Decls) (V : Table) (D : String → String → Var4) : String → String → Var4 :=
  fun a b => edge ds V a b + ds.foldl (fun acc d => acc + edge ds V a d.1 * D d.1 b) bi

/-- Closure of the declaration graph (the algebraic path problem over `Var4`): after `n` rounds,
the parity set of paths of length at most `n` from `a` to `b`. Each round is tabulated, so the
cost is polynomial. -/
def close (ds : Decls) (V : Table) (n : Nat) : String → String → Var4 :=
  let names := ds.map (·.1)
  let tab (D : String → String → Var4) : List ((String × String) × Var4) :=
    names.flatMap fun a => names.map fun b => ((a, b), relax ds V D a b)
  let look (t : List ((String × String) × Var4)) : String → String → Var4 :=
    fun a b => (t.lookup (a, b)).getD bi
  look ((List.range n).foldl (fun t _ => tab (look t)) [])

/-- A declaration lies on an odd cycle when a path from it back to itself has odd parity:
OAI's `SignedPath E I I true`. Its set meaning is then no monotone fixed point, flipped or not. -/
def oddCycle (ds : Decls) (n : String) : Bool := (close ds (infer ds) (2 * ds.length) n n).neg

def ex : Decls :=
  [ ("Tree",    .pair .var0 (.list (.app "Tree" .var0)))      -- covariant recursion
  , ("Sink",    .ctx .var0)                                    -- contravariant
  , ("Both",    .pair .var0 (.app "Sink" .var0))               -- invariant
  , ("Phantom", .str)                                          -- bivariant
  , ("Flip",    .ctx (.app "Flip" .var0))                      -- phantom through recursion
  , ("Odd",     .pair .var0 (.ctx (.app "Odd" .var0)))         -- odd self-cycle
  , ("Even",    .pair .var0 (.ctx (.ctx (.app "Even" .var0)))) -- even self-cycle
  , ("Cell",    .ref (.app "Tree" .var0)) ]                    -- invariant through a cell

#guard isFixed ex (infer ex)
#guard (infer ex).get "Tree" == Var4.co
#guard (infer ex).get "Sink" == Var4.contra
#guard (infer ex).get "Both" == Var4.inv
#guard (infer ex).get "Phantom" == Var4.bi
#guard (infer ex).get "Flip" == Var4.bi
#guard (infer ex).get "Odd" == Var4.inv
#guard (infer ex).get "Even" == Var4.co
#guard (infer ex).get "Cell" == Var4.inv

#guard oddCycle ex "Odd" == true
#guard oddCycle ex "Flip" == true
#guard oddCycle ex "Even" == false
#guard oddCycle ex "Tree" == false
#guard oddCycle ex "Both" == false

end Probe

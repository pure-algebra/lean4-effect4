import Effect4.Program.Polarity
import Effect4.Program.Bounds
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Polarity — the variance semiring, and the tree's copies of it

Slice VAR-1 (`docs/research/2026-10-10-openai-math-type-systems/brief.md`). `Var4` with join and
composition is a commutative idempotent semiring with `bi` as zero and `co` as one; its order is
inclusion. The two copies the tree held agree with it on their images: the composition along the
match's walk (`Bounds.comp`) is the product, and the Boolean reading `Ty.sub` uses at a reference
(`Ty.Variance.select`) is `Var4.select`. A larger variance asks more (`select_le`).

Placement: concept `subtyping-algebra`, claim `variance-semiring` (role compatibility; pointer
`Var4.semiring_laws`). Its consumers are the polarity law of instantiation (slice VAR-2, claim
`instantiate-respects-polarity`) and the row census (slice VAR-3). Reach: the four variances, at
every Boolean relation. It establishes no subtyping fact of `Ty`.
-/

set_option autoImplicit false

namespace Effect4.Program

namespace Var4

theorem ext_iff' {a b : Var4} : a = b ↔ a.pos = b.pos ∧ a.neg = b.neg := by
  obtain ⟨p, n⟩ := a
  obtain ⟨q, m⟩ := b
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

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

theorem le_refl (a : Var4) : le a a = true := by
  obtain ⟨p, n⟩ := a; cases p <;> cases n <;> rfl

theorem le_trans {a b c : Var4} (hab : le a b = true) (hbc : le b c = true) : le a c = true := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b; obtain ⟨s, t⟩ := c
  revert hab hbc
  cases p <;> cases n <;> cases q <;> cases m <;> cases s <;> cases t <;> decide

/-- Join is the least upper bound in the order. -/
theorem le_add_iff (a b c : Var4) : le (a + b) c = (le a c && le b c) := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b; obtain ⟨s, t⟩ := c
  cases p <;> cases n <;> cases q <;> cases m <;> cases s <;> cases t <;> rfl

/-- A larger variance asks more: what it accepts, a smaller one accepts. -/
theorem select_le {a b : Var4} (hab : le a b = true) {xy yx : Bool}
    (h : select b xy yx = true) : select a xy yx = true := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b
  revert hab h
  cases p <;> cases n <;> cases q <;> cases m <;> cases xy <;> cases yx <;> decide

/-- Reading at a join asks both readings. -/
theorem select_add (a b : Var4) (xy yx : Bool) :
    select (a + b) xy yx = (select a xy yx && select b xy yx) := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b
  cases p <;> cases n <;> cases q <;> cases m <;> cases xy <;> cases yx <;> rfl

/-- **The variance semiring** (claim `variance-semiring`): join and composition form a commutative
idempotent semiring with `bi` as zero and `co` as one, composition distributes over join, and
the order is a preorder whose join is `+`. A step of `instantiate-respects-polarity` (slice VAR-2)
and of the row census (slice VAR-3). -/
@[semantics "subtyping-algebra" (requirement := R10)]
theorem semiring_laws :
    (∀ a b : Var4, a + b = b + a) ∧ (∀ a b c : Var4, a + b + c = a + (b + c)) ∧
      (∀ a : Var4, a + a = a) ∧ (∀ a : Var4, bi + a = a) ∧
      (∀ a b : Var4, a * b = b * a) ∧ (∀ a b c : Var4, a * b * c = a * (b * c)) ∧
      (∀ a : Var4, co * a = a) ∧ (∀ a : Var4, bi * a = bi) ∧
      (∀ a b c : Var4, a * (b + c) = a * b + a * c) ∧
      (∀ a : Var4, le a a = true) ∧
      (∀ a b c : Var4, le (a + b) c = (le a c && le b c)) :=
  ⟨add_comm, add_assoc, add_idem, bi_add, mul_comm, mul_assoc, co_mul, bi_mul, mul_add, le_refl,
    le_add_iff⟩

end Var4

/-! ## The tree's copies, as images of `Var4` -/

/-- **The walk's composition is the product** (`Bounds.comp`, `src/Effect4/Program/Bounds.lean`):
on the image of the declared alphabet, composing two positions is multiplying their parity sets.
A step of `variance-semiring`; its consumer is the match's polarity (slice VAR-4). -/
@[semantics "subtyping-algebra"]
theorem Bounds.comp_toVar4 (a b : Ty.Variance) :
    (Bounds.comp a b).toVar4 = a.toVar4 * b.toVar4 := by
  cases a <;> cases b <;> rfl

/-- **The reference's reading is `Var4.select`** (`Ty.Variance.select`, which `Ty.sub` reads at
`app`): on the image of the declared alphabet, the two Boolean readings agree. A step of
`variance-semiring`; its consumer is the subtyping reading of slice VAR-2. -/
@[semantics "subtyping-algebra"]
theorem Ty.Variance.select_toVar4 (v : Ty.Variance) (xy yx : Bool) :
    v.select xy yx = v.toVar4.select xy yx := by
  cases v <;> cases xy <;> cases yx <;> rfl

/-- No declared variance is bivariant: the declared alphabet has no point for a phantom
parameter, which `Ty.argVariance` then reads as `inv`. -/
theorem Ty.Variance.toVar4_ne_bi (v : Ty.Variance) : v.toVar4 ≠ Var4.bi := by
  cases v <;> decide

/-! ## Instantiation respects polarity (slice VAR-2) -/

/-- The binding of parameter `i` in a substitution: its entry, or `never`, as `Ty.instantiate`
reads it. -/
def Ty.Subst.at (σ : Ty.Subst) (i : Nat) : Ty := (σ.lookup i).getD .never

/-- **Instantiation respects polarity** (claim `instantiate-respects-polarity`, slice VAR-2): if
every parameter's two bindings are related by `Ty.sub` at the parameter's polarity in `t` (a
bivariant parameter asks nothing, an invariant one both directions), the two instances are
related. It is the probe's `eval_respects` at the model of `Ty` (raw `Ty.sub`, each head read at
its variance, `HeadReading.sub`). Its consumers are `checker-monotone`'s share at a row (with
`Bounds.matchArgsB_monotone`, at an answer that reads its parameters at co or bi) and HO-4's
instantiated rows. It establishes no semantic variance and nothing of tsgo's inference. -/
@[semantics "subtyping-algebra" (requirement := R10)]
proof_goal Ty.sub_instantiate_polarity (t : Ty) (σ σ' : Ty.Subst)
    (h : ∀ i, (t.polarity .sub i).select (Ty.sub (σ.at i) (σ'.at i))
      (Ty.sub (σ'.at i) (σ.at i)) = true) :
    Ty.sub (Ty.instantiate σ t) (Ty.instantiate σ' t) = true

end Effect4.Program

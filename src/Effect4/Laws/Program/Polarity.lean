import Effect4.Program.Polarity
import Effect4.Program.Bounds
import Effect4.Laws.Program.Template
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

/-! ## Instantiation respects polarity (slice VAR-2)

The proof is the probe's `eval_respects` at the model of `Ty`. Its one view of a head is the
generated one (`Ty.sub_eq_args`, `Laws/Program/TyView.lean`): two members with one head and no
leaf or top rule between them are related exactly when their arguments are, each at its
variance (`Ty.args`). A parameter's polarity in a head bounds each argument's share
(`polarity_args`), so the premise passes to each argument; a position with an odd path asks the
converse, which is the same statement at the swapped substitutions (`PolarityRelated.swap`). -/

namespace Var4

theorem le_add_left (a b : Var4) : le a (a + b) = true := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b
  cases p <;> cases n <;> cases q <;> cases m <;> rfl

theorem le_add_right (a b : Var4) : le b (a + b) = true := by
  obtain ⟨p, n⟩ := a; obtain ⟨q, m⟩ := b
  cases p <;> cases n <;> cases q <;> cases m <;> rfl

/-- Reading at `contra` composed with `p` is reading at `p` the other way round. -/
theorem select_contra_mul (p : Var4) (x y : Bool) : select (contra * p) x y = select p y x := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> cases x <;> cases y <;> rfl

/-- A position with an even path reads its content at least at the content's own polarity. -/
theorem le_self_mul (w p : Var4) (h : w.pos = true) : le p (w * p) = true := by
  obtain ⟨wp, wn⟩ := w; obtain ⟨a, b⟩ := p
  cases h
  cases wn <;> cases a <;> cases b <;> rfl

/-- A position with an odd path reads its content at least at the content's converse polarity. -/
theorem le_contra_mul (w p : Var4) (h : w.neg = true) : le (contra * p) (w * p) = true := by
  obtain ⟨wp, wn⟩ := w; obtain ⟨a, b⟩ := p
  cases h
  cases wp <;> cases a <;> cases b <;> rfl

/-- A reading holds when each parity it has asks a direction that holds. -/
theorem select_of (w : Var4) {x y : Bool} (hx : w.pos = true → x = true)
    (hy : w.neg = true → y = true) : select w x y = true := by
  obtain ⟨p, n⟩ := w
  cases p <;> cases n
  · rfl
  · show ((!false || x) && (!true || y)) = true
    rw [hy rfl]
    rfl
  · show ((!true || x) && (!false || y)) = true
    rw [hx rfl]
    rfl
  · show ((!true || x) && (!true || y)) = true
    rw [hx rfl, hy rfl]
    rfl

theorem le_foldr_add {l : List Var4} {x : Var4} (hx : x ∈ l) :
    le x (l.foldr (· + ·) bi) = true := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_add_left x _
    · exact le_trans (ih h) (le_add_right y _)

end Var4

/-- The binding of parameter `i` in a substitution: its entry, or `never`, as `Ty.instantiate`
reads it. -/
def Ty.Subst.at (σ : Ty.Subst) (i : Nat) : Ty := (σ.lookup i).getD .never

/-- The premise of VAR-2 at a polarity map: each parameter's two bindings are related at its
polarity. -/
def PolarityRelated (p : Nat → Var4) (σ σ' : Ty.Subst) : Prop :=
  ∀ i, (p i).select (Ty.sub (σ.at i) (σ'.at i)) (Ty.sub (σ'.at i) (σ.at i)) = true

/-- A smaller polarity asks less. -/
theorem PolarityRelated.mono {p q : Nat → Var4} (hle : ∀ i, Var4.le (p i) (q i) = true)
    {σ σ' : Ty.Subst} (h : PolarityRelated q σ σ') : PolarityRelated p σ σ' :=
  fun i => Var4.select_le (hle i) (h i)

/-- The converse polarity at one pair is the polarity at the swapped pair. -/
theorem PolarityRelated.swap {p : Nat → Var4} {σ σ' : Ty.Subst}
    (h : PolarityRelated (fun i => Var4.contra * p i) σ σ') : PolarityRelated p σ' σ := by
  intro i
  have hi := h i
  rw [Var4.select_contra_mul] at hi
  exact hi

/-- The join of the shares of a reference's arguments bounds each share. -/
theorem appPolarity_le (at_ : Nat → Var4) :
    ∀ (xs : List Var4) (off k : Nat) (x : Var4), (x, k) ∈ (xs.zipIdx off) →
      Var4.le (at_ k * x) (appPolarity at_ off xs) = true
  | [], _, _, _, h => by cases h
  | y :: ys, off, k, x, h => by
    rw [List.zipIdx_cons, List.mem_cons] at h
    rcases h with h | h
    · cases h
      exact Var4.le_add_left _ _
    · exact Var4.le_trans (appPolarity_le at_ ys (off + 1) k x h) (Var4.le_add_right _ _)

theorem polarity_record (r : HeadReading) (i : Nat) (fs : List (String × Bool × Ty)) :
    (Ty.record fs).polarity r i = (fs.map fun f => f.2.2.polarity r i).foldr (· + ·) .bi := by
  unfold Ty.polarity
  rw [cata_ty_record]
  show (fs.map (prodMapSnd (prodMapSnd (cata_ty (polarityAlg r i))))).foldr
      (fun f acc => f.2.2 + acc) .bi = _
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    obtain ⟨n, b, t⟩ := f
    simp only [List.map_cons, List.foldr_cons, prodMapSnd_mk]
    rw [ih]

theorem polarity_tuple (r : HeadReading) (i : Nat) (ts : List Ty) :
    (Ty.tuple ts).polarity r i = (ts.map fun t => t.polarity r i).foldr (· + ·) .bi := by
  unfold Ty.polarity
  rw [cata_ty_tuple]
  rfl

theorem polarity_app (r : HeadReading) (i : Nat) (n : String) (ts : List Ty) :
    (Ty.app n ts).polarity r i = appPolarity (r.app n) 0 (ts.map fun t => t.polarity r i) := by
  unfold Ty.polarity
  rw [cata_ty_app]
  rfl

/-- **A head's polarity bounds each argument's share**: an argument read at variance `v` adds
`v * p` to the head's polarity, at `Ty.sub`'s reading. A step of `sub_instantiate_polarity`. -/
theorem polarity_args : ∀ (t : Ty) {v : Ty.Variance} {x : Ty}, (v, x) ∈ t.args → ∀ i,
    Var4.le (v.toVar4 * x.polarity .sub i) (t.polarity .sub i) = true := by
  intro t v x hx i
  cases t with
  | option a | list a | causeOf a =>
    simp only [Ty.args, List.mem_singleton, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp only [Ty.Variance.toVar4]
    rw [Var4.co_mul]
    exact Var4.le_refl _
  | prod a b | except a b | exitOf a b | union a b =>
    simp only [Ty.args, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Ty.Variance.toVar4]
    · rw [Var4.co_mul]
      exact Var4.le_add_left _ _
    · rw [Var4.co_mul]
      exact Var4.le_add_right _ _
  | fiberOf a b =>
    simp only [Ty.args, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hx
    show Var4.le _ (Var4.co * (a.polarity .sub i + b.polarity .sub i)) = true
    rw [Var4.co_mul]
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Ty.Variance.toVar4]
    · rw [Var4.co_mul]
      exact Var4.le_add_left _ _
    · rw [Var4.co_mul]
      exact Var4.le_add_right _ _
  | refOf a =>
    simp only [Ty.args, List.mem_singleton, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp only [Ty.Variance.toVar4]
    exact Var4.le_refl _
  | deferredOf a b =>
    simp only [Ty.args, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hx
    show Var4.le _ (Var4.inv * (a.polarity .sub i + b.polarity .sub i)) = true
    rw [Var4.mul_add]
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Ty.Variance.toVar4]
    · exact Var4.le_add_left _ _
    · exact Var4.le_add_right _ _
  | map k w =>
    simp only [Ty.args, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hx
    show Var4.le _ (Var4.inv * k.polarity .sub i + w.polarity .sub i) = true
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Ty.Variance.toVar4]
    · exact Var4.le_add_left _ _
    · rw [Var4.co_mul]
      exact Var4.le_add_right _ _
  | record fs =>
    simp only [Ty.args, List.mem_map, Prod.mk.injEq] at hx
    obtain ⟨f, hf, rfl, rfl⟩ := hx
    simp only [Ty.Variance.toVar4]
    rw [polarity_record, Var4.co_mul]
    exact Var4.le_foldr_add (List.mem_map.mpr ⟨f, Ty.mem_canon hf, rfl⟩)
  | tuple ts =>
    simp only [Ty.args, List.mem_map, Prod.mk.injEq] at hx
    obtain ⟨y, hy, rfl, rfl⟩ := hx
    simp only [Ty.Variance.toVar4]
    rw [polarity_tuple, Var4.co_mul]
    exact Var4.le_foldr_add (List.mem_map.mpr ⟨y, hy, rfl⟩)
  | app n ts =>
    simp only [Ty.args, List.mem_map, Prod.mk.injEq] at hx
    obtain ⟨⟨y, k⟩, hy, rfl, rfl⟩ := hx
    rw [polarity_app]
    have hmem : (y.polarity .sub i, k) ∈ (ts.map fun t => t.polarity .sub i).zipIdx 0 := by
      rw [List.zipIdx_map]
      exact List.mem_map.mpr ⟨(y, k), hy, rfl⟩
    exact appPolarity_le (HeadReading.sub.app n) _ 0 k _ hmem
  | never | unit | nat | int | string | bool | handle _ | lit _ | var _ | unknown | null
    | undefined | number | bytes =>
    simp only [Ty.args, List.not_mem_nil] at hx

/-- An instance's arguments are the template's, instantiated, at the same variances. -/
theorem args_instantiate (σ : Ty.Subst) : ∀ t : Ty, (∀ i, t ≠ .var i) →
    (Ty.instantiate σ t).args = t.args.map fun p => (p.1, Ty.instantiate σ p.2)
  | .var i, h => absurd rfl (h i)
  | .record fs, _ => by
    rw [Ty.instantiate, Ty.instantiateFields_eq_map]
    simp only [Ty.args]
    rw [Ty.canon_map_payload, List.map_map, List.map_map]
    rfl
  | .tuple ts, _ => by
    rw [Ty.instantiate, Ty.instantiateItems_eq_map]
    simp only [Ty.args, List.map_map]
    rfl
  | .app n ts, _ => by
    rw [Ty.instantiate, Ty.instantiateItems_eq_map]
    simp only [Ty.args, List.zipIdx_map, List.map_map]
    rfl
  | .never, _ | .unit, _ | .nat, _ | .int, _ | .string, _ | .bool, _ | .handle _, _
  | .option _, _ | .list _, _ | .prod _ _, _ | .except _ _, _ | .exitOf _ _, _ | .causeOf _, _
  | .fiberOf _ _, _ | .union _ _, _ | .lit _, _ | .refOf _, _ | .deferredOf _ _, _
  | .unknown, _ | .map _ _, _ | .null, _ | .undefined, _ | .number, _ | .bytes, _ => rfl

/-- Two instances of one template that is no parameter and no union have one head. -/
theorem sameHead_instantiate (σ σ' : Ty.Subst) : ∀ t : Ty, (∀ i, t ≠ .var i) →
    (∀ a b, t ≠ .union a b) → Ty.sameHead (Ty.instantiate σ t) (Ty.instantiate σ' t) = true
  | .var i, h, _ => absurd rfl (h i)
  | .union a b, _, h => absurd rfl (h a b)
  | .record fs, _, _ => by
    rw [Ty.instantiate, Ty.instantiate, Ty.instantiateFields_eq_map, Ty.instantiateFields_eq_map]
    simp only [Ty.sameHead, Ty.canon_map_payload, List.map_map]
    exact decide_eq_true rfl
  | .tuple ts, _, _ => by
    rw [Ty.instantiate, Ty.instantiate, Ty.instantiateItems_eq_map, Ty.instantiateItems_eq_map]
    simp only [Ty.sameHead, List.length_map]
    rfl
  | .app n ts, _, _ => by
    rw [Ty.instantiate, Ty.instantiate, Ty.instantiateItems_eq_map, Ty.instantiateItems_eq_map]
    simp only [Ty.sameHead, List.length_map, decide_true, Bool.and_self]
  | .handle s, _, _ => by
    show Ty.sameHead (.handle s) (.handle s) = true
    simp only [Ty.sameHead, decide_true]
  | .lit s, _, _ => by
    show Ty.sameHead (.lit s) (.lit s) = true
    simp only [Ty.sameHead, decide_true]
  | .never, _, _ | .unit, _, _ | .nat, _, _ | .int, _, _ | .string, _, _ | .bool, _, _
  | .option _, _, _ | .list _, _, _ | .prod _ _, _, _ | .except _ _, _, _ | .exitOf _ _, _, _
  | .causeOf _, _, _ | .fiberOf _ _, _, _ | .refOf _, _, _ | .deferredOf _ _, _, _
  | .unknown, _, _ | .map _ _, _, _ | .null, _, _ | .undefined, _, _ | .number, _, _
  | .bytes, _, _ => rfl

/-- A list zipped with itself through two maps is the list read at both. -/
theorem all_zip_map {α β γ : Type} (L : List α) (f : α → β) (g : α → γ) (P : β × γ → Bool) :
    ((L.map f).zip (L.map g)).all P = L.all fun a => P (f a, g a) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.zip_cons_cons, List.all_cons, ih]

/-- Reading at `co` asks the forward direction. -/
theorem Var4.select_co (x y : Bool) : Var4.co.select x y = x := by
  cases x <;> cases y <;> rfl

/-- The case of a head with arguments: two instances of one head are related when each argument
is, at its variance; the premise passes to each argument by `polarity_args`, and an odd path
swaps the pair. `ih` is the statement at every smaller template. A step of
`sub_instantiate_polarity`. -/
theorem sub_instantiate_of_args (t : Ty) (σ σ' : Ty.Subst) (hv : ∀ i, t ≠ .var i)
    (hu : ∀ a b, t ≠ .union a b) (hm : ∀ s : Ty.Subst, Ty.isMember (Ty.instantiate s t) = true)
    (hl : Ty.leafRule (Ty.instantiate σ t) (Ty.instantiate σ' t) = false)
    (ht : Ty.topRule (Ty.instantiate σ t) (Ty.instantiate σ' t) = false)
    (h : PolarityRelated (fun i => t.polarity .sub i) σ σ')
    (ih : ∀ x : Ty, sizeOf x < sizeOf t → ∀ ρ ρ' : Ty.Subst,
      PolarityRelated (fun i => x.polarity .sub i) ρ ρ' →
        Ty.sub (Ty.instantiate ρ x) (Ty.instantiate ρ' x) = true) :
    Ty.sub (Ty.instantiate σ t) (Ty.instantiate σ' t) = true := by
  rw [Ty.sub_eq_args _ _ (hm σ) (hm σ') hl ht, sameHead_instantiate σ σ' t hv hu, Bool.true_and]
  unfold Ty.argsBelow
  rw [args_instantiate σ t hv, args_instantiate σ' t hv, all_zip_map]
  refine List.all_eq_true.mpr fun ⟨v, x⟩ hp => ?_
  have hsize := Ty.sizeOf_args hp
  show v.holds Ty.sub (Ty.instantiate σ x) (Ty.instantiate σ' x) = true
  rw [Ty.Variance.holds_eq_select, Ty.Variance.select_toVar4]
  apply Var4.select_of
  · intro hpos
    exact ih x hsize σ σ' (PolarityRelated.mono
      (fun i => Var4.le_trans (Var4.le_self_mul _ _ hpos) (polarity_args t hp i)) h)
  · intro hneg
    exact ih x hsize σ' σ (PolarityRelated.swap (PolarityRelated.mono
      (fun i => Var4.le_trans (Var4.le_contra_mul _ _ hneg) (polarity_args t hp i)) h))

/-- **Instantiation respects polarity** (claim `instantiate-respects-polarity`, slice VAR-2): if
every parameter's two bindings are related by `Ty.sub` at the parameter's polarity in `t` (a
bivariant parameter asks nothing, an invariant one both directions), the two instances are
related. It is the probe's `eval_respects` at the model of `Ty` (raw `Ty.sub`, each head read at
its variance, `HeadReading.sub`). Its consumers are `checker-monotone`'s share at a row (with
`Bounds.matchArgsB_monotone`, at an answer that reads its parameters at co or bi) and HO-4's
instantiated rows. It establishes no semantic variance and nothing of tsgo's inference. -/
@[semantics "subtyping-algebra" (requirement := R10)]
theorem Ty.sub_instantiate_polarity : ∀ (t : Ty) (σ σ' : Ty.Subst),
    (∀ i, (t.polarity .sub i).select (Ty.sub (σ.at i) (σ'.at i))
      (Ty.sub (σ'.at i) (σ.at i)) = true) →
    Ty.sub (Ty.instantiate σ t) (Ty.instantiate σ' t) = true
  | .var j, σ, σ', h => by
    have hpol : (Ty.var j).polarity .sub j = Var4.co := if_pos rfl
    have hj := h j
    rw [hpol, Var4.select_co] at hj
    exact hj
  | .union a b, σ, σ', h => by
    have ha := Ty.sub_instantiate_polarity a σ σ'
      (PolarityRelated.mono (fun i => Var4.le_add_left _ (b.polarity .sub i)) h)
    have hb := Ty.sub_instantiate_polarity b σ σ'
      (PolarityRelated.mono (fun i => Var4.le_add_right (a.polarity .sub i) _) h)
    show Ty.sub (.union (Ty.instantiate σ a) (Ty.instantiate σ b))
      (.union (Ty.instantiate σ' a) (Ty.instantiate σ' b)) = true
    apply (Ty.OrderProof.sub_iff_members Ty.sub_trans _ _).mpr
    intro x hx
    simp only [Ty.members, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · obtain ⟨y, hy, hxy⟩ := (Ty.OrderProof.sub_iff_members Ty.sub_trans _ _).mp ha x hx
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := (Ty.OrderProof.sub_iff_members Ty.sub_trans _ _).mp hb x hx
      exact ⟨y, Or.inr hy, hxy⟩
  | .never, _, _, _ => Ty.sub_refl _
  | .unknown, _, _, _ => Ty.sub_refl _
  | .unit, _, _, _ => Ty.sub_refl _
  | .nat, _, _, _ => Ty.sub_refl _
  | .int, _, _, _ => Ty.sub_refl _
  | .string, _, _, _ => Ty.sub_refl _
  | .bool, _, _, _ => Ty.sub_refl _
  | .handle _, _, _, _ => Ty.sub_refl _
  | .lit _, _, _, _ => Ty.sub_refl _
  | .null, _, _, _ => Ty.sub_refl _
  | .undefined, _, _, _ => Ty.sub_refl _
  | .number, _, _, _ => Ty.sub_refl _
  | .bytes, _, _, _ => Ty.sub_refl _
  | .option a, σ, σ', h =>
    sub_instantiate_of_args (.option a) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .list a, σ, σ', h =>
    sub_instantiate_of_args (.list a) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .prod a b, σ, σ', h =>
    sub_instantiate_of_args (.prod a b) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .except a b, σ, σ', h =>
    sub_instantiate_of_args (.except a b) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .exitOf a b, σ, σ', h =>
    sub_instantiate_of_args (.exitOf a b) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .causeOf a, σ, σ', h =>
    sub_instantiate_of_args (.causeOf a) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .fiberOf a b, σ, σ', h =>
    sub_instantiate_of_args (.fiberOf a b) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .refOf a, σ, σ', h =>
    sub_instantiate_of_args (.refOf a) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .deferredOf a b, σ, σ', h =>
    sub_instantiate_of_args (.deferredOf a b) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .record fs, σ, σ', h =>
    sub_instantiate_of_args (.record fs) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ =>
        have _ : sizeOf x < 1 + sizeOf fs := Ty.record.sizeOf_spec fs ▸ hx
        Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .map a b, σ, σ', h =>
    sub_instantiate_of_args (.map a b) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ => Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .tuple ts, σ, σ', h =>
    sub_instantiate_of_args (.tuple ts) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ =>
        have _ : sizeOf x < 1 + sizeOf ts := Ty.tuple.sizeOf_spec ts ▸ hx
        Ty.sub_instantiate_polarity x ρ ρ' hρ)
  | .app n ts, σ, σ', h =>
    sub_instantiate_of_args (.app n ts) σ σ' (fun _ hi => by cases hi)
      (fun _ _ hab => by cases hab) (fun _ => rfl) rfl rfl h
      (fun x hx ρ ρ' hρ =>
        have _ : sizeOf x < 1 + sizeOf n + sizeOf ts := Ty.app.sizeOf_spec n ts ▸ hx
        Ty.sub_instantiate_polarity x ρ ρ' hρ)
termination_by t => sizeOf t

end Effect4.Program

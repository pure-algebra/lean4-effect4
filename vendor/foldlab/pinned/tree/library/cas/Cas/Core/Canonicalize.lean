import Cas.Core.Canonical

/-!
# Canonicalization methods — normalizers as first-class data

A canonicalization method is an idempotent normalizer: a function that
maps every presentation of a value onto one representative spelling.
`Canonical` (the sibling class) is the codomain discipline — one byte
representation per value; this module is the morphism discipline — how
raw presentations REACH canonical representatives, and what a method
must satisfy before its representatives may carry identity.

Methods are structure values, not a class: one carrier admits many
methods (trivia erasure, key sorting, name resolution, positional
renaming), and the ladder of methods — composition, refinement — is
itself data to reason about.

The laws, once for every method:

- a method induces an equivalence (same representative), decidable
  whenever the carrier's equality is — the metaprogrammatic payoff;
- a method that PRESERVES an observation never merges two values the
  observation distinguishes (`eq_obs_of_equiv`) — admissibility, with
  the observation instantiated by the canonical bytes today and by the
  run-word observation at the semantic plane;
- `Complete` states the converse bound — the quotient coinciding with
  the observation's. Instances are admitted only against decidable
  syntactic observations, and only by proof; for semantic observations
  the bound stays permanently open — identity hashes presentations,
  never denotations.
- composition of methods is lawful exactly under the ladder-coherence
  premise: the later method preserves the earlier method's normal
  forms;
- the FORM ADDRESS of a value under a method is the address of its
  representative; it is well-defined on the method's quotient at
  lattice Level 0, and reflects the quotient at Level 1 under the
  named injectivity premise — the hash-hypothesis lattice, inherited,
  never assumed.

Direction-law position: a canonicalization method is normalize-side
machinery (acquire → ingest → NORMALIZE → gate → admit). It is never
applied on the load path — renormalize-on-read stays a named defect —
and applying a method never mints identity by itself: the address
comes from the canonical encoding of the representative, as always.
-/

namespace Cas

/-- A canonicalization method: an idempotent normalizer. Idempotence is
the whole admission bar at this altitude — everything else (what the
method erases, what it preserves) is stated per method against named
observations. -/
structure Canonicalizer (α : Type u) where
  canon : α → α
  canon_idem : ∀ a, canon (canon a) = canon a

namespace Canonicalizer

variable {α : Type u} {ω : Type v}

/-- A value in canonical form: a fixed point of the method. -/
def IsCanon (c : Canonicalizer α) (a : α) : Prop := c.canon a = a

theorem isCanon_canon (c : Canonicalizer α) (a : α) :
    c.IsCanon (c.canon a) :=
  c.canon_idem a

/-- Canonical forms are exactly the method's image. -/
theorem isCanon_iff_exists (c : Canonicalizer α) {a : α} :
    c.IsCanon a ↔ ∃ b, c.canon b = a := by
  constructor
  · exact fun h => ⟨a, h⟩
  · rintro ⟨b, rfl⟩
    exact c.canon_idem b

instance (c : Canonicalizer α) [DecidableEq α] (a : α) :
    Decidable (c.IsCanon a) := by
  unfold IsCanon; infer_instance

/-- The induced equivalence: same canonical representative. -/
def Equiv (c : Canonicalizer α) (a b : α) : Prop := c.canon a = c.canon b

theorem equiv_refl (c : Canonicalizer α) (a : α) : c.Equiv a a := rfl

theorem equiv_symm (c : Canonicalizer α) {a b : α}
    (h : c.Equiv a b) : c.Equiv b a := h.symm

theorem equiv_trans (c : Canonicalizer α) {a b d : α}
    (h₁ : c.Equiv a b) (h₂ : c.Equiv b d) : c.Equiv a d := h₁.trans h₂

/-- Every value is equivalent to its representative. -/
theorem equiv_canon (c : Canonicalizer α) (a : α) :
    c.Equiv a (c.canon a) :=
  (c.canon_idem a).symm

/-- The quotient is decidable whenever the carrier's equality is — the
metaprogrammatic payoff: form-equality questions close by computation. -/
instance (c : Canonicalizer α) [DecidableEq α] (a b : α) :
    Decidable (c.Equiv a b) := by
  unfold Equiv; infer_instance

/-- The induced setoid; `Quotient (c.toSetoid)` is the method's form
space. -/
def toSetoid (c : Canonicalizer α) : Setoid α :=
  ⟨c.Equiv, fun a => equiv_refl c a, equiv_symm c, equiv_trans c⟩

/-! ## Observations — admissibility and its deliberate upper bound -/

/-- The method preserves an observation: normalizing never changes what
the observation sees. -/
def Preserves (c : Canonicalizer α) (obs : α → ω) : Prop :=
  ∀ a, obs (c.canon a) = obs a

/-- Admissibility: a preservation-lawful method never merges two values
the observation distinguishes. -/
theorem eq_obs_of_equiv (c : Canonicalizer α) {obs : α → ω}
    (hp : c.Preserves obs) {a b : α} (h : c.Equiv a b) :
    obs a = obs b := by
  rw [← hp a, ← hp b]
  exact congrArg obs h

/-- The upper bound: the method's quotient coincides with the
observation's. Instantiated only against decidable syntactic
observations, and only by proof; for semantic observations the bound
stays permanently open — identity hashes presentations, never
denotations. -/
def Complete (c : Canonicalizer α) (obs : α → ω) : Prop :=
  ∀ a b, obs a = obs b → c.Equiv a b

/-! ## The ladder — refinement and coherent composition -/

/-- `c₁.RefinedBy c₂`: the second method is coarser-or-equal — it
merges everything the first merges. -/
def RefinedBy (c₁ c₂ : Canonicalizer α) : Prop :=
  ∀ a b, c₁.Equiv a b → c₂.Equiv a b

theorem refinedBy_refl (c : Canonicalizer α) : c.RefinedBy c :=
  fun _ _ h => h

theorem refinedBy_trans {c₁ c₂ c₃ : Canonicalizer α}
    (h₁ : c₁.RefinedBy c₂) (h₂ : c₂.RefinedBy c₃) : c₁.RefinedBy c₃ :=
  fun a b h => h₂ a b (h₁ a b h)

/-- The identity method — byte identity, the ladder's floor. -/
protected def id : Canonicalizer α := ⟨fun a => a, fun _ => rfl⟩

/-- The floor refines every method. -/
theorem id_refinedBy (c : Canonicalizer α) :
    (Canonicalizer.id).RefinedBy c :=
  fun _ _ h => congrArg c.canon h

/-- Ladder coherence: the later method maps the earlier method's normal
forms to normal forms. This premise is exactly what makes a two-rung
ladder a method again. -/
def Coherent (c₂ c₁ : Canonicalizer α) : Prop :=
  ∀ a, c₁.canon (c₂.canon (c₁.canon a)) = c₂.canon (c₁.canon a)

/-- Composition of a coherent ladder: normalize by the first method,
then the second. Idempotence is inherited, not re-proved per ladder. -/
def comp (c₂ c₁ : Canonicalizer α) (hco : Coherent c₂ c₁) :
    Canonicalizer α where
  canon a := c₂.canon (c₁.canon a)
  canon_idem a := by
    show c₂.canon (c₁.canon (c₂.canon (c₁.canon a))) = _
    rw [hco a, c₂.canon_idem]

@[simp] theorem comp_canon (c₂ c₁ : Canonicalizer α) (hco : Coherent c₂ c₁)
    (a : α) : (comp c₂ c₁ hco).canon a = c₂.canon (c₁.canon a) := rfl

/-- A coherent ladder preserves every observation both rungs preserve. -/
theorem comp_preserves {obs : α → ω} (c₂ c₁ : Canonicalizer α)
    (hco : Coherent c₂ c₁) (h₂ : c₂.Preserves obs) (h₁ : c₁.Preserves obs) :
    (comp c₂ c₁ hco).Preserves obs := by
  intro a
  show obs (c₂.canon (c₁.canon a)) = obs a
  rw [h₂, h₁]

/-- A rung refines the ladder it opens: composing a further method only
merges more. -/
theorem refinedBy_comp (c₂ c₁ : Canonicalizer α) (hco : Coherent c₂ c₁) :
    c₁.RefinedBy (comp c₂ c₁ hco) := by
  intro a b h
  show c₂.canon (c₁.canon a) = c₂.canon (c₁.canon b)
  exact congrArg c₂.canon h

/-! ## Form addresses — the quotient meets the address lattice -/

section FormAddress

variable [Canonical α] {Addr : Type w}

/-- The form address of a value under a method: the address of its
canonical representative. This is the observed-form hash of the
construct-ledger lane, as a definition rather than a convention. -/
def formAddress (c : Canonicalizer α) (H : Bytes → Addr) (a : α) : Addr :=
  Canonical.address H (c.canon a)

/-- Level 0: form addresses are well-defined on the method's quotient —
no premise on `H`. -/
theorem formAddress_congr (c : Canonicalizer α) (H : Bytes → Addr)
    {a b : α} (h : c.Equiv a b) :
    c.formAddress H a = c.formAddress H b :=
  congrArg (Canonical.address H) h

/-- Level 0: equal form addresses mean equivalent values or an explicit
collision witness on the representatives — the ideal-or-collision
disjunct, lifted to the quotient. -/
theorem formAddress_eq_or_collision (c : Canonicalizer α) (H : Bytes → Addr)
    {a b : α} (h : c.formAddress H a = c.formAddress H b) :
    c.Equiv a b ∨
      (Canonical.encode (c.canon a) ≠ Canonical.encode (c.canon b) ∧
        H (Canonical.encode (c.canon a)) = H (Canonical.encode (c.canon b))) :=
  match Canonical.address_eq_or_collision H h with
  | Or.inl he => Or.inl he
  | Or.inr w => Or.inr w

/-- Level 1: under the named injectivity premise, form addresses reflect
the quotient. -/
theorem formAddress_inj (c : Canonicalizer α) (H : Bytes → Addr)
    (hInj : Function.Injective H) {a b : α}
    (h : c.formAddress H a = c.formAddress H b) : c.Equiv a b :=
  Canonical.address_inj H hInj h

end FormAddress

end Canonicalizer

end Cas

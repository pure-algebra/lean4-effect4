import Cas.IR.Word
import Cas.Core.Admission
import Cas.Grammar.Tree

/-!
# The join algebra of the store

The word face of state-based merge. A store word is an admission
history; two histories JOIN by concatenation, and this module is what
makes that a join rather than a coincidence of list append:
`Store.Compatible` (the agreement condition — no address bound to two
different nodes across the pair), `Store.Sub` (store inclusion, the
order the join is taken in), and `Word.toStore_append`, the
left-biased characterization every proof below reasons through.

Under compatibility the bias is invisible: both operands embed
(`Word.toStore_sub_append_left`, `Word.toStore_sub_append_right`),
operand order does not matter (`Word.toStore_append_comm`), joining a
word with itself changes nothing (`Word.toStore_append_self`), and
admission survives the merge (`Word.wf_append`). Associativity is the
underlying `List.append`'s and needs no theorem of its own. That is
the state-based CRDT shape stated over the store word rather than
assumed of it — and stated over the WORD, so a merge is
byte-decidable, not merely semantic.

Compatibility is a premise, never a gift. `Word.Honest.compatible` is
where it is earned, and it is earned at Level 1 of the
hash-hypothesis lattice (CAS-003) — `Function.Injective H` named, the
same premise `Grammar.Honest.no_alias` carries, one word wider. The
algebra itself is Level 0 throughout; only the honesty bridge climbs.

`RefsOk_mono` and `put_duplicate_iff` close the loop back onto the
admission transition: references that check keep checking as the
store grows, and `put`'s duplicate arm is exactly the singleton
already below the store — which is why re-admitting a node the merge
already carries is a no-op rather than a conflict.
-/

namespace Cas

/-- Two stores agree wherever both are defined. This is the merge
condition: nothing else about the pair is needed to join them, and
without it a join would have to choose, which the store may not do. -/
def Store.Compatible (σ₁ σ₂ : Store) : Prop :=
  ∀ a n₁ n₂, σ₁ a = some n₁ → σ₂ a = some n₂ → n₁ = n₂

/-- Store inclusion: every binding of `σ₁` is a binding of `σ₂` — the
order the join is a least upper bound in. -/
def Store.Sub (σ₁ σ₂ : Store) : Prop :=
  ∀ a n, σ₁ a = some n → σ₂ a = some n

theorem Store.Compatible.symm {σ₁ σ₂ : Store} (h : Compatible σ₁ σ₂) :
    Compatible σ₂ σ₁ :=
  fun a n₁ n₂ h₁ h₂ => (h a n₂ n₁ h₂ h₁).symm

namespace Word

/-- The bridge over a concatenation is the LEFT-BIASED union: the
first word answers wherever it can, the second only where the first is
silent. Order is semantics, so the bias is stated, not smoothed away —
every symmetry below is a theorem paid for by `Store.Compatible`. -/
theorem toStore_append (w₁ w₂ : Word) (a : Addr32) :
    toStore (w₁ ++ w₂) a = (toStore w₁ a).elim (toStore w₂ a) some := by
  show find (w₁ ++ w₂) a = (find w₁ a).elim (find w₂ a) some
  cases hf : find w₁ a with
  | none => rw [find_append_of_none w₂ hf]; rfl
  | some n => rw [find_append_of_some w₂ hf]; rfl

/-- The left operand embeds unconditionally — first-binding
resolution answers it whatever stands behind. -/
theorem toStore_sub_append_left (w₁ w₂ : Word) :
    Store.Sub (toStore w₁) (toStore (w₁ ++ w₂)) := by
  intro a n h
  show find (w₁ ++ w₂) a = some n
  exact find_append_of_some w₂ h

/-- The right operand embeds too, but only up to agreement: a `w₂`
binding may be shadowed by `w₁` exactly when the shadow carries the
same node. That is the whole content of `Store.Compatible`. -/
theorem toStore_sub_append_right {w₁ w₂ : Word}
    (h : Store.Compatible (toStore w₁) (toStore w₂)) :
    Store.Sub (toStore w₂) (toStore (w₁ ++ w₂)) := by
  intro a n hf
  show find (w₁ ++ w₂) a = some n
  cases hw : find w₁ a with
  | none =>
    rw [find_append_of_none w₂ hw]
    exact hf
  | some m =>
    rw [find_append_of_some w₂ hw]
    exact congrArg some (h a m n hw hf)

/-- The join is symmetric where it is defined: compatible words
concatenate to one store in either order. The words themselves differ
as lists — it is the bridge that forgets the order, and only under
agreement. -/
theorem toStore_append_comm {w₁ w₂ : Word}
    (h : Store.Compatible (toStore w₁) (toStore w₂)) :
    toStore (w₁ ++ w₂) = toStore (w₂ ++ w₁) := by
  funext a
  rw [toStore_append, toStore_append]
  cases h₁ : toStore w₁ a with
  | none => cases h₂ : toStore w₂ a <;> rfl
  | some n₁ =>
    cases h₂ : toStore w₂ a with
    | none => rfl
    | some n₂ => exact congrArg some (h a n₁ n₂ h₁ h₂)

/-- Idempotence, and it costs nothing: the left bias makes the second
copy inert without any premise on the word. -/
theorem toStore_append_self (w : Word) : toStore (w ++ w) = toStore w := by
  funext a
  rw [toStore_append]
  cases h : toStore w a <;> rfl

-- byte-scoped injectivity refinement owed (AG-3)
/-- Honest words are pairwise compatible: equal addresses force equal
canonical bytes under `hInj`, and the codec's non-malleability forces
equal nodes. Level 1 of the hash-hypothesis lattice — the premise is
the one `Grammar.Honest.no_alias` already carries, taken across two
words instead of within one. This is what supplies the merge condition
for words the grammar emitted, so the join algebra above never has to
assume it. -/
theorem Honest.compatible (H : Bytes → Addr32) {w₁ w₂ : Word}
    (h₁ : Grammar.Honest H w₁) (h₂ : Grammar.Honest H w₂)
    (hInj : Function.Injective H) :
    Store.Compatible (toStore w₁) (toStore w₂) := by
  intro a n₁ n₂ hf₁ hf₂
  have hm₁ : Binding.mk a n₁ ∈ w₁ := find_mem hf₁
  have hm₂ : Binding.mk a n₂ ∈ w₂ := find_mem hf₂
  obtain ⟨hk₁, hwf₁⟩ := h₁ _ hm₁
  obtain ⟨hk₂, hwf₂⟩ := h₂ _ hm₂
  have hk₁' : a = H (encodeNode n₁) := hk₁
  have hk₂' : a = H (encodeNode n₂) := hk₂
  exact encodeNode_injOn hwf₁ hwf₂ (hInj (hk₁'.symm.trans hk₂'))

/-- Lifting one resolution across a compatible left extension. The
suffix `v` is what makes the premise usable: `p` is a PREFIX of the
right word, so a resolution in `p` is a resolution in the whole right
word, and compatibility can then rule on whatever `w₁` shadows it
with. -/
theorem resolvesIn_prefix_lift {w₁ p v : Word} {r : Ref}
    (hc : Store.Compatible (toStore w₁) (toStore (p ++ v)))
    (h : resolvesIn p r = true) : resolvesIn (w₁ ++ p) r = true := by
  obtain ⟨m, hm, ht⟩ := resolvesIn_iff.mp h
  cases hw : find w₁ r.addr with
  | none =>
    refine resolvesIn_iff.mpr ⟨m, ?_, ht⟩
    rw [find_append_of_none p hw]
    exact hm
  | some m' =>
    have heq : m' = m := hc r.addr m' m hw (find_append_of_some v hm)
    refine resolvesIn_iff.mpr ⟨m', find_append_of_some p hw, ?_⟩
    rw [heq]
    exact ht

/-- The admission scan survives a compatible left extension. The
already-admitted prefix `p` of the right word is generalized — that is
what makes the induction go through, because the compatibility premise
must stay against `p ++ rest`, the whole right word, at every step. -/
theorem wfFrom_left_extend {w₁ : Word} : ∀ rest p : Word,
    Store.Compatible (toStore w₁) (toStore (p ++ rest)) →
    wfFrom p rest = true → wfFrom (w₁ ++ p) rest = true := by
  intro rest
  induction rest with
  | nil => intro p _ _; simp [wfFrom]
  | cons e rest ih =>
    obtain ⟨a, n⟩ := e
    intro p hc h
    simp only [wfFrom, Bool.and_eq_true, List.all_eq_true] at h ⊢
    obtain ⟨hrefs, hrest⟩ := h
    refine ⟨fun r hr => resolvesIn_prefix_lift hc (hrefs r hr), ?_⟩
    have hassoc : (p ++ [Binding.mk a n]) ++ rest
        = p ++ Binding.mk a n :: rest := by simp
    have hc' : Store.Compatible (toStore w₁)
        (toStore ((p ++ [Binding.mk a n]) ++ rest)) := by
      rw [hassoc]; exact hc
    have hlift := ih (p ++ [Binding.mk a n]) hc' hrest
    rw [← List.append_assoc] at hlift
    exact hlift

/-- Closure survives the join: concatenating two admitted words that
agree is admitted. Nothing in the left word can dangle a reference of
the right one — the right word's own resolution stands, and where the
left word shadows it, agreement says it shadows with the same node, so
the kind tag carries. -/
theorem wf_append {w₁ w₂ : Word} (h₁ : wf w₁ = true) (h₂ : wf w₂ = true)
    (hc : Store.Compatible (toStore w₁) (toStore w₂)) :
    wf (w₁ ++ w₂) = true := by
  unfold wf at h₁ h₂ ⊢
  rw [wfFrom_append, List.nil_append]
  simp only [Bool.and_eq_true]
  refine ⟨h₁, ?_⟩
  have hlift := wfFrom_left_extend w₂ [] hc h₂
  simpa using hlift

end Word

/-- Admission is monotone in the store: a reference list that checks
keeps checking as the store grows. With `Word.toStore_sub_append_left`
this is what makes a merge safe for everything already admitted. -/
theorem RefsOk_mono {σ₁ σ₂ : Store} (h : Store.Sub σ₁ σ₂) {rs : List Ref} :
    RefsOk σ₁ rs → RefsOk σ₂ rs := by
  intro hok r hr
  obtain ⟨m, hm, ht⟩ := hok r hr
  exact ⟨m, h r.addr m hm, ht⟩

/-- The duplicate arm is exactly singleton-below: once the references
check, `put` reports `duplicate` precisely when the incoming node is
already resident at its own address. Re-admitting what the store
already carries is a no-op by characterization, not by convention —
the fixed point a join is allowed to reach. -/
theorem put_duplicate_iff {H : Bytes → Addr32} {σ : Store}
    {n : AdmittedNode} (hrefs : RefsOk σ n.val.refs) :
    put H σ n = .ok (.duplicate (addr H n)) ↔ σ (addr H n) = some n.val := by
  constructor
  · intro h
    exact (put_duplicate_spec h).2.2
  · intro h
    have hc : checkRefs σ n.val.refs = .ok () := checkRefs_ok_iff.mpr hrefs
    simp [put, hc, h]

end Cas

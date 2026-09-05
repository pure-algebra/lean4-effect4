import Effect4.Store.Canonical

/-!
# Conformance.GSet: the grow-only set

Owner: the one set type every conformance artifact is stored in. A `GSet α` is
a grow-only set, the simplest state-based CRDT: a list in insertion order whose
only observable is membership, whose `join` is union, and which never shrinks.

Where it sits in the semantic compiler: it is the **merge** of the intermediate
representation. Many front ends (LLM sessions, generators, replay drivers) each
produce a `GSet`, and the result is their join, which is the same whatever the
order or the repetition (`join_comm`, `join_assoc`, `join_idem`). What it makes
mechanical: the question "did this extension invalidate anything" has the answer
`sub_join_left`, a theorem, so no reviewer asks it.

## The algebra

| | |
| --- | --- |
| Carrier | `GSet α`, a `List α` with `DecidableEq α`, `deriving DecidableEq, Repr`; `Canonical` and `Content` when `α` is canonical (`Evidence/Char/Canonical.lean`) |
| Operations | `empty`, `insert`, `join`, `ofList`, `has`, `size` |
| Laws | `has_join`; `join_comm`, `join_assoc`, `join_idem`, `join_empty_left`, `join_empty_right`; `sub_join_left`, `sub_join_right`, `join_mono`, `join_sub`, `join_of_sub`; `ofList_mono`; `nodup_join` |
| Structure | the free join-semilattice on `α` (finite subsets under union): a commutative idempotent monoid with unit `empty`, ordered by `Sub`; a G-Set CRDT |
| Payoff | deletes every "invalidate and regenerate" step and the "is this fixture stale" review question; a re-run is a no-op by `join_idem` |
| Anti-vacuity | `GSet.nodup_ofList` says the set really is keyed (every element once); the worked instance in `Conformance/Cell.lean` shows a join that adds and a join that is a no-op |
| Generation | hand-authored substrate; nothing component-specific here |

The laws are stated up to `Equiv` (same members), because insertion order is
state, not meaning; the address of a set is the address of its list state, a
limit recorded in `workshop/Char/10-conformance/08-open-questions.md`. Nothing
here hashes: sets are keyed by the value, so the kernel decides membership.

The canonical instance is not here. `GSet α` is a generic carrier, and
`Effect4Gen` does not yet take a bare parameter, so its instance is hand-written
with the other generic ones in `Effect4/Evidence/Char/Canonical.lean`, on the
`Prod`/`List` templates of `Effect4/Store/Canonical.lean:486-601`.
-/

set_option autoImplicit false

namespace Effect4.Char

open Effect4.Store

/-- A grow-only set: a list in insertion order with membership as the only
observable. Never shrinks. -/
structure GSet (α : Type) where
  elems : List α
deriving DecidableEq, Repr

namespace GSet

variable {α : Type} [DecidableEq α]

/-- Membership in a list, structurally recursive so the kernel reduces it. -/
def hasL : List α → α → Bool
  | [], _ => false
  | x :: xs, a => decide (x = a) || hasL xs a

theorem hasL_append (xs ys : List α) (a : α) :
    hasL (xs ++ ys) a = (hasL xs a || hasL ys a) := by
  induction xs with
  | nil => simp [hasL]
  | cons x xs ih => simp [hasL, ih, Bool.or_assoc]

theorem hasL_iff_mem (xs : List α) (a : α) : hasL xs a = true ↔ a ∈ xs := by
  induction xs with
  | nil => simp [hasL]
  | cons x xs ih =>
    simp only [hasL, Bool.or_eq_true, decide_eq_true_iff, ih, List.mem_cons]
    exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr,
           fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩

/-- The unit. -/
def empty : GSet α := ⟨[]⟩

/-- The one observable. -/
def has (s : GSet α) (a : α) : Bool := hasL s.elems a

/-- Add one element; a no-op when it is already held. `Store.put`'s shape, keyed
by the value rather than by its digest, so the kernel never hashes. -/
def insert (s : GSet α) (a : α) : GSet α :=
  if s.has a then s else ⟨s.elems ++ [a]⟩

/-- The join: union by membership. -/
def join (s t : GSet α) : GSet α := t.elems.foldl insert s

/-- A set from a list, deduplicated. -/
def ofList (xs : List α) : GSet α := join empty ⟨xs⟩

/-- The number of elements held. -/
def size (s : GSet α) : Nat := s.elems.length

theorem has_empty (a : α) : (empty : GSet α).has a = false := rfl

theorem has_insert (s : GSet α) (a b : α) :
    (s.insert a).has b = (s.has b || decide (a = b)) := by
  unfold insert
  by_cases h : s.has a = true
  · rw [if_pos h]
    by_cases hab : a = b
    · subst hab; simp [h]
    · simp [hab]
  · rw [if_neg h]
    simp [has, hasL_append, hasL]

theorem has_foldl (s : GSet α) (xs : List α) (a : α) :
    (xs.foldl insert s).has a = (s.has a || hasL xs a) := by
  induction xs generalizing s with
  | nil => simp [hasL]
  | cons x xs ih => simp [List.foldl, ih, has_insert, hasL, Bool.or_assoc]

/-- **The join law.** Membership in a join is membership in either side. Every
CRDT law below is a corollary of this one equation and the algebra of `||`. -/
theorem has_join (s t : GSet α) (a : α) : (s.join t).has a = (s.has a || t.has a) :=
  has_foldl s t.elems a

theorem has_ofList (xs : List α) (a : α) : (ofList xs).has a = hasL xs a := by
  show (empty.join ⟨xs⟩).has a = hasL xs a
  rw [has_join, has_empty, Bool.false_or]; rfl

theorem has_of_mem {s : GSet α} {a : α} (h : a ∈ s.elems) : s.has a = true :=
  (hasL_iff_mem _ _).2 h

theorem mem_of_has {s : GSet α} {a : α} (h : s.has a = true) : a ∈ s.elems :=
  (hasL_iff_mem _ _).1 h

theorem mem_ofList {xs : List α} {a : α} : (ofList xs).has a = true ↔ a ∈ xs := by
  rw [has_ofList]; exact hasL_iff_mem xs a

/-- Extensional equality: the same members. -/
def Equiv (s t : GSet α) : Prop := ∀ a, s.has a = t.has a

/-- Inclusion, as the `Prop` theorems take it. -/
def Sub (s t : GSet α) : Prop := ∀ a, s.has a = true → t.has a = true

/-- Inclusion, as a receipt decides it. -/
def subB (s t : GSet α) : Bool := s.elems.all t.has

theorem sub_of_subB {s t : GSet α} (h : subB s t = true) : Sub s t :=
  fun a ha => (List.all_eq_true.1 h) a (mem_of_has ha)

theorem subB_of_sub {s t : GSet α} (h : Sub s t) : subB s t = true :=
  List.all_eq_true.2 fun a ha => h a (has_of_mem ha)

theorem equiv_refl (s : GSet α) : Equiv s s := fun _ => rfl
theorem equiv_symm {s t : GSet α} (h : Equiv s t) : Equiv t s := fun a => (h a).symm
theorem equiv_trans {s t u : GSet α} (h₁ : Equiv s t) (h₂ : Equiv t u) : Equiv s u :=
  fun a => (h₁ a).trans (h₂ a)
theorem sub_refl (s : GSet α) : Sub s s := fun _ h => h
theorem sub_trans {s t u : GSet α} (h₁ : Sub s t) (h₂ : Sub t u) : Sub s u :=
  fun a h => h₂ a (h₁ a h)
theorem sub_of_equiv {s t : GSet α} (h : Equiv s t) : Sub s t := fun a ha => (h a) ▸ ha

/-! ### The G-Set laws: `join` is a commutative idempotent monoid with unit `empty` -/

theorem join_comm (s t : GSet α) : Equiv (s.join t) (t.join s) := fun a => by
  simp [has_join, Bool.or_comm]

theorem join_assoc (s t u : GSet α) : Equiv ((s.join t).join u) (s.join (t.join u)) :=
  fun a => by simp [has_join, Bool.or_assoc]

theorem join_idem (s : GSet α) : Equiv (s.join s) s := fun a => by simp [has_join]

theorem join_empty_left (s : GSet α) : Equiv (empty.join s) s := fun a => by
  simp [has_join, has_empty]

theorem join_empty_right (s : GSet α) : s.join empty = s := rfl

/-- **Join never removes.** Whatever was held before an extension is held after it. -/
theorem sub_join_left (s t : GSet α) : Sub s (s.join t) := fun a h => by
  simp [has_join, h]

theorem sub_join_right (s t : GSet α) : Sub t (s.join t) := fun a h => by
  simp [has_join, h]

theorem join_mono {s s' t t' : GSet α} (hs : Sub s s') (ht : Sub t t') :
    Sub (s.join t) (s'.join t') := fun a h => by
  rw [has_join, Bool.or_eq_true] at h
  rw [has_join, Bool.or_eq_true]
  exact h.elim (fun h => Or.inl (hs a h)) (fun h => Or.inr (ht a h))

theorem join_equiv {s s' t t' : GSet α} (hs : Equiv s s') (ht : Equiv t t') :
    Equiv (s.join t) (s'.join t') := fun a => by
  rw [has_join, has_join, hs a, ht a]

/-- The join is the least upper bound. -/
theorem join_sub {s t u : GSet α} (hs : Sub s u) (ht : Sub t u) : Sub (s.join t) u :=
  fun a h => by
    rw [has_join, Bool.or_eq_true] at h
    exact h.elim (hs a) (ht a)

/-- Absorption: joining a subset changes nothing. -/
theorem join_of_sub {s t : GSet α} (h : Sub t s) : Equiv (s.join t) s := fun a => by
  rw [has_join]
  cases hs : s.has a with
  | true => rfl
  | false =>
    cases ht : t.has a with
    | true => rw [h a ht] at hs; exact absurd hs (by decide)
    | false => rfl

/-- `ofList` is monotone in list membership. Every generator is `ofList` of a
list that only grows with its inputs, so this is the one monotonicity proof. -/
theorem ofList_mono {xs ys : List α} (h : ∀ a ∈ xs, a ∈ ys) : Sub (ofList xs) (ofList ys) :=
  fun a ha => by
    rw [has_ofList] at ha ⊢
    exact (hasL_iff_mem _ _).2 (h a ((hasL_iff_mem _ _).1 ha))

theorem ofList_append (xs ys : List α) :
    Equiv (ofList (xs ++ ys)) ((ofList xs).join (ofList ys)) :=
  fun a => by simp [has_join, has_ofList, hasL_append]

/-! ### Keyed: every element is held once -/

/-- Duplicate-freedom, as a `Bool`. -/
def nodupL : List α → Bool
  | [] => true
  | x :: xs => !(hasL xs x) && nodupL xs

theorem nodupL_append_single {xs : List α} {a : α}
    (h : nodupL xs = true) (ha : hasL xs a = false) : nodupL (xs ++ [a]) = true := by
  induction xs with
  | nil => simp [nodupL, hasL]
  | cons x xs ih =>
    simp only [nodupL, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [hasL, Bool.or_eq_false_iff, decide_eq_false_iff_not] at ha
    simp only [List.cons_append, nodupL, hasL_append, hasL, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.or_false]
    exact ⟨⟨h.1, fun e => ha.1 e.symm⟩, ih h.2 ha.2⟩

theorem nodup_insert {s : GSet α} (h : nodupL s.elems = true) (a : α) :
    nodupL (s.insert a).elems = true := by
  unfold insert
  by_cases hs : s.has a = true
  · rw [if_pos hs]; exact h
  · rw [if_neg hs]
    exact nodupL_append_single h (by simpa [has] using hs)

theorem nodup_foldl {s : GSet α} (h : nodupL s.elems = true) (xs : List α) :
    nodupL (xs.foldl insert s).elems = true := by
  induction xs generalizing s with
  | nil => exact h
  | cons x xs ih => exact ih (nodup_insert h x)

theorem nodup_join {s : GSet α} (h : nodupL s.elems = true) (t : GSet α) :
    nodupL (s.join t).elems = true := nodup_foldl h t.elems

theorem nodup_ofList (xs : List α) : nodupL (ofList xs).elems = true :=
  nodup_join rfl ⟨xs⟩

end GSet

/-! ## Receipts -/

#print axioms GSet.hasL
#print axioms GSet.hasL_append
#print axioms GSet.hasL_iff_mem
#print axioms GSet.empty
#print axioms GSet.has
#print axioms GSet.insert
#print axioms GSet.join
#print axioms GSet.ofList
#print axioms GSet.size
#print axioms GSet.has_empty
#print axioms GSet.has_insert
#print axioms GSet.has_foldl
#print axioms GSet.has_join
#print axioms GSet.has_ofList
#print axioms GSet.has_of_mem
#print axioms GSet.mem_of_has
#print axioms GSet.mem_ofList
#print axioms GSet.subB
#print axioms GSet.sub_of_subB
#print axioms GSet.subB_of_sub
#print axioms GSet.equiv_trans
#print axioms GSet.sub_trans
#print axioms GSet.sub_of_equiv
#print axioms GSet.join_comm
#print axioms GSet.join_assoc
#print axioms GSet.join_idem
#print axioms GSet.join_empty_left
#print axioms GSet.join_empty_right
#print axioms GSet.sub_join_left
#print axioms GSet.sub_join_right
#print axioms GSet.join_mono
#print axioms GSet.join_equiv
#print axioms GSet.join_sub
#print axioms GSet.join_of_sub
#print axioms GSet.ofList_mono
#print axioms GSet.ofList_append
#print axioms GSet.nodupL
#print axioms GSet.nodupL_append_single
#print axioms GSet.nodup_insert
#print axioms GSet.nodup_foldl
#print axioms GSet.nodup_join
#print axioms GSet.nodup_ofList

end Effect4.Char

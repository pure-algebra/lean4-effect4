import Cas.Core.Node

/-!
# The store carrier

The Plebeia-shaped store: a partial map from full-width addresses to nodes,
transition-indexed — the store value IS the state, and every operation is a
function from store to store. `set` is the raw update primitive; the
admission-checked transition lives in `Admission.lean`.

`Store.Closed` is store-level well-formedness: every reference of every
stored node resolves in the store, at the kind the reference declares. A
closed store can dangle nothing and mis-kind nothing — the two admission
clauses are impossible states of the resident graph, not merely rejected
inputs.
-/

namespace Cas

/-- The store: a partial map from addresses to nodes. -/
abbrev Store := Addr32 → Option Node

namespace Store

/-- The empty store. -/
def empty : Store := fun _ => none

/-- Raw update: bind `a` to `n`. Admission does not live here. -/
def set (σ : Store) (a : Addr32) (n : Node) : Store :=
  fun b => if b = a then some n else σ b

@[simp] theorem set_same (σ : Store) (a : Addr32) (n : Node) :
    σ.set a n a = some n := by
  simp [set]

theorem set_other (σ : Store) {a b : Addr32} (n : Node) (h : b ≠ a) :
    σ.set a n b = σ b := by
  simp [set, h]

/-- Store well-formedness: every stored node's references resolve, at their
declared kinds. -/
def Closed (σ : Store) : Prop :=
  ∀ a n, σ a = some n →
    ∀ r ∈ n.refs, ∃ m, σ r.addr = some m ∧ m.tag = r.expectedTag

theorem empty_closed : Closed empty := by
  intro a n h
  simp [empty] at h

/-- In a closed store, an unbound address is unreferenced: no resident node
points at it. Freshness therefore protects every resident reference from an
update at that address. -/
theorem Closed.not_referenced {σ : Store} (hσ : Closed σ) {a : Addr32}
    (hfresh : σ a = none) :
    ∀ b n, σ b = some n → ∀ r ∈ n.refs, r.addr ≠ a := by
  intro b n hb r hr heq
  obtain ⟨m, hm, _⟩ := hσ b n hb r hr
  rw [heq, hfresh] at hm
  exact nomatch hm

end Store

end Cas

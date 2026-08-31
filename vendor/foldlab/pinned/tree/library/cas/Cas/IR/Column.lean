import Cas.IR.Word
import Cas.Grammar.Sorts

/-!
# The column algebra of the trunk

The trunk's front end reads the store word as COLUMNS: one strip per
sort, blocks in admission order down each strip. This module is the
word face of that reading — the word partitioned by a POINTWISE
classifier `c : Binding → Option L`, which is `List.filter` on a
per-binding decision and nothing more.

The classifier is a parameter, not the grammar's. Any local labelling
a view invents — a facet, a selection, a search predicate — gets the
same three laws for free (`columnBy_append`, `mem_columnBy_iff`,
`columnBy_disjoint`), because they hold of pointwise classification
itself and not of what is being classified. The grammar's sort
classifier, `Grammar.Ty.ofTag ∘ Binding.node.tag`, is one instance
(`column`), and the strip of bindings it declines to label is
`unregistered`.

Pointwise is the load-bearing word. Because a binding's column depends
on that binding alone, the partition commutes with append, which is
what makes the front end incremental: a word that grows by a suffix
re-renders by appending to each strip, never by rebuilding it. Order
is semantics in the word, and the column laws preserve it — the
filtered strips keep admission order, and appending a suffix appends
to their tails.
-/

namespace Cas

namespace Word

/-- The strip of bindings a classifier sends to `l`. `List.filter`
wants a `Bool`, so the decision is spelled `decide`; the statements
below are all in terms of the `Option L` equation it decides. -/
def columnBy {L : Type} [DecidableEq L] (c : Binding → Option L) (l : L)
    (w : Word) : Word :=
  w.filter (fun b => decide (c b = some l))

/-- Append-localization: a column of a concatenation is the
concatenation of the columns. This is the incremental render — the UI
that has already drawn `w₁` draws a growth by `w₂` by appending to
each strip, never by recomputing one. -/
theorem columnBy_append {L : Type} [DecidableEq L] (c : Binding → Option L)
    (l : L) (w₁ w₂ : Word) :
    columnBy c l (w₁ ++ w₂) = columnBy c l w₁ ++ columnBy c l w₂ :=
  List.filter_append w₁ w₂

/-- Membership is exactly the classifier's verdict: a block is in the
`l` strip iff it is in the word and `c` labels it `l`. This is the
characterization every column proof reasons through, and it is what
lets the front end justify a rendered square by its binding alone. -/
theorem mem_columnBy_iff {L : Type} [DecidableEq L] {c : Binding → Option L}
    {l : L} {b : Binding} {w : Word} :
    b ∈ columnBy c l w ↔ b ∈ w ∧ c b = some l := by
  simp [columnBy, List.mem_filter]

/-- Distinct labels give disjoint strips: `c b` is one `Option L`, so
it cannot be `some l` and `some l'` at once. No block is ever drawn in
two columns. -/
theorem columnBy_disjoint {L : Type} [DecidableEq L] {c : Binding → Option L}
    {l l' : L} (h : l ≠ l') {b : Binding} {w : Word} :
    b ∈ columnBy c l w → b ∉ columnBy c l' w := by
  intro hb hb'
  have hl : c b = some l := (mem_columnBy_iff.mp hb).2
  have hl' : c b = some l' := (mem_columnBy_iff.mp hb').2
  rw [hl] at hl'
  injection hl' with heq
  exact h heq

/-- The sorts instance: the classifier is the grammar's own partial
inverse of the wire tag, read off the node the binding carries. -/
def column (t : Grammar.Ty) (w : Word) : Word :=
  columnBy (fun b => Grammar.Ty.ofTag b.node.tag) t w

/-- The strip for bindings the grammar declines to label — a tag
outside the sort table. It is a residue, not a refusal: the word is
admitted either way, and the front end still has somewhere to draw
it. -/
def unregistered (w : Word) : Word :=
  w.filter (fun b => decide (Grammar.Ty.ofTag b.node.tag = none))

/-- Append-localization for the sort columns, inherited. -/
theorem column_append (t : Grammar.Ty) (w₁ w₂ : Word) :
    column t (w₁ ++ w₂) = column t w₁ ++ column t w₂ :=
  columnBy_append _ t w₁ w₂

/-- Coverage: every binding of the word lands in some sort column or
in the unregistered strip. With `columnBy_disjoint` this is the front
end's totality guarantee — every block has EXACTLY one place to be
drawn, so a rendered board neither drops a binding nor doubles one. -/
theorem mem_column_or_unregistered {b : Binding} {w : Word} (h : b ∈ w) :
    (∃ t, b ∈ column t w) ∨ b ∈ unregistered w := by
  cases ht : Grammar.Ty.ofTag b.node.tag with
  | none =>
    refine Or.inr ?_
    show b ∈ List.filter _ w
    rw [List.mem_filter]
    exact ⟨h, by simp [ht]⟩
  | some t =>
    refine Or.inl ⟨t, ?_⟩
    show b ∈ columnBy (fun b => Grammar.Ty.ofTag b.node.tag) t w
    exact mem_columnBy_iff.mpr ⟨h, ht⟩

/-- The residue strip localizes over append too, so the incremental
render covers the whole board and not only its named columns. -/
theorem unregistered_append (w₁ w₂ : Word) :
    unregistered (w₁ ++ w₂) = unregistered w₁ ++ unregistered w₂ :=
  List.filter_append w₁ w₂

end Word

end Cas

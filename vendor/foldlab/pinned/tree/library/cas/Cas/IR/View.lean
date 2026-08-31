import Cas.IR.Column

/-!
# The view — "this view is a query", made a structure

A VIEW is a MONOID HOMOMORPHISM out of the store word: a target
carrier with a merge and an empty, a `run` into it, and the two laws
saying `run` respects the word's own monoid `(Word, ++, [])`. That is
the whole content of the phrase — a query over the word is not an
arbitrary function of it, it is a function that COMMUTES WITH GROWTH.

`run_append` IS the incremental render. A word grown by a suffix
re-renders by merging the suffix's contribution into what is already
drawn, never by recomputing the whole. `Column.lean` proves that shape
for the strips, one classifier at a time; this structure is the shape
itself, so a new query is admitted by exhibiting its two laws and
every consumer inherits incrementality without re-proving it.

Columns are the first inhabitants (`View.column`, `View.unregistered`),
and column HEIGHT is the second (`View.height`) — the query the
trunk's hypotenuse sorts by, and the first view whose carrier is not
the word. `View.lastK` is the third and the trunk's own carrier: the
last `k` bindings of ONE column, bounded by construction, so the front
end holds a window rather than a mirror of the store. `View.prod`
closes the family under pairing: a component reading two queries is
ONE view with ONE incremental render, so "how many views does this
component have" stops being a question the render path can get wrong.

## What `View.lastK` shows about this layer

`View` asks for two laws; `Query` (`Cas/IR/Query.lean`) asks for a
MONOID on the carrier and hands the two laws back. Every inhabitant
above `View.lastK` satisfies both, which made the two structures look
like the same demand written twice. `View.lastK` separates them: its
merge truncates, so it is associative on `Word` (`lastK_assoc`) and has
NO two-sided unit there — `merge empty w` is `lastK k w`, not `w`. It
is therefore a lawful view and NOT `View.ofQuery` of anything, which
`View.lastK_not_ofQuery` proves rather than asserts. The monoid it does
have lives on the BOUNDED carrier (words of length at most `k`), where
`lastK` is the identity; `View Word` is the unbounded reading of that
same object, and the gap between the two is exactly the field `Query`
cannot supply.

Associativity of `merge` needs no theorem here. On the image of `run`
it falls out of `List.append_assoc` through `run_append`: the word's
append is associative, and a homomorphism transports that to the
carrier wherever `run` reaches. Stating a view as a homomorphism
rather than as a function beside a cache is what makes that free.

Two things a view deliberately does NOT carry:

- **Its name.** A UI component is a NAMED view; the label comes from
  the naming homomorphism's emitted inventory and is no part of what
  the query computes.
- **Its channels.** How a view's numbers reach the eye is the trunk's
  six-field spec — `(classifier, order ruling, regime, cut cadence,
  DOI parameters, channel assignment)` in `GEOMETRY.md` — ruled by
  perceptual accuracy, and none of it is a fact about the query.

Both are ASSIGNED to a view from outside, which is what lets one view
be drawn twice, or drawn differently under two regimes, off one proof.
-/

namespace Cas

namespace Word

/-- A query over the store word that commutes with growth: `run` into
a carrier `α`, the carrier's `merge` and `empty`, and the two
homomorphism laws — `run_nil`, the empty word renders empty, and
`run_append`, the incremental render. Nothing here is about drawing;
the laws are what make drawing incremental. -/
structure View (α : Type) where
  run : Word → α
  merge : α → α → α
  empty : α
  run_nil : run [] = empty
  run_append : ∀ w v : Word, run (w ++ v) = merge (run w) (run v)

/-- The sort strip as a view. The carrier is the word itself, merge is
append, and `column_append` is the whole of the homomorphism law —
which is why the column algebra needed no new machinery to become a
view. -/
def View.column (t : Grammar.Ty) : View Word where
  run := Word.column t
  merge := (· ++ ·)
  empty := []
  run_nil := rfl
  run_append := Word.column_append t

/-- The residue strip as a view, on the same shape. The board's
totality (`mem_column_or_unregistered`) says the sort views and this
one together read every binding exactly once, so a rendered trunk
drops nothing and doubles nothing. -/
def View.unregistered : View Word where
  run := Word.unregistered
  merge := (· ++ ·)
  empty := []
  run_nil := rfl
  run_append := Word.unregistered_append

/-- COLUMN HEIGHT — the trunk's own numeric query, and the thing the
hypotenuse sorts by. The carrier is `Nat` under addition, so this is
the first view that is not the word cut down: growth adds heights, and
a redraw after a suffix is one addition per strip. -/
def View.height (t : Grammar.Ty) : View Nat where
  run := fun w => (Word.column t w).length
  merge := (· + ·)
  empty := 0
  run_nil := rfl
  run_append := by
    intro w v
    show (Word.column t (w ++ v)).length
        = (Word.column t w).length + (Word.column t v).length
    rw [Word.column_append, List.length_append]

/-! ## The bounded tail

`lastK` is the last `k` elements of a list. It is stated over a bare
`List α` because nothing in it is about bindings: the trunk wants it at
`Word`, the lemmas below are the reusable mint, and a proof that reads
`Binding` where it means `α` is a proof nobody borrows.

`lastK_append_eq` is the master statement and the only place a case
split appears — everything after it is rewriting. Read it as: the last
`k` of a concatenation is whatever the RIGHT side could not supply,
taken from the left. The two corollaries `lastK_left`/`lastK_right` say
a tail already taken is not taken again, and the view law
(`lastK_append`) and associativity (`lastK_assoc`) are one rewrite each
off those. -/

/-- The last `k` elements of a list, `[]` when `k` is `0` and the whole
list when the list is shorter than `k`. Spelled as a `drop` rather than
a reversed `take` because that is what a host does to a growing array
and because the index arithmetic is then the only thing to prove. -/
def lastK {α : Type} (k : Nat) (l : List α) : List α :=
  l.drop (l.length - k)

/-- The window is bounded by `k` and by the list, which is the whole
cost argument for the carrier: a column of ten million receipts is held
as `k` of them. -/
theorem lastK_length {α : Type} (k : Nat) (l : List α) :
    (lastK k l).length = min k l.length := by
  show (l.drop (l.length - k)).length = _
  rw [List.length_drop]
  omega

/-- Below the bound the window is the list itself. This is the sense in
which `lastK` is the identity on the bounded carrier, and it is the
field `Query`'s `Aggregator` needs and cannot have on all of `Word`. -/
theorem lastK_of_length_le {α : Type} {k : Nat} {l : List α}
    (h : l.length ≤ k) : lastK k l = l := by
  show l.drop (l.length - k) = l
  have hz : l.length - k = 0 := by omega
  rw [hz, List.drop_zero]

/-- THE MASTER STATEMENT, and the only case split in the file: the last
`k` of `x ++ y` is all of `y`'s window plus however much of `k` the
right side left unfilled, taken from `x`'s end. The split is on whether
`y` alone already fills the window — above the bound the left
contribution is empty on both sides, below it the two indices agree by
arithmetic. -/
theorem lastK_append_eq {α : Type} (k : Nat) (x y : List α) :
    lastK k (x ++ y) = lastK (k - y.length) x ++ lastK k y := by
  show (x ++ y).drop ((x ++ y).length - k)
      = x.drop (x.length - (k - y.length)) ++ y.drop (y.length - k)
  rw [List.length_append, List.drop_append]
  have hy : x.length + y.length - k - x.length = y.length - k := by omega
  rw [hy]
  by_cases h : k ≤ y.length
  · have h1 : x.length ≤ x.length + y.length - k := by omega
    have h2 : x.length ≤ x.length - (k - y.length) := by omega
    rw [List.drop_eq_nil_of_le h1, List.drop_eq_nil_of_le h2]
  · have h1 : x.length + y.length - k = x.length - (k - y.length) := by omega
    rw [h1]

/-- Nested windows collapse to the tighter one. A consumer that already
holds `k` receipts and is asked for `j ≤ k` of them answers from what it
holds — no re-read, which is why the bound composes down the render
path. -/
theorem lastK_lastK {α : Type} {j k : Nat} (h : j ≤ k) (l : List α) :
    lastK j (lastK k l) = lastK j l := by
  by_cases hl : l.length ≤ k
  · rw [lastK_of_length_le hl]
  · show (lastK k l).drop ((lastK k l).length - j) = l.drop (l.length - j)
    rw [lastK_length]
    show (l.drop (l.length - k)).drop (min k l.length - j) = _
    rw [List.drop_drop]
    congr 1
    omega

/-- Taking the window twice is taking it once. -/
theorem lastK_idem {α : Type} (k : Nat) (l : List α) :
    lastK k (lastK k l) = lastK k l := lastK_lastK (Nat.le_refl k) l

/-- A left operand already cut to the window may be cut again with no
loss: what the second cut would have dropped, the first already did. -/
theorem lastK_left {α : Type} (k : Nat) (x y : List α) :
    lastK k (lastK k x ++ y) = lastK k (x ++ y) := by
  rw [lastK_append_eq, lastK_append_eq, lastK_lastK (Nat.sub_le k y.length)]

/-- The same on the right, and the pair is what makes the merge
well-behaved on windows that were themselves computed by merging. -/
theorem lastK_right {α : Type} (k : Nat) (x y : List α) :
    lastK k (x ++ lastK k y) = lastK k (x ++ y) := by
  rw [lastK_append_eq, lastK_append_eq, lastK_idem, lastK_length]
  congr 2
  omega

/-- THE VIEW LAW, on plain lists: the window over a concatenation is the
window over the two windows. This is `View.lastK`'s `run_append` with
the column peeled off, and the reason the view costs one rewrite. -/
theorem lastK_append {α : Type} (k : Nat) (x y : List α) :
    lastK k (x ++ y) = lastK k (lastK k x ++ lastK k y) := by
  rw [lastK_left, lastK_right]

/-- The truncating merge IS associative on the unbounded carrier, which
is worth stating because the unit laws below are not: what `lastK` costs
a monoid is the identity, not the bracketing. Three pages of receipts
merged left-first and right-first give one window. -/
theorem lastK_assoc {α : Type} (k : Nat) (x y z : List α) :
    lastK k (lastK k (x ++ y) ++ z) = lastK k (x ++ lastK k (y ++ z)) := by
  rw [lastK_left, lastK_right, List.append_assoc]

/-- RUNG 0, first half: the merge does NOT commute. Two devices holding
the same receipts in different admission orders see different windows,
so the trunk's carrier gets no replica-agreement statement — `run_perm`
is unavailable to it by this witness. -/
theorem lastK_not_comm {α : Type} {x y : α} (h : x ≠ y) :
    lastK 1 ([x] ++ [y]) ≠ lastK 1 ([y] ++ [x]) := by
  intro hc
  have hxy : [y] = [x] := hc
  exact h (congrArg (fun l => l.headD x) hxy).symm

/-- RUNG 0, second half: the merge is NOT idempotent. Re-delivering a
page pushes its receipts through the window a second time, so
`run_replay` is unavailable too and the HOST must guard: the trunk's
fold drops entries with `seq < mark` (TRUNK-PLAN §3, S3a). That guard is
not decoration — it is the premise this theorem says the algebra will
not supply. -/
theorem lastK_not_idem {α : Type} (x : α) :
    lastK 2 ([x] ++ [x]) ≠ [x] := by
  intro hc
  have hlen : ([x, x] : List α).length = ([x] : List α).length :=
    congrArg List.length hc
  simp at hlen

/-- THE TRUNK'S CARRIER: the last `k` bindings OF COLUMN `t`. Indexed by
the column, never global — a view over the store's global tail paired
with a column's height would answer two different questions and the
front end would draw the pair as one.

The carrier is the word, the merge truncates, and `run_append` is
`column_append` (the classification localizes over append) followed by
`lastK_append` (the window does too). Cost is the point: `k` receipts
per column rather than the column, so a ten-million-receipt store is
rendered out of a bounded model.

**Rung 0, and the guard it forces on the host.** The merge is neither
commutative (`lastK_not_comm`) nor idempotent (`lastK_not_idem`): this
view is ORDER-SENSITIVE and NOT REPLAY-SAFE. A poll loop that re-
delivers a page corrupts the window, so the consumer's fold must guard
by `seq` (TRUNK-PLAN §3, S3a) — the guard is where replay safety comes
from, because it does not come from here.

**Not a query.** `View.lastK` is the first landed view that is NOT
`View.ofQuery` of any aggregator and generator; `View.lastK_not_ofQuery`
in `Cas/IR/Query.lean` proves it, and the module docstring above says
what the gap is. -/
def View.lastK (t : Grammar.Ty) (k : Nat) : View Word where
  run := fun w => Word.lastK k (Word.column t w)
  merge := fun a b => Word.lastK k (a ++ b)
  empty := []
  run_nil := List.drop_nil
  run_append := by
    intro w v
    show Word.lastK k (Word.column t (w ++ v))
        = Word.lastK k (Word.lastK k (Word.column t w)
            ++ Word.lastK k (Word.column t v))
    rw [Word.column_append, ← Word.lastK_append]

/-- Two views paired is one view, componentwise. A component that
reads a strip and its height, or two strips side by side, is a SINGLE
query with a single incremental render — the pairing carries both laws
and no consumer has to keep two renders in step. -/
def View.prod {α β : Type} (V : View α) (W : View β) : View (α × β) where
  run := fun w => (V.run w, W.run w)
  merge := fun x y => (V.merge x.1 y.1, W.merge x.2 y.2)
  empty := (V.empty, W.empty)
  run_nil := by
    show (V.run [], W.run []) = (V.empty, W.empty)
    rw [V.run_nil, W.run_nil]
  run_append := by
    intro w v
    show (V.run (w ++ v), W.run (w ++ v))
        = (V.merge (V.run w) (V.run v), W.merge (W.run w) (W.run v))
    rw [V.run_append, W.run_append]

end Word

end Cas

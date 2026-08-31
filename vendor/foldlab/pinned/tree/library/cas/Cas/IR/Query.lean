import Cas.IR.View

/-!
# The query layer — one function on the generators, and the laws follow

A VIEW carries its two homomorphism laws as fields. This module is the
step BELOW that: the word is the free monoid on `Binding`, so to give a
query out of it is exactly to give a target monoid and ONE FUNCTION ON
BINDINGS. The laws stop being something a query exhibits and become
something proved once, here, for every query there will ever be.

The target monoid is spelled as a record — `Aggregator`, carrying
`merge`, `empty` and the three laws — because no monoid typeclass
exists in this zero-dependency tower and the record is the honest
spelling of one. `Query.run A f w = (w.map f).foldr A.merge A.empty` is
the computed form, and `run_nil`/`run_append` are its two theorems.
`View.ofQuery` is the bridge: a query becomes a view by handing over
the laws it already has, so `View` stays exactly what it was and
nothing above it moves.

## The correspondence (banked reader lane, 2026-08-30)

Mathlib at tag `v4.33.1` names every piece of this, and the fit is
literal rather than analogical — restated here because the tower
imports nothing:

- `FreeMonoid α := List α` is a plain `def`, so our `Word` IS the free
  monoid on `Binding`. `FreeMonoid.lift : (α → M) ≃ (FreeMonoid α →* M)`
  is a genuine `Equiv`, and `lift_apply : lift f l = ((toList l).map f).prod`
  is `Query.run` character for character — the computed form of the
  universal property, which is why `run` is spelled as a `foldr` over a
  `map` and not as a bespoke recursion.
- `run_nil` and `run_append` are `map_one` and `map_mul` on a
  `MonoidHom`. Every query gets them by construction; `View` asks for
  them per inhabitant. That gap is the whole content of this module.
- `run_perm` is `List.Perm.foldr_eq` under `LeftCommutative`, restated
  in-tree as `Query.foldr_perm`. The reader's sharpest finding is
  preserved: left-commutativity ALONE settles the permutation fold —
  associativity is not needed for that step, and `Aggregator.left_comm`
  is where `Comm` plus `assoc` buys it. The quotient statement it
  computes is `Multiset.prod_add`.
- `storeAgg` is `List.dlookup_append`'s `Option.or` and `AList.union`'s
  documented left bias, with the difference that makes the product:
  `AList` ERASES shadowed keys under a `NodupKeys` invariant, and the
  word keeps them, physically, and lets `find` make them inert. The
  store is not beside this algebra — it is its oldest instance, and
  `Query.run_storeAgg` is the theorem that says so.

## The three rungs, and what each one buys

Each rung is a property of the TARGET, never of the word, and each one
buys a stated capability:

| rung | premise | what it buys |
|---|---|---|
| monoid | `assoc`, `empty_left`, `empty_right` | `run_append` — the incremental render; order-SENSITIVE |
| `Comm` | `merge` commutes | `run_perm` — two devices holding the same content in different admission orders AGREE |
| `Idem` | `merge x x = x` | `run_replay`, `run_dup_adjacent` — duplicate delivery cannot corrupt |

The three landed aggregators sit on three different rungs, which is the
argument for keeping the rungs separate from the floor: `wordAgg` is
the floor and no more (a strip's internal order is admission order,
deliberately), `natAgg` is commutative and not idempotent, `storeAgg`
is idempotent and not commutative — its bias is exactly what
`toStore_append_comm` pays `Store.Compatible` for.

`Query.run_redelivered` is the rung-2 statement in the words a delivery
layer would use: a binding delivered twice, at any two points of the
word, reads as one delivery. It needs both rungs; the adjacent case
needs only `Idem`.

## The floor is a premise, not a formality

The monoid rung is where this module starts, and it is easy to read that
as a technicality every view meets. It is not. `View.lastK` — the
trunk's own carrier, in `Cas/IR/View.lean` — is a lawful view whose
truncating merge is associative and has no unit on `Word`, so it is
`View.ofQuery` of nothing at all. `View.lastK_not_ofQuery`, at the foot
of this module, is that refutation, and it is the honest boundary of the
claim "a query is one function on bindings": it is a claim about the
views whose target really is a monoid on the carrier they answer in.
-/

namespace Cas

namespace Word

/-! ## The target monoid -/

/-- The target of a query: a carrier with a `merge`, an `empty`, and
the three monoid laws. This is the record spelling of a monoid — the
tower imports no algebraic hierarchy, so the structure IS the
typeclass, and every law a query needs is one of these three or a rung
below. -/
structure Aggregator (α : Type) where
  merge : α → α → α
  empty : α
  assoc : ∀ x y z : α, merge (merge x y) z = merge x (merge y z)
  empty_left : ∀ x : α, merge empty x = x
  empty_right : ∀ x : α, merge x empty = x

namespace Aggregator

/-- Rung 1: the target's merge commutes. The word still records
admission order; this says the ANSWER does not read it. -/
def Comm {α : Type} (A : Aggregator α) : Prop :=
  ∀ x y : α, A.merge x y = A.merge y x

/-- Rung 2: the target's merge is idempotent. Together with `Comm` this
is the join-semilattice rung — where every index lives, and where
re-delivery stops being a hazard. -/
def Idem {α : Type} (A : Aggregator α) : Prop :=
  ∀ x : α, A.merge x x = x

/-- Left-commutativity, which is what a permutation-stable fold
actually consumes. Mathlib's `Multiset.foldr` asks for exactly this and
nothing more (`LeftCommutative`); here it is bought with `Comm` and
`assoc` because the record carries both. -/
theorem left_comm {α : Type} {A : Aggregator α} (hc : A.Comm) (x y z : α) :
    A.merge x (A.merge y z) = A.merge y (A.merge x z) := by
  rw [← A.assoc, hc x y, A.assoc]

/-- Folding into a seed is folding into `empty` and then merging the
seed. This is the one lemma `run_append` needs and the only place the
identity laws are used; everything above it reads as algebra. -/
theorem foldr_seed {α : Type} (A : Aggregator α) (l : List α) (z : α) :
    l.foldr A.merge z = A.merge (l.foldr A.merge A.empty) z := by
  induction l with
  | nil => exact (A.empty_left z).symm
  | cons x rest ih =>
    show A.merge x (rest.foldr A.merge z)
        = A.merge (A.merge x (rest.foldr A.merge A.empty)) z
    rw [ih, A.assoc]

end Aggregator

/-! ## The query -/

namespace Query

/-- THE query: map the generator over the word, fold with the target's
merge. This is `FreeMonoid.lift`'s computed form (`lift_apply`) — the
universal property of the free monoid, spelled as the thing a machine
runs. A new query costs one function and one `Aggregator`; the laws
below are already proved for it. -/
def run {α : Type} (A : Aggregator α) (f : Binding → α) (w : Word) : α :=
  (w.map f).foldr A.merge A.empty

/-- The empty word renders empty — `map_one`, and true by computation.
-/
theorem run_nil {α : Type} (A : Aggregator α) (f : Binding → α) :
    run A f [] = A.empty := rfl

/-- One binding in front merges its own contribution — the step
equation every agreement proof below inducts through. -/
theorem run_cons {α : Type} (A : Aggregator α) (f : Binding → α)
    (b : Binding) (w : Word) :
    run A f (b :: w) = A.merge (f b) (run A f w) := rfl

/-- A one-binding word is its generator's value. `FreeMonoid.lift`'s
`lift_eval_of` — the sense in which `f` really is the query, read on
generators. -/
theorem run_singleton {α : Type} (A : Aggregator α) (f : Binding → α)
    (b : Binding) : run A f [b] = f b := by
  rw [run_cons, run_nil, A.empty_right]

/-- THE INCREMENTAL RENDER, proved once for every query there will ever
be — `map_mul` on a `MonoidHom`. A word grown by a suffix re-renders by
merging the suffix's answer into the answer already drawn. `View` asks
each inhabitant to exhibit this; the free monoid gives it away. -/
theorem run_append {α : Type} (A : Aggregator α) (f : Binding → α)
    (w v : Word) : run A f (w ++ v) = A.merge (run A f w) (run A f v) := by
  show ((w ++ v).map f).foldr A.merge A.empty = _
  rw [List.map_append, List.foldr_append]
  exact A.foldr_seed _ _

/-! ### Rung 1 — commutative targets factor through reordering -/

/-- The permutation fold, restated in-tree because the tower imports
nothing: a LEFT-COMMUTATIVE binary operation folds a list to an answer
that does not read the list's order. Mathlib spells this
`List.Perm.foldr_eq` over the `LeftCommutative` class, and the premise
really is that weak — no associativity appears here. -/
theorem foldr_perm {β γ : Type} {g : β → γ → γ}
    (hg : ∀ x y : β, ∀ z : γ, g x (g y z) = g y (g x z)) :
    ∀ {l₁ l₂ : List β}, l₁.Perm l₂ → ∀ z : γ, l₁.foldr g z = l₂.foldr g z := by
  intro l₁ l₂ h
  induction h with
  | nil => intro z; rfl
  | cons x _ ih => intro z; show g x _ = g x _; rw [ih]
  | swap x y l => intro z; exact hg y x (l.foldr g z)
  | trans _ _ ih₁ ih₂ => intro z; rw [ih₁, ih₂]

/-- Rung 1's earned theorem, and the replication statement the store
has wanted a home for: over a COMMUTATIVE target, two words holding the
same bindings in different admission orders give the same answer.
Replica agreement is not a protocol property — it is a rung of the
query's target. -/
theorem run_perm {α : Type} {A : Aggregator α} (hc : A.Comm) (f : Binding → α)
    {w v : Word} (h : w.Perm v) : run A f w = run A f v :=
  foldr_perm (Aggregator.left_comm hc) (h.map f) A.empty

/-! ### Rung 2 — idempotent targets survive re-delivery -/

/-- Whole-word replay: re-admitting everything already admitted changes
no answer. The premise is `Idem` alone. -/
theorem run_replay {α : Type} {A : Aggregator α} (hi : A.Idem) (f : Binding → α)
    (w : Word) : run A f (w ++ w) = run A f w := by
  rw [run_append]; exact hi _

/-- Per-message replay, adjacent case: a binding delivered twice in a
row reads as one delivery. This lands under `Idem` and `assoc` alone —
`Comm` is not consumed, which is worth stating because the general case
below does consume it. -/
theorem run_dup_adjacent {α : Type} {A : Aggregator α} (hi : A.Idem)
    (f : Binding → α) (b : Binding) (w v : Word) :
    run A f (w ++ b :: b :: v) = run A f (w ++ b :: v) := by
  have key : run A f (b :: b :: v) = run A f (b :: v) := by
    rw [run_cons, run_cons, ← A.assoc, hi]
  rw [run_append, key, ← run_append]

/-- Per-message replay, general case — the CRDT rung stated in a
delivery layer's own words: a binding delivered twice, at any two
points of the word, reads as one delivery. Both rungs are consumed:
`Comm` to bring the two deliveries together, `Idem` to collapse them.

The parentheses are written out: `::` binds tighter than `++`, so the
unparenthesized spelling would associate the word somewhere else than
where the statement means it. -/
theorem run_redelivered {α : Type} {A : Aggregator α} (hc : A.Comm) (hi : A.Idem)
    (f : Binding → α) (b : Binding) (w₁ w₂ w₃ : Word) :
    run A f (w₁ ++ (b :: (w₂ ++ (b :: w₃))))
      = run A f (w₁ ++ (b :: (w₂ ++ w₃))) := by
  have key : run A f (b :: (w₂ ++ b :: w₃)) = run A f (b :: (w₂ ++ w₃)) := by
    rw [run_cons, run_cons, run_append, run_append, run_cons,
      Aggregator.left_comm hc (run A f w₂) (f b) (run A f w₃), ← A.assoc, hi]
  rw [run_append, key, ← run_append]

end Query

/-! ## The bridge to `View` -/

/-- A query IS a view: hand `View` the two laws the free monoid already
proved. Every inhabitant of `View` below is now one function and one
`Aggregator`, and `View` itself did not move — the UI-facing kind stays
exactly what it was. -/
def View.ofQuery {α : Type} (A : Aggregator α) (f : Binding → α) : View α where
  run := Query.run A f
  merge := A.merge
  empty := A.empty
  run_nil := rfl
  run_append := Query.run_append A f

/-- Two views with the same `run`, `merge` and `empty` are the same
view. The law fields are propositions, so once the data agrees there is
nothing left to compare — which is what lets the agreements below be
stated as EQUALITIES of views rather than as pointwise coincidences. -/
theorem View.ext {α : Type} {V W : View α} (hrun : V.run = W.run)
    (hmerge : V.merge = W.merge) (hempty : V.empty = W.empty) : V = W := by
  cases V; cases W
  subst hrun; subst hmerge; subst hempty
  rfl

/-! ## The three landed aggregators

One per rung. Their differences are the argument for keeping the rungs
apart from the floor. -/

/-- The word itself as a target: concatenation and the empty word. The
FLOOR rung and no more — a strip's internal order is admission order,
deliberately, so this aggregator is neither commutative nor
idempotent. -/
def wordAgg : Aggregator Word where
  merge := (· ++ ·)
  empty := []
  assoc := List.append_assoc
  empty_left := List.nil_append
  empty_right := List.append_nil

/-- Counting's target: `(Nat, +, 0)`. Rung 1 — commutative, and not
idempotent. -/
def natAgg : Aggregator Nat where
  merge := (· + ·)
  empty := 0
  assoc := Nat.add_assoc
  empty_left := Nat.zero_add
  empty_right := Nat.add_zero

/-- The STORE as a target: pointwise left-biased union, empty
everywhere. `Option.or` is the left bias spelled in core, and it is the
same bias `toStore_append` states — the first word answers wherever it
can. Rung 2 without rung 1: idempotent (`storeAgg_idem`) and NOT
commutative, which is exactly why `toStore_append_comm` has to buy
symmetry with `Store.Compatible`. -/
def storeAgg : Aggregator Store where
  merge := fun σ τ a => (σ a).or (τ a)
  empty := fun _ => none
  assoc := by
    intro σ τ ρ
    funext a
    show (((σ a).or (τ a)).or (ρ a)) = ((σ a).or ((τ a).or (ρ a)))
    cases σ a <;> rfl
  empty_left := by
    intro σ
    funext a
    show (none : Option Node).or (σ a) = σ a
    rfl
  empty_right := by
    intro σ
    funext a
    show (σ a).or none = σ a
    cases σ a <;> rfl

/-- Counting commutes. -/
theorem natAgg_comm : natAgg.Comm := Nat.add_comm

/-- The store join is idempotent, and it costs nothing: the left bias
makes the second copy inert pointwise. This is `toStore_append_self`
one level down, stated about the TARGET rather than about the word. -/
theorem storeAgg_idem : storeAgg.Idem := by
  intro σ
  funext a
  show (σ a).or (σ a) = σ a
  cases σ a <;> rfl

/-! ## The generic shapes the landed views instantiate -/

/-- A word-valued query whose generator emits a singleton or nothing IS
a filter. Pointwise classification and `List.filter` are the same
object read two ways, which is why `columnBy` needed no new machinery
to become a query. -/
theorem Query.run_wordAgg_filter (p : Binding → Bool) (w : Word) :
    Query.run wordAgg (fun b => if p b then [b] else []) w = w.filter p := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
    rw [Query.run_cons, ih]
    show (if p b then [b] else []) ++ rest.filter p = (b :: rest).filter p
    rw [List.filter_cons]
    cases p b <;> simp

/-- A `Nat`-valued query whose generator emits 0 or 1 counts the same
filter. This is `FreeAddMonoid.countP` — Mathlib bundles it as an
`AddMonoidHom`; here it is one instance of the one bundling this module
already has. -/
theorem Query.run_natAgg_count (p : Binding → Bool) (w : Word) :
    Query.run natAgg (fun b => if p b then 1 else 0) w = (w.filter p).length := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
    rw [Query.run_cons, ih]
    show (if p b then 1 else 0) + (rest.filter p).length
        = ((b :: rest).filter p).length
    rw [List.filter_cons]
    cases p b <;> simp <;> omega

/-! ## The landed views, re-derived

Each theorem exhibits a query already in the tree as `Query.run` of a
generator and an aggregator. Nothing is replaced: `Word.column`,
`Word.unregistered` and the height are untouched, and these are the
statements that they were queries all along. -/

/-- The generator of a column: a binding contributes ITSELF when the
classifier labels it `l`, and nothing otherwise. -/
def columnGen {L : Type} [DecidableEq L] (c : Binding → Option L) (l : L)
    (b : Binding) : Word :=
  if c b = some l then [b] else []

/-- The generator of the residue strip: a binding contributes itself
when the grammar declines to label it. -/
def unregisteredGen (b : Binding) : Word :=
  if Grammar.Ty.ofTag b.node.tag = none then [b] else []

/-- The generator of a column's HEIGHT: one for a binding in the strip,
zero otherwise. -/
def heightGen (t : Grammar.Ty) (b : Binding) : Nat :=
  if Grammar.Ty.ofTag b.node.tag = some t then 1 else 0

/-- The generator of the STORE: the one-binding store. `Finsupp.single`
is the same gesture in Mathlib's group-by carrier; the name says
`Store` because in `Word`'s namespace a bare `single` would read as a
one-binding word. -/
def singleStore (b : Binding) : Store :=
  fun a => if a = b.address then some b.node else none

/-- A classified strip is a query over `(Word, ++, [])`. -/
theorem columnBy_eq_run {L : Type} [DecidableEq L] (c : Binding → Option L)
    (l : L) (w : Word) :
    Query.run wordAgg (columnGen c l) w = columnBy c l w := by
  have h : columnGen c l = fun b => if decide (c b = some l) then [b] else [] := by
    funext b
    show (if c b = some l then [b] else []) = _
    by_cases hb : c b = some l <;> simp [hb]
  rw [h, Query.run_wordAgg_filter]
  rfl

/-- The sort strips are queries, inherited from the classifier. -/
theorem column_eq_run (t : Grammar.Ty) (w : Word) :
    Query.run wordAgg (columnGen (fun b => Grammar.Ty.ofTag b.node.tag) t) w
      = column t w :=
  columnBy_eq_run _ t w

/-- The residue strip is a query too, so the re-derivation covers the
whole board and not only its named columns. -/
theorem unregistered_eq_run (w : Word) :
    Query.run wordAgg unregisteredGen w = unregistered w := by
  have h : unregisteredGen
      = fun b => if decide (Grammar.Ty.ofTag b.node.tag = none) then [b] else [] := by
    funext b
    show (if Grammar.Ty.ofTag b.node.tag = none then [b] else []) = _
    by_cases hb : Grammar.Ty.ofTag b.node.tag = none <;> simp [hb]
  rw [h, Query.run_wordAgg_filter]
  rfl

/-- Column height is a query over `(Nat, +, 0)` — the trunk's numeric
view, and the first one whose carrier is not the word cut down. -/
theorem height_eq_run (t : Grammar.Ty) (w : Word) :
    Query.run natAgg (heightGen t) w = (column t w).length := by
  have h : heightGen t
      = fun b => if decide (Grammar.Ty.ofTag b.node.tag = some t) then 1 else 0 := by
    funext b
    show (if Grammar.Ty.ofTag b.node.tag = some t then 1 else 0) = _
    by_cases hb : Grammar.Ty.ofTag b.node.tag = some t <;> simp [hb]
  rw [h, Query.run_natAgg_count]
  rfl

/-- THE CROWN: the bridge onto the store is itself a query. The
aggregator is stores under left-biased pointwise union, the generator
is the one-binding store, and `toStore` is what `Query.run` computes.
The store is not beside the query algebra — it is its oldest instance,
and `toStore_append` was `run_append` all along.

The carrier is a function type, so the equality is `funext`'s; the
statement is an equality of stores because a store IS a function. -/
theorem Query.run_storeAgg (w : Word) :
    Query.run storeAgg singleStore w = toStore w := by
  induction w with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨a, n⟩ := e
    rw [Query.run_cons, ih]
    funext x
    show (if x = a then some n else none).or (find rest x)
        = find (Binding.mk a n :: rest) x
    by_cases hx : x = a <;> simp [find, hx]

/-! ## The views themselves, as equalities

The pointwise agreements above lift to the structures: the landed views
ARE their query-derived twins, not merely equal on every word. -/

/-- `View.column` is `View.ofQuery` of the sort classifier. -/
theorem View.column_eq_ofQuery (t : Grammar.Ty) :
    View.column t
      = View.ofQuery wordAgg (columnGen (fun b => Grammar.Ty.ofTag b.node.tag) t) :=
  View.ext (funext fun w => (column_eq_run t w).symm) rfl rfl

/-- `View.unregistered` is `View.ofQuery` of the residue generator. -/
theorem View.unregistered_eq_ofQuery :
    View.unregistered = View.ofQuery wordAgg unregisteredGen :=
  View.ext (funext fun w => (unregistered_eq_run w).symm) rfl rfl

/-- `View.height` is `View.ofQuery` over `(Nat, +, 0)`. -/
theorem View.height_eq_ofQuery (t : Grammar.Ty) :
    View.height t = View.ofQuery natAgg (heightGen t) :=
  View.ext (funext fun w => (height_eq_run t w).symm) rfl rfl

/-! ## The bridge is not a bijection — `View.lastK` is the witness

Three views in, `View.ofQuery` looked total: every inhabitant of `View`
was a query, and the two structures read like one demand written twice.
The trunk's own carrier is where they come apart, and the separation is
worth a theorem rather than a remark, because a layer nobody can leave
is a layer nobody has to think about.

`View` asks for `run_nil` and `run_append`. `Aggregator` asks for a
MONOID: associativity AND a two-sided unit, on the whole carrier.
`View.lastK`'s merge truncates to `k`, so `merge empty w` is `lastK k w`
and not `w` — associativity survives (`lastK_assoc`), the unit does not.
No aggregator can therefore carry it, and the refutation costs one
witness: a word of `k+1` copies of any binding, whose window is `k`.

What this is NOT: a hole in the query layer. The monoid `lastK` does
have lives on the BOUNDED carrier — words of length at most `k`, where
`lastK` is the identity by `lastK_of_length_le` — and `View Word` is
that object read at the unbounded type. `View.ofQuery` builds views out
of monoids on the carrier as stated; `View.lastK` is a monoid on a
SUBTYPE of it, pushed forward. Closing the gap in general would mean
`Query` over a target carrier that is not the view's carrier, which is a
mint and a ruling, not a lemma. Flagged as such.
-/

/-- A witness binding, private and inert: the refutation below needs a
word of a given length and nothing about what is in it. The zero
address and the empty node follow the spelling five other modules in
this package already use for their fixtures. -/
private def witBinding : Binding :=
  ⟨⟨List.replicate 32 0, by simp⟩, ⟨0, 0, [], []⟩⟩

/-- THE SEPARATION: `View.lastK` is not `View.ofQuery` of any aggregator
and any generator. The proof reads `A.empty_left` off the assumed
equality — it forces `lastK k w = w` for EVERY word — and refutes it by
length at `k+1` copies of one binding.

Stated as a refutation of existence rather than as a `≠` on two named
values, because the content is that NOTHING in the query layer produces
this view, not that some particular candidate fails. -/
theorem View.lastK_not_ofQuery (t : Grammar.Ty) (k : Nat) :
    ¬ ∃ (A : Aggregator Word) (f : Binding → Word),
        View.ofQuery A f = View.lastK t k := by
  rintro ⟨A, _f, h⟩
  have hm : A.merge = fun a b => Word.lastK k (a ++ b) := congrArg View.merge h
  have he : A.empty = ([] : Word) := congrArg View.empty h
  have key := A.empty_left (List.replicate (k + 1) witBinding)
  rw [hm, he] at key
  have key' : Word.lastK k (List.replicate (k + 1) witBinding)
      = List.replicate (k + 1) witBinding := key
  have hlen := congrArg List.length key'
  rw [lastK_length, List.length_replicate] at hlen
  omega

end Word

end Cas

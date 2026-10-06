import Effect4.Laws.Auto.Semantics
import Effect4.Laws.Auto.SubsetTac

/-!
# Laws.Slice.Lattice — the generic theory of type slices

A **type slice** of one program is the part of it that is kept: the list of its kept **sites**
(`Slice.kept`). A site is an address of the program. A site that a slice does not keep is
**omitted**, and the omitted sites of a slice are its **mask** (`Slice.omitted`). A slice is below
another when it keeps no more: **a smaller slice keeps less**. A **slice view** (`SliceView`)
gives each slice a type, and it is monotone: a slice that keeps less has a type at or below. A
query is a type. It is **valid** for a slice when the slice's type is at or above it
(`SliceView.Valid`).

**The words.** In the dictionary (`docs/core/controlled-english.md`) a slice alone is a unit of
work, and a fold is the catamorphism. So each docstring here says "type slice" at its first use,
and a site that is not kept is omitted: no site is called "folded". To omit is to replace a
sub-program by a hole (decisions row 288). What stands at an omitted site is the instance's.

The statements are the consequences of Theorems 4.5, 4.6 and 4.7 of Carroll, Madhavapeddy and
Omar 2026, *Bidirectional Type Slicing* (pages 9 to 12; each page is of the vendored PDF,
`vendor/papers/program-graphs/bidirectional-type-slicing-2607.12197v1.pdf`). Each proof uses two
facts only: a slice keeps finitely many sites, and the view is monotone. No statement names
`Eff`, `Ty` or the checker. An instance owes one fact, `SliceView.mono`, and nothing about its
carrier. Nothing transfers from the paper by citation: each statement is proved here.

**Keeps the same sites, where the paper says equal.** Two lists that keep the same sites are two
values, so the order on slices is a preorder. Where the paper says that two slices are equal,
this module says that each is below the other: they keep the same sites. `SliceView.Minimal` is
the paper's Definition 4.3 (p. 9) read that way.

**An instance chooses its `T`.** A view has one type side, with one order. The checker's type
has three columns, and an instance takes one. The first instance, the omission that declares the
answer alone (decisions rows 286 and 288), takes the error or the requirement, and not the three
columns. A finite probe of seat CENSUS on 2026-10-06 found its answer column not monotone across
a fork, and the two other columns monotone on each pair of masks that it tried.

**A second fact, for a tree of sites only.** The sites of a real program are the addresses of a
tree, and an omission at an address omits its sub-tree. So omitting a site changes nothing when
its parent is omitted already: the instance's no-op. Two statements take it as a premise. A
minimal slice is then a highlighted tree (`SliceView.Minimal.keeps_above`). And the descent can
ask nothing about a site under an omitted parent, and give the same slice
(`SliceView.descendTree_eq_descend`). No other statement needs it.

The parts, in order:

- the carrier and its order, with Lean core's order classes (`Std.IsPreorder`,
  `Std.LawfulOrderSup`, `Std.LawfulOrderInf`), which `CTy` and `ErrTy` carry on the type side
  (`src/Effect4/Laws/Program/TypeAlgebra.lean`);
- the descent on a list of sites: one pass (`Slice.sweep`), the pass's questions
  (`Slice.sweepAsked`), the paper's restart (`Slice.restart`), and the pass that asks nothing at
  a site that changes nothing (`Slice.sweepFree`);
- the view, validity and minimality, with the executable `descend`, `descendTree`, `isMinimal`,
  `minimals` and `contribution`;
- the statements.

Placement. Concept `subtyping-algebra`. Requirement R14, under the claim
`slice-lattice-minimal`, whose pointer is `SliceView.lattice_minimal`. Reach: every monotone map
from the slices of one program to a preorder of types, with a decided order on the types and
decided equality of sites where a statement names them. Consumer: each slice view, first the
error and requirement provenance of the plan
(`docs/research/2026-10-06-type-slicing-plan.md`, section 8, order 4). The statements do not
establish that any real type map is monotone or has the no-op, a least slice, a minimum-size
slice, or a bound for the contribution slice below a search. The design is
`docs/research/2026-10-06-seat-LATTICE-design.md`. The controls and the paper's examples are in
`Test/Program/SliceLattice.lean`.
-/

set_option autoImplicit false

namespace Effect4

universe u v

/-- A type slice of one program: the sites that it keeps. It is the paper's highlight of a term
(p. 7). The order is by what is kept: a smaller slice keeps less. Every site that the list does
not hold is omitted. -/
structure Slice (α : Type u) where
  /-- the kept sites, in the order that the descent tries them -/
  kept : List α
deriving Repr, DecidableEq

namespace Slice

variable {α : Type u}

/-! ## The carrier's order -/

/-- `a ≤ b`: `a` keeps no more than `b`. A smaller type slice keeps less. -/
instance : LE (Slice α) := ⟨fun a b => a.kept ⊆ b.kept⟩

/-- The order is a preorder. It is not antisymmetric: two lists can keep the same sites. -/
@[semantics "subtyping-algebra" (requirement := R14)]
instance : Std.IsPreorder (Slice α) where
  le_refl a := List.Subset.refl a.kept
  le_trans _ _ _ hab hbc := List.Subset.trans hab hbc

/-- The join keeps what either type slice keeps. -/
instance : Max (Slice α) := ⟨fun a b => ⟨a.kept ++ b.kept⟩⟩

/-- The join is the least upper bound. -/
@[semantics "subtyping-algebra" (requirement := R14)]
instance : Std.LawfulOrderSup (Slice α) where
  max_le_iff _ _ _ := List.append_subset

/-- The order is decided, where equality of sites is. -/
instance instDecidableLE [DecidableEq α] (a b : Slice α) : Decidable (a ≤ b) :=
  decidable_of_iff (∀ x ∈ a.kept, x ∈ b.kept) Iff.rfl

/-- The meet keeps what both type slices keep. A view need not keep it: the meet of two valid
slices can lose the type (the paper, p. 23; `Test/Program/SliceLattice.lean`). -/
instance [DecidableEq α] : Min (Slice α) := ⟨fun a b => ⟨a.kept.filter (· ∈ b.kept)⟩⟩

/-- The meet is the greatest lower bound. -/
@[semantics "subtyping-algebra" (requirement := R14)]
instance [DecidableEq α] : Std.LawfulOrderInf (Slice α) where
  le_min_iff a b c := by
    constructor
    · intro h
      exact ⟨fun x hx => (List.mem_filter.mp (h hx)).1,
        fun x hx => of_decide_eq_true (List.mem_filter.mp (h hx)).2⟩
    · intro h x hx
      exact List.mem_filter.mpr ⟨h.1 hx, decide_eq_true (h.2 hx)⟩

/-- The type slice one site below: it keeps every site of `s` but `x`. -/
def drop [DecidableEq α] (s : Slice α) (x : α) : Slice α := ⟨s.kept.filter (· ≠ x)⟩

/-- The type slice without a site is below the slice. A step of `SliceView.minimal_iff_drop`,
its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem drop_le [DecidableEq α] (s : Slice α) (x : α) : s.drop x ≤ s :=
  fun _ hy => (List.mem_filter.mp hy).1

/-- The type slice without a site does not keep it. A step of `SliceView.minimal_iff_drop`, its
one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem not_mem_drop [DecidableEq α] (s : Slice α) (x : α) : x ∉ (s.drop x).kept := by
  intro h
  exact of_decide_eq_true (List.mem_filter.mp h).2 rfl

/-- A type slice below `s` that does not keep `x` is below `s` without `x`: each slice strictly
below is below a slice one site below. A step of `SliceView.minimal_iff_drop`, its one
consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem le_drop [DecidableEq α] {j s : Slice α} {x : α} (h : j ≤ s) (hx : x ∉ j.kept) :
    j ≤ s.drop x := by
  intro y hy
  refine List.mem_filter.mpr ⟨h hy, decide_eq_true ?_⟩
  rintro rfl
  exact hx hy

/-! ## The type slices below one slice -/

/-- Every sub-list of a list: `2 ^ n` lists for `n` elements. -/
def sublists : List α → List (List α)
  | [] => [[]]
  | x :: xs => sublists xs ++ (sublists xs).map (x :: ·)

/-- The type slices below `s`, one for each sub-list of its sites. It is the finiteness of the
carrier, as a list: the paper's Theorem 3.3 (p. 7) for this carrier. A search over it asks
`2 ^ n` slices. The name is not `below`: that spelling under a structure is a generated
companion's, and the tree's population reads it as one (`ProofGraph.isGeneratedCompanion`). -/
def subslices (s : Slice α) : List (Slice α) := (sublists s.kept).map Slice.mk

/-- A listed sub-list holds elements of the list only. A step of `le_of_mem_subslices`, its one
consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sublists_subset : ∀ (l l' : List α), l' ∈ sublists l → l' ⊆ l
  | [], l', h => by
    obtain rfl := List.mem_singleton.mp h
    exact List.Subset.refl _
  | x :: xs, l', h => by
    rcases List.mem_append.mp h with h | h
    · exact List.Subset.trans (sublists_subset xs l' h) (List.subset_cons_self x xs)
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
      exact List.cons_subset_cons x (sublists_subset xs t ht)

/-- Each selection of a list's elements is a listed sub-list. A step of `exists_mem_subslices`,
its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem filter_mem_sublists (p : α → Bool) : ∀ l : List α, l.filter p ∈ sublists l
  | [] => List.mem_singleton.mpr rfl
  | x :: xs => by
    rw [List.filter_cons]
    split
    · exact List.mem_append_right _ (List.mem_map_of_mem (filter_mem_sublists p xs))
    · exact List.mem_append_left _ (filter_mem_sublists p xs)

/-- A listed type slice is below the slice. A step of `SliceView.contribution_lub`, through
`SliceView.minimals_sound`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem le_of_mem_subslices {j s : Slice α} (h : j ∈ s.subslices) : j ≤ s := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h
  exact sublists_subset s.kept l hl

/-- **The type slices below one slice are finitely many**, up to their kept sites: each slice
below `s` keeps the same sites as a listed one. It is the paper's Theorem 3.3 (p. 7), for this
carrier. A step of `SliceView.contribution_lub`, through `SliceView.minimals_complete`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem exists_mem_subslices [DecidableEq α] {j s : Slice α} (h : j ≤ s) :
    ∃ j' ∈ s.subslices, j' ≤ j ∧ j ≤ j' :=
  ⟨⟨s.kept.filter (· ∈ j.kept)⟩, List.mem_map_of_mem (filter_mem_sublists _ s.kept),
    fun _ hx => of_decide_eq_true (List.mem_filter.mp hx).2,
    fun _ hx => List.mem_filter.mpr ⟨h hx, decide_eq_true hx⟩⟩

/-! ## What a type slice omits -/

/-- The mask of the type slice `s`: the sites of `sites` that it omits. A smaller slice omits
more. -/
def omitted [DecidableEq α] (sites : List α) (s : Slice α) : List α := sites.filter (· ∉ s.kept)

/-- A smaller type slice omits more. A step of `SliceView.ofOmitted`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem omitted_anti [DecidableEq α] (sites : List α) {a b : Slice α} (h : a ≤ b) :
    b.omitted sites ⊆ a.omitted sites := by
  intro x hx
  obtain ⟨hs, hb⟩ := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨hs, decide_eq_true fun ha => of_decide_eq_true hb (h ha)⟩

/-- A type slice omits sites of the given list only. A step of `SliceView.ofOmitted`, its one
consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem omitted_subset [DecidableEq α] (sites : List α) (s : Slice α) : s.omitted sites ⊆ sites :=
  fun _ hx => (List.mem_filter.mp hx).1

/-- The type slice of every site omits nothing. A step of `SliceView.ofOmitted_full`, its one
consumer. The proof is by a `match`: `List.filter_eq_nil_iff` reaches `Classical.choice` on this
toolchain. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem omitted_full [DecidableEq α] (sites : List α) : (Slice.mk sites).omitted sites = [] := by
  match h : (Slice.mk sites).omitted sites with
  | [] => rfl
  | x :: _ =>
    have hx : x ∈ (Slice.mk sites).omitted sites := by rw [h]; exact List.mem_cons_self
    exact absurd (List.mem_filter.mp hx).1 (of_decide_eq_true (List.mem_filter.mp hx).2)

/-! ## The descent on a list of sites -/

/-- **The descent, as one pass.** `done` holds the sites tried and kept, and the second list the
sites not yet tried. The pass tries each site once, in the order of the list. It drops a site
exactly when the type slice without it is still valid. The recursion is on the list of sites not yet
tried, so the pass ends. It asks `valid` once for each of those sites (`sweepAsked_length`,
`sweep_congr`). -/
def sweep (valid : Slice α → Bool) : List α → List α → List α
  | done, [] => done
  | done, x :: rest =>
    if valid ⟨done ++ rest⟩ then sweep valid done rest else sweep valid (done ++ [x]) rest

/-- The pass's questions: each type slice that `sweep` asks `valid` about, in the order asked.
It follows the pass's own recursion. `sweep_congr` is what makes it the list of the questions: the
pass's result depends on `valid` at these slices only. -/
def sweepAsked (valid : Slice α → Bool) : List α → List α → List (Slice α)
  | _, [] => []
  | done, x :: rest =>
    ⟨done ++ rest⟩ ::
      (if valid ⟨done ++ rest⟩ then sweepAsked valid done rest
        else sweepAsked valid (done ++ [x]) rest)

/-- The first valid type slice one site below, in the order of the list: the sites of `done`,
then the sites not yet tried without the first one whose removal keeps validity. `none` when no
such site is left. -/
def firstDrop (valid : Slice α → Bool) : List α → List α → Option (List α)
  | _, [] => none
  | done, x :: rest =>
    if valid ⟨done ++ rest⟩ then some (done ++ rest) else firstDrop valid (done ++ [x]) rest

/-- A found type slice has one site fewer. A step of the termination of `restart`, its one
consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem firstDrop_length (valid : Slice α → Bool) (done todo : List α) (l' : List α)
    (h : firstDrop valid done todo = some l') : l'.length + 1 = done.length + todo.length := by
  fun_induction firstDrop valid done todo with
  | case1 done => exact nomatch h
  | case2 done x rest _ =>
    obtain rfl := Option.some.inj h
    rw [List.length_append, List.length_cons]
    omega
  | case3 done x rest _ ih =>
    have := ih h
    rw [List.length_append, List.length_singleton] at this
    rw [List.length_cons]
    omega

/-- **The paper's descent** (the brute-force algorithm, pp. 9 and 10): take the first valid type
slice one site below, and start again from it. It stops when no slice one site below is valid.
Each start asks again about the sites that failed before. `restart_eq_sweep` is its agreement
with the one pass. -/
def restart (valid : Slice α → Bool) (l : List α) : List α :=
  match h : firstDrop valid [] l with
  | none => l
  | some l' =>
    have : l'.length < l.length := by
      have := firstDrop_length valid [] l l' h
      rw [List.length_nil] at this
      omega
    restart valid l'
termination_by l.length

/-! ### The pass's law

The four lemmas of this section are steps of `SliceView.descend_sublist` and
`SliceView.descend_minimal`. The first two hold for every `valid`. The last one asks that
`valid` is upward closed, which a view's validity is (`SliceView.valid_up`). -/

/-- The pass keeps a sub-list of its sites: the sites of `done`, then some of the others, in
their order. A step of `SliceView.descend_sublist`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sweep_sublist (valid : Slice α → Bool) (done todo : List α) :
    (sweep valid done todo).Sublist (done ++ todo) := by
  fun_induction sweep valid done todo with
  | case1 done => rw [List.append_nil]; exact List.Sublist.refl done
  | case2 done x rest _ ih =>
    exact ih.trans (List.Sublist.append_left (List.sublist_cons_self x rest) done)
  | case3 done x rest _ ih => rwa [List.append_assoc, List.singleton_append] at ih

/-- The pass keeps validity: it moves to a type slice only after `valid` accepted it. It needs no
upward closure. A step of `SliceView.descend_minimal`, through `SliceView.descend_valid`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sweep_valid (valid : Slice α → Bool) (done todo : List α)
    (h : valid ⟨done ++ todo⟩ = true) : valid ⟨sweep valid done todo⟩ = true := by
  fun_induction sweep valid done todo with
  | case1 done => rwa [List.append_nil] at h
  | case2 done x rest hc ih => exact ih hc
  | case3 done x rest _ ih => exact ih (by rwa [List.append_assoc, List.singleton_append])

/-- A type slice within `done ++ x :: rest`, without `x`, is below the slice that the pass asked
about at `x`. A step of `sweep_kept_needed` and of `sweepFree_eq_sweep`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem drop_le_of_subset [DecidableEq α] {r done rest : List α} {x : α}
    (h : r ⊆ done ++ x :: rest) : (Slice.mk r).drop x ≤ ⟨done ++ rest⟩ := by
  intro z hz
  obtain ⟨hzr, hzx⟩ := List.mem_filter.mp hz
  rcases List.mem_append.mp (h hzr) with hd | hx
  · exact List.mem_append_left _ hd
  · rcases List.mem_cons.mp hx with rfl | hr
    · exact absurd rfl (of_decide_eq_true hzx)
    · exact List.mem_append_right _ hr

/-- Under an upward closed `valid`, the pass needs each site that it tried and kept: its result
without the site is not valid. The pass refused the type slice without the site when it tried
it, and the result without the site is below that slice. A step of
`SliceView.descend_minimal`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sweep_kept_needed [DecidableEq α] (valid : Slice α → Bool)
    (up : ∀ {a b : Slice α}, a ≤ b → valid a = true → valid b = true) (done todo : List α) :
    ∀ y ∈ sweep valid done todo,
      y ∈ done ∨ valid ((Slice.mk (sweep valid done todo)).drop y) = false := by
  fun_induction sweep valid done todo with
  | case1 done => exact fun y hy => Or.inl hy
  | case2 done x rest _ ih => exact ih
  | case3 done x rest hc ih =>
    intro y hy
    rcases ih y hy with hd | hneeded
    · rcases List.mem_append.mp hd with hd | hx
      · exact Or.inl hd
      · obtain rfl : y = x := List.mem_singleton.mp hx
        refine Or.inr (Bool.eq_false_iff.mpr fun hv => hc (up (drop_le_of_subset ?_) hv))
        exact List.Subset.trans (sweep_sublist valid (done ++ [y]) rest).subset (by sub_tac)
    · exact Or.inr hneeded

/-! ### The pass's cost

The two lemmas of this section are the two halves of `SliceView.descend_asks`, their one
consumer. -/

/-- The pass asks one question for each site not yet tried. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sweepAsked_length (valid : Slice α → Bool) (done todo : List α) :
    (sweepAsked valid done todo).length = todo.length := by
  fun_induction sweep valid done todo with
  | case1 done => rfl
  | case2 done x rest hc ih => rw [sweepAsked, if_pos hc, List.length_cons, List.length_cons, ih]
  | case3 done x rest hc ih => rw [sweepAsked, if_neg hc, List.length_cons, List.length_cons, ih]

/-- The pass reads `valid` at the asked type slices and nowhere else: a `valid'` that agrees
with `valid` there gives the same result. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sweep_congr (valid valid' : Slice α → Bool) (done todo : List α)
    (h : ∀ c ∈ sweepAsked valid done todo, valid' c = valid c) :
    sweep valid' done todo = sweep valid done todo := by
  fun_induction sweep valid done todo with
  | case1 done => rfl
  | case2 done x rest hc ih =>
    rw [sweepAsked, if_pos hc] at h
    rw [sweep, h _ List.mem_cons_self, if_pos hc]
    exact ih fun c hcm => h c (List.mem_cons_of_mem _ hcm)
  | case3 done x rest hc ih =>
    rw [sweepAsked, if_neg hc] at h
    rw [sweep, h _ List.mem_cons_self, if_neg hc]
    exact ih fun c hcm => h c (List.mem_cons_of_mem _ hcm)

/-! ### The restart agrees with the pass

Each lemma of this section is a step of `restart_eq_sweep`, whose one consumer is
`SliceView.descend_eq_restart`. The invariant is `Failed`: each site that the pass tried and
kept still fails. Under an upward closed `valid` it holds along the pass, so a restart finds no
valid type slice among the sites that the pass has kept, and it goes on where the pass is. -/

/-- A restart that finds no valid type slice one site below stops at its list. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem restart_of_none {valid : Slice α → Bool} {l : List α}
    (h : firstDrop valid [] l = none) : restart valid l = l := by
  rw [restart]
  split
  · rfl
  · next l' h' => rw [h] at h'; exact nomatch h'

/-- A restart that finds a valid type slice one site below starts again from it. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem restart_of_some {valid : Slice α → Bool} {l l' : List α}
    (h : firstDrop valid [] l = some l') : restart valid l = restart valid l' := by
  rw [restart]
  split
  · next h' => rw [h] at h'; exact nomatch h'
  · next l'' h' => rw [h] at h'; rw [Option.some.inj h']

/-- Each site of `mid` fails: the type slice `pre ++ mid ++ rest` without it is not valid. It is
the invariant of the agreement, and no tool calls it. -/
def Failed (valid : Slice α → Bool) : List α → List α → List α → Prop
  | _, [], _ => True
  | pre, y :: mid, rest =>
    valid ⟨pre ++ (mid ++ rest)⟩ = false ∧ Failed valid (pre ++ [y]) mid rest

/-- The search for the first valid type slice passes over sites that fail. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem firstDrop_append (valid : Slice α → Bool) (pre mid rest : List α)
    (h : Failed valid pre mid rest) :
    firstDrop valid pre (mid ++ rest) = firstDrop valid (pre ++ mid) rest := by
  induction mid generalizing pre with
  | nil => rw [List.nil_append, List.append_nil]
  | cons y mid ih =>
    rw [List.cons_append, firstDrop, if_neg (Bool.eq_false_iff.mp h.1), ih (pre ++ [y]) h.2,
      List.append_assoc, List.singleton_append]

/-- The invariant grows by a site that the pass tried and kept. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem failed_snoc (valid : Slice α → Bool) (pre mid rest : List α) (x : α)
    (h : Failed valid pre mid (x :: rest)) (hx : valid ⟨pre ++ mid ++ rest⟩ = false) :
    Failed valid pre (mid ++ [x]) rest := by
  induction mid generalizing pre with
  | nil =>
    rw [List.append_nil] at hx
    exact ⟨hx, trivial⟩
  | cons y mid ih =>
    show Failed valid pre (y :: (mid ++ [x])) rest
    refine ⟨?_, ih (pre ++ [y]) h.2 ?_⟩
    · rw [List.append_assoc, List.singleton_append]
      exact h.1
    · rwa [List.append_assoc pre [y] mid, List.singleton_append]

/-- Under an upward closed `valid`, the invariant stays when the pass drops a site: a site that
failed fails at the smaller type slice too. This is the one place where the agreement uses
monotonicity. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem failed_rest (valid : Slice α → Bool)
    (up : ∀ {a b : Slice α}, a ≤ b → valid a = true → valid b = true)
    (pre mid rest : List α) (x : α) (h : Failed valid pre mid (x :: rest)) :
    Failed valid pre mid rest := by
  induction mid generalizing pre with
  | nil => trivial
  | cons y mid ih =>
    refine ⟨Bool.eq_false_iff.mpr fun hv => Bool.eq_false_iff.mp h.1 (up ?_ hv),
      ih (pre ++ [y]) h.2⟩
    show pre ++ (mid ++ rest) ⊆ pre ++ (mid ++ x :: rest)
    sub_tac

/-- The agreement at every state of the pass: with the kept sites failing, the restart from
the pass's type slice gives the pass's result. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem restart_append (valid : Slice α → Bool)
    (up : ∀ {a b : Slice α}, a ≤ b → valid a = true → valid b = true) (done todo : List α)
    (h : Failed valid [] done todo) : restart valid (done ++ todo) = sweep valid done todo := by
  fun_induction sweep valid done todo with
  | case1 done =>
    rw [List.append_nil]
    refine restart_of_none ?_
    have := firstDrop_append valid [] done [] h
    rw [List.append_nil, List.nil_append] at this
    rw [this, firstDrop]
  | case2 done x rest hc ih =>
    have hfirst : firstDrop valid [] (done ++ x :: rest) = some (done ++ rest) := by
      rw [firstDrop_append valid [] done (x :: rest) h, List.nil_append, firstDrop, if_pos hc]
    rw [restart_of_some hfirst]
    exact ih (failed_rest valid up [] done rest x h)
  | case3 done x rest hc ih =>
    have := ih (failed_snoc valid [] done rest x h
      (by rw [List.nil_append]; exact Bool.eq_false_iff.mpr hc))
    rwa [List.append_assoc, List.singleton_append] at this

/-- **The paper's descent and the one pass give one list**, for every upward closed `valid`.
The restart asks again about each site that failed, and the pass does not. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem restart_eq_sweep (valid : Slice α → Bool)
    (up : ∀ {a b : Slice α}, a ≤ b → valid a = true → valid b = true) (l : List α) :
    restart valid l = sweep valid [] l :=
  restart_append valid up [] l trivial

/-! ### The pass with free drops

A site is free at a type slice when dropping it there changes nothing. An instance that can tell
so with no call of its type map gives the test, and the pass asks nothing at a free site. The three
lemmas of this section are steps of `SliceView.descendTree_eq_descend` and of
`SliceView.descendTree_asks`. -/

/-- **The pass with free drops.** `free c x` says that the site `x` changes nothing at the type
slice `c`. Where it holds, the pass drops the site and asks nothing. Elsewhere it is `sweep`. -/
def sweepFree (valid : Slice α → Bool) (free : Slice α → α → Bool) : List α → List α → List α
  | done, [] => done
  | done, x :: rest =>
    if free ⟨done ++ x :: rest⟩ x then sweepFree valid free done rest
    else if valid ⟨done ++ rest⟩ then sweepFree valid free done rest
    else sweepFree valid free (done ++ [x]) rest

/-- The questions of the pass with free drops, in the order asked. It follows the pass's own
recursion, and `sweepFree_congr` makes it the list of the questions. -/
def sweepFreeAsked (valid : Slice α → Bool) (free : Slice α → α → Bool) :
    List α → List α → List (Slice α)
  | _, [] => []
  | done, x :: rest =>
    if free ⟨done ++ x :: rest⟩ x then sweepFreeAsked valid free done rest
    else ⟨done ++ rest⟩ ::
      (if valid ⟨done ++ rest⟩ then sweepFreeAsked valid free done rest
        else sweepFreeAsked valid free (done ++ [x]) rest)

/-- The test of a tree of sites: the site has a parent, and the type slice does not keep the
parent. The omission at the parent has omitted the site already. -/
def parentOmitted [DecidableEq α] (parent : α → Option α) (c : Slice α) (x : α) : Bool :=
  match parent x with
  | some p => !decide (p ∈ c.kept)
  | none => false

/-- From a valid start, the pass with free drops gives the pass's list. The test must be sound
against `valid`: a valid type slice stays valid without a site that the test calls free. Then the
pass drops each free site too, after one question. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sweepFree_eq_sweep [DecidableEq α] (valid : Slice α → Bool) (free : Slice α → α → Bool)
    (up : ∀ {a b : Slice α}, a ≤ b → valid a = true → valid b = true)
    (sound : ∀ (c : Slice α) (x : α), free c x = true → valid c = true → valid (c.drop x) = true)
    (done todo : List α) (h : valid ⟨done ++ todo⟩ = true) :
    sweepFree valid free done todo = sweep valid done todo := by
  fun_induction sweepFree valid free done todo with
  | case1 done => rfl
  | case2 done x rest hfree ih =>
    have hc : valid ⟨done ++ rest⟩ = true :=
      up (drop_le_of_subset (List.Subset.refl _)) (sound _ x hfree h)
    rw [sweep, if_pos hc]
    exact ih hc
  | case3 done x rest _ hc ih =>
    rw [sweep, if_pos hc]
    exact ih hc
  | case4 done x rest _ hc ih =>
    rw [sweep, if_neg hc]
    exact ih (by rwa [List.append_assoc, List.singleton_append])

/-- Under the same premises, the questions of the pass with free drops are a sub-list of the
pass's questions: the same questions, without the ones at free sites. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sweepFreeAsked_sublist [DecidableEq α] (valid : Slice α → Bool)
    (free : Slice α → α → Bool)
    (up : ∀ {a b : Slice α}, a ≤ b → valid a = true → valid b = true)
    (sound : ∀ (c : Slice α) (x : α), free c x = true → valid c = true → valid (c.drop x) = true)
    (done todo : List α) (h : valid ⟨done ++ todo⟩ = true) :
    (sweepFreeAsked valid free done todo).Sublist (sweepAsked valid done todo) := by
  fun_induction sweepFree valid free done todo with
  | case1 done => exact List.Sublist.refl _
  | case2 done x rest hfree ih =>
    have hc : valid ⟨done ++ rest⟩ = true :=
      up (drop_le_of_subset (List.Subset.refl _)) (sound _ x hfree h)
    rw [sweepFreeAsked, if_pos hfree, sweepAsked, if_pos hc]
    exact (ih hc).cons _
  | case3 done x rest hfree hc ih =>
    rw [sweepFreeAsked, if_neg hfree, if_pos hc, sweepAsked, if_pos hc]
    exact (ih hc).cons_cons _
  | case4 done x rest hfree hc ih =>
    rw [sweepFreeAsked, if_neg hfree, if_neg hc, sweepAsked, if_neg hc]
    exact (ih (by rwa [List.append_assoc, List.singleton_append])).cons_cons _

/-- The pass with free drops reads `valid` at its asked type slices and nowhere else. It needs
no premise. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem sweepFree_congr (valid valid' : Slice α → Bool) (free : Slice α → α → Bool)
    (done todo : List α) (h : ∀ c ∈ sweepFreeAsked valid free done todo, valid' c = valid c) :
    sweepFree valid' free done todo = sweepFree valid free done todo := by
  fun_induction sweepFree valid free done todo with
  | case1 done => rfl
  | case2 done x rest hfree ih =>
    rw [sweepFreeAsked, if_pos hfree] at h
    rw [sweepFree, if_pos hfree]
    exact ih h
  | case3 done x rest hfree hc ih =>
    rw [sweepFreeAsked, if_neg hfree, if_pos hc] at h
    rw [sweepFree, if_neg hfree, h _ List.mem_cons_self, if_pos hc]
    exact ih fun c hcm => h c (List.mem_cons_of_mem _ hcm)
  | case4 done x rest hfree hc ih =>
    rw [sweepFreeAsked, if_neg hfree, if_neg hc] at h
    rw [sweepFree, if_neg hfree, h _ List.mem_cons_self, if_neg hc]
    exact ih fun c hcm => h c (List.mem_cons_of_mem _ hcm)

end Slice

/-- **A slice view of one program**: the type of each of its type slices. An instance owes one
fact, `mono`, and nothing about its carrier. The direction: a slice that keeps less has a type at
or below.
For the checker `mono` is graduality (the paper's Definition 2.1, p. 5). The order on the types
is the one that `T` carries as `LE`. -/
structure SliceView (α : Type u) (T : Type v) [LE T] where
  /-- the type of a type slice -/
  typeOf : Slice α → T
  /-- a type slice that keeps less has a type at or below -/
  mono : ∀ {a b : Slice α}, a ≤ b → typeOf a ≤ typeOf b

-- The projection of the proof field is a theorem of the environment. It is placed by its
-- concept and is no node of the requirement: it is what an instance owes, not a result.
attribute [semantics "subtyping-algebra"] SliceView.mono

namespace SliceView

variable {α : Type u} {T : Type v} [LE T]

/-! ## Validity and minimality -/

/-- A query is **valid** for a type slice when the slice's type is at or above the query: the
paper's condition `υ ⊑ φ` (Definition 4.1, p. 9). It is not an equality: an exact slice need not
exist (the paper's Counterexample 4.2, p. 9; `Test/Program/SliceLattice.lean`). -/
def Valid (v : SliceView α T) (q : T) (s : Slice α) : Prop := q ≤ v.typeOf s

/-- Validity is decided, where the order on the types is. -/
instance instDecidableValid [DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α) :
    Decidable (v.Valid q s) :=
  inferInstanceAs (Decidable (q ≤ v.typeOf s))

/-- A type slice is **minimal** for a query when it is valid, and each valid slice below it
keeps the same sites. It is the paper's Definitions 4.3 and 4.4 (p. 9), with "keeps the same
sites" where the paper says "equal". A query can have several minimal slices, and none is the
least. -/
def Minimal (v : SliceView α T) (q : T) (m : Slice α) : Prop :=
  v.Valid q m ∧ ∀ j : Slice α, j ≤ m → v.Valid q j → m ≤ j

/-- **The one-step test of minimality**: valid, and not valid without any one kept site. It
asks the type map once, and once more for each kept site. `isMinimal_iff` is its law. -/
def isMinimal [DecidableEq α] [DecidableLE T] (v : SliceView α T) (q : T) (m : Slice α) : Bool :=
  decide (v.Valid q m) && m.kept.all fun x => !decide (v.Valid q (m.drop x))

/-! ## The executable descent -/

/-- **The descent**: from a type slice down to a minimal slice below it, by one pass over its
sites (`Slice.sweep`). Its choice is fixed by the order of `s.kept`: it tries each site once, in
that order, and drops a site exactly when the slice without it is still valid. So two runs give
one answer. It returns one minimal slice, not the smallest: a minimum-size slice is NP-hard in
the paper's calculus (section 10, p. 22). Its law is `descend_minimal`, and its cost
`descend_asks`. -/
def descend [DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α) : Slice α :=
  ⟨Slice.sweep (fun c => decide (v.Valid q c)) [] s.kept⟩

/-- The type slices whose validity the descent asked, in the order asked. -/
def asked [DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α) : List (Slice α) :=
  Slice.sweepAsked (fun c => decide (v.Valid q c)) [] s.kept

/-- **The descent over a tree of sites.** `parent x` is the site above `x`, where one is. The
descent is `descend`, and it asks nothing about a site whose parent the type slice does not keep
(`Slice.sweepFree` with `Slice.parentOmitted`). With the parents first in `s.kept`, a dropped
site takes its sub-tree with it, for one question. Its law is `descendTree_eq_descend`, under the
instance's no-op premise. -/
def descendTree [DecidableEq α] [DecidableLE T] (v : SliceView α T) (parent : α → Option α)
    (q : T) (s : Slice α) : Slice α :=
  ⟨Slice.sweepFree (fun c => decide (v.Valid q c)) (Slice.parentOmitted parent) [] s.kept⟩

/-- The type slices whose validity the descent over a tree asked, in the order asked. -/
def askedTree [DecidableEq α] [DecidableLE T] (v : SliceView α T) (parent : α → Option α)
    (q : T) (s : Slice α) : List (Slice α) :=
  Slice.sweepFreeAsked (fun c => decide (v.Valid q c)) (Slice.parentOmitted parent) [] s.kept

/-! ## Every minimal type slice, by search -/

/-- Every minimal type slice below `s`, one for each sub-list of its sites that passes the
one-step test. It is a search of `2 ^ n` slices for `n` sites. -/
def minimals [DecidableEq α] [DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α) :
    List (Slice α) :=
  s.subslices.filter (v.isMinimal q)

/-- **The contribution slice** (the paper's section 4.6, p. 12): the sites of `s` that some
minimal type slice below `s` keeps. It is the join of the minimal slices (`contribution_lub`). It
is computed by the search of `minimals`, and no better bound is stated. -/
def contribution [DecidableEq α] [DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α) :
    Slice α :=
  ⟨s.kept.filter fun x => (v.minimals q s).any fun m => decide (x ∈ m.kept)⟩

/-! ## A slice view from a type map of what is omitted -/

/-- **A slice view from a mask.** `f F` is the type of the program with the sites `F` omitted.
The premise is graduality in the mask's direction: omitting more gives a type at or below. It is
owed for the sites of `sites` only, because a real instance can omit only some addresses. The
view's type of a type slice is `f` at its mask: the sites that the slice does not keep. -/
def ofOmitted [DecidableEq α] (sites : List α) (f : List α → T)
    (anti : ∀ {F G : List α}, F ⊆ G → G ⊆ sites → f G ≤ f F) : SliceView α T where
  typeOf s := f (s.omitted sites)
  mono h := anti (Slice.omitted_anti sites h) (Slice.omitted_subset sites _)

/-! ## The statements

Each of the fifteen statements of the brief began as a planned goal, and its proof replaced it in
place. The three statements of the descent over a tree landed with their proofs:
`descendTree_eq_descend`, `descendTree_minimal` and `descendTree_asks`, with their step
`parentOmitted_sound`. The last statement, `lattice_minimal`, is the claim's four parts as one. -/

/-- **Validity is upward closed**: a type slice that keeps more is valid for the same query. The
paper has it by graduality (Theorem 3.5, p. 8) for its calculus. Here it holds for every
monotone view. It establishes no slice that is valid. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem valid_up [Std.IsPreorder T] (v : SliceView α T) {q : T} {a b : Slice α}
    (h : v.Valid q a) (hab : a ≤ b) : v.Valid q b :=
  Std.le_trans h (v.mono hab)

/-- **Minimality is decided one site below.** A valid type slice is minimal exactly when no slice
one site below it is valid. It is the last step of the paper's brute-force algorithm: "if none
of the slices satisfy the query, then a minimal slice has been found, by graduality" (pp. 9
and 10). It uses the view's monotonicity. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem minimal_iff_drop [DecidableEq α] [Std.IsPreorder T] (v : SliceView α T) (q : T)
    (m : Slice α) : v.Minimal q m ↔ v.Valid q m ∧ ∀ x ∈ m.kept, ¬ v.Valid q (m.drop x) := by
  constructor
  · exact fun h => ⟨h.1, fun x hx hv => m.not_mem_drop x (h.2 (m.drop x) (m.drop_le x) hv hx)⟩
  · exact fun h => ⟨h.1, fun j hj hv x hx => Decidable.byContradiction fun hxj =>
      h.2 x hx (v.valid_up hv (Slice.le_drop hj hxj))⟩

/-- The one-step test decides minimality: the executable form of `minimal_iff_drop`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem isMinimal_iff [DecidableEq α] [Std.IsPreorder T] [DecidableLE T] (v : SliceView α T)
    (q : T) (m : Slice α) : v.isMinimal q m = true ↔ v.Minimal q m := by
  rw [minimal_iff_drop, isMinimal, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
  exact and_congr_right fun _ => forall₂_congr fun _ _ => by
    rw [Bool.not_eq_true', decide_eq_false_iff_not]

/-- Minimality is decided, by the one-step test. So `decide` proves the minimality of one type
slice of a finite instance whose type map the kernel can run. -/
instance instDecidableMinimal [DecidableEq α] [Std.IsPreorder T] [DecidableLE T]
    (v : SliceView α T) (q : T) (m : Slice α) : Decidable (v.Minimal q m) :=
  decidable_of_iff _ (v.isMinimal_iff q m)

/-- **A minimal type slice needs each site that it keeps**: its type without the site is not at
or above its type. A step of `Minimal.keeps_above`, and a test that one kept site is no dead
weight. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Minimal.needs [DecidableEq α] [Std.IsPreorder T] {v : SliceView α T} {q : T}
    {m : Slice α} (h : v.Minimal q m) {x : α} (hx : x ∈ m.kept) :
    ¬ v.typeOf m ≤ v.typeOf (m.drop x) :=
  fun hle => ((v.minimal_iff_drop q m).mp h).2 x hx (Std.le_trans h.1 hle)

/-- **A minimal type slice is a highlighted tree**: it keeps each site above a site that it
keeps. `above y x` says that the site `y` is above the site `x`: for the addresses of a tree, an
ancestor. The premise is the instance's: omitting a site changes nothing when a site above it
is omitted already. A type map that omits a whole sub-tree at an address has it. The premise is
asked at the slice `m` only. The statement gives no such closure for a slice that is not
minimal. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Minimal.keeps_above [DecidableEq α] [Std.IsPreorder T] {v : SliceView α T} {q : T}
    {m : Slice α} (h : v.Minimal q m) {above : α → α → Prop}
    (noop : ∀ {x y : α}, above y x → y ∉ m.kept → v.typeOf m ≤ v.typeOf (m.drop x))
    {x y : α} (hx : x ∈ m.kept) (hyx : above y x) : y ∈ m.kept :=
  Decidable.byContradiction fun hy => h.needs hx (noop hyx hy)

/-- The descent keeps sites of its start only, in the start's order, each as often as the start
does. It holds for every start, valid or not. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descend_sublist [DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α) :
    (v.descend q s).kept.Sublist s.kept :=
  Slice.sweep_sublist _ [] s.kept

/-- The descent's type slice is below its start: it keeps no more. A corollary of
`descend_sublist`, and a step of `exists_minimal_below`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descend_le [DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α) :
    v.descend q s ≤ s :=
  (v.descend_sublist q s).subset

/-- The descent of a valid type slice is valid. It needs no monotonicity: the pass moves to
accepted slices only. A step of `descend_minimal`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descend_valid [DecidableLE T] (v : SliceView α T) {q : T} {s : Slice α}
    (h : v.Valid q s) : v.Valid q (v.descend q s) :=
  of_decide_eq_true
    (Slice.sweep_valid (fun c => decide (v.Valid q c)) [] s.kept (decide_eq_true h))

/-- The Boolean that the descent asks is upward closed: `valid_up`, read on the decision. A
step of `descend_minimal` and of `descend_eq_restart`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem decide_valid_up [Std.IsPreorder T] [DecidableLE T] (v : SliceView α T) (q : T)
    {a b : Slice α} (hab : a ≤ b) (ha : decide (v.Valid q a) = true) :
    decide (v.Valid q b) = true :=
  decide_eq_true (v.valid_up (of_decide_eq_true ha) hab)

/-- **The descent ends at a minimal type slice** (the paper's brute-force algorithm, pp. 9 and
10).
From a valid slice it returns a minimal slice, and `descend_sublist` puts that slice below the
start. It returns one minimal slice, and not a least or a smallest one. Without the premise the
start is not valid, and then no slice below it is (`valid_up`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descend_minimal [DecidableEq α] [Std.IsPreorder T] [DecidableLE T] (v : SliceView α T)
    {q : T} {s : Slice α} (h : v.Valid q s) : v.Minimal q (v.descend q s) := by
  refine (v.minimal_iff_drop q _).mpr ⟨v.descend_valid h, fun x hx hv => ?_⟩
  rcases Slice.sweep_kept_needed (fun c => decide (v.Valid q c)) (v.decide_valid_up q) []
    s.kept x hx with hnil | hneeded
  · exact List.not_mem_nil hnil
  · exact of_decide_eq_false hneeded hv

/-- **A minimal valid type slice exists below each valid slice**: the paper's Theorem 4.5
(p. 9).
The paper's proof enumerates the slices below and does not use monotonicity. This proof is the
descent, which uses it. The statement names two decisions, of the order on the types and of
equal sites, because the gate admits no classical axiom. It leaves out a map that is not
monotone. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem exists_minimal_below [DecidableEq α] [Std.IsPreorder T] [DecidableLE T]
    (v : SliceView α T) {q : T} {s : Slice α} (h : v.Valid q s) :
    ∃ m : Slice α, m ≤ s ∧ v.Minimal q m :=
  ⟨v.descend q s, v.descend_le q s, v.descend_minimal h⟩

/-- A type slice that is valid for a query is valid for each query at or below it: a refined
query keeps the valid slices of the wider one. A step of `minimal_refine`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem valid_refine [Std.IsPreorder T] (v : SliceView α T) {q q' : T} {s : Slice α}
    (hq : q' ≤ q) (h : v.Valid q s) : v.Valid q' s :=
  Std.le_trans hq h

/-- **A refined query has a minimal type slice below a minimal slice of the wider query**: the
paper's Theorem 4.6 (p. 10). The witness is the descent from `m₂` for the query `q₁`. Nothing
holds upwards: a minimal slice of `q₁` need not lie below a minimal slice of `q₂` (the paper,
p. 11; `Test/Program/SliceLattice.lean`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem minimal_refine [DecidableEq α] [Std.IsPreorder T] [DecidableLE T]
    (v : SliceView α T) {q₁ q₂ : T} {m₂ : Slice α} (hq : q₁ ≤ q₂) (h : v.Minimal q₂ m₂) :
    ∃ m₁ : Slice α, m₁ ≤ m₂ ∧ v.Minimal q₁ m₁ :=
  v.exists_minimal_below (v.valid_refine hq h.1)

/-- **The one pass is the paper's descent.** The paper's brute force takes the first valid type
slice one site below and starts again (pp. 9 and 10): `Slice.restart`. Monotonicity is what
makes one pass enough: a site that failed once fails at each later slice, so no start needs to
ask about it again. A finite probe counts the questions on one input of `n` sites: the restart
asks 120 at `n = 20` and 255 at `n = 30`, and the pass 20 and 30
(`Test/Program/SliceLattice.lean`). The equality rests on monotonicity, and where a type map is
not monotone the two descents differ (the same file). On programs of the tree, under an
omission that is not monotone, a finite probe of seat CENSUS on 2026-10-06 found the pass in
program order at a slice that is not minimal in 3 of 50 cases, and the restart at a minimal slice
in all 50. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descend_eq_restart [Std.IsPreorder T] [DecidableLE T] (v : SliceView α T) (q : T)
    (s : Slice α) :
    v.descend q s = ⟨Slice.restart (fun c => decide (v.Valid q c)) s.kept⟩ :=
  congrArg Slice.mk (Slice.restart_eq_sweep _ (v.decide_valid_up q) s.kept).symm

/-- **The descent's cost: one question for each site of its start.** The first part counts the
type slices that the descent asked about. The second part says that the descent read the validity at
those slices and nowhere else: a pass over any `valid'` that agrees with the view there returns
the same sites. So the count is of the function's questions, with no counter beside it. Each
question is one call of the type map and one comparison. It is the paper's bound `O(n × T)`
(p. 10), for `n` sites and a type map of cost `T`. It states no bound below `n`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descend_asks [DecidableLE T] (v : SliceView α T) (q : T) (s : Slice α) :
    (v.asked q s).length = s.kept.length ∧
      ∀ valid' : Slice α → Bool, (∀ c ∈ v.asked q s, valid' c = decide (v.Valid q c)) →
        Slice.sweep valid' [] s.kept = (v.descend q s).kept :=
  ⟨Slice.sweepAsked_length _ [] s.kept, fun valid' h => Slice.sweep_congr _ valid' [] s.kept h⟩

/-- The tree's test is sound against a view's validity, under the no-op premise: where the
parent is omitted, a valid type slice stays valid without the site. A step of
`descendTree_eq_descend` and of `descendTree_asks`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem parentOmitted_sound [DecidableEq α] [Std.IsPreorder T] [DecidableLE T] (v : SliceView α T)
    (parent : α → Option α)
    (noop : ∀ (c : Slice α) {x y : α}, parent x = some y → y ∉ c.kept →
      v.typeOf c ≤ v.typeOf (c.drop x))
    (q : T) (c : Slice α) (x : α) (hfree : Slice.parentOmitted parent c x = true)
    (hc : decide (v.Valid q c) = true) : decide (v.Valid q (c.drop x)) = true := by
  unfold Slice.parentOmitted at hfree
  split at hfree
  · next p hp =>
    exact decide_eq_true (Std.le_trans (of_decide_eq_true hc)
      (noop c hp (of_decide_eq_false (Eq.mp (Bool.not_eq_true' _) hfree))))
  · exact nomatch hfree

/-- **The descent over a tree gives the descent's type slice.** The premise is the instance's
no-op, the one of `Minimal.keeps_above`, asked at every slice: omitting a site changes nothing
when its parent is omitted already. A type map that omits a whole sub-tree at an address has it.
From a
valid start the two descents give one slice. The statement says nothing for a start that is not
valid, and it gives no order of the sites: with a child before its parent the descent asks about
the child. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descendTree_eq_descend [DecidableEq α] [Std.IsPreorder T] [DecidableLE T]
    (v : SliceView α T) (parent : α → Option α)
    (noop : ∀ (c : Slice α) {x y : α}, parent x = some y → y ∉ c.kept →
      v.typeOf c ≤ v.typeOf (c.drop x))
    {q : T} {s : Slice α} (h : v.Valid q s) : v.descendTree parent q s = v.descend q s :=
  congrArg Slice.mk (Slice.sweepFree_eq_sweep _ _ (v.decide_valid_up q)
    (v.parentOmitted_sound parent noop q) [] s.kept (decide_eq_true h))

/-- The descent over a tree ends at a minimal type slice: `descend_minimal`, through
`descendTree_eq_descend`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descendTree_minimal [DecidableEq α] [Std.IsPreorder T] [DecidableLE T]
    (v : SliceView α T) (parent : α → Option α)
    (noop : ∀ (c : Slice α) {x y : α}, parent x = some y → y ∉ c.kept →
      v.typeOf c ≤ v.typeOf (c.drop x))
    {q : T} {s : Slice α} (h : v.Valid q s) : v.Minimal q (v.descendTree parent q s) :=
  v.descendTree_eq_descend parent noop h ▸ v.descend_minimal h

/-- **The descent over a tree asks no more.** Its questions are a sub-list of the descent's
questions: the same ones, without those at a site under an omitted parent. And its result
depends on the validity at its own questions only. A finite probe on the toy: 8 questions against
10 on the page 18 program, and 1 against 4 where the root is omitted
(`Test/Program/SliceLattice.lean`). It states no count below the sub-list. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem descendTree_asks [DecidableEq α] [Std.IsPreorder T] [DecidableLE T]
    (v : SliceView α T) (parent : α → Option α)
    (noop : ∀ (c : Slice α) {x y : α}, parent x = some y → y ∉ c.kept →
      v.typeOf c ≤ v.typeOf (c.drop x))
    {q : T} {s : Slice α} (h : v.Valid q s) :
    (v.askedTree parent q s).Sublist (v.asked q s) ∧
      ∀ valid' : Slice α → Bool,
        (∀ c ∈ v.askedTree parent q s, valid' c = decide (v.Valid q c)) →
          Slice.sweepFree valid' (Slice.parentOmitted parent) [] s.kept =
            (v.descendTree parent q s).kept :=
  ⟨Slice.sweepFreeAsked_sublist _ _ (v.decide_valid_up q) (v.parentOmitted_sound parent noop q)
      [] s.kept (decide_eq_true h),
    fun valid' hv => Slice.sweepFree_congr _ valid' _ [] s.kept hv⟩

/-- **The join of two valid type slices is valid for the join of their queries**: the paper's
Theorem 4.7 (p. 12). The type side needs a join here, and in no other statement: `max` with
`Std.LawfulOrderSup`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem valid_max [Std.IsPreorder T] [Max T] [Std.LawfulOrderSup T] (v : SliceView α T)
    {q₁ q₂ : T} {a b : Slice α} (ha : v.Valid q₁ a) (hb : v.Valid q₂ b) :
    v.Valid (max q₁ q₂) (max a b) :=
  Std.max_le_iff.mpr ⟨v.valid_up ha Std.left_le_max, v.valid_up hb Std.right_le_max⟩

/-- A type slice that keeps the same sites as a minimal slice is minimal. A step of
`minimals_complete`, its one consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Minimal.of_same_sites [Std.IsPreorder T] {v : SliceView α T} {q : T} {m m' : Slice α}
    (h : v.Minimal q m) (h₁ : m ≤ m') (h₂ : m' ≤ m) : v.Minimal q m' :=
  ⟨v.valid_up h.1 h₁, fun j hj hv => Std.le_trans h₂ (h.2 j (Std.le_trans hj h₂) hv)⟩

/-- Each type slice that the search lists is minimal and below the start. A step of
`contribution_lub`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem minimals_sound [DecidableEq α] [Std.IsPreorder T] [DecidableLE T] (v : SliceView α T)
    {q : T} {s m : Slice α} (h : m ∈ v.minimals q s) : m ≤ s ∧ v.Minimal q m :=
  ⟨Slice.le_of_mem_subslices (List.mem_filter.mp h).1,
    (v.isMinimal_iff q m).mp (List.mem_filter.mp h).2⟩

/-- The search misses no minimal type slice below the start: each one keeps the same sites as a
listed one. A step of `contribution_lub`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem minimals_complete [DecidableEq α] [Std.IsPreorder T] [DecidableLE T] (v : SliceView α T)
    {q : T} {s m : Slice α} (hs : m ≤ s) (h : v.Minimal q m) :
    ∃ m' ∈ v.minimals q s, m' ≤ m ∧ m ≤ m' := by
  obtain ⟨m', hm', h₁, h₂⟩ := Slice.exists_mem_subslices hs
  exact ⟨m', List.mem_filter.mpr ⟨hm', (v.isMinimal_iff q m').mpr (h.of_same_sites h₂ h₁)⟩,
    h₁, h₂⟩

/-- **The contribution slice is the join of the minimal type slices**: it is below a slice
exactly when each minimal slice below `s` is. The paper calls it "a least upper bound of actual
minimal slices" (p. 12). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem contribution_lub [DecidableEq α] [Std.IsPreorder T] [DecidableLE T]
    (v : SliceView α T) (q : T) (s u : Slice α) :
    v.contribution q s ≤ u ↔ ∀ m : Slice α, m ≤ s → v.Minimal q m → m ≤ u := by
  constructor
  · intro h m hs hm x hx
    obtain ⟨m', hm', _, h₂⟩ := v.minimals_complete hs hm
    exact h (List.mem_filter.mpr
      ⟨hs hx, List.any_eq_true.mpr ⟨m', hm', decide_eq_true (h₂ hx)⟩⟩)
  · intro h x hx
    obtain ⟨m, hm, hxm⟩ := List.any_eq_true.mp (List.mem_filter.mp hx).2
    exact h m (v.minimals_sound hm).1 (v.minimals_sound hm).2 (of_decide_eq_true hxm)

/-- The contribution slice is a type slice below its start: it keeps sites of the start only, in
the start's order. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem contribution_le [DecidableEq α] [DecidableLE T] (v : SliceView α T) (q : T)
    (s : Slice α) : v.contribution q s ≤ s :=
  fun _ hx => (List.mem_filter.mp hx).1

/-- **The contribution slice is valid** when its start is: the join of all minimal type slices
is a slice for the query (the paper's section 4.6, p. 12). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem contribution_valid [DecidableEq α] [Std.IsPreorder T] [DecidableLE T]
    (v : SliceView α T) {q : T} {s : Slice α} (h : v.Valid q s) :
    v.Valid q (v.contribution q s) :=
  v.valid_up (v.descend_valid h)
    ((v.contribution_lub q s _).mp (Std.le_refl _) _ (v.descend_le q s) (v.descend_minimal h))

/-- **At the full type slice nothing is omitted**: the slice view of a mask gives the type map
at the empty mask. It is the generic half of the plan's `slice-conservative`. It does not say
that `f []` is the checker's answer: that is the instance's. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem ofOmitted_full [DecidableEq α] (sites : List α) (f : List α → T)
    (anti : ∀ {F G : List α}, F ⊆ G → G ⊆ sites → f G ≤ f F) :
    (ofOmitted sites f anti).typeOf ⟨sites⟩ = f [] :=
  congrArg f (Slice.omitted_full sites)

/-- **The claim `slice-lattice-minimal`, as one statement**: its four parts, for one monotone
view. A minimal valid type slice exists below each valid slice (Theorem 4.5). The descent ends at
one, below its start. A refined query has a minimal slice below a minimal slice of the wider query
(Theorem 4.6). The join of two valid slices is valid for the join of their queries (Theorem 4.7).
It is the pointer that the claim's row needs, and it adds nothing to its four parts. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem lattice_minimal [DecidableEq α] [Std.IsPreorder T] [DecidableLE T] [Max T]
    [Std.LawfulOrderSup T] (v : SliceView α T) :
    (∀ {q : T} {s : Slice α}, v.Valid q s → ∃ m : Slice α, m ≤ s ∧ v.Minimal q m) ∧
    (∀ {q : T} {s : Slice α}, v.Valid q s →
      v.descend q s ≤ s ∧ v.Minimal q (v.descend q s)) ∧
    (∀ {q₁ q₂ : T} {m₂ : Slice α}, q₁ ≤ q₂ → v.Minimal q₂ m₂ →
      ∃ m₁ : Slice α, m₁ ≤ m₂ ∧ v.Minimal q₁ m₁) ∧
    (∀ {q₁ q₂ : T} {a b : Slice α}, v.Valid q₁ a → v.Valid q₂ b →
      v.Valid (max q₁ q₂) (max a b)) :=
  ⟨v.exists_minimal_below, fun h => ⟨v.descend_le _ _, v.descend_minimal h⟩, v.minimal_refine,
    v.valid_max⟩

end SliceView

end Effect4

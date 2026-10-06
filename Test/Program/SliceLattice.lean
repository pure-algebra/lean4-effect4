import Effect4.Laws.Slice.Lattice
import ProofGraph.Plan

/-!
# The generic theory of slices: its pinned outputs, the paper's examples and the red controls

The statements and their proofs are in `src/Effect4/Laws/Slice/Lattice.lean`. This battery pins
each statement's axioms and its plan status. It then holds one instance, a toy: a term with holes
over types with a gap, with sliced assumptions. The toy owes one fact, its monotonicity
(`synth_mono`). For the tree's two statements it owes a second one: a site under a folded parent
changes nothing (`toy_noop`). The toy renders the examples of Carroll, Madhavapeddy and Omar
2026, *Bidirectional Type Slicing* (each page is of the vendored PDF,
`vendor/papers/program-graphs/bidirectional-type-slicing-2607.12197v1.pdf`):

- page 18: the four incomparable minimal slices of `if true then x else y`;
- page 23: the two slices whose meet loses the type, so no least slice exists;
- page 9: Counterexample 4.2, a query with no exact slice;
- page 11: a minimal slice of a refined query that lies below no minimal slice of the wider one.

It also holds the descent over the tree, the toy as the view of a mask, and the count of the
restart's questions against the pass's.

The red controls:

- a validity that is not upward closed: the pass stops at a slice that is not minimal, and the
  restart gives another slice;
- a query above the full type, which no slice serves;
- a slice that keeps a site under a folded one, which is not minimal;
- a parent function that is not the fold's: the descent over the tree returns a slice that is
  not valid.

Evidence. Each theorem here is about the toy only. `synth_mono`, `toy_noop` and their
corollaries hold for every toy program. Each other theorem is the kernel's evaluation of a
decision on one program (`decide`). A `#guard` is a finite check: tested, not proved. No
statement of this battery is a law of the module.
-/

namespace Test.Program.SliceLattice
open Effect4

/-! ## The statements: their axioms and their plan status -/

/-- info: 'Effect4.SliceView.valid_up' does not depend on any axioms -/
#guard_msgs in
#print axioms SliceView.valid_up

/-- info: 'Effect4.SliceView.minimal_iff_drop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SliceView.minimal_iff_drop

/-- info: 'Effect4.SliceView.isMinimal_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.isMinimal_iff

/-- info: 'Effect4.SliceView.Minimal.needs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SliceView.Minimal.needs

/-- info: 'Effect4.SliceView.Minimal.keeps_above' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SliceView.Minimal.keeps_above

/-- info: 'Effect4.SliceView.descend_sublist' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SliceView.descend_sublist

/-- info: 'Effect4.SliceView.descend_minimal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.descend_minimal

/-- info: 'Effect4.SliceView.exists_minimal_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.exists_minimal_below

/-- info: 'Effect4.SliceView.minimal_refine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.minimal_refine

/-- info: 'Effect4.SliceView.descend_eq_restart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.descend_eq_restart

/-- info: 'Effect4.SliceView.descend_asks' does not depend on any axioms -/
#guard_msgs in
#print axioms SliceView.descend_asks

/-- info: 'Effect4.SliceView.valid_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.valid_max

/-- info: 'Effect4.SliceView.contribution_lub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.contribution_lub

/-- info: 'Effect4.SliceView.contribution_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.contribution_valid

/-- info: 'Effect4.SliceView.ofFolded_full' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SliceView.ofFolded_full

/-- info: 'Effect4.SliceView.descendTree_eq_descend' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SliceView.descendTree_eq_descend

/-- info: 'Effect4.SliceView.descendTree_minimal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.descendTree_minimal

/-- info: 'Effect4.SliceView.descendTree_asks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SliceView.descendTree_asks

/-- info: 'Effect4.SliceView.lattice_minimal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SliceView.lattice_minimal

-- The standing is derived from each proof. The counts are of this battery's tree, which holds no
-- step of a proof: the steps are in the law module.
/--
info: Effect4.SliceView.valid_up: proved; nearest []; 0 lemmas, 0 definitions
Effect4.SliceView.minimal_iff_drop: proved; nearest [Effect4.SliceView.valid_up]; 0 lemmas, 0 definitions
Effect4.SliceView.isMinimal_iff: proved; nearest [Effect4.SliceView.minimal_iff_drop]; 0 lemmas, 0 definitions
Effect4.SliceView.Minimal.needs: proved; nearest [Effect4.SliceView.minimal_iff_drop]; 0 lemmas, 0 definitions
Effect4.SliceView.Minimal.keeps_above: proved; nearest [Effect4.SliceView.Minimal.needs]; 0 lemmas, 0 definitions
Effect4.SliceView.descend_sublist: proved; nearest []; 0 lemmas, 0 definitions
Effect4.SliceView.descend_minimal: proved; nearest [Effect4.SliceView.minimal_iff_drop]; 0 lemmas, 0 definitions
Effect4.SliceView.exists_minimal_below: proved; nearest [Effect4.SliceView.descend_minimal]; 0 lemmas, 0 definitions
Effect4.SliceView.minimal_refine: proved; nearest [Effect4.SliceView.exists_minimal_below]; 0 lemmas, 0 definitions
Effect4.SliceView.descend_eq_restart: proved; nearest []; 0 lemmas, 0 definitions
Effect4.SliceView.descend_asks: proved; nearest []; 0 lemmas, 0 definitions
Effect4.SliceView.valid_max: proved; nearest [Effect4.SliceView.valid_up]; 0 lemmas, 0 definitions
Effect4.SliceView.contribution_lub: proved; nearest []; 0 lemmas, 0 definitions
Effect4.SliceView.contribution_valid: proved; nearest [Effect4.SliceView.descend_minimal, Effect4.SliceView.contribution_lub, Effect4.SliceView.valid_up]; 0 lemmas, 0 definitions
Effect4.SliceView.ofFolded_full: proved; nearest []; 0 lemmas, 0 definitions
Effect4.SliceView.descendTree_eq_descend: proved; nearest []; 0 lemmas, 0 definitions
Effect4.SliceView.descendTree_minimal: proved; nearest [Effect4.SliceView.descendTree_eq_descend, Effect4.SliceView.descend_minimal]; 0 lemmas, 0 definitions
Effect4.SliceView.descendTree_asks: proved; nearest []; 0 lemmas, 0 definitions
Effect4.SliceView.lattice_minimal: proved; nearest [Effect4.SliceView.valid_max, Effect4.SliceView.minimal_refine, Effect4.SliceView.descend_minimal, Effect4.SliceView.exists_minimal_below]; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status SliceView.valid_up SliceView.minimal_iff_drop SliceView.isMinimal_iff
  SliceView.Minimal.needs SliceView.Minimal.keeps_above SliceView.descend_sublist
  SliceView.descend_minimal SliceView.exists_minimal_below SliceView.minimal_refine
  SliceView.descend_eq_restart SliceView.descend_asks SliceView.valid_max
  SliceView.contribution_lub SliceView.contribution_valid SliceView.ofFolded_full
  SliceView.descendTree_eq_descend SliceView.descendTree_minimal SliceView.descendTree_asks
  SliceView.lattice_minimal

/-! ## The toy: a term with holes, over types with a gap -/

/-- A type of the toy calculus, with the paper's gap `□`. -/
inductive ToyTy where
  | gap
  | one
  | arrow (a b : ToyTy)
  | prod (a b : ToyTy)

/-- A position of a type: the path of child indices from its root. -/
abbrev TyPos := List Nat

/-- A term of the toy calculus: a hole, a constant of type `1`, a variable, a pair and a
conditional. -/
inductive ToyTm where
  | hole
  | lit
  | var (x : Nat)
  | pair (a b : ToyTm)
  | ite (c t e : ToyTm)

/-- A site of a toy program: a position of an assumption's type, or an address of the term. -/
inductive Site where
  | asm (x : Nat) (p : TyPos)
  | tm (a : List Nat)
deriving DecidableEq

/-- The positions of a type that a kept list knows. A node counts when its site is kept and each
node above it counts: a fold at a node folds its sub-tree. `site` names the node at a
position. -/
def ToyTy.known (k : List Site) (site : TyPos → Site) : TyPos → ToyTy → List TyPos
  | _, .gap => []
  | p, .one => if site p ∈ k then [p] else []
  | p, .arrow a b =>
    if site p ∈ k then p :: (known k site (p ++ [0]) a ++ known k site (p ++ [1]) b) else []
  | p, .prod a b =>
    if site p ∈ k then p :: (known k site (p ++ [0]) a ++ known k site (p ++ [1]) b) else []

/-- Every position of a type that is not a gap. -/
def ToyTy.positions : TyPos → ToyTy → List TyPos
  | _, .gap => []
  | p, .one => [p]
  | p, .arrow a b => p :: (positions (p ++ [0]) a ++ positions (p ++ [1]) b)
  | p, .prod a b => p :: (positions (p ++ [0]) a ++ positions (p ++ [1]) b)

/-- A type as the slice of its positions. The type side of the toy is the paper's slice lattice
of the full type (p. 7): a type with gaps keeps the positions that are no gap, and precision is
inclusion. So the module's own carrier serves on both sides. -/
def ToyTy.slice (t : ToyTy) : Slice TyPos := ⟨t.positions []⟩

/-- The type that the kept part of a term synthesises, as its known positions. A node that is
not kept is a hole: it gives the gap, and nothing below it is read. A conditional joins its
branches and does not read its condition. -/
def synth (k : List Site) (env : List ToyTy) : List Nat → ToyTm → List TyPos
  | _, .hole => []
  | a, .lit => if Site.tm a ∈ k then [[]] else []
  | a, .var x => if Site.tm a ∈ k then (env.getD x .gap).known k (Site.asm x) [] else []
  | a, .pair l r =>
    if Site.tm a ∈ k then
      [] :: ((synth k env (a ++ [0]) l).map (0 :: ·) ++ (synth k env (a ++ [1]) r).map (1 :: ·))
    else []
  | a, .ite _ t e =>
    if Site.tm a ∈ k then synth k env (a ++ [1]) t ++ synth k env (a ++ [2]) e else []

/-- A helper of `synth_mono`: an assumption's known positions grow with the kept sites. -/
theorem known_mono {k k' : List Site} (h : k ⊆ k') (site : TyPos → Site) :
    ∀ (t : ToyTy) (p : TyPos), t.known k site p ⊆ t.known k' site p
  | .gap, _ => List.Subset.refl _
  | .one, p => by
    unfold ToyTy.known
    split
    · next hp => rw [if_pos (h hp)]; exact List.Subset.refl _
    · exact List.nil_subset _
  | .arrow a b, p => by
    unfold ToyTy.known
    split
    · next hp =>
      rw [if_pos (h hp)]
      have ha := known_mono h site a (p ++ [0])
      have hb := known_mono h site b (p ++ [1])
      sub_tac using ha, hb
    · exact List.nil_subset _
  | .prod a b, p => by
    unfold ToyTy.known
    split
    · next hp =>
      rw [if_pos (h hp)]
      have ha := known_mono h site a (p ++ [0])
      have hb := known_mono h site b (p ++ [1])
      sub_tac using ha, hb
    · exact List.nil_subset _

/-- **The toy's one fact**: a kept list that keeps more synthesises a type that knows more. It
is the toy's graduality (the paper's Definition 2.1, p. 5). -/
theorem synth_mono {k k' : List Site} (h : k ⊆ k') (env : List ToyTy) :
    ∀ (e : ToyTm) (a : List Nat), synth k env a e ⊆ synth k' env a e
  | .hole, _ => List.Subset.refl _
  | .lit, a => by
    unfold synth
    split
    · next ha => rw [if_pos (h ha)]; exact List.Subset.refl _
    · exact List.nil_subset _
  | .var x, a => by
    unfold synth
    split
    · next ha => rw [if_pos (h ha)]; exact known_mono h _ _ _
    · exact List.nil_subset _
  | .pair l r, a => by
    unfold synth
    split
    · next ha =>
      rw [if_pos (h ha)]
      have hl := List.map_subset (0 :: ·) (synth_mono h env l (a ++ [0]))
      have hr := List.map_subset (1 :: ·) (synth_mono h env r (a ++ [1]))
      sub_tac using hl, hr
    · exact List.nil_subset _
  | .ite _ t e, a => by
    unfold synth
    split
    · next ha =>
      rw [if_pos (h ha)]
      have ht := synth_mono h env t (a ++ [1])
      have he := synth_mono h env e (a ++ [2])
      sub_tac using ht, he
    · exact List.nil_subset _

/-- A toy program: its assumptions, by index, and its term. -/
structure Prog where
  env : List ToyTy
  term : ToyTm

/-- **The toy view**: a slice of the program to the slice of its type. It owes `synth_mono` and
nothing else. -/
def toy (P : Prog) : SliceView Site (Slice TyPos) where
  typeOf s := ⟨synth s.kept P.env [] P.term⟩
  mono h := synth_mono h P.env P.term []

/-- The addresses of a term's nodes, holes left out, parents first. -/
def ToyTm.addrs : List Nat → ToyTm → List (List Nat)
  | _, .hole => []
  | a, .lit => [a]
  | a, .var _ => [a]
  | a, .pair l r => a :: (l.addrs (a ++ [0]) ++ r.addrs (a ++ [1]))
  | a, .ite c t e => a :: (c.addrs (a ++ [0]) ++ t.addrs (a ++ [1]) ++ e.addrs (a ++ [2]))

/-- The sites of the assumptions, from the index `x` on. -/
def envSites : Nat → List ToyTy → List Site
  | _, [] => []
  | x, t :: ts => (t.positions []).map (Site.asm x) ++ envSites (x + 1) ts

/-- The full slice: every site of the program, the assumptions first. Its order is the order in
which the descent tries the sites. -/
def Prog.full (P : Prog) : Slice Site :=
  ⟨envSites 0 P.env ++ (P.term.addrs []).map Site.tm⟩

/-! ## Page 18: four incomparable minimal slices

`Γ = (x : 1 → 1, y : 1 → 1)`, `e = if true then x else y`, and the query `1 → 1` (the paper's
section 8.1). -/

/-- The program of the paper's page 18. -/
def page18 : Prog := ⟨[.arrow .one .one, .arrow .one .one], .ite .lit (.var 0) (.var 1)⟩

/-- The query `1 → 1`. -/
def q11 : Slice TyPos := (ToyTy.arrow .one .one).slice
/-- The query `1 → □`. -/
def q10 : Slice TyPos := (ToyTy.arrow .one .gap).slice
/-- The query `□ → 1`. -/
def q01 : Slice TyPos := (ToyTy.arrow .gap .one).slice

/-- (A): both branches; `x : 1 → □` and `y : □ → 1`. -/
def sliceA : Slice Site :=
  ⟨[.asm 0 [], .asm 0 [0], .asm 1 [], .asm 1 [1], .tm [], .tm [1], .tm [2]]⟩
/-- (B): both branches; `x : □ → 1` and `y : 1 → □`. -/
def sliceB : Slice Site :=
  ⟨[.asm 0 [], .asm 0 [1], .asm 1 [], .asm 1 [0], .tm [], .tm [1], .tm [2]]⟩
/-- (C): the else-branch omitted; `x : 1 → 1`. -/
def sliceC : Slice Site := ⟨[.asm 0 [], .asm 0 [0], .asm 0 [1], .tm [], .tm [1]]⟩
/-- (D): the then-branch omitted; `y : 1 → 1`. -/
def sliceD : Slice Site := ⟨[.asm 1 [], .asm 1 [0], .asm 1 [1], .tm [], .tm [2]]⟩

-- The program has ten sites, and its full type is the query.
#guard page18.full.kept.length == 10
theorem page18_full_valid : (toy page18).Valid q11 page18.full := by decide

-- Each of the four is minimal: the module's `Decidable` instance, run by the kernel.
theorem sliceA_minimal : (toy page18).Minimal q11 sliceA := by decide
theorem sliceB_minimal : (toy page18).Minimal q11 sliceB := by decide
theorem sliceC_minimal : (toy page18).Minimal q11 sliceC := by decide
theorem sliceD_minimal : (toy page18).Minimal q11 sliceD := by decide

/-- No one of the four is below another. -/
theorem page18_incomparable :
    ¬ sliceA ≤ sliceB ∧ ¬ sliceB ≤ sliceA ∧ ¬ sliceA ≤ sliceC ∧ ¬ sliceC ≤ sliceA ∧
    ¬ sliceA ≤ sliceD ∧ ¬ sliceD ≤ sliceA ∧ ¬ sliceB ≤ sliceC ∧ ¬ sliceC ≤ sliceB ∧
    ¬ sliceB ≤ sliceD ∧ ¬ sliceD ≤ sliceB ∧ ¬ sliceC ≤ sliceD ∧ ¬ sliceD ≤ sliceC := by decide

/-- **They are all the minimal slices**: the search over the 1024 sub-lists of the ten sites
finds these four. -/
theorem page18_four :
    (toy page18).minimals q11 page18.full = [sliceD, sliceB, sliceA, sliceC] := by
  decide +kernel

/-- **The descent returns one of them**, fixed by the order of the start's sites: here (D). -/
theorem page18_descent : (toy page18).descend q11 page18.full = sliceD := by decide

/-- The descent asked ten questions: one for each site of its start. -/
theorem page18_asked : ((toy page18).asked q11 page18.full).length = 10 := by decide

-- The paper's restart gives the same slice (`SliceView.descend_eq_restart`, on this input).
#guard Slice.restart (fun c => decide ((toy page18).Valid q11 c)) page18.full.kept == sliceD.kept

/-- The same ten sites in another order: `x`'s codomain and `y`'s domain first. -/
def page18Reordered : Slice Site :=
  ⟨[.asm 0 [1], .asm 1 [0], .asm 0 [], .asm 0 [0], .asm 1 [], .asm 1 [1], .tm [], .tm [0],
    .tm [1], .tm [2]]⟩

/-- **One minimal slice, and not the smallest.** From the other order the descent returns (A),
which keeps seven sites. (C) and (D) keep five. -/
theorem page18_other_order : (toy page18).descend q11 page18Reordered = sliceA := by decide

#guard sliceA.kept.length == 7 && sliceD.kept.length == 5

-- The contribution slice keeps every site but the condition `true`, which no minimal slice keeps.
#guard (toy page18).contribution q11 page18.full ==
  ⟨[.asm 0 [], .asm 0 [0], .asm 0 [1], .asm 1 [], .asm 1 [0], .asm 1 [1], .tm [], .tm [1],
    .tm [2]]⟩

/-- The module's law on the toy: the contribution slice is valid. -/
theorem page18_contribution_valid :
    (toy page18).Valid q11 ((toy page18).contribution q11 page18.full) :=
  (toy page18).contribution_valid page18_full_valid

/-- Theorem 4.6 on the toy: the query `1 → □` refines `1 → 1`, and the descent from (A) for it
is a minimal slice below (A). -/
theorem page18_refined :
    (toy page18).descend q10 sliceA = ⟨[.asm 0 [], .asm 0 [0], .tm [], .tm [1]]⟩ ∧
    (toy page18).Minimal q10 ((toy page18).descend q10 sliceA) :=
  ⟨by decide, (toy page18).descend_minimal ((toy page18).valid_refine (by decide) sliceA_minimal.1)⟩

/-- Theorem 4.7 on the toy: (C) is valid for `1 → □` and (D) for `□ → 1`, so their join is valid
for the join of the two queries. -/
theorem page18_join : (toy page18).Valid (max q10 q01) (max sliceC sliceD) :=
  (toy page18).valid_max (by decide) (by decide)

/-! ## Page 23: the meet of two valid slices loses the type

A conditional whose two branches each give the type `1` (the paper's section 11.2). -/

/-- The program of the paper's page 23, with `1` for its type `τ`. -/
def page23 : Prog := ⟨[], .ite .lit .lit .lit⟩
/-- The query `1`. -/
def q1 : Slice TyPos := ToyTy.one.slice
/-- The slice that keeps the first branch only. -/
def thenOnly : Slice Site := ⟨[.tm [], .tm [1]]⟩
/-- The slice that keeps the second branch only. -/
def elseOnly : Slice Site := ⟨[.tm [], .tm [2]]⟩

/-- Both slices are valid, and their meet is not: it omits both branches. -/
theorem page23_meet :
    (toy page23).Valid q1 thenOnly ∧ (toy page23).Valid q1 elseOnly ∧
    ¬ (toy page23).Valid q1 (min thenOnly elseOnly) := by decide

/-- The type map does not keep the meet: the meet's type is the gap, and the meet of the two
types is `1`. -/
theorem page23_types :
    (toy page23).typeOf (min thenOnly elseOnly) = ⟨[]⟩ ∧
    min ((toy page23).typeOf thenOnly) ((toy page23).typeOf elseOnly) = q1 := by decide

/-- Both slices are minimal. -/
theorem page23_two_minimal :
    (toy page23).Minimal q1 thenOnly ∧ (toy page23).Minimal q1 elseOnly := by decide

/-- **No least slice.** A least valid slice would be below both, so below their meet, and the
meet would be valid. This is what the module's statements do not establish, and cannot. -/
theorem page23_no_least :
    ¬ ∃ l : Slice Site, (toy page23).Valid q1 l ∧ ∀ j, (toy page23).Valid q1 j → l ≤ j :=
  fun ⟨_, hl, hleast⟩ => page23_meet.2.2 ((toy page23).valid_up hl
    (Std.le_min_iff.mpr ⟨hleast _ page23_meet.1, hleast _ page23_meet.2.1⟩))

/-! ## Page 9: Counterexample 4.2, no exact slice

`x : 1 → 1 ⊢ (x, x)`, with the query `(1 → □) × (□ → 1)`. -/

/-- The program of the paper's Counterexample 4.2. -/
def pairXX : Prog := ⟨[.arrow .one .one], .pair (.var 0) (.var 0)⟩
/-- The query `(1 → □) × (□ → 1)`. -/
def qInexact : Slice TyPos := (ToyTy.prod (.arrow .one .gap) (.arrow .gap .one)).slice

/-- The whole program is the only minimal slice among the 64 sub-lists of its six sites. -/
theorem pairXX_only_full : (toy pairXX).minimals qInexact pairXX.full = [pairXX.full] := by
  decide +kernel

/-- Its type is strictly above the query. -/
theorem pairXX_strictly_above :
    qInexact ≤ (toy pairXX).typeOf pairXX.full ∧
    ¬ (toy pairXX).typeOf pairXX.full ≤ qInexact := by decide

/-- **No exact slice**: no listed slice has the query's type. So validity is "at or above". -/
theorem pairXX_no_exact : ∀ s ∈ pairXX.full.below,
    ¬ ((toy pairXX).typeOf s ≤ qInexact ∧ qInexact ≤ (toy pairXX).typeOf s) := by
  decide +kernel

/-! ## Page 11: nothing upwards

`Γ = (x : 1 → 1, y : □ → □)`, `e = if true then x else y`. The slice through `y` is minimal for
`□ → □`. The wider query `1 → 1` has one minimal slice, through `x`, and it is not above. This
renders the paper's remark on a program of this battery, not its figure. -/

/-- A program whose second assumption knows an arrow and no more. -/
def page11 : Prog := ⟨[.arrow .one .one, .arrow .gap .gap], .ite .lit (.var 0) (.var 1)⟩
/-- The query `□ → □`. -/
def q00 : Slice TyPos := (ToyTy.arrow .gap .gap).slice
/-- The slice through `y`. -/
def viaY : Slice Site := ⟨[.asm 1 [], .tm [], .tm [2]]⟩

theorem viaY_minimal : (toy page11).Minimal q00 viaY := by decide

/-- The refined query is below the wider one, and no minimal slice of the wider one is above
the slice through `y`. Theorem 4.6 goes down only. -/
theorem page11_nothing_upwards :
    q00 ≤ q11 ∧ ∀ m ∈ (toy page11).minimals q11 page11.full, ¬ viaY ≤ m := by
  decide +kernel

/-! ## A minimal slice is a highlighted tree, and the descent over a tree

A fold at a site folds its sub-tree, so a site under a folded parent changes nothing. The
module's `SliceView.Minimal.keeps_above` and `SliceView.descendTree_eq_descend` take that as the
instance's premise. The toy proves it by its fold (`toy_noop`): it is the toy's second fact, owed
for the tree only. -/

/-- The site above a site: the same kind, at the path without its last index. -/
def Site.parent : Site → Option Site
  | .asm _ [] => none
  | .asm x (i :: p) => some (.asm x (i :: p).dropLast)
  | .tm [] => none
  | .tm (i :: a) => some (.tm (i :: a).dropLast)

/-- A site other than `x` is kept without `x` exactly when it is kept. A helper of `toy_noop`. -/
theorem mem_filter_ne {k : List Site} {x y : Site} (h : y ≠ x) :
    y ∈ k.filter (· ≠ x) ↔ y ∈ k := by
  rw [List.mem_filter]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', decide_eq_true h⟩⟩

/-- A helper of `toy_noop`: the known positions of a type do not read the site `x`, when the
fold never stands at `x`. It stands at a child only under a kept node (`hstep`). -/
theorem known_drop {k : List Site} {x : Site} (site : TyPos → Site)
    (hstep : ∀ (q : TyPos) (i : Nat), site q ∈ k → site (q ++ [i]) ≠ x) :
    ∀ (t : ToyTy) (q : TyPos), site q ≠ x →
      t.known (k.filter (· ≠ x)) site q = t.known k site q
  | .gap, _, _ => rfl
  | .one, q, hq => by
    unfold ToyTy.known
    by_cases hk : site q ∈ k
    · rw [if_pos hk, if_pos ((mem_filter_ne hq).mpr hk)]
    · rw [if_neg hk, if_neg fun h => hk ((mem_filter_ne hq).mp h)]
  | .arrow a b, q, hq => by
    unfold ToyTy.known
    by_cases hk : site q ∈ k
    · rw [if_pos hk, if_pos ((mem_filter_ne hq).mpr hk),
        known_drop site hstep a (q ++ [0]) (hstep q 0 hk),
        known_drop site hstep b (q ++ [1]) (hstep q 1 hk)]
    · rw [if_neg hk, if_neg fun h => hk ((mem_filter_ne hq).mp h)]
  | .prod a b, q, hq => by
    unfold ToyTy.known
    by_cases hk : site q ∈ k
    · rw [if_pos hk, if_pos ((mem_filter_ne hq).mpr hk),
        known_drop site hstep a (q ++ [0]) (hstep q 0 hk),
        known_drop site hstep b (q ++ [1]) (hstep q 1 hk)]
    · rw [if_neg hk, if_neg fun h => hk ((mem_filter_ne hq).mp h)]

/-- A helper of `toy_noop`: the synthesis does not read the site `x`, when the fold never
stands at `x`. -/
theorem synth_drop {k : List Site} {x : Site} (env : List ToyTy)
    (htm : ∀ (b : List Nat) (i : Nat), Site.tm b ∈ k → Site.tm (b ++ [i]) ≠ x)
    (hasm : ∀ (w : Nat) (q : TyPos) (i : Nat), Site.asm w q ∈ k → Site.asm w (q ++ [i]) ≠ x)
    (hroot : ∀ w : Nat, Site.asm w [] ≠ x) :
    ∀ (e : ToyTm) (b : List Nat), Site.tm b ≠ x →
      synth (k.filter (· ≠ x)) env b e = synth k env b e
  | .hole, _, _ => rfl
  | .lit, b, hb => by
    unfold synth
    by_cases hk : Site.tm b ∈ k
    · rw [if_pos hk, if_pos ((mem_filter_ne hb).mpr hk)]
    · rw [if_neg hk, if_neg fun h => hk ((mem_filter_ne hb).mp h)]
  | .var w, b, hb => by
    unfold synth
    by_cases hk : Site.tm b ∈ k
    · rw [if_pos hk, if_pos ((mem_filter_ne hb).mpr hk),
        known_drop (Site.asm w) (hasm w) _ [] (hroot w)]
    · rw [if_neg hk, if_neg fun h => hk ((mem_filter_ne hb).mp h)]
  | .pair l r, b, hb => by
    unfold synth
    by_cases hk : Site.tm b ∈ k
    · rw [if_pos hk, if_pos ((mem_filter_ne hb).mpr hk),
        synth_drop env htm hasm hroot l (b ++ [0]) (htm b 0 hk),
        synth_drop env htm hasm hroot r (b ++ [1]) (htm b 1 hk)]
    · rw [if_neg hk, if_neg fun h => hk ((mem_filter_ne hb).mp h)]
  | .ite _ t e, b, hb => by
    unfold synth
    by_cases hk : Site.tm b ∈ k
    · rw [if_pos hk, if_pos ((mem_filter_ne hb).mpr hk),
        synth_drop env htm hasm hroot t (b ++ [1]) (htm b 1 hk),
        synth_drop env htm hasm hroot e (b ++ [2]) (htm b 2 hk)]
    · rw [if_neg hk, if_neg fun h => hk ((mem_filter_ne hb).mp h)]

/-- **The toy's second fact**, owed for the tree only: a site under a folded parent changes
nothing. The fold stands at a site only under its kept parent, so it never stands at `x`. -/
theorem toy_noop (P : Prog) (c : Slice Site) {x y : Site} (hp : x.parent = some y)
    (hy : y ∉ c.kept) : (toy P).typeOf c ≤ (toy P).typeOf (c.drop x) := by
  have key : synth (c.kept.filter (· ≠ x)) P.env [] P.term = synth c.kept P.env [] P.term := by
    cases x with
    | asm v p =>
      cases p with
      | nil => exact nomatch hp
      | cons i p =>
        obtain rfl : Site.asm v (i :: p).dropLast = y := Option.some.inj hp
        refine synth_drop (k := c.kept) (x := .asm v (i :: p)) P.env (fun _ _ _ h => nomatch h)
          (fun w q j hk h => hy ?_) (fun _ h => nomatch h) P.term [] (fun h => nomatch h)
        obtain ⟨rfl, hq⟩ := Site.asm.inj h
        rw [← hq, List.dropLast_concat]
        exact hk
    | tm a =>
      cases a with
      | nil => exact nomatch hp
      | cons i a =>
        obtain rfl : Site.tm (i :: a).dropLast = y := Option.some.inj hp
        refine synth_drop (k := c.kept) (x := .tm (i :: a)) P.env (fun b j hk h => hy ?_)
          (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h) P.term [] (fun h => nomatch h)
        have hb := Site.tm.inj h
        rw [← hb, List.dropLast_concat]
        exact hk
  show synth c.kept P.env [] P.term ⊆ synth (c.kept.filter (· ≠ x)) P.env [] P.term
  rw [key]
  exact List.Subset.refl _

/-- **The module's statement on the toy**: a minimal slice of a toy program keeps the parent of
each site that it keeps. So it is a highlighted tree. -/
theorem toy_minimal_closed (P : Prog) {q : Slice TyPos} {m : Slice Site}
    (h : (toy P).Minimal q m) {x y : Site} (hx : x ∈ m.kept) (hp : x.parent = some y) :
    y ∈ m.kept :=
  h.keeps_above (above := fun y x => x.parent = some y) (fun hyx hy => toy_noop P m hyx hy) hx hp

/-- On the page 18 program: (D) keeps `y`'s arrow because it keeps `y`'s domain. -/
theorem sliceD_keeps_arrow : Site.asm 1 [] ∈ sliceD.kept :=
  toy_minimal_closed page18 sliceD_minimal (x := .asm 1 [0]) (by decide) rfl

/-- (D) with `x`'s domain: a site under the folded arrow of `x`. -/
def dangling : Slice Site := ⟨sliceD.kept ++ [.asm 0 [0]]⟩

/-- Red control: the slice is valid, the site changes nothing, and so the slice is not minimal
(`SliceView.Minimal.needs`). -/
theorem dangling_not_minimal :
    (toy page18).Valid q11 dangling ∧ ¬ (toy page18).Minimal q11 dangling :=
  ⟨by decide, fun h => h.needs (x := .asm 0 [0]) (by decide)
    (toy_noop page18 dangling (y := .asm 0 []) rfl (by decide))⟩

/-- **The descent over a tree, on the toy**: from a valid start it gives the descent's slice,
for every toy program (`SliceView.descendTree_eq_descend`). -/
theorem toy_descendTree (P : Prog) {q : Slice TyPos} {s : Slice Site} (h : (toy P).Valid q s) :
    (toy P).descendTree Site.parent q s = (toy P).descend q s :=
  (toy P).descendTree_eq_descend Site.parent (fun c _ _ hp hy => toy_noop P c hp hy) h

/-- On the page 18 program the descent over the tree returns (D) too. -/
theorem page18_tree : (toy page18).descendTree Site.parent q11 page18.full = sliceD :=
  (toy_descendTree page18 page18_full_valid).trans page18_descent

/-- It asks 8 questions, against 10: `x`'s arrow goes, and its domain and codomain go with it. -/
theorem page18_tree_asked :
    ((toy page18).askedTree Site.parent q11 page18.full).length = 8 := by decide

/-- The query `□`: every slice serves it, the empty one too. -/
def qGap : Slice TyPos := ToyTy.gap.slice

/-- Where the root folds, the descent over the tree asks 1 question, against 4: the root goes,
and the three sites under it go with it. -/
theorem page23_tree_asked :
    ((toy page23).askedTree Site.parent qGap page23.full).length = 1 ∧
    ((toy page23).asked qGap page23.full).length = 4 ∧
    (toy page23).descendTree Site.parent qGap page23.full = ⟨[]⟩ := by decide

/-- Red control: a parent function that is not the fold's. It calls the condition the parent of
the else-branch. -/
def Site.wrongParent : Site → Option Site
  | .tm [2] => some (.tm [0])
  | s => s.parent

/-- **Without the no-op the descent over the tree goes wrong.** The condition goes, and the
else-branch goes with it, unasked. The slice that is left is not valid. The descent returns the
slice with the else-branch. -/
theorem page23_wrong_parent :
    (toy page23).descendTree Site.wrongParent q1 page23.full = ⟨[.tm []]⟩ ∧
    ¬ (toy page23).Valid q1 ⟨[.tm []]⟩ ∧
    (toy page23).descend q1 page23.full = elseOnly := by decide

/-! ## The view of a mask -/

/-- The toy through the plan's mask: the type of the program with the sites `F` folded. -/
def maskedType (P : Prog) (F : List Site) : Slice TyPos :=
  ⟨synth (P.full.kept.filter (· ∉ F)) P.env [] P.term⟩

/-- The mask's graduality: folding more gives a type at or below. -/
theorem maskedType_anti (P : Prog) {F G : List Site} (h : F ⊆ G) :
    maskedType P G ≤ maskedType P F := by
  refine synth_mono (fun x hx => ?_) P.env P.term []
  obtain ⟨hs, hG⟩ := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨hs, decide_eq_true fun hF => of_decide_eq_true hG (h hF)⟩

/-- The toy as the view of a mask. -/
def toyMasked (P : Prog) : SliceView Site (Slice TyPos) :=
  SliceView.ofFolded P.full.kept (maskedType P) (fun h _ => maskedType_anti P h)

/-- At the full slice nothing is folded (`SliceView.ofFolded_full`). -/
theorem toyMasked_full : (toyMasked page18).typeOf page18.full = maskedType page18 [] :=
  SliceView.ofFolded_full _ _ _

-- The two views give one type on each listed slice, and one descent.
#guard page18.full.below.all fun s => (toyMasked page18).typeOf s == (toy page18).typeOf s
theorem toyMasked_descent : (toyMasked page18).descend q11 page18.full = sliceD := by decide

/-! ## The two counts: the restart against the one pass

A finite probe. The validity is upward closed: a slice is valid when it keeps the first half of
`n` sites. The restart asks again about each kept site at each start. -/

/-- An instrument of this battery: one search for the first valid slice one site below, with
the number of its questions. It follows `Slice.firstDrop`. -/
def firstDropAsks (valid : Slice Nat → Bool) : List Nat → List Nat → Nat × Option (List Nat)
  | _, [] => (0, none)
  | done, x :: rest =>
    if valid ⟨done ++ rest⟩ then (1, some (done ++ rest))
    else
      let r := firstDropAsks valid (done ++ [x]) rest
      (r.1 + 1, r.2)

/-- An instrument of this battery: the paper's restart with the number of its questions. The
fuel bounds the number of starts. It follows `Slice.restart`. -/
def restartAsks (valid : Slice Nat → Bool) : Nat → List Nat → Nat × List Nat
  | 0, l => (0, l)
  | fuel + 1, l =>
    match firstDropAsks valid [] l with
    | (n, none) => (n, l)
    | (n, some l') =>
      let r := restartAsks valid fuel l'
      (n + r.1, r.2)

/-- Valid when the slice keeps each of the first `k` numbers: upward closed. -/
def keepsFirst (k : Nat) (s : Slice Nat) : Bool := (List.range k).all fun i => decide (i ∈ s.kept)

-- At 20 sites: the restart asks 120 questions and the pass 20, for one slice.
#guard restartAsks (keepsFirst 10) 21 (List.range 20) == (120, List.range 10)
#guard (Slice.sweepAsked (keepsFirst 10) [] (List.range 20)).length == 20
#guard Slice.sweep (keepsFirst 10) [] (List.range 20) == List.range 10
#guard Slice.restart (keepsFirst 10) (List.range 20) == List.range 10
-- At 30 sites: 255 against 30.
#guard restartAsks (keepsFirst 15) 31 (List.range 30) == (255, List.range 15)
#guard (Slice.sweepAsked (keepsFirst 15) [] (List.range 30)).length == 30
#guard Slice.sweep (keepsFirst 15) [] (List.range 30) == List.range 15
#guard Slice.restart (keepsFirst 15) (List.range 30) == List.range 15

/-! ## Red control: a validity that is not upward closed -/

/-- Not upward closed: `[2]` is valid and `[2, 3]` is not. No view has it as its validity. -/
def crooked (s : Slice Nat) : Bool := s.kept == [1, 2, 3] || s.kept == [1, 2] || s.kept == [2]

theorem crooked_not_up :
    ¬ ∀ a b : Slice Nat, a ≤ b → crooked a = true → crooked b = true :=
  fun h => absurd (h ⟨[2]⟩ ⟨[2, 3]⟩ (by decide) (by decide)) (by decide)

/-- **The pass stops at a slice that is not minimal**: at `[1, 2]`, with the valid `[2]` strictly
below it. The pass refused to drop `1` at `[1, 2, 3]` and never asked again. -/
theorem crooked_pass :
    Slice.sweep crooked [] [1, 2, 3] = [1, 2] ∧ crooked ⟨[2]⟩ = true ∧
    (⟨[2]⟩ : Slice Nat) ≤ ⟨[1, 2]⟩ ∧ ¬ (⟨[1, 2]⟩ : Slice Nat) ≤ ⟨[2]⟩ := by decide

-- The restart asks again and goes on to `[2]`: without monotonicity the two descents differ.
#guard Slice.restart crooked [1, 2, 3] == [2]

/-! ## Red control: a query above the full type -/

/-- The query `1 → 1` with one position more, which the program's type does not have. -/
def qTooBig : Slice TyPos := ⟨[[], [0], [1], [0, 0]]⟩

theorem page18_too_big : ¬ (toy page18).Valid qTooBig page18.full := by decide

/-- **No slice serves it**: `SliceView.valid_up`, read backwards. -/
theorem page18_no_slice_serves (j : Slice Site) (hj : j ≤ page18.full) :
    ¬ (toy page18).Valid qTooBig j :=
  fun hv => page18_too_big ((toy page18).valid_up hv hj)

-- The search finds no minimal slice.
#guard (toy page18).minimals qTooBig page18.full == []

/-- The descent's premise is needed: from a start that is not valid it returns the start. -/
theorem page18_descent_needs_valid :
    (toy page18).descend qTooBig page18.full = page18.full := by decide

end Test.Program.SliceLattice

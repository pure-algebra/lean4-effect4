# 2026-10-06 seat REFS design: a well-formed program expands to a program with no reference

Status: a design note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-refs-brief.md`. Base: `b199c15f`. A scratch
probe at the base states and proves every statement below, and the kernel accepts it. No file
of the slice is in the tree yet, so this note claims no theorem.

## 1. The rank

- **Domain.** The original reference occurrences: `root.refSites []`, a finite list of pairs
  of a site and a target (`Eff.refSites`, `src/Effect4/Program/Refs.lean`).
- **Order.** Program order of the sites, `Path.lt`.
- **Rank.** The rank of a site is the count of original sites that precede it.
- **Edge.** An edge runs from an original occurrence to each original occurrence inside the
  layer at its target. The nested site precedes the caller's site (`target_refs_prior`).
- **Why.** The target precedes the caller's site and is no prefix of it (`Eff.layerRefsWF`).
  The nested site extends the target. So it leaves the caller's site where the target does.
- **A copy.** A round copies a target's layer to a site. A reference in the copy names the
  target of the nested original occurrence, and it takes that occurrence's rank.
- **The budget.** After `k` rounds, each reference left has such an occurrence with
  `rank + k < n`, where `n` is the count of original sites. The program holds it at `k = 0`. A
  round raises `k` by one and lowers the rank by one or more. At `k ≥ n` no reference is left.
- **The bound.** `Eff.expandRefs` runs `n + 1` rounds. The budget ends at `n`, and the case
  `n = 0` needs no separate argument.

Three measures fail, and the rank avoids each:

- a descent over arbitrary paths does not end (`[1]`, `[0,1]`, `[0,0,1]`), so the rank counts
  original sites only;
- target paths do not descend, because a target may contain another target;
- the count of sites can grow in a round (Codex's diamond: 6, 9, 0).

## 2. The one-round step: one law of the generated folds

One law holds at the seven sorts, for every substitute `f` of the references and every two
paths. Its `Eff` instance is below, and the six siblings have the same shape.

```lean
private theorem refSites_onRef_eff (f : List Nat → LayerTerm Op) (node : Eff Op) (p q : List Nat) :
    foldMapAt_eff [] (· ++ ·) (p ++ q) (cata_eff (refAlgebra f) node) (f_layer := LayerTerm.refSite) =
      (foldMapAt_eff [] (· ++ ·) q node (f_layer := LayerTerm.refSite)).flatMap fun x =>
        foldMapAt_layer [] (· ++ ·) (p ++ x.1) (f x.2) (f_layer := LayerTerm.refSite)
```

`refAlgebra f` is `EffAlgebra.onRef f` (`src/Effect4/Program/Fold.lean`) under a reducible
name, equal by `rfl`. The seven proofs are one mutual structural recursion. Each is
`cases node <;> simp only [...]`: the arm list is the fold's own, and no constructor is named.
The reducible name lets `simp only` read a field of the algebra at a constructor. It leaves
the algebra of a recursive call as it is, so the recursive statement still matches. Two
instances are public:

```lean
theorem Eff.refSites_expandRound (orig : Node Op) (e : Eff Op) (p : List Nat) :
    (Eff.expandRound orig e).refSites p =
      (e.refSites p).flatMap fun x => ((orig.layerAt x.2).getD (.ref x.2)).refSites x.1
theorem LayerTerm.refSites_append (l : LayerTerm Op) (p q : List Nat) :
    l.refSites (p ++ q) = (l.refSites q).map fun x => (p ++ x.1, x.2)
theorem LayerTerm.refSites_move {l : LayerTerm Op} {p q : List Nat} {x : List Nat × List Nat}
    (h : x ∈ l.refSites p) : ∃ r, x.1 = p ++ r ∧ (q ++ r, x.2) ∈ l.refSites q
```

The first is the law at `expandAlgebra orig` and the empty path. The second is the law at
`LayerTerm.ref`, where the fold is the identity (`cata_id_layer`). The third reads the second
at two paths.

## 3. The general facts, in their owners' files

`src/Effect4/Laws/Program/PathOrder.lean`, consumer `target_refs_prior` and the budget:

```lean
theorem lt_append_of_lt {a b : List Nat} (hab : lt a b = true) (hpre : properPrefix a b = false)
    (c : List Nat) : lt (a ++ c) b = true
def rank (xs : List (List Nat)) (a : List Nat) : Nat := xs.countP (fun x => lt x a)
theorem rank_lt_length {xs : List (List Nat)} {a : List Nat} (ha : a ∈ xs) : rank xs a < xs.length
theorem rank_lt_rank {xs : List (List Nat)} {a b : List Nat} (ha : a ∈ xs) (hab : lt a b = true) :
    rank xs a < rank xs b
```

`src/Effect4/Laws/Program/PathFold.lean`, consumer `target_refs_prior`:

```lean
theorem Node.foldList_subset_of_at (y : PathYield Op α) :
    ∀ (path : List Nat) (n m : Node Op) (p : List Nat), Node.at_ n path = some m →
      foldList y (p ++ path) m ⊆ foldList y p n
theorem refSites_subset_of_at {root : Eff Op} {path : List Nat} {layer : LayerTerm Op}
    (h : Node.at_ (.eff root) path = some (.layer layer)) : layer.refSites path ⊆ root.refSites []
theorem layerRefsWF_mem {root : Eff Op} (hwf : root.layerRefsWF = true) {site target : List Nat}
    (h : (site, target) ∈ root.refSites []) :
    Path.lt target site = true ∧ Path.properPrefix target site = false ∧
      ∃ l, (Node.eff root).layerAt target = some l ∧ ∀ t', l ≠ .ref t'
```

`Node.yieldAt_subset_of_at` and `layerRefsWF_at` keep their statements. Each becomes a
corollary of the fact above it.

## 4. The new module, `src/Effect4/Laws/Program/ReferenceExpansion.lean`

```lean
theorem target_refs_prior (root : Eff Op) (valid : root.layerRefsWF = true)
    {site target nested next : List Nat} {layer : LayerTerm Op}
    (caller : (site, target) ∈ root.refSites [])
    (lookup : (Node.eff root).layerAt target = some layer)
    (inside : (nested, next) ∈ layer.refSites target) :
    (nested, next) ∈ root.refSites [] ∧ Path.lt nested site = true
def RefsWithin (root : Eff Op) (k : Nat) (e : Eff Op) : Prop :=
  ∀ x ∈ e.refSites [], ∃ site, (site, x.2) ∈ root.refSites [] ∧
    Path.rank ((root.refSites []).map Prod.fst) site + k < (root.refSites []).length
theorem refsWithin_self (root : Eff Op) : RefsWithin root 0 root
theorem refsWithin_round (root : Eff Op) (valid : root.layerRefsWF = true) {k : Nat} {e : Eff Op}
    (h : RefsWithin root k e) : RefsWithin root (k + 1) (Eff.expandRound (.eff root) e)
theorem refSites_nil_of_refsWithin {root : Eff Op} {k : Nat} {e : Eff Op}
    (h : RefsWithin root k e) (enough : (root.refSites []).length ≤ k) : e.refSites [] = []
theorem foldl_expandRound_refSites_nil (root : Eff Op) (valid : root.layerRefsWF = true)
    (rounds : List Nat) (enough : (root.refSites []).length ≤ rounds.length) :
    (rounds.foldl (fun acc _ => Eff.expandRound (.eff root) acc) root).refSites [] = []
@[semantics "initial-algebras-folds" (requirement := R5)]
theorem expanded_refs_nil_of_wf {Op : Type} (root : Eff Op)
    (valid : root.layerRefsWF = true) : root.expandRefs.refSites [] = []
```

The top statement is the brief's, unchanged. It lands first as a `proof_goal`. The module adds
no expander and no library of graphs. `RefsWithin` is the one new predicate.

## 5. The existing lemmas that each step uses

| Step | Uses |
| --- | --- |
| `lt_append_of_lt` | `Path.lt` and `Path.properPrefix` (`src/Effect4/Program/Refs.lean`), by `fun_induction` |
| `rank_lt_length`, `rank_lt_rank` | `Path.lt_irrefl`, `Path.lt_trans` (`PathOrder.lean`); `List.countP_mono_left` (the toolchain) |
| `Node.foldList_subset_of_at` | `Node.foldList_child` (`PathFold.lean`) |
| `refSites_subset_of_at` | `refYield` (`PathFold.lean`) |
| the law of section 2 | `cata_eff` and `foldMapAt_eff` with their siblings, `EffAlgebra.id`, `cata_id_layer` (`src/Effect4/Program/Fold.lean`); `LayerTerm.refSite` (`Refs.lean`) |
| `target_refs_prior` | `Node.layerAt_eq_some_iff` (`src/Effect4/Laws/Program/References.lean`); the facts of sections 2 and 3 |
| the two consumers | `expandRefs_eq_self_of_refSites_nil`, `layerRefsWF_of_refSites_nil` (`src/Effect4/Laws/Program/ReferenceTyping.lean`); `checkTypedProgram_complete` (`src/Effect4/Laws/Program/CheckedTyping.lean`); `effTy_complete` (`src/Effect4/Laws/Program/Typing/Sound.lean`) |

The proof differs from Codex's review in one place. It proves no inverse fact from a collected
site to an address. The law of section 2 moves a layer's sites with its path, and that
replaces it.

## 6. The consumers

```lean
theorem typeOfProgram_eq_if_refsWF {Op : Type} (sig : Signature Op) (p : Eff Op) :
    typeOfProgram sig p = if p.layerRefsWF then typeOf sig p.expandRefs else none
theorem typeOfProgram_expandRefs {Op : Type} (sig : Signature Op) (p : Eff Op)
    (hwf : p.layerRefsWF = true) : typeOfProgram sig p.expandRefs = typeOfProgram sig p
theorem checkTypedProgram_of_hasTy {ty : EffTy} (references : program.layerRefsWF = true)
    (typed : Conform.Effect4.Typing.HasTy sig [] program.expandRefs ty) :
    ∃ checked, checkTypedProgram sig program = some checked ∧ checked.ty = ty
```

The equation follows from the top theorem, and both consumers follow from the equation.
`typeOfProgram_expandRefs` keeps `hwf`. The probe shows why on one program with a forward
reference: the checker refuses the program, and it gives the program's expansion a type.

## 7. The required property's text, for `docs/core/semantics.md` under `initial-algebras-folds`

> - **Reference expansion leaves no reference (`reference-expansion-complete`)**: a program
>   whose layer references are well formed (`Eff.layerRefsWF`) expands to a program with no
>   reference site. The bound is that of `Eff.expandRefs`: one more round than the program has
>   reference sites (`expanded_refs_nil_of_wf`
>   (`src/Effect4/Laws/Program/ReferenceExpansion.lean`)). The one premise is the formation of
>   the references. Scope, type formation and typing are not conclusions. So the second test
>   of the whole-program checker follows from its first (`typeOfProgram_eq_if_refsWF`,
>   `src/Effect4/Laws/Program/ReferenceTyping.lean`). The property is about the expansion that
>   typing reads. The compile does not expand: it redirects a reference to its target, and a
>   run shares the layer by its path.

## 8. What this does not establish

The theorem gives no scope, no type formation and no typing success. It says nothing about a
run, about the sharing of layers, about `lower_refines_build` or about R8. One theorem of the
reference expansion closes no requirement.

## 9. Addendum, at the landing (2026-10-06)

The landed tree differs from sections 3 and 5 in two places. The receipt
(`docs/research/2026-10-06-seat-REFS-receipt.md`) gives the reason.

- `refSites_subset_of_at` landed as `refSites_subset_of_layerAt`. Its premise is the layer
  lookup `Node.layerAt`, the form that `Eff.layerRefsWF` reads. So the new module does not
  import `src/Effect4/Laws/Program/References.lean`, and it does not use
  `Node.layerAt_eq_some_iff`.
- `lt_append_of_lt` and the counting step of the rank are proved by hand, with no search.
  `PathOrder.lean` keeps its two imports.

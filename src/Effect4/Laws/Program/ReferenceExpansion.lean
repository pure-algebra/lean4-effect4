import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.PathOrder
import Effect4.Laws.Auto.Semantics

/-!
# Laws/Program/ReferenceExpansion — a well-formed program expands to a program with no reference

`Eff.expandRefs` (`Program/Refs.lean`) replaces each layer reference by the term at its target,
for one more round than the program has reference sites. This module proves that the bound is
enough: a program whose layer references are well formed (`Eff.layerRefsWF`) expands to a program
with no reference site (`expanded_refs_nil_of_wf`).

Proof graph, each fact a step of `expanded_refs_nil_of_wf`:

* **One law of the generated folds**, at the seven sorts (`refSites_onRef_eff` and its six
  siblings): the reference sites under a substitution of the references are, at each reference
  site, the reference sites of the substitute. Two instances are read off it. One round is the
  law at the expansion algebra (`Eff.refSites_expandRound`). A layer's reference sites move with
  its path (`LayerTerm.refSites_append`, `LayerTerm.refSites_move`): the law at the identity.
* **The edge descends** (`target_refs_prior`): a reference inside a target is an original
  reference of the program, and its site precedes the site of every reference to that target.
  The target precedes the caller's site and is no prefix of it (`layerRefsWF_mem`,
  `Laws/Program/PathFold.lean`), and the nested site extends the target
  (`Path.lt_append_of_lt`, `Laws/Program/PathOrder.lean`).
* **The budget** (`RefsWithin`): after `k` rounds, each reference left names the target of an
  original occurrence whose rank (`Path.rank`) leaves room for `k` rounds. The program holds it
  at `k = 0` (`refsWithin_self`), and a round keeps it at `k + 1` (`refsWithin_round`). At the
  count of the original sites no reference is left (`refSites_nil_of_refsWithin`).

The rank's domain is the finite list of the original reference sites. A descent over all paths
does not end, and target paths do not descend: a target may contain another target. The count of
the sites is no measure either, since a round can raise it
(`Test/Program/ReferenceExpansion.lean`, the diamond).

Placement (AGENTS.md, Trust):

- concept initial-algebras-folds (`docs/core/semantics.md` §2.7), requirement R5; the proposed
  registry claim is `reference-expansion-complete`;
- reach: every operation alphabet, one premise (`Eff.layerRefsWF`), the bound of
  `Eff.expandRefs`;
- it does not establish scope, type formation or typing success. It says nothing about a run:
  the compile does not expand, it redirects a reference to its target and shares the layer by
  its path. It does not establish `lower_refines_build` or any equal-observation claim of R8;
- consumers: `typeOfProgram_expandRefs` (`Laws/Program/ReferenceTyping.lean`) and
  `TypedProgram.expanded_refSites` (`Laws/Program/CheckedTyping.lean`). The checker
  (`typeOfProgram`, `Program/Typing.lean`) and the facade's refusal (`Api.explain`, `Api.lean`)
  make no second test because of it (decisions row 273). So each equation is its definition's
  own: `typeOfProgram_eq_if_refsWF`, and `Api.explain_eq_if_refsWF` (`Laws/Api/Codegen.lean`).

The design is `docs/research/2026-10-06-seat-REFS-design.md`.
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-! ## One law of the generated folds: the reference sites under a substitution -/

/-- `EffAlgebra.onRef f` (`Program/Fold.lean`) under a reducible name: the identity algebra with
the reference slot replaced by `f`. `simp only` reads a field of this algebra at a constructor
through the name, and it leaves the algebra of a recursive call as it is. So one `simp only` call
closes every arm of a sort, and the recursive statement still matches. Its consumers are the two
laws of the generated folds under a substitution: the reference sites here, and the fixed syntax
of `Laws/Program/ReferenceTyping.lean` (`onRef_eq_self_eff` and its siblings). -/
@[reducible] def refAlgebra (f : List Nat → LayerTerm Op) :
    EffAlgebra Op (EffSelfCarrier Op) :=
  { EffAlgebra.id Op with layer_ref := f }

/-- The reducible name is the generated algebra. -/
example (f : List Nat → LayerTerm Op) : refAlgebra f = EffAlgebra.onRef f := rfl

/-- The reference sites that a substitution `f` puts at one reference site `x`, under the
path `p`. -/
private abbrev sitesAt (f : List Nat → LayerTerm Op) (p : List Nat) (x : List Nat × List Nat) :
    List (List Nat × List Nat) :=
  foldMapAt_layer [] (· ++ ·) (p ++ x.1) (f x.2) (f_layer := LayerTerm.refSite)

/-! The law, stated on the generated folds themselves: `Eff.refSites` and its siblings are
`foldMapAt_eff` and its siblings at the yield `LayerTerm.refSite`, by definition. The seven
statements are one structural recursion over the seven sorts. Each proof takes its arms from the
sort (`cases node`), which are the arms of its fold, and one `simp only` call closes them all:
it unfolds the two folds at the constructor, and it rewrites each child by the statement at the
child's sort. The paths `p` and `q` split the fold's path, so that a child's path `q ++ [i]`
stays under the same `p`. -/

mutual
/-- The law at `Eff`. A step of `expanded_refs_nil_of_wf`; consumer `Eff.refSites_expandRound`. -/
private theorem refSites_onRef_eff (f : List Nat → LayerTerm Op) (node : Eff Op)
    (p q : List Nat) :
    foldMapAt_eff [] (· ++ ·) (p ++ q) (cata_eff (refAlgebra f) node)
        (f_layer := LayerTerm.refSite) =
      (foldMapAt_eff [] (· ++ ·) q node (f_layer := LayerTerm.refSite)).flatMap (sitesAt f p) := by
  cases node <;> simp only [cata_eff, EffAlgebra.id, foldMapAt_eff, List.flatMap_append,
    List.flatMap_nil, List.nil_append, List.append_assoc, refSites_onRef_eff f,
    refSites_onRef_stmts f, refSites_onRef_action f, refSites_onRef_layer f]

/-- The law at `Stmt`. -/
private theorem refSites_onRef_stmt (f : List Nat → LayerTerm Op) (node : Stmt Op)
    (p q : List Nat) :
    foldMapAt_stmt [] (· ++ ·) (p ++ q) (cata_stmt (refAlgebra f) node)
        (f_layer := LayerTerm.refSite) =
      (foldMapAt_stmt [] (· ++ ·) q node (f_layer := LayerTerm.refSite)).flatMap (sitesAt f p) := by
  cases node <;> simp only [cata_stmt, EffAlgebra.id, foldMapAt_stmt, List.flatMap_append,
    List.flatMap_nil, List.nil_append, List.append_assoc, refSites_onRef_eff f,
    refSites_onRef_stmts f]

/-- The law at `Stmts`. -/
private theorem refSites_onRef_stmts (f : List Nat → LayerTerm Op) (node : Stmts Op)
    (p q : List Nat) :
    foldMapAt_stmts [] (· ++ ·) (p ++ q) (cata_stmts (refAlgebra f) node)
        (f_layer := LayerTerm.refSite) =
      (foldMapAt_stmts [] (· ++ ·) q node (f_layer := LayerTerm.refSite)).flatMap
        (sitesAt f p) := by
  cases node <;> simp only [cata_stmts, EffAlgebra.id, foldMapAt_stmts, List.flatMap_append,
    List.flatMap_nil, List.nil_append, List.append_assoc, refSites_onRef_stmt f,
    refSites_onRef_stmts f]

/-- The law at `Effs`. -/
private theorem refSites_onRef_effs (f : List Nat → LayerTerm Op) (node : Effs Op)
    (p q : List Nat) :
    foldMapAt_effs [] (· ++ ·) (p ++ q) (cata_effs (refAlgebra f) node)
        (f_layer := LayerTerm.refSite) =
      (foldMapAt_effs [] (· ++ ·) q node (f_layer := LayerTerm.refSite)).flatMap (sitesAt f p) := by
  cases node <;> simp only [cata_effs, EffAlgebra.id, foldMapAt_effs, List.flatMap_append,
    List.flatMap_nil, List.nil_append, List.append_assoc, refSites_onRef_eff f,
    refSites_onRef_effs f]

/-- The law at `ActionTerm`. -/
private theorem refSites_onRef_action (f : List Nat → LayerTerm Op) (node : ActionTerm Op)
    (p q : List Nat) :
    foldMapAt_action [] (· ++ ·) (p ++ q) (cata_action (refAlgebra f) node)
        (f_layer := LayerTerm.refSite) =
      (foldMapAt_action [] (· ++ ·) q node (f_layer := LayerTerm.refSite)).flatMap
        (sitesAt f p) := by
  cases node <;> simp only [cata_action, EffAlgebra.id, foldMapAt_action, List.flatMap_nil,
    List.nil_append, List.append_assoc, refSites_onRef_eff f, refSites_onRef_effs f]

/-- The law at `LayerTerm`, the one sort with a reference: at `ref target` the substitute's
sites stand for the one site. Consumer `LayerTerm.refSites_append`. -/
private theorem refSites_onRef_layer (f : List Nat → LayerTerm Op) (node : LayerTerm Op)
    (p q : List Nat) :
    foldMapAt_layer [] (· ++ ·) (p ++ q) (cata_layer (refAlgebra f) node)
        (f_layer := LayerTerm.refSite) =
      (foldMapAt_layer [] (· ++ ·) q node (f_layer := LayerTerm.refSite)).flatMap
        (sitesAt f p) := by
  cases node <;> simp only [cata_layer, EffAlgebra.id, foldMapAt_layer, LayerTerm.refSite,
    List.flatMap_append, List.flatMap_nil, List.flatMap_cons, List.append_nil, List.nil_append,
    List.append_assoc, refSites_onRef_eff f, refSites_onRef_layer f, refSites_onRef_layers f]

/-- The law at `LayerTerms`. -/
private theorem refSites_onRef_layers (f : List Nat → LayerTerm Op) (node : LayerTerms Op)
    (p q : List Nat) :
    foldMapAt_layers [] (· ++ ·) (p ++ q) (cata_layers (refAlgebra f) node)
        (f_layer := LayerTerm.refSite) =
      (foldMapAt_layers [] (· ++ ·) q node (f_layer := LayerTerm.refSite)).flatMap
        (sitesAt f p) := by
  cases node <;> simp only [cata_layers, EffAlgebra.id, foldMapAt_layers, List.flatMap_append,
    List.flatMap_nil, List.nil_append, List.append_assoc, refSites_onRef_layer f,
    refSites_onRef_layers f]
end

/-- **One round, at a program.** The reference sites of a round are, at each reference site of
the program, the reference sites of what the round puts there: the layer at the target, or the
reference itself when the target names no layer. The law at `expandAlgebra orig` and the empty
path. A step of `expanded_refs_nil_of_wf`; consumer `refsWithin_round`. -/
theorem Eff.refSites_expandRound (orig : Node Op) (e : Eff Op) (p : List Nat) :
    (Eff.expandRound orig e).refSites p =
      (e.refSites p).flatMap fun x => ((orig.layerAt x.2).getD (.ref x.2)).refSites x.1 :=
  refSites_onRef_eff (fun target => (orig.layerAt target).getD (.ref target)) e [] p

/-- **A layer's reference sites move with its path**: a longer path prefixes each site and
changes no target. The law at `LayerTerm.ref`, where the fold is the identity (`cata_id_layer`).
A step of `expanded_refs_nil_of_wf`; consumer `LayerTerm.refSites_move`. -/
theorem LayerTerm.refSites_append (l : LayerTerm Op) (p q : List Nat) :
    l.refSites (p ++ q) = (l.refSites q).map fun x => (p ++ x.1, x.2) := by
  have h := refSites_onRef_layer LayerTerm.ref l p q
  rw [show refAlgebra (Op := Op) LayerTerm.ref = EffAlgebra.id Op from rfl, cata_id_layer] at h
  rw [List.map_eq_flatMap]
  exact h

/-- A reference site of a layer at one path is the same reference at any other path: the site
extends the layer's path, and the same extension of the other path is a site with the same
target. A step of `expanded_refs_nil_of_wf`; consumers `target_refs_prior` and
`refsWithin_round`. -/
theorem LayerTerm.refSites_move {l : LayerTerm Op} {p q : List Nat} {x : List Nat × List Nat}
    (h : x ∈ l.refSites p) : ∃ r, x.1 = p ++ r ∧ (q ++ r, x.2) ∈ l.refSites q := by
  have hp := l.refSites_append p []
  have hq := l.refSites_append q []
  rw [List.append_nil] at hp hq
  rw [hp] at h
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
  exact ⟨z.1, rfl, by rw [hq]; exact List.mem_map.mpr ⟨z, hz, rfl⟩⟩

/-! ## The edge descends -/

/-- **A reference inside a target is an original reference, and it precedes every reference to
the target.** The target's layer is a layer of the program, so its sites are the program's
(`refSites_subset_of_layerAt`). The target precedes the caller's site and is no prefix of it
(`layerRefsWF_mem`), and the nested site extends the target (`LayerTerm.refSites_move`,
`Path.lt_append_of_lt`). A step of `expanded_refs_nil_of_wf`; consumer `refsWithin_round`. -/
theorem target_refs_prior (root : Eff Op) (valid : root.layerRefsWF = true)
    {site target nested next : List Nat} {layer : LayerTerm Op}
    (caller : (site, target) ∈ root.refSites [])
    (lookup : (Node.eff root).layerAt target = some layer)
    (inside : (nested, next) ∈ layer.refSites target) :
    (nested, next) ∈ root.refSites [] ∧ Path.lt nested site = true := by
  refine ⟨refSites_subset_of_layerAt lookup inside, ?_⟩
  obtain ⟨hlt, hpre, -⟩ := layerRefsWF_mem valid caller
  obtain ⟨r, hr, -⟩ := LayerTerm.refSites_move (q := []) inside
  have hnested : nested = target ++ r := hr
  rw [hnested]
  exact Path.lt_append_of_lt hlt hpre r

/-! ## The budget -/

/-- **The budget after `k` rounds.** Every reference that `e` holds names the target of an
original occurrence of the program, and that occurrence's rank among the original sites
(`Path.rank`) leaves room for `k` rounds below their count. A copy of a reference keeps no site
of its own: the budget reads the target only. -/
def RefsWithin (root : Eff Op) (k : Nat) (e : Eff Op) : Prop :=
  ∀ x ∈ e.refSites [], ∃ site, (site, x.2) ∈ root.refSites [] ∧
    Path.rank ((root.refSites []).map Prod.fst) site + k < (root.refSites []).length

/-- The program holds its own budget before a round: a member's rank is below the count
(`Path.rank_lt_length`). A step of `expanded_refs_nil_of_wf`; consumer
`foldl_expandRound_refSites_nil`. -/
theorem refsWithin_self (root : Eff Op) : RefsWithin root 0 root := by
  intro x hx
  refine ⟨x.1, hx, ?_⟩
  have hrank := Path.rank_lt_length
    (List.mem_map.mpr ⟨x, hx, rfl⟩ : x.1 ∈ (root.refSites []).map Prod.fst)
  rw [List.length_map] at hrank
  omega

/-- **A round keeps the budget, one round on.** A reference of the round's result is in the copy
of a target's layer (`Eff.refSites_expandRound`). It names the target of an original occurrence
inside that layer (`LayerTerm.refSites_move`), which precedes the occurrence that the replaced
reference had (`target_refs_prior`). So its rank is smaller (`Path.rank_lt_rank`). A step of
`expanded_refs_nil_of_wf`; consumer `refsWithin_rounds`. -/
theorem refsWithin_round (root : Eff Op) (valid : root.layerRefsWF = true) {k : Nat} {e : Eff Op}
    (h : RefsWithin root k e) : RefsWithin root (k + 1) (Eff.expandRound (.eff root) e) := by
  intro y hy
  rw [Eff.refSites_expandRound] at hy
  obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.mp hy
  obtain ⟨site, hsite, hrank⟩ := h x hx
  obtain ⟨-, -, layer, hlayer, -⟩ := layerRefsWF_mem valid hsite
  rw [hlayer, Option.getD_some] at hyx
  obtain ⟨r, -, horig⟩ := LayerTerm.refSites_move (q := x.2) hyx
  obtain ⟨hmem, hlt⟩ := target_refs_prior root valid hsite hlayer horig
  refine ⟨x.2 ++ r, hmem, ?_⟩
  have hless := Path.rank_lt_rank
    (List.mem_map.mpr ⟨_, hmem, rfl⟩ : x.2 ++ r ∈ (root.refSites []).map Prod.fst) hlt
  omega

/-- The rounds keep the budget, one round each. A step of `expanded_refs_nil_of_wf`; consumer
`foldl_expandRound_refSites_nil`. -/
theorem refsWithin_rounds (root : Eff Op) (valid : root.layerRefsWF = true) :
    ∀ (rounds : List Nat) (k : Nat) (e : Eff Op), RefsWithin root k e →
      RefsWithin root (k + rounds.length)
        (rounds.foldl (fun acc _ => Eff.expandRound (.eff root) acc) e)
  | [], _, _, h => h
  | _ :: rounds, k, e, h => by
    have hrest := refsWithin_rounds root valid rounds (k + 1) _ (refsWithin_round root valid h)
    rw [List.length_cons, show k + (rounds.length + 1) = k + 1 + rounds.length by omega]
    exact hrest

/-- A spent budget leaves no reference: at as many rounds as the program has original sites, no
rank is small enough. A step of `expanded_refs_nil_of_wf`; consumer
`foldl_expandRound_refSites_nil`. -/
theorem refSites_nil_of_refsWithin {root : Eff Op} {k : Nat} {e : Eff Op}
    (h : RefsWithin root k e) (enough : (root.refSites []).length ≤ k) : e.refSites [] = [] := by
  cases hs : e.refSites [] with
  | nil => rfl
  | cons x rest =>
    obtain ⟨_, _, hrank⟩ := h x (by rw [hs]; exact List.mem_cons_self)
    omega

/-- **As many rounds as the program has reference sites leave no reference**, and so does every
longer run of rounds. The exact bound, of which `Eff.expandRefs` runs one round more. A step of
`expanded_refs_nil_of_wf`. -/
theorem foldl_expandRound_refSites_nil (root : Eff Op) (valid : root.layerRefsWF = true)
    (rounds : List Nat) (enough : (root.refSites []).length ≤ rounds.length) :
    (rounds.foldl (fun acc _ => Eff.expandRound (.eff root) acc) root).refSites [] = [] :=
  refSites_nil_of_refsWithin (refsWithin_rounds root valid rounds 0 root (refsWithin_self root))
    (by omega)

/-- **A well-formed program expands to a program with no reference site**, at the bound that
`Eff.expandRefs` uses: one more round than the program has reference sites. The case of no
reference site is the same statement, at one round. -/
@[semantics "initial-algebras-folds" (requirement := R5)]
theorem expanded_refs_nil_of_wf {Op : Type} (root : Eff Op)
    (valid : root.layerRefsWF = true) : root.expandRefs.refSites [] = [] :=
  foldl_expandRound_refSites_nil root valid _ (by rw [List.length_range]; omega)

end Effect4.Program

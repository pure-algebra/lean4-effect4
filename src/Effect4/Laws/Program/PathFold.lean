import Effect4.Program.Refs

/-!
# Laws/Program/PathFold — the path fold visits every addressed node

The generated path folds (`foldMapAt_eff` and its six siblings, `Program/Fold.lean`) and the
node addressing (`Node.child`, `Node.at_`, `Program/NodeLenses.lean`, `Program/Refs.lean`) are
both read off the one signature. Here the two are related once, at the list monoid and for any
yields (`PathYield`): a node's own yield is in its fold (`yieldAt_subset_foldList`), a child's
fold at `p ++ [i]` is in its parent's (`foldList_child`, the case list `Node.child`'s own), so
every addressed node's yield, at its path, is in the root's fold (`yieldAt_subset_of_at`).
A census over the program by the path fold is an instance: the layer reference sites
(`Eff.refSites`, `mem_refSites_of_at`), the premise of the reference formation rule
(`Eff.layerRefsWF`) at a reference reached by its address.

Placement (AGENTS.md, Trust): concept initial-algebras-folds (`docs/core/semantics.md` §2.7);
consumer the layer family's reference hop (`Typed/LayerArm.lean`, decisions row 170's premise read
at an address).
-/

set_option autoImplicit false

namespace Effect4.Program

/-- Yields for the path fold at every sort a node can be. -/
structure PathYield (Op α : Type) where
  eff : Eff Op → List Nat → List α := fun _ _ => []
  stmt : Stmt Op → List Nat → List α := fun _ _ => []
  stmts : Stmts Op → List Nat → List α := fun _ _ => []
  effs : Effs Op → List Nat → List α := fun _ _ => []
  action : ActionTerm Op → List Nat → List α := fun _ _ => []
  layer : LayerTerm Op → List Nat → List α := fun _ _ => []
  layers : LayerTerms Op → List Nat → List α := fun _ _ => []

namespace Node

variable {Op α : Type}

/-- The path fold at the list monoid over a node of any sort: its sort's generated fold. -/
def foldList (y : PathYield Op α) (p : List Nat) : Node Op → List α
  | .eff e => foldMapAt_eff [] (· ++ ·) p e y.eff y.stmt y.stmts y.effs y.action y.layer y.layers
  | .stmts s => foldMapAt_stmts [] (· ++ ·) p s y.eff y.stmt y.stmts y.effs y.action y.layer y.layers
  | .stmt s => foldMapAt_stmt [] (· ++ ·) p s y.eff y.stmt y.stmts y.effs y.action y.layer y.layers
  | .action a => foldMapAt_action [] (· ++ ·) p a y.eff y.stmt y.stmts y.effs y.action y.layer y.layers
  | .effs es => foldMapAt_effs [] (· ++ ·) p es y.eff y.stmt y.stmts y.effs y.action y.layer y.layers
  | .layer l => foldMapAt_layer [] (· ++ ·) p l y.eff y.stmt y.stmts y.effs y.action y.layer y.layers
  | .layers ls => foldMapAt_layers [] (· ++ ·) p ls y.eff y.stmt y.stmts y.effs y.action y.layer y.layers

/-- The yield at one node. -/
def yieldAt (y : PathYield Op α) : Node Op → List Nat → List α
  | .eff e, p => y.eff e p
  | .stmts s, p => y.stmts s p
  | .stmt s, p => y.stmt s p
  | .action a, p => y.action a p
  | .effs es, p => y.effs es p
  | .layer l, p => y.layer l p
  | .layers ls, p => y.layers ls p

/-- A node's own yield is in its fold: every generated arm folds the node's yield first. -/
theorem yieldAt_subset_foldList (y : PathYield Op α) (p : List Nat) (n : Node Op) :
    yieldAt y n p ⊆ foldList y p n := by
  intro x hx
  cases n with
  | eff e => cases e <;> simp only [yieldAt, foldList, foldMapAt_eff, List.mem_append] at hx ⊢ <;>
      simp only [hx, true_or]
  | stmts s => cases s <;> simp only [yieldAt, foldList, foldMapAt_stmts, List.mem_append] at hx ⊢ <;>
      simp only [hx, true_or]
  | stmt s => cases s <;> simp only [yieldAt, foldList, foldMapAt_stmt, List.mem_append] at hx ⊢ <;>
      simp only [hx, true_or]
  | action a => cases a <;> simp only [yieldAt, foldList, foldMapAt_action, List.mem_append] at hx ⊢ <;>
      simp only [hx, true_or]
  | effs es => cases es <;> simp only [yieldAt, foldList, foldMapAt_effs, List.mem_append] at hx ⊢ <;>
      simp only [hx, true_or]
  | layer l => cases l <;> simp only [yieldAt, foldList, foldMapAt_layer, List.mem_append] at hx ⊢ <;>
      simp only [hx, true_or]
  | layers ls => cases ls <;> simp only [yieldAt, foldList, foldMapAt_layers, List.mem_append] at hx ⊢ <;>
      simp only [hx, true_or]

/-- A child's fold, at the child's path, is in its parent's: every generated arm folds each
node-typed argument at `p ++ [i]`, the index `Node.child` gives it. -/
theorem foldList_child (y : PathYield Op α) : ∀ (n : Node Op) (i : Nat) (c : Node Op)
    (p : List Nat), n.child i = some c → foldList y (p ++ [i]) c ⊆ foldList y p n := by
  intro n i c p
  fun_cases Node.child n i
  all_goals intro h
  all_goals cases h
  all_goals intro x hx
  all_goals simp only [foldList, foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_action,
    foldMapAt_effs, foldMapAt_layer, foldMapAt_layers, List.mem_append] at hx ⊢
  all_goals simp only [hx, true_or, or_true]

/-- **The path fold collects every addressed node's yield, at the node's path.** -/
theorem yieldAt_subset_of_at (y : PathYield Op α) :
    ∀ (path : List Nat) (n m : Node Op) (p : List Nat), Node.at_ n path = some m →
      yieldAt y m (p ++ path) ⊆ foldList y p n
  | [], n, m, p, h => by
    simp only [Node.at_, Option.some.injEq] at h
    subst h
    rw [List.append_nil]
    exact yieldAt_subset_foldList y p n
  | i :: rest, n, m, p, h => by
    simp only [Node.at_] at h
    obtain ⟨c, hc, hrest⟩ := Option.bind_eq_some_iff.mp h
    have ih := yieldAt_subset_of_at y rest c m (p ++ [i]) hrest
    rw [List.append_assoc, List.singleton_append] at ih
    exact List.Subset.trans ih (foldList_child y n i c p hc)

end Node

/-- The reference sites as a path fold: each reference yields `(site, target)`. -/
def refYield {Op : Type} : PathYield Op (List Nat × List Nat) := { layer := LayerTerm.refSite }

/-- **A reference at an address is one of the program's reference sites.** -/
theorem mem_refSites_of_at {Op : Type} {root : Eff Op} {path target : List Nat}
    (h : Node.at_ (.eff root) path = some (.layer (.ref target))) :
    (path, target) ∈ root.refSites [] := by
  have hsub := Node.yieldAt_subset_of_at refYield path (.eff root) _ [] h
  rw [List.nil_append] at hsub
  exact hsub (List.mem_singleton_self _)

/-- Well-formed references, read at an address: the target names a layer that is no reference. -/
theorem layerRefsWF_at {Op : Type} {root : Eff Op} {path target : List Nat}
    (hwf : root.layerRefsWF = true) (h : Node.at_ (.eff root) path = some (.layer (.ref target))) :
    ∃ l, (Node.eff root).layerAt target = some l ∧ ∀ t', l ≠ .ref t' := by
  have hall := List.all_eq_true.mp hwf (path, target) (mem_refSites_of_at h)
  simp only [Bool.and_eq_true] at hall
  obtain ⟨_, hlayer⟩ := hall
  cases hl : (Node.eff root).layerAt target with
  | none =>
    rw [hl] at hlayer
    exact Bool.noConfusion hlayer
  | some l =>
    rw [hl] at hlayer
    refine ⟨l, rfl, fun t' heq => ?_⟩
    subst heq
    exact Bool.noConfusion hlayer

end Effect4.Program

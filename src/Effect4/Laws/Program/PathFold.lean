import Effect4.Program.Refs
import Effect4.Laws.Auto.Semantics

/-!
# Laws/Program/PathFold — the path fold visits every addressed node

The generated path folds (`foldMapAt_eff` and its six siblings, `Program/Fold.lean`) and the
node addressing (`Node.child`, `Node.at_`, `Program/NodeLenses.lean`, `Program/Refs.lean`) are
both read off the one signature. Here the two are related once, at the list monoid and for any
yields (`PathYield`): a node's own yield is in its fold (`yieldAt_subset_foldList`), a child's
fold at `p ++ [i]` is in its parent's (`foldList_child`, the case list `Node.child`'s own), so
every addressed node's fold, at its path, is in the root's fold (`foldList_subset_of_at`), and
its yield with it (`yieldAt_subset_of_at`).
The converse holds too: a member of a fold is in its node's yield or in a child's fold
(`foldList_cases`), so the fold collects the yields of the addressed nodes and nothing else
(`mem_foldList_iff`). Its consumer is the address list of a node (`mem_addresses_iff`,
`Laws/Program/Typing/Table.lean`).
A census over the program by the path fold is an instance: the layer reference sites
(`Eff.refSites`, `mem_refSites_of_at`, `refSites_subset_of_layerAt`), the premise of the reference
formation rule (`Eff.layerRefsWF`) at a reference site (`layerRefsWF_mem`) and at a reference
reached by its address (`layerRefsWF_at`).

The last section relates a path fold to the fold with no path (`foldMap_eff` and its siblings).
Through a homomorphism that reads no path, a path fold is the fold with no path. The law is
`foldMapAt_eff_fuse` with its six siblings, and `foldMapAt_term_fuse` for a term. It holds at
every operation, not at the list monoid alone. So a census that a path fold collects is a
conjunction over the program's shape, once its paths are forgotten.

Placement (AGENTS.md, Trust): concept initial-algebras-folds (`docs/core/semantics.md` §2.7).
The consumers are the layer family's reference hop (`Typed/LayerArm.lean`, decisions row 170's
premise read at an address) and the reference expansion (`Laws/Program/ReferenceExpansion.lean`,
`target_refs_prior`, a step of `expanded_refs_nil_of_wf`). The consumer of the last section is
the fold form of a program's annotations (`Formation.programAnnotations_all`,
`Laws/Program/Typing/Closed.lean`), a step of `check_closed` (requirement R14).
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

/-- **A descendant's fold, at its path, is in its ancestor's**: the child step (`foldList_child`)
along the address. Its consumers are `yieldAt_subset_of_at` below and
`refSites_subset_of_layerAt`. -/
theorem foldList_subset_of_at (y : PathYield Op α) :
    ∀ (path : List Nat) (n m : Node Op) (p : List Nat), Node.at_ n path = some m →
      foldList y (p ++ path) m ⊆ foldList y p n
  | [], n, m, p, h => by
    simp only [Node.at_, Option.some.injEq] at h
    subst h
    rw [List.append_nil]
    exact List.Subset.refl _
  | i :: rest, n, m, p, h => by
    simp only [Node.at_] at h
    obtain ⟨c, hc, hrest⟩ := Option.bind_eq_some_iff.mp h
    have ih := foldList_subset_of_at y rest c m (p ++ [i]) hrest
    rw [List.append_assoc, List.singleton_append] at ih
    exact List.Subset.trans ih (foldList_child y n i c p hc)

/-- **The path fold collects every addressed node's yield, at the node's path.** -/
theorem yieldAt_subset_of_at (y : PathYield Op α) (path : List Nat) (n m : Node Op) (p : List Nat)
    (h : Node.at_ n path = some m) : yieldAt y m (p ++ path) ⊆ foldList y p n :=
  List.Subset.trans (yieldAt_subset_foldList y (p ++ path) m) (foldList_subset_of_at y path n m p h)

/-! ### The converse: the fold collects nothing else -/

/-- **One step of the path fold, read back.** A member of a node's fold is in the node's own
yield, or in the fold of a child at the child's path. It is the converse of
`yieldAt_subset_foldList` and `foldList_child` together.

The proof reads each generated arm against `Node.child` at the indices 0, 1 and 2, which
evaluation reduces at a constructor. A constructor with a fourth node-typed argument fails the
proof at its case, so the bound cannot go stale in silence. A step of `focus-function`. Its
consumer is `exists_at_of_mem_foldList` below. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldList_cases (y : PathYield Op α) (p : List Nat) (n : Node Op) {x : α}
    (hx : x ∈ foldList y p n) :
    x ∈ yieldAt y n p ∨ ∃ i c, n.child i = some c ∧ x ∈ foldList y (p ++ [i]) c := by
  suffices h : x ∈ yieldAt y n p ∨
      ∃ i, (i = 0 ∨ i = 1 ∨ i = 2) ∧ ∃ c, n.child i = some c ∧ x ∈ foldList y (p ++ [i]) c by
    rcases h with h | ⟨i, -, c, hc, h⟩
    · exact .inl h
    · exact .inr ⟨i, c, hc, h⟩
  simp only [or_and_right, exists_or, exists_eq_left]
  rcases n with e | e | e | e | e | e | e <;> cases e <;>
    simp only [foldList, foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_action,
      foldMapAt_effs, foldMapAt_layer, foldMapAt_layers, List.mem_append] at hx <;>
    (conv in (occs := *) Node.child _ _ => all_goals whnf) <;>
    simp only [foldList, yieldAt, Option.some.injEq, exists_eq_left', reduceCtorEq, false_and,
      exists_false, or_false] <;>
    exact hx

/-- A child is smaller than its node: the measure of the recursion along `Node.child`. The case
list is `Node.child`'s own. A step of `focus-function`. Its consumer is
`exists_at_of_mem_foldList` below. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem sizeOf_child_lt : ∀ (n : Node Op) (i : Nat) (c : Node Op), n.child i = some c →
    sizeOf c < sizeOf n := by
  intro n i c
  fun_cases Node.child n i
  all_goals intro h
  all_goals cases h
  all_goals decreasing_tactic

/-- **A member of the path fold is the yield of an addressed node, at the node's path**: the
converse of `yieldAt_subset_of_at`. The step is `foldList_cases`, and the recursion goes down
`Node.child`. A step of `focus-function`. Its consumer is `mem_foldList_iff` below. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem exists_at_of_mem_foldList (y : PathYield Op α) (n : Node Op) (p : List Nat) {x : α}
    (hx : x ∈ foldList y p n) :
    ∃ path m, Node.at_ n path = some m ∧ x ∈ yieldAt y m (p ++ path) := by
  rcases foldList_cases y p n hx with h | ⟨i, c, hc, h⟩
  · exact ⟨[], n, rfl, by rwa [List.append_nil]⟩
  · have := sizeOf_child_lt n i c hc
    obtain ⟨path, m, hat, hm⟩ := exists_at_of_mem_foldList y c (p ++ [i]) h
    refine ⟨i :: path, m, ?_, ?_⟩
    · simp only [Node.at_, hc, Option.bind_some]
      exact hat
    · rwa [List.append_assoc, List.singleton_append] at hm
termination_by sizeOf n

/-- **The path fold collects the yields of the addressed nodes, each at its path, and nothing
else.** The two inclusions are `yieldAt_subset_of_at` and `exists_at_of_mem_foldList`. It says
nothing of the order of the fold's list. A step of `focus-function`. Its consumer is the
address list of a node (`mem_addresses_iff`, `Laws/Program/Typing/Table.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem mem_foldList_iff (y : PathYield Op α) (n : Node Op) (p : List Nat) (x : α) :
    x ∈ foldList y p n ↔ ∃ path m, Node.at_ n path = some m ∧ x ∈ yieldAt y m (p ++ path) :=
  ⟨exists_at_of_mem_foldList y n p, fun ⟨path, m, hat, hx⟩ =>
    yieldAt_subset_of_at y path n m p hat hx⟩

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

/-- **The reference sites of the layer at a path, at that path, are reference sites of the
program.** The premise is the layer lookup of the formation rule (`Node.layerAt`,
`Program/Refs.lean`), which reads the node at the path. A step of `expanded_refs_nil_of_wf`
(`Laws/Program/ReferenceExpansion.lean`). Its consumer is `target_refs_prior` there, at the layer
that a reference names. -/
theorem refSites_subset_of_layerAt {Op : Type} {root : Eff Op} {path : List Nat}
    {layer : LayerTerm Op} (h : (Node.eff root).layerAt path = some layer) :
    layer.refSites path ⊆ root.refSites [] := by
  unfold Node.layerAt at h
  split at h
  · rename_i found hat
    rw [Option.some.inj h] at hat
    have hsub := Node.foldList_subset_of_at refYield path (.eff root) (.layer layer) [] hat
    rw [List.nil_append] at hsub
    exact hsub
  · cases h

/-- Well-formed references, read at a reference site: the three clauses of `Eff.layerRefsWF`.
The target precedes the site, it is no prefix of the site, and it names a layer that is no
reference. Its consumers are `layerRefsWF_at` below and the reference expansion
(`target_refs_prior` and `refsWithin_round`, `Laws/Program/ReferenceExpansion.lean`). -/
theorem layerRefsWF_mem {Op : Type} {root : Eff Op} (hwf : root.layerRefsWF = true)
    {site target : List Nat} (h : (site, target) ∈ root.refSites []) :
    Path.lt target site = true ∧ Path.properPrefix target site = false ∧
      ∃ l, (Node.eff root).layerAt target = some l ∧ ∀ t', l ≠ .ref t' := by
  have hall := List.all_eq_true.mp hwf (site, target) h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
  obtain ⟨⟨⟨hlt, hpre⟩, hlayer⟩, -⟩ := hall
  refine ⟨hlt, hpre, ?_⟩
  cases hl : (Node.eff root).layerAt target with
  | none =>
    rw [hl] at hlayer
    exact Bool.noConfusion hlayer
  | some l =>
    rw [hl] at hlayer
    refine ⟨l, rfl, fun t' heq => ?_⟩
    subst heq
    exact Bool.noConfusion hlayer

/-- Well-formed references, read at a reference site: the target stands in the site's scope
(decisions row 340, ruling of 2026-10-10). Its consumer is `scopeParams_ref`
(`Typed/LayerArm.lean`). -/
theorem layerRefsWF_scopeOf {Op : Type} {root : Eff Op} (hwf : root.layerRefsWF = true)
    {site target : List Nat} (h : (site, target) ∈ root.refSites []) :
    root.scopeOf target = root.scopeOf site := by
  have hall := List.all_eq_true.mp hwf (site, target) h
  simp only [Bool.and_eq_true] at hall
  exact eq_of_beq hall.2

/-- Well-formed references, read at an address: the target names a layer that is no reference. -/
theorem layerRefsWF_at {Op : Type} {root : Eff Op} {path target : List Nat}
    (hwf : root.layerRefsWF = true) (h : Node.at_ (.eff root) path = some (.layer (.ref target))) :
    ∃ l, (Node.eff root).layerAt target = some l ∧ ∀ t', l ≠ .ref t' :=
  (layerRefsWF_mem hwf (mem_refSites_of_at h)).2.2

/-! ## A path fold and the fold with no path

The generated module has two folds into a carrier with an operation: the path fold
(`foldMapAt_*`), whose node function reads the node's path, and the fold with no path
(`foldMap_*`). A homomorphism `φ` carries the first to the second when the image of each node's
value does not depend on the path. Each statement is one line for its sort: the sort's case
list, and the law at each recursive argument. -/

section Fuse

universe u v

variable {Op : Type} {M : Type u} {N : Type v}

mutual

/-- **A path fold, through a homomorphism that reads no path, is the fold with no path**, at a
term. `φ` carries the fold's operation to `op'`, and the image of each node's value does not
depend on the node's path. With `φ` the identity it says that a path fold whose node function
reads no path is the fold with no path. It is a law of the generated folds
(`Program/Fold.lean`). A term has two sorts, and each has its own hypothesis. Its consumer is
`Formation.termAnnotations_all` (`Laws/Program/Typing/Closed.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_term_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f_term : Term → List Nat → M} {f_terms : Terms → List Nat → M}
    {g_term : Term → N} {g_terms : Terms → N}
    (hterm : ∀ n q, φ (f_term n q) = g_term n) (hterms : ∀ n q, φ (f_terms n q) = g_terms n)
    (t : Term) (p : List Nat) :
    φ (foldMapAt_term unit op p t f_term f_terms) = foldMap_term unit' op' t g_term g_terms := by
  cases t <;>
    simp only [foldMapAt_term, foldMap_term, hop, hterm,
      foldMapAt_term_fuse φ (unit' := unit') hop hterm hterms,
      foldMapAt_terms_fuse φ (unit' := unit') hop hterm hterms]

/-- `foldMapAt_term_fuse` at an argument list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_terms_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f_term : Term → List Nat → M} {f_terms : Terms → List Nat → M}
    {g_term : Term → N} {g_terms : Terms → N}
    (hterm : ∀ n q, φ (f_term n q) = g_term n) (hterms : ∀ n q, φ (f_terms n q) = g_terms n)
    (ts : Terms) (p : List Nat) :
    φ (foldMapAt_terms unit op p ts f_term f_terms) =
      foldMap_terms unit' op' ts g_term g_terms := by
  cases ts <;>
    simp only [foldMapAt_terms, foldMap_terms, hop, hterms,
      foldMapAt_term_fuse φ (unit' := unit') hop hterm hterms,
      foldMapAt_terms_fuse φ (unit' := unit') hop hterm hterms]

end

mutual

/-- **A path fold, through a homomorphism that reads no path, is the fold with no path**, at a
program. It is `foldMapAt_term_fuse` for the program's family: one statement for each sort, each
proved by the sort's own case list. The node functions of the seven sorts are one function of
the family (`EffSelfCarrier`), so the statement has one hypothesis on them. Its consumer is
`Formation.programAnnotations_all` (`Laws/Program/Typing/Closed.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_eff_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f : (fam : EffFam) → EffSelfCarrier Op fam → List Nat → M}
    {g : (fam : EffFam) → EffSelfCarrier Op fam → N}
    (h : ∀ fam n q, φ (f fam n q) = g fam n) (e : Eff Op) (p : List Nat) :
    φ (foldMapAt_eff unit op p e (f .eff) (f .stmt) (f .stmts) (f .effs) (f .action) (f .layer)
        (f .layers)) =
      foldMap_eff unit' op' e (g .eff) (g .stmt) (g .stmts) (g .effs) (g .action) (g .layer)
        (g .layers) := by
  cases e <;>
    simp only [foldMapAt_eff, foldMap_eff, hop, h,
      foldMapAt_eff_fuse φ (unit' := unit') hop h, foldMapAt_stmts_fuse φ (unit' := unit') hop h,
      foldMapAt_effs_fuse φ (unit' := unit') hop h, foldMapAt_action_fuse φ (unit' := unit') hop h,
      foldMapAt_layer_fuse φ (unit' := unit') hop h]

/-- `foldMapAt_eff_fuse` at a statement. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmt_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f : (fam : EffFam) → EffSelfCarrier Op fam → List Nat → M}
    {g : (fam : EffFam) → EffSelfCarrier Op fam → N}
    (h : ∀ fam n q, φ (f fam n q) = g fam n) (e : Stmt Op) (p : List Nat) :
    φ (foldMapAt_stmt unit op p e (f .eff) (f .stmt) (f .stmts) (f .effs) (f .action) (f .layer)
        (f .layers)) =
      foldMap_stmt unit' op' e (g .eff) (g .stmt) (g .stmts) (g .effs) (g .action) (g .layer)
        (g .layers) := by
  cases e <;>
    simp only [foldMapAt_stmt, foldMap_stmt, hop, h,
      foldMapAt_eff_fuse φ (unit' := unit') hop h, foldMapAt_stmts_fuse φ (unit' := unit') hop h]

/-- `foldMapAt_eff_fuse` at a statement list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmts_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f : (fam : EffFam) → EffSelfCarrier Op fam → List Nat → M}
    {g : (fam : EffFam) → EffSelfCarrier Op fam → N}
    (h : ∀ fam n q, φ (f fam n q) = g fam n) (e : Stmts Op) (p : List Nat) :
    φ (foldMapAt_stmts unit op p e (f .eff) (f .stmt) (f .stmts) (f .effs) (f .action) (f .layer)
        (f .layers)) =
      foldMap_stmts unit' op' e (g .eff) (g .stmt) (g .stmts) (g .effs) (g .action) (g .layer)
        (g .layers) := by
  cases e <;>
    simp only [foldMapAt_stmts, foldMap_stmts, hop, h,
      foldMapAt_stmt_fuse φ (unit' := unit') hop h, foldMapAt_stmts_fuse φ (unit' := unit') hop h]

/-- `foldMapAt_eff_fuse` at a race's entrants. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_effs_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f : (fam : EffFam) → EffSelfCarrier Op fam → List Nat → M}
    {g : (fam : EffFam) → EffSelfCarrier Op fam → N}
    (h : ∀ fam n q, φ (f fam n q) = g fam n) (e : Effs Op) (p : List Nat) :
    φ (foldMapAt_effs unit op p e (f .eff) (f .stmt) (f .stmts) (f .effs) (f .action) (f .layer)
        (f .layers)) =
      foldMap_effs unit' op' e (g .eff) (g .stmt) (g .stmts) (g .effs) (g .action) (g .layer)
        (g .layers) := by
  cases e <;>
    simp only [foldMapAt_effs, foldMap_effs, hop, h,
      foldMapAt_eff_fuse φ (unit' := unit') hop h, foldMapAt_effs_fuse φ (unit' := unit') hop h]

/-- `foldMapAt_eff_fuse` at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_action_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f : (fam : EffFam) → EffSelfCarrier Op fam → List Nat → M}
    {g : (fam : EffFam) → EffSelfCarrier Op fam → N}
    (h : ∀ fam n q, φ (f fam n q) = g fam n) (e : ActionTerm Op) (p : List Nat) :
    φ (foldMapAt_action unit op p e (f .eff) (f .stmt) (f .stmts) (f .effs) (f .action) (f .layer)
        (f .layers)) =
      foldMap_action unit' op' e (g .eff) (g .stmt) (g .stmts) (g .effs) (g .action) (g .layer)
        (g .layers) := by
  cases e <;>
    simp only [foldMapAt_action, foldMap_action, hop, h,
      foldMapAt_eff_fuse φ (unit' := unit') hop h, foldMapAt_effs_fuse φ (unit' := unit') hop h]

/-- `foldMapAt_eff_fuse` at a layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layer_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f : (fam : EffFam) → EffSelfCarrier Op fam → List Nat → M}
    {g : (fam : EffFam) → EffSelfCarrier Op fam → N}
    (h : ∀ fam n q, φ (f fam n q) = g fam n) (e : LayerTerm Op) (p : List Nat) :
    φ (foldMapAt_layer unit op p e (f .eff) (f .stmt) (f .stmts) (f .effs) (f .action) (f .layer)
        (f .layers)) =
      foldMap_layer unit' op' e (g .eff) (g .stmt) (g .stmts) (g .effs) (g .action) (g .layer)
        (g .layers) := by
  cases e <;>
    simp only [foldMapAt_layer, foldMap_layer, hop, h,
      foldMapAt_eff_fuse φ (unit' := unit') hop h, foldMapAt_layer_fuse φ (unit' := unit') hop h,
      foldMapAt_layers_fuse φ (unit' := unit') hop h]

/-- `foldMapAt_eff_fuse` at a layer list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layers_fuse (φ : M → N) {unit : M} {op : M → M → M} {unit' : N}
    {op' : N → N → N} (hop : ∀ a b, φ (op a b) = op' (φ a) (φ b))
    {f : (fam : EffFam) → EffSelfCarrier Op fam → List Nat → M}
    {g : (fam : EffFam) → EffSelfCarrier Op fam → N}
    (h : ∀ fam n q, φ (f fam n q) = g fam n) (e : LayerTerms Op) (p : List Nat) :
    φ (foldMapAt_layers unit op p e (f .eff) (f .stmt) (f .stmts) (f .effs) (f .action) (f .layer)
        (f .layers)) =
      foldMap_layers unit' op' e (g .eff) (g .stmt) (g .stmts) (g .effs) (g .action) (g .layer)
        (g .layers) := by
  cases e <;>
    simp only [foldMapAt_layers, foldMap_layers, hop, h,
      foldMapAt_layer_fuse φ (unit' := unit') hop h,
      foldMapAt_layers_fuse φ (unit' := unit') hop h]

end

end Fuse

end Effect4.Program

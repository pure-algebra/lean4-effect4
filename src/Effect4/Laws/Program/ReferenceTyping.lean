import Effect4.Program.Typing
import Effect4.Laws.Program.ReferenceExpansion

/-!
C4: expanding layer references leaves the whole-program type checker unchanged
when the original references are well formed. The operation alphabet and signature
are arbitrary.

Proof graph:
* The seven mutual `*_expandRound_eq_self` lemmas use structural induction to
  show that one expansion round fixes syntax with no reference sites.
* `expandRefs_eq_self_of_refSites_nil` reduces the expansion fold to that round;
  `layerRefsWF_of_refSites_nil` discharges well-formedness of reference-free syntax.
* `typeOfProgram_eq_if_refsWF` is the checker's equation. The checker's second test, that
  the expansion has no reference site, follows from its first, that the references are
  well formed (`expanded_refs_nil_of_wf`, `Laws/Program/ReferenceExpansion.lean`).
* `typeOfProgram_expandRefs` reads the equation at the program and at its expansion,
  which the first two facts fix. Its one premise is the well-formed references.

The proved judgment is equality of `typeOfProgram` results. Neither answer is shown to
be a type. Runtime behavior and layer sharing are separate C4 obligations.

Imports. This file imports `Laws/Program/ReferenceExpansion.lean` for the top theorem.
Keep `aesop`, and with it the `batteries` package, out of that module's imports and out of
the imports of `PathFold.lean` and `PathOrder.lean`. With `batteries` imported here, its
linter `unnecessarySeqFocus` refuses the last line of `action_expandRound_eq_self` below,
and the file does not build (`docs/research/2026-10-06-seat-REFS-receipt.md`, finding F1).
The limit goes when the seven `*_expandRound_eq_self` proofs are rewritten.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Effect4.Program
open Effect4.Program

set_option hygiene false in
scoped macro "close_ref_free" : tactic => `(tactic|
  (first
  | apply eff_expandRound_eq_self
  | apply stmts_expandRound_eq_self
  | apply stmt_expandRound_eq_self
  | apply effs_expandRound_eq_self
  | apply action_expandRound_eq_self
  | apply layer_expandRound_eq_self
  | apply layers_expandRound_eq_self) <;> solve_by_elim [And.left, And.right])

mutual
  theorem eff_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Eff Op) (path : List Nat) (h : node.refSites path = []) :
      Eff.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_eff, List.nil_append, Eff.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_eff, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, Eff.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem stmts_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Stmts Op) (path : List Nat) (h : node.refSites path = []) :
      Stmts.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_stmts, List.nil_append, Stmts.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_stmts, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, Stmts.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem stmt_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Stmt Op) (path : List Nat) (h : node.refSites path = []) :
      Stmt.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_stmt, List.nil_append, Stmt.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_stmt, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, Stmt.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem effs_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Effs Op) (path : List Nat) (h : node.refSites path = []) :
      Effs.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_effs, List.nil_append, Effs.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_effs, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, Effs.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem action_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : ActionTerm Op) (path : List Nat) (h : node.refSites path = []) :
      ActionTerm.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_action, List.nil_append, ActionTerm.refSites]
    all_goals simp only [cata_action, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, ActionTerm.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem layer_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : LayerTerm Op) (path : List Nat) (h : node.refSites path = []) :
      LayerTerm.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_layer, LayerTerm.refSite, List.nil_append, LayerTerm.refSites, List.append_eq_nil_iff,
      List.cons_ne_nil]
    all_goals simp only [cata_layer, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, LayerTerm.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem layers_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : LayerTerms Op) (path : List Nat) (h : node.refSites path = []) :
      LayerTerms.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_layers, List.nil_append, LayerTerms.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_layers, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, LayerTerms.expandRound]
    all_goals congr 1 <;> close_ref_free
end

theorem expandRefs_eq_self_of_refSites_nil {Op : Type} (p : Eff Op)
    (h : p.refSites [] = []) : p.expandRefs = p := by
  simp only [Eff.expandRefs, h, List.length_nil, Nat.zero_add, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_cons, List.foldl_nil]
  exact eff_expandRound_eq_self _ p [] h

theorem layerRefsWF_of_refSites_nil {Op : Type} (p : Eff Op)
    (h : p.refSites [] = []) : p.layerRefsWF = true := by
  simp [Eff.layerRefsWF, h]

/-- **The checker's equation.** The whole-program checker makes two tests before it types the
expansion (`typeOfProgram`, `Program/Typing.lean`): the references are well formed, and the
expansion has no reference site. The second follows from the first (`expanded_refs_nil_of_wf`,
`Laws/Program/ReferenceExpansion.lean`). So the checker answers the structural type of the
expansion exactly when the references are well formed. The equation does not say that the answer
is a type. Its consumers are `typeOfProgram_expandRefs` below and `checkTypedProgram_of_hasTy`
(`Laws/Program/CheckedTyping.lean`). -/
theorem typeOfProgram_eq_if_refsWF {Op : Type} (sig : Signature Op) (p : Eff Op) :
    typeOfProgram sig p = if p.layerRefsWF then typeOf sig p.expandRefs else none := by
  unfold typeOfProgram
  cases hwf : p.layerRefsWF with
  | false => rfl
  | true =>
    rw [expanded_refs_nil_of_wf p hwf]
    rfl

/-- C4 typing equation with its one premise, well-formed original layer references: the
checker's answer on the expanded program is its answer on the program. The expansion has no
reference site (`expanded_refs_nil_of_wf`), so it is well formed and its own expansion. The
theorem does not say that either answer is a type. The premise stays: the checker refuses a
program with a forward reference, and it types that program's expansion
(`Test/Program/ReferenceExpansion.lean`, `forward_needs_wellFormed`). -/
@[semantics "initial-algebras-folds" (requirement := R5)]
theorem typeOfProgram_expandRefs {Op : Type} (sig : Signature Op) (p : Eff Op)
    (hwf : p.layerRefsWF = true) :
    typeOfProgram sig p.expandRefs = typeOfProgram sig p := by
  have hrefs := expanded_refs_nil_of_wf p hwf
  rw [typeOfProgram_eq_if_refsWF, typeOfProgram_eq_if_refsWF, hwf,
    layerRefsWF_of_refSites_nil p.expandRefs hrefs,
    expandRefs_eq_self_of_refSites_nil p.expandRefs hrefs]

/-! ## A subterm's expansion (decisions row 153)

`expandRefs` runs its rounds on the whole program. `Eff.expandIn root e` runs the same rounds on
a subterm `e`, against `root`'s layers, so the whole program's expansion is `expandIn root root`
(`Eff.expandIn_self`, by definition) and a reference-free subterm is its own expansion
(`Eff.expandIn_eq_self`). The typed state checks a point's node through it
(`Typed/Admission.lean`, `PointTyped`): a program with references is checked as its expansion
(`typeOfProgram`) and runs as written, each reference redirected to its target
(`Laws/Program/DenoteR.lean`, `denoteLayer_ref_redirect`). -/

/-- The subterm `e` after the rounds `root`'s expansion runs. -/
def Eff.expandIn {Op : Type} (root e : Eff Op) : Eff Op :=
  let orig := Node.eff root
  (List.range ((root.refSites []).length + 1)).foldl (fun acc _ => Eff.expandRound orig acc) e

/-- A layer subterm after the rounds `root`'s expansion runs. -/
def LayerTerm.expandIn {Op : Type} (root : Eff Op) (l : LayerTerm Op) : LayerTerm Op :=
  let orig := Node.eff root
  (List.range ((root.refSites []).length + 1)).foldl (fun acc _ => LayerTerm.expandRound orig acc) l

/-- The whole program's expansion is its own subterm's. -/
theorem Eff.expandIn_self {Op : Type} (root : Eff Op) : Eff.expandIn root root = root.expandRefs :=
  rfl

theorem foldl_expandRound_eq_self {Op : Type} (orig : Node Op) (e : Eff Op) (p : List Nat)
    (h : e.refSites p = []) :
    ∀ xs : List Nat, xs.foldl (fun acc _ => Eff.expandRound orig acc) e = e
  | [] => rfl
  | _ :: xs => by
    rw [List.foldl_cons, eff_expandRound_eq_self orig e p h]
    exact foldl_expandRound_eq_self orig e p h xs

theorem foldl_layer_expandRound_eq_self {Op : Type} (orig : Node Op) (l : LayerTerm Op)
    (p : List Nat) (h : l.refSites p = []) :
    ∀ xs : List Nat, xs.foldl (fun acc _ => LayerTerm.expandRound orig acc) l = l
  | [] => rfl
  | _ :: xs => by
    rw [List.foldl_cons, layer_expandRound_eq_self orig l p h]
    exact foldl_layer_expandRound_eq_self orig l p h xs

/-- A reference-free subterm is its own expansion. -/
theorem Eff.expandIn_eq_self {Op : Type} (root e : Eff Op) (p : List Nat) (h : e.refSites p = []) :
    Eff.expandIn root e = e :=
  foldl_expandRound_eq_self _ e p h _

/-- A reference-free layer is its own expansion. -/
theorem LayerTerm.expandIn_eq_self {Op : Type} (root : Eff Op) (l : LayerTerm Op) (p : List Nat)
    (h : l.refSites p = []) : LayerTerm.expandIn root l = l :=
  foldl_layer_expandRound_eq_self _ l p h _

theorem foldl_expandRound_acquireRelease {Op : Type} (orig : Node Op) (a r : Eff Op) :
    ∀ xs : List Nat, xs.foldl (fun acc _ => Eff.expandRound orig acc) (.acquireRelease a r) =
      .acquireRelease (xs.foldl (fun acc _ => Eff.expandRound orig acc) a)
        (xs.foldl (fun acc _ => Eff.expandRound orig acc) r)
  | [] => rfl
  | _ :: xs => foldl_expandRound_acquireRelease orig _ _ xs

/-- Expansion distributes over `acquireRelease`. -/
theorem Eff.expandIn_acquireRelease {Op : Type} (root a r : Eff Op) :
    Eff.expandIn root (.acquireRelease a r) =
      .acquireRelease (Eff.expandIn root a) (Eff.expandIn root r) :=
  foldl_expandRound_acquireRelease _ a r _

end Effect4.Program

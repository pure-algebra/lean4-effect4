import Effect4.Program.Typing

/-!
C4: expanding layer references leaves the whole-program type checker unchanged
when the original references are well formed and the expansion has no reference
sites. The operation alphabet and signature are arbitrary.

Proof graph:
* The seven mutual `*_expandRound_eq_self` lemmas use structural induction to
  show that one expansion round fixes syntax with no reference sites.
* `expandRefs_eq_self_of_refSites_nil` reduces the expansion fold to that round;
  `layerRefsWF_of_refSites_nil` discharges well-formedness of reference-free syntax.
* `typeOfProgram_expandRefs` applies those facts to the expanded program and
  unfolds the existing whole-program checker, preserving both dispatch premises.

The proved judgment is equality of `typeOfProgram` results. Runtime behavior and
layer sharing are separate C4 obligations.
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
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, Eff.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_eff, cata_stmts, cata_stmt, cata_effs, cata_action, cata_layer, cata_layers, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, Eff.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem stmts_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Stmts Op) (path : List Nat) (h : node.refSites path = []) :
      Stmts.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, Stmts.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_eff, cata_stmts, cata_stmt, cata_effs, cata_action, cata_layer, cata_layers, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, Stmts.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem stmt_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Stmt Op) (path : List Nat) (h : node.refSites path = []) :
      Stmt.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, Stmt.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_eff, cata_stmts, cata_stmt, cata_effs, cata_action, cata_layer, cata_layers, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, Stmt.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem effs_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Effs Op) (path : List Nat) (h : node.refSites path = []) :
      Effs.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, Effs.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_eff, cata_stmts, cata_stmt, cata_effs, cata_action, cata_layer, cata_layers, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, Effs.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem action_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : ActionTerm Op) (path : List Nat) (h : node.refSites path = []) :
      ActionTerm.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, ActionTerm.refSites]
    all_goals simp only [cata_eff, cata_stmts, cata_stmt, cata_effs, cata_action, cata_layer, cata_layers, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, ActionTerm.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem layer_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : LayerTerm Op) (path : List Nat) (h : node.refSites path = []) :
      LayerTerm.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, LayerTerm.refSites, List.append_eq_nil_iff,
      List.cons_ne_nil]
    all_goals simp only [cata_eff, cata_stmts, cata_stmt, cata_effs, cata_action, cata_layer, cata_layers, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, LayerTerm.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem layers_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : LayerTerms Op) (path : List Nat) (h : node.refSites path = []) :
      LayerTerms.expandRound orig node = node := by
    cases node <;> simp_all only [foldMapAt_eff, foldMapAt_stmts, foldMapAt_stmt, foldMapAt_effs, foldMapAt_action, foldMapAt_layer, foldMapAt_layers, LayerTerm.refSite, List.nil_append, List.append_nil, LayerTerms.refSites, List.append_eq_nil_iff]
    all_goals simp only [cata_eff, cata_stmts, cata_stmt, cata_effs, cata_action, cata_layer, cata_layers, expandAlgebra, EffAlgebra.onRef, EffAlgebra.id, LayerTerms.expandRound]
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

/-- C4 typing equation with the exact two dispatch premises: well-formed original
layer references and no remaining reference sites after expansion. -/
theorem typeOfProgram_expandRefs {Op : Type} (sig : Signature Op) (p : Eff Op)
    (hwf : p.layerRefsWF = true)
    (hempty : (p.expandRefs.refSites []).isEmpty = true) :
    typeOfProgram sig p.expandRefs = typeOfProgram sig p := by
  have hrefs : p.expandRefs.refSites [] = [] := List.isEmpty_iff.mp hempty
  have hfixed := expandRefs_eq_self_of_refSites_nil p.expandRefs hrefs
  have hwf' := layerRefsWF_of_refSites_nil p.expandRefs hrefs
  simp [typeOfProgram, hwf, hempty, hfixed, hwf']

#check (typeOfProgram_expandRefs :
  ∀ {Op : Type} (sig : Signature Op) (p : Eff Op),
    p.layerRefsWF = true → (p.expandRefs.refSites []).isEmpty = true →
    typeOfProgram sig p.expandRefs = typeOfProgram sig p)

end Effect4.Program

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
local macro "close_ref_free" : tactic => `(tactic|
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
    cases node <;> simp_all only [Eff.refSites, List.append_eq_nil_iff]
    all_goals simp only [Eff.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem stmts_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Stmts Op) (path : List Nat) (h : node.refSites path = []) :
      Stmts.expandRound orig node = node := by
    cases node <;> simp_all only [Stmts.refSites, List.append_eq_nil_iff]
    all_goals simp only [Stmts.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem stmt_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Stmt Op) (path : List Nat) (h : node.refSites path = []) :
      Stmt.expandRound orig node = node := by
    cases node <;> simp_all only [Stmt.refSites, List.append_eq_nil_iff]
    all_goals simp only [Stmt.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem effs_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : Effs Op) (path : List Nat) (h : node.refSites path = []) :
      Effs.expandRound orig node = node := by
    cases node <;> simp_all only [Effs.refSites, List.append_eq_nil_iff]
    all_goals simp only [Effs.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem action_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : ActionTerm Op) (path : List Nat) (h : node.refSites path = []) :
      ActionTerm.expandRound orig node = node := by
    cases node <;> simp_all only [ActionTerm.refSites]
    all_goals simp only [ActionTerm.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem layer_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : LayerTerm Op) (path : List Nat) (h : node.refSites path = []) :
      LayerTerm.expandRound orig node = node := by
    cases node <;> simp_all only [LayerTerm.refSites, List.append_eq_nil_iff,
      List.cons_ne_nil]
    all_goals simp only [LayerTerm.expandRound]
    all_goals congr 1 <;> close_ref_free

  theorem layers_expandRound_eq_self {Op : Type} (orig : Node Op)
      (node : LayerTerms Op) (path : List Nat) (h : node.refSites path = []) :
      LayerTerms.expandRound orig node = node := by
    cases node <;> simp_all only [LayerTerms.refSites, List.append_eq_nil_iff]
    all_goals simp only [LayerTerms.expandRound]
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

#print axioms eff_expandRound_eq_self
#print axioms stmts_expandRound_eq_self
#print axioms stmt_expandRound_eq_self
#print axioms effs_expandRound_eq_self
#print axioms action_expandRound_eq_self
#print axioms layer_expandRound_eq_self
#print axioms layers_expandRound_eq_self
#print axioms expandRefs_eq_self_of_refSites_nil
#print axioms layerRefsWF_of_refSites_nil
#print axioms typeOfProgram_expandRefs

#check (typeOfProgram_expandRefs :
  ∀ {Op : Type} (sig : Signature Op) (p : Eff Op),
    p.layerRefsWF = true → (p.expandRefs.refSites []).isEmpty = true →
    typeOfProgram sig p.expandRefs = typeOfProgram sig p)

end Effect4.Program

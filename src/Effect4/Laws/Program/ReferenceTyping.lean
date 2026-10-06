import Effect4.Program.Typing
import Effect4.Laws.Program.ReferenceExpansion

/-!
C4: expanding layer references leaves the whole-program type checker unchanged
when the original references are well formed. The operation alphabet and signature
are arbitrary.

Proof graph:
* A substitution of the references fixes syntax with no reference site, at the seven sorts
  (`onRef_eq_self_eff` and its six siblings): one structural recursion over the sorts. The
  seven `*_expandRound_eq_self` lemmas are its instances at the expansion algebra: one
  expansion round fixes syntax with no reference sites.
* `expandRefs_eq_self_of_refSites_nil` reduces the expansion fold to that round;
  `layerRefsWF_of_refSites_nil` discharges well-formedness of reference-free syntax.
* `typeOfProgram_eq_if_refsWF` is the checker's equation, and it is the checker's definition
  (`typeOfProgram`, `Program/Typing.lean`). The checker tests the references' formation only.
  Until 2026-10-06 it made a second test, that the expansion has no reference site. That test
  followed from the first (`expanded_refs_nil_of_wf`, `Laws/Program/ReferenceExpansion.lean`),
  and decisions row 273 removed it.
* `typeOfProgram_expandRefs` reads the equation at the program and at its expansion. The
  expansion has no reference site (`expanded_refs_nil_of_wf`), so the first two facts fix it.
  Its one premise is the well-formed references.

The proved judgment is equality of `typeOfProgram` results. Neither answer is shown to
be a type. Runtime behavior and layer sharing are separate C4 obligations.
-/

set_option autoImplicit false

namespace Effect4.Program
open Effect4.Program

/-! ## A substitution fixes syntax with no reference site

The second law of the generated folds under a substitution of the references. The first is the
law of the reference sites (`Laws/Program/ReferenceExpansion.lean`), and both read the algebra
under its reducible name `refAlgebra`. The seven statements are one structural recursion over
the seven sorts. Each proof takes its arms from the sort, which are the arms of its fold, and one
`simp only` call closes them all. The call unfolds the two folds at the constructor. It reads the
premise as one fact for each child, and it rewrites each child by the statement at the child's
sort and path. A child's path is the node's path with the child's index, so the statements at
the indices `0`, `1` and `2` cover every arm. At `ref` the premise is false. -/

mutual
/-- A substitution fixes an `Eff` with no reference site. A step of `eff_expandRound_eq_self`. -/
private theorem onRef_eq_self_eff {Op : Type} (f : List Nat → LayerTerm Op) (q : List Nat)
    (node : Eff Op) :
    foldMapAt_eff [] (· ++ ·) q node (f_layer := LayerTerm.refSite) = [] →
      cata_eff (refAlgebra f) node = node := by
  cases node <;> simp +contextual only [foldMapAt_eff, cata_eff, EffAlgebra.id, List.nil_append,
    List.append_eq_nil_iff, implies_true, onRef_eq_self_eff f (q ++ [0]),
    onRef_eq_self_eff f (q ++ [1]), onRef_eq_self_eff f (q ++ [2]),
    onRef_eq_self_stmts f (q ++ [0]), onRef_eq_self_action f (q ++ [0]),
    onRef_eq_self_layer f (q ++ [0])]

/-- A substitution fixes a `Stmt` with no reference site. -/
private theorem onRef_eq_self_stmt {Op : Type} (f : List Nat → LayerTerm Op) (q : List Nat)
    (node : Stmt Op) :
    foldMapAt_stmt [] (· ++ ·) q node (f_layer := LayerTerm.refSite) = [] →
      cata_stmt (refAlgebra f) node = node := by
  cases node <;> simp +contextual only [foldMapAt_stmt, cata_stmt, EffAlgebra.id, List.nil_append,
    List.append_eq_nil_iff, implies_true, onRef_eq_self_eff f (q ++ [0]),
    onRef_eq_self_stmts f (q ++ [0]), onRef_eq_self_stmts f (q ++ [1])]

/-- A substitution fixes a `Stmts` with no reference site. -/
private theorem onRef_eq_self_stmts {Op : Type} (f : List Nat → LayerTerm Op) (q : List Nat)
    (node : Stmts Op) :
    foldMapAt_stmts [] (· ++ ·) q node (f_layer := LayerTerm.refSite) = [] →
      cata_stmts (refAlgebra f) node = node := by
  cases node <;> simp +contextual only [foldMapAt_stmts, cata_stmts, EffAlgebra.id,
    List.nil_append, List.append_eq_nil_iff, implies_true, onRef_eq_self_stmt f (q ++ [0]),
    onRef_eq_self_stmts f (q ++ [1])]

/-- A substitution fixes an `Effs` with no reference site. -/
private theorem onRef_eq_self_effs {Op : Type} (f : List Nat → LayerTerm Op) (q : List Nat)
    (node : Effs Op) :
    foldMapAt_effs [] (· ++ ·) q node (f_layer := LayerTerm.refSite) = [] →
      cata_effs (refAlgebra f) node = node := by
  cases node <;> simp +contextual only [foldMapAt_effs, cata_effs, EffAlgebra.id, List.nil_append,
    List.append_eq_nil_iff, implies_true, onRef_eq_self_eff f (q ++ [0]),
    onRef_eq_self_effs f (q ++ [1])]

/-- A substitution fixes an `ActionTerm` with no reference site. -/
private theorem onRef_eq_self_action {Op : Type} (f : List Nat → LayerTerm Op) (q : List Nat)
    (node : ActionTerm Op) :
    foldMapAt_action [] (· ++ ·) q node (f_layer := LayerTerm.refSite) = [] →
      cata_action (refAlgebra f) node = node := by
  cases node <;> simp +contextual only [foldMapAt_action, cata_action, EffAlgebra.id,
    List.nil_append, implies_true, onRef_eq_self_eff f (q ++ [0]),
    onRef_eq_self_effs f (q ++ [0])]

/-- A substitution fixes a `LayerTerm` with no reference site. A reference has a site, so its
premise is false. A step of `layer_expandRound_eq_self`. -/
private theorem onRef_eq_self_layer {Op : Type} (f : List Nat → LayerTerm Op) (q : List Nat)
    (node : LayerTerm Op) :
    foldMapAt_layer [] (· ++ ·) q node (f_layer := LayerTerm.refSite) = [] →
      cata_layer (refAlgebra f) node = node := by
  cases node <;> simp +contextual only [foldMapAt_layer, cata_layer, EffAlgebra.id,
    LayerTerm.refSite, List.nil_append, List.append_eq_nil_iff, implies_true, reduceCtorEq,
    false_implies, onRef_eq_self_eff f (q ++ [0]), onRef_eq_self_layer f (q ++ [0]),
    onRef_eq_self_layer f (q ++ [1]), onRef_eq_self_layers f (q ++ [0])]

/-- A substitution fixes a `LayerTerms` with no reference site. -/
private theorem onRef_eq_self_layers {Op : Type} (f : List Nat → LayerTerm Op) (q : List Nat)
    (node : LayerTerms Op) :
    foldMapAt_layers [] (· ++ ·) q node (f_layer := LayerTerm.refSite) = [] →
      cata_layers (refAlgebra f) node = node := by
  cases node <;> simp +contextual only [foldMapAt_layers, cata_layers, EffAlgebra.id,
    List.nil_append, List.append_eq_nil_iff, implies_true, onRef_eq_self_layer f (q ++ [0]),
    onRef_eq_self_layers f (q ++ [1])]
end

/-- One expansion round fixes a program with no reference site. -/
theorem eff_expandRound_eq_self {Op : Type} (orig : Node Op)
    (node : Eff Op) (path : List Nat) (h : node.refSites path = []) :
    Eff.expandRound orig node = node :=
  onRef_eq_self_eff _ path node h

theorem stmts_expandRound_eq_self {Op : Type} (orig : Node Op)
    (node : Stmts Op) (path : List Nat) (h : node.refSites path = []) :
    Stmts.expandRound orig node = node :=
  onRef_eq_self_stmts _ path node h

theorem stmt_expandRound_eq_self {Op : Type} (orig : Node Op)
    (node : Stmt Op) (path : List Nat) (h : node.refSites path = []) :
    Stmt.expandRound orig node = node :=
  onRef_eq_self_stmt _ path node h

theorem effs_expandRound_eq_self {Op : Type} (orig : Node Op)
    (node : Effs Op) (path : List Nat) (h : node.refSites path = []) :
    Effs.expandRound orig node = node :=
  onRef_eq_self_effs _ path node h

theorem action_expandRound_eq_self {Op : Type} (orig : Node Op)
    (node : ActionTerm Op) (path : List Nat) (h : node.refSites path = []) :
    ActionTerm.expandRound orig node = node :=
  onRef_eq_self_action _ path node h

/-- One expansion round fixes a layer with no reference site. -/
theorem layer_expandRound_eq_self {Op : Type} (orig : Node Op)
    (node : LayerTerm Op) (path : List Nat) (h : node.refSites path = []) :
    LayerTerm.expandRound orig node = node :=
  onRef_eq_self_layer _ path node h

theorem layers_expandRound_eq_self {Op : Type} (orig : Node Op)
    (node : LayerTerms Op) (path : List Nat) (h : node.refSites path = []) :
    LayerTerms.expandRound orig node = node :=
  onRef_eq_self_layers _ path node h

theorem expandRefs_eq_self_of_refSites_nil {Op : Type} (p : Eff Op)
    (h : p.refSites [] = []) : p.expandRefs = p := by
  simp only [Eff.expandRefs, h, List.length_nil, Nat.zero_add, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_cons, List.foldl_nil]
  exact eff_expandRound_eq_self _ p [] h

theorem layerRefsWF_of_refSites_nil {Op : Type} (p : Eff Op)
    (h : p.refSites [] = []) : p.layerRefsWF = true := by
  simp [Eff.layerRefsWF, h]

/-- **The checker's equation.** The whole-program checker tests one thing before it types the
expansion (`typeOfProgram`, `Program/Typing.lean`): the references are well formed. So it
answers the structural type of the expansion exactly when the references are well formed. The
equation is the checker's definition, so its proof is `rfl`. Until 2026-10-06 the checker also
tested that the expansion has no reference site. That test followed from the first
(`expanded_refs_nil_of_wf`, `Laws/Program/ReferenceExpansion.lean`), and it is gone (decisions
row 273). The equation does not say that the answer is a type. Its consumers are
`typeOfProgram_expandRefs` below, `TypedProgram.hasTy` and `checkTypedProgram_of_hasTy`
(`Laws/Program/CheckedTyping.lean`), and `typeOfProgram_looped` (`Laws/Program/TypedRun.lean`). -/
theorem typeOfProgram_eq_if_refsWF {Op : Type} (sig : Signature Op) (p : Eff Op) :
    typeOfProgram sig p = if p.layerRefsWF then typeOf sig p.expandRefs else none := rfl

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

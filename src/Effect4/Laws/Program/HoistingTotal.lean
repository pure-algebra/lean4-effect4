import Effect4.Laws.Program.Hoisting

/-!
# Hoisting succeeds when every referenced target exists

Frozen statement, for arbitrary operation alphabet `Op`:

If every `(site, target)` in `root.refSites []` has a layer at `target` in
`Node.eff root`, then there exist `main` and `declarations` with
`root.hoistAll = .ok (main, declarations)`. In particular, `root.layerRefsWF = true`
implies this success equation. Neither statement assumes successful hoisting.

Proof route: replacing a later layer retains the existence of every earlier
layer, including an enclosing layer. This invariant follows the descending
target list. Compose the result with the existing inverse to recover the
original program. These are structural facts, not typing or host execution.
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

open scoped Effect4.Program.Path

private theorem captureFold_exists (targets : List (List Nat))
    (ordered : targets.Pairwise (fun a b => Path.lt b a = true))
    (root : Eff Op) (history : List (List Nat × LayerTerm Op))
    (targetsExist : ∀ target ∈ targets, ∃ layer, (Node.eff root).layerAt target = some layer) :
    ∃ main declarations,
      targets.foldlM (init := (root, history))
        (fun (acc, decls) target =>
          match (Node.eff acc).layerAt target,
              (Node.eff acc).replaceLayerAt target (.ref target) with
          | some layer, some (Node.eff next) => .ok (next, (target, layer) :: decls)
          | _, _ => .error target) =
        (Except.ok (main, declarations) : Except (List Nat) _) := by
  induction targets generalizing root history with
  | nil => exact ⟨root, history, rfl⟩
  | cons target targets ih =>
      obtain ⟨old, found⟩ := targetsExist target (by simp)
      obtain ⟨next, updated⟩ := Node.replaceLayerAt_eff_exists found (.ref target)
      obtain ⟨before, tailOrdered⟩ := List.pairwise_cons.mp ordered
      have remainingExist : ∀ earlier ∈ targets,
          ∃ layer, (Node.eff next).layerAt earlier = some layer := by
        intro earlier member
        obtain ⟨layer, lookup⟩ := targetsExist earlier (List.mem_cons_of_mem _ member)
        exact Node.layerAt_exists_before_replaceLayerAt (before earlier member) lookup updated
      obtain ⟨main, declarations, completed⟩ :=
        ih tailOrdered next ((target, old) :: history) remainingExist
      refine ⟨main, declarations, ?_⟩
      simpa only [List.foldlM_cons, found, updated, Bind.bind, Except.bind] using completed

/-- Hoisting succeeds whenever every referenced target names an existing layer.
This requires neither reference ordering nor exclusion of self-references; those
are stronger admission properties, not prerequisites for capturing the tree. -/
theorem Eff.hoistAll_exists_of_targets (root : Eff Op)
    (targetsExist : ∀ site target, (site, target) ∈ root.refSites [] →
      ∃ layer, (Node.eff root).layerAt target = some layer) :
    ∃ main declarations, root.hoistAll = .ok (main, declarations) := by
  have unique : root.refTargets.Nodup :=
    Path.sortBy_nodup Path.declBefore (Path.eraseDups_nodup _)
  have ordered := Path.sortBy_pairwise (fun a b => Path.lt b a)
    (fun _ _ _ hab hbc => Path.lt_trans hbc hab)
    (fun a b hne => (Path.lt_total hne).symm) unique
  apply captureFold_exists _ ordered root []
  intro target member
  have inTargets := (Path.sortBy_perm (fun a b => Path.lt b a) root.refTargets).mem_iff.mp member
  have inDistinct := (Path.sortBy_perm Path.declBefore
    ((root.refSites []).map Prod.snd).eraseDups).mem_iff.mp inTargets
  have inSites := List.mem_eraseDups.mp inDistinct
  obtain ⟨⟨site, named⟩, atSite, same⟩ := List.mem_map.mp inSites
  cases same
  exact targetsExist site named atSite

/-- Every well-formed reference program has a successful hoisted representation. -/
theorem Eff.hoistAll_exists (root : Eff Op) (valid : root.layerRefsWF = true) :
    ∃ main declarations, root.hoistAll = .ok (main, declarations) := by
  apply root.hoistAll_exists_of_targets
  intro site target member
  have admitted := List.all_eq_true.mp valid (site, target) member
  cases lookup : (Node.eff root).layerAt target with
  | none => simp [lookup] at admitted
  | some layer => exact ⟨layer, rfl⟩

/-- Well-formed references admit a hoist whose restoration recovers the same tree.
This composes totality with the existing structural inverse, preserving sharing. -/
theorem Eff.hoistAll_restoreAll (root : Eff Op) (valid : root.layerRefsWF = true) :
    ∃ main declarations, root.hoistAll = .ok (main, declarations) ∧
      main.restoreAll declarations = some root := by
  obtain ⟨main, declarations, hoisted⟩ := root.hoistAll_exists valid
  exact ⟨main, declarations, hoisted, Eff.restoreAll_hoistAll hoisted⟩

end Effect4.Program

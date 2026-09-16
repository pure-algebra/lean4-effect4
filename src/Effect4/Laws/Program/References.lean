import Effect4.Program.Refs

/-!
Reversible layer updates over the existing addressed program tree.

Proof graph: the local child lookup/update laws lift by induction on a path to
layer lookup/update laws. These supply the single-update algebra needed by the
module hoist/restore proof; they do not yet establish the multi-update fold or
the module printer/reader round trip. No executable tree operation is changed.
-/

set_option autoImplicit false

namespace Effect4.Program.Node

variable {Op : Type}

/-- A successful child update exposes the inserted child, retains the parent's
node sort, and can be reversed by putting back the old child. -/
theorem setChild_spec {node result replacement : Node Op} {index : Nat}
    (updated : node.setChild index replacement = some result) :
    result.child index = some replacement ∧ result.ctorIdx = node.ctorIdx ∧
      ∀ old, node.child index = some old → result.setChild index old = some node := by
  unfold setChild at updated
  split at updated <;> cases updated
  all_goals refine ⟨rfl, rfl, ?_⟩
  all_goals intro old found; cases found; rfl

/-- A child can be replaced by any node of the same sort. -/
theorem setChild_exists {node old replacement : Node Op} {index : Nat}
    (found : node.child index = some old)
    (sameSort : replacement.ctorIdx = old.ctorIdx) :
    ∃ result, node.setChild index replacement = some result := by
  unfold child at found
  split at found <;> cases found
  all_goals cases replacement <;> cases sameSort
  all_goals exact ⟨_, rfl⟩

/-- Layer lookup follows the same first child as layer replacement. -/
theorem layerAt_cons (node : Node Op) (index : Nat) (path : List Nat) :
    node.layerAt (index :: path) = (node.child index).bind (fun next => next.layerAt path) := by
  cases found : node.child index <;> simp [layerAt, at_, found]

/-- A successful layer replacement exposes the inserted layer, retains the root
node sort, and can be reversed with the old layer. No reference well-formedness
or typing premise is needed for this addressed-tree equation. -/
theorem replaceLayerAt_spec {node result : Node Op} {path : List Nat}
    {replacement : LayerTerm Op}
    (updated : node.replaceLayerAt path replacement = some result) :
    result.layerAt path = some replacement ∧ result.ctorIdx = node.ctorIdx ∧
      ∀ old, node.layerAt path = some old → result.replaceLayerAt path old = some node := by
  induction path generalizing node result with
  | nil =>
      cases node <;> cases updated
      refine ⟨rfl, rfl, ?_⟩
      intro old found
      cases found
      rfl
  | cons index path ih =>
      cases first : node.child index with
      | none => simp [replaceLayerAt, first] at updated
      | some next =>
          cases changed : next.replaceLayerAt path replacement with
          | none => simp [replaceLayerAt, first, changed] at updated
          | some next' =>
              have set : node.setChild index next' = some result := by
                simpa [replaceLayerAt, first, changed] using updated
              obtain ⟨newChild, sameSort, undoChild⟩ := setChild_spec set
              obtain ⟨newLayer, _, undoLayer⟩ := ih changed
              refine ⟨?_, sameSort, ?_⟩
              · simpa [layerAt_cons, newChild] using newLayer
              · intro old found
                have oldLayer : next.layerAt path = some old := by
                  simpa [layerAt_cons, first] using found
                simpa [replaceLayerAt, newChild, undoLayer old oldLayer] using undoChild next first

/-- Looking up the replaced path returns the replacement layer. -/
theorem layerAt_replaceLayerAt {node result : Node Op} {path : List Nat}
    {replacement : LayerTerm Op}
    (updated : node.replaceLayerAt path replacement = some result) :
    result.layerAt path = some replacement := (replaceLayerAt_spec updated).1

/-- Restoring the original layer reverses a successful replacement at the same path. -/
theorem replaceLayerAt_restore {node result : Node Op} {path : List Nat}
    {old replacement : LayerTerm Op}
    (found : node.layerAt path = some old)
    (updated : node.replaceLayerAt path replacement = some result) :
    result.replaceLayerAt path old = some node :=
  (replaceLayerAt_spec updated).2.2 old found

/-- Replacing an existing layer always succeeds and retains the root node sort. -/
theorem replaceLayerAt_exists {node : Node Op} {path : List Nat}
    {old : LayerTerm Op} (found : node.layerAt path = some old)
    (replacement : LayerTerm Op) :
    ∃ result, node.replaceLayerAt path replacement = some result ∧
      result.ctorIdx = node.ctorIdx := by
  induction path generalizing node with
  | nil =>
      cases node <;> cases found
      exact ⟨.layer replacement, rfl, rfl⟩
  | cons index path ih =>
      cases first : node.child index with
      | none => simp [layerAt_cons, first] at found
      | some next =>
          have oldLayer : next.layerAt path = some old := by
            simpa [layerAt_cons, first] using found
          obtain ⟨next', changed, sameSort⟩ := ih oldLayer
          obtain ⟨result, set⟩ := setChild_exists first sameSort
          refine ⟨result, ?_, (setChild_spec set).2.1⟩
          simpa [replaceLayerAt, first, changed] using set

/-- A layer update inside a program returns a program, not another node sort. -/
theorem replaceLayerAt_eff_exists {program : Eff Op} {path : List Nat}
    {old : LayerTerm Op} (found : (Node.eff program).layerAt path = some old)
    (replacement : LayerTerm Op) :
    ∃ result, (Node.eff program).replaceLayerAt path replacement = some (.eff result) := by
  obtain ⟨result, updated, sameSort⟩ := replaceLayerAt_exists found replacement
  cases result <;> cases sameSort
  exact ⟨_, updated⟩

end Effect4.Program.Node

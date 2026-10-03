import Effect4.Program.Refs
import Effect4.Laws.Auto.RuleSets

/-!
Reversible updates over the existing addressed program tree.

Concept 7, proposed registry claim `addressed-replacement`: the generated child
lookup/update laws lift by induction on a path to sort-preserving structural
edits. The layer wrapper feeds `Eff.restoreAll_hoistAll` and
`Eff.hoistAll_restoreAll`, the module reader's reconstruction path (R8).
These equations make no typing or execution claim; replacing a referenced
ancestor can invalidate the resulting program's reference graph.
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

/-- Updating one immediate child leaves every different child unchanged. -/
theorem child_setChild_ne {node result replacement : Node Op} {index other : Nat}
    (updated : node.setChild index replacement = some result) (distinct : other ≠ index) :
    result.child other = node.child other := by
  unfold setChild at updated
  split at updated <;> cases updated
  all_goals cases other with
    | zero => aesop
    | succ other =>
      cases other with
      | zero => aesop
      | succ other =>
        cases other with
        | zero => aesop
        | succ other => rfl

/-- Reinstalling an immediate child leaves its parent unchanged. -/
theorem setChild_self {node old : Node Op} {index : Nat}
    (found : node.child index = some old) : node.setChild index old = some node := by
  unfold child at found
  split at found <;> cases found
  all_goals rfl

/-- A second replacement of the same child overwrites the first, including refusals. -/
theorem setChild_overwrite {node result replacement : Node Op} {index : Nat}
    (updated : node.setChild index replacement = some result) (last : Node Op) :
    result.setChild index last = node.setChild index last := by
  unfold setChild at updated
  split at updated <;> cases updated
  all_goals cases last <;> rfl

/-- A child can be replaced by any node of the same sort. -/
theorem setChild_exists {node old replacement : Node Op} {index : Nat}
    (found : node.child index = some old)
    (sameSort : replacement.ctorIdx = old.ctorIdx) :
    ∃ result, node.setChild index replacement = some result := by
  unfold child at found
  split at found <;> cases found
  all_goals cases replacement <;> cases sameSort
  all_goals exact ⟨_, rfl⟩

/-- A successful addressed edit exposes its replacement, preserves the root sort,
and is reversed by restoring the original node. This is the structural witness for
Concept 7's proposed `addressed-replacement` claim, consumed by the layer laws below. -/
theorem replaceAt_spec {node result replacement : Node Op} {path : List Nat}
    (updated : node.replaceAt path replacement = some result) :
    result.at_ path = some replacement ∧ result.ctorIdx = node.ctorIdx ∧
      ∀ old, node.at_ path = some old → result.replaceAt path old = some node := by
  induction path generalizing node result with
  | nil =>
      simp only [replaceAt] at updated
      split at updated
      · cases updated
        refine ⟨rfl, by assumption, ?_⟩
        intro old found
        cases found
        simp only [replaceAt]
        split <;> aesop
      · cases updated
  | cons index path ih =>
      cases first : node.child index with
      | none => simp only [replaceAt, first, Option.bind_none, reduceCtorEq] at updated
      | some next =>
          cases changed : next.replaceAt path replacement with
          | none => simp only [replaceAt, first, Option.bind_some, changed, Option.bind_none, reduceCtorEq] at updated
          | some next' =>
              have set : node.setChild index next' = some result := by
                simpa only [replaceAt, first, Option.bind_some, changed] using updated
              obtain ⟨newChild, sameSort, undoChild⟩ := setChild_spec set
              obtain ⟨newNode, _, undoNode⟩ := ih changed
              refine ⟨?_, sameSort, ?_⟩
              · simpa only [at_, newChild, Option.bind_some] using newNode
              · intro old found
                have oldNode : next.at_ path = some old := by
                  simpa only [at_, first, Option.bind_some] using found
                simpa only [replaceAt, newChild, Option.bind_some, undoNode old oldNode]
                  using undoChild next first

/-- An existing addressed node can be replaced by any node of the same sort. -/
theorem replaceAt_exists {node old replacement : Node Op} {path : List Nat}
    (found : node.at_ path = some old) (sameSort : replacement.ctorIdx = old.ctorIdx) :
    ∃ result, node.replaceAt path replacement = some result := by
  induction path generalizing node with
  | nil =>
      cases found
      exact ⟨replacement, by simp only [replaceAt, sameSort, ↓reduceIte]⟩
  | cons index path ih =>
      cases first : node.child index with
      | none => simp only [at_, first, Option.bind_none, reduceCtorEq] at found
      | some next =>
          have oldNode : next.at_ path = some old := by
            simpa only [at_, first, Option.bind_some] using found
          obtain ⟨next', changed⟩ := ih oldNode
          obtain ⟨result, set⟩ := setChild_exists first (replaceAt_spec changed).2.1
          exact ⟨result, by simpa only [replaceAt, first, Option.bind_some, changed] using set⟩

/-- Putting back exactly the addressed node makes no structural change. -/
theorem replaceAt_self {node old : Node Op} {path : List Nat}
    (found : node.at_ path = some old) : node.replaceAt path old = some node := by
  induction path generalizing node with
  | nil => cases found; simp only [replaceAt, ↓reduceIte]
  | cons index path ih =>
      cases first : node.child index with
      | none => simp only [at_, first, Option.bind_none, reduceCtorEq] at found
      | some next =>
          have oldNode : next.at_ path = some old := by
            simpa only [at_, first, Option.bind_some] using found
          simpa only [replaceAt, first, Option.bind_some, ih oldNode] using setChild_self first

/-- A second edit at the same path overwrites the first, including a wrong-sort refusal. -/
theorem replaceAt_overwrite {node result replacement : Node Op} {path : List Nat}
    (updated : node.replaceAt path replacement = some result) (last : Node Op) :
    result.replaceAt path last = node.replaceAt path last := by
  induction path generalizing node result with
  | nil =>
      have sorts := (replaceAt_spec updated).2.1
      simp only [replaceAt, sorts]
  | cons index path ih =>
      cases first : node.child index with
      | none => simp only [replaceAt, first, Option.bind_none, reduceCtorEq] at updated
      | some next =>
          cases changed : next.replaceAt path replacement with
          | none => simp only [replaceAt, first, Option.bind_some, changed, Option.bind_none, reduceCtorEq] at updated
          | some next' =>
              have set : node.setChild index next' = some result := by
                simpa only [replaceAt, first, Option.bind_some, changed] using updated
              simp only [replaceAt, (setChild_spec set).1, first, Option.bind_some, ih changed]
              cases next.replaceAt path last with
              | none => rfl
              | some final => exact setChild_overwrite set final

/-- Paths that split at different children below a common common are independent.
An ancestor or descendant is deliberately excluded: replacing an ancestor can erase paths. -/
theorem at_replaceAt_disjoint {node result replacement : Node Op}
    (common path other : List Nat) {index sibling : Nat}
    (updated : node.replaceAt (common ++ index :: path) replacement = some result)
    (distinct : sibling ≠ index) :
    result.at_ (common ++ sibling :: other) = node.at_ (common ++ sibling :: other) := by
  induction common generalizing node result with
  | nil =>
      cases first : node.child index with
      | none => simp only [List.nil_append, replaceAt, first, Option.bind_none, reduceCtorEq] at updated
      | some next =>
          cases changed : next.replaceAt path replacement with
          | none =>
              simp only [List.nil_append, replaceAt, first, Option.bind_some, changed,
                Option.bind_none, reduceCtorEq] at updated
          | some next' =>
              have set : node.setChild index next' = some result := by
                simpa only [List.nil_append, replaceAt, first, Option.bind_some, changed] using updated
              simp only [List.nil_append, at_, child_setChild_ne set distinct]
  | cons head common ih =>
      cases first : node.child head with
      | none => simp only [List.cons_append, replaceAt, first, Option.bind_none, reduceCtorEq] at updated
      | some next =>
          cases changed : next.replaceAt (common ++ index :: path) replacement with
          | none =>
              simp only [List.cons_append, replaceAt, first, Option.bind_some, changed,
                Option.bind_none, reduceCtorEq] at updated
          | some next' =>
              have set : node.setChild head next' = some result := by
                simpa only [List.cons_append, replaceAt, first, Option.bind_some, changed] using updated
              simp only [List.cons_append, at_, (setChild_spec set).1, first, Option.bind_some]
              exact ih changed

/-- Layer replacement is precisely the general edit with a layer replacement. -/
theorem replaceLayerAt_eq_replaceAt (node : Node Op) (path : List Nat) (layer : LayerTerm Op) :
    node.replaceLayerAt path layer = node.replaceAt path (.layer layer) := rfl

/-- The layer wrapper keeps the original recursive child-update equation. -/
theorem replaceLayerAt_cons (node : Node Op) (index : Nat) (path : List Nat)
    (layer : LayerTerm Op) :
    node.replaceLayerAt (index :: path) layer =
      (node.child index).bind (fun child =>
        (child.replaceLayerAt path layer).bind (node.setChild index)) := rfl

/-- The layer projection succeeds exactly at a layer node. -/
theorem layerAt_eq_some_iff (node : Node Op) (path : List Nat) (layer : LayerTerm Op) :
    node.layerAt path = some layer ↔ node.at_ path = some (.layer layer) := by
  unfold layerAt
  split <;> aesop

/-- Layer lookup follows the same first child as layer replacement. -/
theorem layerAt_cons (node : Node Op) (index : Nat) (path : List Nat) :
    node.layerAt (index :: path) = (node.child index).bind (fun next => next.layerAt path) := by
  cases found : node.child index <;> simp only [layerAt, at_, found, Option.bind_none, Option.bind_some]

/-- A successful layer replacement exposes the inserted layer, retains the root
node sort, and can be reversed with the old layer. This specializes `replaceAt_spec`
without any reference well-formedness or typing premise. -/
theorem replaceLayerAt_spec {node result : Node Op} {path : List Nat}
    {replacement : LayerTerm Op}
    (updated : node.replaceLayerAt path replacement = some result) :
    result.layerAt path = some replacement ∧ result.ctorIdx = node.ctorIdx ∧
      ∀ old, node.layerAt path = some old → result.replaceLayerAt path old = some node := by
  obtain ⟨found, sorts, undo⟩ := replaceAt_spec updated
  refine ⟨(layerAt_eq_some_iff _ _ _).mpr found, sorts, ?_⟩
  intro old original
  exact undo (.layer old) ((layerAt_eq_some_iff _ _ _).mp original)

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
  obtain ⟨result, updated⟩ := replaceAt_exists
    ((layerAt_eq_some_iff _ _ _).mp found) (replacement := .layer replacement) rfl
  exact ⟨result, updated, (replaceAt_spec updated).2.1⟩

/-- A layer update inside a program returns a program, not another node sort. -/
theorem replaceLayerAt_eff_exists {program : Eff Op} {path : List Nat}
    {old : LayerTerm Op} (found : (Node.eff program).layerAt path = some old)
    (replacement : LayerTerm Op) :
    ∃ result, (Node.eff program).replaceLayerAt path replacement = some (.eff result) := by
  obtain ⟨result, updated, sameSort⟩ := replaceLayerAt_exists found replacement
  cases result <;> cases sameSort
  exact ⟨_, updated⟩

/-- Replacing a later layer retains an earlier layer's existence. The earlier
layer may enclose the update, so its value need not remain equal. -/
theorem layerAt_exists_before_replaceLayerAt {node result : Node Op}
    {path earlier : List Nat} {old replacement : LayerTerm Op}
    (before : Path.lt earlier path = true)
    (found : node.layerAt earlier = some old)
    (updated : node.replaceLayerAt path replacement = some result) :
    ∃ layer, result.layerAt earlier = some layer := by
  induction path generalizing node result earlier with
  | nil => cases earlier <;> simp only [Path.lt, Bool.false_eq_true] at before
  | cons index path ih =>
      cases earlier with
      | nil =>
          have sameSort := (replaceLayerAt_spec updated).2.1
          cases node <;> cases found
          cases result <;> cases sameSort
          exact ⟨_, rfl⟩
      | cons other rest =>
          cases first : node.child index with
          | none => simp only [replaceLayerAt_cons, first, Option.bind_none, reduceCtorEq] at updated
          | some next =>
              cases changed : next.replaceLayerAt path replacement with
              | none => simp only [replaceLayerAt_cons, first, Option.bind_some, changed, Option.bind_none, reduceCtorEq] at updated
              | some next' =>
                  have set : node.setChild index next' = some result := by
                    simpa only [replaceLayerAt_cons, first, Option.bind_some, changed] using updated
                  by_cases sameIndex : other = index
                  · subst other
                    have before' : Path.lt rest path = true := by
                      simpa only [Path.lt, Nat.lt_irrefl, if_false] using before
                    have found' : next.layerAt rest = some old := by
                      simpa only [layerAt_cons, first, Option.bind_some] using found
                    obtain ⟨layer, survives⟩ := ih before' found' changed
                    refine ⟨layer, ?_⟩
                    simpa only [layerAt_cons, (setChild_spec set).1, Option.bind_some] using survives
                  · refine ⟨old, ?_⟩
                    simpa only [layerAt_cons, child_setChild_ne set sameIndex] using found

end Effect4.Program.Node

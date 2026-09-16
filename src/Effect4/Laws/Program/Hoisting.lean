import Effect4.Laws.Program.References
import Effect4.Laws.Program.PathOrder

/-!
# The shared-layer declaration history

The printer's hoisting operation captures old layers before replacing their sites.
The first invariant below undoes that capture history in reverse order. The second
connects the history's path order to the existing module restoration operation.
These are structural equations over the original program, including its references;
they do not expand sharing or establish a target execution theorem.
-/

namespace Effect4.Program

variable {Op : Type}

-- Use equality's constructive reflexivity instance directly. The generic Ord
-- route to ReflBEq Nat reaches Classical.choice on the pinned toolchain.
local instance : ReflBEq Nat where
  rfl := (beq_iff_eq).mpr rfl

private abbrev History (Op : Type) := List (List Nat × LayerTerm Op)

private def undoStep (root : Eff Op) (entry : List Nat × LayerTerm Op) : Option (Eff Op) := do
  let restored ← (Node.eff root).replaceLayerAt entry.1 entry.2
  restored.eff?

private def undoHistory (root : Eff Op) (history : History Op) : Option (Eff Op) :=
  history.foldlM undoStep root

private def captureStep (state : Eff Op × History Op) (target : List Nat) :
    Except (List Nat) (Eff Op × History Op) :=
  match (Node.eff state.1).layerAt target,
      (Node.eff state.1).replaceLayerAt target (.ref target) with
  | some layer, some (Node.eff next) => .ok (next, (target, layer) :: state.2)
  | _, _ => .error target

private theorem captureStep_undo {state next : Eff Op × History Op} {target : List Nat}
    (h : captureStep state target = .ok next) :
    undoHistory next.1 next.2 = undoHistory state.1 state.2 := by
  rcases state with ⟨root, history⟩
  unfold captureStep at h
  cases hl : (Node.eff root).layerAt target with
  | none => simp [hl] at h
  | some layer =>
    cases hr : (Node.eff root).replaceLayerAt target (.ref target) with
    | none => simp [hl, hr] at h
    | some node =>
      cases node <;> simp only [hl, hr] at h
      all_goals try contradiction
      rename_i updated
      cases h
      have back := Node.replaceLayerAt_restore hl hr
      simp [undoHistory, undoStep, back, Node.eff?]

private theorem captureStep_keys {state next : Eff Op × History Op} {target : List Nat}
    (h : captureStep state target = .ok next) :
    next.2.map Prod.fst = target :: state.2.map Prod.fst := by
  unfold captureStep at h
  split at h <;> cases h
  rfl

private theorem captureFold_undo (targets : List (List Nat))
    {state final : Eff Op × History Op}
    (h : targets.foldlM captureStep state = .ok final) :
    undoHistory final.1 final.2 = undoHistory state.1 state.2 := by
  induction targets generalizing state with
  | nil => cases h; rfl
  | cons target targets ih =>
    cases hs : captureStep state target with
    | error why => simp [List.foldlM_cons, hs, Bind.bind, Except.bind] at h
    | ok next =>
      have ht : targets.foldlM captureStep next = .ok final := by
        simpa [List.foldlM_cons, hs, Bind.bind, Except.bind] using h
      exact (ih ht).trans (captureStep_undo hs)

private theorem captureFold_keys (targets : List (List Nat))
    {state final : Eff Op × History Op}
    (h : targets.foldlM captureStep state = .ok final) :
    final.2.map Prod.fst = targets.reverse ++ state.2.map Prod.fst := by
  induction targets generalizing state with
  | nil => cases h; rfl
  | cons target targets ih =>
    cases hs : captureStep state target with
    | error why => simp [List.foldlM_cons, hs, Bind.bind, Except.bind] at h
    | ok next =>
      have ht : targets.foldlM captureStep next = .ok final := by
        simpa [List.foldlM_cons, hs, Bind.bind, Except.bind] using h
      rw [ih ht, captureStep_keys hs]
      simp [List.reverse_cons, List.append_assoc]

private theorem findHistory {history : History Op}
    (unique : (history.map Prod.fst).Nodup) {entry : List Nat × LayerTerm Op}
    (mem : entry ∈ history) : history.find? (fun item => item.1 == entry.1) = some entry := by
  induction history with
  | nil => cases mem
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp mem with rfl | mem
    · simp
    · have different : head.1 ≠ entry.1 := by
        intro equal
        apply unique.1
        exact List.mem_map.mpr ⟨entry, mem, equal.symm⟩
      have distinct : (head.1 == entry.1) = false := by
        simpa only [beq_eq_false_iff_ne] using different
      simpa [List.find?, distinct] using ih unique.2 mem

private theorem restoreFold_eq_undo (all rest : History Op)
    (unique : (all.map Prod.fst).Nodup) (contained : ∀ entry ∈ rest, entry ∈ all)
    (root : Eff Op) :
    (rest.map Prod.fst).foldlM (fun acc target => do
      let layer ← (all.find? (·.1 == target)).map (·.2)
      let node ← (Node.eff acc).replaceLayerAt target layer
      node.eff?) root = undoHistory root rest := by
  induction rest generalizing root with
  | nil => rfl
  | cons entry rest ih =>
    have hf := findHistory unique (contained entry (by simp))
    simp only [List.map_cons, List.foldlM_cons, hf, Option.map_some,
      undoHistory, undoStep]
    congr 1
    funext next
    exact ih (fun e he => contained e (List.mem_cons_of_mem _ he)) next

private theorem restoreAll_eq_undo (root : Eff Op) (history : History Op)
    (ordered : (history.map Prod.fst).Pairwise (fun a b => Path.lt a b = true)) :
    root.restoreAll history = undoHistory root history := by
  have unique : (history.map Prod.fst).Nodup := ordered.imp (by
    intro a b before equal
    subst b
    simp [Path.lt_irrefl] at before)
  unfold Eff.restoreAll
  rw [Path.sortBy_lt_eq_self ordered]
  exact restoreFold_eq_undo history history unique (fun _ h => h) root

private theorem eraseDups_nodup (paths : List (List Nat)) : paths.eraseDups.Nodup := by
  cases paths with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · simp [List.mem_eraseDups]
    · exact eraseDups_nodup (tail.filter (fun p => !p == head))
termination_by paths.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A successful hoist returns its capture history in ascending path order.
This is the reverse of the replacement order, not the source declaration order. -/
theorem Eff.hoistAll_ordered {root main : Eff Op} {history : History Op}
    (h : root.hoistAll = .ok (main, history)) :
    (history.map Prod.fst).Pairwise (fun a b => Path.lt a b = true) := by
  have unique : root.refTargets.Nodup :=
    Path.sortBy_nodup Path.declBefore (eraseDups_nodup _)
  have keys := captureFold_keys
    (Path.sortBy (fun a b => Path.lt b a) root.refTargets) h
  simp only [List.map_nil, List.append_nil] at keys
  rw [keys]
  exact Path.reverse_sortBy_flip_lt_pairwise unique

/-- Restoring a successful capture history recovers the entire original program,
including its sharing references. The equation is structural and conditional only
on hoisting success; it does not assume typing or change execution semantics. -/
theorem Eff.restoreAll_hoistAll {root main : Eff Op} {history : History Op}
    (h : root.hoistAll = .ok (main, history)) : main.restoreAll history = some root := by
  rw [restoreAll_eq_undo main history (Eff.hoistAll_ordered h)]
  exact captureFold_undo
    (Path.sortBy (fun a b => Path.lt b a) root.refTargets) h

end Effect4.Program

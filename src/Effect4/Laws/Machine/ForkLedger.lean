import Effect4.Machine.Fibers
import Effect4.Laws.Auto.RuleSets

/-!
Local fork-ledger laws (origin-ledger plan §3). Append equations hold on arbitrary machines.
The new-id lookup requires both fiber and record freshness; the other-id equation does not.
These laws do not establish the ledger invariant on every reachable machine.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Effect4.Machine.ForkLedger
open Effect4 Effect4.Machine
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable {κ φ η : Type (max u v)}

private theorem find_append_hit {α : Type _} (p : α → Bool) (xs : List α) (x : α)
    (hn : xs.find? p = none) (hx : p x = true) :
    (xs ++ [x]).find? p = some x := by
  have hs : [x].find? p = some x := by rw [List.find?_cons, hx]
  rw [List.find?_append, hn, Option.none_or, hs]

private theorem find_append_miss {α : Type _} (p : α → Bool) (xs : List α) (x : α)
    (hx : p x = false) : (xs ++ [x]).find? p = xs.find? p := by
  have hs : [x].find? p = none := by
    rw [List.find?_cons, hx]
    rfl
  rw [List.find?_append, hs, Option.or_none]

theorem originOf_absent (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId)
    (hf : m.fiber? id = none) : m.originOf id = none := by
  simp only [RunMachine.originOf, hf]

theorem originOf_root (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId)
    (f : RunFiber ν σ β ε δ ι α χ κ φ)
    (hf : m.fiber? id = some f) (hr : m.forkRecord? id = none) :
    m.originOf id = some .root := by
  simp only [RunMachine.originOf, hf, hr]

theorem originOf_forked (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) (record : ForkRecord)
    (hf : m.fiber? id = some f) (hr : m.forkRecord? id = some record) :
    m.originOf id = some (.forked record.parent record.daemon record.site) := by
  simp only [RunMachine.originOf, hf, hr]

theorem forkRecord_nextId_none (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (below : ∀ record ∈ m.forks, record.child.value < m.nextId) :
    m.forkRecord? ⟨m.nextId⟩ = none := by
  apply List.find?_eq_none.mpr
  intro record hr he
  have he := of_decide_eq_true he
  have hb := below record hr
  have hv := congrArg FiberId.value he
  simp only at hv
  omega

variable [core : FiberCore ν β ε δ ι α κ φ]
variable (interp : RunInterp ν σ β ε δ ι α χ St κ)
variable (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
variable (parent : RunFiber ν σ β ε δ ι α χ κ φ) (program : κ)
variable (options : Supervision.ForkOptions) (site : List Nat)

theorem spawn_forks :
    (spawn interp m parent program options site).1.forks =
      m.forks ++ [(ForkRecord.mk ⟨m.nextId⟩ parent.id options.daemon site)] := rfl

theorem spawn_forkRecord_new (hr : m.forkRecord? ⟨m.nextId⟩ = none) :
    (spawn interp m parent program options site).1.forkRecord? ⟨m.nextId⟩ =
      some (ForkRecord.mk ⟨m.nextId⟩ parent.id options.daemon site) := by
  change (m.forks ++ [(ForkRecord.mk ⟨m.nextId⟩ parent.id options.daemon site)]).find?
      (fun record => record.child = ⟨m.nextId⟩) = some _
  exact find_append_hit _ _ _ hr (decide_eq_true rfl)

theorem spawn_forkRecord_other (id : FiberId) (hne : ⟨m.nextId⟩ ≠ id) :
    (spawn interp m parent program options site).1.forkRecord? id = m.forkRecord? id := by
  change (m.forks ++ [(ForkRecord.mk ⟨m.nextId⟩ parent.id options.daemon site)]).find?
      (fun record => record.child = id) = m.forks.find? _
  exact find_append_miss _ _ _ (decide_eq_false hne)

theorem spawn_originOf_new (hf : m.fiber? ⟨m.nextId⟩ = none)
    (hr : m.forkRecord? ⟨m.nextId⟩ = none) :
    (spawn interp m parent program options site).1.originOf ⟨m.nextId⟩ =
      some (.forked parent.id options.daemon site) := by
  have record := spawn_forkRecord_new interp m parent program options site hr
  unfold RunMachine.originOf
  rw [record]
  change m.fibers.find? _ = none at hf
  simp only [spawn, RunMachine.emit, RunMachine.fiber?, List.find?_append,
    hf, Option.none_or, List.find?_cons, RunFiber.make, decide_true]

theorem spawn_originOf_other (id : FiberId) (hne : ⟨m.nextId⟩ ≠ id) :
    (spawn interp m parent program options site).1.originOf id = m.originOf id := by
  have record := spawn_forkRecord_other interp m parent program options site id hne
  have fiber : (spawn interp m parent program options site).1.fiber? id = m.fiber? id := by
    unfold spawn RunMachine.emit RunMachine.fiber?
    exact find_append_miss _ _ _ (decide_eq_false hne)
  simp only [RunMachine.originOf, fiber, record]

end Effect4.Machine.ForkLedger

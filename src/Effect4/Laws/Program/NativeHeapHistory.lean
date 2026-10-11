import Effect4.Laws.Program.NativeHeapExecution

/-!
Concept: store-typing R4, claim `cell-invariant-from-write-sites`, role preservation.
The existing native source relation supplies the actual writer's checked site.
The existing machine lift retains that relation and the cell predicate through control histories.
Consumer: `HeapSites.heap_sites_keep` and the original Atomic bounded statement.
The fragment excludes raw generators, layers, definitions, invocation and call heads.
No progress or external behavior is asserted.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program Effect4.Run HeapSites

/-- The existing decision lift carries source ownership together with the cell predicate. -/
theorem heap_decision_lift (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (P : Val → Prop) (sites : SitesKeep root P) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => ConfigurationAt root m ∧ HeapOk P m.state.refs)
      (fun _ _ cmds => CommandsAt root cmds) (fun _ _ tasks => TasksAt root tasks)
      (fun _ _ d => IsControl d) := by
  letI := evaluatorFor root table
  have source := decision_lift_at root fragment table
  refine {
    step := ?_, nil := source.nil, evaluate := ?_, drain := ?_, ran := ?_, task := ?_, skip := source.skip,
    yield := ?_, interrupt := ?_, middleware := ?_, clockNone := ?_, clockSome := ?_, answer := ?_ }
  · intro ts w m c rest notStuck held
    have moved := command_at root fragment table m c rest held.1.1 ((held.2 notStuck).1)
    have heap := command_heap root table m c rest held.1.1 P sites held.1.2
    exact ⟨(), trivial, ⟨moved.1, heap⟩, fun _ => ⟨moved.2, (held.2 notStuck).2⟩⟩
  · intro w m id held notStuck
    exact source.evaluate w m id held.1 notStuck
  · intro w m owner fiber held found
    have moved := source.drain w m owner fiber held.1 found
    exact ⟨⟨moved.1, held.2⟩, moved.2⟩
  · intro w m owner task held
    exact ⟨source.ran w m owner task held.1, held.2⟩
  · intro w m owner task rest held notStuck saved
    exact source.task w m owner task rest held.1 notStuck saved
  · intro w m id verdict held
    refine ⟨source.yield w m id verdict held.1, ?_⟩
    change HeapOk P (m.modify id (fun f => {f with yieldOverride := some verdict})).state.refs
    rw [modify_state]
    exact held.2
  · intro w m who extra target fiber held found
    refine ⟨source.interrupt w m who extra target fiber held.1 found, ?_⟩
    unfold Lift.interruptEdit
    dsimp only
    split <;> exact held.2
  · intro w m held
    exact ⟨source.middleware w m held.1, held.2⟩
  · intro w m millis state held notStuck found
    obtain ⟨later, order, moved⟩ := source.clockNone w m millis state held.1 notStuck found
    have refs : ((interpOf root table).clockStep millis m.state).2.refs = m.state.refs := rfl
    rw [found] at refs
    exact ⟨later, order, moved, refs ▸ held.2⟩
  · intro w m millis owed state held notStuck found
    obtain ⟨later, order, moved, commands⟩ := source.clockSome w m millis owed state held.1 notStuck found
    have refs : ((interpOf root table).clockStep millis m.state).2.refs = m.state.refs := rfl
    rw [found] at refs
    have drained := drain_refs {m with state} [owed]
    exact ⟨later, order, ⟨moved, drained ▸ (refs ▸ held.2)⟩, commands⟩
  · intro w m id token answer held notStuck refused
    exact False.elim refused

/-- The actual load has an empty heap at every compiler budget. -/
theorem load_heap (root : NativeEff) (compileFuel : Nat) (P : Val → Prop) :
    HeapOk P (Api.load root compileFuel).state.refs := by
  intro index value found
  change ([] : List Val)[index]? = some value at found
  rw [List.getElem?_nil] at found
  cases found

/-- The cell predicate follows every actual control history from its checked write sites. -/
theorem heap_history_at (b : Api.Built) (fragment : Fragment b.program) (compileFuel : Nat)
    (P : Val → Prop) (sites : SitesKeep b.program P)
    (m : NativeMachine) (history : ControlHistory b compileFuel m) : HeapOk P m.state.refs := by
  letI := evaluatorFor b.program b.table
  obtain ⟨rows, controls, rfl⟩ := history
  have step (before : NativeMachine) (row : Nat × NativeDecision)
      (held : ConfigurationAt b.program before ∧ HeapOk P before.state.refs) (control : IsControl row.2) :
      ConfigurationAt b.program (stepBy b before row) ∧ HeapOk P (stepBy b before row).state.refs := by
    obtain ⟨_, _, moved⟩ := Lift.stepDecisionState_lift (heap_decision_lift b.program fragment b.table P sites)
      row.1 () before row.2 held control
    exact moved
  have fold : ∀ (rows : List (Nat × NativeDecision)) (before : NativeMachine),
      (∀ row ∈ rows, IsControl row.2) → (ConfigurationAt b.program before ∧ HeapOk P before.state.refs) →
      ConfigurationAt b.program (rows.foldl (stepBy b) before) ∧ HeapOk P (rows.foldl (stepBy b) before).state.refs := by
    intro rows
    induction rows with
    | nil => intro before _ held; exact held
    | cons row rest ih =>
      intro before controls held
      exact ih (stepBy b before row) (fun x member => controls x (.tail _ member))
        (step before row held (controls row (.head _)))
  exact (fold rows _ controls ⟨load_at b.program fragment compileFuel, load_heap b.program compileFuel P⟩).2

end Effect4.Program.SourceScope

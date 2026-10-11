import Effect4.Laws.Machine.RefKernel

/-!
Reference lookup locality for actual synchronous store operations.
Concept: store-typing, R4, and reactive-scheduling, R11.
These helpers serve the proposed cell-invariant-from-write-sites claim and the original application accounting goals.
StoreExecution consumes the projection and frame rule; Atomic consumes the exact read rule.
The footprint includes allocation's actual answer and conservatively includes read-only selected cells.
The laws establish no source ownership, history invariant, progress, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Machine

/-- Actual synchronous store execution projects to the existing heap operation.
Concept: store-typing, R4; a step of cell-invariant-from-write-sites.
Consumer: the native RefTransfer connector and Atomic's reference-read debit. -/
theorem syncOpStep_refProjection {op : SyncOp} {before after : Stores} {value : Val}
    (step : syncOpStep op before = some (after, value)) :
    match refStep op before.refs with
    | none => after.refs = before.refs
    | some result => result = (value, after.refs) := by
  cases kernel : op.refKernel with
  | some row =>
    obtain ⟨cell, k⟩ := row
    rw [syncOpStep_eq_refStepOf kernel] at step
    obtain ⟨pair, actual, equal⟩ := Option.map_eq_some_iff.mp step
    cases equal
    rw [refStep_eq_refStepOf kernel, actual]
  | none =>
    cases op <;> cases kernel
    all_goals simp only [syncOpStep] at step
    all_goals repeat' split at step
    all_goals aesop (add norm simp [refStep])
/-- A conservative reference footprint, including the actual key returned by allocation. -/
def SyncOp.refFootprint (op : SyncOp) (answer : Val) : Option RefKey :=
  match op.refKernel with
  | some (cell, _) => some cell
  | none => match op, answer with
    | .refMake _, .cell ⟨index⟩ => some ⟨index⟩
    | _, _ => none

/-- A cell outside the actual row's footprint keeps even an absent lookup. -/
theorem syncOpStep_refPeek_other {op : SyncOp} {before after : Stores} {answer : Val}
    (step : syncOpStep op before = some (after, answer)) (cell : RefKey)
    (outside : op.refFootprint answer ≠ some cell) :
    refPeek after.refs cell = refPeek before.refs cell := by
  have projected := syncOpStep_refProjection step
  cases actual : refStep op before.refs with
  | none =>
    rw [actual] at projected
    exact projected ▸ rfl
  | some result =>
    rw [actual] at projected
    dsimp only at projected
    rw [projected] at actual
    rcases refStep_cases actual with ⟨initial, rfl⟩ | ⟨target, kernel, row, executed⟩
    · have output := Option.some.inj actual
      change (Val.cell ⟨before.refs.length⟩, before.refs ++ [initial]) = (answer, after.refs) at output
      have resultValue : Val.cell ⟨before.refs.length⟩ = answer := congrArg Prod.fst output
      have heap : before.refs ++ [initial] = after.refs := congrArg Prod.snd output
      rw [← resultValue] at outside
      have different : cell.index ≠ before.refs.length := by
        intro equal
        apply outside
        cases cell
        cases equal
        rfl
      rw [← heap]
      change (before.refs ++ [initial])[cell.index]? = before.refs[cell.index]?
      by_cases inside : cell.index < before.refs.length
      · exact List.getElem?_append_left inside
      · rw [List.getElem?_eq_none (by
          simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getElem?_eq_none (by omega)]
    · obtain ⟨value, _, mapped⟩ := Option.bind_eq_some_iff.mp executed
      obtain ⟨pair, _, equal⟩ := Option.map_eq_some_iff.mp mapped
      have heap : refWriteBack before.refs target pair.2 = after.refs := congrArg Prod.snd equal
      have different : cell.index ≠ target.index := by
        intro same
        apply outside
        simp only [SyncOp.refFootprint, row]
        cases cell
        cases target
        cases same
        rfl
      rw [← heap]
      exact refWriteBack_peek_other before.refs target pair.2 cell.index different

/-- A reference read retains the entire reference heap. -/
theorem syncOpStep_refGet_refs {cell : RefKey} {before after : Stores} {answer : Val}
    (step : syncOpStep (.refGet cell) before = some (after, answer)) :
    after.refs = before.refs := by
  have projected := syncOpStep_refProjection step
  cases lookup : refPeek before.refs cell with
  | none =>
    simpa only [refStep, lookup, Option.map_none] using projected
  | some value =>
    simp only [refStep, lookup, Option.map_some] at projected
    exact (congrArg Prod.snd projected).symm

end Effect4.Machine

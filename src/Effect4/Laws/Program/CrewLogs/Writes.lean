import Effect4.Laws.Program.CrewLogs

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual reference operations supply the shared crew log observation.
Consumers: the concrete Workers and QueueWorkers writer contracts.
Reach: actual successful synchronous operations and captured source values.
The source census and initialized frame producer remain separate premises.
-/
set_option autoImplicit false
namespace Effect4.Program.CrewLogs
open Effect4 Effect4.Machine Effect4.Program

/-- The common source expression appends the captured identity to the current reference list. -/
def appendTerm (oldIndex acquiredIndex : Nat) : Term :=
  .app "append" (.cons (.var oldIndex) (.cons
    (.app "cons" (.cons (.var acquiredIndex) (.cons (.app "nil" .nil) .nil))) .nil))

/-- The source expression reads the actual current cell value and protected captured identity. -/
theorem append_value (env : List Val) (index identity : Nat)
    (acquired : env[index]? = some (.nat identity)) (old : Val) :
    evalTerm (env ++ [old]) (appendTerm env.length index) =
      old.asList?.map (fun values => .list (values ++ [.nat identity])) := by
  have oldSlot : (env ++ [old])[env.length]? = some old := List.getElem?_concat_length
  have identitySlot : (env ++ [old])[index]? = some (.nat identity) :=
    (List.getElem?_append_left (List.getElem?_eq_some_iff.mp acquired).1).trans acquired
  simp only [appendTerm, evalTerm, evalTerms, oldSlot, identitySlot, Option.bind_some,
    nativeAtom, NativeAtom.ofName?]
  change (old.asList?.bind fun values => some (Val.list (values ++ [.nat identity]))) = _
  cases old.asList? <;> rfl

/-- A reference lookup equality also gives equality of the observed log. -/
theorem entries_of_peek (cell : Nat) (before after : RefHeap)
    (same : refPeek after ⟨cell⟩ = refPeek before ⟨cell⟩) : entries cell after = entries cell before := by
  unfold entries
  change after[cell]? = before[cell]? at same
  rw [same]

/-- A successful update of the log appends the exact acquired identity named by its source term. -/
theorem update_change (spec : Spec) (identity : Nat) (member : identity ∈ spec.identities)
    (env : List Val) (before after : Stores) (value : Val)
    (term : ∀ old : Val, evalTerm (env ++ [old]) (spec.term identity) =
      old.asList?.map (fun values => .list (values ++ [.nat identity])))
    (ran : syncOpStep (.refUpdate ⟨spec.cell⟩ (spec.term identity) env) before = some (after, value)) :
    SyncChange spec before.refs after.refs (.op (.refUpdate ⟨spec.cell⟩ (spec.term identity) env)) := by
  change (refStep (.refUpdate ⟨spec.cell⟩ (spec.term identity) env) before.refs).map _ =
    some (after, value) at ran
  obtain ⟨⟨answer, heap⟩, executed, equal⟩ := Option.map_eq_some_iff.mp ran
  cases equal
  unfold refStep at executed
  obtain ⟨old, read, computed⟩ := Option.bind_eq_some_iff.mp executed
  rw [term old] at computed
  obtain ⟨writtenValue, evaluated, computed⟩ := Option.map_eq_some_iff.mp computed
  obtain ⟨values, viewed, writtenValueEq⟩ := Option.map_eq_some_iff.mp evaluated
  cases writtenValueEq
  cases computed
  refine .inr ⟨identity, member, env, .inl rfl, ?_⟩
  have written := refPeek_poke_self before.refs ⟨spec.cell⟩ (.list (values ++ [.nat identity])) old read
  change before.refs[spec.cell]? = some old at read
  change (refPoke before.refs ⟨spec.cell⟩ (.list (values ++ [.nat identity])))[spec.cell]? =
    some (.list (values ++ [.nat identity])) at written
  simp only [entries, read, written, Option.bind_some]
  rw [viewed]
  rfl

/-- Native stored wrappers retain the very same observed write. -/
theorem SyncChange.stored {spec : Spec} {before after : RefHeap} {operation : SyncOp}
    (held : SyncChange spec before after (.op operation)) :
    SyncChange spec before after (.store (.op operation)) := by
  rcases held with same | ⟨identity, member, env, actual, appended⟩
  · exact .inl same
  · rcases actual with actual | impossible
    · cases actual
      exact .inr ⟨identity, member, env, .inr rfl, appended⟩
    · cases impossible

/-- An operation outside the log's reference footprint leaves the observed log. -/
theorem outside_change (spec : Spec) (operation : SyncOp) (before after : Stores) (value : Val)
    (ran : syncOpStep operation before = some (after, value))
    (outside : operation.refFootprint value ≠ some ⟨spec.cell⟩) :
    SyncChange spec before.refs after.refs (.op operation) :=
  .inl (entries_of_peek spec.cell before.refs after.refs (syncOpStep_refPeek_other ran ⟨spec.cell⟩ outside))

/-- Allocating a value with no log entries leaves the observed log, including before its allocation. -/
theorem make_change (spec : Spec) (initial : Val)
    (empty : initial.asList?.getD [] = []) (before after : Stores) (value : Val)
    (ran : syncOpStep (.refMake initial) before = some (after, value)) :
    SyncChange spec before.refs after.refs (.op (.refMake initial)) := by
  change some ({before with refs := before.refs ++ [initial]}, .cell ⟨before.refs.length⟩) = some (after, value) at ran
  cases ran
  by_cases selected : spec.cell = before.refs.length
  · apply Or.inl
    unfold entries
    rw [selected, List.getElem?_concat_length, List.getElem?_eq_none (Nat.le_refl _)]
    exact empty
  · apply outside_change spec (.refMake initial) before _ _ rfl
    intro equal
    have indices := congrArg (fun key : Option RefKey => key.map RefKey.index) equal
    change some before.refs.length = some spec.cell at indices
    exact selected (Option.some.inj indices).symm
end Effect4.Program.CrewLogs

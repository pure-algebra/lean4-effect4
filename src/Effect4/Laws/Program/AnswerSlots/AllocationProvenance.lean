import Effect4.Laws.Program.AnswerSlots.AllocationAdapter
import Effect4.Laws.Program.AnswerSlots.PrefixStable

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: bare Atomic and Timeout initializers enter at their actual point with exact cells.
Reach: actual native reference allocation, returned key and view-updated saved callback.
Consumer: the common allocation saved edge and the numeric entry hooks.
No history, empty suffix or fresh point is assumed by these local producers.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Actual allocation chooses one world for both the heap and its returned key class. -/
theorem allocated_actual (spec : Spec) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) (after : Stores) (answer : Val)
    (ran : syncOpStep (.refMake (spec.initialization.initial index)) world.state = some (after, answer)) :
    let next : World := ⟨world.owner, after, world.entered⟩
    Future world next ∧ ValueAt spec next (.allocated index) answer := by
  obtain ⟨key, written⟩ := Initialization.actual spec.initialization index world.state after answer ran
  rw [stage.stage.source.2.2.2.1] at key
  subst answer
  subst after
  have contents : world.state.refs ++ [spec.initialization.initial index] =
      Initialization.values spec.initialization (index + 1) := by
    rw [stage.stage.contents, Initialization.values_next]
  have count : (world.state.refs ++ [spec.initialization.initial index]).length = index + 1 := by
    rw [List.length_append, List.length_singleton, stage.stage.source.2.2.2.1]
  refine ⟨⟨rfl, ?_, Nat.le_refl _, fun held => held⟩, .inl stage.owner, rfl, count, stage.deferreds, contents, stage.pending⟩
  simp only [List.length_append, List.length_singleton]
  omega

/-- An actual saved allocation callback retains its point while consuming its exact returned key. -/
theorem allocation_advance (spec : Spec) (before after : World) (index : Nat) (point : Point)
    (small : index < spec.initialization.width) (stage : RootStage spec before index point)
    (future : Future before after) (view : List (FiberId × ExitV)) (answer : Val)
    (good : ValueAt spec after (.allocated index) answer) :
    RootStage spec after (index + 1) ({point with completed := view}.childWith 1 answer) := by
  obtain ⟨phase, key, count, deferreds, contents, pending⟩ := good
  subst answer
  have advanced := Initialization.advance spec.initialization index point before.state.refs
    small stage.stage.source view (spec.initialization.initial index)
  refine ⟨future.owner.symm.trans stage.owner, ⟨?_, contents⟩, deferreds, pending⟩
  exact ⟨advanced.1, advanced.2.1, advanced.2.2.1, count, advanced.2.2.2.2⟩

/-- The bare boundary retains its real point, exact cells and current completed-fiber view. -/
theorem bare_entry (spec : Spec) (world : World) (point : Point) (noGate : spec.gate = none)
    (stage : RootStage spec world spec.initialization.width point) : Entry spec world point := by
  have zero : spec.gateNeed = 0 := by simp only [Spec.gateNeed, noGate, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  refine ⟨stage.owner, stage.stage.source.2.2.2.2, ?_, ?_, stage.stage.contents, ?_, stage.pending⟩
  · rw [zero, Nat.add_zero]
    exact stage.stage.source.2.1
  · exact stage.stage.source.2.2.1.trans (spec.noGate noGate)
  · refine ⟨?_, ?_⟩
    · exact Nat.le_of_eq stage.stage.source.2.2.2.1.symm
    · rw [zero]
      exact Nat.zero_le _

/-- A saved allocation callback either retains the next prefix stage or exposes exact entry. -/
theorem allocation_callback (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (before after : World) (index : Nat) (point : Point) (small : index < spec.initialization.width)
    (stage : RootStage spec before index point) (future : Future before after)
    (view : List (FiberId × ExitV)) (answer : Val) (good : ValueAt spec after (.allocated index) answer) :
    CodeAt spec after (.stable spec.stable.rootKind) ((interpAt spec.root view spec.table).contA (.cont point) answer) := by
  have advanced := allocation_advance spec before after index point small stage future view answer good
  change CodeAt spec after (.stable spec.stable.rootKind)
    (resolve spec.root ({point with completed := view}.childWith 1 answer))
  by_cases pending : index + 1 < spec.initialization.width
  · exact .initial advanced (.inl pending)
  · have last : index + 1 = spec.initialization.width := by omega
    rw [last] at advanced
    cases gate : spec.gate with
    | none => exact .entered fragment (bare_entry spec after _ gate advanced)
    | some present => exact .initial advanced (.inr (by simp only [gate, Option.isSome_some]))

/-- The actual optional gate preserves the completed initial reference heap. -/
theorem gate_actual (spec : Spec) (world : World) (point : Point)
    (stage : RootStage spec world spec.initialization.width point) (available : spec.gate.isSome = true)
    (after : Stores) (answer : Val)
    (ran : syncOpStep .deferredMake world.state = some (after, answer)) :
    let next : World := ⟨world.owner, after, world.entered⟩
    Future world next ∧ ValueAt spec next .gate answer := by
  rw [syncOpStep_deferredMake] at ran
  cases ran
  have need : spec.gateNeed = 1 := by simp only [Spec.gateNeed, available, ↓reduceIte]
  refine ⟨⟨rfl, Nat.le_refl _, ?_, fun held => held⟩, .inl stage.owner, ?_, ?_, stage.stage.contents, stage.pending⟩
  · change world.state.deferreds.cells.length ≤ (world.state.deferreds.cells ++ [_]).length
    rw [List.length_append, List.length_singleton]
    omega
  · change Val.promise ⟨world.state.deferreds.cells.length⟩ = Val.promise ⟨0⟩
    rw [stage.deferreds]
  · refine ⟨Nat.le_of_eq stage.stage.source.2.2.2.1.symm, ?_⟩
    rw [need]
    change 1 ≤ (world.state.deferreds.cells ++ [_]).length
    rw [List.length_append, List.length_singleton]
    omega

/-- The actual gate callback exposes its source entry point and the same initial reference heap. -/
theorem gate_entry (spec : Spec) (before after : World) (point : Point)
    (stage : RootStage spec before spec.initialization.width point) (future : Future before after)
    (gate : Gate spec.root spec.initialization.width spec.bindings) (present : spec.gate = some gate)
    (view : List (FiberId × ExitV)) (answer : Val) (good : ValueAt spec after .gate answer) :
    Entry spec after ({point with completed := view}.childWith 1 answer) := by
  obtain ⟨phase, key, cells, contents, pending⟩ := good
  subst answer
  obtain ⟨tail, found⟩ := gate.head
  rw [← stage.stage.source.2.1] at found
  have child := SourceScope.next_of_at spec.root point _ 1 1 found stage.stage.source.2.2.2.2 rfl
  have need : spec.gateNeed = 1 := by
    unfold Spec.gateNeed
    rw [present]
    rfl
  refine ⟨future.owner.symm.trans stage.owner, SourceScope.childWith_at spec.root _ 1 _ child, ?_, ?_, contents, cells, pending⟩
  · change point.path ++ [1] = List.replicate (spec.initialization.width + spec.gateNeed) 1
    rw [stage.stage.source.2.1, need, List.replicate_succ']
  · change point.env ++ [.promise ⟨0⟩] = spec.bindings
    rw [stage.stage.source.2.2.1]
    exact gate.next

/-- Consuming an actual entry marker activates the stable graph at the same source point and heap. -/
theorem activate_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (world : World) (point : Point) (entry : Entry spec world point) :
    let after : World := {world with entered := true}
    Future world after ∧ Ready spec after ∧
      CodeAt spec after (.stable spec.stable.rootKind) (resolve spec.root point) := by
  have ready : Ready spec {world with entered := true} := ⟨rfl, entry.cells.1, entry.cells.2⟩
  refine ⟨⟨rfl, Nat.le_refl _, Nat.le_refl _, fun _ => rfl⟩, ready, .stable ready ?_⟩
  apply spec.entry fragment point entry.source
  · rw [entry.env]
    exact List.take_length
  · exact entry.path

/-- A reference-only prefix uses the common broad binding model without a crew gate. -/
def bareSpec (root : NativeEff) (table : RowTable) (initialization : Initialization root)
    (positive : 0 < initialization.width)
    (complete : initialization.bindings.take initialization.width = initialization.bindings) : Spec where
  stable := prefixSpec root table initialization.bindings
  initialization := initialization
  positive := positive
  gate := none
  noGate _ := complete
  laws fragment := prefixLaws root fragment initialization.bindings table
  root_value _ := trivial
  yield_code _ := trivial
  sync_value _ _ _ _ := trivial
  entry fragment point _ slots _ := resolve_at root fragment initialization.bindings point slots

end Effect4.Program.AnswerSlots.AllocationAdapter

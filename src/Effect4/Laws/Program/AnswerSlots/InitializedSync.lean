import Effect4.Laws.Program.AnswerSlots.InitializedTransport
import Effect4.Laws.Machine.StoresLaws

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual synchronous initializer answers retain their returned key and post-operation phase.
Reach: certified initializer heads, actual native sync operations and monotone native store growth.
Limit: saved-stack, queued-command and scope-store invariants remain separate producers.
Consumer: initialized native primitive evaluation and concrete cleanup writer classification.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- An initializer source root is a binder or frontier, never a direct synchronous operation. -/
theorem initial_not_sync (spec : Spec) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) (thunk : EffThunk) : resolve spec.root point ≠ .sync thunk := by
  intro same
  cases amount : point.fuel with
  | zero =>
    unfold resolve at same
    split at same
    · rw [Agreement.compileEff_at_zero _ amount] at same
      cases same
    · cases same
  | succ fuel =>
    by_cases small : index < spec.initialization.width
    · rw [spec.initialization.compile index point fuel small stage.2.2.1 amount] at same
      cases same
    · have bound := stage.1
      have last : index = spec.initialization.width := by omega
      subst index
      obtain ⟨tail, found⟩ := spec.gate_head
      rw [← stage.2.2.1] at found
      rw [Agreement.resolve_of_at found, Agreement.compileEff_bind _ _ amount] at same
      cases same

/-- Every actual native synchronous operation grows only the counted allocation stores. -/
theorem sync_future (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (thunk : EffThunk) (state : Stores) (value : Val)
    (ran : (interpAt spec.root completed spec.table).syncState thunk world.state = some (state, value)) :
    Future world ⟨world.owner, state⟩ := by
  cases thunk
  case op operation =>
    have growth := syncOpStep_le operation world.state state value ran
    exact ⟨rfl, growth.1, growth.2.1⟩
  case store thunk =>
    cases thunk
    case op operation =>
      have growth := syncOpStep_le operation world.state state value ran
      exact ⟨rfl, growth.1, growth.2.1⟩
    all_goals cases ran
  all_goals cases ran

/-- The actual allocator returns its old reference length and appends exactly one reference cell. -/
theorem allocation_value (spec : Spec) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) (initial : Val) :
    ValueAt spec ⟨world.owner, {world.state with refs := world.state.refs ++ [initial]}⟩
      (.allocated index) (.cell ⟨world.state.refs.length⟩) := by
  obtain ⟨bound, owner, path, env, refs, deferred, source⟩ := stage
  refine ⟨.inl owner, ?_, ?_, deferred⟩
  · rw [refs]
  · change (world.state.refs ++ [initial]).length = index + 1
    rw [List.length_append, List.length_singleton, refs]

/-- The actual first deferred allocation returns the gate key and enters the ready phase. -/
theorem gate_value (spec : Spec) (world : World) (point : Point)
    (stage : RootStage spec world spec.initialization.width point) :
    ValueAt spec ⟨world.owner, {world.state with deferreds := world.state.deferreds.make.2}⟩ .gate
      (.promise world.state.deferreds.make.1) := by
  obtain ⟨bound, owner, path, env, refs, deferred, source⟩ := stage
  refine ⟨?_, ?_, ?_⟩
  · change Val.promise ⟨world.state.deferreds.cells.length⟩ = Val.promise ⟨0⟩
    rw [deferred]
  · exact Nat.le_of_eq refs.symm
  · change 1 ≤ (world.state.deferreds.cells ++ [_]).length
    rw [List.length_append, List.length_singleton]
    omega
/-- An actual native sync reply satisfies its current allocation or protected stable answer class. -/
theorem sync_value (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (kind : Kind) (thunk : EffThunk) (state : Stores) (value : Val)
    (owned : CodeAt spec world kind (.sync thunk))
    (ran : (interpAt spec.root completed spec.table).syncState thunk world.state = some (state, value)) :
    ValueAt spec ⟨world.owner, state⟩ kind value := by
  generalize same : Prim.sync thunk = program at owned
  cases owned with
  | success good | failure phase => cases same
  | initial stage => exact (initial_not_sync spec world _ _ stage thunk same.symm).elim
  | allocating small stage =>
    cases same
    dsimp only [interpAt, interpOf, syncOpStep, refStep, Option.map] at ran
    cases ran
    exact allocation_value spec world _ _ stage _
  | gateAllocating stage =>
    cases same
    change some ({world.state with deferreds := world.state.deferreds.make.2}, .promise world.state.deferreds.make.1) =
      some (state, value) at ran
    cases ran
    exact gate_value spec world _ stage
  | stable ready held =>
    cases same
    obtain ⟨rfl, allowed⟩ := held
    exact ⟨.inr (ready_future spec world _ (sync_future spec completed world thunk state value ran) ready), trivial⟩
  | frontier zero phase | yielding phase refs deferred pending | bound first callback | yieldThen phase held => cases same

/-- A native sync fallback is possible only at the protected stable broad answer class. -/
theorem sync_fallback (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (kind : Kind) (thunk : EffThunk) (owned : CodeAt spec world kind (.sync thunk))
    (missing : (interpAt spec.root completed spec.table).syncState thunk world.state = none) :
    ValueAt spec world kind ((interpAt spec.root completed spec.table).syncValue thunk) := by
  generalize same : Prim.sync thunk = program at owned
  cases owned with
  | success good | failure phase => cases same
  | initial stage => exact (initial_not_sync spec world _ _ stage thunk same.symm).elim
  | allocating small stage => cases same; cases missing
  | gateAllocating stage => cases same; cases missing
  | stable ready held =>
    cases same
    obtain ⟨rfl, allowed⟩ := held
    exact ⟨.inr ready, trivial⟩
  | frontier zero phase | yielding phase refs deferred pending | bound first callback | yieldThen phase held => cases same
end Effect4.Program.AnswerSlots.Initialized

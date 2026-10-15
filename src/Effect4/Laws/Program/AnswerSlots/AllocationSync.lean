import Effect4.Laws.Program.AnswerSlots.AllocationHead

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual initializer sync replies share the exact allocation world with their saved callback.
Reach: actual native synchronous store updates, or the explicit source entry marker.
Consumer: the common bare native evaluator for Atomic and Timeout histories.
The entry alternative requires the caller's joint numeric invariant activation.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts

/-- Actual prefix resolution exposes one binder, a source frontier or its located failure. -/
theorem initial_shape (spec : Spec) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) (active : Active spec index) :
    (∃ body name, resolve spec.root point = .onSuccess body name) ∨
    resolve spec.root point = frontier point ∨ (∃ cause, resolve spec.root point = .failure cause) := by
  change (∃ body name, resolve spec.stable.root point = .onSuccess body name) ∨
    resolve spec.stable.root point = frontier point ∨ (∃ cause, resolve spec.stable.root point = .failure cause)
  cases amount : point.fuel with
  | zero =>
    unfold resolve
    split
    · rw [Agreement.compileEff_at_zero _ amount]
      exact .inr (.inl rfl)
    · exact .inr (.inr ⟨_, rfl⟩)
  | succ fuel =>
    by_cases small : index < spec.initialization.width
    · rw [spec.initialization.compile index point fuel small stage.stage.source.2.1 amount]
      exact .inl ⟨_, _, rfl⟩
    · have last : index = spec.initialization.width := by
        have bound := stage.stage.source.1
        omega
      subst index
      have available : spec.gate.isSome = true := active.resolve_left small
      cases present : spec.gate with
      | none => rw [present] at available; cases available
      | some gate =>
        obtain ⟨tail, found⟩ := gate.head
        rw [← stage.stage.source.2.1] at found
        rw [Agreement.resolve_of_at found, Agreement.compileEff_bind _ _ amount]
        exact .inl ⟨_, _, rfl⟩

/-- An actual prefix binder cannot itself be a direct synchronous operation. -/
theorem initial_not_sync (spec : Spec) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) (active : Active spec index) (thunk : EffThunk) :
    resolve spec.root point ≠ .sync thunk := by
  intro same
  rcases initial_shape spec world index point stage active with ⟨body, name, shape⟩ | shape | ⟨cause, shape⟩
  all_goals rw [shape] at same
  all_goals cases same

/-- Actual synchronous store steps preserve the independent entry flag and grow allocation counts. -/
theorem sync_future (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (thunk : EffThunk) (state : Stores) (value : Val)
    (ran : (interpAt spec.root view spec.table).syncState thunk world.state = some (state, value)) :
    Future world ⟨world.owner, state, world.entered⟩ := by
  cases thunk
  case op operation =>
    have growth := syncOpStep_le operation world.state state value ran
    exact ⟨rfl, growth.1, growth.2.1, fun held => held⟩
  case store thunk =>
    cases thunk
    case op operation =>
      have growth := syncOpStep_le operation world.state state value ran
      exact ⟨rfl, growth.1, growth.2.1, fun held => held⟩
    all_goals cases ran
  all_goals cases ran

/-- A real native sync answer has its actual class, unless the exact entry hook must run first. -/
theorem sync_or_entry (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (kind : Kind spec.stable.Kind) (thunk : EffThunk) (state : Stores) (value : Val)
    (owned : CodeAt spec world kind (.sync thunk))
    (ran : (interpAt spec.root view spec.table).syncState thunk world.state = some (state, value)) :
    ValueAt spec ⟨world.owner, state, world.entered⟩ kind value ∨
      ∃ point, kind = .stable spec.stable.rootKind ∧ .sync thunk = resolve spec.root point ∧ Entry spec world point := by
  generalize same : Prim.sync thunk = program at owned
  cases owned with
  | success good | failure phase => cases same
  | initial stage active => exact (initial_not_sync spec world _ _ stage active thunk same.symm).elim
  | allocating small stage =>
    cases same
    exact .inl (allocated_actual spec world _ _ stage state value ran).2
  | gateAllocating stage available =>
    cases same
    exact .inl (gate_actual spec world _ stage available state value ran).2
  | @reading refs deferred cell phase refsEq deferredEq pending contents entered =>
    cases same
    change syncOpStep (.refGet cell) world.state = some (state, value) at ran
    cases peek : refPeek world.state.refs cell with
    | none =>
      simp only [syncOpStep, refStep, peek, Option.map_none] at ran
      cases ran
    | some answer =>
      simp only [syncOpStep, refStep, peek, Option.map_some] at ran
      cases ran
      exact .inl ⟨phase, refsEq, deferredEq, pending, contents, entered⟩
  | entered fragment entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready held =>
    cases same
    exact .inl ⟨ready_future spec world _ (sync_future spec view world thunk state value ran) ready,
      spec.sync_value _ thunk value held⟩
  | frontier zero phase | yielding phase refs deferred pending contents entered
    | yieldThen phase held pending => cases same

/-- An absent native operation retains its real fallback value at the ignored or stable class. -/
theorem fallback_or_entry (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (kind : Kind spec.stable.Kind) (thunk : EffThunk) (owned : CodeAt spec world kind (.sync thunk))
    (missing : (interpAt spec.root view spec.table).syncState thunk world.state = none) :
    ValueAt spec world kind ((interpAt spec.root view spec.table).syncValue thunk) ∨
      ∃ point, kind = .stable spec.stable.rootKind ∧ .sync thunk = resolve spec.root point ∧ Entry spec world point := by
  generalize same : Prim.sync thunk = program at owned
  cases owned with
  | success good | failure phase => cases same
  | initial stage active => exact (initial_not_sync spec world _ _ stage active thunk same.symm).elim
  | allocating small stage => cases same; cases missing
  | gateAllocating stage available => cases same; cases missing
  | reading phase refs deferred pending contents entered =>
    cases same
    exact .inl ⟨phase, refs, deferred, pending, contents, entered⟩
  | entered fragment entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready held =>
    cases same
    exact .inl ⟨ready, spec.sync_value _ thunk _ held⟩
  | frontier zero phase | yielding phase refs deferred pending contents entered
    | yieldThen phase held pending => cases same

/-- A real pending sync step preserves the exact initial prefix or exposes the application entry. -/
theorem pending_sync_heap_or_entry (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (kind : Kind spec.stable.Kind) (thunk : EffThunk) (state : Stores) (value : Val)
    (owned : CodeAt spec world kind (.sync thunk)) (pending : world.entered = false)
    (heap : HeapPrefix spec world.state)
    (ran : (interpAt spec.root view spec.table).syncState thunk world.state = some (state, value)) :
    HeapPrefix spec state ∨
      ∃ point, kind = .stable spec.stable.rootKind ∧ .sync thunk = resolve spec.root point ∧ Entry spec world point := by
  generalize same : Prim.sync thunk = program at owned
  cases owned with
  | success good | failure phase => cases same
  | initial stage active => exact (initial_not_sync spec world _ _ stage active thunk same.symm).elim
  | @allocating index point small stage =>
    cases same
    obtain ⟨key, written⟩ := Initialization.actual spec.initialization _ world.state state value ran
    subst state
    have refs : (world.state.refs ++ [spec.initialization.initial index]).length = index + 1 := by
      rw [List.length_append, List.length_singleton, stage.stage.source.2.2.2.1]
    apply Or.inl
    refine ⟨?_, ?_, ?_⟩
    · rw [refs, stage.stage.contents, Initialization.values_next]
    · rw [refs]
      exact small
    · change world.state.deferreds.cells.length ≤ spec.gateNeed
      rw [stage.deferreds]
      exact Nat.zero_le _
  | gateAllocating stage available =>
    cases same
    change syncOpStep .deferredMake world.state = some (state, value) at ran
    rw [syncOpStep_deferredMake] at ran
    cases ran
    apply Or.inl
    refine ⟨?_, ?_, ?_⟩
    · change world.state.refs = Initialization.values spec.initialization world.state.refs.length
      rw [stage.stage.source.2.2.2.1]
      exact stage.stage.contents
    · exact Nat.le_of_eq stage.stage.source.2.2.2.1
    · change (world.state.deferreds.cells ++ [_]).length ≤ spec.gateNeed
      rw [List.length_append, List.length_singleton, stage.deferreds]
      have need : spec.gateNeed = 1 := by simp only [Spec.gateNeed, available, ↓reduceIte]
      rw [need]
      exact Nat.le_refl 1
  | @reading refs deferred cell phase refsEq deferredEq missing contents entered =>
    cases same
    change syncOpStep (.refGet cell) world.state = some (state, value) at ran
    cases peek : refPeek world.state.refs cell with
    | none =>
      simp only [syncOpStep, refStep, peek, Option.map_none] at ran
      cases ran
    | some answer =>
      simp only [syncOpStep, refStep, peek, Option.map_some] at ran
      cases ran
      exact .inl heap
  | entered fragment entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready held => exact (pending_not_ready spec world pending ready).elim
  | frontier zero phase | yielding phase refs deferred missing contents entered
    | yieldThen phase held missing => cases same

end Effect4.Program.AnswerSlots.AllocationAdapter

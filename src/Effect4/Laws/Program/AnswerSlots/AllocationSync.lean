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

/-- The source prefix root is a binder or frontier and cannot itself be a direct sync operation. -/
theorem initial_not_sync (spec : Spec) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) (active : Active spec index) (thunk : EffThunk) :
    resolve spec.root point ≠ .sync thunk := by
  intro same
  change resolve spec.stable.root point = .sync thunk at same
  cases amount : point.fuel with
  | zero =>
    unfold resolve at same
    split at same
    · rw [Agreement.compileEff_at_zero _ amount] at same
      cases same
    · cases same
  | succ fuel =>
    by_cases small : index < spec.initialization.width
    · rw [spec.initialization.compile index point fuel small stage.stage.source.2.1 amount] at same
      cases same
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
        rw [Agreement.resolve_of_at found, Agreement.compileEff_bind _ _ amount] at same
        cases same

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
  | entered fragment entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready held =>
    cases same
    exact .inl ⟨.inr (ready_future spec world _ (sync_future spec view world thunk state value ran) ready),
      spec.sync_value _ thunk value held⟩
  | frontier zero phase | yielding phase refs deferred pending contents entered
    | bound first callback | yieldThen phase held pending => cases same

end Effect4.Program.AnswerSlots.AllocationAdapter

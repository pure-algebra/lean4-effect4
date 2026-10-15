import Test.Dogfood.Scenario.Atomic.StageNativeData

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Consumer: the actual Atomic native configuration's empty deferred store.
The existing local primitive proof reads actual source operation permissions.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Every actual reference-kernel operation leaves the deferred store unchanged. -/
theorem ref_deferreds (operation : SyncOp) (cell : RefKey) (kernel : RefKernel)
    (shape : operation.refKernel = some (cell, kernel)) (before after : Stores) (value : Val)
    (actual : syncOpStep operation before = some (after, value)) : after.deferreds = before.deferreds := by
  rw [syncOpStep_eq_refStepOf shape before] at actual
  cases step : refStepOf cell kernel before.refs with
  | none => rw [step] at actual; cases actual
  | some pair =>
    simp only [step, Option.map_some] at actual
    cases actual
    rfl

/-- The daemon's two synchronous forms change only references or timers. -/
theorem daemon_sync_deferreds (root : NativeEff) (table : RowTable) (thunk : EffThunk)
    (shape : DaemonGraph.SyncAt thunk) (before after : Stores) (value : Val)
    (actual : (interpOf root table).syncState thunk before = some (after, value)) :
    after.deferreds = before.deferreds := by
  cases shape with
  | refill env length =>
    exact ref_deferreds (.refUpdate ⟨0⟩ (Store.refillAt 5) env) ⟨0⟩ _ rfl before after value actual
  | cancel waiter token =>
    change syncOpStep (.sleepCancel waiter token) before = some (after, value) at actual
    rw [syncOpStep_sleepCancel before waiter token] at actual
    cases actual
    rfl

/-- The root's actual synchronous forms leave the deferred store unchanged. -/
theorem root_sync_deferreds (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (kind : StageWorld.Kind) (thunk : EffThunk)
    (held : RootGraph.CodeAt built.program built.table world kind (.sync thunk))
    (before after : Stores) (value : Val)
    (actual : (interpOf built.program built.table).syncState thunk before = some (after, value)) :
    after.deferreds = before.deferreds := by
  rcases (RootGraph.sync_shape built accepted world kind thunk held).2 with rfl | daemon
  · exact ref_deferreds (.refGet ⟨0⟩) ⟨0⟩ _ rfl before after value actual
  · exact daemon_sync_deferreds built.program built.table thunk daemon before after value actual

/-- The request's four synchronous source forms are reference-kernel operations. -/
theorem request_sync_deferreds (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (owner : Nat) (kind : StageWorld.Kind) (thunk : EffThunk)
    (held : StageGraph.CodeAt root table owner world kind (.sync thunk))
    (before after : Stores) (value : Val)
    (actual : (interpOf root table).syncState thunk before = some (after, value)) :
    after.deferreds = before.deferreds := by
  cases held with
  | @decision _ env waiting =>
    exact ref_deferreds (.refModify ⟨0⟩ (Store.decisionAt env.length) env) ⟨0⟩ _ rfl before after value actual
  | @deposit _ env admitted =>
    exact ref_deferreds (.refModify ⟨1⟩ (Store.depositAt owner env.length) env) ⟨1⟩ _ rfl before after value actual
  | reading => exact ref_deferreds (.refGet ⟨0⟩) ⟨0⟩ _ rfl before after value actual
  | @note _ env used admitted rejected positive =>
    exact ref_deferreds (.refUpdate ⟨2⟩ (Store.noteAt owner (env.length + 1))
      (env ++ [Test.Dogfood.P4RateLimiter.windowVal used admitted rejected])) ⟨2⟩ _ rfl before after value actual

/-- Actual request native evaluation leaves its deferred store unchanged. -/
theorem request_native_deferreds (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (owner : Nat) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : StageGraph.FrameAt root table owner world fiber.frame) (recorded : StageGraph.Recorded fiber.frame) :
    (evaluateNative root machine fiber yielding table).machine.state.deferreds = machine.state.deferreds := by
  rw [StageGraph.native_primitive_eq root table owner world machine fiber yielding held recorded]
  obtain ⟨kind, code, saved⟩ := held
  apply StatePreservation.primitive_at (interpAt root machine.completedExits table)
    (fun state => state.deferreds = machine.state.deferreds) machine fiber yielding rfl
  · intro thunk after value current actual
    exact request_sync_deferreds root table world owner kind thunk (current ▸ code) machine.state after value actual
  · intro name signal cancel current
    have ordinary := StageGraph.ordinary_shape root table owner machine.completedExits world kind fiber.frame.current code
    exact (ordinary.2.2 name signal cancel current).elim
  · intro thunk action current found
    have ordinary := StageGraph.ordinary_shape root table owner machine.completedExits world kind fiber.frame.current code
    exact (ordinary.2.1 thunk current).elim

/-- Actual daemon native evaluation changes references or timers, leaving deferred replies unchanged. -/
theorem daemon_native_deferreds (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : DaemonGraph.FrameAt root table world fiber.frame) :
    (evaluateNative root machine fiber yielding table).machine.state.deferreds = machine.state.deferreds := by
  rw [DaemonGraph.native_primitive_eq root table world machine fiber yielding held]
  apply StatePreservation.primitive_at (interpAt root machine.completedExits table)
    (fun state => state.deferreds = machine.state.deferreds) machine fiber yielding rfl
  · intro thunk after value current actual
    exact daemon_sync_deferreds root table thunk
      (DaemonGraph.sync_shape root table _ held.1 thunk current) machine.state after value actual
  · intro name signal cancel current
    obtain ⟨rfl, rfl, rfl⟩ := DaemonGraph.async_shape root table name signal cancel (current ▸ held.1)
    rfl
  · intro thunk action current found
    rw [(DaemonGraph.action_frame root table world machine.completedExits machine fiber yielding thunk action held current found).1]

/-- Actual root native evaluation preserves the empty deferred-store entry certificate. -/
theorem root_native_deferreds (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (fresh : Fresh world) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : RootGraph.FrameAt built.program built.table world fiber.frame)
    (heap : HeapAt world machine.state) (counter : machine.nextId = world.nextId) :
    (evaluateNative built.program machine fiber yielding built.table).machine.state.deferreds = machine.state.deferreds := by
  rw [RootGraph.native_primitive_eq built accepted world machine fiber yielding held]
  obtain ⟨kind, code, saved⟩ := held
  apply StatePreservation.primitive_at (interpAt built.program machine.completedExits built.table)
    (fun state => state.deferreds = machine.state.deferreds) machine fiber yielding rfl
  · intro thunk after value current actual
    exact root_sync_deferreds built accepted world kind thunk (current ▸ code) machine.state after value actual
  · intro name signal cancel current
    obtain ⟨millis, rfl, rfl, rfl, owns, values⟩ := RootGraph.async_shape built accepted world kind name signal cancel (current ▸ code)
    rfl
  · intro thunk action current found
    obtain ⟨next, future, freshNext, counterNext, heapNext, actor, rows, same⟩ :=
      RootGraph.action_result built accepted machine.completedExits world fresh machine fiber yielding kind thunk action
        (current ▸ code) current heap counter saved found (fun _ => True) (fun _ _ _ => Or.inr True.intro)
    rw [same.1]

end Test.Dogfood.Scenario.Atomic.StageConfiguration

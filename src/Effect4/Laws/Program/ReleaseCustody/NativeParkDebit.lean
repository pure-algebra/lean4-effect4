import Effect4.Laws.Program.ReleaseCustody.NativePrimitiveDebit
import Effect4.Laws.Program.ReleaseCustody.ReplySequencing

/-!
Concept: scope-lifetime-finalization R11.
Question: actual parked evaluator clauses serve Execution.history and Workers.releases_step.
Reach: actual native parks with distinct fiber identities and the existing saved-frame assertion.
Limit: local accounting establishes neither command sequencing nor admitted-history closure.
Unlock: the primitive evaluator census composes actual waits with frame and action debit.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.NativeParkDebit
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing

/-- A suspended native park has no pending scope-add response.
Consumer: the actual park evaluator clauses. -/
theorem suspended_clean (thunk : EffThunk) (frames : List NCode)
    (held : Kept (.suspend thunk) frames) : NoAdd frames := by
  apply opaque_noAdd held
  · intro fin phase; cases phase
  · intro phase; cases phase

/-- The actual exit-value hook creates no foreign-release reservation.
Consumer: already-finished join responses. -/
theorem exit_zero (q : List Nat) (root : NativeEff) (completed) (table : RowTable)
    (exit : ExitV) (mode : Supervision.ObserverMode) :
    currentCredits q ((interpAt root completed table).exitValue exit mode) = 0 := by
  cases mode
  · rfl
  · cases exit <;> rfl

/-- A race-free configuration has no registration program to launch.
Consumer: the selected actual race park in the primitive census. -/
theorem race_missing (q : List Nat) (m : NativeMachine) (fiber : Control.Fiber)
    (yielding : Bool) (race : Nat) (empty : m.races = []) :
    IterDebit q m fiber (registerRace m fiber yielding race) := by
  have absent : m.race? race = none := by simp only [RunMachine.race?, empty, List.find?_nil]
  simp only [registerRace, absent]
  unfold IterDebit
  simp only [List.map_nil, List.sum_nil, Nat.add_zero]
  exact Nat.le_refl _

/-- Native join waits retain caller custody and alter only the target's observer metadata.
Consumer: the full actual primitive evaluator debit. -/
theorem join (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (thunk : EffThunk) (target : FiberId)
    (mode : Supervision.ObserverMode) (current : fiber.frame.current = .suspend thunk)
    (park : (interpAt root m.completedExits table).parkOf (.suspend thunk) = some (.ok (.join target mode)))
    (held : Kept fiber.frame.current fiber.frame.stack) (unique : (m.fibers.map RunFiber.id).Nodup) :
    IterDebit q m fiber (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have clean := suspended_clean thunk fiber.frame.stack (current ▸ held)
  have full (active : NCode) := noAdd_full q active fiber.frame.stack clean
  cases found : m.fiber? target with
  | none =>
    unfold IterDebit
    simp only [evaluatePrim, current, park, found, List.map_nil, List.sum_nil, Nat.add_zero]
    exact Nat.le_refl _
  | some other =>
    cases exited : other.exit with
    | some exit =>
      unfold IterDebit
      simp only [evaluatePrim, current, park, found, exited, List.map_nil, List.sum_nil,
        Nat.add_zero, fiberCredits, exit_zero, full, Nat.zero_add]
      omega
    | none =>
      have found' : m.fiber? other.id = some other := by
        rw [RunMachine.id_of_fiber? found]
        exact found
      have outside := outside_update_le q m fiber.id other
        {other with observers := other.observers ++ [.resumeAwait fiber.id m.nextToken mode]}
        unique found' rfl (Nat.le_refl _)
      simp only [exited] at outside
      unfold IterDebit
      simp only [evaluatePrim, current, park, found, exited, RunMachine.emit_trace,
        List.countP_append, List.countP_cons, List.countP_nil, ReleaseTrace.releaseAt,
        ReleaseTrace.registeredAt, Bool.false_eq_true, if_false, RunMachine.update_trace,
        List.map_nil, List.sum_nil, Nat.add_zero, fiberCredits, RunFiber.park, stackCredits,
        futureCredits, full, Nat.zero_add]
      simp only [outsideCredits, RunMachine.emit, RunMachine.update] at outside ⊢
      omega

/-- Every native suspended park preserves its release reservation.
Consumer: the complete primitive evaluator census. -/
theorem suspend (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool) (thunk : EffThunk)
    (current : fiber.frame.current = .suspend thunk)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (unique : (m.fibers.map RunFiber.id).Nodup) (races : m.races = []) :
    IterDebit q m fiber (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have clean := suspended_clean thunk fiber.frame.stack (current ▸ held)
  cases park : (interpAt root m.completedExits table).parkOf (.suspend thunk) with
  | none =>
    simpa only [evaluatePrim, current, park] using
      NativeAccounting.step_frame q root m.completedExits table m fiber yielding
  | some result =>
    cases result with
    | error cause =>
      simpa only [evaluatePrim, current, park] using
        NativeActionDebit.replace_current q m fiber yielding (.failure cause) .continue_ clean (Nat.zero_le _)
    | ok kind =>
      cases kind with
      | race rid =>
        simpa only [evaluatePrim, current, park] using race_missing q m fiber yielding rid races
      | awaitAll targets =>
        simpa only [evaluatePrim, current, park, IterDebit] using
          NativeActionDebit.countdown q root table m fiber yielding targets .exitsValue false clean unique (Or.inl rfl)
      | join target mode => exact join q root table m fiber yielding thunk target mode current park held unique

/-- Every actual primitive evaluator case accounts for its foreign-release custody.
Consumer: native scoped evaluator assembly and the original admitted Workers history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem primitive (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Control.Fiber) (yielding : Bool)
    (held : Kept fiber.frame.current fiber.frame.stack)
    (fragment : SourceScope.Fragment root) (owned : SourceScope.FrameAt root fiber.frame)
    (sequential : SourceScope.SequentialSource root)
    (fibers : (m.fibers.map RunFiber.id).Nodup)
    (scopes : (m.state.scopes.entries.map ScopeEntry.key).Nodup) (fresh : m.state.ScopeKeysFresh)
    (races : m.races = []) :
    IterDebit q m fiber (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have ordinary := NativeAccounting.step_frame q root m.completedExits table m fiber yielding
  cases current : fiber.frame.current
  case yieldNowWith priority =>
    exact NativePrimitiveDebit.yielding q root table m fiber yielding priority current held
  case async register signal cancel =>
    exact NativePrimitiveDebit.asynchronous q root table m fiber yielding register signal cancel current held
  case success value =>
    have park : (interpAt root m.completedExits table).parkOf (.success value) = none := rfl
    simpa only [evaluatePrim, current, park] using
      NativePrimitiveDebit.finalizer q root m.completedExits table m fiber yielding (.success value) held
  case failure cause =>
    have park : (interpAt root m.completedExits table).parkOf (.failure cause) = none := rfl
    simpa only [evaluatePrim, current, park] using
      NativePrimitiveDebit.finalizer q root m.completedExits table m fiber yielding (.failure cause) held
  case withFiber thunk =>
    have park : (interpAt root m.completedExits table).parkOf (.withFiber thunk) = none := rfl
    cases selected : (interpAt root m.completedExits table).withFiberOf thunk with
    | none => simpa only [evaluatePrim, current, park, selected] using ordinary
    | some action =>
      simpa only [evaluatePrim, current, park, selected] using
        NativeActionDebit.native_action q root table m fiber yielding thunk action current held fragment
          owned sequential fibers scopes fresh selected
  case sync thunk =>
    cases response : (interpAt root m.completedExits table).syncState thunk m.state with
    | none => exact NativePrimitiveDebit.sync_none q root table m fiber yielding thunk current response
    | some result =>
      obtain ⟨state, value⟩ := result
      exact NativePrimitiveDebit.sync_some q root table m fiber yielding thunk state value current held scopes fresh response
  case suspend thunk => exact suspend q root table m fiber yielding thunk current held fibers races
  all_goals
    simp only [evaluatePrim, current]
    exact ordinary

end Effect4.Program.ReleaseCustody.NativeParkDebit

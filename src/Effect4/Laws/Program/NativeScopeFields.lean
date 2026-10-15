import Effect4.Laws.Machine.ScopeFields
import Effect4.Laws.Machine.StatePreservation
import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Program.NativeEvaluation

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: captured connection values serve the two crews' release-log claims.
Reach: every native command, with the actual synchronous operation's field permission.
The permission comes from the answer-flow invariant at its looked-up fiber.
This file supplies no source permission, answer class, or history premise itself.
Consumer: the coupled answer-flow and captured-scope invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.ScopeFields
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Machine.ScopeFields

/-- A native synchronous thunk carries only its represented operation's field obligation. -/
def ThunkAt (model : Model) : EffThunk → Prop
  | .op operation | .store (.op operation) => OperationAt model operation
  | _ => True

/-- The active synchronous operation supplies the capture that registration stores. -/
def CurrentAt (model : Model) (code : NCode) : Prop :=
  ∀ thunk, code = .sync thunk → ThunkAt model thunk

/-- Native registration changes deferred cells and timers, never captured scope fields. -/
theorem register_scopes (root : NativeEff) (completed) (table : RowTable)
    (name : EffName) (id : FiberId) (token : Nat) (state : Stores) :
    ((interpAt root completed table).registerAsync name id token state).1.scopes = state.scopes := by
  cases name
  case store name => cases name <;> rfl
  all_goals rfl

/-- Native synchronous execution retains captures under its actual operation permission. -/
theorem sync_scopes (model : Model) (root : NativeEff) (completed) (table : RowTable)
    (thunk : EffThunk) (state next : Stores) (value : Val)
    (held : ScopesAt model state.scopes) (allowed : ThunkAt model thunk)
    (ran : (interpAt root completed table).syncState thunk state = some (next, value)) :
    ScopesAt model next.scopes := by
  cases thunk
  case op operation => exact sync_scopes_at model operation state next value held allowed ran
  case store stored =>
    cases stored
    case op operation => exact sync_scopes_at model operation state next value held allowed ran
    all_goals cases ran
  all_goals cases ran

/-- Unsafe close removes the saved fields before returning its cleanup program. -/
theorem close_unsafe_scopes (model : Model) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Program) (held : ScopesAt model state.scopes)
    (closed : storesCloseScopeUnsafe scope exit flag state = some (next, program)) :
    ScopesAt model next.scopes := by
  unfold storesCloseScopeUnsafe at closed
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at closed; cases closed
  | some result =>
    rcases result with ⟨after, strategy, order⟩
    have scopes := (close_snapshot_at model scope exit state after strategy order held snapshot).1
    simp only [snapshot, Option.pure_def] at closed
    cases order with
    | nil => cases closed; exact scopes
    | cons first rest => cases rest <;> cases closed <;> exact scopes

/-- Public close removes the same fields before its administrative continuation. -/
theorem close_public_scopes (model : Model) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Program) (held : ScopesAt model state.scopes)
    (closed : storesCloseScope scope exit flag state = some (next, program)) :
    ScopesAt model next.scopes := by
  unfold storesCloseScope at closed
  cases snapshot : scopeCloseSnapshot scope exit state with
  | none => rw [snapshot] at closed; cases closed
  | some result =>
    rcases result with ⟨after, strategy, order⟩
    have scopes := (close_snapshot_at model scope exit state after strategy order held snapshot).1
    simp only [snapshot, Option.pure_def] at closed
    cases order with
    | nil => cases closed; exact scopes
    | cons first rest => cases rest <;> cases closed <;> exact scopes

/-- Native public close embeds its cleanup without changing the retained scope result. -/
theorem close_scopes (model : Model) (root : NativeEff) (completed) (table : RowTable)
    (scope : Nat) (exit : ExitV) (flag : Bool) (fiber : FiberId)
    (state next : Stores) (program : Option NCode) (held : ScopesAt model state.scopes)
    (closed : (interpAt root completed table).closeScope scope exit flag fiber state = some (next, program)) :
    ScopesAt model next.scopes := by
  change (storesCloseScope scope exit flag state).map (fun r => (r.1, r.2.map embed)) =
    some (next, program) at closed
  obtain ⟨⟨after, closing⟩, operation, same⟩ := Option.map_eq_some_iff.mp closed
  cases same
  exact close_public_scopes model scope exit flag state after closing held operation

/-- Administrative commands introduce only interrupt finalizers and retain all saved captures. -/
theorem command_hooks (model : Model)
    (interrupt : ∀ fiber flag, model.finalizer (.interruptFiber fiber flag))
    (root : NativeEff) (completed) (table : RowTable) :
    StatePreservation.CommandHooks (interpAt root completed table)
      (fun state => ScopesAt model state.scopes) := by
  constructor
  · intro mode scope id state next key held linked
    simp only [interpAt, interpOf] at linked
    split at linked
    · cases linked
    · cases linked
      exact scope_register_at model state.scopes scope state.nextName _ held (interrupt _ _)
  · intro scope key state next held dropped
    change (match state.scopes.entryAt scope with
      | none => none
      | some _ => some {state with scopes := state.scopes.removeFinalizer scope key}) = some next at dropped
    split at dropped
    · cases dropped
    · cases dropped
      exact scope_remove_at model state.scopes scope key held
  · intro state held
    exact held
  · intro list phase state held
    change ScopesAt model (Stores.wakeList list phase state).scopes
    unfold Stores.wakeList
    split <;> exact held

/-- The existing primitive producer reads the permission only at a real synchronous head. -/
theorem primitive_scopes (model : Model)
    (interrupt : ∀ fiber flag, model.finalizer (.interruptFiber fiber flag))
    (root : NativeEff) (completed) (table : RowTable) (m : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : ScopesAt model m.state.scopes) (allowed : CurrentAt model fiber.frame.current) :
    ScopesAt model (evaluatePrim (interpAt root completed table) m fiber yielding).machine.state.scopes := by
  have producer := Moves.evaluatePrim_producer (interpAt root completed table) m fiber yielding
  generalize actual : evaluatePrim (interpAt root completed table) m fiber yielding = result at producer ⊢
  cases producer with
  | step => exact StatePreservation.stepFrame _ (fun state : Stores => ScopesAt model state.scopes) m fiber yielding held
  | finalizer exit current => exact StatePreservation.finalizerOr _ (fun state : Stores => ScopesAt model state.scopes) m fiber yielding exit held
  | action thunk action current unparked found =>
    exact StatePreservation.withFiber_on _ _ (command_hooks model interrupt root completed table)
      (close_scopes model root completed table) m fiber yielding action held
  | sync thunk next value current unparked found =>
    exact sync_scopes model root completed table thunk m.state next value held (allowed thunk current) found
  | asyncImmediate name signal cancel next code current registered =>
    have kept := register_scopes root completed table name fiber.id m.nextToken m.state
    rw [registered] at kept
    exact kept ▸ held
  | asyncParked name signal cancel next current registered =>
    have kept := register_scopes root completed table name fiber.id m.nextToken m.state
    rw [registered] at kept
    exact kept ▸ held
  | racePark race park =>
    unfold registerRace
    split <;> exact held
  | countdownPark targets next returned parked edits park counted =>
    have kept := StatePreservation.countdown_plan_state (interpAt root completed table) m fiber targets .exitsValue false
    rw [counted] at kept
    exact congrArg Stores.scopes kept ▸ held
  | fallback | yieldNow | rejectedPark | joinMissing | joinExited | joinWaiting => exact held

/-- The scoped callback closes actual saved fields before any cleanup runs. -/
theorem exit_scopes (model : Model)
    (interrupt : ∀ fiber flag, model.finalizer (.interruptFiber fiber flag))
    (root : NativeEff) (m : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV) (held : ScopesAt model m.state.scopes)
    (allowed : CurrentAt model fiber.frame.current) :
    ScopesAt model (exitScoped root m fiber yielding exit).machine.state.scopes := by
  generalize actual : exitScoped root m fiber yielding exit = result
  unfold exitScoped at actual
  dsimp only at actual
  split at actual
  · split at actual
    · cases actual
      exact held
    · rename_i state program closed
      have kept := close_unsafe_scopes model _ _ _ m.state state program held closed
      cases program <;> cases actual <;> exact kept
  · cases actual
    exact primitive_scopes model interrupt root m.completedExits [] m fiber yielding held allowed

/-- Native entry creates an empty sequential scope; other heads use the same local store permission. -/
theorem native_scopes (model : Model)
    (interrupt : ∀ fiber flag, model.finalizer (.interruptFiber fiber flag))
    (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : ScopesAt model m.state.scopes) (allowed : CurrentAt model fiber.frame.current) :
    ScopesAt model (evaluateNative root m fiber yielding table).machine.state.scopes := by
  generalize actual : evaluateNative root m fiber yielding table = result
  unfold evaluateNative at actual
  split at actual
  · split at actual
    · cases actual
      exact scope_make_at model m.state.scopes m.state.nextName .sequential held model.sequential
    · cases actual
      exact primitive_scopes model interrupt root m.completedExits table m fiber yielding held allowed
  · cases actual
    exact exit_scopes model interrupt root m fiber yielding _ held allowed
  · cases actual
    exact exit_scopes model interrupt root m fiber yielding _ held allowed
  · cases actual
    exact primitive_scopes model interrupt root m.completedExits table m fiber yielding held allowed

/-- Runloop interruption replaces the current program only with a failure. -/
theorem current_top (model : Model) (fiber : SourceScope.SourceFiber)
    (allowed : CurrentAt model fiber.frame.current) : CurrentAt model (runloopTop fiber).frame.current := by
  unfold runloopTop
  split
  · intro thunk impossible
    cases impossible
  · exact allowed

/-- Charging and forced yield retain the actual synchronous field permission. -/
theorem iteration_scopes (model : Model)
    (interrupt : ∀ fiber flag, model.finalizer (.interruptFiber fiber flag))
    (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : ScopesAt model m.state.scopes) (allowed : CurrentAt model fiber.frame.current) :
    ScopesAt model (iteration (evaluator := evaluatorFor root table)
      (interpOf root table) m fiber yielding).machine.state.scopes := by
  generalize actual : iteration (evaluator := evaluatorFor root table)
    (interpOf root table) m fiber yielding = result
  unfold iteration at actual
  dsimp only at actual
  split at actual
  · rename_i injectedResult injected
    cases actual
    unfold injectYield at injected
    split at injected
    · cases injected
      apply native_scopes model interrupt root table
        (m.emit [.yieldInjected (countOp (runloopTop fiber)).id (countOp (runloopTop fiber)).currentOpCount])
        {(countOp (runloopTop fiber)) with yieldOverride := none, frame := {(countOp (runloopTop fiber)).frame with current := .onSuccessConst (.yieldNowWith 0) (countOp (runloopTop fiber)).frame.current}} true held
      intro thunk impossible
      cases impossible
    · cases injected
  · cases actual
    exact native_scopes model interrupt root table m (countOp (runloopTop fiber)) yielding held
      (current_top model fiber allowed)

/-- Every command retains captured scopes from the permission at its actual looked-up synchronous head. -/
theorem command_scopes (model : Model)
    (interrupt : ∀ fiber flag, model.finalizer (.interruptFiber fiber flag))
    (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (command : SourceScope.SourceCommand) (rest : List SourceScope.SourceCommand)
    (held : ScopesAt model m.state.scopes)
    (allowed : ∀ id yielding fiber, m.fiber? id = some fiber →
      (command = .loop id yielding ∨ command = .deliver id yielding) →
      CurrentAt model fiber.frame.current) :
    ScopesAt model (driveStep (evaluator := evaluatorFor root table)
      (interpOf root table) m command rest).1.state.scopes := by
  apply StatePreservation.command_on (evaluator := evaluatorFor root table)
    (interpOf root table) (fun state : Stores => ScopesAt model state.scopes)
    (by
      have hooks := command_hooks model interrupt root [] table
      exact ⟨hooks.link, hooks.drop, hooks.due, hooks.wake⟩) m command rest held
  · intro id yielding fiber current found
    exact iteration_scopes model interrupt root table m fiber yielding held
      (allowed id yielding fiber found (.inl current))
  · intro id yielding fiber current found
    exact native_scopes model interrupt root table m fiber yielding held
      (allowed id yielding fiber found (.inr current))

end Effect4.Program.ScopeFields

import Effect4.Laws.Program.AnswerSlots.InitializedNativeParks
import Effect4.Laws.Machine.StatePreservation

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: native actions retain the allocation counts read by initialized answer classes.
Reach: actual administrative store hooks and the existing shared action preservation theorem.
Limit: source sync allocation and update use their separate actual-operation producers.
Consumer: initialized action frame transport and the coupled crew history driver.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

def Counts (refs deferred : Nat) (state : Stores) : Prop :=
  state.refs.length = refs ∧ state.deferreds.cells.length = deferred

/-- A scope snapshot changes scopes, never the counted allocation stores. -/
theorem snapshot_counts (scope : Nat) (exit : ExitV) (state next : Stores)
    (strategy : FinalizerStrategy) (order : List FinName)
    (found : scopeCloseSnapshot scope exit state = some (next, strategy, order)) :
    Counts state.refs.length state.deferreds.cells.length next := by
  unfold scopeCloseSnapshot at found
  cases actual : state.scopes.entryAt scope with
  | none => rw [actual] at found; cases found
  | some entry =>
    simp only [actual, Option.pure_def] at found
    cases found
    exact ⟨rfl, rfl⟩

/-- Native close retains allocation counts while returning its actual optional program. -/
theorem close_counts (spec : Spec) (view : List (FiberId × ExitV)) (scope : Nat) (exit : ExitV)
    (flag : Bool) (owner : FiberId) (state next : Stores) (program : Option NCode)
    (found : (interpAt spec.root view spec.table).closeScope scope exit flag owner state = some (next, program)) :
    Counts state.refs.length state.deferreds.cells.length next := by
  change (storesCloseScope scope exit flag state).map (fun result => (result.1, result.2.map embed)) =
    some (next, program) at found
  obtain ⟨⟨after, closing⟩, operation, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  unfold storesCloseScope at operation
  cases actual : scopeCloseSnapshot scope exit state with
  | none => rw [actual] at operation; cases operation
  | some result =>
    obtain ⟨after, strategy, order⟩ := result
    have counts := snapshot_counts scope exit state after strategy order actual
    simp only [actual, Option.pure_def] at operation
    cases operation
    exact counts

/-- Deferred batch waking keeps the number of deferred cells. -/
theorem wake_length (store : DeferredStore) (cell : DeferredKey) :
    (store.wakeBatch cell).cells.length = store.cells.length := by
  unfold DeferredStore.wakeBatch
  split
  · rfl
  · split <;> exact DeferredStore.setCell_cells_length _ _ _

/-- All native administrative store hooks keep both allocation counts. -/
theorem count_hooks (spec : Spec) (view : List (FiberId × ExitV)) (refs deferred : Nat) :
    StatePreservation.CommandHooks (interpAt spec.root view spec.table) (Counts refs deferred) where
  link := by
    intro mode scope owner state next key held ran
    dsimp only [interpAt, interpOf] at ran
    split at ran
    · cases ran
    · cases ran; exact held
  drop := by
    intro scope key state next held ran
    change (match state.scopes.entryAt scope with
      | none => none
      | some _ => some {state with scopes := state.scopes.removeFinalizer scope key}) = some next at ran
    split at ran
    · cases ran
    · cases ran; exact held
  due := fun _ held => held
  wake := by
    intro key phase state held
    change Counts refs deferred (state.wakeList key phase)
    unfold Stores.wakeList
    split
    · exact ⟨held.1, (wake_length _ _).trans held.2⟩
    · exact held

/-- Actual native fiber actions retain both allocation counts without a second action walk. -/
theorem action_counts (spec : Spec) (view : List (FiberId × ExitV)) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (action : NAction) :
    Counts machine.state.refs.length machine.state.deferreds.cells.length
      (evaluatePrim.withFiber (interpAt spec.root view spec.table) machine fiber yielding action).machine.state := by
  apply StatePreservation.withFiber_on (interpAt spec.root view spec.table)
    (Counts machine.state.refs.length machine.state.deferreds.cells.length)
    (count_hooks spec view _ _)
  · intro scope exit flag owner state next program held ran
    have counts := close_counts spec view scope exit flag owner state next program ran
    exact ⟨counts.1.trans held.1, counts.2.trans held.2⟩
  · exact ⟨rfl, rfl⟩
end Effect4.Program.AnswerSlots.Initialized

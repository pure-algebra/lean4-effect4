import Effect4.Laws.Program.FinalizerNativeIteration
import Effect4.Laws.Program.FinalizerTemplateCommands
import Effect4.Laws.Program.CodeClosure.ConfigurationNativeMetadata
import Effect4.Laws.Program.PrimitiveEffects

/-!
Concept: scope-lifetime-finalization R11.
Question: full source locations serve FinalizerRun.once_placed_outside_census.
Consumer: the common configuration command and decision transports.
The actual native producer combines existing frame, scope, pending and scheduler facts.
These local facts establish neither a history bound nor release custody.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Full source templates instantiate the existing configuration locations. -/
def configurationModel (q : List Nat) : CodeClosure.Configuration.Model where
  code := TemplateAt q
  scopes := ScopesAt q
  races := True

/-- Every existing administrative nested-command form carries no reply program. -/
theorem nested_commands (model : CodeClosure.Configuration.Model) (root : NativeEff) (table : RowTable)
    (result : SourceScope.SourceIteration) (held : Guard.ReturnCommands.Nested root table result) :
    CodeClosure.Configuration.CommandsAt model result.nested := by
  have simple (command : SourceScope.SourceCommand) (allowed : Guard.ReturnCommands.Simple command) :
      CodeClosure.Configuration.CommandAt model command := by
    cases command
    case resume => exact allowed.elim
    all_goals trivial
  cases held with
  | simple commands => exact fun command member => simple command (commands command member)
  | owned outcome front last commands ordinary isLocal =>
    rw [commands]
    apply CodeClosure.Configuration.commands_append model front [last] (fun command member => simple command (ordinary command member))
    intro command member
    rw [List.mem_singleton.mp member]
    cases last
    case resume => exact isLocal.elim
    all_goals trivial
  | registration outcome rid race lookup host park commands =>
    rw [commands]
    intro command member
    rcases List.mem_cons.mp member with same | later
    · rw [same]; trivial
    · rw [List.mem_singleton.mp later]; trivial

/-- Arbitrary primitive actions and parks introduce no resume command into their nested word. -/
theorem primitive_commands (model : CodeClosure.Configuration.Model) (root : NativeEff) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    CodeClosure.Configuration.CommandsAt model (evaluatePrim (interpAt root view table) machine fiber yielding).nested := by
  apply (Moves.evaluatePrim_effects (interpAt root view table) machine fiber yielding
    (CodeClosure.Configuration.CommandAt model) (fun _ => True) trivial ?_ ?_ (by intros; trivial) (by intros; trivial)).commands
  · intro thunk action selected unparked found
    exact ⟨nested_commands model root table _
      (Guard.ReturnCommands.withFiber_nested root table (interpAt root view table) machine fiber yielding action),
      fun _ _ => True.intro⟩
  · intro race parked
    unfold registerRace
    split
    · exact ⟨(fun _ member => nomatch member), fun _ _ => True.intro⟩
    · refine ⟨?_, fun _ _ => True.intro⟩
      intro command member
      rcases List.mem_cons.mp member with same | later
      · rw [same]; trivial
      · rw [List.mem_singleton.mp later]; trivial

/-- Actual action children retain the full source template at their supplied program locations. -/
theorem configuration_action (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (fiber : SourceScope.SourceFiber) (thunk : EffThunk) (action : NAction)
    (held : TemplateFrame q fiber.frame) (selected : fiber.frame.current = .withFiber thunk)
    (found : (interpAt root view table).withFiberOf thunk = some action) :
    SourceScope.ChildProgramsWith True True (TemplateAt q) action := by
  have owned := held.1.1
  rw [selected] at owned
  exact SourceScope.ActionProgramsWith.mono action
    (interp_action_at root q view table thunk action owned found)
    (fun _ => True.intro) (fun _ => True.intro) (by intro role code owned; cases role <;> trivial)

/-- Actual primitive evaluation retains the full configuration without a fragment premise. -/
theorem primitive_configuration (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (owned : CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine)
    (held : CodeClosure.Configuration.FiberAt (configurationModel q) fiber) :
    CodeClosure.Configuration.EvaluationAt (configurationModel q) root
      (evaluatePrim (interpAt root view table) machine fiber yielding) := by
  have children := configuration_action root q view table fiber
  have rows := CodeClosure.Configuration.primitive_rows_dispatcher (configurationModel q) root view table machine fiber yielding
    (fun _ => ⟨trivial, trivial, trivial⟩) owned.fibers held.dispatcher
    (fun thunk action selected _ found => children thunk action held.frame selected found)
  have races := CodeClosure.Configuration.primitive_races (configurationModel q) (interpAt root view table) machine fiber yielding owned.races
    (fun thunk action selected _ found => CodeClosure.Configuration.action_races (configurationModel q)
      (interpAt root view table) machine fiber yielding action owned.races
      (children thunk action held.frame selected found))
  have scopes := ScopeFields.primitive_scopes (scopeModel q) (fun _ _ => True.intro)
    root view table machine fiber yielding owned.scopes (scope_current q _ held.frame.1)
  have pending := (CodeClosure.Configuration.pending_iff (configurationModel q) _).mpr
    (Sched.evaluatePrim_pendingOk (interpAt root view table) machine fiber yielding
      ((CodeClosure.Configuration.pending_iff (configurationModel q) fiber).mp held.pending))
  exact ⟨⟨rows.1, races, scopes⟩,
    ⟨primitive_frame root q view table placed machine fiber yielding held.frame owned.scopes, pending, rows.2⟩,
    primitive_commands (configurationModel q) root view table machine fiber yielding⟩

/-- Native scoped exits reuse full frame closure and their exact unchanged metadata. -/
theorem exit_configuration (root : NativeEff) (q : List Nat)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (owned : CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine)
    (held : CodeClosure.Configuration.FiberAt (configurationModel q) fiber) :
    CodeClosure.Configuration.EvaluationAt (configurationModel q) root (exitScoped root machine fiber yielding exit) := by
  have frame := exit_scoped_frame root q placed machine fiber yielding exit held.frame owned.scopes
  have scopes := ScopeFields.exit_scopes (scopeModel q) (fun _ _ => True.intro)
    root machine fiber yielding exit owned.scopes (scope_current q _ held.frame.1)
  generalize actual : exitScoped root machine fiber yielding exit = result at frame scopes ⊢
  unfold exitScoped at actual
  dsimp only at actual
  split at actual
  · split at actual
    · cases actual
      exact ⟨⟨owned.fibers, owned.races, scopes⟩, ⟨frame, held.pending, held.dispatcher⟩,
        fun _ member => nomatch member⟩
    · rename_i state program closed
      cases program <;> cases actual
      all_goals exact ⟨⟨owned.fibers, owned.races, scopes⟩,
        ⟨frame, held.pending, held.dispatcher⟩, fun _ member => nomatch member⟩
  · cases actual
    exact primitive_configuration root q machine.completedExits [] placed machine fiber yielding owned held

/-- Full source templates instantiate the complete native evaluator's configuration result. -/
theorem native_configuration (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (owned : CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine)
    (held : CodeClosure.Configuration.FiberAt (configurationModel q) fiber) :
    CodeClosure.Configuration.EvaluationAt (configurationModel q) root (evaluateNative root machine fiber yielding table) := by
  unfold evaluateNative
  split
  · rename_i point selected
    split
    · have frame := enter_scoped_frame root q point machine fiber yielding selected held.frame
      exact ⟨⟨owned.fibers, owned.races,
          Machine.ScopeFields.scope_make_at (scopeModel q) machine.state.scopes machine.state.nextName
            .sequential owned.scopes trivial⟩,
        ⟨frame, held.pending, held.dispatcher⟩, fun _ member => nomatch member⟩
    · exact primitive_configuration root q machine.completedExits table placed machine fiber yielding owned held
  · exact exit_configuration root q placed machine fiber yielding _ owned held
  · exact exit_configuration root q placed machine fiber yielding _ owned held
  · exact primitive_configuration root q machine.completedExits table placed machine fiber yielding owned held

/-- The existing charged iteration retains the same full source configuration. -/
theorem iteration_configuration (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (owned : CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine)
    (held : CodeClosure.Configuration.FiberAt (configurationModel q) fiber) :
    CodeClosure.Configuration.EvaluationAt (configurationModel q) root
      (iteration (evaluator := evaluatorFor root table) (interpOf root table) machine fiber yielding) := by
  have charged : CodeClosure.Configuration.FiberAt (configurationModel q) (countOp (runloopTop fiber)) :=
    ⟨charged_frame q fiber held.frame, by unfold runloopTop; split <;> exact held.pending,
      by unfold runloopTop; split <;> exact held.dispatcher⟩
  unfold iteration
  dsimp only
  split
  · rename_i result found
    unfold injectYield at found
    split at found
    · cases found
      exact native_configuration root q table placed _ _ true
        ⟨owned.fibers, owned.races, owned.scopes⟩
        ⟨⟨yield_template q _ charged.frame.1, charged.frame.2⟩, charged.pending, charged.dispatcher⟩
    · cases found
  · exact native_configuration root q table placed machine _ yielding owned charged

end Effect4.Program.FinalizerSource

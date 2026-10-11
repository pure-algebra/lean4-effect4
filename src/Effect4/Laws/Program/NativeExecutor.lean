import Effect4.Laws.Machine.Eliminators
import Effect4.Laws.Program.NativeActions

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The concrete evaluator retains every actual source-bearing configuration field.
The source fragment is explicit; no source value-typing premise is introduced.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

set_option maxHeartbeats 1600000 in
/-- Actual primitive evaluation retains the configuration and its returned source programs. -/
theorem primitive_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    EvaluationAt root (evaluatePrim (interpAt root completed table) m fiber yielding) := by
  have fibers := owned.fibers
  have races := owned.races
  have scopes := owned.scopes
  have frame := held.frame
  have pending := held.pending
  have dispatcher := held.dispatcher
  have actionOwned (thunk : EffThunk) (action : NAction)
      (current : fiber.frame.current = .withFiber thunk)
      (found : (interpAt root completed table).withFiberOf thunk = some action) : ActionAt root action := by
    have source := held.frame.1
    rw [current] at source
    exact interp_action_at root fragment completed table thunk action source found
  have syncOwned (thunk : EffThunk) (state : Stores) (value : Val)
      (current : fiber.frame.current = .sync thunk)
      (found : (interpAt root completed table).syncState thunk m.state = some (state, value)) :
      ScopesAt root state.scopes := by
    have source := held.frame.1
    rw [current] at source
    exact sync_at root completed table thunk m.state state value owned.scopes source found
  have registered (name : EffName) :
      ScopesAt root ((interpAt root completed table).registerAsync name fiber.id m.nextToken m.state).1.scopes ∧
      ∀ code ∈ ((interpAt root completed table).registerAsync name fiber.id m.nextToken m.state).2, CodeAt root code :=
    register_at root completed table name fiber.id m.nextToken m.state owned.scopes
  fun_cases evaluatePrim (interpAt root completed table) m fiber yielding
  case case1 priority current token grown before parked =>
    have grownAt : ConfigurationAt root grown := ⟨owned.fibers, owned.races, owned.scopes⟩
    have beforeAt : FiberAt root before := by
      refine ⟨⟨trivial, held.frame.2⟩, held.pending, ?_⟩
      exact dispatcher_enqueue_at root fiber.dispatcher priority _ held.dispatcher ⟨trivial, .success _⟩
    exact ⟨configuration_emit root _ _ (configuration_arm root grown fiber.id grownAt),
      fiber_park_at root before _ beforeAt trivial, by intro command member; cases member⟩
  case case3 register signal cancel current token state grown before parked registeredEq =>
    have scopesAt := registered register
    rw [registeredEq] at scopesAt
    have cancelAt : NameAt root (cancel.getD .abort) := by
      have source := held.frame.1
      rw [current] at source
      cases found : cancel with
      | none => trivial
      | some name =>
        exact (source.2 name (by rw [found]; rfl)).1
    have beforeAt : FiberAt root before := by
      dsimp only [before]
      split
      · exact fiber_cancel_at root fiber _ held cancelAt
      · exact held
    exact ⟨configuration_emit root grown _ ⟨owned.fibers, owned.races, scopesAt.1⟩,
      fiber_park_at root before _ beforeAt trivial, by intro command member; cases member⟩
  case case9 target mode park targetFiber found noExit token grown cancel before parked noYield noAsync =>
    have beforeAt : FiberAt root before := fiber_cancel_at root fiber _ held trivial
    exact ⟨configuration_emit root grown _ ⟨owned.fibers, owned.races, owned.scopes⟩,
      fiber_park_at root before _ beforeAt trivial, by intro command member; cases member⟩
  case case6 targets current machine returned parked edits counted noYield noAsync =>
    have retained := countdown_edits_at root completed table m fiber targets .exitsValue false owned held trivial
    rw [counted] at retained
    exact ⟨retained.1, retained.2, by intro command member; cases member⟩
  all_goals aesop (add safe constructors [EvaluationAt, ConfigurationAt, FiberAt, TerminalReply]) (add safe apply [(step_frame_at root fragment), (finalizer_at root fragment), register_race_at, (with_fiber_at root), configuration_update, configuration_emit, configuration_arm, fiber_current_at, fiber_park_at, fiber_cancel_at, dispatcher_enqueue_at, exit_value_at]) (add safe forward [actionOwned, syncOwned, registered, (countdown_edits_at root completed table)]) (add norm simp [CommandsAt, CommandAt, List.mem_cons, FrameAt, CodeAt, ThunkAt, NameAt, ResumeAt, TaskAt, RunFiber.park])

/-- Scoped entry installs its actual zero-binder source child and a fresh empty scope. -/
theorem enter_scoped_at (root : NativeEff) (fragment : Fragment root) (p : Point)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (body : NativeEff)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) (point : At root p)
    (found : Node.at_ (.eff root) p.path = some (.eff (.scoped body))) :
    EvaluationAt root (enterScoped root p m fiber yielding) := by
  have child := node_child_at root p (.eff (.scoped body)) (.eff body) 0 found point rfl rfl
  have code := resolve_scoped root fragment (p.child 0) child.2
  exact ⟨⟨owned.fibers, owned.races, scope_make_at root m.state.scopes _ _ owned.scopes (Or.inl rfl)⟩,
    ⟨⟨⟨code, trivial⟩, held.frame.2⟩, held.pending, held.dispatcher⟩,
    by intro command member; cases member⟩

/-- Scoped cleanup preserves captured source programs after the actual continuation pop. -/
theorem exit_scoped_at (root : NativeEff) (fragment : Fragment root)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (exit : ExitV)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    EvaluationAt root (exitScoped root m fiber yielding exit) := by
  let pop := fiber.frame.getCont
    (match exit with | .success _ => .contA | .failure _ => .contE)
    (match exit with | .success _ => false | .failure _ => true)
    (match exit with | .success _ => none | .failure cause => some cause)
  have popped : StackAt root pop.fiber.stack := (getCont_at root fiber.frame _ _ _ held.frame.2).1
  have closing (scope : Nat) (next : Stores) (program : Option Program)
      (found : storesCloseScopeUnsafe scope (pop.deliveredExit exit) pop.fiber.interruptible m.state =
        some (next, program)) : ScopesAt root next.scopes ∧ ∀ code ∈ program, CodeAt root (embed code) :=
    close_unsafe_at root scope _ _ m.state next program owned.scopes found
  unfold exitScoped
  dsimp only
  split
  · rename_i body previous scope flag selected
    split
    · exact ⟨configuration_emit root m _ owned,
        ⟨⟨ofExit_at root _, popped⟩, held.pending, held.dispatcher⟩,
        by intro command member; cases member⟩
    · rename_i state program closed
      have retained := closing scope state program (by cases exit <;> exact closed)
      cases program with
      | none =>
        exact ⟨⟨owned.fibers, owned.races, retained.1⟩,
          ⟨⟨ofExit_at root _, popped⟩, held.pending, held.dispatcher⟩,
          by intro command member; cases member⟩
      | some code =>
        exact ⟨⟨owned.fibers, owned.races, retained.1⟩,
          ⟨⟨finalizer_code_at root _ [] _ _ (retained.2 code rfl), popped⟩, held.pending, held.dispatcher⟩,
          by intro command member; cases member⟩
  · exact primitive_at root fragment m.completedExits [] m fiber yielding owned held

/-- The actual native evaluator retains all source-bearing configuration fields. -/
theorem native_at (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    EvaluationAt root (evaluateNative root m fiber yielding table) := by
  unfold evaluateNative
  split
  · rename_i point current
    have sourcePoint : At root point := by have h := held.frame.1; rw [current] at h; exact h
    split
    · rename_i body found
      exact enter_scoped_at root fragment point m fiber yielding body owned held sourcePoint found
    · exact primitive_at root fragment m.completedExits table m fiber yielding owned held
  · exact exit_scoped_at root fragment m fiber yielding _ owned held
  · exact exit_scoped_at root fragment m fiber yielding _ owned held
  · exact primitive_at root fragment m.completedExits table m fiber yielding owned held

end Effect4.Program.SourceScope

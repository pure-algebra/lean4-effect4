import Effect4.Laws.Program.FinalizerActions
import Effect4.Laws.Program.NativeScopeFields
import Effect4.Laws.Machine.ScopeCloseFields

/-!
Concept: scope-lifetime-finalization R11.
Question: captured source annotations serve FinalizerRun.once_placed_outside_census.
Consumer: the full source configuration and actual scope-close evaluator.
The existing scope-field producer carries the annotation through every command.
The existing close-result producer returns its captured programs.
These facts establish no source-use count, complete history or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Scope entries retain the selected source's parameter-frame annotation. -/
def scopeModel (q : List Nat) : Machine.ScopeFields.Model where
  finalizer := CodeClosure.Slots.FinAt (PointAt q) (fun _ => True)
  strategy := fun _ => True
  sequential := trivial
  closeChild := fun _ => trivial
  detach := fun _ _ => trivial

abbrev ScopesAt (q : List Nat) := Machine.ScopeFields.ScopesAt (scopeModel q)

/-- A current synchronous source template supplies the captured finalizer permission. -/
theorem scope_current (q : List Nat) (code : NCode) (held : TemplateAt q code) :
    ScopeFields.CurrentAt (scopeModel q) code := by
  intro suspended selected
  rw [selected] at held
  have owned := held.1
  cases suspended
  case op operation =>
    cases operation <;> exact owned
  case store suspended =>
    cases suspended
    case op operation => cases operation <;> exact owned
    all_goals trivial
  all_goals trivial

/-- The full annotation supplies the three actual close-result constructors. -/
theorem closePrograms (q : List Nat) :
    Machine.ScopeFields.ClosePrograms (scopeModel q) (fun code => TemplateAt q (embed code)) where
  finalizer := finalizer_at q
  void := by
    intro body held
    change TemplateAt q (.onSuccessConst (embed body) (.success .unit))
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt])
  walk := by
    intro strategy order exit _ held
    exact ⟨held, trivial, trivial⟩

/-- Unsafe close exposes only finalizers carrying the source annotation. -/
theorem close_unsafe_at (q : List Nat) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Machine.Program) (owned : ScopesAt q state.scopes)
    (found : storesCloseScopeUnsafe scope exit flag state = some (next, program)) :
    ScopesAt q next.scopes ∧ ∀ code ∈ program, TemplateAt q (embed code) :=
  Machine.ScopeFields.close_unsafe_at (scopeModel q) _ (closePrograms q)
    scope exit flag state next program owned found

/-- Public close retains captured annotations through its void continuation. -/
theorem close_public_at (q : List Nat) (scope : Nat) (exit : ExitV) (flag : Bool)
    (state next : Stores) (program : Option Machine.Program) (owned : ScopesAt q state.scopes)
    (found : storesCloseScope scope exit flag state = some (next, program)) :
    ScopesAt q next.scopes ∧ ∀ code, program = some code → TemplateAt q (embed code) :=
  Machine.ScopeFields.close_public_at (scopeModel q) _ (closePrograms q)
    scope exit flag state next program owned found

/-- Native close embeds its captured program without introducing another source. -/
theorem close_native_at (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (scope : Nat) (exit : ExitV) (flag : Bool) (owner : FiberId)
    (state next : Stores) (program : Option NCode) (held : ScopesAt q state.scopes)
    (found : (interpAt root view table).closeScope scope exit flag owner state = some (next, program)) :
    ScopesAt q next.scopes ∧ ∀ code, program = some code → TemplateAt q code := by
  change (storesCloseScope scope exit flag state).map (fun r => (r.1, r.2.map embed)) =
    some (next, program) at found
  obtain ⟨⟨after, closing⟩, closed, equal⟩ := Option.map_eq_some_iff.mp found
  cases equal
  have result := close_public_at q scope exit flag state after closing held closed
  refine ⟨result.1, ?_⟩
  intro code selected
  obtain ⟨body, actual, same⟩ := Option.map_eq_some_iff.mp selected
  rw [← same]
  exact result.2 body actual

/-- Captured close programs retain custody before they expose active source reservations. -/
theorem closeWeightPrograms (root : NativeEff) (q : List Nat) :
    Machine.ScopeFields.ClosePrograms (scopeModel q) (fun code => current root q (embed code) = 0) where
  finalizer := fun fin exit _ => fin_program_zero root q fin exit
  void := by
    intro body held
    change current root q (embed body) + 0 = 0
    exact Nat.add_zero _ |>.trans held
  walk := fun _ _ _ _ _ => rfl

/-- The actual native close returns zero active source weight before custody opens. -/
theorem close_native_zero (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (scope : Nat) (exit : ExitV) (flag : Bool) (owner : FiberId)
    (state next : Stores) (program : NCode) (held : ScopesAt q state.scopes)
    (found : (interpAt root view table).closeScope scope exit flag owner state = some (next, some program)) :
    current root q program = 0 := by
  change (storesCloseScope scope exit flag state).map (fun r => (r.1, r.2.map embed)) =
    some (next, some program) at found
  obtain ⟨⟨after, closing⟩, closed, equal⟩ := Option.map_eq_some_iff.mp found
  cases closing with
  | none => cases equal
  | some body =>
    cases equal
    exact (Machine.ScopeFields.close_public_at (scopeModel q) _ (closeWeightPrograms root q)
      scope exit flag state after (some body) held closed).2 body rfl

/-- The common scope-field invariant reads permissions at the actual command's active head. -/
theorem command_scopes (root : NativeEff) (q : List Nat) (table : RowTable)
    (machine : NativeMachine) (command : SourceScope.SourceCommand) (rest : List SourceScope.SourceCommand)
    (held : ScopesAt q machine.state.scopes)
    (active : ∀ id yielding fiber, machine.fiber? id = some fiber →
      (command = .loop id yielding ∨ command = .deliver id yielding) → TemplateAt q fiber.frame.current) :
    ScopesAt q (driveStep (evaluator := evaluatorFor root table)
      (interpOf root table) machine command rest).1.state.scopes :=
  ScopeFields.command_scopes (scopeModel q) (fun _ _ => trivial) root table machine command rest held
    (fun id yielding fiber found selected => scope_current q _ (active id yielding fiber found selected))

end Effect4.Program.FinalizerSource

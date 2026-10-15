import Effect4.Laws.Program.FinalizerInterp
import Effect4.Laws.Program.NativeActionScope
import Effect4.Laws.Program.SourceOpportunityActions

/-!
Concept: scope-lifetime-finalization R11.
Question: actual action closure and debit serve `once_placed_outside_census`.
Consumer: the full source native evaluator and its command invariant.
Exact child provenance and action accounting reuse the existing common producers.
Stored releases retain their transferred custody before launching.
These local facts establish no history bound or progress.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Source actions retain parameter frames at their actual zero-binder child. -/
theorem actionChildClosure (root : NativeEff) (q : List Nat) :
    SourceScope.ChildClosure root (PointAt q) := fun _ _ _ _ _ held _ _ => held

/-- Exact action child provenance supplies the full source template annotation. -/
theorem actionProgram (root : NativeEff) (q : List Nat) (parent : Point)
    (role : SourceScope.ProgramRole) (code : NCode)
    (held : SourceScope.SourceProgramUnder root (PointAt q) parent role code) : TemplateAt q code := by
  cases role
  case forkBody | maskBody =>
    obtain ⟨effect, _, owned, equal⟩ := held
    rw [equal]
    exact resolve_at root q _ owned
  case entrantBody =>
    obtain ⟨index, effect, _, owned, equal⟩ := held
    rw [equal]
    exact resolve_at root q _ owned

/-- Stored action programs retain their captured source annotations. -/
theorem stored_action_at (q : List Nat) (name : ActionName)
    (held : CodeClosure.Slots.StoreActionAt (PointAt q) (fun _ => True) name) :
    SourceScope.ActionProgramsWith True True (fun _ => TemplateAt q) (embedAction (actionOf name)) := by
  cases name
  case fork | forkIn | forkScoped | setInterruptible => exact stored_at q _ held
  case closePar order exit =>
    refine ⟨?_, trivial⟩
    change ∀ body ∈ (order.map (fun fin => finProgram fin exit)).map embed, TemplateAt q body
    rw [List.map_map]
    intro body member
    obtain ⟨fin, present, equal⟩ := List.mem_map.mp member
    rw [← equal]
    exact finalizer_at q fin exit (held fin present)
  case raceAll race =>
    cases race
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [actionOf, embedAction,
      SourceScope.ActionProgramsWith, raceEntrants, progOf, embed, TemplateAt, OrdinaryNameAt,
      NameAt, ThunkAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt,
      CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.StoreThunkAt,
      CodeClosure.Qualified.StoreThunkAt, CodeClosure.Slots.StoreNameAt, CodeClosure.Qualified.StoreNameAt])
  all_goals trivial

/-- The full annotation instantiates the existing native action interpreter producer. -/
theorem actionClosure (root : NativeEff) (q : List Nat) :
    SourceScope.ActionClosure root True True (ThunkAt q) (TemplateAt q) where
  source := by
    intro point action owned found
    exact SourceScope.ActionProgramsWith.mono action
      (SourceScope.source_action_children_under root (PointAt q) (actionChildClosure root q) point action owned found)
      (fun _ => trivial) (fun _ => trivial) (actionProgram root q point)
  scopedFork := by
    intro point scope action owned found
    exact SourceScope.ActionProgramsWith.mono action
      (SourceScope.scoped_fork_children_under root (PointAt q) (actionChildClosure root q) point scope action owned found)
      (fun _ => trivial) (fun _ => trivial) (actionProgram root q point)
  stored := fun name held => stored_action_at q name held
  acquire := by
    intro point context held
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody,
      OrdinaryNameAt, NameAt, ThunkAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt,
      CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.StoreThunkAt,
      CodeClosure.Qualified.StoreThunkAt, CodeClosure.Qualified.StoreActionAt])
  release := by
    intro point previous held
    have closed := resolve_at root q point held
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, OrdinaryNameAt, NameAt,
      CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt])
  layer := fun point memo scope held => (resolve_layer root q point memo scope held).1
  provide := by
    intro update body flag held
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody,
      OrdinaryNameAt, NameAt, ThunkAt, CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt])
  restore := fun body flag held => (region_at root q body held).1

/-- Actual action results retain every program they can install or launch. -/
theorem interp_action_at (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (suspended : EffThunk) (next : NAction) (held : ThunkAt q suspended)
    (found : (interpAt root view table).withFiberOf suspended = some next) :
    SourceScope.ActionProgramsWith True True (fun _ => TemplateAt q) next :=
  SourceScope.interp_action_closed root view table True True (ThunkAt q) (TemplateAt q)
    (actionClosure root q) suspended next held found

abbrev actionWeight (root : NativeEff) (q : List Nat) :=
  SourceScope.Opportunities.actionWeight (current root q)

/-- Stored actions keep captured releases in custody, outside active source reservations. -/
theorem stored_action_zero (root : NativeEff) (q : List Nat) (name : ActionName) :
    actionWeight root q (embedAction (actionOf name)) = 0 := by
  cases name
  case fork | forkIn | forkScoped | setInterruptible => exact stored_program_zero root q _
  case closePar order exit =>
    change ((order.map (fun fin => finProgram fin exit)).map embed |>.map (current root q)).sum = 0
    simp only [List.map_map, Function.comp_def, fin_program_zero, List.map_const', List.sum_replicate_nat, Nat.mul_zero]
  case raceAll race =>
    cases race
    all_goals aesop (add norm simp [actionWeight, SourceScope.Opportunities.actionWeight, actionOf,
      embedAction, raceEntrants, List.map_map, Function.comp_def, stored_program_zero])
  all_goals rfl

/-- Actual native action accounting instantiates the common program-slot bound. -/
theorem actionBounds (root : NativeEff) (q : List Nat) :
    SourceScope.Opportunities.ActionBounds root (current root q) (thunk root q) (ThunkAt q) where
  source := fun point next _ found => SourceScope.Opportunities.source_action_le_with root q
    (current root q) (compile_le root q) (resolve_le root q) point next found
  scopedFork := fun point scope next _ found => SourceScope.Opportunities.fork_scoped_le_with root q
    (current root q) (resolve_le root q) point scope next found
  stored := fun name _ => Nat.le_of_eq (stored_action_zero root q name)
  acquire := by
    intro point context _
    simp only [current, cata_prim, thunk, name, successPush, SourceScope.Opportunities.thunk,
      SourceScope.Opportunities.name, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  release := by
    intro point previous _
    simpa only [current, cata_prim, name, exitPush, Nat.add_zero, thunk,
      SourceScope.Opportunities.thunk, SourceScope.Opportunities.name] using resolve_le root q point
  layer := fun point memo scope held => Nat.le_of_eq (resolve_layer root q point memo scope held).2
  provide := by
    intro update body flag _
    cases body
    all_goals simp only [current, cata_prim, thunk, name, successPush, SourceScope.Opportunities.thunk,
      SourceScope.Opportunities.name, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  restore := by
    intro body flag held
    cases body <;> exact (region_at root q _ held).2

/-- The action spends only the source reservation of its actual current suspension. -/
theorem interp_action_le (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (suspended : EffThunk) (next : NAction) (held : ThunkAt q suspended)
    (found : (interpAt root view table).withFiberOf suspended = some next) :
    actionWeight root q next ≤ thunk root q suspended :=
  SourceScope.Opportunities.interp_action_bound root view table (current root q) (thunk root q)
    (ThunkAt q) (actionBounds root q) suspended next held found

end Effect4.Program.FinalizerSource

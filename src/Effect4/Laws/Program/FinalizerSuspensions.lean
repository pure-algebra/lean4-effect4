import Effect4.Laws.Program.FinalizerCallbacks

/-!
Concept: scope-lifetime-finalization R11.
Question: full suspended-source debit for `once_placed_outside_census`.
Consumer: native frame evaluation at an annotated suspension.
Definition and parameter redirects retain the existing invocation stack and the static placement exclusion.
These local bounds establish no history invariant or progress.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- A definition call without programs pushes one empty parameter frame. -/
theorem empty_params (q : List Nat) (params : List (List ArgSite)) (held : ParamsClear q params) :
    ParamsClear q ([] :: params) := by
  intro sites member site selected
  cases member with
  | head => cases selected
  | tail _ member => exact held sites member site selected

/-- Returning from a program parameter retains every older frame. -/
theorem tail_params (q : List Nat) (sites : List ArgSite) (rest : List (List ArgSite))
    (held : ParamsClear q (sites :: rest)) : ParamsClear q rest :=
  fun next member site selected => held next (.tail _ member) site selected

/-- A selected child keeps its source annotation and spends at most its parent's reservation. -/
theorem selected_child (root : NativeEff) (q : List Nat) (point : Point) (index : Nat)
    (value : Option Val) (held : PointAt q point) :
    TemplateAt q (resolve root (point.childBind index value)) ∧
      current root q (resolve root (point.childBind index value)) ≤ SourceScope.Opportunities.below q point.path := by
  cases value with
  | none => exact ⟨resolve_at root q _ held, Nat.le_trans (resolve_le root q _)
      (SourceScope.Opportunities.child_le q point.path index)⟩
  | some value => exact ⟨resolve_at root q _ held, Nat.le_trans (resolve_le root q _)
      (SourceScope.Opportunities.child_le q point.path index)⟩

/-- Native suspensions retain annotations and spend their existing source reservation. -/
theorem suspended (root : NativeEff) (q : List Nat) (suspension : EffThunk)
    (placed : OncePlaced (.eff root) q = true) (held : ThunkAt q suspension) :
    TemplateAt q (suspendBodyAt root suspension) ∧
      current root q (suspendBodyAt root suspension) ≤ thunk root q suspension := by
  revert held
  fun_cases suspendBodyAt root suspension
  all_goals intro held
  case case2 point n fuel body found =>
    refine ⟨resolve_at root q _ held, ?_⟩
    change _ ≤ if point.fuel = 0 then 0 else _
    rw [if_neg (by omega)]
    exact Nat.le_trans (resolve_le root q (point.child 0)) (SourceScope.Opportunities.child_le q point.path 0)
  case case3 point n fuel scrutinee decide yes no found first bound result =>
    have child := selected_child root q point (bif first then 0 else 1) bound held
    refine ⟨child.1, ?_⟩
    change _ ≤ if point.fuel = 0 then 0 else _
    rw [if_neg (by omega)]
    exact child.2
  case case5 point n fuel body found =>
    refine ⟨⟨⟨held, .nil⟩, trivial, trivial⟩, ?_⟩
    change FinalizerGenerator.remaining q (point.path ++ [0]) [] ≤ if point.fuel = 0 then 0 else _
    rw [if_neg (by omega), FinalizerGenerator.remaining_start]
    exact SourceScope.Opportunities.child_le q point.path 0
  case case9 point n fuel key request found value path body evaluated =>
    refine ⟨resolve_at root q _ (empty_params q _ held), ?_⟩
    have zero := definition_full_zero root q
      {point.redirect path with env := point.env.take 0 ++ [value], params := [] :: point.params, call := point.path :: point.call}
      key path body rfl placed
    rw [zero]
    exact Nat.zero_le _
  case case11 point n fuel key request args found value path body evaluated =>
    refine ⟨resolve_at root q _ (invocation_params_clear root q point key request args found placed held), ?_⟩
    have zero := definition_full_zero root q
      {point.redirect path with env := point.env.take 0 ++ [value], params := argSitesAt (point.path ++ [0]) point.env args :: point.params, call := point.path :: point.call}
      key path body rfl placed
    rw [zero]
    exact Nat.zero_le _
  case case13 point n fuel index request found value top rest params evaluated site selected =>
    have clear : ParamsClear q (top :: rest) := by change ParamsClear q point.params at held; rw [params] at held; exact held
    refine ⟨resolve_at root q _ (tail_params q top rest clear), ?_⟩
    rw [parameter_resolve_zero root q point top rest site params held
      (List.mem_of_getElem? selected) value]
    exact Nat.zero_le _
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, OrdinaryNameAt, NameAt, ThunkAt,
    CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt,
    CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.StoreThunkAt, CodeClosure.Qualified.StoreThunkAt,
    CodeClosure.Slots.FinAt, CodeClosure.Qualified.FinAt, CodeClosure.Qualified.OpAt,
    CodeClosure.Qualified.EnvironmentWrites, current, cata_prim, thunk, name, successPush, exitPush,
    SourceScope.Opportunities.thunk, SourceScope.Opportunities.name, frontier, badShape,
    PointAt, Point.ofCapture]) (add safe forward [(compile_at root q), (stored_at q)]) (add safe apply [compile_le,
      SourceScope.Opportunities.child_le]) (add norm simp [stored_program_zero])

end Effect4.Program.FinalizerSource

import Effect4.Laws.Program.FinalizerLayers

/-!
Concept: scope-lifetime-finalization R11.
Question: value and cause callback debit for `once_placed_outside_census`.
Consumer: the full source frame invariant.
The existing callback functions retain annotations and spend their saved reservations together.
Release-start callbacks spend the reservation transferred from registered custody.
These local facts establish no history bound or progress.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Stored value callbacks reuse stored closure and expose no active release reservation. -/
theorem stored_value (root : NativeEff) (q : List Nat) (callback : Name) (value : Val)
    (held : CodeClosure.Slots.StoreNameAt (PointAt q) (fun _ => True) callback) :
    TemplateAt q (embed (Machine.contAOf callback value)) ∧
      current root q (embed (Machine.contAOf callback value)) = 0 := by
  refine ⟨embedded_code q _ (CodeClosure.Slots.store_contA_at _ _ callback value held), ?_⟩
  fun_cases Machine.contAOf callback value
  all_goals aesop (add norm simp [current, cata_prim, name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, embed, Prim.ofExit,
    stored_program_zero, fin_program_zero])

/-- Stored cause callbacks expose only an exit. -/
theorem stored_cause (root : NativeEff) (q : List Nat) (callback : Name) (cause : CauseV) :
    TemplateAt q (embed (Machine.contEOf callback cause)) ∧
      current root q (embed (Machine.contEOf callback cause)) = 0 := by
  refine ⟨embedded_code q _ (CodeClosure.Slots.store_contE_at _ _ callback cause), ?_⟩
  fun_cases Machine.contEOf callback cause
  all_goals aesop (add norm simp [current, cata_prim, name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, embed, Prim.ofExit])

/-- Delayed layer entry retains its caller's parameter frames. -/
theorem provide_with_at (root : NativeEff) (q : List Nat) (point : Point)
    (scope : Nat) (held : PointAt q point) : TemplateAt q (provideLayerWithK root point scope) := by
  unfold provideLayerWithK
  repeat' split
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, OrdinaryNameAt, NameAt, ThunkAt,
    CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.OpAt, CodeClosure.Qualified.OpAt,
    CodeClosure.Qualified.EnvironmentWrites, PointAt, Point.layerBuild,
    Point.child, badShape])

/-- Delayed layer-body entry retains the caller's body point. -/
theorem provide_body_at (root : NativeEff) (q : List Nat) (point : Point)
    (value : Val) (held : PointAt q point) : TemplateAt q (provideLayerBodyK root point value) := by
  unfold provideLayerBodyK
  repeat' split
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, OrdinaryNameAt, NameAt, ThunkAt,
    RegionAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, updateContextAt,
    PointAt, Point.child, badShape, Prim.ofExit]) (add safe cases [Exit])

/-- Full native value callbacks retain source annotations and debit the same saved reservation. -/
theorem value_callback (root : NativeEff) (q : List Nat) (callback : EffName) (value : Val)
    (placed : OncePlaced (.eff root) q = true) (held : NameAt q callback) :
    TemplateAt q (contAOf root callback value) ∧
      current root q (contAOf root callback value) ≤ savedSuccess q (name q) callback := by
  revert held
  fun_cases contAOf root callback value
  all_goals intro held
  case case1 point => exact ⟨resolve_at root q _ held, resolve_le root q (point.childWith 1 value)⟩
  case case2 point => exact ⟨resolve_at root q _ held, resolve_le root q (point.childWith 1 value)⟩
  case case12 point previous =>
    have closed := resolve_at root q (point.child 0) held
    refine ⟨by aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody]), ?_⟩
    simpa only [current, cata_prim, name, successPush, exitPush, savedSuccess,
      SourceScope.Opportunities.name, Nat.add_zero, Point.child] using resolve_le root q (point.child 0)
  case case18 point context scope =>
    have closed := resolve_at root q (point.child 0) held
    refine ⟨by aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody]), ?_⟩
    have body := resolve_le root q (point.child 0)
    have parts := SourceScope.Opportunities.acquisition_parts_le q point.path
    change current root q (resolve root (point.child 0)) ≤ SourceScope.Opportunities.below q (point.path ++ [0]) at body
    change current root q (resolve root (point.child 0)) +
      (SourceScope.Opportunities.here q point.path + SourceScope.Opportunities.below q (point.path ++ [1])) + 0 ≤
        SourceScope.Opportunities.below q point.path
    omega
  case case22 acquired fin exit different found =>
    have closed := finalizer_at q fin exit held
    exact ⟨by aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody]), by
      change current root q (embed (finProgram fin exit)) + 0 + 0 ≤ 0
      rw [fin_program_zero]; exact Nat.le_refl _⟩
  case case15 callback =>
    have h := stored_value root q callback value held
    exact ⟨h.1, Nat.le_of_eq h.2⟩
  case case27 point scope =>
    exact ⟨provide_with_at root q point scope held, provide_layer_with_le root q point (.scopeHandle scope)⟩
  case case29 point => exact ⟨provide_body_at root q point value held, provide_layer_body_le root q point value⟩
  case case34 point scope =>
    unfold buildWithScopeK
    split
    · exact ⟨by aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, OrdinaryNameAt, NameAt, ThunkAt, RegionAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.OpAt, CodeClosure.Qualified.OpAt, CodeClosure.Qualified.EnvironmentWrites, updateContextAt]), Nat.le_refl _⟩
    · exact ⟨⟨trivial, trivial, trivial⟩, Nat.le_refl _⟩
  case case38 point memo child =>
    have h := inner_layer root q point memo child held
    exact ⟨by aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody]), Nat.le_of_eq h.2⟩
  case case46 point memo scope =>
    have h := construction_at root q point scope held placed
    exact ⟨by aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody]), Nat.le_of_eq h.2⟩
  case case47 point scope id =>
    have h := resolve_layer root q point ⟨id⟩ scope held
    exact ⟨h.1, Nat.le_of_eq h.2⟩
  case case49 point memo scope mode =>
    unfold provideThenK
    split
    · exact ⟨by aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, OrdinaryNameAt, NameAt, ThunkAt, RegionAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.OpAt, CodeClosure.Qualified.OpAt, CodeClosure.Qualified.EnvironmentWrites, updateContextAt]), Nat.le_refl _⟩
    · exact ⟨⟨trivial, trivial, trivial⟩, Nat.le_refl _⟩
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, OrdinaryNameAt, NameAt, ThunkAt,
    RegionAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.StoreNameAt, CodeClosure.Qualified.StoreNameAt,
    CodeClosure.Slots.StoreThunkAt, CodeClosure.Qualified.StoreThunkAt, CodeClosure.Slots.OpAt, CodeClosure.Qualified.OpAt, CodeClosure.Slots.FinAt, CodeClosure.Qualified.FinAt,
    CodeClosure.Qualified.EnvironmentWrites,
    current, cata_prim, name, thunk, successPush, exitPush, savedSuccess, releaseWeight,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk,
    PointAt, Point.child, Point.childWith, Point.layerBuild, Point.ofCapture, Point.capture,
    badShape, updateThenK, addCurrentMemoMapK, combineWithK, updateContextAt, scopeAddAt,
    mergeContextsK, serviceLookupK, bindServiceK, Prim.ofExit]) (add safe apply [spine_point]) (add safe tactic (by omega))

/-- Full native cause callbacks retain source annotations and spend their saved handler reservation. -/
theorem cause_callback (root : NativeEff) (q : List Nat) (callback : EffName) (cause : CauseV)
    (held : NameAt q callback) :
    TemplateAt q (contEOf root callback cause) ∧
      current root q (contEOf root callback cause) ≤ name q callback := by
  revert held
  fun_cases contEOf root callback cause
  all_goals intro held
  case case1 point => exact ⟨resolve_at root q _ held, resolve_le root q (point.childWith 1 (.exitErr cause))⟩
  case case2 point test body handler found value answer =>
    exact ⟨resolve_at root q _ held, resolve_le root q (point.childWith 1 value)⟩
  case case5 point => exact ⟨resolve_at root q _ held, resolve_le root q (point.childWith 2 (.exitErr cause))⟩
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody, OrdinaryNameAt, NameAt,
    CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, current, cata_prim, name, SourceScope.Opportunities.name,
    Prim.ofExit]) (add safe forward [(stored_cause root q)])

end Effect4.Program.FinalizerSource

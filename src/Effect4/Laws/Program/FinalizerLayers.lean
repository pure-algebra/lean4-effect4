import Effect4.Laws.Program.FinalizerSyntax

/-!
Concept: scope-lifetime-finalization R11.
Question: the layer part of `once_placed_outside_census`.
Consumer: native region, callback and action debit.
The actual layer producers retain parameter frames and expose no selected source during construction.
OncePlaced excludes the effect child of every layer leaf.
These local facts establish no history invariant or progress.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Layer-spine descent retains the same stored argument frames. -/
theorem spine_point (q : List Nat) (point : Point) (index : Nat) (held : PointAt q point) :
    PointAt q (point.spineChild index) := by
  have walk (indices : List Nat) (p : Point) (h : PointAt q p) :
      PointAt q (indices.foldl (fun p _ => p.child 1) p) := by
    induction indices generalizing p with
    | nil => exact h
    | cons i indices ih => exact ih (p.child 1) h
  exact walk (List.range index) (point.child 0) held

/-- Layer compilation uses only its own delayed layer leaves, with zero selected source weight. -/
theorem compile_layer (root : NativeEff) (q : List Nat) (layer : LayerTerm NativeOp)
    (point : Point) (memo : MemoMapId) (scope : Nat) (held : PointAt q point) :
    CodeAt q (compileLayer layer point memo scope) ∧
      current root q (compileLayer layer point memo scope) = 0 := by
  revert held
  fun_induction compileLayer layer point memo scope
  all_goals intro held
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, NameAt, ThunkAt,
    CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.OpAt, CodeClosure.Qualified.OpAt, CodeClosure.Qualified.EnvironmentWrites,
    current, cata_prim, name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, badShape, PointAt, Point.child])

/-- A fuel-zero layer reference remains a zero-weight frontier. -/
theorem layer_zero (root : NativeEff) (q : List Nat) (layer : LayerTerm NativeOp)
    (point : Point) (memo : MemoMapId) (scope : Nat) (held : PointAt q point)
    (empty : point.fuel = 0) :
    CodeAt q (resolveLayerZero layer point memo scope) ∧
      current root q (resolveLayerZero layer point memo scope) = 0 := by
  revert held empty
  fun_induction resolveLayerZero layer point memo scope
  all_goals intro held empty
  case case1 =>
    constructor
    · exact held
    · simp only [frontier, current, cata_prim, thunk, empty, ↓reduceIte]
  case case2 inner point memo scope ih =>
    have child := ih held (by change point.fuel - 1 = 0; rw [empty])
    exact ⟨⟨child.1, trivial⟩, child.2⟩
  all_goals exact compile_layer root q _ _ _ _ held

/-- The actual layer resolver retains annotations through every fuel-bounded reference hop. -/
theorem layer_with (root : NativeEff) (q : List Nat) (fuel : Nat) (layer : LayerTerm NativeOp)
    (point : Point) (memo : MemoMapId) (scope : Nat) (held : PointAt q point)
    (budget : point.fuel = fuel) :
    CodeAt q (resolveLayerWith root fuel layer point memo scope) ∧
      current root q (resolveLayerWith root fuel layer point memo scope) = 0 := by
  induction fuel generalizing layer point with
  | zero => exact layer_zero root q layer point memo scope held budget
  | succ fuel ih =>
    cases layer
    case ref target =>
      unfold resolveLayerWith
      split
      · exact ⟨trivial, rfl⟩
      · rename_i next skipped found
        exact ih next (point.redirect target) held (by change point.fuel - 1 = fuel; omega)
      · exact ⟨trivial, rfl⟩
    case orDie inner =>
      have child := ih inner (point.child 0) held (by change point.fuel - 1 = fuel; omega)
      exact ⟨⟨child.1, trivial⟩, child.2⟩
    all_goals exact compile_layer root q _ point memo scope held

/-- A layer entry cannot create a selected source reservation. -/
theorem resolve_layer (root : NativeEff) (q : List Nat) (point : Point)
    (memo : MemoMapId) (scope : Nat) (held : PointAt q point) :
    CodeAt q (resolveLayer root point memo scope) ∧ current root q (resolveLayer root point memo scope) = 0 := by
  unfold resolveLayer
  split
  · exact layer_with root q point.fuel _ point memo scope held rfl
  · exact ⟨trivial, rfl⟩

/-- Inner layer dispatch uses the same zero-weight layer resolver. -/
theorem inner_layer (root : NativeEff) (q : List Nat) (point : Point)
    (memo : MemoMapId) (scope : Nat) (held : PointAt q point) :
    CodeAt q (innerLayerAt root point memo scope) ∧ current root q (innerLayerAt root point memo scope) = 0 := by
  fun_cases innerLayerAt root point memo scope
  case case3 | case4 =>
    have child := resolve_layer root q (point.child 1) memo scope held
    exact ⟨⟨child.1, held⟩, child.2⟩
  case case7 => exact compile_layer root q _ point memo scope held
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, NameAt, ThunkAt,
    CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt, CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.OpAt, CodeClosure.Qualified.OpAt, CodeClosure.Qualified.EnvironmentWrites,
    current, cata_prim, name, thunk, successPush, exitPush,
    SourceScope.Opportunities.name, SourceScope.Opportunities.thunk, badShape])

/-- Opening an actual layer leaf certifies its excluded effect-child region. -/
theorem construction_at (root : NativeEff) (q : List Nat) (point : Point)
    (scope : Nat) (held : PointAt q point) (placed : OncePlaced (.eff root) q = true) :
    CodeAt q (constructionAt root point scope) ∧ current root q (constructionAt root point scope) = 0 := by
  unfold constructionAt
  split
  · rename_i key body found
    have zero := FinalizerPlacement.forbidden_child_zero (.eff root)
      (.layer (.effect key body)) q point.path 0 found rfl placed
    exact ⟨⟨trivial, held, zero⟩, rfl⟩
  · rename_i body found
    have zero := FinalizerPlacement.forbidden_child_zero (.eff root)
      (.layer (.effectDiscard body)) q point.path 0 found rfl placed
    exact ⟨⟨trivial, held, zero⟩, rfl⟩
  · exact ⟨trivial, rfl⟩

/-- A region spends its program reservation; layer and construction regions carry zero. -/
def regionWeight (q : List Nat) : Region → Nat
  | .program point => SourceScope.Opportunities.below q point.path
  | _ => 0

/-- The actual region runner uses the existing compiler and layer proofs. -/
theorem region_at (root : NativeEff) (q : List Nat) (region : Region) (held : RegionAt q region) :
    CodeAt q (regionCode root region) ∧ current root q (regionCode root region) ≤ regionWeight q region := by
  cases region with
  | program point => exact ⟨resolve_at root q point held, resolve_le root q point⟩
  | build point memo scope =>
    have h := resolve_layer root q point memo scope held
    exact ⟨h.1, Nat.le_of_eq h.2⟩
  | buildAdding point memo scope =>
    have h := resolve_layer root q point memo scope held
    exact ⟨⟨h.1, trivial⟩, Nat.le_of_eq h.2⟩
  | construct point key =>
    have h := resolve_le root q point
    rw [held.2] at h
    exact ⟨⟨resolve_at root q point held.1, trivial⟩, h⟩

end Effect4.Program.FinalizerSource

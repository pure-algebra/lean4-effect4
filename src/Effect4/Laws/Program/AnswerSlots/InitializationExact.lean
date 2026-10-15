import Effect4.Laws.Program.AnswerSlots.InitializationProtocol

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: Atomic and Timeout initialization retain actual heap contents and callback points.
Reach: one Initialization certificate, actual native allocations and the actual completed-fiber view.
Consumer: AllocationAdapter's structured saved allocation edges and boundary entry certificate.
These local steps supply no whole-history invariant or fabricated empty saved suffix.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialization
open Effect4 Effect4.Machine Effect4.Program

/-- The actual allocated prefix contains the source certificate's initial values in order. -/
def values {root : NativeEff} (spec : AnswerSlots.Initialization root) (index : Nat) : List Val :=
  (List.range index).map spec.initial

theorem values_length {root : NativeEff} (spec : AnswerSlots.Initialization root) (index : Nat) :
    (values spec index).length = index := by
  simp only [values, List.length_map, List.length_range]

theorem values_next {root : NativeEff} (spec : AnswerSlots.Initialization root) (index : Nat) :
    values spec (index + 1) = values spec index ++ [spec.initial index] := by
  simp only [values, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The source prefix and its exact initial heap share one actual point. -/
structure ExactStage {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (index : Nat) (point : Point) (refs : List Val) : Prop where
  source : Stage spec index point refs
  contents : refs = values spec index

theorem exact_start {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (fuel : Nat) (tape : List Bool) : ExactStage spec 0 (rootPoint fuel tape) [] :=
  ⟨start spec fuel tape [] rfl, rfl⟩

/-- One actual allocation and callback retain the same point metadata and exact new heap. -/
theorem exact_actual {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (index : Nat) (point : Point) (small : index < spec.width)
    (state after : Stores) (answer : Val) (view : List (FiberId × ExitV)) (table : RowTable)
    (stage : ExactStage spec index point state.refs)
    (ran : syncOpStep (.refMake (spec.initial index)) state = some (after, answer)) :
    let next := ({point with completed := view} : Point).childWith 1 answer
    answer = .cell ⟨index⟩ ∧ after = {state with refs := values spec (index + 1)} ∧
      ExactStage spec (index + 1) next after.refs ∧
      (interpAt root view table).contA (.cont point) answer = resolve root next := by
  obtain ⟨value, written⟩ := actual spec index state after answer ran
  rw [stage.source.2.2.2.1] at value
  subst answer
  subst after
  have contents : state.refs ++ [spec.initial index] = values spec (index + 1) := by
    rw [stage.contents, values_next]
  refine ⟨rfl, ?_, ⟨advance spec index point state.refs small stage.source view (spec.initial index), contents⟩, rfl⟩
  exact congrArg (fun refs => {state with refs := refs}) contents

/-- Boundary entry exposes the actual source point and exact heap without resetting its metadata. -/
theorem exact_boundary {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (point : Point) (refs : List Val) (stage : ExactStage spec spec.width point refs) :
    point.path = List.replicate spec.width 1 ∧ point.env = spec.bindings.take spec.width ∧
      refs = values spec spec.width ∧ SourceScope.At root point :=
  ⟨stage.source.2.1, stage.source.2.2.1, stage.contents, stage.source.2.2.2.2⟩

/-- The actual allocation continuation keeps its existing saved suffix and point metadata. -/
theorem callback_frame {root : NativeEff} (point : Point) (view : List (FiberId × ExitV))
    (table : RowTable) (body : NCode) (answer : Val)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (noDeferred : fiber.deferredInterrupt = false) :
    ({fiber with stack := .onSuccess body (.cont point) :: fiber.stack}).resumeValue
        (interpAt root view table).toPrimInterp answer none =
      (.running {fiber with current := resolve root ({point with completed := view}.childWith 1 answer)},
        [.popped (.onSuccess body (.cont point))]) := by
  cases fiber with
  | mk current stack flag pending deferred =>
    change deferred = false at noDeferred
    subst deferred
    cases flag <;> rfl

/-- The final real allocation supplies the actual entry frame with its untouched older suffix. -/
theorem actual_boundary {root : NativeEff} (spec : AnswerSlots.Initialization root)
    (index : Nat) (point : Point) (small : index < spec.width) (last : index + 1 = spec.width)
    (state after : Stores) (answer : Val) (view : List (FiberId × ExitV)) (table : RowTable)
    (body : NCode) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (noDeferred : fiber.deferredInterrupt = false)
    (stage : ExactStage spec index point state.refs)
    (ran : syncOpStep (.refMake (spec.initial index)) state = some (after, answer)) :
    ∃ next : Point, next.path = List.replicate spec.width 1 ∧
      next.env = spec.bindings.take spec.width ∧ after.refs = values spec spec.width ∧
      SourceScope.At root next ∧
      ({fiber with stack := .onSuccess body (.cont point) :: fiber.stack}).resumeValue
          (interpAt root view table).toPrimInterp answer none =
        (.running {fiber with current := resolve root next}, [.popped (.onSuccess body (.cont point))]) := by
  obtain ⟨key, written, advanced, callback⟩ := exact_actual spec index point small state after answer view table stage ran
  rw [last] at advanced
  obtain ⟨path, env, contents, source⟩ := exact_boundary spec _ after.refs advanced
  exact ⟨_, path, env, contents, source, callback_frame point view table body answer fiber noDeferred⟩

/-- A partial initializer heap is the corresponding prefix of the complete declared initial heap. -/
theorem values_take {root : NativeEff} (spec : AnswerSlots.Initialization root) (index : Nat)
    (small : index ≤ spec.width) : values spec index = (values spec spec.width).take index := by
  simp only [values, ← List.map_take, List.take_range, Nat.min_eq_left small]

end Effect4.Program.AnswerSlots.Initialization

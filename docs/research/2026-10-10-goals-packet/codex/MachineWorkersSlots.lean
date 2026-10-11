import MachineAnswerFlow
import MachineWorkersWriters

/-!
Concept: store-typing R4, scope-lifetime-finalization R11.
Question: initialization slots serve the unchanged Workers.Assertions.logs_step.
Reach: actual native initialization binders; the world retains the actual owner and store.
Limit: this probe gives no initial-command exclusivity or whole-history closure.
Consumer: the source's saved root binders consume the post-allocation answer class.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace MachineWorkersSlots
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario

structure World where
  owner : FiberId
  state : Stores

inductive Kind
  | root | allocated (index : Nat)

def bindings : List Val := [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩, .cell ⟨3⟩, .promise ⟨0⟩]

/-- Every live answer and current code retains initialization ownership or the stable phase. -/
def Phase (world : World) : Prop :=
  world.owner = ⟨0⟩ ∨ (4 ≤ world.state.refs.length ∧ 1 ≤ world.state.deferreds.cells.length)

/-- The root reaches an initializer with the exact completed binding prefix.
Both transient store lengths belong to the current root position, not to copied saved bodies. -/
def RootStage (world : World) (index : Nat) (point : Point) : Prop :=
  index ≤ 4 ∧ world.owner = ⟨0⟩ ∧ point.path = List.replicate index 1 ∧
    point.env = bindings.take index ∧ world.state.refs.length = index ∧
    world.state.deferreds.cells.length = 0

/-- The successful allocation class describes the post-operation store.
The callback can therefore extend its lexical prefix without guessing the returned key. -/
def ValueAt (world : World) : Kind → Val → Prop
  | .root, _ => Phase world
  | .allocated index, value => Phase world ∧ value = .cell ⟨index⟩ ∧
      world.state.refs.length = index + 1 ∧ world.state.deferreds.cells.length = 0

inductive CodeAt (total : Nat) (world : World) : Kind → NCode → Prop
  | success (kind : Kind) (value : Val) (good : ValueAt world kind value) :
      CodeAt total world kind (.success value)
  | failure (kind : Kind) (cause : CauseV) (phase : Phase world) :
      CodeAt total world kind (.failure cause)
  | root (index : Nat) (point : Point) (stage : RootStage world index point) :
      CodeAt total world .root (resolve (Programs.workersProgram total) point)

def model (total : Nat) : AnswerFlow.Model (ν := EffName) (σ := EffThunk)
    (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) World Kind where
  future first last := first.owner = last.owner
  future_refl _ := rfl
  future_trans _ _ _ := Eq.trans
  value := ValueAt
  cause world _ _ := Phase world
  code := CodeAt total
  finalizer _ _ _ := none
  success := fun _ kind value good => .success kind value good
  failure := fun _ kind cause phase => .failure kind cause phase

/-- The initial-stage exclusivity consumer reads the condition from every current code. -/
theorem code_phase {total : Nat} {world : World} {kind : Kind} {code : NCode}
    (held : CodeAt total world kind code) : Phase world := by
  cases held with
  | success kind value good => cases kind with
    | root => exact good
    | allocated _ => exact good.1
  | failure _ _ phase => exact phase
  | root _ _ stage => exact Or.inl stage.2.1

/-- Appending the actual allocated key extends the concrete prefix through the fourth reference. -/
theorem prefix_append (index : Nat) (small : index < 4) :
    bindings.take index ++ [Val.cell ⟨index⟩] = bindings.take (index + 1) := by
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  rcases index with _ | index
  · kernel_rfl
  omega

/-- A saved initializer consumes the exact key and post-state that its body produces.
This is a real source contA callback at every total, view and compile fuel. -/
theorem initializer_callback (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (index : Nat) (point : Point) (small : index < 4)
    (stage : RootStage world index point) :
    ∀ nextWorld, (model total).future world nextWorld → ∀ value,
      (model total).value nextWorld (.allocated index) value →
      (model total).code nextWorld .root
        ((interpAt (Programs.workersProgram total) view table).contA (.cont point) value) := by
  intro nextWorld future value good
  obtain ⟨_, valueEq, refs, deferred⟩ := good
  subst value
  change CodeAt total nextWorld .root
    (resolve (Programs.workersProgram total) ({point with completed := view}.childWith 1 (.cell ⟨index⟩)))
  refine .root (index + 1) _ ?_
  obtain ⟨bound, owner, path, env, _, _⟩ := stage
  refine ⟨by omega, future ▸ owner, ?_, ?_, refs, deferred⟩
  · change point.path ++ [1] = List.replicate (index + 1) 1
    rw [path, List.replicate_succ']
  · change point.env ++ [Val.cell ⟨index⟩] = bindings.take (index + 1)
    rw [env]
    exact prefix_append index small

/-- The actual saved root binder now consumes the shared future-state contract. -/
theorem initializer_saved (total : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (world : World) (index : Nat) (point : Point) (body : NCode) (small : index < 4)
    (stage : RootStage world index point) :
    AnswerFlow.SavedAt (model total) (interpAt (Programs.workersProgram total) view table).toPrimInterp
      world (.allocated index) .root (.onSuccess body (.cont point)) := by
  exact AnswerFlow.saved_success (model total) _ world (.allocated index) .root body (.cont point)
    (initializer_callback total view table world index point small stage)
    (fun _ _ _ good => good)

/-- The actual native allocator produces the answer class consumed by its saved binder.
The current source stage supplies the length; this law does not manufacture a history witness. -/
theorem initializer_native (total : Nat) (table : RowTable) (machine : Api.Machine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (index : Nat) (point : Point) (initial : Val) (yielding : Bool)
    (stage : RootStage ⟨fiber.id, machine.state⟩ index point)
    (current : fiber.frame.current = .sync (.op (.refMake initial)))
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, machine.state⟩ (.allocated index) .root fiber.frame.stack) :
    evaluateNative (Programs.workersProgram total) machine fiber yielding table =
      ⟨{machine with state := {machine.state with refs := machine.state.refs ++ [initial]}},
        {fiber with frame := {fiber.frame with current := .success (.cell ⟨index⟩)}},
        yielding, .answered, [.drainDue]⟩ ∧
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, {machine.state with refs := machine.state.refs ++ [initial]}⟩ .root
      {fiber.frame with current := .success (.cell ⟨index⟩)} := by
  obtain ⟨_, owner, _, _, length, deferred⟩ := stage
  constructor
  · apply ControlSteps.native_sync_op _ table machine fiber yielding _ _ _ current
    change some (_, Val.cell ⟨machine.state.refs.length⟩) = _
    rw [length]
  · have future : (model total).future ⟨fiber.id, machine.state⟩
        ⟨fiber.id, {machine.state with refs := machine.state.refs ++ [initial]}⟩ := rfl
    apply AnswerFlow.sync_answer (model total) _ future
      (.allocated index) .root fiber.frame (.cell ⟨index⟩) _ stack
    change Phase _ ∧ Val.cell ⟨index⟩ = Val.cell ⟨index⟩ ∧
      (machine.state.refs ++ [initial]).length = index + 1 ∧
      machine.state.deferreds.cells.length = 0
    exact ⟨Or.inl owner, rfl, by rw [List.length_append, List.length_singleton, length], deferred⟩

end MachineWorkersSlots

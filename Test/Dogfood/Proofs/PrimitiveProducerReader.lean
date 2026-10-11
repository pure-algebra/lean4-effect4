import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Program.ControlSteps
import Effect4.Laws.Machine.RefKernel
import Effect4.Laws.Program.NativeHeapExecution

/-!
Readers of the actual primitive producer at allocated reference cells.
Concept: store-typing R4; consumer: executed store labels and Timeout's numeric producer.
These readers retain the operation even when its reference heap stays equal.
They establish one evaluator call, not source permission or a reached-history invariant.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.PrimitiveProducerReader
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Moves

/-- A real allocated read has an executed-operation witness although its stores stay equal. -/
theorem read (root : NativeEff) (table : RowTable) (machine : NativeMachine) (fiber : NFiber)
    (yielding : Bool) (cell : RefKey) (allocated : cell.index < machine.state.refs.length)
    (current : fiber.frame.current = .sync (.op (.refGet cell))) :
    let value := machine.state.refs[cell.index]'allocated
    let result : NIteration := ⟨machine, {fiber with frame := {fiber.frame with current := .success value}},
      yielding, .answered, [.drainDue], []⟩
    evaluateNative root machine fiber yielding table = result ∧
      PrimitiveProducer (interpAt root machine.completedExits table) machine fiber yielding result := by
  dsimp only
  have executed := syncOpStep_refGet_allocated allocated
  refine ⟨ControlSteps.native_sync_op root table machine fiber yielding (.refGet cell)
    machine.state _ current executed, ?_⟩
  exact .sync (.op (.refGet cell)) machine.state _ current
    (by rw [current]; rfl) executed

/-- Writing back the value already stored still has an executed write witness. -/
theorem write_same (root : NativeEff) (table : RowTable) (machine : NativeMachine) (fiber : NFiber)
    (yielding : Bool) (cell : RefKey) (allocated : cell.index < machine.state.refs.length)
    (current : fiber.frame.current = .sync (.op (.refSet cell (machine.state.refs[cell.index]'allocated)))) :
    let result : NIteration := ⟨machine, {fiber with frame := {fiber.frame with current := .success (.cell cell)}},
      yielding, .answered, [.drainDue], []⟩
    evaluateNative root machine fiber yielding table = result ∧
      PrimitiveProducer (interpAt root machine.completedExits table) machine fiber yielding result := by
  dsimp only
  have executed := syncOpStep_refSet_allocated allocated (machine.state.refs[cell.index]'allocated)
  rw [List.set_getElem_self] at executed
  refine ⟨ControlSteps.native_sync_op root table machine fiber yielding
    (.refSet cell (machine.state.refs[cell.index]'allocated)) machine.state (.cell cell) current executed, ?_⟩
  exact .sync (.op (.refSet cell (machine.state.refs[cell.index]'allocated))) machine.state (.cell cell)
    current (by rw [current]; rfl) executed

/-- The allocated-read producer supplies the composable reference certificate. -/
example (root : NativeEff) (table : RowTable) (machine : NativeMachine) (fiber : NFiber)
    (yielding : Bool) (cell : RefKey) (allocated : cell.index < machine.state.refs.length)
    (current : fiber.frame.current = .sync (.op (.refGet cell))) :
    RefWords.Certified machine fiber.frame machine
      {fiber.frame with current := .success (machine.state.refs[cell.index]'allocated)} :=
  (StoreExecution.primitive_refEffects root machine.completedExits table machine fiber yielding _
    (read root table machine fiber yielding cell allocated current).2).2

namespace ReferenceWords
open RefWords

def before : Stores := {Stores.empty with refs := [.nat 10, .nat 20]}
def middle : Stores := {before with refs := [.nat 11, .nat 20]}
def after : Stores := {middle with refs := middle.refs ++ [.unit]}
def write : Annotation :=
  (⟨.answer (.sync (.op (.refSet ⟨0⟩ (.nat 11)))) (.success (.cell ⟨0⟩)), []⟩,
    some (.refSet ⟨0⟩ (.nat 11), .cell ⟨0⟩))
def allocate : Annotation :=
  (⟨.answer (.sync (.op (.refMake .unit))) (.success (.cell ⟨2⟩)), []⟩,
    some (.refMake .unit, .cell ⟨2⟩))

theorem actual : Contracts.Path Edge before.refs after.refs [write, allocate] :=
  .cons (.sync _ _ _ before middle (.inl rfl) rfl)
    (.cons (.sync _ _ _ middle after (.inl rfl) rfl) (.nil after.refs))

example : run [write, allocate] before.refs = after.refs := path_fold actual
example : refPeek after.refs ⟨1⟩ = refPeek before.refs ⟨1⟩ :=
  path_refPeek_other actual ⟨1⟩ (by decide)
example : refPeek after.refs ⟨7⟩ = refPeek before.refs ⟨7⟩ :=
  path_refPeek_other actual ⟨7⟩ (by decide)

/-- A successful read still records its actual operation and answer. -/
example : Edge before.refs before.refs
    (⟨.answer (.sync (.op (.refGet ⟨0⟩))) (.success (.nat 10)), []⟩,
      some (.refGet ⟨0⟩, .nat 10)) :=
  .sync _ _ _ before before (.inl rfl) rfl

end ReferenceWords


end Test.Dogfood.Proofs.PrimitiveProducerReader

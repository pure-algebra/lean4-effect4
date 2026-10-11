import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Program.ControlSteps
import Effect4.Laws.Machine.RefKernel

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

end Test.Dogfood.Proofs.PrimitiveProducerReader

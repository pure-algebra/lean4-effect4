import Effect4.Laws.Machine.ControlSteps
import Effect4.Laws.Machine.AnswerFlow
import Effect4.Api

/-!
# Compiled store steps on an arbitrary fiber

Each law serves `fiber-local-positions` and the packet's `heap_sites_keep`.
The concept is `reactive-scheduling`, serving R4, R10 and R11 through the scenario invariants.
The rules retain the actual completed-exit view, row table, other fibers and command residue.
They establish one step under its explicit premises, not write provenance or invariant closure.
The `Sync` ordering transcribes rc.112 `internal/effect.ts:931-935`.
-/

set_option autoImplicit false

namespace Effect4.Program.ControlSteps

open Effect4 Effect4.Machine Effect4.Program

/-- A recognized compiled store operation answers on any fiber and retains its stack.
A step of `heap_sites_keep`; the worker store rule consumes it. -/
@[semantics "store-typing" (requirement := R4)]
theorem native_sync_op (root : NativeEff) (table : RowTable) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (op : SyncOp) (state : Stores) (value : Val)
    (current : f.frame.current = .sync (.op op))
    (answer : syncOpStep op m.state = some (state, value)) :
    evaluateNative root m f yielding table =
      ⟨{ m with state }, { f with frame := { f.frame with current := .success value } },
        yielding, .answered, [.drainDue], []⟩ := by
  have park : (interpAt root m.completedExits table).parkOf (.sync (.op op)) = none := rfl
  have sync : (interpAt root m.completedExits table).syncState (.op op) m.state =
      syncOpStep op m.state := rfl
  simp only [evaluateNative, current, evaluatePrim, park, sync, answer]

/-- An actual compiled store answer consumes the post-state contract on the unchanged saved stack.
Consumer: Timeout's count read, cleanup writer and selected-exit writer.
The world reads the actual stores; source selection and post-state admissibility remain premises. -/
@[semantics "store-typing" (requirement := R4)]
theorem native_sync_answer {World Kind : Type} (root : NativeEff) (table : RowTable)
    (m : Api.Machine) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (op : SyncOp) (state : Stores) (value : Val)
    (world : Stores → World)
    (model : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val)
      (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) World Kind)
    (interp : PrimInterp EffName EffThunk Val Err Defect FiberId Ann) (input output : Kind)
    (current : f.frame.current = .sync (.op op))
    (answer : syncOpStep op m.state = some (state, value))
    (future : model.future (world m.state) (world state))
    (answered : model.value (world state) input value)
    (stack : AnswerFlow.StackAt model interp (world m.state) input output f.frame.stack) :
    evaluateNative root m f yielding table =
      ⟨{m with state}, {f with frame := {f.frame with current := .success value}},
        yielding, .answered, [.drainDue], []⟩ ∧
      AnswerFlow.FrameAt model interp (world state) output
        {f.frame with current := .success value} :=
  ⟨native_sync_op root table m f yielding op state value current answer,
    AnswerFlow.sync_answer model interp future input output f.frame value answered stack⟩

/-- One compiled store command on an arbitrary fiber commits before its owed resumes.
A step of `heap_sites_keep` and `fiber-local-positions`; the worker probe consumes it. -/
@[semantics "store-typing" (requirement := R4)]
theorem loop_sync_op (root : NativeEff) (table : RowTable) (m : Api.Machine)
    (id : FiberId) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (op : SyncOp) (state : Stores) (value : Val) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .sync (.op op))
    (interrupt : f.frame.deferredInterrupt = false)
    (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield)
    (answer : syncOpStep op m.state = some (state, value)) :
    driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) rest =
      (({ m with state }).update
        { countOp f with frame := { f.frame with current := .success value } },
       [.drainDue, .deliver id yielding] ++ rest) := by
  rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table) _ m id f yielding rest found]
  rw [Machine.ControlSteps.iteration_below_budget (evaluator := evaluatorFor root table) _ m f yielding interrupt override budget]
  change settle id rest (evaluateNative root m (countOp f) yielding table) = _
  rw [native_sync_op root table m (countOp f) yielding op state value current answer]
  rfl

end Effect4.Program.ControlSteps

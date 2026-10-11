import Effect4.Laws.Program.ControlSteps

/-!
# Compiled store rows on the native machine

Concept: translation-simulation R10, the command half of proposed `queue-expansion-agrees`.
Consumers: Atomic heap-site transfers and QueueWorkers `Assertions.jobs_step`.
Reach: an arbitrary fiber at a compiled store row, with the row's captured values and cell relation.
The command retains its stack, operation count and unfinished command suffix.
The model premises remain explicit; this module establishes no cell writer census or wrapper delivery.
It establishes no whole-run closure, progress or outside-host behavior.
Decisions rows 233, 255 and 275 bound the queue consumer fragment.
-/

set_option autoImplicit false

namespace Effect4.Program.StoreExecution

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-- The compiled Ref.modify row uses exactly its captured environment. -/
theorem compile_modify (term request : Term) (p : Point) (fuel : Nat) (q : RefKey)
    (hf : p.fuel = fuel + 1) (hq : evalTerm p.env request = some (.cell q)) :
    compileEff (.perform (.refModifyWith term) request) p =
      .sync (.op (.refModify q term p.env)) := by
  unfold compileEff
  rw [hf]
  change (match evalTerm p.env request with
    | some value => match NativeOp.syncOpOf (.refModifyWith term) p.env value with
      | some operation => Prim.sync (EffThunk.op operation)
      | none => badShape
    | none => badShape) = _
  rw [hq]
  cases q
  rfl

/-- One actual compiled Ref.modify command commits its store answer before pending resumes. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem modify_loop (root : NativeEff) (table : RowTable) (m : Api.Machine)
    (id : FiberId) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (term request : Term) (p : Point) (fuel : Nat) (q : RefKey)
    (state : Stores) (value : Val) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : m.fiber? id = some f)
    (current : f.frame.current = compileEff (.perform (.refModifyWith term) request) p)
    (hf : p.fuel = fuel + 1) (hq : evalTerm p.env request = some (.cell q))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield)
    (answer : syncOpStep (.refModify q term p.env) m.state = some (state, value)) :
    driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) rest =
      (({ m with state }).update
        { countOp f with frame := { f.frame with current := .success value } },
       [.drainDue, .deliver id yielding] ++ rest) := by
  rw [compile_modify term request p fuel q hf hq] at current
  exact ControlSteps.loop_sync_op root table m id f (.refModify q term p.env)
    state value yielding rest found current interrupt override budget answer

end Effect4.Program.StoreExecution

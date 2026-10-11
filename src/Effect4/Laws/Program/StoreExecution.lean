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
The shared reference transfer serves HeapSites.heap_sites_keep and Timeout.cleanup_keeps.
It retains the actual synchronous source; its predicate instances still owe source permission and order.
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

/-- One native evaluation either retains references or executes its actual synchronous source.
This is a relation over existing code and stores, not stored program syntax. -/
inductive RefTransfer (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (input : NCode) (before : Stores) : Stores → Prop
  | same (after : Stores) (refs : after.refs = before.refs) : RefTransfer interp input before after
  | sync (thunk : EffThunk) (after : Stores) (value : Val)
      (current : input = .sync thunk) (unparked : interp.parkOf input = none)
      (answer : interp.syncState thunk before = some (after, value)) :
      RefTransfer interp input before after

/-- A reference predicate uses its actual source permission only at the executed synchronous row. -/
theorem RefTransfer.preserves
    {interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores}
    {input : NCode} {before after : Stores}
    (step : RefTransfer interp input before after) (P : RefHeap → Prop)
    (held : P before.refs)
    (sync : ∀ thunk next value, input = .sync thunk → interp.parkOf input = none →
      interp.syncState thunk before = some (next, value) → P next.refs) : P after.refs := by
  cases step with
  | same next refs => exact refs ▸ held
  | sync thunk next value current unparked answer => exact sync thunk _ value current unparked answer



end Effect4.Program.StoreExecution

import Effect4.Laws.Program.ReleaseWriter.Primitive

/-!
Concept: scope-lifetime-finalization R11.
Question: source evaluation and scoped entry transfer the shared direct-release reservation.
Reach: direct source-owned programs with sequential scopes, no races, and the actual sync-write bound.
Consumers: both crews' writer histories through the existing native command lift.
These laws establish no captured value or execution progress.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- A trace extension cannot remove recorded release starts. -/
theorem issued_mono (target : Target) (before after : NativeMachine) (extended : RunMachine.Extends before after) :
    issued target before ≤ issued target after := by
  obtain ⟨events, appended⟩ := extended.exists
  simp only [issued, appended, List.countP_append]
  omega

/-- A preserved heap and lowered frame suffice when the trace only extends. -/
theorem rows_debit (target : Target) (m : NativeMachine) (fiber : SourceFiber) (next : SourceIteration)
    (rows : next.machine.fibers = m.fibers) (refs : next.machine.state.refs = m.state.refs)
    (extended : RunMachine.Extends m next.machine)
    (bounded : frame target next.fiber.frame ≤ frame target fiber.frame) :
    (ledger target).IterDebit m fiber next := by
  apply same_rows_debit target m fiber next rows
  have trace := issued_mono target m next.machine extended
  have store := state_le_of_refs target m.state next.machine.state refs
  omega

/-- Emission extends the existing trace. -/
theorem emit_extends (m : NativeMachine) (events : List Moves.REvent) : RunMachine.Extends m (m.emit events) := by
  unfold RunMachine.Extends
  rw [RunMachine.emit_trace]
  exact List.prefix_append _ _

/-- Replacing the popped frame's current code by free code retains no more than its old reservation. -/
theorem pop_frame_le (target : Target) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) (code : NCode)
    (zero : current target code = 0) :
    frame target {(fiber.getCont demand skip cause).fiber with current := code} ≤ frame target fiber := by
  have bounded := FrameWeights.getCont_le (model target) fiber demand skip cause
  simp only [frame, FrameWeights.frame, model, zero, Nat.zero_add] at bounded ⊢
  omega

/-- Scoped entry moves its source reservation to its body without a new one. -/
theorem enter_scoped_debit {target : Target} {root : NativeEff} (source : Source target root) (point : Point) (body : NativeEff)
    (_found : Node.at_ (.eff root) point.path = some (.eff (.scoped body)))
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (selected : fiber.frame.current = .withFiber (.act point)) (_owned : At root point) :
    (ledger target).IterDebit m fiber (enterScoped root point m fiber yielding) := by
  have child := source.resolve_bound (point.child 0)
  have inherited : leaf target (point.path ++ [0]) = 0 := leaf_child_zero target _ 0 (by decide)
  have bounded : current target (Prim.onExit (resolve root (point.child 0))
      (.scopedExit fiber.context m.state.nextName) false) ≤ current target fiber.frame.current := by
    rw [selected]
    change current target (resolve root (point.child 0)) + 0 + 0 ≤ leaf target point.path
    change current target (resolve root (point.child 0)) ≤ leaf target (point.path ++ [0]) at child
    omega
  refine rows_debit target m fiber _ rfl rfl (RunMachine.Extends.refl m) ?_
  change current target (Prim.onExit (resolve root (point.child 0))
      (.scopedExit fiber.context m.state.nextName) false) + (fiber.frame.stack.map (saved target)).sum ≤
    current target fiber.frame.current + (fiber.frame.stack.map (saved target)).sum
  omega

/-- Scoped exit installs only zero-weight close code after the actual pop, or falls back to the
primitive evaluator. -/
theorem exit_scoped_debit {target : Target} {root : NativeEff} (source : Source target root)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (exit : ExitV) (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (noSync : ∀ suspended, fiber.frame.current ≠ .sync suspended) :
    (ledger target).IterDebit m fiber (exitScoped root m fiber yielding exit) := by
  have primitive := primitive_debit source [] sequential raceFree m fiber yielding owned held
    (SyncBound.of_not_sync target root [] m fiber.frame.current noSync)
  cases exit with
  | success value =>
    unfold exitScoped
    dsimp only
    split
    · rename_i _ _ scope _ _
      split
      · refine rows_debit target m fiber _ rfl rfl (emit_extends m _) ?_
        exact pop_frame_le target fiber.frame .contA false none _ (exit_zero target _)
      · rename_i state program closed
        have refs := close_unsafe_refs scope _ _ m.state state program closed
        cases program with
        | none =>
          refine rows_debit target m fiber _ rfl refs (emit_extends m _) ?_
          exact pop_frame_le target fiber.frame .contA false none _ (exit_zero target _)
        | some code =>
          have zero := close_unsafe_zero target scope _ _ m.state state code closed
          refine rows_debit target m fiber _ rfl refs ?_ ?_
          · unfold RunMachine.Extends
            simp only [RunMachine.emit_trace, List.append_assoc]
            exact List.prefix_append _ _
          · refine pop_frame_le target fiber.frame .contA false none _ ?_
            dsimp only
            rw [restoring_count]
            exact zero
    · exact primitive
  | failure cause =>
    unfold exitScoped
    dsimp only
    split
    · rename_i _ _ scope _ _
      split
      · refine rows_debit target m fiber _ rfl rfl (emit_extends m _) ?_
        exact pop_frame_le target fiber.frame .contE true (some cause) _ (exit_zero target _)
      · rename_i state program closed
        have refs := close_unsafe_refs scope _ _ m.state state program closed
        cases program with
        | none =>
          refine rows_debit target m fiber _ rfl refs (emit_extends m _) ?_
          exact pop_frame_le target fiber.frame .contE true (some cause) _ (exit_zero target _)
        | some code =>
          have zero := close_unsafe_zero target scope _ _ m.state state code closed
          refine rows_debit target m fiber _ rfl refs ?_ ?_
          · unfold RunMachine.Extends
            simp only [RunMachine.emit_trace, List.append_assoc]
            exact List.prefix_append _ _
          · refine pop_frame_le target fiber.frame .contE true (some cause) _ ?_
            dsimp only
            rw [restoring_count]
            exact zero
    · exact primitive

/-! ## The native evaluator and the iteration -/

/-- **The writer's native evaluator debit**: one evaluation of an owned fiber spends only its
acting frame's reservation or a recorded start. Consumer: `WriterHistory.evaluation`. -/
theorem native_debit {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) (syncBound : SyncBound target root table m fiber.frame.current) :
    (ledger target).IterDebit m fiber (evaluateNative root m fiber yielding table) := by
  have primitive := primitive_debit source table sequential raceFree m fiber yielding owned held syncBound
  unfold evaluateNative
  split
  · rename_i point selected
    split
    · rename_i body found
      have thunkOwned := held.frame.1
      rw [selected] at thunkOwned
      exact enter_scoped_debit source point body found m fiber yielding selected thunkOwned
    · exact primitive
  · rename_i value selected
    exact exit_scoped_debit source sequential raceFree m fiber yielding _ owned held
      (by intro suspended wrong; rw [selected] at wrong; cases wrong)
  · rename_i cause selected
    exact exit_scoped_debit source sequential raceFree m fiber yielding _ owned held
      (by intro suspended wrong; rw [selected] at wrong; cases wrong)
  · exact primitive


end Effect4.Program.ReleaseWriter

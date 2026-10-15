import Test.Dogfood.Proofs.WorkersConnections
import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Machine.AnswerFlowPop

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual post-operation answers serve the unchanged Workers.Assertions.logs_step.
Reach: native sync operations at the ordinary answer class, with the actual ordered stack.
Limit: allocation classes, capture ownership and whole-history closure remain separate.
Consumer: the acquisition note answers before its saved literal-return callback.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.WorkersNativeSlots
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Scenario WorkersSlots WorkersConnections

/-- The ordinary answer phase remains available after the existing store-growth law.
Consumer: native sync replies read the post-operation store. -/
theorem phase_future (first last : WorkersSlots.World) (future : Future first last)
    (phase : Phase first) : Phase last := by
  rcases phase with root | ready
  · exact Or.inl (future.1.symm.trans root)
  · exact Or.inr ⟨Nat.le_trans ready.1 future.2.1, Nat.le_trans ready.2 future.2.2⟩

/-- Every actual native sync reply preserves an ordinary saved answer class.
The missing-store branch returns the actual fallback value in the unchanged store. -/
theorem sync_root_native (total : Nat) (table : RowTable) (machine : Api.Machine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (operation : SyncOp) (yielding : Bool) (output : Kind)
    (phase : Phase ⟨fiber.id, machine.state⟩)
    (current : fiber.frame.current = .sync (.op operation))
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, machine.state⟩ .root output fiber.frame.stack) :
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, (evaluateNative (Programs.workersProgram total) machine fiber yielding table).machine.state⟩
      output (evaluateNative (Programs.workersProgram total) machine fiber yielding table).fiber.frame := by
  cases reply : syncOpStep operation machine.state with
  | none =>
    simp only [evaluateNative, current, evaluatePrim, interpAt, interpOf, reply]
    exact AnswerFlow.sync_answer (model total) _ ((model total).future_refl _)
      .root output fiber.frame _ phase stack
  | some pair =>
    rcases pair with ⟨state, value⟩
    rw [ControlSteps.native_sync_op _ table machine fiber yielding operation state value current reply]
    have growth := syncOpStep_le operation machine.state state value reply
    have future : Future ⟨fiber.id, machine.state⟩ ⟨fiber.id, state⟩ :=
      ⟨rfl, growth.1, growth.2.1⟩
    exact AnswerFlow.sync_answer (model total) _ future .root output fiber.frame value
      (phase_future _ _ future phase) stack

/-- The actual first acquisition note appends its literal and answers unit.
Consumer: the native reply retains the ordinary input of its literal-return callback. -/
theorem acquisition_one_note_step (state : Stores) (old : List Val)
    (read : refPeek state.refs ⟨0⟩ = some (.list old)) :
    syncOpStep (.refUpdate ⟨0⟩ (WorkersWriters.appendOne 5 (.lit (.nat 1))) bindings) state =
      some ({state with refs := refPoke state.refs ⟨0⟩ (.list (old ++ [.nat 1]))}, .unit) := by
  change (refStep (.refUpdate ⟨0⟩ (WorkersWriters.appendOne 5 (.lit (.nat 1))) bindings)
    state.refs).map _ = _
  rw [refStep_update state.refs ⟨0⟩ _ _ _ _ read (show evalTerm (bindings ++ [.list old])
    (WorkersWriters.appendOne 5 (.lit (.nat 1))) = some (.list (old ++ [.nat 1])) from by kernel_rfl)]
  rfl

/-- The second acquisition note retains its previous answer but appends only its own literal. -/
theorem acquisition_two_note_step (state : Stores) (previous : Val) (old : List Val)
    (read : refPeek state.refs ⟨0⟩ = some (.list old)) :
    syncOpStep (.refUpdate ⟨0⟩ (WorkersWriters.appendOne 6 (.lit (.nat 2)))
      (bindings ++ [previous])) state =
      some ({state with refs := refPoke state.refs ⟨0⟩ (.list (old ++ [.nat 2]))}, .unit) := by
  change (refStep (.refUpdate ⟨0⟩ (WorkersWriters.appendOne 6 (.lit (.nat 2)))
    (bindings ++ [previous])) state.refs).map _ = _
  rw [refStep_update state.refs ⟨0⟩ _ _ _ _ read (show evalTerm ((bindings ++ [previous]) ++ [.list old])
    (WorkersWriters.appendOne 6 (.lit (.nat 2))) = some (.list (old ++ [.nat 2])) from by kernel_rfl)]
  rfl

/-- The saved acquisition note binder accepts an ordinary answer and returns its literal class.
Its saved original body stays inert; every actual completed-exit view remains permitted. -/
theorem acquisition_note_saved (total : Nat) (world : WorkersSlots.World)
    (identity : Nat) (point : Point) (body : NCode)
    (view : List (FiberId × ExitV)) (table : RowTable)
    (identitySite : identity = 1 ∨ identity = 2)
    (path : point.path = Programs.crewAcquire identity ++ [0]) :
    AnswerFlow.SavedAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp world
      .root (.connection identity) (.onSuccess body (.cont point)) := by
  apply AnswerFlow.saved_success (model total) _ world .root (.connection identity) body (.cont point)
  · intro nextWorld future answer good
    exact acquisition_return_callback total world identity point identitySite path nextWorld future view table answer good
  · intro nextWorld future reason good
    exact good

/-- An actual note response selects its real saved literal-return callback.
The response's post-state phase supplies the callback input; the ordered older suffix remains typed. -/
theorem acquisition_note_delivery (total : Nat) (world : WorkersSlots.World)
    (identity : Nat) (point : Point) (body : NCode)
    (view : List (FiberId × ExitV)) (table : RowTable)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (answer : Val) (output : Kind)
    (identitySite : identity = 1 ∨ identity = 2)
    (path : point.path = Programs.crewAcquire identity ++ [0])
    (phase : Phase world) (noInterrupt : fiber.deferredInterrupt = false)
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp world
      (.connection identity) output fiber.stack) :
    ({fiber with stack := .onSuccess body (.cont point) :: fiber.stack}).resumeValue
      (interpAt (Programs.workersProgram total) view table).toPrimInterp answer none =
        (.running {fiber with current := (interpAt (Programs.workersProgram total) view table).contA (.cont point) answer},
          [.popped (.onSuccess body (.cont point))]) ∧
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) view table).toPrimInterp world output
      {fiber with current := (interpAt (Programs.workersProgram total) view table).contA (.cont point) answer} := by
  apply AnswerFlow.resume_success (model total) _ world .root (.connection identity) output
    fiber body (.cont point) answer none noInterrupt phase
  · intro exit member
    cases member
  · exact acquisition_note_saved total world identity point body view table identitySite path
  · exact stack

/-- The actual first note source resolves to the opened-reference operation with its five bindings. -/
theorem acquisition_one_note_code (total : Nat) (point : Point) (fuel : Nat)
    (path : point.path = Programs.crewAcquire 1)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) (amount : point.fuel = fuel + 3) :
    resolve (Programs.workersProgram total) ((point.child 0).child 0) =
      .sync (.op (.refUpdate ⟨0⟩ (WorkersWriters.appendOne 5 (.lit (.nat 1))) bindings)) := by
  have env := acquisition_one_env total point path lexical leading
  have found : Node.at_ (.eff (Programs.workersProgram total)) ((point.child 0).child 0).path =
      some (.eff (.perform (.refUpdateWith (WorkersWriters.appendOne 5 (.lit (.nat 1)))) (.var 0))) := by
    change Node.at_ _ ((point.path ++ [0]) ++ [0]) = _
    rw [path]
    kernel_rfl
  rw [Agreement.resolve_of_at found]
  rw [Agreement.compileEff_perform_sync _ _ (k := fuel) (by
    change (point.fuel - 1) - 1 = fuel + 1
    rw [amount]
    omega) rfl]
  change (match evalTerm point.env (.var 0) with
    | some value => match NativeOp.syncOpOf (.refUpdateWith (WorkersWriters.appendOne 5 (.lit (.nat 1))))
        point.env value with
      | some operation => Prim.sync (EffThunk.op operation)
      | none => badShape
    | none => badShape) = _
  rw [env]
  kernel_rfl

/-- The actual second note source retains the previous answer beyond the five bindings. -/
theorem acquisition_two_note_code (total : Nat) (point : Point) (fuel : Nat)
    (path : point.path = Programs.crewAcquire 2)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) (amount : point.fuel = fuel + 3) :
    ∃ previous, point.env = bindings ++ [previous] ∧
      resolve (Programs.workersProgram total) ((point.child 0).child 0) =
      .sync (.op (.refUpdate ⟨0⟩ (WorkersWriters.appendOne 6 (.lit (.nat 2)))
        (bindings ++ [previous]))) := by
  obtain ⟨previous, env⟩ := acquisition_two_env total point path lexical leading
  refine ⟨previous, env, ?_⟩
  have found : Node.at_ (.eff (Programs.workersProgram total)) ((point.child 0).child 0).path =
      some (.eff (.perform (.refUpdateWith (WorkersWriters.appendOne 6 (.lit (.nat 2)))) (.var 0))) := by
    change Node.at_ _ ((point.path ++ [0]) ++ [0]) = _
    rw [path]
    kernel_rfl
  rw [Agreement.resolve_of_at found]
  rw [Agreement.compileEff_perform_sync _ _ (k := fuel) (by
    change (point.fuel - 1) - 1 = fuel + 1
    rw [amount]
    omega) rfl]
  change (match evalTerm point.env (.var 0) with
    | some value => match NativeOp.syncOpOf (.refUpdateWith (WorkersWriters.appendOne 6 (.lit (.nat 2))))
        point.env value with
      | some operation => Prim.sync (EffThunk.op operation)
      | none => badShape
    | none => badShape) = _
  rw [env]
  kernel_rfl

/-- The actual first acquisition note supplies the post-state frame consumed by delivery.
The source, operation equation and saved literal class meet at a native evaluator boundary. -/
theorem acquisition_one_note_native (total : Nat) (table : RowTable) (machine : Api.Machine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (point : Point)
    (fuel : Nat) (yielding : Bool) (old : List Val) (output : Kind)
    (path : point.path = Programs.crewAcquire 1)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) (amount : point.fuel = fuel + 3)
    (phase : Phase ⟨fiber.id, machine.state⟩)
    (current : fiber.frame.current = resolve (Programs.workersProgram total) ((point.child 0).child 0))
    (read : refPeek machine.state.refs ⟨0⟩ = some (.list old))
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, machine.state⟩ .root output fiber.frame.stack) :
    evaluateNative (Programs.workersProgram total) machine fiber yielding table =
      ⟨{machine with state := {machine.state with refs := refPoke machine.state.refs ⟨0⟩ (.list (old ++ [.nat 1]))}},
        {fiber with frame := {fiber.frame with current := .success .unit}}, yielding, .answered, [.drainDue], []⟩ ∧
    AnswerFlow.FrameAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, (evaluateNative (Programs.workersProgram total) machine fiber yielding table).machine.state⟩
      output (evaluateNative (Programs.workersProgram total) machine fiber yielding table).fiber.frame := by
  have code := current.trans (acquisition_one_note_code total point fuel path lexical leading amount)
  exact ⟨ControlSteps.native_sync_op _ table machine fiber yielding _ _ _ code
    (acquisition_one_note_step machine.state old read),
    sync_root_native total table machine fiber _ yielding output phase code stack⟩

/-- The second actual note uses the same native answer rule and keeps its previous answer inert. -/
theorem acquisition_two_note_native (total : Nat) (table : RowTable) (machine : Api.Machine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (point : Point)
    (fuel : Nat) (yielding : Bool) (old : List Val) (output : Kind)
    (path : point.path = Programs.crewAcquire 2)
    (lexical : SourceScope.At (Programs.workersProgram total) point)
    (leading : point.env.take 5 = bindings) (amount : point.fuel = fuel + 3)
    (phase : Phase ⟨fiber.id, machine.state⟩)
    (current : fiber.frame.current = resolve (Programs.workersProgram total) ((point.child 0).child 0))
    (read : refPeek machine.state.refs ⟨0⟩ = some (.list old))
    (stack : AnswerFlow.StackAt (model total)
      (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
      ⟨fiber.id, machine.state⟩ .root output fiber.frame.stack) :
    ∃ previous, evaluateNative (Programs.workersProgram total) machine fiber yielding table =
      ⟨{machine with state := {machine.state with refs := refPoke machine.state.refs ⟨0⟩ (.list (old ++ [.nat 2]))}},
        {fiber with frame := {fiber.frame with current := .success .unit}}, yielding, .answered, [.drainDue], []⟩ ∧
      point.env = bindings ++ [previous] ∧
      AnswerFlow.FrameAt (model total)
        (interpAt (Programs.workersProgram total) machine.completedExits table).toPrimInterp
        ⟨fiber.id, (evaluateNative (Programs.workersProgram total) machine fiber yielding table).machine.state⟩
        output (evaluateNative (Programs.workersProgram total) machine fiber yielding table).fiber.frame := by
  obtain ⟨previous, environment, code⟩ := acquisition_two_note_code total point fuel path lexical leading amount
  have currentCode := current.trans code
  exact ⟨previous, ControlSteps.native_sync_op _ table machine fiber yielding _ _ _ currentCode
    (acquisition_two_note_step machine.state previous old read), environment,
    sync_root_native total table machine fiber _ yielding output phase currentCode stack⟩

end Test.Dogfood.Proofs.WorkersNativeSlots

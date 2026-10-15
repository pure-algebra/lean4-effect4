import Effect4.Laws.Program.CodeClosure.NativeFunding

/-!
Concept: scope-lifetime-finalization R11.
Question: actual scope closure serves the finalizer source accounting claim.
Consumer: FinalizerSource.exit_scoped_debit; the direct source budget uses the same connector.
The existing pop bound accounts for discarded frames and the installed close program.
This local transfer establishes no source closure, history bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Funding
open Effect4 Effect4.Machine Effect4.Program

/-- The existing exit selector is the actual native continuation pop. -/
theorem pop_for_eq (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (exit : ExitV) :
    WriterWeights.popFor fiber exit = fiber.getCont
      (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause) := by
  cases exit <;> rfl

/-- Replacing the actual popped head by free code cannot increase its frame reservation. -/
theorem pop_zero_bound (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (exit : ExitV) (code : NCode)
    (zero : model.current code = 0) :
    FrameWeights.frame model {(WriterWeights.popFor fiber exit).fiber with current := code} ≤
      FrameWeights.frame model fiber := by
  have bounded := FrameWeights.getCont_le model fiber
    (match exit with | .success _ => .contA | .failure _ => .contE)
    (match exit with | .success _ => false | .failure _ => true)
    (match exit with | .success _ => none | .failure cause => some cause)
  simp only [FrameWeights.frame, pop_for_eq, zero, Nat.zero_add] at bounded ⊢
  omega

/-- Actual scoped dispatch shares one frame and trace transfer for every source ledger. -/
theorem exit_scoped_bound (model : FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann)
    (successWeight : EffName → Nat) (exitWeight : EffName → Bool → Nat)
    (produce : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat)
    (root : NativeEff) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) (exit : ExitV)
    (free : ∀ result, model.current (.ofExit result) = 0)
    (closing : ∀ scope flag state code,
      storesCloseScopeUnsafe scope ((WriterWeights.popFor fiber.frame exit).deliveredExit exit)
        flag machine.state = some (state, some code) →
      model.current (finalizerCode (interpAt root machine.completedExits [])
        ((WriterWeights.popFor fiber.frame exit).deliveredExit exit) (embed code)) = 0)
    (delegated : let next := evaluatePrim (interpAt root machine.completedExits []) machine fiber yielding
      recorded (Events.event successWeight exitWeight) next.machine + FrameWeights.frame model next.fiber.frame + recorded produce machine ≤
        recorded (Events.event successWeight exitWeight) machine + FrameWeights.frame model fiber.frame + recorded produce next.machine) :
    let next := exitScoped root machine fiber yielding exit
    recorded (Events.event successWeight exitWeight) next.machine + FrameWeights.frame model next.fiber.frame + recorded produce machine ≤
      recorded (Events.event successWeight exitWeight) machine + FrameWeights.frame model fiber.frame + recorded produce next.machine := by
  have consumed : ((WriterWeights.popFor fiber.frame exit).events.map (Events.event successWeight exitWeight)).sum = 0 := by
    cases exit <;> exact Events.getCont_events_zero successWeight exitWeight fiber.frame _ _ _
  have terminal := pop_zero_bound model fiber.frame exit _ (free ((WriterWeights.popFor fiber.frame exit).deliveredExit exit))
  have closingBound (scope : Nat) (flag : Bool) (state : Stores) (code : Program)
      (closed : storesCloseScopeUnsafe scope ((WriterWeights.popFor fiber.frame exit).deliveredExit exit)
        flag machine.state = some (state, some code)) :=
    pop_zero_bound model fiber.frame exit _ (closing scope flag state code closed)
  cases exit
  all_goals
    simp only [WriterWeights.popFor] at terminal consumed closingBound
    unfold exitScoped
    dsimp only
    split
    · split
      · simp only [recorded, RunMachine.emit_trace, List.map_append, List.sum_append,
          List.map_map, Function.comp_def, runWeight, consumed, Nat.add_zero]
        omega
      · rename_i state program closed
        cases program with
        | none =>
          simp only [recorded, RunMachine.emit_trace, List.map_append, List.sum_append,
            List.map_map, Function.comp_def, runWeight, consumed, Nat.add_zero]
          omega
        | some code =>
          have bounded := closingBound _ _ state code closed
          simp only [recorded, RunMachine.emit_trace, List.map_append, List.sum_append,
            List.map_map, Function.comp_def, runWeight, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, consumed, Nat.add_zero]
          omega
    · exact delegated

/-- Scope dispatch retains the ambient rows, races and nested commands whenever delegation does. -/
theorem exit_scoped_fields (root : NativeEff) (machine : NativeMachine)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) (exit : ExitV)
    (delegated : let next := evaluatePrim (interpAt root machine.completedExits []) machine fiber yielding
      next.machine.fibers = machine.fibers ∧ next.machine.races = machine.races ∧ next.nested = []) :
    let next := exitScoped root machine fiber yielding exit
    next.machine.fibers = machine.fibers ∧ next.machine.races = machine.races ∧ next.nested = [] := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · rename_i state program _
      cases program <;> exact ⟨rfl, rfl, rfl⟩
  · exact delegated

end Effect4.Program.CodeClosure.Funding

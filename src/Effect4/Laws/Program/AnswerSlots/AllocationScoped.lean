import Effect4.Laws.Program.AnswerSlots.AllocationNative

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: pending initialization cannot enter or close a source scope before its actual boundary.
Reach: actual native scoped dispatch and the retained ordered saved suffix.
Consumer: Atomic's pending-prefix iteration producer.
The numeric application owns execution after actual source entry.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Actual scoped-exit selection requires the stable entry flag, even across a fused callback pop. -/
theorem pending_scoped_impossible (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (input output : Kind spec.stable.Kind)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (exit : ExitV)
    (pending : world.entered = false) (good : AnswerFlow.ExitAt (model spec view) world input exit)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) input output frame.stack)
    (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool) :
    (frame.getCont (match exit with | .success _ => .contA | .failure _ => .contE)
      (match exit with | .success _ => false | .failure _ => true)
      (match exit with | .success _ => none | .failure cause => some cause)).answer ≠
      .frame (.onExit body (.scopedExit previous scope) flag) := by
  intro chosen
  cases exit with
  | success value =>
    obtain ⟨incoming, middle, value, edge, suffix⟩ := AnswerFlow.External.getCont_value_selected
      (model spec view) (interpAt spec.root view spec.table).toPrimInterp (Edge spec fragment)
      (family spec fragment view) (fun world kind => mask_edge spec fragment world kind true)
      world input output frame value _ good saved chosen
    exact (pending_not_ready spec world pending (scoped_edge_ready spec fragment world incoming middle body previous scope flag edge)).elim
  | failure cause =>
    obtain ⟨incoming, middle, delivered, carried, cause, edge, suffix⟩ := AnswerFlow.External.getCont_cause_selected
      (model spec view) (interpAt spec.root view spec.table).toPrimInterp (Edge spec fragment)
      (family spec fragment view) (fun world kind => mask_edge spec fragment world kind true)
      world input output frame cause _ good (by
        intro interrupt member kind old allowed
        exact phase_future spec world world ((model spec view).future_refl world) good) saved chosen
    exact (pending_not_ready spec world pending (scoped_edge_ready spec fragment world incoming middle body previous scope flag edge)).elim

/-- A pending terminal native operation dispatches the actual primitive or exposes source entry first. -/
theorem pending_exit_eq_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind) (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    :
    exitScoped spec.root machine fiber yielding exit =
      evaluatePrim (interpAt spec.root machine.completedExits spec.table) machine fiber yielding ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
      Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases current_exit_or_entry spec fragment machine.completedExits _ input exit (current ▸ owned) with good | entry
  swap
  · obtain ⟨point, kind, code, stage⟩ := entry
    exact .inr ⟨point, kind, current.trans code, stage⟩
  apply Or.inl
  have excluded := pending_scoped_impossible spec fragment machine.completedExits ⟨fiber.id, machine.state, false⟩
    input output fiber.frame exit rfl good saved
  cases exit <;> unfold exitScoped <;> dsimp only
  all_goals
    split
    · rename_i body previous scope flag chosen
      exact (excluded body previous scope flag chosen).elim
    · simp only [evaluatePrim, current]
      rfl

/-- Actual native evaluation before entry supplies installed-row flow or the real application handoff. -/
theorem pending_native_iterflows_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (input output : Kind spec.stable.Kind)
    (owned : CodeAt spec ⟨fiber.id, machine.state, false⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment ⟨fiber.id, machine.state, false⟩) input output fiber.frame.stack)
    (held : FramesAt spec fragment false machine) :
    AnswerFlow.IterFlows (fun world _ => FrameAt spec fragment world) (fun state id => ⟨id, state, false⟩)
      (evaluateNative spec.root machine fiber yielding spec.table) ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.frame.current = resolve spec.root point ∧
      Entry spec ⟨fiber.id, machine.state, false⟩ point := by
  rcases pending_ordinary_or_entry spec machine.completedExits ⟨fiber.id, machine.state, false⟩ input fiber.frame.current owned rfl with ordinary | entry
  swap
  · exact .inr entry
  unfold evaluateNative
  split
  · rename_i point current
    exact (ordinary.2.1 (.act point) current).elim
  · rename_i value current
    rcases pending_exit_eq_or_entry spec fragment machine fiber yielding input output (.success value) current owned saved with same | entry
    · rw [same]
      exact pending_primitive_iterflows_or_entry spec fragment machine.completedExits machine fiber yielding input output owned saved held
    · exact .inr entry
  · rename_i cause current
    rcases pending_exit_eq_or_entry spec fragment machine fiber yielding input output (.failure cause) current owned saved with same | entry
    · rw [same]
      exact pending_primitive_iterflows_or_entry spec fragment machine.completedExits machine fiber yielding input output owned saved held
    · exact .inr entry
  · exact pending_primitive_iterflows_or_entry spec fragment machine.completedExits machine fiber yielding input output owned saved held

end Effect4.Program.AnswerSlots.AllocationAdapter

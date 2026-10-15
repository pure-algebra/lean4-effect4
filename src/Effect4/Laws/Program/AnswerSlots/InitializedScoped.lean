import Effect4.Laws.Program.AnswerSlots.InitializedNative

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: native scoped entry and state-first cleanup retain actual protected release captures.
Reach: the real selected scoped callback, its source-generated class tag and actual unsafe close result.
Limit: command admission and stored-row preservation remain carried by the joint driver.
Consumer: the complete initialized native evaluator and crew log histories.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- The native exit demand is computed independently of the current-code certificate. -/
def exit_pop (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : ExitV → FramePop EffName EffThunk Val Err Defect FiberId Ann
  | .success _ => frame.getCont .contA false
  | .failure cause => frame.getCont .contE true (some cause)

/-- The table is read only during external reply preparation, outside finalizer dispatch. -/
theorem finalizer_table (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV) :
    evaluatePrim.finalizerOr (interpAt root view table) machine fiber yielding exit =
      evaluatePrim.finalizerOr (interpAt root view []) machine fiber yielding exit := by
  rfl

/-- A native terminal primitive dispatches its actual exit through the finalizer hook. -/
theorem primitive_exit (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (current : fiber.frame.current = Prim.ofExit exit) :
    evaluatePrim (interpAt root view table) machine fiber yielding =
      evaluatePrim.finalizerOr (interpAt root view table) machine fiber yielding exit := by
  cases exit <;> simp only [evaluatePrim, current] <;> rfl

/-- Actual scoped entry retains the stable class and resolves its source's zero child. -/
theorem enter_scoped_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (input output : Kind) (point : Point) (body : NativeEff)
    (current : fiber.frame.current = .withFiber (.act point))
    (owned : CodeAt spec ⟨fiber.id, machine.state⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec view ⟨fiber.id, machine.state⟩) input output fiber.frame.stack)
    (found : Node.at_ (.eff spec.root) point.path = some (.eff (.scoped body))) :
    let next := enterScoped spec.root point machine fiber yielding
    AnswerFlow.FamilyResult (model spec view) (Edge spec view) ⟨fiber.id, next.machine.state⟩ output
      next.fiber.frame.current next.fiber.frame.stack := by
  obtain ⟨same, ready, permission⟩ := action_shape spec _ input (.act point) (current ▸ owned)
  subst input
  have source : Typed.SourcePoint spec.toSpec point := permission.2.2
  have next := SourceScope.next_of_at spec.root point _ 0 0 found source.1 rfl
  have child := Typed.zero_source spec.toSpec point next source.2.1
  refine ⟨.stable .root, .stable ready ?_, ?_⟩
  · exact ⟨rfl, Typed.resolve_source spec.toSpec fragment (point.child 0) child, trivial, trivial, trivial⟩
  · exact path_future spec view ⟨fiber.id, machine.state⟩ ⟨fiber.id, (enterScoped spec.root point machine fiber yielding).machine.state⟩ ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩ _ output fiber.frame.stack saved

/-- The actual selected scoped callback retains its ready phase and broad saved suffix. -/
theorem scoped_pop (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (input output : Kind)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (exit : ExitV)
    (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool)
    (owned : CodeAt spec world input (Prim.ofExit exit))
    (saved : Effect4.Contracts.Path (Edge spec view world) input output frame.stack)
    (selected : (exit_pop frame exit).answer = .frame (.onExit body (.scopedExit previous scope) flag)) :
    Ready spec world ∧ Effect4.Contracts.Path (Edge spec view world) (.stable .root) output (exit_pop frame exit).fiber.stack := by
  have good := current_exit spec fragment view world input exit owned
  have phase := code_phase spec world input _ owned
  cases exit with
  | success value =>
    obtain ⟨incoming, middle, _, edge, suffix⟩ := AnswerFlow.External.getCont_value_selected
      (model spec view) (interpAt spec.root view spec.table).toPrimInterp (Edge spec view)
      (family spec fragment view) (mask_edge spec view) world input output frame value _ good saved selected
    obtain ⟨_, rfl, ready⟩ := scoped_edge spec view world incoming middle body previous scope flag edge
    exact ⟨ready, suffix⟩
  | failure cause =>
    obtain ⟨incoming, middle, delivered, carried, _, edge, suffix⟩ := AnswerFlow.External.getCont_cause_selected
      (model spec view) (interpAt spec.root view spec.table).toPrimInterp (Edge spec view)
      (family spec fragment view) (mask_edge spec view) world input output frame cause _ good
      (by intro interrupt member kind old allowed; exact phase) saved selected
    obtain ⟨_, rfl, ready⟩ := scoped_edge spec view world incoming middle body previous scope flag edge
    exact ⟨ready, suffix⟩
/-- Native scoped exit closes the actual captured scope after its selected callback pop. -/
theorem exit_scoped_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (input output : Kind)
    (exit : ExitV) (current : fiber.frame.current = Prim.ofExit exit)
    (owned : CodeAt spec ⟨fiber.id, machine.state⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec machine.completedExits ⟨fiber.id, machine.state⟩) input output fiber.frame.stack)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    let next := exitScoped spec.root machine fiber yielding exit
    ∃ result, AnswerFlow.FamilyResult (model spec machine.completedExits) (Edge spec machine.completedExits)
      ⟨fiber.id, next.machine.state⟩ result next.fiber.frame.current next.fiber.frame.stack := by
  have terminal : CodeAt spec ⟨fiber.id, machine.state⟩ input (Prim.ofExit exit) := by
    rw [← current]
    exact owned
  let pop := exit_pop fiber.frame exit
  have closing (scope : Nat) (next : Stores) (program : Option Program)
      (found : storesCloseScopeUnsafe scope (pop.deliveredExit exit) pop.fiber.interruptible machine.state = some (next, program)) :=
    Typed.close_unsafe spec.toSpec scope (pop.deliveredExit exit) pop.fiber.interruptible machine.state next program scopes found
  unfold exitScoped
  dsimp only
  split
  · rename_i body previous scope flag selected
    have popped : Ready spec ⟨fiber.id, machine.state⟩ ∧
        Effect4.Contracts.Path (Edge spec machine.completedExits ⟨fiber.id, machine.state⟩) (.stable .root) output pop.fiber.stack := by
      apply scoped_pop spec fragment machine.completedExits ⟨fiber.id, machine.state⟩ input output
        fiber.frame exit body previous scope flag terminal saved
      cases exit <;> exact selected
    split
    · have result : AnswerFlow.FamilyResult (model spec machine.completedExits) (Edge spec machine.completedExits)
        ⟨fiber.id, machine.state⟩ output (Prim.ofExit (pop.deliveredExit exit)) pop.fiber.stack :=
        ⟨.stable .root, .stable popped.1 (Typed.exit_at spec.toSpec (pop.deliveredExit exit)), popped.2⟩
      cases exit <;> exact ⟨output, result⟩
    · rename_i state program closed
      have actual : storesCloseScopeUnsafe scope (pop.deliveredExit exit) pop.fiber.interruptible machine.state = some (state, program) := by
        cases exit <;> exact closed
      have retained := closing scope state program actual
      have counts := unsafe_counts scope (pop.deliveredExit exit) pop.fiber.interruptible machine.state state program actual
      have future : Future ⟨fiber.id, machine.state⟩ ⟨fiber.id, state⟩ :=
        ⟨rfl, Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩
      have ready := ready_future spec _ _ future popped.1
      have suffix := path_future spec machine.completedExits _ _ future (.stable .root) output _ popped.2
      cases program with
      | none =>
        have result : AnswerFlow.FamilyResult (model spec machine.completedExits) (Edge spec machine.completedExits)
            ⟨fiber.id, state⟩ output (Prim.ofExit (pop.deliveredExit exit)) pop.fiber.stack :=
          ⟨.stable .root, .stable ready (Typed.exit_at spec.toSpec (pop.deliveredExit exit)), suffix⟩
        cases exit <;> exact ⟨output, result⟩
      | some code =>
        have result : AnswerFlow.FamilyResult (model spec machine.completedExits) (Edge spec machine.completedExits)
            ⟨fiber.id, state⟩ output (finalizerCode (interpAt spec.root machine.completedExits spec.table)
              (pop.deliveredExit exit) (embed code)) pop.fiber.stack :=
          ⟨.stable .root, .stable ready (Typed.finalizerCode_at spec.toSpec machine.completedExits
            (pop.deliveredExit exit) (embed code) (retained.2 code rfl)), suffix⟩
        cases exit <;> exact ⟨output, result⟩
  · have state := StatePreservation.finalizerOr (interpAt spec.root machine.completedExits spec.table)
      (fun state => state = machine.state) machine fiber yielding exit rfl
    have result := finalizer_frame spec fragment machine.completedExits ⟨fiber.id, machine.state⟩
      input output machine fiber yielding exit current owned saved
    rw [primitive_exit spec.root machine.completedExits [] machine fiber yielding exit current,
      ← finalizer_table spec.root machine.completedExits spec.table, state]
    exact result
end Effect4.Program.AnswerSlots.Initialized

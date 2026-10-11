import Effect4.Laws.Program.ReleaseCustody.Control

/-!
Concept: scope-lifetime-finalization, R11, at most once per registered source identity.
Question: callback and evaluator clauses of `Execution.history`.
Reach: the existing native code, callbacks and stored programs, at the actual supplied root.
Limit: these producer bounds alone establish no whole-command or outside-loop preservation.
Unlock: continuation pop and native evaluator debit reuse the same residual credit projection.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Evaluation
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control

/-- Embedded exits carry no foreign release custody.
Consumer: `store_contA_credits` and `store_contE_credits`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem store_exit_credits (q : List Nat) (exit : ExitV) :
    currentCredits q (embed (Prim.ofExit exit)) = 0 := by
  cases exit <;> rfl

/-- Store value callbacks retain only their explicitly saved program credits.
Consumer: the native continuation-pop clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem store_contA_credits (q : List Nat) (name : Name) (value : Val) :
    currentCredits q (embed (Machine.contAOf name value)) = Names.contCredits q name := by
  fun_cases Machine.contAOf name value <;>
    simp only [embed, currentCredits, Names.contCredits, Names.actionCredits, opCredits,
      prog_of_credits, store_exit_credits, credit, foreignAt, Bool.false_eq_true, if_false, Nat.add_zero]

/-- Store cause callbacks produce exits, without new foreign release custody.
Consumer: the native continuation-pop clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem store_contE_credits (q : List Nat) (name : Name) (cause : CauseV) :
    currentCredits q (embed (Machine.contEOf name cause)) = 0 := by
  fun_cases Machine.contEOf name cause <;>
    simp only [store_exit_credits, embed, currentCredits]

/-- Every compiled source callback starts with zero outstanding foreign custody.
Consumer: the native continuation and suspension clauses of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resolve_credits (q : List Nat) (root : NativeEff) (point : Point) :
    currentCredits q (resolve root point) = 0 := by
  fun_cases resolve root point <;> simp only [compile_credits, badShape, currentCredits]

/-- Native exits have no outstanding foreign release credit.
Consumer: `contE_credits` and the native value continuation clause. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem exit_credits (q : List Nat) (exit : ExitV) :
    currentCredits q (Prim.ofExit exit) = 0 := by
  cases exit <;> rfl

/-- Layer compilation creates no foreign release custody before registration.
Consumer: `layer_zero_credits` and the native value continuation clause. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem layer_compile_credits (q : List Nat) (layer : LayerTerm NativeOp) (point : Point)
    (memo : MemoMapId) (scope : Nat) :
    currentCredits q (compileLayer layer point memo scope) = 0 := by
  fun_induction compileLayer layer point memo scope <;>
    simp only [currentCredits, nameCredits, opCredits, badShape, Nat.add_zero]
  assumption

/-- A layer frontier and its structural failure wrappers create no custody.
Consumer: `layer_with_credits`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem layer_zero_credits (q : List Nat) (layer : LayerTerm NativeOp) (point : Point)
    (memo : MemoMapId) (scope : Nat) :
    currentCredits q (resolveLayerZero layer point memo scope) = 0 := by
  fun_induction resolveLayerZero layer point memo scope <;>
    simp only [currentCredits, nameCredits, frontier, layer_compile_credits, Nat.add_zero]
  assumption

/-- A layer redirection retains zero custody at every fuel.
Consumer: `layer_resolve_credits`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem layer_with_credits (q : List Nat) (root : NativeEff) (fuel : Nat)
    (layer : LayerTerm NativeOp) (point : Point) (memo : MemoMapId) (scope : Nat) :
    currentCredits q (resolveLayerWith root fuel layer point memo scope) = 0 := by
  fun_induction resolveLayerWith root fuel layer point memo scope <;>
    simp (config := { failIfUnchanged := false }) only [currentCredits, nameCredits, badShape, layer_zero_credits,
      layer_compile_credits, Nat.add_zero]
  all_goals assumption

/-- Looking up the native layer producer introduces no foreign credit.
Consumer: native layer and value callback clauses of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem layer_resolve_credits (q : List Nat) (root : NativeEff) (point : Point)
    (memo : MemoMapId) (scope : Nat) :
    currentCredits q (resolveLayer root point memo scope) = 0 := by
  fun_cases resolveLayer root point memo scope <;>
    simp only [resolveLayer.resolveLayerTerm, layer_with_credits, badShape, currentCredits]

/-- Native region bodies retain zero custody before their registrations run.
Consumer: the native value continuation clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem region_credits (q : List Nat) (root : NativeEff) (region : Region) :
    currentCredits q (regionCode root region) = 0 := by
  fun_cases regionCode root region <;>
    simp only [currentCredits, resolve_credits, layer_resolve_credits]

/-- Context administration introduces no foreign release custody.
Consumer: the native layer callback clauses of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem context_credits (q : List Nat) (update : Env.ContextUpdate) (body : Region) :
    currentCredits q (updateContextAt update body) = 0 := rfl

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem layer_inner_credits (q : List Nat) (root : NativeEff) (point : Point) (memo : MemoMapId) (child : Nat) :
    currentCredits q (innerLayerAt root point memo child) = 0 := by
  fun_cases innerLayerAt root point memo child <;>
    simp only [currentCredits, opCredits, badShape, layer_resolve_credits, layer_compile_credits]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem layer_construction_credits (q : List Nat) (root : NativeEff) (point : Point) (scope : Nat) :
    currentCredits q (constructionAt root point scope) = 0 := by
  fun_cases constructionAt root point scope <;>
    simp only [currentCredits, context_credits, badShape]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem provide_layer_credits (q : List Nat) (root : NativeEff) (point : Point) (scope : Nat) :
    currentCredits q (provideLayerWithK root point scope) = 0 := by
  fun_cases provideLayerWithK root point scope <;>
    simp only [currentCredits, badShape]

  split <;> rfl

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem provide_body_credits (q : List Nat) (root : NativeEff) (point : Point) (value : Val) :
    currentCredits q (provideLayerBodyK root point value) = 0 := by
  fun_cases provideLayerBodyK root point value <;>
    simp only [currentCredits, context_credits, exit_credits, badShape]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem update_body_credits (q : List Nat) (root : NativeEff) (update : Env.ContextUpdate) (body : Region) (value : Val) :
    currentCredits q (updateThenK root update body value) = 0 := by
  fun_cases updateThenK root update body value <;>
    simp only [currentCredits, region_credits, badShape]


/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem build_scope_credits (q : List Nat) (point : Point) (scope : Nat) (value : Val) :
    currentCredits q (buildWithScopeK point scope value) = 0 := by
  fun_cases buildWithScopeK point scope value <;>
    simp only [currentCredits, opCredits, badShape]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem add_memo_credits (q : List Nat) (memo : MemoMapId) (value : Val) :
    currentCredits q (addCurrentMemoMapK memo value) = 0 := by
  fun_cases addCurrentMemoMapK memo value <;>
    simp only [currentCredits, badShape]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem provide_then_credits (q : List Nat) (point : Point) (memo : MemoMapId) (scope : Nat) (mode : CombineMode) (value : Val) :
    currentCredits q (provideThenK point memo scope mode value) = 0 := by
  fun_cases provideThenK point memo scope mode value <;>
    simp only [currentCredits, context_credits, badShape]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem combine_credits (q : List Nat) (mode : CombineMode) (that : Env.Ctx) (value : Val) :
    currentCredits q (combineWithK mode that value) = 0 := by
  fun_cases combineWithK mode that value <;>
    simp only [currentCredits, badShape]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem merge_context_credits (q : List Nat) (value : Val) :
    currentCredits q (mergeContextsK value) = 0 := by
  fun_cases mergeContextsK value <;>
    simp only [currentCredits, badShape]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem bind_service_credits (q : List Nat) (key : Option ServiceKey) (value : Val) :
    currentCredits q (bindServiceK key value) = 0 := by
  fun_cases bindServiceK key value <;>
    simp only [currentCredits]

/-- This native value producer introduces no foreign release custody.
Consumer: `contA_credits`, then `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem service_lookup_credits (q : List Nat) (key : ServiceKey) (value : Val) :
    currentCredits q (serviceLookupK key value) = 0 := by
  fun_cases serviceLookupK key value <;>
    simp only [currentCredits, badShape]

/-- Every native value callback fits the reservation of its existing name.
Consumer: the value-pop clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem contA_credits (q : List Nat) (root : NativeEff) (name : EffName) (value : Val) :
    currentCredits q (Program.contAOf root name value) ≤ nameCredits q name := by
  fun_cases Program.contAOf root name value <;>
    simp only [resolve_credits, exit_credits, store_contA_credits, currentCredits,
      nameCredits, opCredits, responseCredits, ite_true, registration_template, fin_program_credits, Names.contCredits,
      layer_inner_credits, layer_construction_credits, provide_layer_credits,
      provide_body_credits, update_body_credits, build_scope_credits, add_memo_credits,
      provide_then_credits, combine_credits, merge_context_credits, bind_service_credits,
      service_lookup_credits, layer_resolve_credits, region_credits, context_credits, scopeAddAt,
      credit, foreignAt, badShape, Bool.false_eq_true, if_false, Nat.add_zero, 
      Nat.sub_self, Nat.le_refl, Nat.zero_le]

/-- Every native failure callback has zero outstanding foreign release custody.
Consumer: the cause-pop clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem contE_credits (q : List Nat) (root : NativeEff) (name : EffName) (cause : CauseV) :
    currentCredits q (Program.contEOf root name cause) = 0 := by
  fun_cases Program.contEOf root name cause <;>
    simp only [resolve_credits, exit_credits, store_contE_credits, currentCredits]

/-- Opening every native suspension retains exactly the credits of its stored residual.
Consumer: the suspension and with-fiber fallback clauses of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem suspend_credits (q : List Nat) (root : NativeEff) (thunk : EffThunk) :
    currentCredits q (suspendBodyAt root thunk) = currentCredits q (.suspend thunk) := by
  fun_cases suspendBodyAt root thunk <;>
    simp only [currentCredits, opCredits, resolve_credits, compile_credits,
      prog_of_credits, Point.ofCapture, credit, foreignAt, frontier, badShape, Nat.zero_add]

  case case20 => rfl
  case case21 =>
    cases thunk <;> simp (config := { failIfUnchanged := false }) only [currentCredits]
    case store stored noBody noMemo noProgram noForeign =>
      cases stored <;> simp (config := { failIfUnchanged := false }) only [currentCredits]
      all_goals aesop (rule_sets := [Effect4.Stores])

/-- The saved constant determines response custody beneath a wrapper.
Consumer: the complete forced-yield clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem constant_stack_credits (q : List Nat) (body next : NCode) (stack : List NCode) :
    stackCredits q (.onSuccessConst body next) stack = stackCredits q next stack := by
  unfold stackCredits
  split <;> rfl

/-- Injecting a yield keeps the selected fiber's full residual credit.
Consumer: the complete loop injection clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem yield_wrapper_credits (q : List Nat) (fiber : Fiber) :
    fiberCredits q { fiber with
      frame := { fiber.frame with current := .onSuccessConst (.yieldNowWith 0) fiber.frame.current }
      yieldOverride := none } = fiberCredits q fiber := by
  simp only [fiberCredits, currentCredits, Nat.zero_add, constant_stack_credits]

/-- Pushing any constant continuation transfers its saved code without duplicating lower custody.
Consumer: the full frame-step clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem constant_push_credits (q : List Nat) (fiber : Fiber) (body next : NCode)
    (current : fiber.frame.current = .onSuccessConst body next) :
    fiberCredits q { fiber with frame := { fiber.frame with
      current := body
      stack := .onSuccessConst body next :: fiber.frame.stack } } = fiberCredits q fiber := by
  unfold fiberCredits
  rw [current]
  simp only [currentCredits, stackCredits, constant_stack_credits, Nat.add_assoc]

/-- Replacing active code by an interruption cause can only discard response custody.
Consumer: loop-top interruption in `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem failure_stack_le (q : List Nat) (cause : CauseV) (active : NCode) (stack : List NCode) :
    stackCredits q (.failure cause) stack ≤ stackCredits q active stack := by
  unfold stackCredits
  split
  · exact Nat.le_refl _
  · simp only [responseCredits, Nat.zero_add]
    exact Nat.le_add_left _ _
  · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- An interruption cause discards active and response custody without creating credits.
Consumer: the actual interrupt edit in `Execution.outer_custody`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem failure_fiber_le (q : List Nat) (fiber : Fiber) (cause : CauseV) :
    fiberCredits q { fiber with frame := { fiber.frame with current := .failure cause } } ≤
      fiberCredits q fiber := by
  have smaller := failure_stack_le q cause fiber.frame.current fiber.frame.stack
  simp only [fiberCredits, currentCredits, Nat.zero_add]
  omega

/-- The actual loop-top edit never increases selected control custody.
Consumer: the full iteration clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem loop_top_credits (q : List Nat) (fiber : Fiber) :
    fiberCredits q (countOp (runloopTop fiber)) ≤ fiberCredits q fiber := by
  unfold countOp runloopTop
  split
  · simp only [fiberCredits, currentCredits, Nat.zero_add]
    have smaller := failure_stack_le q fiber.frame.pendingCause fiber.frame.current fiber.frame.stack
    omega
  · exact Nat.le_refl _

/-- The native evaluator pushes every constant continuation with its actual frame event.
Consumer: the actual forced-yield command clause of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem constant_start (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : Fiber) (yielding : Bool) (body next : NCode)
    (current : fiber.frame.current = .onSuccessConst body next) :
    evaluateNative root machine fiber yielding table =
      ⟨machine.emit [.frame fiber.id (.pushed (.onSuccessConst body next))],
        { fiber with frame := { fiber.frame with
          current := body
          stack := .onSuccessConst body next :: fiber.frame.stack } }, yielding, .continue_, []⟩ := by
  have park : (interpAt root machine.completedExits table).parkOf (.onSuccessConst body next) = none := rfl
  have frame : fiber.frame.step (interpAt root machine.completedExits table).toPrimInterp =
      (.running { fiber.frame with
        current := body
        stack := .onSuccessConst body next :: fiber.frame.stack },
       [.pushed (.onSuccessConst body next)]) := by
    unfold FrameFiber.step
    rw [current]
  simp only [evaluateNative, evaluatePrim, current, park, evaluatePrim.stepFrame, frame]
  rfl

/-- A true charged yield verdict injects and pushes the saved constant at one charged checkpoint.
Consumer: the full yield branch of `Execution.history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem forced_yield_iteration (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (fiber : Fiber) (interrupt : fiber.frame.deferredInterrupt = false)
    (verdict : yieldVerdict (countOp fiber) = true) (prevent : fiber.preventYield = false) :
    iteration (evaluator := evaluatorFor root table) (interpOf root table) machine fiber false =
      ⟨(machine.emit [.yieldInjected fiber.id (fiber.currentOpCount + 1)]).emit
          [.frame fiber.id (.pushed (.onSuccessConst (.yieldNowWith 0) fiber.frame.current))],
        { countOp fiber with
          frame := { fiber.frame with
            current := .yieldNowWith 0
            stack := .onSuccessConst (.yieldNowWith 0) fiber.frame.current :: fiber.frame.stack }
          yieldOverride := none }, true, .continue_, []⟩ := by
  have top : runloopTop fiber = fiber := by
    simp only [runloopTop, interrupt, Bool.false_eq_true, if_false]
  have injected : injectYield machine (countOp fiber) false =
      some ⟨machine.emit [.yieldInjected fiber.id (fiber.currentOpCount + 1)],
        { countOp fiber with
          frame := { fiber.frame with current := .onSuccessConst (.yieldNowWith 0) fiber.frame.current }
          yieldOverride := none }, true, .continue_, []⟩ := by
    unfold injectYield
    rw [verdict]
    simp only [countOp, prevent, Bool.not_false, Bool.and_true, if_true]
  simp only [iteration, top, injected]
  change evaluateNative root _ _ true table = _
  rw [constant_start root table _ _ true (.yieldNowWith 0) fiber.frame.current rfl]
  rfl

/-- The actual forced-yield command retains full custody on every selected native fiber.
Consumer: the yield-injection branch of `Execution.history`.
The arbitrary pending suffix, actual operation count and stored continuation remain explicit. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem forced_yield_loop_funded (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (id : FiberId) (fiber : Fiber) (pending : List Command) (q : List Nat)
    (unique : (machine.fibers.map RunFiber.id).Nodup)
    (funded : Funded q machine (.loop id false :: pending))
    (found : machine.fiber? id = some fiber)
    (interrupt : fiber.frame.deferredInterrupt = false)
    (verdict : yieldVerdict (countOp fiber) = true) (prevent : fiber.preventYield = false) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) machine
      (.loop id false) pending).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) machine
        (.loop id false) pending).2 := by
  rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table)
    _ machine id fiber false pending found,
    forced_yield_iteration root table machine fiber interrupt verdict prevent]
  let next : Fiber := { countOp fiber with
    frame := { fiber.frame with
      current := .yieldNowWith 0
      stack := .onSuccessConst (.yieldNowWith 0) fiber.frame.current :: fiber.frame.stack }
    yieldOverride := none }
  let injected : NativeMachine := machine.emit [.yieldInjected fiber.id (fiber.currentOpCount + 1)]
  let events : List ReleaseTrace.Event :=
    [.frame fiber.id (.pushed (.onSuccessConst (.yieldNowWith 0) fiber.frame.current))]
  change Funded q ((injected.emit events).update next) (.loop id true :: pending)
  have member : fiber ∈ (injected.emit events).fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q (injected.emit events) fiber next unique member rfl
  rw [emit_credits, emit_credits] at changed
  have frame : fiberCredits q next = fiberCredits q fiber := by
    simp only [next, fiberCredits, countOp, currentCredits, stackCredits, Nat.zero_add]
  have registered : ((injected.emit events).update next).trace.countP (ReleaseTrace.registeredAt q) =
      machine.trace.countP (ReleaseTrace.registeredAt q) := by
    change (injected.emit events).trace.countP (ReleaseTrace.registeredAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    change injected.trace.countP (ReleaseTrace.registeredAt q) + 0 = _
    rw [Nat.add_zero]
    change (machine.emit _).trace.countP (ReleaseTrace.registeredAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    exact Nat.add_zero _
  have starts : ((injected.emit events).update next).trace.countP (ReleaseTrace.releaseAt q) =
      machine.trace.countP (ReleaseTrace.releaseAt q) := by
    change (injected.emit events).trace.countP (ReleaseTrace.releaseAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    change injected.trace.countP (ReleaseTrace.releaseAt q) + 0 = _
    rw [Nat.add_zero]
    change (machine.emit _).trace.countP (ReleaseTrace.releaseAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    exact Nat.add_zero _
  unfold Funded at funded ⊢
  rw [registered, starts]
  simp only [List.map_cons, commandCredits, List.sum_cons, Nat.zero_add] at funded ⊢
  omega

end Effect4.Program.ReleaseCustody.Evaluation

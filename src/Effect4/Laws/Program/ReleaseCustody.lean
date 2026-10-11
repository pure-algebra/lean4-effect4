import Effect4.Laws.Program.ReleaseTrace
import Effect4.Laws.Program.ControlSteps

/-!
# Finalization custody transfers

Concept: scope-lifetime-finalization, R11, at most once per registration counted by identity.
Question: helpers of `Workers.Assertions.releases_step` and `QueueWorkers` release accounting.
Reach: source-indexed foreign finalizers, fresh registration keys, scope close orders and native continuation responses.
The clauses track stored entries, residual close chains and response-dependent `afterScopeAdd` ownership.
They do not prove whole-machine custody preservation, source-use uniqueness, progress or host behavior.
Unlock: command custody can reuse these transfers before applying the existing machine lift.
Point environments remain name-specific; generator points require their separate program counter.
-/

set_option autoImplicit false

namespace Effect4.Program.ReleaseCustody

open Effect4 Effect4.Machine Effect4.Program

/-- A foreign finalizer carries its acquisition's source identity. -/
def foreignAt (q : List Nat) : FinName → Bool
  | .foreign c => c.path == q
  | _ => false

/-- One foreign finalizer contributes one credit at its acquisition source. -/
def credit (q : List Nat) (fin : FinName) : Nat := if foreignAt q fin then 1 else 0

/-- Credits in a captured close order or the remainder of its sequential walk. -/
def orderCredits (q : List Nat) (fins : List FinName) : Nat := fins.countP (foreignAt q)

/-- Credits in live scope entries, before transfer into a close order. -/
def scopeCredits (q : List Nat) (scope : ScopeV) : Nat :=
  orderCredits q (scope.finalizers.map Prod.snd)

/-- The continuation owns a release only when registration answers a closing exit.
A unit response transfers ownership to the scope entry. A malformed response owns no executable release. -/
def afterAddCredits (q : List Nat) (fin : FinName) (response : Val) : Nat :=
  if response = Val.unit then 0 else
    if (exitOfVal response).isSome then credit q fin else 0

/-- Fresh open registration transfers one source credit into the scope entry.
Consumer: the scope-add command custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem add_open (q : List Nat) (scope : ScopeV) (key : Nat) (fin : FinName)
    (opened : scope.isClosed = false) (fresh : key ∉ scope.finalizerKeys) :
    scopeCredits q (scope.addUnsafe key fin) = scopeCredits q scope + credit q fin := by
  unfold scopeCredits orderCredits credit
  rw [Scope.addUnsafe_finalizers scope key fin opened fresh,
    List.map_append, List.countP_append]
  simp only [List.map_cons, List.map_nil, List.countP_cons, List.countP_nil, Nat.zero_add]

/-- Closing transfers every source credit into the exact residual close order and empties the entry.
Consumer: `close_chain_transfer`, then the close command custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem close_scope (q : List Nat) (scope : ScopeV) (exit : ExitV) :
    scopeCredits q (Scope.closeState scope exit) = 0 ∧
      orderCredits q scope.closeOrder = scopeCredits q scope := by
  constructor
  · unfold scopeCredits orderCredits
    rw [Scope.closeState_finalizers]
    rfl
  · unfold scopeCredits orderCredits
    rw [Scope.closeOrder_eq, List.countP_reverse]

/-- The first close-chain step moves one credit to the selected finalizer and retains the tail.
Consumer: the sequential iterator command custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem close_chain_transfer (q : List Nat) (scope : ScopeV) (exit : ExitV)
    (fin : FinName) (rest : List FinName) (order : scope.closeOrder = fin :: rest) :
    scopeCredits q (Scope.closeState scope exit) + credit q fin + orderCredits q rest =
      scopeCredits q scope := by
  obtain ⟨closed, transferred⟩ := close_scope q scope exit
  rw [closed, Nat.zero_add]
  rw [order] at transferred
  simpa only [orderCredits, List.countP_cons, credit, Nat.add_comm] using transferred

/-- Unit delivery leaves no release credit in `afterScopeAdd`.
Consumer: `after_add_unit`, then the delivery command custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem after_add_unit_credit (q : List Nat) (fin : FinName) :
    afterAddCredits q fin Val.unit = 0 := by
  unfold afterAddCredits
  rw [if_pos rfl]

/-- A reified closing exit carries one residual release credit.
Consumer: `after_add_exit`, then the delivery command custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem after_add_exit_credit (q : List Nat) (fin : FinName) (exit : ExitV) :
    afterAddCredits q fin (reifyExitVal exit) = credit q fin := by
  have notUnit : reifyExitVal exit ≠ Val.unit := by
    cases exit <;> intro h <;> cases h
  have read : exitOfVal (reifyExitVal exit) = some exit := by
    cases exit with
    | success value => exact exitOfVal_exitOk value
    | failure cause => exact exitOfVal_exitErr cause
  unfold afterAddCredits
  rw [if_neg notUnit, read]
  rfl

/-- Actual native unit continuation consumes its response-dependent credit and answers the acquisition value.
Consumer: the delivery command custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem after_add_unit (root : NativeEff) (q : List Nat) (a : Val) (fin : FinName) :
    afterAddCredits q fin Val.unit = 0 ∧
      contAOf root (.afterScopeAdd a fin) Val.unit = .success a :=
  ⟨after_add_unit_credit q fin, rfl⟩

/-- Actual native closed-scope continuation moves its credit to exactly one residual finalizer program.
Consumer: the delivery command custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem after_add_exit (root : NativeEff) (q : List Nat) (a : Val) (fin : FinName) (exit : ExitV) :
    afterAddCredits q fin (reifyExitVal exit) = credit q fin ∧
      contAOf root (.afterScopeAdd a fin) (reifyExitVal exit) =
        .onSuccess (embed (finProgram fin exit)) (.constant a) := by
  refine ⟨after_add_exit_credit q fin exit, ?_⟩
  have notUnit : reifyExitVal exit ≠ Val.unit := by
    cases exit <;> intro h <;> cases h
  have read : exitOfVal (reifyExitVal exit) = some exit := by
    cases exit with
    | success value => exact exitOfVal_exitOk value
    | failure cause => exact exitOfVal_exitErr cause
  change (if reifyExitVal exit = Val.unit then _ else _) = _
  rw [if_neg notUnit, read]

/-- A foreign suspension transfers the registered capture to the actual release-start continuation.
Consumer: the suspension and frame-push command custody clauses of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem foreign_suspension (root : NativeEff) (q : List Nat) (c : Capture) (exit : ExitV) :
    suspendBodyAt root (.store (.foreign c exit)) =
      .onSuccess (.withFiber .getCtx) (.releaseUnder (Point.ofCapture c) c.ctx exit) ∧
    ReleaseTrace.releaseAt q
      (.frame ⟨0⟩ (.pushed (.onSuccess (.withFiber .getCtx)
        (.releaseUnder (Point.ofCapture c) c.ctx exit)))) = foreignAt q (.foreign c) :=
  ⟨rfl, rfl⟩

/-- The actual native scope-add command transfers the credit to a fresh open-scope entry.
Consumer: the registration command custody clause of `Workers.Assertions.releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_add_open (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (q : List Nat) (scope : Nat) (entry : ScopeEntry) (fin : FinName)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (found : m.state.scopes.entryAt scope = some entry)
    (opened : entry.scope.isClosed = false) (fresh : m.state.nextName ∉ entry.scope.finalizerKeys) :
    (evaluateNative root m f yielding table).machine.state =
      { m.state with
        scopes := m.state.scopes.setEntry { entry with scope := entry.scope.addUnsafe m.state.nextName fin }
        nextName := m.state.nextName + 1 } ∧
    scopeCredits q (entry.scope.addUnsafe m.state.nextName fin) + afterAddCredits q fin Val.unit =
      scopeCredits q entry.scope + credit q fin := by
  have closing : entry.scope.closingExit? = none :=
    ScopeState.closingExit_of_not_closed entry.scope.state opened
  have answer : syncOpStep (.scopeAdd scope fin) m.state = some
      ({ m.state with
        scopes := m.state.scopes.setEntry { entry with scope := entry.scope.addUnsafe m.state.nextName fin }
        nextName := m.state.nextName + 1 }, Val.unit) := by
    simp only [syncOpStep, found, closing]
  constructor
  · rw [ControlSteps.native_sync_op root table m f yielding (.scopeAdd scope fin) _ _ current answer]
  · rw [after_add_unit_credit, Nat.add_zero]
    exact add_open q entry.scope m.state.nextName fin opened fresh

/-- The actual native scope-add command on a closed scope leaves the credit in the closing-exit response.
Consumer: the immediate-release command custody clause of `Workers.Assertions.releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_add_closed (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (q : List Nat) (scope : Nat) (entry : ScopeEntry) (fin : FinName) (exit : ExitV)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (found : m.state.scopes.entryAt scope = some entry)
    (closing : entry.scope.closingExit? = some exit) :
    (evaluateNative root m f yielding table).machine.state = m.state ∧
    (evaluateNative root m f yielding table).fiber.frame.current = .success (reifyExitVal exit) ∧
    afterAddCredits q fin (reifyExitVal exit) = credit q fin := by
  have answer : syncOpStep (.scopeAdd scope fin) m.state = some (m.state, reifyExitVal exit) := by
    simp only [syncOpStep, found, closing]
  rw [ControlSteps.native_sync_op root table m f yielding (.scopeAdd scope fin) _ _ current answer]
  exact ⟨rfl, rfl, after_add_exit_credit q fin exit⟩

/-- The actual close iterator selects its head and retains the exact residual order.
Consumer: `close_seq_command` and the close-iterator custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem close_seq_start (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (fin : FinName) (rest : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (cursor : Val)
    (current : f.frame.current = .iterator (.store (.closeSeq (fin :: rest) exit captured)) cursor) :
 evaluateNative root m f yielding table =
      ⟨m.emit [.frame f.id (.pushed (.iterator
          (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) cursor))],
       { f with frame := { f.frame with
         current := .exitFrame (embed (finProgram fin exit))
         stack := .iterator (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) cursor :: f.frame.stack } },
       yielding, .continue_, [], []⟩ := by
  have next : ((interpAt root m.completedExits table).toPrimInterp.iterNext
      (.store (.closeSeq (fin :: rest) exit captured)) cursor).snd =
      .resume (.exitFrame (embed (finProgram fin exit)))
        (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) := rfl
  have arm := Prim.armA_iterator_resume (interpAt root m.completedExits table).toPrimInterp
    (.store (.closeSeq (fin :: rest) exit captured)) cursor cursor
    (.exitFrame (embed (finProgram fin exit)))
    (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) none next
  have frame : f.frame.step (interpAt root m.completedExits table).toPrimInterp =
      (.running { f.frame with
        current := .exitFrame (embed (finProgram fin exit))
        stack := .iterator (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) cursor :: f.frame.stack },
      [.pushed (.iterator (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) cursor)]) := by
    simp only [FrameFiber.step, current, arm]
    rfl
  have park : (interpAt root m.completedExits table).parkOf
      (.iterator (.store (.closeSeq (fin :: rest) exit captured)) cursor) = none := rfl
  simp only [evaluateNative, evaluatePrim, current, park, evaluatePrim.stepFrame, frame]
  rfl


/-- The actual native close iterator transfers its head credit to the selected finalizer,
retains its tail in the pushed iterator, and emits no release-start event yet.
Consumer: the close-iterator command custody clause of `Workers.Assertions.releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem close_seq_command (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (q : List Nat) (fin : FinName) (rest : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (cursor : Val)
    (current : f.frame.current = .iterator (.store (.closeSeq (fin :: rest) exit captured)) cursor) :
    (evaluateNative root m f yielding table).fiber.frame.current = .exitFrame (embed (finProgram fin exit)) ∧
    (evaluateNative root m f yielding table).fiber.frame.stack =
      .iterator (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) cursor :: f.frame.stack ∧
    (evaluateNative root m f yielding table).machine.trace.countP (ReleaseTrace.releaseAt q) =
      m.trace.countP (ReleaseTrace.releaseAt q) ∧
    credit q fin + orderCredits q rest = orderCredits q (fin :: rest) := by
  rw [close_seq_start root table m f yielding fin rest exit captured cursor current]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.releaseAt q) + 0 = _
    exact Nat.add_zero _
  · simp only [orderCredits, List.countP_cons, credit, Nat.add_comm]

/-- The actual release-start command pushes one source-identified frame on the arbitrary fiber.
Consumer: `release_start_count`, then the frame-push custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_start (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) (c : Capture) (exit : ExitV)
    (current : f.frame.current = suspendBodyAt root (.store (.foreign c exit))) :
    evaluateNative root m f yielding table =
      ⟨m.emit [.frame f.id (.pushed (.onSuccess (.withFiber .getCtx)
          (.releaseUnder (Point.ofCapture c) c.ctx exit)))],
       { f with frame := { f.frame with
         current := Prim.withFiber EffThunk.getCtx
         stack := .onSuccess (.withFiber .getCtx)
           (.releaseUnder (Point.ofCapture c) c.ctx exit) :: f.frame.stack } },
       yielding, .continue_, [], []⟩ := by
  have shape : f.frame.current = .onSuccess (.withFiber .getCtx)
      (.releaseUnder (Point.ofCapture c) c.ctx exit) := current
  have park : (interpAt root m.completedExits table).parkOf
      (.onSuccess (.withFiber .getCtx) (.releaseUnder (Point.ofCapture c) c.ctx exit)) = none := rfl
  have frame : f.frame.step (interpAt root m.completedExits table).toPrimInterp =
      (.running { f.frame with
        current := Prim.withFiber EffThunk.getCtx
        stack := .onSuccess (.withFiber .getCtx)
          (.releaseUnder (Point.ofCapture c) c.ctx exit) :: f.frame.stack },
       [.pushed (.onSuccess (.withFiber .getCtx)
         (.releaseUnder (Point.ofCapture c) c.ctx exit))]) := by
    unfold FrameFiber.step
    rw [shape]
  simp only [evaluateNative, evaluatePrim, shape, park, evaluatePrim.stepFrame, frame]
  rfl

/-- A release-start command spends exactly one credit at its acquisition's source identity.
Consumer: the frame-push custody clause of `releases_step`; it does not bound prior registrations. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_start_count (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) (q : List Nat) (c : Capture) (exit : ExitV)
    (current : f.frame.current = suspendBodyAt root (.store (.foreign c exit))) :
    (evaluateNative root m f yielding table).machine.trace.countP (ReleaseTrace.releaseAt q) =
      m.trace.countP (ReleaseTrace.releaseAt q) + credit q (.foreign c) := by
  rw [release_start root table m f yielding c exit current]
  rw [RunMachine.emit_trace, List.countP_append]
  simp only [List.countP_cons, List.countP_nil, Nat.zero_add, ReleaseTrace.releaseAt,
    Point.ofCapture, credit, foreignAt]
  rfl

/-- A release start changes no registration count.
Consumer: `release_start_debit`, then the frame-push custody clause of `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_start_registered (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (q : List Nat) (c : Capture) (exit : ExitV)
    (current : f.frame.current = suspendBodyAt root (.store (.foreign c exit))) :
    (evaluateNative root m f yielding table).machine.trace.countP (ReleaseTrace.registeredAt q) =
      m.trace.countP (ReleaseTrace.registeredAt q) := by
  rw [release_start root table m f yielding c exit current]
  rw [RunMachine.emit_trace, List.countP_append]
  change m.trace.countP (ReleaseTrace.registeredAt q) + 0 = _
  exact Nat.add_zero _

/-- The actual release-start command consumes one available source credit.
Consumer: `release_loop_debit`; the custody invariant must supply the available credit. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_start_debit (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (q : List Nat) (c : Capture) (exit : ExitV)
    (current : f.frame.current = suspendBodyAt root (.store (.foreign c exit)))
    (available : m.trace.countP (ReleaseTrace.releaseAt q) + credit q (.foreign c) ≤
      m.trace.countP (ReleaseTrace.registeredAt q)) :
    (evaluateNative root m f yielding table).machine.trace.countP (ReleaseTrace.releaseAt q) ≤
      (evaluateNative root m f yielding table).machine.trace.countP (ReleaseTrace.registeredAt q) := by
  rw [release_start_count root table m f yielding q c exit current,
    release_start_registered root table m f yielding q c exit current]
  exact available

/-- An arbitrary-fiber loop command consumes the source credit and retains its unfinished commands.
Consumer: the loop command custody clause of `Workers.Assertions.releases_step`.
The available-credit premise remains the whole-configuration custody obligation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_loop_debit (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (q : List Nat) (c : Capture) (exit : ExitV)
    (found : m.fiber? id = some f)
    (current : f.frame.current = suspendBodyAt root (.store (.foreign c exit)))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield)
    (available : m.trace.countP (ReleaseTrace.releaseAt q) + credit q (.foreign c) ≤
      m.trace.countP (ReleaseTrace.registeredAt q)) :
    (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest).1.trace.countP (ReleaseTrace.releaseAt q) ≤
    (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest).1.trace.countP (ReleaseTrace.registeredAt q) := by
  have trace : (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest).1.trace =
      (evaluateNative root m (countOp f) yielding table).machine.trace := by
    rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table)
      _ m id f yielding rest found]
    rw [Machine.ControlSteps.iteration_below_budget (evaluator := evaluatorFor root table)
      _ m f yielding interrupt override budget]
    change (settle id rest (evaluateNative root m (countOp f) yielding table)).1.trace = _
    rw [release_start root table m (countOp f) yielding c exit current]
    rfl
  rw [trace]
  exact release_start_debit root table m (countOp f) yielding q c exit current available

end Effect4.Program.ReleaseCustody

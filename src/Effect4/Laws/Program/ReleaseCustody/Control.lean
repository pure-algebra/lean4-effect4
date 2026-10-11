import Effect4.Laws.Program.ReleaseCustody
import Effect4.Laws.Machine.ControlWeights

/-!
# Registration custody at control positions

Concept: scope-lifetime-finalization, R11, at most once per registration counted by identity.
Question: helpers of `Workers.Assertions.releases_step` and the queue release debit claim.
Reach: the source compile, initial machine and named native registration command.
The projection distinguishes active code from remaining stack callbacks and close iterators.
It includes scope entries, queued resume code, unlaunched race programs and pending resume commands.
It does not establish whole-command preservation, source-use uniqueness, progress or host behavior.
Foreign code hidden in arbitrary synthetic store-program names requires a separate source-shape premise.
Unlock: source initialization and the registration clause of a command custody invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Control
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.ReleaseCustody
abbrev Fiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev Command := Cmd EffName EffThunk Val Err Defect FiberId Ann

def opCredits (q : List Nat) : SyncOp → Nat
  | .scopeAdd _ fin => credit q fin
  | _ => 0

def responseCredits (q : List Nat) (fin : FinName) : NCode → Nat
  | .success v => afterAddCredits q fin v
  | .failure _ => 0
  | .sync (.op (.scopeAdd _ pending)) => if pending = fin then 0 else credit q fin
  | _ => credit q fin

def currentCredits (q : List Nat) : NCode → Nat
  | .sync (.op op) => opCredits q op
  | .sync (.store (.op op)) => opCredits q op
  | .suspend (.store (.foreign c _)) => credit q (.foreign c)
  | .suspend (.store (.body (.closeWalk _ order _))) => orderCredits q order
  | .withFiber (.store (.act (.closePar order _))) => orderCredits q order
  | .iterator (.store (.closeSeq order _ _)) _ => orderCredits q order
  | .onSuccess body (.afterScopeAdd _ fin) =>
      (currentCredits q body + responseCredits q fin body) - credit q fin
  | .onSuccess body (.releaseUnder p _ _) => currentCredits q body + if p.path == q then 1 else 0
  | .onSuccess body _ => currentCredits q body
  | .onSuccessConst body next => currentCredits q body + currentCredits q next
  | .onFailure body _ => currentCredits q body
  | .onSuccessAndFailure body _ _ => currentCredits q body
  | .exitFrame body => currentCredits q body
  | .onExit body (.store (.finalizerName fin)) _ => currentCredits q body + credit q fin
  | .onExit body _ _ => currentCredits q body
  | _ => 0

def futureCredits (q : List Nat) : NCode → Nat
  | .onSuccess _ (.afterScopeAdd _ fin) => credit q fin
  | .onSuccessConst _ next => currentCredits q next
  | .iterator (.store (.closeSeq order _ _)) _ => orderCredits q order
  | .onExit _ (.store (.finalizerName fin)) _ => credit q fin
  | _ => 0

def stackCredits (q : List Nat) (active : NCode) : List NCode → Nat
  | .onSuccess _ (.afterScopeAdd _ fin) :: rest =>
      responseCredits q fin active + (rest.map (futureCredits q)).sum
  | head :: rest => futureCredits q head + (rest.map (futureCredits q)).sum
  | [] => 0

def taskCredits (q : List Nat) : Task EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .resume _ _ answer => currentCredits q answer
  | _ => 0

def fiberCredits (q : List Nat) (f : Fiber) : Nat :=
  currentCredits q f.frame.current + stackCredits q f.frame.current f.frame.stack +
    (f.dispatcher.buckets.map fun bucket => (bucket.tasks.map (taskCredits q)).sum).sum

def commandCredits (q : List Nat) : Command → Nat
  | .resume _ _ answer => currentCredits q answer
  | _ => 0

def machineCredits (q : List Nat) (m : NativeMachine) : Nat :=
  (m.state.scopes.entries.map fun e => scopeCredits q e.scope).sum +
    (m.fibers.map (fiberCredits q)).sum +
    (m.races.map fun r => (r.programs.map (currentCredits q)).sum).sum

def Funded (q : List Nat) (m : NativeMachine) (pending : List Command) : Prop :=
  m.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q m +
    (pending.map (commandCredits q)).sum ≤ m.trace.countP (ReleaseTrace.registeredAt q)

/-- The unpushed registration template owns no credit yet.
Consumer: `registration_frame_credits`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registration_template (q : List Nat) (scope : Nat) (a : Val) (fin : FinName) :
    currentCredits q (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)) = 0 := by
  simp only [currentCredits, opCredits, responseCredits, ite_true, Nat.add_zero, Nat.sub_self]

/-- Active non-exit code keeps every lower callback reservation.
Consumer: `registration_frame_credits`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_before_push (q : List Nat) (body : NCode) (name : EffName) (stack : List NCode) :
    stackCredits q (.onSuccess body name) stack = (stack.map (futureCredits q)).sum := by
  unfold stackCredits
  split <;> rfl

/-- Pushing the registration template creates exactly the credit its trace registration funds.
Consumer: `registration_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registration_frame_credits (q : List Nat) (f : Fiber) (scope : Nat) (a : Val) (fin : FinName)
    (current : f.frame.current = .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)) :
    fiberCredits q { f with frame := { f.frame with
      current := .sync (.op (.scopeAdd scope fin))
      stack := .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: f.frame.stack } } =
      fiberCredits q f + credit q fin := by
  unfold fiberCredits
  rw [current, registration_template, stack_before_push]
  simp only [currentCredits, opCredits, stackCredits, responseCredits, ite_true, Nat.zero_add]
  omega

/-- The actual registration command pushes its callback before evaluating scope-add.
Consumer: `registration_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registration_start (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : Fiber) (yielding : Bool) (scope : Nat) (a : Val) (fin : FinName)
    (current : f.frame.current = .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)) :
    evaluateNative root m f yielding table =
      ⟨m.emit [.frame f.id (.pushed (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)))],
       { f with frame := { f.frame with
         current := .sync (.op (.scopeAdd scope fin))
         stack := .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: f.frame.stack } },
       yielding, .continue_, []⟩ := by
  have park : (interpAt root m.completedExits table).parkOf
      (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)) = none := rfl
  have frame : f.frame.step (interpAt root m.completedExits table).toPrimInterp =
      (.running { f.frame with
        current := .sync (.op (.scopeAdd scope fin))
        stack := .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: f.frame.stack },
      [.pushed (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin))]) := by
    unfold FrameFiber.step
    rw [current]
  simp only [evaluateNative, evaluatePrim, current, park, evaluatePrim.stepFrame, frame]
  rfl

/-- The actual registration loop preserves its pending command suffix.
Consumer: `registration_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registration_loop (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (rest : List Command)
    (scope : Nat) (a : Val) (fin : FinName)
    (found : m.fiber? id = some f)
    (current : f.frame.current = .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    driveStep (evaluator := evaluatorFor root table) (interpOf root table) m (.loop id yielding) rest =
      ((m.emit [.frame f.id (.pushed (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)))]).update
        { countOp f with frame := { f.frame with
          current := .sync (.op (.scopeAdd scope fin))
          stack := .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: f.frame.stack } },
        .loop id yielding :: rest) := by
  rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table) _ m id f yielding rest found]
  rw [Machine.ControlSteps.iteration_below_budget (evaluator := evaluatorFor root table)
    _ m f yielding interrupt override budget]
  change settle id rest (evaluateNative root m (countOp f) yielding table) = _
  rw [registration_start root table m (countOp f) yielding scope a fin current]
  rfl

/-- Trace emission changes no outstanding control credit.
Consumer: `registration_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem emit_credits (q : List Nat) (m : NativeMachine) (events : List ReleaseTrace.Event) :
    machineCredits q (m.emit events) = machineCredits q m := by
  cases events <;> rfl

/-- An actual keyed fiber update changes only the selected fiber's control credit.
Consumer: `registration_loop_funded`; distinct IDs come from the existing Guard invariant. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem update_credits (q : List Nat) (m : NativeMachine) (old next : Fiber)
    (unique : (m.fibers.map RunFiber.id).Nodup) (member : old ∈ m.fibers)
    (same : next.id = old.id) :
    machineCredits q (m.update next) + fiberCredits q old =
      machineCredits q m + fiberCredits q next := by
  have changed := Machine.ControlWeights.replace_sum RunFiber.id (fiberCredits q) old next same
    m.fibers unique member
  simp only [machineCredits, RunMachine.update]
  omega

/-- The registration command preserves the concrete funded configuration, including its pending suffix.
Consumer: `Workers.Assertions.registration_custody_command`, then the registration clause of `releases_step`.
This proves one actual command under its selected-fiber and budget premises. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registration_loop_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (rest : List Command)
    (q : List Nat) (scope : Nat) (a : Val) (fin : FinName)
    (unique : (m.fibers.map RunFiber.id).Nodup) (funded : Funded q m (.loop id yielding :: rest))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) rest).2 := by
  rw [registration_loop root table m id f yielding rest scope a fin found current interrupt override budget]
  let next : Fiber := { countOp f with frame := { f.frame with
    current := .sync (.op (.scopeAdd scope fin))
    stack := .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: f.frame.stack } }
  let events : List ReleaseTrace.Event :=
    [.frame f.id (.pushed (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)))]
  change Funded q ((m.emit events).update next) (.loop id yielding :: rest)
  have member : f ∈ (m.emit events).fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q (m.emit events) f next unique member rfl
  rw [emit_credits] at changed
  have frame := registration_frame_credits q (countOp f) scope a fin current
  change fiberCredits q next = fiberCredits q f + credit q fin at frame
  have registered : ((m.emit events).update next).trace.countP (ReleaseTrace.registeredAt q) =
      m.trace.countP (ReleaseTrace.registeredAt q) + credit q fin := by
    change (m.emit events).trace.countP (ReleaseTrace.registeredAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    simp only [events, List.countP_cons, List.countP_nil, Nat.zero_add]
    cases fin <;> rfl
  have starts : ((m.emit events).update next).trace.countP (ReleaseTrace.releaseAt q) =
      m.trace.countP (ReleaseTrace.releaseAt q) := by
    change (m.emit events).trace.countP (ReleaseTrace.releaseAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.releaseAt q) + 0 = _
    exact Nat.add_zero _
  unfold Funded at funded ⊢
  rw [registered, starts]
  simp only [List.map_cons, commandCredits, List.sum_cons, Nat.zero_add] at funded ⊢
  omega

/-- Starting the foreign release spends exactly one active credit and leaves lower callbacks intact.
Consumer: `release_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_frame_credits (q : List Nat) (root : NativeEff) (f : Fiber) (c : Capture) (exit : ExitV)
    (current : f.frame.current = suspendBodyAt root (.store (.foreign c exit))) :
    fiberCredits q { f with frame := { f.frame with
      current := .withFiber .getCtx
      stack := .onSuccess (.withFiber .getCtx) (.releaseUnder (Point.ofCapture c) c.ctx exit) :: f.frame.stack } } +
      credit q (.foreign c) = fiberCredits q f := by
  unfold fiberCredits
  rw [current]
  change _ = currentCredits q (.onSuccess (.withFiber .getCtx)
      (.releaseUnder (Point.ofCapture c) c.ctx exit)) +
    stackCredits q (.onSuccess (.withFiber .getCtx) (.releaseUnder (Point.ofCapture c) c.ctx exit)) f.frame.stack + _
  rw [stack_before_push]
  simp only [currentCredits, stackCredits, futureCredits, Nat.zero_add]
  change _ + credit q (.foreign c) = credit q (.foreign c) + _ + _
  omega

/-- The actual release-start loop keeps its unfinished commands and updated fiber.
Consumer: `release_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_loop (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (rest : List Command) (c : Capture) (exit : ExitV)
    (found : m.fiber? id = some f)
    (current : f.frame.current = suspendBodyAt root (.store (.foreign c exit)))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    driveStep (evaluator := evaluatorFor root table) (interpOf root table) m (.loop id yielding) rest =
      ((m.emit [.frame f.id (.pushed (.onSuccess (.withFiber .getCtx)
        (.releaseUnder (Point.ofCapture c) c.ctx exit)))]).update
        { countOp f with frame := { f.frame with
          current := .withFiber .getCtx
          stack := .onSuccess (.withFiber .getCtx) (.releaseUnder (Point.ofCapture c) c.ctx exit) :: f.frame.stack } },
       .loop id yielding :: rest) := by
  rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table) _ m id f yielding rest found]
  rw [Machine.ControlSteps.iteration_below_budget (evaluator := evaluatorFor root table)
    _ m f yielding interrupt override budget]
  change settle id rest (evaluateNative root m (countOp f) yielding table) = _
  rw [ReleaseCustody.release_start root table m (countOp f) yielding c exit current]
  rfl

/-- The counted release command spends an existing control credit in the concrete configuration.
Consumer: `Workers.Assertions.release_custody_command`, then the release-start clause of `releases_step`.
The available-credit premise of `ReleaseCustody.release_loop_debit` is discharged by this assertion. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_loop_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (rest : List Command)
    (q : List Nat) (c : Capture) (exit : ExitV)
    (unique : (m.fibers.map RunFiber.id).Nodup) (funded : Funded q m (.loop id yielding :: rest))
    (found : m.fiber? id = some f)
    (current : f.frame.current = suspendBodyAt root (.store (.foreign c exit)))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) rest).2 := by
  rw [release_loop root table m id f yielding rest c exit found current interrupt override budget]
  let next : Fiber := { countOp f with frame := { f.frame with
    current := .withFiber .getCtx
    stack := .onSuccess (.withFiber .getCtx) (.releaseUnder (Point.ofCapture c) c.ctx exit) :: f.frame.stack } }
  let events : List ReleaseTrace.Event := [.frame f.id (.pushed (.onSuccess (.withFiber .getCtx)
    (.releaseUnder (Point.ofCapture c) c.ctx exit)))]
  change Funded q ((m.emit events).update next) (.loop id yielding :: rest)
  have member : f ∈ (m.emit events).fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q (m.emit events) f next unique member rfl
  rw [emit_credits] at changed
  have frame := release_frame_credits q root (countOp f) c exit current
  change fiberCredits q next + credit q (.foreign c) = fiberCredits q f at frame
  have registered : ((m.emit events).update next).trace.countP (ReleaseTrace.registeredAt q) =
      m.trace.countP (ReleaseTrace.registeredAt q) := by
    change (m.emit events).trace.countP (ReleaseTrace.registeredAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.registeredAt q) + 0 = _
    exact Nat.add_zero _
  have starts : ((m.emit events).update next).trace.countP (ReleaseTrace.releaseAt q) =
      m.trace.countP (ReleaseTrace.releaseAt q) + credit q (.foreign c) := by
    change (m.emit events).trace.countP (ReleaseTrace.releaseAt q) = _
    have raw := ReleaseCustody.release_start_count root table m (countOp f) yielding q c exit current
    rw [ReleaseCustody.release_start root table m (countOp f) yielding c exit current] at raw
    exact raw
  unfold Funded at funded ⊢
  rw [registered, starts]
  simp only [List.map_cons, commandCredits, List.sum_cons, Nat.zero_add] at funded ⊢
  omega

/-- The concrete custody assertion supplies the original trace debit observation.
Consumer: `Workers.Assertions.release_custody_command`. It establishes no preservation by itself. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem Funded.read {q : List Nat} {m : NativeMachine} {pending : List Command}
    (held : Funded q m pending) :
    m.trace.countP (ReleaseTrace.releaseAt q) ≤ m.trace.countP (ReleaseTrace.registeredAt q) := by
  unfold Funded at held
  omega

/-- Source store rows mint no foreign registration; consumer: compile-load custody setup. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem source_op_credits (q : List Nat) (op : NativeOp) (env : List Val) (v : Val)
    (actual : SyncOp) (answer : NativeOp.syncOpOf op env v = some actual) :
    opCredits q actual = 0 := by
  unfold NativeOp.syncOpOf at answer
  split at answer <;> cases answer <;> rfl

/-- Asynchronous source rows carry no already-registered release.
Consumer: `compile_credits`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem async_route_credits (q : List Nat) (op : NativeOp) (request : Term) (p : Point) :
    currentCredits q (asyncRoute op request p) = 0 := by
  unfold asyncRoute
  split
  · split <;> rfl
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

/-- Source compilation starts with no outstanding foreign custody.
Consumer: the load premise of the candidate configuration invariant. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem compile_credits (q : List Nat) (e : NativeEff) (p : Point) :
    currentCredits q (compileEff e p) = 0 := by
  fun_induction compileEff e p <;>
    simp (config := { failIfUnchanged := false }) only
      [currentCredits, frontier, badShape, async_route_credits, updateContextAt]
  case case13 p n hf op request hk v hv operation hop _ _ _ =>
    simp only [hk, hv, hop, currentCredits]
    exact source_op_credits q op p.env v operation hop
  case case14 p n hf op request hk v hv hop _ _ _ =>
    simp only [hk, hv, hop, currentCredits]
  case case15 p n hf op request hk hv _ _ _ =>
    rw [hk, hv]
    rfl
  case case16 p n hf op request hk _ _ _ =>
    rw [hk]
    exact async_route_credits q op request p
  case case17 p n hf op request hk _ _ _ =>
    rw [hk]
    rfl
  case case18 | case20 | case21 | case22 | case23 | case25 | case43 | case45 => assumption
  case case31 p n hf fiber mode id hv exit hx => cases exit <;> rfl

/-- The actual native load owns no outstanding foreign credit.
Consumer: the candidate command-lift load premise. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem load_credits (q : List Nat) (root : NativeEff) (fuel : Nat) :
    machineCredits q (Api.load root fuel) = 0 := by
  simp only [machineCredits, Api.load, RunMachine.empty, Stores.empty, List.map_nil,
    List.map_cons, List.sum_nil, List.sum_cons, fiberCredits, RunFiber.make, FrameFiber.start,
    Dispatcher.empty, stackCredits, Api.compile, compile, compile_credits, Nat.add_zero]

/-- The concrete command assertion holds on the actual initial machine and empty pending list.
Consumer: `Workers.Assertions.load_custody`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem load_funded (q : List Nat) (root : NativeEff) (fuel : Nat) :
    Funded q (Api.load root fuel) [] := by
  unfold Funded
  rw [load_credits]
  change 0 + 0 + 0 ≤ 0
  exact Nat.le_refl 0

end Effect4.Program.ReleaseCustody.Control

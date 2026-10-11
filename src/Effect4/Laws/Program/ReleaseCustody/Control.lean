import Effect4.Laws.Program.ReleaseCustody.Names
import Effect4.Laws.Machine.ControlWeights

/-!
# Registration custody at control positions

Concept: scope-lifetime-finalization, R11, at most once per registration counted by identity.
Question: helpers of `Workers.Assertions.releases_step` and the queue release debit claim.
Reach: the source compile, initial machine and named native registration command.
The projection distinguishes active code from remaining stack callbacks and close iterators.
It includes scope entries, queued resume code, unlaunched race programs and pending resume commands.
It does not establish whole-command preservation, source-use uniqueness, progress or host behavior.
The residual-name projection includes foreign finalizers hidden by stored program wrappers.
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
  | .onSuccessConst _ next => responseCredits q fin next
  | _ => credit q fin

def nameCredits (q : List Nat) : EffName → Nat
  | .afterScopeAdd _ fin => credit q fin
  | .store name => Names.contCredits q name
  | _ => 0

def currentCredits (q : List Nat) : NCode → Nat
  | .sync (.op op) => opCredits q op
  | .sync (.store (.op op)) => opCredits q op
  | .suspend (.store (.foreign c _)) => credit q (.foreign c)
  | .suspend (.store (.body program)) => Names.progCredits q program
  | .withFiber (.store (.act action)) => Names.actionCredits q action
  | .withFiber (.store (.body program)) => Names.progCredits q program
  | .withFiber (.store (.foreign c _)) => credit q (.foreign c)
  | .iterator (.store (.closeSeq order _ _)) _ => orderCredits q order
  | .onSuccess body (.afterScopeAdd _ fin) =>
      (currentCredits q body + responseCredits q fin body) - credit q fin
  | .onSuccess body (.releaseUnder p _ _) => currentCredits q body + if p.path == q then 1 else 0
  | .onSuccess body (.store name) => currentCredits q body + Names.contCredits q name
  | .onSuccess body _ => currentCredits q body
  | .onSuccessConst body next => currentCredits q body + currentCredits q next
  | .onFailure body name => currentCredits q body + nameCredits q name
  | .onSuccessAndFailure body a e => currentCredits q body + nameCredits q a + nameCredits q e
  | .exitFrame body => currentCredits q body
  | .onExit body (.store (.finalizerName fin)) _ => currentCredits q body + credit q fin
  | .onExit body _ _ => currentCredits q body
  | _ => 0

def futureCredits (q : List Nat) : NCode → Nat
  | .onSuccess _ (.afterScopeAdd _ fin) => credit q fin
  | .onSuccess _ (.store name) => Names.contCredits q name
  | .onFailure _ name => nameCredits q name
  | .onSuccessAndFailure _ a e => nameCredits q a + nameCredits q e
  | .onSuccessConst _ next => currentCredits q next
  | .iterator (.store (.closeSeq order _ _)) _ => orderCredits q order
  | .onExit _ (.store (.finalizerName fin)) _ => credit q fin
  | _ => 0

mutual
  def stackCredits (q : List Nat) (active : NCode) : List NCode → Nat
    | .onSuccessConst _ next :: rest => currentCredits q next + stackCredits q next rest
    | .onSuccess _ (.afterScopeAdd _ fin) :: rest => responseCredits q fin active + stackCap q rest
    | head :: rest => futureCredits q head + stackCap q rest
    | [] => 0

  def stackCap (q : List Nat) : List NCode → Nat
    | .onSuccessConst _ next :: rest => currentCredits q next + stackCredits q next rest
    | .onSuccess _ (.afterScopeAdd _ fin) :: rest => credit q fin + stackCap q rest
    | head :: rest => futureCredits q head + stackCap q rest
    | [] => 0
end

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
    stackCredits q (.onSuccess body name) stack = stackCap q stack := by
  unfold stackCredits
  split <;> simp only [stackCap, responseCredits]

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

/-- A closed scope returns its exit and retains the registration credit in the actual callback.
Consumer: `scope_add_closed_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_add_closed_frame_credits (q : List Nat) (f : Fiber) (scope : Nat)
    (a : Val) (fin : FinName) (exit : ExitV) (lower : List NCode)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (stack : f.frame.stack =
      .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: lower) :
    fiberCredits q { countOp f with frame := { f.frame with current := .success (reifyExitVal exit) } } =
      fiberCredits q f := by
  simp only [fiberCredits, current, stack, currentCredits, opCredits, stackCredits,
    responseCredits, ite_true, Nat.zero_add, after_add_exit_credit, countOp]

/-- The actual closed-scope addition preserves custody in its closing-exit response.
Consumer: the closed scope-add clause of `Workers.Assertions.releases_step`.
The unchanged scope store needs no scope-key uniqueness premise. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_add_closed_loop_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (rest : List Command)
    (q : List Nat) (scope : Nat) (entry : ScopeEntry) (a : Val) (fin : FinName)
    (exit : ExitV) (lower : List NCode)
    (unique : (m.fibers.map RunFiber.id).Nodup) (funded : Funded q m (.loop id yielding :: rest))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (stack : f.frame.stack =
      .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: lower)
    (entryFound : m.state.scopes.entryAt scope = some entry)
    (closing : entry.scope.closingExit? = some exit)
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) rest).2 := by
  have answer : syncOpStep (.scopeAdd scope fin) m.state = some (m.state, reifyExitVal exit) := by
    simp only [syncOpStep, entryFound, closing]
  rw [ControlSteps.loop_sync_op root table m id f (.scopeAdd scope fin) m.state
    (reifyExitVal exit) yielding rest found current interrupt override budget answer]
  let next : Fiber := { countOp f with frame := { f.frame with current := .success (reifyExitVal exit) } }
  change Funded q (m.update next) ([.drainDue, .deliver id yielding] ++ rest)
  have member : f ∈ m.fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q m f next unique member rfl
  have frame := scope_add_closed_frame_credits q f scope a fin exit lower current stack
  change fiberCredits q next = fiberCredits q f at frame
  unfold Funded at funded ⊢
  change m.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (m.update next) +
      (([Cmd.drainDue, Cmd.deliver id yielding] ++ rest).map (commandCredits q)).sum ≤
    m.trace.countP (ReleaseTrace.registeredAt q)
  simp only [List.cons_append, List.nil_append, List.map_cons, commandCredits, List.sum_cons,
    Nat.zero_add] at funded ⊢
  omega

/-- Unit response removes the active credit after the actual scope owns it.
Consumer: `scope_add_open_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_add_open_frame_credits (q : List Nat) (f : Fiber) (scope : Nat)
    (a : Val) (fin : FinName) (lower : List NCode)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (stack : f.frame.stack =
      .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: lower) :
    fiberCredits q { countOp f with frame := { f.frame with current := .success Val.unit } } +
      credit q fin = fiberCredits q f := by
  simp only [fiberCredits, current, stack, currentCredits, opCredits, stackCredits,
    responseCredits, ite_true, Nat.zero_add, after_add_unit_credit, countOp]
  omega

/-- Replacing one actual scope entry changes only its selected weight.
Consumer: `scope_add_open_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_update_credits (q : List Nat) (m : NativeMachine) (entry : ScopeEntry)
    (nextScope : ScopeV) (nextName : Nat)
    (unique : (m.state.scopes.entries.map ScopeEntry.key).Nodup)
    (member : entry ∈ m.state.scopes.entries) :
    machineCredits q { m with state := { m.state with
      scopes := m.state.scopes.setEntry { entry with scope := nextScope }
      nextName := nextName } } + scopeCredits q entry.scope =
      machineCredits q m + scopeCredits q nextScope := by
  have changed := Machine.ControlWeights.replace_sum ScopeEntry.key
    (fun e => scopeCredits q e.scope) entry { entry with scope := nextScope } rfl
    m.state.scopes.entries unique member
  change ((m.state.scopes.entries.map fun e => if e.key = entry.key then
      { entry with scope := nextScope } else e).map fun e => scopeCredits q e.scope).sum +
      scopeCredits q entry.scope =
    (m.state.scopes.entries.map fun e => scopeCredits q e.scope).sum + scopeCredits q nextScope at changed
  simp only [machineCredits, ScopeStore.setEntry]
  omega

/-- The actual open-scope command transfers its active credit into the selected scope entry.
Consumer: the open scope-add clause of `Workers.Assertions.releases_step`.
Distinct scope-entry keys and fresh finalizer keys remain explicit store premises. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_add_open_loop_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (rest : List Command)
    (q : List Nat) (scope : Nat) (entry : ScopeEntry) (a : Val) (fin : FinName)
    (lower : List NCode)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (scopeUnique : (m.state.scopes.entries.map ScopeEntry.key).Nodup)
    (funded : Funded q m (.loop id yielding :: rest))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (stack : f.frame.stack =
      .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: lower)
    (entryFound : m.state.scopes.entryAt scope = some entry)
    (opened : entry.scope.isClosed = false) (fresh : m.state.nextName ∉ entry.scope.finalizerKeys)
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) rest).2 := by
  let state : Stores := { m.state with
    scopes := m.state.scopes.setEntry { entry with scope := entry.scope.addUnsafe m.state.nextName fin }
    nextName := m.state.nextName + 1 }
  have closing : entry.scope.closingExit? = none :=
    ScopeState.closingExit_of_not_closed entry.scope.state opened
  have answer : syncOpStep (.scopeAdd scope fin) m.state = some (state, Val.unit) := by
    simp only [syncOpStep, entryFound, closing]
    rfl
  rw [ControlSteps.loop_sync_op root table m id f (.scopeAdd scope fin) state Val.unit
    yielding rest found current interrupt override budget answer]
  let next : Fiber := { countOp f with frame := { f.frame with current := .success Val.unit } }
  change Funded q (({ m with state }).update next) ([.drainDue, .deliver id yielding] ++ rest)
  have entryMember : entry ∈ m.state.scopes.entries := List.mem_of_find?_eq_some entryFound
  have scopeChanged := scope_update_credits q m entry
    (entry.scope.addUnsafe m.state.nextName fin) (m.state.nextName + 1) scopeUnique entryMember
  have registeredCredit := add_open q entry.scope m.state.nextName fin opened fresh
  have member : f ∈ ({ m with state } : NativeMachine).fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q { m with state } f next unique member rfl
  have frame := scope_add_open_frame_credits q f scope a fin lower current stack
  change fiberCredits q next + credit q fin = fiberCredits q f at frame
  change machineCredits q { m with state } + scopeCredits q entry.scope =
    machineCredits q m + scopeCredits q (entry.scope.addUnsafe m.state.nextName fin) at scopeChanged
  unfold Funded at funded ⊢
  change m.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (({ m with state }).update next) +
      (([Cmd.drainDue, Cmd.deliver id yielding] ++ rest).map (commandCredits q)).sum ≤
    m.trace.countP (ReleaseTrace.registeredAt q)
  simp only [List.cons_append, List.nil_append, List.map_cons, commandCredits, List.sum_cons,
    Nat.zero_add] at funded ⊢
  omega

/-- A forced yield above scope-add reserves its saved operation once, including the lower callback.
Consumer: the yield-injection clause of `Execution.command_custody`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_add_yield_frame_credits (q : List Nat) (f : Fiber) (scope : Nat)
    (a : Val) (fin : FinName) (lower : List NCode)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (stack : f.frame.stack = .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: lower) :
    fiberCredits q { countOp f with
      frame := { f.frame with
        current := .yieldNowWith 0
        stack := .onSuccessConst (.yieldNowWith 0) (.sync (.op (.scopeAdd scope fin))) :: f.frame.stack }
      yieldOverride := none } = fiberCredits q f := by
  unfold fiberCredits
  rw [current, stack]
  simp only [countOp, currentCredits, opCredits, stackCredits, responseCredits,
    ite_true, Nat.zero_add]

/-- Any actual scope-add response owns at most its reserved finalizer credit.
Consumer: `stack_credits_bounded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem response_credits_bounded (q : List Nat) (fin : FinName) (body : NCode) :
    responseCredits q fin body ≤ credit q fin := by
  fun_induction responseCredits q fin body
  case case1 value =>
    unfold afterAddCredits
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.le_refl _
      · exact Nat.zero_le _
  case case2 => exact Nat.zero_le _
  case case3 => exact Nat.zero_le _
  case case4 => exact Nat.le_refl _
  case case5 => assumption
  case case6 => exact Nat.le_refl _

/-- The active response cannot exceed the lower stack's reserved credit.
Consumer: the actual scope-close command custody clause. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_credits_bounded (q : List Nat) (body : NCode) (stack : List NCode) :
    stackCredits q body stack ≤ stackCap q stack := by
  unfold stackCredits
  split
  · simp only [stackCap]
    exact Nat.le_refl _
  · simp only [stackCap]
    exact Nat.add_le_add_right (response_credits_bounded q _ body) _
  · simp only [stackCap]
    exact Nat.le_refl _
  · exact Nat.le_refl _

/-- A with-fiber action retains every lower stack reservation before it returns a program.
Consumer: the actual scope-close command custody clause. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_before_action (q : List Nat) (action : EffThunk) (stack : List NCode) :
    stackCredits q (.withFiber action) stack = stackCap q stack := by
  unfold stackCredits
  split <;> simp only [stackCap, responseCredits]

/-- The store's finalizer program owns exactly its source-indexed foreign credit.
Consumer: the actual scope-close command custody clause. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem fin_program_credits (q : List Nat) (fin : FinName) (exit : ExitV) :
    currentCredits q (embed (finProgram fin exit)) = credit q fin := by
  fun_cases finProgram fin exit <;>
    simp only [embed, currentCredits, opCredits, credit, foreignAt, Bool.false_eq_true,
      if_false, Names.actionCredits, Names.contCredits, Nat.zero_add]

/-- Interpreting every stored program constructor retains its residual credits.
Consumer: the stored-suspension command custody clause of `Workers.Assertions.releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem prog_of_credits (q : List Nat) (program : ProgName) :
    currentCredits q (embed (progOf program)) = Names.progCredits q program := by
  fun_induction progOf program <;>
    simp (config := { failIfUnchanged := false }) only [embed, currentCredits,
      Names.progCredits, Names.contCredits, Names.actionCredits, opCredits, fin_program_credits,
      Nat.zero_add, Nat.add_zero]
  case case3 =>
    rename_i op
    cases op <;> rfl
  case case13 =>
    rename_i body fin flag ih
    exact congrArg (fun n => n + credit q fin) ih
  case case14 =>
    rename_i first second ih
    exact congrArg (fun n => n + Names.progCredits q second) ih

/-- A suspended stored program retains every lower callback reservation.
Consumer: `stored_suspend_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_before_suspend (q : List Nat) (thunk : EffThunk) (stack : List NCode) :
    stackCredits q (.suspend thunk) stack = stackCap q stack := by
  unfold stackCredits
  split <;> simp only [stackCap, responseCredits]

/-- The native suspension opens the stored program without emitting an event or changing its stack.
Consumer: `stored_suspend_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stored_suspend_start (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : Fiber) (yielding : Bool) (program : ProgName)
    (current : f.frame.current = .suspend (.store (.body program))) :
    evaluateNative root m f yielding table =
      ⟨m, { f with frame := { f.frame with current := embed (progOf program) } },
        yielding, .continue_, []⟩ := by
  have park : (interpAt root m.completedExits table).parkOf
      (.suspend (.store (.body program))) = none := rfl
  have frame : f.frame.step (interpAt root m.completedExits table).toPrimInterp =
      (.running { f.frame with current := embed (progOf program) }, []) := by
    unfold FrameFiber.step
    rw [current]
    rfl
  simp only [evaluateNative, evaluatePrim, current, park, evaluatePrim.stepFrame, frame]
  rfl

/-- Opening any stored program transfers its residual credit to the actual active code.
Consumer: the stored-suspension command clause of `Workers.Assertions.releases_step`.
The selected fiber, operation budget and pending suffix are those of the actual command. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stored_suspend_loop_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (pending : List Command)
    (q : List Nat) (program : ProgName)
    (unique : (m.fibers.map RunFiber.id).Nodup) (funded : Funded q m (.loop id yielding :: pending))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .suspend (.store (.body program)))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) pending).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) pending).2 := by
  let next : Fiber := { countOp f with frame := { f.frame with current := embed (progOf program) } }
  have stepped : driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) pending = (m.update next, .loop id yielding :: pending) := by
    rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table) _ m id f yielding pending found]
    rw [Machine.ControlSteps.iteration_below_budget (evaluator := evaluatorFor root table)
      _ m f yielding interrupt override budget]
    change settle id pending (evaluateNative root m (countOp f) yielding table) = _
    rw [stored_suspend_start root table m (countOp f) yielding program current]
    rfl
  rw [stepped]
  change Funded q (m.update next) (.loop id yielding :: pending)
  have bounded := stack_credits_bounded q (embed (progOf program)) f.frame.stack
  have frame : fiberCredits q next ≤ fiberCredits q f := by
    unfold fiberCredits
    simp only [next, countOp]
    rw [current, stack_before_suspend, prog_of_credits]
    change Names.progCredits q program + stackCredits q (embed (progOf program)) f.frame.stack + _ ≤
      Names.progCredits q program + stackCap q f.frame.stack + _
    omega
  have member : f ∈ m.fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q m f next unique member rfl
  unfold Funded at funded ⊢
  change m.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (m.update next) + _ ≤
    m.trace.countP (ReleaseTrace.registeredAt q)
  omega

/-- A stored mask transfers the named body's credit through the actual restoring frame.
Consumer: `stored_mask_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stored_mask_frame_credits (q : List Nat) (f : Fiber) (program : ProgName)
    (current : f.frame.current = .withFiber (.store (.act (.setInterruptible program false)))) :
    fiberCredits q { countOp f with
      frame := { f.frame.uninterruptible with current := embed (progOf program) } } ≤ fiberCredits q f := by
  have bounded := stack_credits_bounded q (embed (progOf program)) f.frame.stack
  unfold fiberCredits
  rw [current, stack_before_action]
  simp only [currentCredits, Names.actionCredits]
  cases masked : f.frame.interruptible
  · simp only [FrameFiber.uninterruptible, masked, Bool.false_eq_true, if_false, countOp, prog_of_credits]
    omega
  · simp only [FrameFiber.uninterruptible, masked, if_true, countOp, prog_of_credits,
      stackCredits, futureCredits, Nat.zero_add]
    exact Nat.le_refl _

/-- The actual native mask installs the named body beneath its existing restore frame.
Consumer: `stored_mask_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stored_mask_start (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : Fiber) (yielding : Bool) (program : ProgName)
    (current : f.frame.current = .withFiber (.store (.act (.setInterruptible program false)))) :
    evaluateNative root m f yielding table =
      ⟨m, { f with frame := { f.frame.uninterruptible with current := embed (progOf program) } },
        yielding, .continue_, []⟩ := by
  have park : (interpAt root m.completedExits table).parkOf
      (.withFiber (.store (.act (.setInterruptible program false)))) = none := rfl
  have action : (interpAt root m.completedExits table).withFiberOf
      (.store (.act (.setInterruptible program false))) =
      some (.setInterruptible (embed (progOf program)) false) := rfl
  simp only [evaluateNative, current, evaluatePrim, park, action, evaluatePrim.withFiber]

/-- Entering the actual stored mask preserves cleanup funding, including its restoring frame.
Consumer: the masking command clause of `Workers.Assertions.releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stored_mask_loop_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (pending : List Command)
    (q : List Nat) (program : ProgName)
    (unique : (m.fibers.map RunFiber.id).Nodup) (funded : Funded q m (.loop id yielding :: pending))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .withFiber (.store (.act (.setInterruptible program false))))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) pending).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) pending).2 := by
  let next : Fiber := { countOp f with
    frame := { f.frame.uninterruptible with current := embed (progOf program) } }
  have stepped : driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) pending = (m.update next, .loop id yielding :: pending) := by
    rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table) _ m id f yielding pending found]
    rw [Machine.ControlSteps.iteration_below_budget (evaluator := evaluatorFor root table)
      _ m f yielding interrupt override budget]
    change settle id pending (evaluateNative root m (countOp f) yielding table) = _
    rw [stored_mask_start root table m (countOp f) yielding program current]
    rfl
  rw [stepped]
  change Funded q (m.update next) (.loop id yielding :: pending)
  have frame : fiberCredits q next ≤ fiberCredits q f := stored_mask_frame_credits q f program current
  have member : f ∈ m.fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q m f next unique member rfl
  unfold Funded at funded ⊢
  change m.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (m.update next) + _ ≤
    m.trace.countP (ReleaseTrace.registeredAt q)
  omega

/-- The actual close result owns the exact captured close order, including singleton and empty cases.
Consumer: `scope_close_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem close_program_credits (q : List Nat) (strategy : FinalizerStrategy)
    (order : List FinName) (exit : ExitV) :
    currentCredits q (embed (match order with
      | [] => Prim.success Val.unit
      | [fin] => Prim.onSuccessConst (finProgram fin exit) (Prim.success Val.unit)
      | _ => Prim.suspend (Thunk.body (ProgName.closeWalk strategy order exit)))) =
      orderCredits q order := by
  cases order with
  | nil => rfl
  | cons fin rest =>
    cases rest with
    | nil =>
      simp only [embed, currentCredits, fin_program_credits, Nat.add_zero, orderCredits,
        List.countP_cons, List.countP_nil, Nat.zero_add, credit]
    | cons second rest => rfl

/-- An actual scope-close action returns the state and program before the selected loop continues.
Consumer: `scope_close_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_close_start (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : Fiber) (yielding : Bool) (scope : Nat) (exit : ExitV) (state : Stores) (program : Program)
    (current : f.frame.current = .withFiber (.closeScope scope exit))
    (answer : storesCloseScope scope exit f.frame.interruptible m.state = some (state, program)) :
    evaluateNative root m f yielding table =
      ⟨{ m with state }, { f with frame := { f.frame with current := embed program } },
        yielding, .continue_, []⟩ := by
  have park : (interpAt root m.completedExits table).parkOf (.withFiber (.closeScope scope exit)) = none := rfl
  have action : (interpAt root m.completedExits table).withFiberOf (.closeScope scope exit) =
      some (.closeScope scope exit) := rfl
  have close : (interpAt root m.completedExits table).closeScope scope exit f.frame.interruptible f.id m.state =
      some (state, embed program) := by
    change (storesCloseScope scope exit f.frame.interruptible m.state).map _ = _
    rw [answer]
    rfl
  simp only [evaluateNative, current, evaluatePrim, park, action, evaluatePrim.withFiber, close]

/-- Closing an actual scope transfers the entry's credits into its returned close program.
Consumer: the scope-close command clause of `Workers.Assertions.releases_step`.
The clause keeps the actual state-first close and pending command suffix. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_close_loop_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (rest : List Command)
    (q : List Nat) (scope : Nat) (entry : ScopeEntry) (exit : ExitV)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (scopeUnique : (m.state.scopes.entries.map ScopeEntry.key).Nodup)
    (funded : Funded q m (.loop id yielding :: rest))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .withFiber (.closeScope scope exit))
    (entryFound : m.state.scopes.entryAt scope = some entry)
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) rest).2 := by
  let state : Stores := { m.state with
    scopes := m.state.scopes.setEntry { entry with scope := Scope.closeState entry.scope exit } }
  let program : Program := match entry.scope.closeOrder with
    | [] => Prim.success Val.unit
    | [fin] => Prim.onSuccessConst (finProgram fin exit) (Prim.success Val.unit)
    | _ => Prim.suspend (Thunk.body (ProgName.closeWalk entry.scope.strategy entry.scope.closeOrder exit))
  have answer : storesCloseScope scope exit f.frame.interruptible m.state = some (state, program) := by
    simp only [storesCloseScope, scopeCloseSnapshot, entryFound, Option.pure_def,
      ScopeStore.closeState]
    rfl
  have loop : driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) rest =
      (({ m with state }).update
        { countOp f with frame := { f.frame with current := embed program } }, .loop id yielding :: rest) := by
    rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table)
      _ m id f yielding rest found]
    rw [Machine.ControlSteps.iteration_below_budget (evaluator := evaluatorFor root table)
      _ m f yielding interrupt override budget]
    change settle id rest (evaluateNative root m (countOp f) yielding table) = _
    rw [scope_close_start root table m (countOp f) yielding scope exit state program current answer]
    rfl
  rw [loop]
  let next : Fiber := { countOp f with frame := { f.frame with current := embed program } }
  change Funded q (({ m with state }).update next) (.loop id yielding :: rest)
  obtain ⟨closed, order⟩ := close_scope q entry.scope exit
  have returned := close_program_credits q entry.scope.strategy entry.scope.closeOrder exit
  change currentCredits q (embed program) = orderCredits q entry.scope.closeOrder at returned
  rw [order] at returned
  have bounded := stack_credits_bounded q (embed program) f.frame.stack
  have frame : fiberCredits q next ≤ fiberCredits q f + scopeCredits q entry.scope := by
    unfold fiberCredits
    simp only [next, countOp]
    rw [current]
    change currentCredits q (embed program) + stackCredits q (embed program) f.frame.stack + _ ≤
      0 + stackCredits q (.withFiber (.closeScope scope exit)) f.frame.stack + _ + scopeCredits q entry.scope
    rw [stack_before_action, returned]
    omega
  have entryMember : entry ∈ m.state.scopes.entries := List.mem_of_find?_eq_some entryFound
  have scopeChanged := scope_update_credits q m entry (Scope.closeState entry.scope exit)
    m.state.nextName scopeUnique entryMember
  change machineCredits q { m with state } + scopeCredits q entry.scope =
    machineCredits q m + scopeCredits q (Scope.closeState entry.scope exit) at scopeChanged
  rw [closed, Nat.add_zero] at scopeChanged
  have member : f ∈ ({ m with state } : NativeMachine).fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q { m with state } f next unique member rfl
  unfold Funded at funded ⊢
  change m.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (({ m with state }).update next) +
      ((Cmd.loop id yielding :: rest).map (commandCredits q)).sum ≤
    m.trace.countP (ReleaseTrace.registeredAt q)
  simp only [List.map_cons, commandCredits, List.sum_cons, Nat.zero_add] at funded ⊢
  omega

/-- An active close iterator retains every lower callback reservation.
Consumer: `close_seq_loop_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_before_iterator (q : List Nat) (name : EffName) (cursor : Val) (stack : List NCode) :
    stackCredits q (.iterator name cursor) stack = stackCap q stack := by
  unfold stackCredits
  split <;> simp only [stackCap, responseCredits]

/-- The actual iterator command transfers head credit into the selected finalizer and tail credit into its frame.
Consumer: the close-iterator command clause of `Workers.Assertions.releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem close_seq_loop_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (pending : List Command)
    (q : List Nat) (fin : FinName) (rest : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (cursor : Val)
    (unique : (m.fibers.map RunFiber.id).Nodup) (funded : Funded q m (.loop id yielding :: pending))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .iterator (.store (.closeSeq (fin :: rest) exit captured)) cursor)
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) pending).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) pending).2 := by
  let next : Fiber := { countOp f with frame := { f.frame with
    current := .exitFrame (embed (finProgram fin exit))
    stack := .iterator (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) cursor :: f.frame.stack } }
  let events : List ReleaseTrace.Event := [.frame f.id (.pushed
    (.iterator (.store (.closeSeq rest exit (captured ++ reasonsOfVal cursor))) cursor))]
  have loop : driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id yielding) pending = ((m.emit events).update next, .loop id yielding :: pending) := by
    rw [Machine.ControlSteps.loop_of_iteration (evaluator := evaluatorFor root table)
      _ m id f yielding pending found]
    rw [Machine.ControlSteps.iteration_below_budget (evaluator := evaluatorFor root table)
      _ m f yielding interrupt override budget]
    change settle id pending (evaluateNative root m (countOp f) yielding table) = _
    rw [close_seq_start root table m (countOp f) yielding fin rest exit captured cursor current]
    rfl
  rw [loop]
  change Funded q ((m.emit events).update next) (.loop id yielding :: pending)
  have order : orderCredits q (fin :: rest) = credit q fin + orderCredits q rest := by
    simp only [orderCredits, List.countP_cons, credit, Nat.add_comm]
  have frame : fiberCredits q next = fiberCredits q f := by
    unfold fiberCredits
    simp only [next, countOp]
    rw [current, stack_before_iterator]
    simp only [currentCredits, fin_program_credits, stackCredits, futureCredits]
    rw [order]
    omega
  have member : f ∈ (m.emit events).fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q (m.emit events) f next unique member rfl
  rw [emit_credits] at changed
  have starts : ((m.emit events).update next).trace.countP (ReleaseTrace.releaseAt q) =
      m.trace.countP (ReleaseTrace.releaseAt q) := by
    change (m.emit events).trace.countP (ReleaseTrace.releaseAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.releaseAt q) + 0 = _
    exact Nat.add_zero _
  have registered : ((m.emit events).update next).trace.countP (ReleaseTrace.registeredAt q) =
      m.trace.countP (ReleaseTrace.registeredAt q) := by
    change (m.emit events).trace.countP (ReleaseTrace.registeredAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.registeredAt q) + 0 = _
    exact Nat.add_zero _
  unfold Funded at funded ⊢
  rw [starts, registered]
  simp only [List.map_cons, commandCredits, List.sum_cons, Nat.zero_add] at funded ⊢
  omega

/-- The actual scope-add callback carries exactly its response-dependent credit into the next program.
Consumer: `after_add_deliver_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem after_add_code_credits (root : NativeEff) (q : List Nat) (a : Val) (fin : FinName) (value : Val) :
    currentCredits q (contAOf root (.afterScopeAdd a fin) value) = afterAddCredits q fin value := by
  change currentCredits q (if value = Val.unit then .success a else
    match exitOfVal value with
    | some exit => .onSuccess (embed (finProgram fin exit)) (.constant a)
    | none => badShape) = _
  unfold afterAddCredits
  split
  · rfl
  · cases answer : exitOfVal value with
    | none => rfl
    | some exit => simp only [Option.isSome_some, if_true, currentCredits, fin_program_credits]

/-- Delivering the actual scope-add response pops only its own callback.
Consumer: `after_add_deliver_funded`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem after_add_start (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : Fiber) (yielding : Bool) (scope : Nat) (a : Val) (fin : FinName)
    (value : Val) (lower : List NCode)
    (current : f.frame.current = .success value)
    (stack : f.frame.stack = .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: lower)
    (interrupt : f.frame.deferredInterrupt = false) :
    evaluateNative root m f yielding table =
      ⟨m.emit [.frame f.id (.popped (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)))],
       { f with frame := { f.frame with
         current := contAOf root (.afterScopeAdd a fin) value
         stack := lower
         deferredInterrupt := false } }, yielding, .continue_, []⟩ := by
  let template : NCode := .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)
  have pop : f.frame.getCont .contA false =
      ⟨.frame template, [template], [.popped template],
        { f.frame with stack := lower, deferredInterrupt := false }, none⟩ := by
    unfold FrameFiber.getCont
    rw [interrupt, stack]
    change FrameFiber.popFrom .contA false (template :: lower)
      { f.frame with stack := [], deferredInterrupt := false } none = _
    rfl
  have frame : f.frame.step (interpAt root m.completedExits).toPrimInterp =
      (.running { f.frame with
        current := contAOf root (.afterScopeAdd a fin) value
        stack := lower
        deferredInterrupt := false }, [.popped template]) := by
    unfold FrameFiber.step
    rw [current]
    unfold FrameFiber.resumeValue
    rw [pop]
    rfl
  have park : (interpAt root m.completedExits).parkOf (.success value) = none := rfl
  simp only [evaluateNative, exitScoped, evaluatePrim, current, park, evaluatePrim.finalizerOr, pop,
    evaluatePrim.stepFrame, frame]
  rfl

/-- The actual delivery command spends the scope-add response credit on exactly its returned callback program.
Consumer: the scope-add delivery clause of `Workers.Assertions.releases_step`.
The lower callbacks remain reserved; the actual row table and pending suffix stay fixed. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem after_add_deliver_funded (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (f : Fiber) (yielding : Bool) (pending : List Command)
    (q : List Nat) (scope : Nat) (a : Val) (fin : FinName) (value : Val) (lower : List NCode)
    (unique : (m.fibers.map RunFiber.id).Nodup) (funded : Funded q m (.deliver id yielding :: pending))
    (found : m.fiber? id = some f) (current : f.frame.current = .success value)
    (stack : f.frame.stack = .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: lower)
    (interrupt : f.frame.deferredInterrupt = false) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.deliver id yielding) pending).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.deliver id yielding) pending).2 := by
  let next : Fiber := { f with frame := { f.frame with
    current := contAOf root (.afterScopeAdd a fin) value
    stack := lower
    deferredInterrupt := false } }
  let events : List ReleaseTrace.Event := [.frame f.id
    (.popped (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)))]
  have delivered : driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.deliver id yielding) pending = ((m.emit events).update next, .loop id yielding :: pending) := by
    simp only [driveStep, found]
    change settle id pending (evaluateNative root m f yielding table) = _
    rw [after_add_start root table m f yielding scope a fin value lower current stack interrupt]
    rfl
  rw [delivered]
  change Funded q ((m.emit events).update next) (.loop id yielding :: pending)
  have bounded := stack_credits_bounded q (contAOf root (.afterScopeAdd a fin) value) lower
  have frame : fiberCredits q next ≤ fiberCredits q f := by
    unfold fiberCredits
    simp only [next]
    rw [current, stack]
    simp only [currentCredits, stackCredits, responseCredits]
    change currentCredits q (contAOf root (.afterScopeAdd a fin) value) +
        stackCredits q (contAOf root (.afterScopeAdd a fin) value) lower + _ ≤
      0 + (afterAddCredits q fin value + stackCap q lower) + _
    rw [after_add_code_credits]
    omega
  have member : f ∈ (m.emit events).fibers := List.mem_of_find?_eq_some found
  have changed := update_credits q (m.emit events) f next unique member rfl
  rw [emit_credits] at changed
  have starts : ((m.emit events).update next).trace.countP (ReleaseTrace.releaseAt q) =
      m.trace.countP (ReleaseTrace.releaseAt q) := by
    change (m.emit events).trace.countP (ReleaseTrace.releaseAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.releaseAt q) + 0 = _
    exact Nat.add_zero _
  have registered : ((m.emit events).update next).trace.countP (ReleaseTrace.registeredAt q) =
      m.trace.countP (ReleaseTrace.registeredAt q) := by
    change (m.emit events).trace.countP (ReleaseTrace.registeredAt q) = _
    rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.registeredAt q) + 0 = _
    exact Nat.add_zero _
  unfold Funded at funded ⊢
  rw [starts, registered]
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

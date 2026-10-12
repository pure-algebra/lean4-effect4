import Effect4.Laws.Program.CompileInduction
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
Consumer: the native registration debit and command closure. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registration_template (q : List Nat) (scope : Nat) (a : Val) (fin : FinName) :
    currentCredits q (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)) = 0 := by
  simp only [currentCredits, opCredits, responseCredits, ite_true, Nat.add_zero, Nat.sub_self]

/-- Active non-exit code keeps every lower callback reservation.
Consumer: the native registration debit and command closure. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_before_push (q : List Nat) (body : NCode) (name : EffName) (stack : List NCode) :
    stackCredits q (.onSuccess body name) stack = stackCap q stack := by
  unfold stackCredits
  split <;> simp only [stackCap, responseCredits]

/-- Trace emission changes no outstanding control credit.
Consumer: the native registration debit and command closure. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem emit_credits (q : List Nat) (m : NativeMachine) (events : List ReleaseTrace.Event) :
    machineCredits q (m.emit events) = machineCredits q m := by
  cases events <;> rfl

/-- An actual keyed fiber update changes only the selected fiber's control credit.
Consumer: native command closure; distinct IDs come from the existing Guard invariant. -/
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
Consumer: the native suspension debit and command closure. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_before_suspend (q : List Nat) (thunk : EffThunk) (stack : List NCode) :
    stackCredits q (.suspend thunk) stack = stackCap q stack := by
  unfold stackCredits
  split <;> simp only [stackCap, responseCredits]

/-- The actual close result owns the exact captured close order, including singleton and empty cases.
Consumer: the native scope-close debit and command closure. -/
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

/-- An active close iterator retains every lower callback reservation.
Consumer: the sequential close-iterator debit and command closure. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stack_before_iterator (q : List Nat) (name : EffName) (cursor : Val) (stack : List NCode) :
    stackCredits q (.iterator name cursor) stack = stackCap q stack := by
  unfold stackCredits
  split <;> simp only [stackCap, responseCredits]

/-- The actual scope-add callback carries exactly its response-dependent credit into the next program.
Consumer: the scope-add response debit and command closure. -/
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

/-- The concrete custody assertion supplies the original trace debit observation.
Consumer: `Workers.Assertions.releases_step`, through complete command preservation and admitted history. -/
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
Consumer: `load_credits`, then `Execution.load`. -/
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
  case case18 | case20 | case21 | case22 | case23 | case25 | case46 | case48 => assumption
  case case42 =>
    rename_i exit _ _
    cases exit <;> rfl
  case case31 p n hf fiber mode id hv exit hx => cases exit <;> rfl

/-- The actual native load owns no outstanding foreign credit.
Consumer: `load_funded`, then `Execution.load`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem load_credits (q : List Nat) (root : NativeEff) (fuel : Nat) :
    machineCredits q (Api.load root fuel) = 0 := by
  simp only [machineCredits, Api.load, RunMachine.empty, Stores.empty, List.map_nil,
    List.map_cons, List.sum_nil, List.sum_cons, fiberCredits, RunFiber.make, FrameFiber.start,
    Dispatcher.empty, stackCredits, Api.compile, compile, compile_credits, Nat.add_zero]

/-- The concrete command assertion holds on the actual initial machine and empty pending list.
Consumer: `Execution.load`, then the admitted-history custody theorem. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem load_funded (q : List Nat) (root : NativeEff) (fuel : Nat) :
    Funded q (Api.load root fuel) [] := by
  unfold Funded
  rw [load_credits]
  change 0 + 0 + 0 ≤ 0
  exact Nat.le_refl 0

end Effect4.Program.ReleaseCustody.Control

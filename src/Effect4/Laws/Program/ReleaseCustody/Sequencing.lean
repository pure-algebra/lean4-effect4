import Effect4.Laws.Program.ReleaseCustody.FrameDebit

/-!
Concept: scope-lifetime-finalization, R11.
Question: narrow callback sequencing serves Execution.history and Workers.Assertions.releases_step.
Reach: existing native code and frame lists; no second source syntax or execution carrier.
Limit: this predicate alone proves neither command custody nor native history closure.
Unlock: parked-response and forced-yield cuts for the release-custody invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Sequencing
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Pop (Frame)

def NoAdd (frames : List NCode) : Prop :=
  ∀ frame ∈ frames, ∀ body a fin, frame ≠ .onSuccess body (.afterScopeAdd a fin)

/-- A saved forced yield runs a yield, an admitted response, or another forced-yield wrapper. -/
inductive YieldPhase : NCode → Prop
  | value (value : Val) : YieldPhase (.success value)
  | cause (cause : CauseV) : YieldPhase (.failure cause)
  | refGet (cell : RefKey) : YieldPhase (.sync (.store (.op (.refGet cell))))
  | yielding (priority : Nat) : YieldPhase (.yieldNowWith priority)
  | forced (priority : Nat) {next : NCode} (held : YieldPhase next) :
      YieldPhase (.onSuccessConst (.yieldNowWith priority) next)

/-- Scope-add owns its callback until the matching operation or its response is consumed. -/
inductive AddPhase (fin : FinName) : NCode → Prop
  | operation (scope : Nat) : AddPhase fin (.sync (.op (.scopeAdd scope fin)))
  | value (value : Val) : AddPhase fin (.success value)
  | cause (cause : CauseV) : AddPhase fin (.failure cause)
  | forced (priority : Nat) {next : NCode} (held : AddPhase fin next) :
      AddPhase fin (.onSuccessConst (.yieldNowWith priority) next)

/-- Existing masks and forced-yield constants transport the one pending callback.
Ordinary source continuations remain below it. -/
inductive Kept : NCode → List NCode → Prop
  | clean (active : NCode) (frames : List NCode) (held : NoAdd frames) : Kept active frames
  | add (active : NCode) (scope : Nat) (a : Val) (fin : FinName) (rest : List NCode)
      (tail : NoAdd rest) (held : AddPhase fin active) :
      Kept active (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: rest)
  | constant (priority : Nat) {active next : NCode} {rest : List NCode}
      (phase : YieldPhase active) (held : Kept next rest) :
      Kept active (.onSuccessConst (.yieldNowWith priority) next :: rest)

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noAdd_empty : NoAdd [] := by
  intro frame mem
  exact False.elim (List.not_mem_nil mem)

/-- The compiled root starts before any scope callback is pushed. Consumer: history load. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem load (root : NativeEff) (fuel : Nat) : Kept (Program.compile root fuel) [] :=
  .clean _ _ noAdd_empty

/-- Frames without the callback have their full response-independent credits.
Consumer: the actual raw-yield parked response below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noAdd_full (q : List Nat) (active : NCode) (frames : List NCode) (held : NoAdd frames) :
    stackCredits q active frames = stackCap q frames := by
  unfold stackCredits
  split
  · rfl
  · rename_i body a fin rest
    exact False.elim (held _ List.mem_cons_self body a fin rfl)
  · simp only [stackCap]
  · rfl

/-- Interruption replaces the current primitive without opening a pending callback.
Consumer: native runloop-top and interrupt-record cuts. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem interrupt {active : NCode} {frames : List NCode} (held : Kept active frames) (cause : CauseV) :
    Kept (.failure cause) frames := by
  induction held with
  | clean active frames held => exact .clean _ _ held
  | add active scope a fin rest tail phase => exact .add _ scope a fin rest tail (.cause cause)
  | constant priority phase held ih => exact .constant priority (.cause cause) held

/-- The injected constant retains the exact callback phase of its saved primitive.
Consumer: actual forced-yield wrapper construction. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem forced_wrapper {active : NCode} {frames : List NCode} (held : Kept active frames)
    (priority : Nat) : Kept (.onSuccessConst (.yieldNowWith priority) active) frames := by
  induction held with
  | clean active frames held => exact .clean _ _ held
  | add active scope a fin rest tail phase => exact .add _ scope a fin rest tail (.forced priority phase)
  | constant saved phase held ih => exact .constant saved (.forced priority phase) held

/-- Pushing the injected yield leaves its saved callback phase under the constant.
Consumer: actual forced-yield primitive push. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem forced_push {active : NCode} {frames : List NCode} (held : Kept active frames) (priority : Nat) :
    Kept (.yieldNowWith priority) (.onSuccessConst (.yieldNowWith priority) active :: frames) :=
  .constant priority (.yielding priority) held

/-- A direct raw yield cannot replace the operation immediately above scope-add's callback.
Consumer: the parked response fullness theorem below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem raw_yield_excluded (priority scope : Nat) (a : Val) (fin : FinName) (rest : List NCode) :
    ¬ Kept (.yieldNowWith priority)
      (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: rest) := by
  intro held
  cases held
  case clean missing => exact missing _ List.mem_cons_self _ _ _ rfl
  case add phase tail => cases phase

/-- The real raw-yield evaluator replaces current with unit before parking.
The sequence clause proves that this change retains full saved credits.
Consumer: native parked-full preservation in Execution.history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem yield_response_full (q : List Nat) (priority : Nat) (frames : List NCode)
    (held : Kept (.yieldNowWith priority) frames) (value : Val) :
    stackCredits q (.success value) frames = stackCap q frames := by
  cases held
  case clean missing => exact noAdd_full q _ _ missing
  case add tail phase => cases phase
  case constant => rfl

/-- Parked stacks retain their credits through every answer and interruption.
The saved constant keeps the precise callback sequence below its own yield. -/
inductive StableFrames : List NCode → Prop
  | clean (frames : List NCode) (held : NoAdd frames) : StableFrames frames
  | constant (priority : Nat) {next : NCode} {rest : List NCode} (held : Kept next rest) :
      StableFrames (.onSuccessConst (.yieldNowWith priority) next :: rest)

/-- Stability is response independent, unlike equality at one parked value.
Consumer: actual resume debit and interrupt replacement. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stable_full (q : List Nat) (active : NCode) {frames : List NCode}
    (held : StableFrames frames) : stackCredits q active frames = stackCap q frames := by
  cases held with
  | clean frames held => exact noAdd_full q active frames held
  | constant priority held => rfl

/-- A parked success retains the saved forced-yield sequence.
Consumer: native resume command and synchronous async responses. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stable_value {frames : List NCode} (held : StableFrames frames) (value : Val) :
    Kept (.success value) frames := by
  induction held with
  | clean frames held => exact .clean _ _ held
  | constant priority held => exact .constant priority (.value value) held

/-- A parked failure retains the sequence even when interruption replaces its answer.
Consumer: native interrupt-record and resume command. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stable_cause {frames : List NCode} (held : StableFrames frames) (cause : CauseV) :
    Kept (.failure cause) frames := by
  induction held with
  | clean frames held => exact .clean _ _ held
  | constant priority held => exact .constant priority (.cause cause) held

/-- A delayed reference answer retains the saved forced-yield sequence.
Consumer: native completion resumes in the actual admitted command history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem stable_refGet {frames : List NCode} (held : StableFrames frames) (cell : RefKey) :
    Kept (.sync (.store (.op (.refGet cell)))) frames := by
  cases held with
  | clean frames missing => exact .clean _ _ missing
  | constant priority saved => exact .constant priority (.refGet cell) saved

/-- The real yield producer supplies a stable stack before replacing current with unit.
Consumer: evaluatePrim's raw and injected yield parks. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem yield_stable {priority : Nat} {frames : List NCode}
    (held : Kept (.yieldNowWith priority) frames) : StableFrames frames := by
  cases held
  case clean missing => exact .clean _ missing
  case add tail phase => cases phase
  case constant priority next rest held phase => exact .constant priority held

/-- A mask is not a scope-add callback. Consumer: opaque primitive sequencing. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noAdd_mask (flag : Bool) {frames : List NCode} (held : NoAdd frames) :
    NoAdd (.setInterruptible flag :: frames) := by
  intro frame present body a fin same
  cases List.mem_cons.mp present with
  | inl head => cases head; cases same
  | inr tail => exact held frame tail body a fin same

/-- Other current primitives cannot own the transient scope-add response.
Consumer: native async, suspend and action producers of parked stacks. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem opaque_noAdd {active : NCode} {frames : List NCode} (held : Kept active frames)
    (notAdd : ∀ fin, ¬ AddPhase fin active) (notYield : ¬ YieldPhase active) : NoAdd frames := by
  induction held with
  | clean active frames held => exact held
  | add active scope a fin rest tail phase => exact False.elim (notAdd fin phase)
  | constant priority phase held ih => exact False.elim (notYield phase)

/-- The async producer enters with no pending scope-add callback.
Consumer: evaluatePrim's controller/cancel frame and async park. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem async_noAdd (register : EffName) (signal : Bool) (cancel : Option EffName)
    {frames : List NCode} (held : Kept (.async register signal cancel) frames) : NoAdd frames := by
  apply opaque_noAdd held
  · intro fin phase; cases phase
  · intro phase; cases phase

/-- The actual injected constant resumes precisely the saved callback sequence.
Consumer: the success response after a forced-yield park. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem saved_resume (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (fiber : Frame) (priority : Nat) (next : NCode)
    (value : Val) (provided : Option ExitV) (deferred : fiber.deferredInterrupt = false)
    (held : Kept next fiber.stack) :
    ∃ returned : Frame,
      ({fiber with stack := .onSuccessConst (.yieldNowWith priority) next :: fiber.stack}).resumeValue
        (interpAt root completed table).toPrimInterp value provided =
          (.running returned, [.popped (.onSuccessConst (.yieldNowWith priority) next)]) ∧
      Kept returned.current returned.stack := by
  refine ⟨{fiber with current := next}, ?_, held⟩
  exact FrameFiber.resumeValue_onSuccessConst _ _ _ _ _ _ deferred

/-- Any actual scope-add result retains the active callback until its pop.
Consumer: native sync-state success and failure cuts. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem value_response {active : NCode} {frames : List NCode} (held : Kept active frames)
    (value : Val) : Kept (.success value) frames := by
  induction held with
  | clean active frames held => exact .clean _ _ held
  | add active scope a fin rest tail phase => exact .add _ scope a fin rest tail (.value value)
  | constant priority phase held ih => exact .constant priority (.value value) held

/-- The actual registration push installs its matching transient callback.
Consumer: evaluateNative's registration command. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registration_step (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (fiber : Frame) (scope : Nat) (a : Val) (fin : FinName)
    (held : Kept (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)) fiber.stack) :
    ∃ returned : Frame,
      ({fiber with current := .onSuccess (.sync (EffThunk.op (.scopeAdd scope fin))) (EffName.afterScopeAdd a fin)} : Frame).step
        (interpAt root completed table).toPrimInterp =
          (.running returned, [.pushed (.onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin))]) ∧
      Kept returned.current returned.stack := by
  have missing := opaque_noAdd held (by intro fin phase; cases phase) (by intro phase; cases phase)
  refine ⟨{fiber with
    current := .sync (.op (.scopeAdd scope fin))
    stack := .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: fiber.stack}, rfl, ?_⟩
  exact .add _ scope a fin fiber.stack missing (.operation scope)

/-- The actual yield producer parks with a stable stack and its unit response.
Consumer: raw and forced yield command preservation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem yield_producer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Fiber) (yielding : Bool) (priority : Nat)
    (held : Kept (.yieldNowWith priority) fiber.frame.stack) :
    let next := (FiberAction.yieldNow (interpOf root table) m fiber yielding priority).fiber
    StableFrames next.frame.stack ∧ Kept next.frame.current next.frame.stack := by
  have stable := yield_stable held
  exact ⟨stable, stable_value stable _⟩

/-- A stable parked stack cannot create saved credit when its answer changes.
Consumer: the actual successful resume command below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resume_frame_debit (q : List Nat) (fiber : Fiber) (answer : NCode)
    (held : StableFrames fiber.frame.stack) :
    fiberCredits q {fiber with frame := {fiber.frame with current := answer}} ≤
      fiberCredits q fiber + currentCredits q answer := by
  unfold fiberCredits
  dsimp only
  rw [stable_full q answer held, stable_full q fiber.frame.current held]
  omega

/-- The actual token-matched resume consumes its queued answer credit.
Consumer: the native admitted-command history obligation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem resume_command (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (token : Nat) (answer : NCode) (rest : List Command) (fiber : Fiber)
    (found : m.fiber? id = some fiber) (parked : fiber.parked = .withGuard token)
    (unique : (m.fibers.map RunFiber.id).Nodup) (stable : StableFrames fiber.frame.stack)
    (funded : Funded q m (.resume id token answer :: rest)) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.resume id token answer) rest).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.resume id token answer) rest).2 := by
  let next : Fiber := {fiber with
    parked := .notParked
    pending := fiber.pending.filter (fun p => p.token ≠ token)
    frame := {fiber.frame with current := answer}}
  have run : driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.resume id token answer) rest =
      ((m.update next).emit [.resumedWith id token answer], .evaluate id :: rest) := by
    simp only [driveStep, found, parked, FiberCore.answerWith]
    rfl
  rw [run]
  have changed := update_credits q m fiber next unique (List.mem_of_find?_eq_some found) rfl
  have debit := resume_frame_debit q fiber answer stable
  change fiberCredits q next ≤ fiberCredits q fiber + currentCredits q answer at debit
  have starts : ((m.update next).emit [.resumedWith id token answer]).trace.countP
      (ReleaseTrace.releaseAt q) = m.trace.countP (ReleaseTrace.releaseAt q) := by
    rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.releaseAt q) + 0 = _
    exact Nat.add_zero _
  have registered : ((m.update next).emit [.resumedWith id token answer]).trace.countP
      (ReleaseTrace.registeredAt q) = m.trace.countP (ReleaseTrace.registeredAt q) := by
    rw [RunMachine.emit_trace, List.countP_append]
    change m.trace.countP (ReleaseTrace.registeredAt q) + 0 = _
    exact Nat.add_zero _
  unfold Funded at funded ⊢
  rw [starts, registered, emit_credits]
  simp only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add] at funded ⊢
  omega

/-- The native acquired callback creates exactly the correlated registration template.
Consumer: registration_step; no lexical or value-typing premise is assumed here. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem acquired_registration (root : NativeEff) (point : Point) (ctx : Ctx) (scope : Nat) (a : Val) :
    contAOf root (.acquired point ctx scope) a =
      .onSuccess (.sync (.op (.scopeAdd scope (.foreign (point.capture a ctx)))))
        (.afterScopeAdd a (.foreign (point.capture a ctx))) := rfl

/-- An async cancel frame is not a scope-add callback.
Consumer: the actual async park's stable-stack producer. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem noAdd_asyncFinalizer (name : EffName) {frames : List NCode} (held : NoAdd frames) :
    NoAdd (.asyncFinalizer name :: frames) := by
  intro frame present body a fin same
  cases List.mem_cons.mp present with
  | inl head => cases head; cases same
  | inr tail => exact held frame tail body a fin same

/-- Both immediate and parked async branches retain stable saved frames.
Consumer: native async resume command preservation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem async_producer (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (fiber : Fiber) (yielding : Bool) (register : EffName) (signal : Bool) (cancel : Option EffName)
    (held : Kept (.async register signal cancel) fiber.frame.stack) :
    let next := (evaluatePrim (interpOf root table) m
      {fiber with frame := {fiber.frame with current := .async register signal cancel}} yielding).fiber
    StableFrames next.frame.stack ∧ Kept next.frame.current next.frame.stack := by
  have missing := async_noAdd register signal cancel held
  unfold evaluatePrim
  dsimp only
  split
  · exact ⟨.clean _ missing, .clean _ _ missing⟩
  · split
    · have kept := noAdd_asyncFinalizer
        ((interpOf root table).cancelName (cancel.getD (interpOf root table).abortName) fiber.id m.nextToken) missing
      exact ⟨.clean _ kept, .clean _ _ kept⟩
    · exact ⟨.clean _ missing, .clean _ _ missing⟩

end Effect4.Program.ReleaseCustody.Sequencing

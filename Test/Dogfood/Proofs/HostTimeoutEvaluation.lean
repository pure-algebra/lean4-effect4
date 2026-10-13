import Test.Dogfood.Proofs.HostTimeoutFrames

/-!
# Timeout values through native finalizer evaluation

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the command assertion over reached native runs.
The evaluator follows the actual answering frame and finalizer program.
A finalizer returns unit; its restoring continuation keeps the saved exit's value class.
These transfer laws establish neither reached-machine closure nor progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutEvaluation
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSlots HostTimeoutFlow HostTimeoutNative HostTimeoutFrames Effect4.Laws.Auto

abbrev NativeFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev NativeMachine := RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NativeIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

def exitDemand : ExitV → Effect4.Arm
  | .success _ => .contA
  | .failure _ => .contE
def exitSkip : ExitV → Bool
  | .success _ => false
  | .failure _ => true
def exitCause : ExitV → Option CauseV
  | .success _ => none
  | .failure cause => some cause

/-- Delivery may change a failure's cause but retains every successful value. -/
theorem delivered_exit {B : List Val} {kind : Kind} {exit : ExitV}
    (good : ExitAt B kind exit) (pop : NativePop) : ExitAt B kind (pop.deliveredExit exit) := by
  cases exit <;> exact good

/-- The native restoring name discards cleanup's successful value. -/
theorem restore_callback {B : List Val} {kind : Kind} {exit : ExitV}
    (good : ExitAt B kind exit) (view : View) (value : Val) :
    CodeAt B kind ((interpreter view).contA (.restore exit) value) := by
  exact exit_code good

/-- A native merge continuation answers only the combined failure. -/
theorem merge_callback {B : List Val} {exit : ExitV} (view : View) (cause : CauseV) :
    CodeAt B .unit ((interpreter view).contE (.merge exit) cause) := by
  cases exit <;> exact .head (.failure .unit _)

/-- Actual native finalizer code restores the original successful value after unit cleanup. -/
theorem finalizer_code {B : List Val} {kind : Kind} {exit : ExitV} {program : NCode}
    (view : View) (good : ExitAt B kind exit) (cleanup : CodeAt B .unit program) :
    CodeAt B kind (finalizerCode (interpreter view) exit program) := by
  apply CodeAt.head
  refine HeadAt.onSuccess .unit kind _ (.restore exit) ?_ ?_
  · cases exit with
    | success value => exact cleanup
    | failure cause => exact .head (.onFailure .unit program (.merge (.failure cause)) cleanup
        (fun view cause => merge_callback view cause))
  · exact fun view value _ => restore_callback good view value

/-- An evaluator iteration either retains its ordered frame or finishes at its expected class. -/
def IterKind (B : List Val) (kind : Kind) (iter : NativeIter) : Prop :=
  match iter.outcome with
  | .finished exit => ExitAt B kind exit ∧ CodeAt B kind iter.fiber.frame.current ∧ Masks iter.fiber.frame.stack
  | _ => FrameKind B kind iter.fiber.frame

/-- Delegating the primitive frame step retains the successful output class. -/
theorem step_frame {B : List Val} {kind : Kind} (view : View) (machine : NativeMachine)
    (fiber : NativeFiber) (yielding : Bool) (owned : FrameKind B kind fiber.frame)
    (regular : (interpreter view).parkOf fiber.frame.current = none)
    (ordinary : ∀ thunk, fiber.frame.current = .withFiber thunk →
      (interpreter view).withFiberOf thunk = none) :
    IterKind B kind (evaluatePrim.stepFrame (interpreter view) machine fiber yielding) := by
  have good := HostTimeoutFrames.step_frame view fiber.frame owned regular ordinary
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  cases pair : fiber.frame.step (interpreter view).toPrimInterp with
  | mk next events =>
    cases next with
    | running frame => simpa only [pair, StepKind, IterKind] using good
    | finished exit =>
      have terminal := finished_frame view fiber.frame owned regular ordinary exit
        (congrArg Prod.fst pair)
      have answer : ExitAt B kind exit := by simpa only [pair, StepKind] using good
      simpa only [pair, IterKind] using And.intro answer terminal

/-- Every evaluator result keeps its stored frame, including terminal frames awaiting publication. -/
theorem IterKind.frame {B : List Val} {kind : Kind} {iter : NativeIter}
    (owned : IterKind B kind iter) : FrameKind B kind iter.fiber.frame := by
  cases outcome : iter.outcome
  all_goals simp only [IterKind, outcome] at owned
  case finished exit => exact ⟨kind, owned.2.1, masks_stack kind owned.2.2⟩
  all_goals exact owned

/-- Selecting an actual source finalizer retains the saved exit and its ordered suffix. -/
theorem finalizer_answer {B : List Val} {input output : Kind} (view : View)
    (fiber : NativeFrame) (exit : ExitV) (body : NCode) (name : EffName) (flag : Bool)
    (good : ExitAt B input exit) (stack : StackAt B input output fiber.stack)
    (chosen : (fiber.getCont
      (exitDemand exit)
      (exitSkip exit)
      (exitCause exit)).answer =
        .frame (.onExit body name flag)) :
    ∃ point middle, name = .fin point ∧
      let pop := fiber.getCont
        (exitDemand exit)
        (exitSkip exit)
        (exitCause exit)
      ExitAt B middle (pop.deliveredExit exit) ∧ StackAt B middle output pop.fiber.stack ∧
        ∀ program, (interpreter view).finalizerProgram name (pop.deliveredExit exit) = some program →
          CodeAt B .unit program := by
  cases exit with
  | success value =>
    simp only [exitDemand, exitSkip, exitCause] at chosen
    have owned := get_cont fiber .contA (.inl rfl) false none (fun _ => rfl) stack
    simp only [PopAt, chosen] at owned
    obtain ⟨incoming, middle, saved, rest, same⟩ := owned
    cases saved with
    | exit kind body point flag callback =>
      have equal := same trivial
      subst incoming
      exact ⟨point, input, rfl, good, rest, fun program found => callback view _ program good found⟩
  | failure cause =>
    simp only [exitDemand, exitSkip, exitCause] at chosen
    have owned := get_cont fiber .contE (.inr rfl) true (some cause) (fun h => by cases h) stack
    simp only [PopAt, chosen] at owned
    obtain ⟨incoming, middle, saved, rest, _⟩ := owned
    cases saved with
    | exit kind body point flag callback =>
      exact ⟨point, incoming, rfl, trivial, rest, fun program found => callback view (.failure ((fiber.getCont .contE true (some cause)).carriedCause.getD cause)) program trivial found⟩

/-- Actual finalizer evaluation consumes the selected source cleanup and restores its saved exit. -/
theorem finalizer_or {B : List Val} {input output : Kind} (view : View)
    (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool) (exit : ExitV)
    (current : fiber.frame.current = Prim.ofExit exit) (good : ExitAt B input exit)
    (stack : StackAt B input output fiber.frame.stack) :
    IterKind B output (evaluatePrim.finalizerOr (interpreter view) machine fiber yielding exit) := by
  have fallback : IterKind B output
      (evaluatePrim.stepFrame (interpreter view) machine fiber yielding) := by
    apply step_frame view machine fiber yielding ⟨input, current ▸ exit_code good, stack⟩
    · cases exit <;> rw [current] <;> rfl
    · intro thunk eq
      cases exit <;> rw [current] at eq <;> cases eq
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · rename_i body name flag answer
    obtain ⟨point, middle, equal, saved, rest, cleanup⟩ :=
      finalizer_answer view fiber.frame exit body name flag good stack (by cases exit <;> exact answer)
    split
    · rename_i program selected
      cases exit <;> exact ⟨middle, finalizer_code view saved (cleanup program selected), rest⟩
    · exact fallback
  · exact fallback

/-- A native race cleanup action returns unit. -/
theorem cancel_race_code (B : List Val) (race : Nat) :
    CodeAt B .unit (.withFiber (.store (.act (.cancelRace race)))) := by
  exact .head (.action .unit _ (fun _ => .cancelRace race) (fun _ => rfl)
    (fun _ => .cancelRace race))

/-- Removing native countdown observers returns unit. -/
theorem drop_observers_code (B : List Val) (token : Nat) :
    CodeAt B .unit (.withFiber (.store (.act (.dropObservers token)))) := by
  exact .head (.action .unit _ (fun _ => .dropObservers token) (fun _ => rfl)
    (fun _ => .dropObservers token))

/-- The three cancellation names created by Timeout's native parks. -/
inductive CancelAt : EffName → Prop
  | sleep (waiter : FiberId) (token : Nat) : CancelAt (.withWaiter (.store .cancelSleep) waiter token)
  | race (race : Nat) (waiter : FiberId) (token : Nat) :
      CancelAt (.withWaiter (.store (.cancelRace race)) waiter token)
  | park (waiter : FiberId) (token : Nat) : CancelAt (.withWaiter (.store .cancelPark) waiter token)

/-- Every actual Timeout park cleanup has a unit successful result. -/
theorem cancel_program {B : List Val} {name : EffName} (owned : CancelAt name) :
    CodeAt B .unit (cancelProgramOf name) := by
  cases owned with
  | sleep waiter token =>
    apply CodeAt.head
    refine HeadAt.sync .unit _ ?_ (fun _ => .unit) (.cancel waiter token)
    intro view state next value found
    change some ({state with timers := state.timers.cancel waiter token}, Val.unit) = some (next, value) at found
    cases found
    exact .unit
  | race race waiter token => exact cancel_race_code B race
  | park waiter token => exact drop_observers_code B token

/-- Interrupt cleanup returns to the exact failure at every saved result class. -/
theorem cancel_then_failure {B : List Val} {name : EffName} (owned : CancelAt name)
    (kind : Kind) (view : View) (cause : CauseV) :
    CodeAt B kind ((interpreter view).cancelThenFail name cause) := by
  exact .head (.onSuccess .unit kind _ (.reFail cause) (cancel_program owned)
    (fun _ _ _ => .head (.failure kind cause)))

/-- The embedded store restore name keeps the race's accepted exit. -/
theorem store_restore_callback {B : List Val} {kind : Kind} {exit : ExitV}
    (good : ExitAt B kind exit) (view : View) (value : Val) :
    CodeAt B kind ((interpreter view).contA (.store (.restore exit)) value) := by
  cases exit with
  | success value => exact .head (.success good)
  | failure cause => exact .head (.failure kind cause)

/-- The actual masked race cancellation answers unit before its restoring continuation. -/
theorem masked_race_code (B : List Val) (race : Nat) : CodeAt B .unit
    (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false)))) := by
  exact .head (.action .unit _ (fun _ => .setInterruptible _ false) (fun _ => rfl)
    (fun _ => .mask .unit _ false (cancel_race_code B race)))

/-- Native race settlement keeps its accepted successful body through cancellation. -/
theorem race_settle {B : List Val} {kind : Kind} {exit : ExitV}
    (good : ExitAt B kind exit) (view : View) (race : Nat) (cleanup : Bool) :
    CodeAt B kind ((interpreter view).raceSettle race cleanup exit) := by
  cases cleanup with
  | false => cases exit <;> exact exit_code good
  | true => exact .head (.onSuccess .unit kind _ (.store (.restore exit))
      (masked_race_code B race) (fun view value _ => store_restore_callback good view value))

/-- Native cancellation's await discards the collected exits and returns unit. -/
theorem await_void (B : List Val) (view : View) (targets : List FiberId) :
    CodeAt B .unit (asVoidCode (interpreter view)
      ((interpreter view).parkCode (.awaitAll targets))) := by
  exact .head (.onSuccess .any .unit _ (.restore (.success .unit))
    (.head (.awaitPark targets)) (fun view value _ => restore_callback (kind := .unit) (exit := .success .unit) ValueAt.unit view value))

/-- A forced yield keeps the entire code as its constant successful continuation. -/
theorem yield_before {B : List Val} {kind : Kind} {code : NCode}
    (owned : CodeAt B kind code) :
    CodeAt B kind (.onSuccessConst (.yieldNowWith 0) code) := by
  exact .head (.constant kind _ code (.head (.yieldNow 0)) owned)

/-- Pushing a native park's interruption cleanup keeps the ordered success chain. -/
theorem push_cancel {B : List Val} {input output : Kind} {frame : NativeFrame}
    {name : EffName} (good : CodeAt B input frame.current)
    (stack : StackAt B input output frame.stack) (cancel : CancelAt name) :
    FrameKind B output {frame with stack := .asyncFinalizer name :: frame.stack} := by
  exact ⟨input, good, .cons (.cancel input name (cancel_then_failure cancel input)) stack⟩

/-- A synchronous timeout head changes only refs or removes its sleep registration. -/
theorem sync_state_shape {thunk : EffThunk} (allowed : SyncAt thunk) (view : View)
    (state next : Stores) (value : Val)
    (found : (interpreter view).syncState thunk state = some (next, value)) :
    (∃ refs, next = {state with refs}) ∨
      ∃ waiter token, next = {state with timers := state.timers.cancel waiter token} := by
  cases allowed with
  | make initial outer =>
    change (refStep (.refMake initial) state.refs).map (fun step => ({state with refs := step.2}, step.1)) =
      some (next, value) at found
    obtain ⟨step, _, equal⟩ := Option.map_eq_some_iff.mp found
    exact .inl ⟨step.2, (congrArg Prod.fst equal).symm⟩
  | get cell =>
    change (refStep (.refGet cell) state.refs).map (fun step => ({state with refs := step.2}, step.1)) =
      some (next, value) at found
    obtain ⟨step, _, equal⟩ := Option.map_eq_some_iff.mp found
    exact .inl ⟨step.2, (congrArg Prod.fst equal).symm⟩
  | update cell term env outer =>
    change (refStep (.refUpdate cell term env) state.refs).map (fun step => ({state with refs := step.2}, step.1)) =
      some (next, value) at found
    obtain ⟨step, _, equal⟩ := Option.map_eq_some_iff.mp found
    exact .inl ⟨step.2, (congrArg Prod.fst equal).symm⟩
  | cancel waiter token =>
    change some ({state with timers := state.timers.cancel waiter token}, Val.unit) = some (next, value) at found
    exact .inr ⟨waiter, token, (congrArg Prod.fst (Option.some.inj found)).symm⟩

/-- The actual synchronous write keeps every timeout cell's number or list outer shape. -/
theorem sync_state_outer {thunk : EffThunk} (allowed : SyncAt thunk) (view : View)
    (state next : Stores) (value : Val) (heap : OuterHeap state.refs)
    (found : (interpreter view).syncState thunk state = some (next, value)) : OuterHeap next.refs := by
  cases allowed with
  | make initial outer =>
    change some ({state with refs := state.refs ++ [initial]}, Val.cell ⟨state.refs.length⟩) =
      some (next, value) at found
    cases found
    exact heap.append outer
  | get cell =>
    change (refStep (.refGet cell) state.refs).map
      (fun step => ({state with refs := step.2}, step.1)) = some (next, value) at found
    obtain ⟨step, result, equal⟩ := Option.map_eq_some_iff.mp found
    change (refPeek state.refs cell).map (fun read => (read, state.refs)) = some step at result
    obtain ⟨read, _, same⟩ := Option.map_eq_some_iff.mp result
    cases same
    cases equal
    exact heap
  | update cell term env outer =>
    change ((refPeek state.refs cell).bind fun old =>
      (evalTerm (env ++ [old]) term).map fun written =>
        (Val.unit, refPoke state.refs cell written)).map
      (fun step => ({state with refs := step.2}, step.1)) = some (next, value) at found
    obtain ⟨step, result, equal⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨old, _, result⟩ := Option.bind_eq_some_iff.mp result
    obtain ⟨written, computed, same⟩ := Option.map_eq_some_iff.mp result
    cases same
    cases equal
    exact heap.poke cell (outer old written computed)
  | cancel waiter token =>
    change some ({state with timers := state.timers.cancel waiter token}, Val.unit) = some (next, value) at found
    cases found
    exact heap

/-- Synchronous timeout evaluation cannot create a deferred cell or a scope. -/
theorem sync_state_stores {thunk : EffThunk} (allowed : SyncAt thunk) (view : View)
    (state next : Stores) (value : Val)
    (found : (interpreter view).syncState thunk state = some (next, value)) :
    next.deferreds = state.deferreds ∧ next.scopes = state.scopes := by
  rcases sync_state_shape allowed view state next value found with ⟨refs, rfl⟩ | ⟨waiter, token, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

/-- Actual race, mask and cancellation actions retain the expected successful result. -/
theorem with_fiber {B : List Val} {input output : Kind} (view : View)
    (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (action : NAction) (allowed : ActionAt B input action)
    (current : CodeAt B input fiber.frame.current) (stack : StackAt B input output fiber.frame.stack) :
    IterKind B output (evaluatePrim.withFiber (interpreter view) machine fiber yielding action) := by
  cases allowed with
  | race programs site entrants =>
    exact ⟨.body, .head (.racePark machine.nextRace), stack⟩
  | mask kind body flag good =>
    cases flag
    · unfold evaluatePrim.withFiber FrameFiber.uninterruptible
      dsimp only
      split
      · exact ⟨input, good, .cons (.mask input true) stack⟩
      · exact ⟨input, good, stack⟩
    · unfold evaluatePrim.withFiber FrameFiber.interruptibleRegion FrameFiber.setFiberInterruptible
      dsimp only
      split
      · exact ⟨input, good, stack⟩
      · split
        · exact ⟨input, .head (.failure input _), .cons (.mask input false) stack⟩
        · exact ⟨input, good, .cons (.mask input false) stack⟩
  | cancelRace race =>
    unfold evaluatePrim.withFiber
    dsimp only
    split
    · exact ⟨.unit, .head (.success .unit), stack⟩
    · exact ⟨.unit, current, stack⟩
  | dropObservers token => exact ⟨.unit, .head (.success .unit), stack⟩

/-- Native countdowns may collect arbitrary exits, then their wrapper discards those values. -/
theorem countdown {B : List Val} {output : Kind} (view : View)
    (machine : NativeMachine) (fiber : NativeFiber) (targets : List FiberId)
    (current : CodeAt B .any fiber.frame.current) (stack : StackAt B .any output fiber.frame.stack) :
    FrameKind B output (countdownPark (interpreter view) machine fiber targets .exitsValue).2.1.frame := by
  unfold countdownPark countdownParkEdits
  dsimp only
  split
  · exact ⟨.any, .head (.success (.any _)), stack⟩
  · exact push_cancel current stack (.park fiber.id machine.nextToken)

/-- The registered timer pushes only its own unit cleanup and retains its current class. -/
theorem sleep_eval {B : List Val} {output : Kind} (view : View)
    (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool) (millis : ClockMillis)
    (current : fiber.frame.current = .async (.store (.registerSleep millis)) true (some (.store .cancelSleep)))
    (stack : StackAt B .unit output fiber.frame.stack) :
    IterKind B output (evaluatePrim (interpreter view) machine fiber yielding) := by
  rw [evaluatePrim, current]
  dsimp only
  exact push_cancel (by rw [current]; exact .head (.sleep millis)) stack (.sleep fiber.id machine.nextToken)

/-- A host call's registration yields no immediate value and installs no cancel frame. -/
theorem external_eval {B : List Val} {output : Kind} (view : View)
    (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (op : NativeOp) (request : Val) (path : List Nat)
    (current : fiber.frame.current = .async (.external op request path) false none)
    (stack : StackAt B .body output fiber.frame.stack) :
    IterKind B output (evaluatePrim (interpreter view) machine fiber yielding) := by
  have shape : evaluatePrim (interpreter view) machine fiber yielding =
      ⟨({machine with nextToken := machine.nextToken + 1}).emit
          [.parkedOn fiber.id machine.nextToken],
        fiber.park ⟨machine.nextToken, none, [], [], .void, false⟩, yielding, .parked, [], []⟩ := by
    rw [evaluatePrim, current]
    kernel_rfl
  rw [shape]
  change FrameKind B output fiber.frame
  exact ⟨.body, by rw [current]; exact .head (.external op request path), stack⟩

/-- Every allowed native primitive evaluator case retains its ordered successful value flow. -/
theorem evaluate_head {B : List Val} {input output : Kind} (view : View)
    (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (head : HeadAt B input fiber.frame.current) (stack : StackAt B input output fiber.frame.stack) :
    IterKind B output (evaluatePrim (interpreter view) machine fiber yielding) := by
  have owned : FrameKind B output fiber.frame := ⟨input, .head head, stack⟩
  generalize current : fiber.frame.current = code at head
  cases head with
  | success good =>
    rename_i value
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.finalizerOr (interpreter view) machine fiber yielding (.success value) := by
      rw [evaluatePrim, current]
      rfl
    rw [dispatch]
    exact finalizer_or view machine fiber yielding _ current good stack
  | failure kind cause =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.finalizerOr (interpreter view) machine fiber yielding (.failure cause) := by
      rw [evaluatePrim, current]
      rfl
    rw [dispatch]
    exact finalizer_or view machine fiber yielding _ current trivial stack
  | sync kind thunk answer fallback operation =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        (match (interpreter view).syncState thunk machine.state with
         | some (state, value) => ⟨{machine with state},
             {fiber with frame := {fiber.frame with current := .success value}}, yielding, .answered, [.drainDue], []⟩
         | none => ⟨machine, {fiber with frame := {fiber.frame with current := .success ((interpreter view).syncValue thunk)}},
             yielding, .answered, [], []⟩) := by
      rw [evaluatePrim, current]
      kernel_rfl
    rw [dispatch]
    split
    · rename_i state value found
      exact ⟨input, .head (.success (answer view machine.state state value found)), stack⟩
    · exact ⟨input, .head (.success (fallback view)), stack⟩
  | action kind thunk operation action good =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.withFiber (interpreter view) machine fiber yielding (operation view) := by
      rw [evaluatePrim, current]
      dsimp only
      rw [action view]
      kernel_rfl
    rw [dispatch]
    exact with_fiber view machine fiber yielding _ (good view) (by rw [current]; exact .head (.action _ _ operation action good)) stack
  | external op request path => exact external_eval view machine fiber yielding op request path current stack
  | sleep millis => exact sleep_eval view machine fiber yielding millis current stack
  | yieldNow priority =>
    rw [evaluatePrim, current]
    exact ⟨.unit, .head (.success .unit), stack⟩
  | racePark race =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        registerRace machine fiber yielding race := by
      rw [evaluatePrim, current]
      rfl
    rw [dispatch]
    unfold registerRace
    split <;> exact owned
  | awaitPark targets =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        ⟨(countdownParkEdits (interpreter view) machine fiber targets .exitsValue).1,
          (countdownParkEdits (interpreter view) machine fiber targets .exitsValue).2.1, yielding,
          if (countdownParkEdits (interpreter view) machine fiber targets .exitsValue).2.2.1 then .parked else .continue_, [],
          (countdownParkEdits (interpreter view) machine fiber targets .exitsValue).2.2.2⟩ := by
      rw [evaluatePrim, current]
      rfl
    rw [dispatch]
    have next := countdown view machine fiber targets
      (by rw [current]; exact .head (.awaitPark targets)) stack
    cases parked : (countdownParkEdits (interpreter view) machine fiber targets .exitsValue).2.2.1
    all_goals simp only [IterKind, Bool.false_eq_true, ite_false, ite_true]
    all_goals exact next
  | suspend kind point body =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    apply step_frame view machine fiber yielding owned
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | onSuccess incoming middle body name first next =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    apply step_frame view machine fiber yielding owned
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | constant middle body next first saved =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    apply step_frame view machine fiber yielding owned
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | onFailure kind body name first caught =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    apply step_frame view machine fiber yielding owned
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | onExit kind body name flag first cleanup =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    apply step_frame view machine fiber yielding owned
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong
  | loop name cursor cursorGood enter resume =>
    have dispatch : evaluatePrim (interpreter view) machine fiber yielding =
        evaluatePrim.stepFrame (interpreter view) machine fiber yielding := by rw [evaluatePrim, current]; rfl
    rw [dispatch]
    apply step_frame view machine fiber yielding owned
    · rw [current]; rfl
    · intro thunk wrong; rw [current] at wrong; cases wrong

/-- Primitive evaluation does not inspect the external reply table's admission field. -/
theorem evaluate_table_free (view : View) (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool) :
    evaluatePrim (interpAt HostTimeoutSource.program view []) machine fiber yielding =
      evaluatePrim (interpreter view) machine fiber yielding := by
  kernel_rfl

/-- A source finalizer cannot be mistaken for the stateful scoped-exit callback. -/
theorem exit_scoped_free {B : List Val} {input output : Kind} (view : View)
    (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool) (exit : ExitV)
    (good : ExitAt B input exit) (stack : StackAt B input output fiber.frame.stack) :
    exitScoped HostTimeoutSource.program machine fiber yielding exit =
      evaluatePrim (interpreter machine.completedExits) machine fiber yielding := by
  unfold exitScoped
  dsimp only
  split
  · rename_i body previous scope flag answer
    obtain ⟨point, middle, wrong, _⟩ := finalizer_answer view fiber.frame exit body (.scopedExit previous scope) flag good stack
      (by cases exit <;> exact answer)
    cases wrong
  · exact evaluate_table_free machine.completedExits machine fiber yielding

/-- Native source interception has no extra value-producing case for Timeout. -/
theorem evaluate_native_head {B : List Val} {input output : Kind}
    (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (head : HeadAt B input fiber.frame.current) (stack : StackAt B input output fiber.frame.stack) :
    IterKind B output (evaluateNative HostTimeoutSource.program machine fiber yielding
      Test.Dogfood.Scenario.Timeout.fetch.table) := by
  have basic := evaluate_head machine.completedExits machine fiber yielding head stack
  generalize current : fiber.frame.current = code at head
  cases head with
  | success good =>
    rename_i value
    rw [evaluateNative, current]
    dsimp only
    rw [exit_scoped_free machine.completedExits machine fiber yielding (.success value) good stack]
    exact basic
  | failure kind cause =>
    rw [evaluateNative, current]
    dsimp only
    rw [exit_scoped_free machine.completedExits machine fiber yielding (.failure cause) (input := input) trivial stack]
    exact basic
  | action kind thunk operation action good =>
    unfold evaluateNative
    rw [current]
    cases thunk
    case act point =>
      dsimp only
      split
      · rename_i body found
        have absent : (interpreter machine.completedExits).withFiberOf (.act point) = none := by
          change actionAt HostTimeoutSource.program point = none
          unfold actionAt
          rw [found]
        rw [action machine.completedExits] at absent
        cases absent
      · exact basic
    all_goals exact basic
  | sync kind thunk answer fallback operation => rw [evaluateNative, current]; exact basic
  | suspend kind point body => rw [evaluateNative, current]; exact basic
  | onSuccess incoming middle body name first next => rw [evaluateNative, current]; exact basic
  | constant middle body next first saved => rw [evaluateNative, current]; exact basic
  | onFailure kind body name first caught => rw [evaluateNative, current]; exact basic
  | onExit kind body name flag first cleanup => rw [evaluateNative, current]; exact basic
  | loop name cursor cursorGood enter resume => rw [evaluateNative, current]; exact basic
  | yieldNow priority => rw [evaluateNative, current]; exact basic
  | external op request path => rw [evaluateNative, current]; exact basic
  | sleep millis => rw [evaluateNative, current]; exact basic
  | racePark race => rw [evaluateNative, current]; exact basic
  | awaitPark targets => rw [evaluateNative, current]; exact basic

/-- Actual native evaluation either keeps the ordered frame or finishes at its asserted output. -/
theorem evaluate_native {B : List Val} {output : Kind}
    (machine : NativeMachine) (fiber : NativeFiber) (yielding : Bool)
    (owned : FrameKind B output fiber.frame) :
    IterKind B output (evaluateNative HostTimeoutSource.program machine fiber yielding
      Test.Dogfood.Scenario.Timeout.fetch.table) := by
  obtain ⟨input, code, stack⟩ := owned
  exact evaluate_native_head machine fiber yielding (code_head code) stack

end Test.Dogfood.Proofs.HostTimeoutEvaluation

import Effect4.Laws.Program.PrimitiveProducer
import Effect4.Laws.Program.Interference
import Effect4.Laws.Program.Guard.Command

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Question: the crew answer-flow histories read a parked current head without a new queue invariant.
Reach: the existing native evaluator and actual parked fibers.
The predicate observes existing current code and parked status, independently of stores and values.
Consumer: Initialized.Waits follows from this shape and the initialized current-code certificate.
This shape establishes no answer class, progress or host agreement on its own.
-/
set_option autoImplicit false
namespace Effect4.Program.ParkedShape
open Effect4 Effect4.Machine Effect4.Program
abbrev Fiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- Native parks leave a void yield result, a registration, or an explicit fiber action or await. -/
inductive Head : NCode → Prop
  | yielded : Head (.success .unit)
  | async (register : EffName) (signal : Bool) (cancel : Option EffName) : Head (.async register signal cancel)
  | action (thunk : EffThunk) : Head (.withFiber thunk)
  | park (kind : ParkKind) : Head (.suspend (.park kind))
  | storedPark (kind : ParkKind) : Head (.suspend (.store (.park kind)))

/-- Only a parked fiber owes a park-head observation. -/
def Held (fiber : Fiber) : Prop := fiber.parked ≠ .notParked → Head fiber.frame.current

def Configuration (machine : NativeMachine) : Prop := ∀ fiber ∈ machine.fibers, Held fiber

theorem unparked {fiber : Fiber} (active : fiber.parked = .notParked) : Held fiber :=
  fun parked => False.elim (parked active)

theorem fields {first last : Fiber} (held : Held first)
    (parked : last.parked = first.parked) (current : last.frame.current = first.frame.current) : Held last := by
  intro pending
  rw [current]
  exact held (fun empty => pending (parked.trans empty))

/-- Interrupt recording retains the parked head or removes the park before replacing it. -/
theorem interruption (cause : CauseV) (fiber : Fiber) (held : Held fiber) :
    Held (interruptWithCause cause fiber).1 := by
  unfold interruptWithCause
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore]
  split
  · exact held
  · split
    · split
      · exact held
      · exact unparked rfl
    · exact held

/-- Existing other-fiber edits retain the parked-head observation. -/
theorem edit {first last : Fiber} (word : Moves.OtherEdit first last) (held : Held first) : Held last := by
  cases word with
  | observe => exact held
  | filterObservers => exact held
  | interruptCause cause => exact interruption cause _ held

theorem edits {first last : Fiber} (word : Moves.OtherEdits first last) (held : Held first) : Held last := by
  induction word with
  | refl => exact held
  | tail prior next ih => exact edit next ih

/-- The existing interference witness retains old parked heads; every birth starts unparked. -/
theorem interferes {first last : NativeMachine} (word : Moves.Interferes first last)
    (held : Configuration first) : Configuration last := by
  intro fiber member
  rcases word.fibers fiber member with ⟨old, inside, changed⟩ | ⟨_, program, flag, budget, context, changed⟩
  · exact edits changed (held old inside)
  · exact edits changed (unparked rfl)

/-- Pure frame evaluation changes no parked status. -/
theorem step_frame (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) : Held (evaluatePrim.stepFrame interp machine fiber yielding).fiber := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact unparked active

/-- Finalizer interception either runs a pure frame step or retains the original unparked status. -/
theorem finalizer (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (exit : ExitV) (active : fiber.parked = .notParked) :
    Held (evaluatePrim.finalizerOr interp machine fiber yielding exit).fiber := by
  unfold evaluatePrim.finalizerOr
  repeat' split
  all_goals aesop (add safe apply [step_frame], unsafe apply [unparked])

/-- A countdown either answers without a park or retains the original await head. -/
theorem countdown (interp : Moves.NInterp) (machine : NativeMachine) (fiber : Fiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (active : fiber.parked = .notParked) (head : Head fiber.frame.current) :
    Held (countdownParkEdits interp machine fiber targets resume failFast).2.1 := by
  unfold countdownParkEdits
  dsimp only
  split
  · exact unparked active
  · exact fun _ => head

/-- Action entry can park only an await action; all other actions retain the unparked status. -/
theorem action (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (machine : NativeMachine) (fiber : Fiber) (yielding : Bool) (action : NAction)
    (active : fiber.parked = .notParked) (head : Head fiber.frame.current) :
    Held (evaluatePrim.withFiber (interpAt root view table) machine fiber yielding action).fiber := by
  cases action
  case fork body options site =>
    cases options with
    | mk immediate daemon mode =>
      cases daemon <;> cases immediate
      all_goals exact unparked active
  case forkIn body options scope site =>
    cases options with
    | mk immediate daemon mode =>
      cases immediate
      all_goals exact unparked active
  case forkScoped body options site =>
    simp only [evaluatePrim.withFiber]
    split
    · cases options with
      | mk immediate daemon mode =>
        cases immediate
        all_goals exact unparked active
    · exact unparked active
  case interruptAs target owner =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split <;> exact unparked active
  case awaitAll targets =>
    exact countdown (interpAt root view table) machine fiber targets .exitsValue false active head
  case awaitAllFailFast targets =>
    exact countdown (interpAt root view table) machine fiber targets .exitsValue true active head
  case awaitNewChildren snapshot =>
    exact countdown (interpAt root view table) machine fiber _ .void false active head
  case setInterruptible body flag =>
    cases flag <;> exact unparked active
  case ambientScope =>
    simp only [evaluatePrim.withFiber]
    split <;> exact unparked active
  case runIn target scope => exact unparked active
  case interrupt target => exact unparked active
  case interruptScoped target =>
    simp only [evaluatePrim.withFiber]
    split <;> exact unparked active
  case interruptAll targets owner => exact unparked active
  case snapshotChildren => exact unparked active
  case raceAll bodies site => exact unparked active
  case raceAllFirst bodies site => exact unparked active
  case setContext context => exact unparked active
  case getContext => exact unparked active
  case getId => exact unparked active
  case closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split <;> exact unparked active
  case closePar programs => exact unparked active
  case refuse cause => exact unparked active
  case dropObservers token => exact unparked active
  case cancelRace race =>
    simp only [evaluatePrim.withFiber]
    split <;> exact unparked active
  case getInterruptible => exact unparked active

/-- The native park decoder exposes an explicit park in the existing code. -/
theorem park_head (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (program : NCode) (park : (interpAt root view table).parkOf program ≠ none) : Head program := by
  cases program
  case suspend thunk =>
    cases thunk
    case park kind => exact .park kind
    case store stored =>
      cases stored
      case park kind => exact .storedPark kind
      all_goals exact (park rfl).elim
    all_goals exact (park rfl).elim
  all_goals exact (park rfl).elim

/-- The shared primitive classification supplies each actual parked head. -/
theorem primitive (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (active : fiber.parked = .notParked) :
    Held (evaluatePrim (interpAt root view table) machine fiber yielding).fiber := by
  have producer := Moves.evaluatePrim_producer (interpAt root view table) machine fiber yielding
  generalize actual : evaluatePrim (interpAt root view table) machine fiber yielding = result at producer ⊢
  cases producer with
  | step => exact step_frame _ _ _ _ active
  | finalizer exit current => exact finalizer _ _ _ _ exit active
  | action thunk chosen current unparked found =>
    exact action root view table machine fiber yielding chosen active (current ▸ Head.action thunk)
  | sync | fallback | asyncImmediate | rejectedPark | joinMissing | joinExited => exact unparked active
  | yieldNow => exact fun _ => .yielded
  | asyncParked register signal cancel state current registered =>
    dsimp only
    split <;> exact fun _ => current ▸ Head.async register signal cancel
  | racePark race park =>
    unfold registerRace
    split <;> exact unparked active
  | countdownPark targets next returned parked edits park counted =>
    have result := countdown (interpAt root view table) machine fiber targets .exitsValue false active
      (park_head root view table fiber.frame.current (by rw [park]; intro wrong; cases wrong))
    rw [counted] at result
    exact result
  | joinWaiting target mode other park found live =>
    exact fun _ => park_head root view table fiber.frame.current (by rw [park]; intro wrong; cases wrong)

/-- Scoped exit changes the frame and context while retaining the old unparked status. -/
theorem scoped_exit (root : NativeEff) (machine : NativeMachine) (fiber : Fiber) (yielding : Bool)
    (exit : ExitV) (active : fiber.parked = .notParked) :
    Held (exitScoped root machine fiber yielding exit).fiber := by
  unfold exitScoped
  repeat' split
  all_goals aesop (add safe apply [primitive], unsafe apply [unparked])

/-- Native scoped dispatch and primitive evaluation share the same parked-head observation. -/
theorem native (root : NativeEff) (table : RowTable) (machine : NativeMachine) (fiber : Fiber)
    (yielding : Bool) (active : fiber.parked = .notParked) :
    Held (evaluateNative root machine fiber yielding table).fiber := by
  unfold evaluateNative
  split
  · split
    · exact unparked active
    · exact primitive root machine.completedExits table machine fiber yielding active
  · exact scoped_exit root machine fiber yielding _ active
  · exact scoped_exit root machine fiber yielding _ active
  · exact primitive root machine.completedExits table machine fiber yielding active

/-- The counted iteration keeps its input park absent before actual evaluation. -/
theorem iteration (root : NativeEff) (table : RowTable) (machine : NativeMachine) (fiber : Fiber)
    (yielding : Bool) (active : fiber.parked = .notParked) :
    Held (Machine.iteration (evaluator := evaluatorFor root table) (interpOf root table)
      machine fiber yielding).fiber := by
  have top : (countOp (runloopTop fiber)).parked = .notParked := by
    unfold countOp runloopTop
    split <;> exact active
  unfold Machine.iteration
  dsimp only
  split
  · rename_i result injected
    unfold injectYield at injected
    split at injected
    · cases injected
      exact native root table _ _ _ top
    · cases injected
  · exact native root table _ _ _ top

end Effect4.Program.ParkedShape
